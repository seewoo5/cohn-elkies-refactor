import CohnElkies.SpherePacking.PeriodicApproximation
import CohnElkiesForMathlib.Analysis.Fourier.PoissonSummation

/-!
# The Cohn–Elkies linear programming bound

Let `f : 𝓢(ℝ^d, ℂ)` be a nonzero Schwartz function which is real valued, has real valued Fourier
transform, satisfies `(f x).re ≤ 0` for `‖x‖ ≥ 1` and `(𝓕 f x).re ≥ 0` for all `x`.  Then

`Δ_d = SpherePackingConstant d ≤ (f 0).re / (𝓕 f 0).re * vol (B (0, 1/2))`.

This is `LinearProgrammingBound`, the linear programming bound of Cohn and Elkies.

The proof compares two evaluations of the double sum
`∑_{x, y ∈ centers ∩ D} ∑_{ℓ ∈ Λ} (f (x - y + ℓ)).re` for a periodic packing `P` of separation `1`
with lattice `Λ` and fundamental region `D`.  Bounding each term using `(f ·).re ≤ 0` away from the
origin gives `≤ N * (f 0).re`, where `N` is the number of centers in `D`
(`packing_bound_auxiliary_estimate`).  Poisson summation
(`SchwartzMap.latticePoissonSummationFormula`) rewrites it as a spectral sum over the polar lattice
all of whose terms are nonnegative, so it is at least its `m = 0` term
`N ^ 2 * (𝓕 f 0).re / covolume Λ` (`packing_bound_spectral_estimate`).  Comparing and taking the
supremum over all periodic packings gives the bound.
-/

section
open scoped Real
open Complex (I)

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap

/-! ### Generalities -/

namespace SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

@[simp] theorem schwartz_fourier_inverse_identity (f : 𝓢(V, E)) : 𝓕⁻ (𝓕 ⇑f) = f := by
  simpa only [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe] using
    congrArg (fun g : 𝓢(V, E) ↦ (g : V → E))
      (show (𝓕⁻ (𝓕 f : 𝓢(V, E)) : 𝓢(V, E)) = f from FourierTransform.fourierInv_fourier_eq f)

end SchwartzMap

section OpenPos

variable {E : Type*} [NormedAddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddLeftInvariant]
  [(volume : Measure E).Regular] [NeZero (volume : Measure E)]

instance : (volume : Measure E).IsOpenPosMeasure := isOpenPosMeasure_of_addLeftInvariant_of_regular

end OpenPos

/-- `exp (-2 π i t) = conj (exp (2 π i t))` for real `t`. -/
theorem Complex.exp_neg_two_pi_mul_I (t : ℝ) :
    Complex.exp (-(2 * π * I * t)) = (starRingEnd ℂ) (Complex.exp (2 * π * I * t)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
  ring

namespace SpherePacking.CohnElkies

variable {d : ℕ}

/-- The polar lattice of a lattice is again discrete. -/
instance (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    DiscreteTopology (SchwartzMap.polarIntegerLattice (d := d) Λ) := by
  let bR : Module.Basis (Module.Free.ChooseBasisIndex ℤ Λ) ℝ (EuclideanSpace ℝ (Fin d)) :=
    (Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis ℝ Λ
  have hB : LinearMap.BilinForm.Nondegenerate
      (innerₗ (EuclideanSpace ℝ (Fin d)) : LinearMap.BilinForm ℝ (EuclideanSpace ℝ (Fin d))) := by
    constructor <;> intro x hx <;>
      exact inner_self_eq_zero.1 (show inner ℝ x x = (0 : ℝ) by
        simpa only [innerₗ_apply_apply] using hx x)
  have hdual : SchwartzMap.polarIntegerLattice (d := d) Λ = Submodule.span ℤ (Set.range
      (LinearMap.BilinForm.dualBasis (B := innerₗ (EuclideanSpace ℝ (Fin d))) hB bR)) := by
    simpa [bR, (Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis_span (K := ℝ) (L := Λ)] using
      LinearMap.BilinForm.dualSubmodule_span_of_basis (B := innerₗ (EuclideanSpace ℝ (Fin d)))
        (R := ℤ) (S := ℝ) (M := EuclideanSpace ℝ (Fin d)) hB bR
  exact hdual ▸ inferInstance

/-! ### Summability over a lattice -/

section Summability

variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ]
  (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (a : EuclideanSpace ℝ (Fin d))

open SchwartzMap.PoissonSummation.Standard in
theorem summable_lattice_shift_values :
    Summable fun ℓ : Λ ↦ f (a + (ℓ : EuclideanSpace ℝ (Fin d))) :=
  Summable.of_norm (summable_norm_translate Λ f a)

theorem summable_lattice_shift_real_parts :
    Summable fun ℓ : Λ ↦ (f (a + (ℓ : EuclideanSpace ℝ (Fin d)))).re :=
  Complex.reCLM.summable (summable_lattice_shift_values Λ f a)

end Summability

/-! ### The spectral side -/

section Spectral

variable (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (P : PeriodicSpherePacking d)

open SchwartzMap.PoissonSummation.Standard in
/-- `𝓕 f` is absolutely summable over the polar lattice of the packing lattice. -/
lemma summable_norm_fourier_polar :
    Summable fun m : SchwartzMap.polarIntegerLattice (d := d) P.lattice ↦
      ‖𝓕 ⇑f (m : EuclideanSpace ℝ (Fin d))‖ := by
  simpa [SchwartzMap.fourier_coe] using
    summable_norm_translate (SchwartzMap.polarIntegerLattice (d := d) P.lattice) (𝓕 f) 0

/-- The twisted spectral sum `∑ 𝓕 f m * exp (2πi ⟪v, m⟫)` converges absolutely. -/
lemma summable_fourier_character (v : EuclideanSpace ℝ (Fin d)) :
    Summable fun m : SchwartzMap.polarIntegerLattice (d := d) P.lattice ↦
      𝓕 ⇑f (m : EuclideanSpace ℝ (Fin d)) *
        Complex.exp (2 * π * I * ⟪v, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]) := by
  refine Summable.of_norm ?_
  simpa [norm_mul, Complex.norm_exp, Complex.mul_re, mul_assoc] using
    summable_norm_fourier_polar f P

end Spectral

lemma norm_sq_origin_character_sum (P : PeriodicSpherePacking d)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hd : 0 < d) (hD_isBounded : Bornology.IsBounded D) :
    ‖∑' x : ↑(P.centers ∩ D), Complex.exp (2 * π * I *
        ⟪(x : EuclideanSpace ℝ (Fin d)), (0 : EuclideanSpace ℝ (Fin d))⟫_[ℝ])‖ ^ 2 =
      (P.boundedCenterRepresentativeCount hd hD_isBounded : ℝ) ^ 2 := by
  let := P.instFintypeBoundedCenterRepresentatives hd hD_isBounded
  simp [PeriodicSpherePacking.boundedCenterRepresentativeCount]

/-- All nonzero frequencies contribute nonnegatively to the spectral sum. -/
lemma nonnegative_weighted_nonzero_frequency_sum (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (P : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))
    (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0) :
    0 ≤ ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
      if m = 0 then 0 else (𝓕 ⇑f m).re * ‖∑' x : ↑(P.centers ∩ D), Complex.exp (2 * π * I *
        ⟪(x : EuclideanSpace ℝ (Fin d)), (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])‖ ^ 2 := by
  refine tsum_nonneg fun m ↦ ?_
  by_cases hm : m = 0
  · simp [hm]
  · rw [ite_eq_right hm]
    have hf : 0 ≤ (𝓕 ⇑f (m : EuclideanSpace ℝ (Fin d))).re := by
      simpa using! hCohnElkies₂ (m : EuclideanSpace ℝ (Fin d))
    exact mul_nonneg hf (sq_nonneg _)

/-- Exchanging the finite double sum over centers with the spectral sum over the polar lattice. -/
lemma packing_spectral_sum_exchange (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), ((𝓕 f x).re : ℂ) = 𝓕 f x)
    (P : PeriodicSpherePacking d) {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD_isBounded : Bornology.IsBounded D) (hd : 0 < d) :
    (∑' x : ↑(P.centers ∩ D), ∑' y : ↑(P.centers ∩ D),
        (1 / ZLattice.covolume P.lattice volume) *
          ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice, (𝓕 f m) *
            Complex.exp (2 * π * I * ⟪(x : EuclideanSpace ℝ (Fin d)) -
              (y : EuclideanSpace ℝ (Fin d)), (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])).re =
      ((1 / ZLattice.covolume P.lattice volume) *
        ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice, (𝓕 f m).re *
          ∑' x : ↑(P.centers ∩ D), ∑' y : ↑(P.centers ∩ D), Complex.exp (2 * π * I *
            ⟪(x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)),
              (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])).re := by
  classical
  let := P.instFintypeBoundedCenterRepresentatives hd hD_isBounded
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℂ := 1 / ZLattice.covolume P.lattice volume
  have hW (x y : ↑(P.centers ∩ D)) :
      Summable fun m : SchwartzMap.polarIntegerLattice (d := d) P.lattice ↦ (𝓕 f m) *
        Complex.exp (2 * π * I * ⟪(x : E) - (y : E), (m : E)⟫_[ℝ]) :=
    summable_fourier_character f P ((x : E) - (y : E))
  have hExchange : (∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D), c *
      ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice, (𝓕 f m) *
        Complex.exp (2 * π * I * ⟪(x : E) - (y : E), (m : E)⟫_[ℝ])) =
      c * ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice, (𝓕 f m) *
        ∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D),
          Complex.exp (2 * π * I * ⟪(x : E) - (y : E), (m : E)⟫_[ℝ]) := by
    calc
      _ = c * ∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D),
            ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice, (𝓕 f m) *
              Complex.exp (2 * π * I * ⟪(x : E) - (y : E), (m : E)⟫_[ℝ]) := by
          simp [Finset.mul_sum]
      _ = c * ∑ x : ↑(P.centers ∩ D),
            ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
              ∑ y : ↑(P.centers ∩ D), (𝓕 f m) *
                Complex.exp (2 * π * I * ⟪(x : E) - (y : E), (m : E)⟫_[ℝ]) := by
          congr 1
          exact Finset.sum_congr rfl fun x _ ↦ (Summable.tsum_finsetSum fun y _ ↦ hW x y).symm
      _ = c * ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
            ∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D), (𝓕 f m) *
              Complex.exp (2 * π * I * ⟪(x : E) - (y : E), (m : E)⟫_[ℝ]) := by
          congr 1
          exact (Summable.tsum_finsetSum fun x _ ↦ summable_sum fun y _ ↦ hW x y).symm
      _ = _ := by
          congr 1
          exact tsum_congr fun m ↦ by simp [Finset.mul_sum]
  have hRealCoeff (m : SchwartzMap.polarIntegerLattice (d := d) P.lattice) :
      ((𝓕 f m).re : ℂ) = 𝓕 f m := hRealFourier (m : E)
  simpa [tsum_fintype, c, hRealCoeff] using congrArg Complex.re hExchange

/-! ### The geometric side -/

/-- The centers of a periodic packing are the lattice translates of the centers in a fundamental
region. -/
def fundamentalCentersLatticeProductEquiv (P : PeriodicSpherePacking d) [Nonempty P.centers]
    {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D) :
    (↑(P.centers ∩ D) × P.lattice) ≃ P.centers := by
  classical
  let E := EuclideanSpace ℝ (Fin d)
  refine
    { toFun := fun z ↦ ⟨(z.2 : E) + (z.1 : E), P.lattice_action z.2.property z.1.property.1⟩
      invFun := fun x ↦
        let g := Classical.choose (hD_unique_covers (x : E))
        (⟨(g : E) + (x : E), P.lattice_action g.property x.property,
            (Classical.choose_spec (hD_unique_covers (x : E))).1⟩, -g)
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨x, g⟩
    let k := Classical.choose (hD_unique_covers ((g : E) + (x : E)))
    have hk : k = -g :=
      ((Classical.choose_spec (hD_unique_covers ((g : E) + (x : E)))).2 _
        (by simpa [Submodule.vadd_def, vadd_eq_add, add_assoc] using x.property.2)).symm
    change (⟨(k : E) + ((g : E) + (x : E)), _⟩, -k) = (x, g)
    refine Prod.ext (Subtype.ext ?_) ?_
    · change (k : E) + ((g : E) + (x : E)) = (x : E)
      simp [hk]
    · change -k = g
      simp [hk]
  · exact fun x ↦ Subtype.ext (by simp)

/-- Summing `(f (x - y)).re` over all centers `x` amounts to summing over the centers in a
fundamental region and over the lattice. -/
lemma center_double_sum_eq_region_lattice_sum (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    (P : PeriodicSpherePacking d) [Nonempty P.centers] {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD_isBounded : Bornology.IsBounded D)
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D) (hd : 0 < d) :
    ∑' (x : P.centers) (y : ↑(P.centers ∩ D)), (f (x - (y : EuclideanSpace ℝ (Fin d)))).re =
      ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
        (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
          (ℓ : EuclideanSpace ℝ (Fin d)))).re := by
  classical
  let : Fintype ↑(P.centers ∩ D) :=
    @Fintype.ofFinite _ (finite_centers_in_bounded_region P D hD_isBounded hd)
  let E := EuclideanSpace ℝ (Fin d)
  let e := fundamentalCentersLatticeProductEquiv P hD_unique_covers
  have hs (x y : ↑(P.centers ∩ D)) :
      Summable fun ℓ : P.lattice ↦ (f ((x : E) - (y : E) + (ℓ : E))).re :=
    summable_lattice_shift_real_parts P.lattice f ((x : E) - (y : E))
  have hsummable (x : ↑(P.centers ∩ D)) :
      Summable fun ℓ : P.lattice ↦ ∑' y : ↑(P.centers ∩ D),
        (f ((x : E) - (y : E) + (ℓ : E))).re := by
    simpa [tsum_fintype] using summable_sum (s := (Finset.univ : Finset ↑(P.centers ∩ D)))
      fun y _ ↦ hs x y
  have hswap (x : ↑(P.centers ∩ D)) :
      (∑' (ℓ : P.lattice) (y : ↑(P.centers ∩ D)), (f ((x : E) - (y : E) + (ℓ : E))).re) =
        ∑' (y : ↑(P.centers ∩ D)) (ℓ : P.lattice), (f ((x : E) - (y : E) + (ℓ : E))).re := by
    simpa [tsum_fintype] using Summable.tsum_finsetSum
      (s := (Finset.univ : Finset ↑(P.centers ∩ D))) fun y _ ↦ hs x y
  have htotal : Summable fun z : Σ _ : ↑(P.centers ∩ D), P.lattice ↦
      ∑' y : ↑(P.centers ∩ D), (f ((z.1 : E) - (y : E) + ((z.2 : P.lattice) : E))).re := by
    set G : (Σ _ : ↑(P.centers ∩ D), P.lattice) → ℝ := fun z ↦
      ∑' y : ↑(P.centers ∩ D), (f ((z.1 : E) - (y : E) + ((z.2 : P.lattice) : E))).re with hG
    have hind (x : ↑(P.centers ∩ D)) :
        Summable (({z : Σ _ : ↑(P.centers ∩ D), P.lattice | z.1 = x}).indicator G) := by
      let ex : P.lattice ≃ {z : Σ _ : ↑(P.centers ∩ D), P.lattice | z.1 = x} :=
        { toFun := fun ℓ ↦ ⟨⟨x, ℓ⟩, rfl⟩
          invFun := fun z ↦ z.val.2
          left_inv := fun _ ↦ rfl
          right_inv := by rintro ⟨⟨x', ℓ⟩, rfl⟩; rfl }
      refine summable_subtype_iff_indicator.mp (ex.summable_iff.mp ?_)
      simpa [hG, ex, Function.comp_def] using hsummable x
    simpa [Set.indicator, eq_comm, hG] using
      summable_sum (s := (Finset.univ : Finset ↑(P.centers ∩ D))) fun x _ ↦ hind x
  calc ∑' (x : P.centers) (y : ↑(P.centers ∩ D)), (f ((x : E) - (y : E))).re
      = ∑' (z : ↑(P.centers ∩ D) × P.lattice) (y : ↑(P.centers ∩ D)),
          (f (((z.2 : P.lattice) : E) + (z.1 : E) - (y : E))).re := by
        simpa [e, fundamentalCentersLatticeProductEquiv] using (e.tsum_eq
          (f := fun x : P.centers ↦ ∑' y : ↑(P.centers ∩ D), (f ((x : E) - (y : E))).re)).symm
    _ = ∑' (z : Σ _ : ↑(P.centers ∩ D), P.lattice) (y : ↑(P.centers ∩ D)),
          (f (((z.2 : P.lattice) : E) + (z.1 : E) - (y : E))).re := by
        let ep : (Σ _ : ↑(P.centers ∩ D), P.lattice) ≃ (↑(P.centers ∩ D) × P.lattice) :=
          Equiv.sigmaEquivProd _ _
        simpa [ep] using (ep.tsum_eq (f := fun z : ↑(P.centers ∩ D) × P.lattice ↦
          ∑' y : ↑(P.centers ∩ D),
            (f (((z.2 : P.lattice) : E) + (z.1 : E) - (y : E))).re)).symm
    _ = ∑' (z : Σ _ : ↑(P.centers ∩ D), P.lattice) (y : ↑(P.centers ∩ D)),
          (f ((z.1 : E) - (y : E) + ((z.2 : P.lattice) : E))).re :=
        tsum_congr fun z ↦ tsum_congr fun y ↦ by congr 2; abel
    _ = ∑' (x : ↑(P.centers ∩ D)) (ℓ : P.lattice) (y : ↑(P.centers ∩ D)),
          (f ((x : E) - (y : E) + (ℓ : E))).re :=
        Summable.tsum_sigma' (fun x ↦ hsummable x) htotal
    _ = _ := tsum_congr hswap

/-- Off the diagonal every lattice sum of `(f (x - y + ℓ)).re` is nonpositive; on the diagonal it
is bounded by the term at the origin. -/
lemma real_lattice_sum_bounded_by_origin_term {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)}
    {P : PeriodicSpherePacking d} {D : Set (EuclideanSpace ℝ (Fin d))} (hP : P.separation = 1)
    (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
    (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
    (x y : ↑(P.centers ∩ D)) :
    (∑' ℓ : P.lattice, (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
        (ℓ : EuclideanSpace ℝ (Fin d)))).re) ≤ if x = y then (f 0).re else 0 := by
  classical
  let E := EuclideanSpace ℝ (Fin d)
  have hsum : Summable fun ℓ : P.lattice ↦ (f ((x : E) - (y : E) + (ℓ : E))).re :=
    summable_lattice_shift_real_parts P.lattice f ((x : E) - (y : E))
  have hnonpos (ℓ : P.lattice) (hne : (ℓ : E) + (x : E) ≠ (y : E)) :
      (f ((x : E) - (y : E) + (ℓ : E))).re ≤ 0 := by
    have hdist : 1 ≤ dist ((ℓ : E) + (x : E)) (y : E) := by
      rw [← hP]
      exact P.toSpherePacking.distinct_centers_separation_bound _ _
        (P.lattice_action ℓ.property x.property.1) y.property.1 hne
    exact hCohnElkies₁ _ (by
      simpa [dist_eq_norm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hdist)
  by_cases hxy : x = y
  · subst hxy
    have hmajor : Summable fun ℓ : P.lattice ↦ if ℓ = 0 then (f 0).re else 0 :=
      summable_of_ne_finset_zero (s := {0}) fun ℓ hℓ ↦ ite_eq_right fun h ↦ hℓ (by simp [h])
    have hle : (∑' ℓ : P.lattice, (f ((x : E) - (x : E) + (ℓ : E))).re) ≤
        ∑' ℓ : P.lattice, if ℓ = 0 then (f 0).re else 0 := by
      refine Summable.tsum_le_tsum (fun ℓ ↦ ?_) hsum hmajor
      by_cases hℓ : ℓ = 0
      · simp [hℓ]
      · rw [ite_eq_right hℓ]
        refine hnonpos ℓ fun heq ↦ hℓ (Subtype.ext ?_)
        simpa using congrArg (fun z : E ↦ z - (x : E)) heq
    simpa using hle
  · simp only [ite_eq_right hxy]
    have hterms (ℓ : P.lattice) : (f ((x : E) - (y : E) + (ℓ : E))).re ≤ 0 := by
      refine hnonpos ℓ fun heq ↦ hxy (Subtype.ext ?_)
      have hℓ : ℓ = (0 : P.lattice) := (hD_unique_covers (x : E)).unique
        (show (ℓ : E) + (x : E) ∈ D from heq ▸ y.property.2) (by simpa using x.property.2)
      simpa [hℓ] using heq
    simpa using Summable.tsum_le_tsum hterms hsum summable_zero

end SpherePacking.CohnElkies

/-! ### Positivity of `f 0` -/

section

open SpherePacking MeasureTheory Complex Real Bornology Module
open scoped FourierTransform ENNReal SchwartzMap BigOperators

variable {d : ℕ} {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)} (hne_zero : f ≠ 0)
variable (hReal : ∀ x : EuclideanSpace ℝ (Fin d), ↑(f x).re = (f x))
variable (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), ↑(𝓕 f x).re = (𝓕 f x))
variable (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0)

include hRealFourier in
@[simp]
theorem fourier_imaginary_component_vanishes (x : EuclideanSpace ℝ (Fin d)) : (𝓕 f x).im = 0 := by
  simpa [eq_comm] using congrArg Complex.im (hRealFourier x)

theorem fourier_transform_is_integrable : MeasureTheory.Integrable (𝓕 ⇑f) :=
  ((FourierTransform.fourierCLE ℝ (SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ)) f).integrable

include hne_zero in
theorem fourier_transform_nonzero : 𝓕 f ≠ 0 := fun hzero ↦ hne_zero <| by
  rwa [← ContinuousLinearEquiv.map_eq_zero_iff (FourierTransform.fourierCLE ℝ _)]

include hCohnElkies₂ in
theorem test_function_nonnegative_at_origin : 0 ≤ (f 0).re := by
  rw [← f.schwartz_fourier_inverse_identity, fourierInv_eq]
  simp only [inner_zero_right, AddChar.map_zero_eq_one, one_smul]
  rw [← RCLike.re_eq_complex_re, ← integral_re fourier_transform_is_integrable]
  exact integral_nonneg fun v ↦ by simpa [RCLike.re_eq_complex_re] using! hCohnElkies₂ v

include hne_zero hReal hRealFourier hCohnElkies₂ in
theorem test_function_positive_at_origin : 0 < (f 0).re := by
  refine lt_of_le_of_ne (test_function_nonnegative_at_origin (f := f) hCohnElkies₂) fun hf0re ↦ ?_
  have hf0 : f 0 = 0 := by simpa [hf0re.symm] using (hReal 0).symm
  have hintRe : ∫ v : EuclideanSpace ℝ (Fin d), (𝓕 ⇑f v).re = 0 := by
    have hInv : 𝓕⁻ (𝓕 ⇑f) 0 = f 0 :=
      congrArg (fun g : EuclideanSpace ℝ (Fin d) → ℂ ↦ g 0) f.schwartz_fourier_inverse_identity
    have hint0 : (∫ v : EuclideanSpace ℝ (Fin d), 𝓕 (⇑f) v) = 0 := by
      simpa [fourierInv_eq, inner_zero_right, AddChar.map_zero_eq_one, one_smul, hf0] using hInv
    have hre : (∫ v : EuclideanSpace ℝ (Fin d), (𝓕 ⇑f v).re) =
        (∫ v : EuclideanSpace ℝ (Fin d), 𝓕 ⇑f v).re := by
      simpa using (integral_re (f := fun v : EuclideanSpace ℝ (Fin d) ↦ 𝓕 ⇑f v)
        fourier_transform_is_integrable)
    rw [hre, hint0, Complex.zero_re]
  have hfun : (fun x : EuclideanSpace ℝ (Fin d) ↦ (𝓕 f x).re) = 0 := by
    have hint : MeasureTheory.Integrable fun x : EuclideanSpace ℝ (Fin d) ↦ 𝓕 f x := by
      rw [← FourierTransform.fourierCLE_apply (R := ℝ) (E := 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) f]
      exact ((FourierTransform.fourierCLE ℝ
        (SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ)) f).integrable
    refine (Continuous.ae_eq_iff_eq (volume : Measure (EuclideanSpace ℝ (Fin d)))
      (by fun_prop) continuous_const).1
      ((integral_eq_zero_iff_of_nonneg (fun v ↦ hCohnElkies₂ v) hint.re).1 ?_)
    simpa using! hintRe
  refine fourier_transform_nonzero hne_zero ?_
  ext x
  have hx : ((𝓕 f) x).re = 0 := congrFun hfun x
  simpa [hx] using (hRealFourier x).symm

end

/-! ### The bound for a single periodic packing -/

section

open SpherePacking SpherePacking.CohnElkies MeasureTheory Complex Real Bornology Module
open scoped FourierTransform ENNReal SchwartzMap BigOperators

variable {d : ℕ} {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)}
variable {P : PeriodicSpherePacking d} {D : Set (EuclideanSpace ℝ (Fin d))}

/-- Bounding the geometric double sum termwise gives `N * (f 0).re`. -/
theorem packing_bound_auxiliary_estimate [Nonempty P.centers] (hP : P.separation = 1)
    (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
    (hD_isBounded : IsBounded D) (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
    (hd : 0 < d) :
    ∑' (x : P.centers) (y : ↑(P.centers ∩ D)), (f (x - (y : EuclideanSpace ℝ (Fin d)))).re ≤
      ↑(P.boundedCenterRepresentativeCount hd hD_isBounded) * (f 0).re := by
  classical
  let := P.instFintypeBoundedCenterRepresentatives hd hD_isBounded
  rw [center_double_sum_eq_region_lattice_sum f P hD_isBounded hD_unique_covers hd]
  simp_rw [tsum_fintype]
  calc (∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D), ∑' ℓ : P.lattice,
        (f ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d)) +
          (ℓ : EuclideanSpace ℝ (Fin d)))).re)
      ≤ ∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D), if x = y then (f 0).re else 0 :=
        Finset.sum_le_sum fun x _ ↦ Finset.sum_le_sum fun y _ ↦
          real_lattice_sum_bounded_by_origin_term hP hD_unique_covers hCohnElkies₁ x y
    _ = ↑(P.boundedCenterRepresentativeCount hd hD_isBounded) * (f 0).re := by
        simp [PeriodicSpherePacking.boundedCenterRepresentativeCount]

/-- The real part of the triple sum may be taken termwise. -/
lemma packing_bound_complete_estimate_refined (hD_isBounded : IsBounded D) (hd : 0 < d) :
    ∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice), (f (↑x - ↑y + ↑ℓ)).re =
      (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice), f (↑x - ↑y + ↑ℓ)).re := by
  have : Finite ↑(P.centers ∩ D) := finite_centers_in_bounded_region P D hD_isBounded hd
  rw [re_tsum Summable.of_finite]
  refine tsum_congr fun x ↦ ?_
  rw [re_tsum Summable.of_finite]
  refine tsum_congr fun y ↦ ?_
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (re_tsum (summable_lattice_shift_values P.lattice f
      ((x : EuclideanSpace ℝ (Fin d)) - (y : EuclideanSpace ℝ (Fin d))))).symm

/-- Poisson summation turns the geometric double sum into a spectral sum. -/
theorem packing_bound_geometric_estimate [Nonempty P.centers] (hP : P.separation = 1)
    (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), ↑(𝓕 f x).re = (𝓕 f x))
    (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
    (hD_isBounded : IsBounded D) (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
    (hd : 0 < d) :
    ↑(P.boundedCenterRepresentativeCount hd hD_isBounded) * (f 0).re ≥
      (1 / ZLattice.covolume P.lattice volume) *
        ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice, (𝓕 ⇑f m).re *
          ‖∑' x : ↑(P.centers ∩ D), exp (2 * π * I *
            ⟪(x : EuclideanSpace ℝ (Fin d)), (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])‖ ^ 2 := by
  classical
  let : Fintype ↑(P.centers ∩ D) := P.instFintypeBoundedCenterRepresentatives hd hD_isBounded
  let E := EuclideanSpace ℝ (Fin d)
  have hcharacter (x y : ↑(P.centers ∩ D))
      (m : SchwartzMap.polarIntegerLattice (d := d) P.lattice) :
      exp (2 * π * I * ⟪(x : E) - (y : E), (m : E)⟫_[ℝ]) =
        exp (2 * π * I * ⟪(x : E), (m : E)⟫_[ℝ]) *
          (starRingEnd ℂ) (exp (2 * π * I * ⟪(y : E), (m : E)⟫_[ℝ])) := by
    have hinner : ⟪(x : E) - (y : E), (m : E)⟫_[ℝ] =
        ⟪(x : E), (m : E)⟫_[ℝ] - ⟪(y : E), (m : E)⟫_[ℝ] := by
      simpa only [← RCLike.inner_eq_wInner_one] using
        inner_sub_left (x : E) (y : E) (m : E)
    rw [hinner, Complex.ofReal_sub, show (2 * (π : ℂ) * I * ((⟪(x : E), (m : E)⟫_[ℝ] : ℂ) -
          ⟪(y : E), (m : E)⟫_[ℝ])) =
        2 * (π : ℂ) * I * (⟪(x : E), (m : E)⟫_[ℝ] : ℂ) +
          -(2 * (π : ℂ) * I * (⟪(y : E), (m : E)⟫_[ℝ] : ℂ)) by ring,
      Complex.exp_add, Complex.exp_neg_two_pi_mul_I]
  have hfactor (m : SchwartzMap.polarIntegerLattice (d := d) P.lattice) :
      (∑' x : ↑(P.centers ∩ D), ∑' y : ↑(P.centers ∩ D),
          exp (2 * π * I * ⟪(x : E) - (y : E), (m : E)⟫_[ℝ])) =
        (‖∑' x : ↑(P.centers ∩ D), exp (2 * π * I * ⟪(x : E), (m : E)⟫_[ℝ])‖ ^ 2 : ℝ) := by
    simp_rw [tsum_fintype, hcharacter]
    calc
      _ = (∑ x : ↑(P.centers ∩ D), exp (2 * π * I * ⟪(x : E), (m : E)⟫_[ℝ])) *
            ∑ y : ↑(P.centers ∩ D), (starRingEnd ℂ)
              (exp (2 * π * I * ⟪(y : E), (m : E)⟫_[ℝ])) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun x _ ↦ (Finset.mul_sum ..).symm
      _ = (∑ x : ↑(P.centers ∩ D), exp (2 * π * I * ⟪(x : E), (m : E)⟫_[ℝ])) *
            (starRingEnd ℂ) (∑ y : ↑(P.centers ∩ D),
              exp (2 * π * I * ⟪(y : E), (m : E)⟫_[ℝ])) := by rw [map_sum]
      _ = _ := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hSpectral : Summable fun m : SchwartzMap.polarIntegerLattice (d := d) P.lattice ↦
      ((𝓕 f m).re : ℂ) *
        (‖∑' x : ↑(P.centers ∩ D), exp (2 * π * I * ⟪(x : E), (m : E)⟫_[ℝ])‖ ^ 2 : ℝ) := by
    have hFull : Summable fun m : SchwartzMap.polarIntegerLattice (d := d) P.lattice ↦
        ∑ x : ↑(P.centers ∩ D), ∑ y : ↑(P.centers ∩ D), 𝓕 f (m : E) *
          exp (2 * π * I * ⟪(x : E) - (y : E), (m : E)⟫_[ℝ]) :=
      summable_sum fun x _ ↦ summable_sum fun y _ ↦
        summable_fourier_character f P ((x : E) - (y : E))
    refine (summable_congr fun m ↦ ?_).mp hFull
    rw [← hRealFourier (m : E), ← hfactor m]
    simp [tsum_fintype, Finset.mul_sum]
  have hgeom : (∑' (x : ↑(P.centers ∩ D)) (y : ↑(P.centers ∩ D)) (ℓ : P.lattice),
        (f (↑x - ↑y + ↑ℓ)).re) = (1 / ZLattice.covolume P.lattice volume) *
      ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice, (𝓕 ⇑f m).re *
        ‖∑' x : ↑(P.centers ∩ D), exp (2 * π * I * ⟪(x : E), (m : E)⟫_[ℝ])‖ ^ 2 := by
    rw [packing_bound_complete_estimate_refined hD_isBounded hd]
    simp_rw [SchwartzMap.latticePoissonSummationFormula P.lattice f, ← SchwartzMap.fourier_coe]
    rw [packing_spectral_sum_exchange f hRealFourier P hD_isBounded hd]
    simp_rw [hfactor]
    rw [one_div (ZLattice.covolume P.lattice volume : ℂ), ← Complex.ofReal_inv,
      Complex.re_ofReal_mul, Complex.re_tsum hSpectral, ← one_div]
    congr 1
    refine tsum_congr fun m ↦ ?_
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hbound := packing_bound_auxiliary_estimate hP hCohnElkies₁ hD_isBounded hD_unique_covers hd
  rw [center_double_sum_eq_region_lattice_sum f P hD_isBounded hD_unique_covers hd] at hbound
  linarith [hgeom]

/-- The spectral sum is at least its contribution at the origin. -/
theorem packing_bound_spectral_estimate
    (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0) (hD_isBounded : IsBounded D)
    (hd : 0 < d) : (1 / ZLattice.covolume P.lattice volume) *
      ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice, (𝓕 ⇑f m).re *
        ‖∑' x : ↑(P.centers ∩ D), exp (2 * π * I * ⟪(x : EuclideanSpace ℝ (Fin d)),
          (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ])‖ ^ 2 ≥
      ↑(P.boundedCenterRepresentativeCount hd hD_isBounded) ^ 2 * (𝓕 f 0).re /
        ZLattice.covolume P.lattice volume := by
  classical
  let := P.instFintypeBoundedCenterRepresentatives hd hD_isBounded
  let E := EuclideanSpace ℝ (Fin d)
  let N : ℝ := P.boundedCenterRepresentativeCount hd hD_isBounded
  let F : SchwartzMap.polarIntegerLattice (d := d) P.lattice → ℝ := fun m ↦
    (𝓕 ⇑f m).re * ‖∑' x : ↑(P.centers ∩ D), exp (2 * π * I * ⟪(x : E), (m : E)⟫_[ℝ])‖ ^ 2
  have hNnonneg : 0 ≤ N := by dsimp [N]; positivity
  have hCharacterBound (m : SchwartzMap.polarIntegerLattice (d := d) P.lattice) :
      ‖∑' x : ↑(P.centers ∩ D), exp (2 * π * I * ⟪(x : E), (m : E)⟫_[ℝ])‖ ≤ N := by
    rw [tsum_fintype]
    refine (norm_sum_le _ _).trans_eq ?_
    simp [N, PeriodicSpherePacking.boundedCenterRepresentativeCount, Complex.norm_exp,
      Complex.mul_re, mul_assoc]
  have hFsummable : Summable F := by
    refine Summable.of_nonneg_of_le (fun m ↦ mul_nonneg (hCohnElkies₂ _) (sq_nonneg _))
      (fun m ↦ ?_) ((summable_norm_fourier_polar f P).mul_left (N ^ 2))
    calc F m ≤ ‖𝓕 ⇑f (m : E)‖ * N ^ 2 :=
          mul_le_mul ((le_abs_self _).trans (Complex.abs_re_le_norm _))
            (pow_le_pow_left₀ (norm_nonneg _) (hCharacterBound m) 2) (sq_nonneg _) (norm_nonneg _)
      _ = N ^ 2 * ‖𝓕 ⇑f (m : E)‖ := mul_comm _ _
  have horigin : F (0 : SchwartzMap.polarIntegerLattice (d := d) P.lattice) =
      (𝓕 f 0).re * N ^ 2 := by
    change (𝓕 f (0 : E)).re *
      ‖∑' x : ↑(P.centers ∩ D), exp (2 * π * I * ⟪(x : E), (0 : E)⟫_[ℝ])‖ ^ 2 = (𝓕 f 0).re * N ^ 2
    rw [norm_sq_origin_character_sum P hd hD_isBounded]
  have htail : 0 ≤ ∑' m : SchwartzMap.polarIntegerLattice (d := d) P.lattice,
      if m = 0 then 0 else F m :=
    nonnegative_weighted_nonzero_frequency_sum f P D hCohnElkies₂
  have hsum : (𝓕 f 0).re * N ^ 2 ≤ ∑' m, F m := by
    rw [hFsummable.tsum_eq_add_tsum_ite 0, horigin]
    linarith
  have hcovol : 0 ≤ ZLattice.covolume P.lattice volume := by
    rw [SchwartzMap.lattice_covolume_eq_coordinate_determinant]
    exact abs_nonneg _
  simpa [F, N, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_left hsum
      (by positivity : 0 ≤ (1 / ZLattice.covolume P.lattice volume : ℝ))

/-- The linear programming bound for a single periodic packing of separation `1`. -/
theorem LinearProgrammingBound' [Nonempty P.centers] (hne_zero : f ≠ 0)
    (hReal : ∀ x : EuclideanSpace ℝ (Fin d), ↑(f x).re = (f x))
    (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), ↑(𝓕 f x).re = (𝓕 f x))
    (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
    (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0) (hP : P.separation = 1)
    (hD_isBounded : IsBounded D) (hD_unique_covers : ∀ x, ∃! g : P.lattice, g +ᵥ x ∈ D)
    (hd : 0 < d) : P.upperPackingDensity ≤ (f 0).re.toNNReal / (𝓕 f 0).re.toNNReal *
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) := by
  classical
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hfunction : 0 < (f 0).re :=
    test_function_positive_at_origin hne_zero hReal hRealFourier hCohnElkies₂
  have hball : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) ≠ 0 :=
    (EuclideanSpace.euclidean_ball_volume_positive (0 : EuclideanSpace ℝ (Fin d))
      (by norm_num : (0 : ℝ) < 1 / 2)).ne'
  by_cases hfourier_zero : (𝓕 f 0).re = 0
  · simp [hfourier_zero, div_eq_mul_inv, (Real.toNNReal_pos.mpr hfunction).ne',
      show volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (2 : ℝ)⁻¹) ≠ 0 by
        simpa only [one_div] using hball]
  have hfourier : 0 < (𝓕 f 0).re := lt_of_le_of_ne (hCohnElkies₂ 0) (Ne.symm hfourier_zero)
  have hcount : 0 < (P.boundedCenterRepresentativeCount hd hD_isBounded : ℝ) := by
    rw [← P.orbit_cardinality_eq_bounded_representatives hd hD_isBounded hD_unique_covers]
    have hpos : 0 < P.centerOrbitCardinality := by
      unfold PeriodicSpherePacking.centerOrbitCardinality
      exact Fintype.card_pos_iff.mpr ⟨Quotient.mk _ (Classical.choice inferInstance)⟩
    exact_mod_cast hpos
  have hcovolume : 0 < ZLattice.covolume P.lattice volume := by
    rw [SchwartzMap.lattice_covolume_eq_coordinate_determinant]
    refine abs_pos.mpr fun hdet ↦ ?_
    have hdetcomp := congrArg (LinearMap.det : (EuclideanSpace ℝ (Fin d) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin d)) →* ℝ)
      (show (SchwartzMap.latticeCoordinateEquiv P.lattice).toLinearMap *
        (SchwartzMap.latticeCoordinateEquiv P.lattice).symm.toLinearMap = 1 by ext x; simp)
    simp [map_mul, hdet] at hdetcomp
  have hestimate := (packing_bound_spectral_estimate hCohnElkies₂ hD_isBounded hd).trans
    (packing_bound_geometric_estimate hP hRealFourier hCohnElkies₁ hD_isBounded
      hD_unique_covers hd)
  have hcancel : (P.boundedCenterRepresentativeCount hd hD_isBounded : ℝ) * (𝓕 f 0).re ≤
      (f 0).re * ZLattice.covolume P.lattice volume := by
    refine le_of_mul_le_mul_left ?_ hcount
    have hscaled : (P.boundedCenterRepresentativeCount hd hD_isBounded : ℝ) ^ 2 * (𝓕 f 0).re ≤
        ((P.boundedCenterRepresentativeCount hd hD_isBounded : ℝ) * (f 0).re) *
          ZLattice.covolume P.lattice volume := (div_le_iff₀ hcovolume).mp hestimate
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hnonnegative := ENNReal.ofReal_le_ofReal
    ((div_le_div_iff₀ hcovolume hfourier).mpr hcancel)
  rw [ENNReal.ofReal_div_of_pos hcovolume, ENNReal.ofReal_div_of_pos hfourier] at hnonnegative
  have hnonnegative' : (P.boundedCenterRepresentativeCount hd hD_isBounded : ℝ≥0∞) /
      (ZLattice.covolume P.lattice volume).toNNReal ≤
        (f 0).re.toNNReal / (𝓕 f 0).re.toNNReal := by
    simpa [ENNReal.ofReal] using hnonnegative
  rw [P.density_eq_numReps_mul_volume_ball_div_covolume hd, hP,
    P.orbit_cardinality_eq_bounded_representatives hd hD_isBounded hD_unique_covers]
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_left hnonnegative'
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)))

/-- **The Cohn–Elkies linear programming bound**: if `f` is a nonzero real valued Schwartz function
with real valued Fourier transform such that `f ≤ 0` outside the unit ball and `𝓕 f ≥ 0`, then the
sphere packing constant of `ℝ^d` is at most `f 0 / 𝓕 f 0` times the volume of a ball of radius
`1 / 2`. -/
theorem LinearProgrammingBound (hne_zero : f ≠ 0)
    (hReal : ∀ x : EuclideanSpace ℝ (Fin d), ↑(f x).re = (f x))
    (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), ↑(𝓕 f x).re = (𝓕 f x))
    (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
    (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0) (hd : 0 < d) :
    SpherePackingConstant d ≤ (f 0).re.toNNReal / (𝓕 ⇑f 0).re.toNNReal *
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) := by
  rw [← periodic_packing_supremum_eq_unrestricted hd,
    periodic_packing_supremum_eq_unit_separation (d := d)]
  refine iSup_le fun P ↦ iSup_le fun hP ↦ ?_
  cases isEmpty_or_nonempty ↑P.centers with
  | inl _ => simp [P.packing_density_zero_of_empty_centers hd]
  | inr _ =>
    let b : Module.Basis (Fin d) ℤ P.lattice :=
      ((ZLattice.module_free ℝ P.lattice).chooseBasis).reindex
        (PeriodicSpherePacking.coordinateIndexEquiv P)
    exact LinearProgrammingBound' hne_zero hReal hRealFourier hCohnElkies₁ hCohnElkies₂ hP
      (ZSpan.fundamentalDomain_isBounded (Module.Basis.ofZLatticeBasis ℝ P.lattice b))
      (PeriodicSpherePacking.basis_region_translates_cover_uniquely (S := P) b) hd

end

end

end
