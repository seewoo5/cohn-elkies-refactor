import Mathlib
import CohnElkiesForMathlib.Analysis.Fourier.FourierTransform

/-!
# Poisson summation for lattices in `ℝ^d`

Let `Λ ⊆ ℝ^d` be a lattice and `Λ* = SchwartzMap.polarIntegerLattice Λ` its polar (dual) lattice.
For a Schwartz function `f : 𝓢(ℝ^d, ℂ)` the Poisson summation formula

`∑' ℓ : Λ, f (v + ℓ) = (covolume Λ)⁻¹ * ∑' m : Λ*, 𝓕 f m * exp (2 π i ⟪v, m⟫)`

is proved in `SchwartzMap.latticePoissonSummationFormula`.

The argument is the classical one.  For the standard lattice `ℤ^d`
(`SchwartzMap.referenceIntegerLattice`) the periodization `∑' n : ℤ^d, f (· + n)` is a continuous
function on the torus `(ℝ/ℤ)^d` whose `n`-th Fourier coefficient is `𝓕 f n`; evaluating its
absolutely convergent Fourier series gives the formula for `ℤ^d`.  A general lattice is the image
of `ℤ^d` under a linear equivalence `A`, and `Real.fourier_comp_linearEquiv` transports the
`ℤ^d`-formula, the Jacobian `|det A|` being the covolume of `Λ`.
-/

open MeasureTheory
open scoped BigOperators FourierTransform Real
open Complex (I)

noncomputable section

namespace SchwartzMap

variable {d : ℕ}

/-! ### The standard lattice `ℤ^d` -/

/-- The standard lattice `ℤ^d ⊆ ℝ^d`, spanned over `ℤ` by the standard orthonormal basis. -/
def referenceIntegerLattice (d : ℕ) : Submodule ℤ (EuclideanSpace ℝ (Fin d)) :=
  Submodule.span ℤ (Set.range ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis))

namespace referenceIntegerLattice

instance instDiscreteReferenceIntegerLattice : DiscreteTopology (referenceIntegerLattice d) :=
  inferInstanceAs (DiscreteTopology
    (Submodule.span ℤ (Set.range ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis))))

instance instFullRankPackingLattice : IsZLattice ℝ (referenceIntegerLattice d) :=
  inferInstanceAs (IsZLattice ℝ
    (Submodule.span ℤ (Set.range ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis))))

end referenceIntegerLattice

namespace PoissonSummation.Standard

/-- The point of the standard lattice `ℤ^d ⊆ ℝ^d` with integer coordinates `k`. -/
def embeddedIntegerVector (k : Fin d → ℤ) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp (2 : ENNReal) fun i : Fin d ↦ (k i : ℝ)

@[simp] lemma embeddedIntegerVector_apply (k : Fin d → ℤ) (i : Fin d) :
    embeddedIntegerVector (d := d) k i = (k i : ℝ) := rfl

@[simp] lemma embeddedIntegerVector_neg (n : Fin d → ℤ) :
    embeddedIntegerVector (-n) = -embeddedIntegerVector (d := d) n := by
  ext i; simp

lemma embeddedIntegerVector_mem (k : Fin d → ℤ) :
    embeddedIntegerVector k ∈ referenceIntegerLattice d := by
  have hsum : embeddedIntegerVector (d := d) k =
      ∑ i : Fin d, k i • ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis i) := by
    ext j
    simp [embeddedIntegerVector, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
      Pi.single_apply]
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

lemma exists_eq_embeddedIntegerVector {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ referenceIntegerLattice d) : ∃ n : Fin d → ℤ, x = embeddedIntegerVector n := by
  choose n hn using (Module.Basis.mem_span_iff_repr_mem (R := ℤ)
    (b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis) x).1 hx
  exact ⟨n, by ext i; simpa using (hn i).symm⟩

/-- Integer vectors parametrise the standard lattice `ℤ^d`. -/
def integerVectorLatticeEquiv : (Fin d → ℤ) ≃ referenceIntegerLattice d :=
  Equiv.ofBijective (fun n ↦ ⟨embeddedIntegerVector n, embeddedIntegerVector_mem n⟩) <| by
    refine ⟨fun a b hab ↦ funext fun i ↦ ?_, fun ℓ ↦ ?_⟩
    · simpa using congrArg (fun x : EuclideanSpace ℝ (Fin d) ↦ x i) (congrArg Subtype.val hab)
    · obtain ⟨n, hn⟩ := exists_eq_embeddedIntegerVector ℓ.property
      exact ⟨n, Subtype.ext hn.symm⟩

@[simp] lemma integerVectorLatticeEquiv_coe (n : Fin d → ℤ) :
    ((integerVectorLatticeEquiv n : referenceIntegerLattice d) : EuclideanSpace ℝ (Fin d)) =
      embeddedIntegerVector n := rfl

/-- The standard lattice is its own polar lattice. -/
lemma dualSubmodule_referenceIntegerLattice :
    LinearMap.BilinForm.dualSubmodule
        (B := (innerₗ (EuclideanSpace ℝ (Fin d)) : LinearMap.BilinForm ℝ _))
        (referenceIntegerLattice d) = referenceIntegerLattice d := by
  ext x
  constructor
  · intro hx
    have hxcoord (i : Fin d) : ∃ n : ℤ, (n : ℝ) = x i := by
      have hinner : inner ℝ x (EuclideanSpace.basisFun (Fin d) ℝ i) ∈ (1 : Submodule ℤ ℝ) := by
        simpa [innerₗ_apply_apply] using hx _ (Submodule.subset_span ⟨i, by simp⟩)
      obtain ⟨n, hn⟩ := Submodule.mem_one.mp hinner
      exact ⟨n, by simpa [-EuclideanSpace.basisFun_apply] using hn⟩
    choose n hn using hxcoord
    have hx' : x = embeddedIntegerVector n := by ext i; simp [hn i]
    simpa [hx'] using embeddedIntegerVector_mem (d := d) n
  · intro hx y hy
    obtain ⟨n, rfl⟩ := exists_eq_embeddedIntegerVector hx
    obtain ⟨m, rfl⟩ := exists_eq_embeddedIntegerVector hy
    exact Submodule.mem_one.mpr ⟨∑ i : Fin d, n i * m i, by
      simp [innerₗ_apply_apply, embeddedIntegerVector, PiLp.inner_apply, map_sum, mul_comm]⟩

/-! ### The torus `(ℝ/ℤ)^d` and the half-open unit cell -/

/-- The projection of `ℝ^d` onto the torus `(ℝ/ℤ)^d`: coordinatewise reduction modulo `1`. -/
def torusMk (x : EuclideanSpace ℝ (Fin d)) : UnitAddTorus (Fin d) := fun i ↦ (x i : UnitAddCircle)

@[continuity]
theorem continuous_torusMk : Continuous (torusMk (d := d)) :=
  continuous_pi fun i ↦ (AddCircle.continuous_mk' (p := (1 : ℝ))).comp
    (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin d ↦ ℝ) i)

theorem isOpenQuotientMap_torusMk : IsOpenQuotientMap (torusMk (d := d)) :=
  (IsOpenQuotientMap.piMap fun _ : Fin d ↦
      QuotientAddGroup.isOpenQuotientMap_mk (G := ℝ) (N := AddSubgroup.zmultiples (1 : ℝ))).comp
    (PiLp.homeomorph (p := (2 : ENNReal)) (β := fun _ : Fin d ↦ ℝ)).isOpenQuotientMap

/-- The projection `ℝ^d → (ℝ/ℤ)^d`, as a bundled continuous map. -/
def torusMkHom : C(EuclideanSpace ℝ (Fin d), UnitAddTorus (Fin d)) := ⟨torusMk, continuous_torusMk⟩

theorem isQuotientMap_torusMkHom : Topology.IsQuotientMap (torusMkHom (d := d)) :=
  isOpenQuotientMap_torusMk.isQuotientMap

@[simp]
theorem torusMk_add_embeddedIntegerVector (x : EuclideanSpace ℝ (Fin d)) (n : Fin d → ℤ) :
    torusMk (x + embeddedIntegerVector n) = torusMk x := by
  ext i; simp [torusMk]

theorem exists_sub_eq_embeddedIntegerVector {x y : EuclideanSpace ℝ (Fin d)}
    (h : torusMk x = torusMk y) : ∃ n : Fin d → ℤ, x - y = embeddedIntegerVector n := by
  have hcoord (i : Fin d) : ∃ n : ℤ, (n : ℝ) = x i - y i := by
    have hsub : ((x i - y i : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      simpa [UnitAddCircle, AddCircle.coe_sub, torusMk] using sub_eq_zero.2 (congrFun h i)
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ)) (x := (x i - y i : ℝ))).1 hsub
    exact ⟨n, by simpa using hn⟩
  choose n hn using hcoord
  exact ⟨n, by ext i; simp [hn i]⟩

/-- The half-open unit cell `(0, 1]^d`, a fundamental domain for the action of `ℤ^d` on `ℝ^d`. -/
def halfOpenUnitCell : Set (EuclideanSpace ℝ (Fin d)) := {x | ∀ i : Fin d, x i ∈ Set.Ioc (0 : ℝ) 1}

lemma measurableSet_halfOpenUnitCell : MeasurableSet (halfOpenUnitCell (d := d)) := by
  have hset : halfOpenUnitCell (d := d) =
      ⋂ i : Fin d, (fun x : EuclideanSpace ℝ (Fin d) ↦ x i) ⁻¹' Set.Ioc (0 : ℝ) 1 := by
    ext x; simp [halfOpenUnitCell]
  rw [hset]
  exact .iInter fun i ↦
    (PiLp.continuous_apply (p := (2 : ENNReal)) (β := fun _ : Fin d ↦ ℝ) i).measurable
      measurableSet_Ioc

lemma existsUnique_add_embeddedIntegerVector_mem (x : EuclideanSpace ℝ (Fin d)) :
    ∃! n : Fin d → ℤ, x + embeddedIntegerVector n ∈ halfOpenUnitCell (d := d) := by
  have hxcoord (i : Fin d) : ∃! m : ℤ, (x i : ℝ) + m • (1 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by
    simpa [one_smul, add_assoc] using
      existsUnique_add_zsmul_mem_Ioc (G := ℝ) (ha := zero_lt_one) (b := (x i : ℝ)) (c := (0 : ℝ))
  choose n hn hn_unique using hxcoord
  refine ⟨n, fun i ↦ by simpa [halfOpenUnitCell, zsmul_one] using hn i, fun n' hn' ↦ ?_⟩
  funext i
  exact hn_unique i (n' i) (by simpa [halfOpenUnitCell, zsmul_one] using hn' i)

/-- The half-open unit cell `(0, 1]^d` is a fundamental domain for the action of `ℤ^d`. -/
theorem isAddFundamentalDomain_halfOpenUnitCell :
    IsAddFundamentalDomain (referenceIntegerLattice d) (halfOpenUnitCell (d := d)) volume := by
  refine .mk' (measurableSet_halfOpenUnitCell (d := d)).nullMeasurableSet fun x ↦ ?_
  obtain ⟨n, hn, hn_unique⟩ := existsUnique_add_embeddedIntegerVector_mem x
  refine ⟨⟨embeddedIntegerVector n, embeddedIntegerVector_mem n⟩, ?_, fun ℓ hℓ ↦ ?_⟩
  · simpa [Submodule.vadd_def, vadd_eq_add, add_comm] using hn
  · obtain ⟨n', hn'⟩ := exists_eq_embeddedIntegerVector ℓ.property
    have hnn : n' = n :=
      hn_unique n' (by simpa [Submodule.vadd_def, vadd_eq_add, add_comm, hn'] using hℓ)
    exact Subtype.ext (by simp [hn', hnn])

lemma halfOpenUnitCell_subset_closedBall :
    halfOpenUnitCell (d := d) ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (√d) := by
  intro x hx
  have hsum : (∑ i : Fin d, ‖x i‖ ^ 2) ≤ (d : ℝ) := by
    have hterm (i : Fin d) : ‖x i‖ ^ 2 ≤ (1 : ℝ) := by
      have hi : x i ∈ Set.Ioc (0 : ℝ) 1 := hx i
      have hxle : ‖x i‖ ≤ 1 := by
        simpa [Real.norm_eq_abs, abs_of_nonneg hi.1.le] using hi.2
      nlinarith [norm_nonneg (x i)]
    simpa using (Finset.sum_le_sum fun i _ ↦ hterm i).trans_eq (by simp)
  simpa [Metric.mem_closedBall, dist_eq_norm, EuclideanSpace.norm_eq] using Real.sqrt_le_sqrt hsum

lemma measure_halfOpenUnitCell_lt_top : volume (halfOpenUnitCell (d := d)) < ⊤ :=
  ((Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin d))) (r := √d)).subset
    halfOpenUnitCell_subset_closedBall).measure_lt_top

/-- Integration over the box `(0, 1]^d ⊆ ℝ^d` is integration over the half-open unit cell of the
Euclidean space `ℝ^d`. -/
theorem integral_pi_eq_integral_cell (g : UnitAddTorus (Fin d) → ℂ) :
    (∫ x : Fin d → ℝ in {x | ∀ i, x i ∈ Set.Ioc (0 : ℝ) (0 + 1)},
        g fun i ↦ (x i : UnitAddCircle)) = ∫ x in halfOpenUnitCell, g (torusMk x) := by
  have hmp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin d → ℝ))
      (volume : Measure (Fin d → ℝ)) (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
    simpa [MeasurableEquiv.coe_toLp] using PiLp.volume_preserving_toLp (ι := Fin d)
  have hpre : (MeasurableEquiv.toLp 2 (Fin d → ℝ)) ⁻¹' (halfOpenUnitCell (d := d)) =
      {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) (0 + 1)} := by
    ext x; simp [halfOpenUnitCell, MeasurableEquiv.coe_toLp]
  have hres := (hmp.restrict_preimage (measurableSet_halfOpenUnitCell (d := d))).integral_comp'
    (fun y : EuclideanSpace ℝ (Fin d) ↦ g (torusMk y))
  rw [← hres, hpre]
  exact integral_congr_ae (.of_forall fun _ ↦ rfl)

/-! ### Characters of the torus -/

lemma mFourier_torusMk_eq (n : Fin d → ℤ) (x : EuclideanSpace ℝ (Fin d)) :
    UnitAddTorus.mFourier n (torusMk x) =
      Complex.exp (2 * π * I * ∑ i : Fin d, (n i : ℝ) * x i) := by
  simpa [UnitAddTorus.mFourier, ContinuousMap.coe_mk, torusMk, fourier_coe_apply, Finset.mul_sum,
    mul_assoc, mul_left_comm, mul_comm] using
    (Complex.exp_sum (s := (Finset.univ : Finset (Fin d)))
      (f := fun i : Fin d ↦ 2 * π * I * ((n i : ℝ) * x i))).symm

lemma mFourier_torusMk (n : Fin d → ℤ) (x : EuclideanSpace ℝ (Fin d)) :
    UnitAddTorus.mFourier n (torusMk x) = (𝐞 (inner ℝ x (embeddedIntegerVector n)) : ℂ) := by
  simp [mFourier_torusMk_eq, Real.fourierChar_apply, embeddedIntegerVector, PiLp.inner_apply,
    mul_assoc, mul_comm]

lemma mFourier_torusMk_exp (n : Fin d → ℤ) (x : EuclideanSpace ℝ (Fin d)) :
    UnitAddTorus.mFourier n (torusMk x) =
      Complex.exp (2 * π * I * ⟪x, embeddedIntegerVector n⟫_[ℝ]) := by
  have hinner : inner ℝ x (embeddedIntegerVector (d := d) n) =
      RCLike.wInner (𝕜 := ℝ) 1 x.ofLp (embeddedIntegerVector (d := d) n).ofLp :=
    RCLike.inner_eq_wInner_one x (embeddedIntegerVector n)
  simpa [Real.fourierChar_apply, mul_assoc, mul_comm, hinner] using mFourier_torusMk n x

lemma mFourier_torusMk_add_lattice (n : Fin d → ℤ) (ℓ : referenceIntegerLattice d)
    (x : EuclideanSpace ℝ (Fin d)) :
    UnitAddTorus.mFourier n (torusMk (x + ℓ)) = UnitAddTorus.mFourier n (torusMk x) := by
  obtain ⟨m, hm⟩ := exists_eq_embeddedIntegerVector ℓ.property
  simp [hm]

lemma norm_mFourier_torusMk_le (n : Fin d → ℤ) (x : EuclideanSpace ℝ (Fin d)) :
    ‖UnitAddTorus.mFourier n (torusMk x)‖ ≤ 1 := by
  simpa [UnitAddTorus.mFourier_norm (d := Fin d) (n := n)] using
    (UnitAddTorus.mFourier n).norm_coe_le_norm (torusMk x)

/-- The compact ball of radius `√d` around the origin; it contains the half-open unit cell. -/
def ball : TopologicalSpace.Compacts (EuclideanSpace ℝ (Fin d)) :=
  ⟨Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (√d),
    isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) (√d)⟩

/-! ### Summability of the lattice translates of a Schwartz function -/

section Translates

variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ]
  (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))

/-- The translate `x ↦ f (x + v)` of a Schwartz function, as a continuous map. -/
def translate (v : EuclideanSpace ℝ (Fin d)) : C(EuclideanSpace ℝ (Fin d), ℂ) :=
  (⟨f, f.continuous⟩ : C(EuclideanSpace ℝ (Fin d), ℂ)).comp (ContinuousMap.addRight v)

@[simp] lemma translate_apply (v x : EuclideanSpace ℝ (Fin d)) : translate f v x = f (x + v) := rfl

/-- The sup-norms over a fixed compact set of the lattice translates of a Schwartz function are
summable; this is the local uniform convergence of the lattice periodization. -/
lemma summable_norm_restrict_translate (K : TopologicalSpace.Compacts (EuclideanSpace ℝ (Fin d))) :
    Summable fun ℓ : Λ ↦ ‖(translate f (ℓ : EuclideanSpace ℝ (Fin d))).restrict K‖ := by
  set k : ℕ := Module.finrank ℤ Λ + 1 with hk
  obtain ⟨C, hC₀, hC⟩ := f.decay k 0
  have hC' (x : EuclideanSpace ℝ (Fin d)) : ‖x‖ ^ k * ‖f x‖ ≤ C := by
    simpa [norm_iteratedFDeriv_zero] using hC x
  obtain ⟨r, hrK⟩ := K.isCompact.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
  set R : ℝ := max (2 * max r 0) 1 with hR
  have hKr : (K : Set (EuclideanSpace ℝ (Fin d))) ⊆ Metric.closedBall 0 (max r 0) := fun x hx ↦
    Metric.closedBall_subset_closedBall (le_max_left r 0) (hrK hx)
  have hfin : {ℓ : Λ | ‖(ℓ : EuclideanSpace ℝ (Fin d))‖ ≤ R}.Finite := by
    have hcl : IsClosed (X := EuclideanSpace ℝ (Fin d)) (Λ : Set (EuclideanSpace ℝ (Fin d))) :=
      @AddSubgroup.isClosed_of_discrete _ _ _ _ _ Λ.toAddSubgroup
        (inferInstanceAs (DiscreteTopology Λ))
    refine ((Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin d))) (r := R))
      hcl).preimage_embedding (.subtype _)).subset fun ℓ hℓ ↦ ?_
    simpa [Metric.mem_closedBall, dist_eq_norm] using hℓ
  refine Summable.of_norm_bounded_eventually
    ((ZLattice.summable_norm_pow_inv (L := Λ) (n := k) (by simp [hk])).mul_left (C * 2 ^ k)) ?_
  filter_upwards [hfin.eventually_cofinite_notMem] with ℓ hℓ
  have hlt : R < ‖(ℓ : EuclideanSpace ℝ (Fin d))‖ := lt_of_not_ge (by simpa using hℓ)
  have hpos : 0 < ‖(ℓ : EuclideanSpace ℝ (Fin d))‖ :=
    lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans hlt.le)
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  refine (ContinuousMap.norm_le _ (by positivity)).2 ?_
  rintro ⟨x, hxK⟩
  have hxr : ‖x‖ ≤ max r 0 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hKr hxK
  have hhalf : 2⁻¹ * ‖(ℓ : EuclideanSpace ℝ (Fin d))‖ ≤ ‖x + (ℓ : EuclideanSpace ℝ (Fin d))‖ := by
    have htri : ‖(ℓ : EuclideanSpace ℝ (Fin d))‖ - ‖x‖ ≤ ‖x + (ℓ : EuclideanSpace ℝ (Fin d))‖ := by
      simpa [add_comm] using norm_sub_norm_le (ℓ : EuclideanSpace ℝ (Fin d)) (-x)
    have := (le_max_left (2 * max r 0) 1).trans_lt hlt
    linarith
  have hhalfpos : (0 : ℝ) < 2⁻¹ * ‖(ℓ : EuclideanSpace ℝ (Fin d))‖ := by positivity
  have hpowle : (2⁻¹ * ‖(ℓ : EuclideanSpace ℝ (Fin d))‖) ^ k ≤
      ‖x + (ℓ : EuclideanSpace ℝ (Fin d))‖ ^ k := pow_le_pow_left₀ hhalfpos.le hhalf k
  change ‖f (x + (ℓ : EuclideanSpace ℝ (Fin d)))‖ ≤ _
  calc ‖f (x + (ℓ : EuclideanSpace ℝ (Fin d)))‖
      ≤ C / ‖x + (ℓ : EuclideanSpace ℝ (Fin d))‖ ^ k :=
        (le_div_iff₀' (pow_pos (hhalfpos.trans_le hhalf) k)).2 (hC' _)
    _ ≤ C / (2⁻¹ * ‖(ℓ : EuclideanSpace ℝ (Fin d))‖) ^ k :=
        div_le_div_of_nonneg_left hC₀.le (pow_pos hhalfpos k) hpowle
    _ = C * 2 ^ k * ‖(ℓ : EuclideanSpace ℝ (Fin d))‖⁻¹ ^ k := by
        rw [show (2 : ℝ)⁻¹ * ‖(ℓ : EuclideanSpace ℝ (Fin d))‖ =
              (2 * ‖(ℓ : EuclideanSpace ℝ (Fin d))‖⁻¹)⁻¹ by rw [mul_inv, inv_inv],
          inv_pow, div_eq_mul_inv, inv_inv, mul_pow]
        ring

/-- The lattice translates of a Schwartz function are absolutely summable. -/
lemma summable_norm_translate (a : EuclideanSpace ℝ (Fin d)) :
    Summable fun ℓ : Λ ↦ ‖f (a + (ℓ : EuclideanSpace ℝ (Fin d)))‖ := by
  refine (summable_norm_restrict_translate Λ f ⟨{a}, isCompact_singleton⟩).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) fun ℓ ↦ ?_
  simpa using ((translate f (ℓ : EuclideanSpace ℝ (Fin d))).restrict
    (⟨{a}, isCompact_singleton⟩ : TopologicalSpace.Compacts _)).norm_coe_le_norm ⟨a, rfl⟩

end Translates

/-! ### The periodization of a Schwartz function and its Fourier coefficients -/

section Periodization

variable (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))

/-- The `ℤ^d`-periodization `x ↦ ∑' n : ℤ^d, f (x + n)` of a Schwartz function. -/
def periodization : C(EuclideanSpace ℝ (Fin d), ℂ) :=
  ∑' ℓ : referenceIntegerLattice d, translate f (ℓ : EuclideanSpace ℝ (Fin d))

lemma periodization_apply (x : EuclideanSpace ℝ (Fin d)) :
    periodization f x = ∑' ℓ : referenceIntegerLattice d, f (x + (ℓ : EuclideanSpace ℝ (Fin d))) :=
  (ContinuousMap.tsum_apply (ContinuousMap.summable_of_locally_summable_norm
    (summable_norm_restrict_translate (referenceIntegerLattice d) f)) x).symm

@[simp] lemma periodization_add_lattice (x : EuclideanSpace ℝ (Fin d))
    (ℓ₀ : referenceIntegerLattice d) : periodization f (x + ℓ₀) = periodization f x := by
  simpa [periodization_apply, add_assoc] using
    (Equiv.addLeft ℓ₀).tsum_eq fun ℓ ↦ f (x + (ℓ : EuclideanSpace ℝ (Fin d)))

lemma factorsThrough_periodization :
    Function.FactorsThrough (periodization f) (torusMkHom (d := d)) := by
  intro x y hxy
  obtain ⟨n, hn⟩ := exists_sub_eq_embeddedIntegerVector (x := x) (y := y) hxy
  have hx : x = y + embeddedIntegerVector n := by rw [← hn]; abel
  simpa [hx] using periodization_add_lattice f y
    ⟨embeddedIntegerVector n, embeddedIntegerVector_mem n⟩

/-- The periodization of `f`, viewed as a continuous function on the torus `(ℝ/ℤ)^d`. -/
def torusPeriodization : C(UnitAddTorus (Fin d), ℂ) :=
  isQuotientMap_torusMkHom.lift (periodization f) (factorsThrough_periodization f)

@[simp] lemma torusPeriodization_torusMk (x : EuclideanSpace ℝ (Fin d)) :
    torusPeriodization f (torusMk x) = periodization f x :=
  congrArg (fun g : C(EuclideanSpace ℝ (Fin d), ℂ) ↦ g x)
    (isQuotientMap_torusMkHom.lift_comp (periodization f) (factorsThrough_periodization f))

lemma norm_mFourier_mul_translate_le (n : Fin d → ℤ) (ℓ : referenceIntegerLattice d)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ halfOpenUnitCell (d := d)) :
    ‖UnitAddTorus.mFourier (-n) (torusMk x) * f (x + (ℓ : EuclideanSpace ℝ (Fin d)))‖ ≤
      ‖(translate f (ℓ : EuclideanSpace ℝ (Fin d))).restrict (ball (d := d))‖ := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (norm_mFourier_torusMk_le _ _)).trans
    (((translate f (ℓ : EuclideanSpace ℝ (Fin d))).restrict
      (ball (d := d) : Set (EuclideanSpace ℝ (Fin d)))).norm_coe_le_norm
      ⟨x, halfOpenUnitCell_subset_closedBall hx⟩)

lemma integrableOn_mFourier_mul_translate (n : Fin d → ℤ) (ℓ : referenceIntegerLattice d) :
    IntegrableOn (fun x ↦ UnitAddTorus.mFourier (-n) (torusMk x) *
      f (x + (ℓ : EuclideanSpace ℝ (Fin d)))) (halfOpenUnitCell (d := d)) volume :=
  Measure.integrableOn_of_bounded (s_finite := (measure_halfOpenUnitCell_lt_top (d := d)).ne)
    (M := ‖(translate f (ℓ : EuclideanSpace ℝ (Fin d))).restrict (ball (d := d))‖)
    (((UnitAddTorus.mFourier (-n)).continuous.comp continuous_torusMk).mul
      (f.continuous.comp (continuous_id.add continuous_const))).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_halfOpenUnitCell fun _ hx ↦
      norm_mFourier_mul_translate_le f n ℓ hx)

lemma summable_integral_norm_mFourier_mul_translate (n : Fin d → ℤ) :
    Summable fun ℓ : referenceIntegerLattice d ↦ ∫ x in halfOpenUnitCell,
      ‖UnitAddTorus.mFourier (-n) (torusMk x) * f (x + (ℓ : EuclideanSpace ℝ (Fin d)))‖ := by
  set μ : Measure (EuclideanSpace ℝ (Fin d)) := volume.restrict (halfOpenUnitCell (d := d))
    with hμ
  have : IsFiniteMeasure μ := ⟨by simpa [hμ] using measure_halfOpenUnitCell_lt_top (d := d)⟩
  refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun ℓ ↦ ?_)
    ((summable_norm_restrict_translate _ f (ball (d := d))).mul_left (μ.real Set.univ))
  have hle := integral_mono_of_nonneg (μ := μ) (ae_of_all _ fun _ ↦ norm_nonneg _)
    (integrable_const ‖(translate f (ℓ : EuclideanSpace ℝ (Fin d))).restrict (ball (d := d))‖)
    (ae_restrict_of_forall_mem measurableSet_halfOpenUnitCell fun _ hx ↦
      norm_mFourier_mul_translate_le f n ℓ hx)
  simpa [hμ, MeasureTheory.integral_const (μ := μ), smul_eq_mul, mul_comm] using hle

/-- Translating the domain of a set integral by `a`. -/
private lemma setIntegral_image_add_left (G : EuclideanSpace ℝ (Fin d) → ℂ)
    (a : EuclideanSpace ℝ (Fin d)) (s : Set (EuclideanSpace ℝ (Fin d))) :
    ∫ x in (fun y ↦ a + y) '' s, G x = ∫ x in s, G (a + x) := by
  rw [← (measurePreserving_add_left volume a).setIntegral_preimage_emb
    (measurableEmbedding_addLeft a), Set.preimage_image_eq _ (add_right_injective a)]

/-- The Fourier coefficients of the `ℤ^d`-periodization of `f` are the values of `𝓕 f` on `ℤ^d`. -/
lemma mFourierCoeff_torusPeriodization (n : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (torusPeriodization f) n = 𝓕 ⇑f (embeddedIntegerVector n) := by
  set χ : EuclideanSpace ℝ (Fin d) → ℂ := fun x ↦ UnitAddTorus.mFourier (-n) (torusMk x) with hχ
  set G : EuclideanSpace ℝ (Fin d) → ℂ := fun x ↦ χ x * f x with hG
  have hχcont : Continuous χ := (UnitAddTorus.mFourier (-n)).continuous.comp continuous_torusMk
  have hGint : Integrable G volume :=
    f.integrable.norm.mono' (hχcont.mul f.continuous).aestronglyMeasurable <| .of_forall fun x ↦
      (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (norm_mFourier_torusMk_le _ _))
  have hglobal : (∫ x : EuclideanSpace ℝ (Fin d), G x) =
      ∑' ℓ : referenceIntegerLattice d,
        ∫ x in halfOpenUnitCell, χ x * f (x + (ℓ : EuclideanSpace ℝ (Fin d))) := by
    have : VAddInvariantMeasure (referenceIntegerLattice d) (EuclideanSpace ℝ (Fin d)) volume :=
      (inferInstance : VAddInvariantMeasure (referenceIntegerLattice d).toAddSubgroup
        (EuclideanSpace ℝ (Fin d)) volume)
    rw [(isAddFundamentalDomain_halfOpenUnitCell (d := d)).integral_eq_tsum G hGint]
    refine tsum_congr fun ℓ ↦ ?_
    change (∫ x in (fun y ↦ (ℓ : EuclideanSpace ℝ (Fin d)) + y) '' halfOpenUnitCell, G x) = _
    rw [setIntegral_image_add_left]
    exact integral_congr_ae (.of_forall fun x ↦ by
      simp [hG, hχ, add_comm, mFourier_torusMk_add_lattice])
  calc UnitAddTorus.mFourierCoeff (torusPeriodization f) n
      = ∫ x in halfOpenUnitCell, χ x * periodization f x := by
        rw [UnitAddTorus.mFourierCoeff_eq_integral (⇑(torusPeriodization f)) n fun _ ↦ (0 : ℝ),
          integral_pi_eq_integral_cell fun y ↦ UnitAddTorus.mFourier (-n) y •
            torusPeriodization f y]
        exact integral_congr_ae (.of_forall fun x ↦ by simp [hχ, smul_eq_mul])
    _ = ∫ x in halfOpenUnitCell, ∑' ℓ : referenceIntegerLattice d,
          χ x * f (x + (ℓ : EuclideanSpace ℝ (Fin d))) :=
        integral_congr_ae (.of_forall fun x ↦ by
          dsimp only
          rw [periodization_apply, tsum_mul_left])
    _ = ∑' ℓ : referenceIntegerLattice d,
          ∫ x in halfOpenUnitCell, χ x * f (x + (ℓ : EuclideanSpace ℝ (Fin d))) :=
        (integral_tsum_of_summable_integral_norm
          (fun ℓ ↦ integrableOn_mFourier_mul_translate f n ℓ)
          (summable_integral_norm_mFourier_mul_translate f n)).symm
    _ = ∫ x : EuclideanSpace ℝ (Fin d), G x := hglobal.symm
    _ = 𝓕 ⇑f (embeddedIntegerVector n) := by
        rw [Real.fourier_eq']
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        simp only [hG, hχ, mFourier_torusMk, embeddedIntegerVector_neg, inner_neg_right,
          Real.fourierChar_apply, smul_eq_mul]
        congr 1
        push_cast
        ring_nf

/-- The Fourier coefficients of the `ℤ^d`-periodization of `f` are absolutely summable. -/
lemma summable_mFourierCoeff_torusPeriodization :
    Summable (UnitAddTorus.mFourierCoeff (torusPeriodization f)) := by
  have hlattice : Summable fun ℓ : referenceIntegerLattice d ↦
      ‖𝓕 ⇑f (ℓ : EuclideanSpace ℝ (Fin d))‖ := by
    simpa [FourierTransform.fourierCLE_apply, fourier_coe] using summable_norm_translate
      (referenceIntegerLattice d)
      (FourierTransform.fourierCLE ℂ (SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) f) 0
  refine Summable.of_norm ?_
  simpa [Function.comp_def, mFourierCoeff_torusPeriodization] using
    hlattice.comp_injective (integerVectorLatticeEquiv (d := d)).injective

/-- Poisson summation for the standard lattice `ℤ^d`. -/
theorem poissonSummation_referenceIntegerLattice (v : EuclideanSpace ℝ (Fin d)) :
    (∑' ℓ : referenceIntegerLattice d, f (v + (ℓ : EuclideanSpace ℝ (Fin d)))) =
      ∑' n : Fin d → ℤ, 𝓕 ⇑f (embeddedIntegerVector n) *
        Complex.exp (2 * π * I * ⟪v, embeddedIntegerVector n⟫_[ℝ]) := by
  simpa [periodization_apply, smul_eq_mul, mFourierCoeff_torusPeriodization,
    mFourier_torusMk_exp, mul_assoc, mul_left_comm, mul_comm] using
    (UnitAddTorus.hasSum_mFourier_series_apply_of_summable
      (f := torusPeriodization f) (summable_mFourierCoeff_torusPeriodization f)
      (torusMk v)).tsum_eq.symm

end Periodization

end PoissonSummation.Standard

/-! ### Transport to an arbitrary lattice -/

open Module PoissonSummation.Standard

/-- The polar (dual) lattice `{y | ∀ x ∈ L, ⟪x, y⟫ ∈ ℤ}` of a lattice `L ⊆ ℝ^d`. -/
abbrev polarIntegerLattice (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) :
    Submodule ℤ (EuclideanSpace ℝ (Fin d)) :=
  LinearMap.BilinForm.dualSubmodule
    (B := (innerₗ (EuclideanSpace ℝ (Fin d)) : LinearMap.BilinForm ℝ (EuclideanSpace ℝ (Fin d)))) L

section Lattice

variable (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology L] [IsZLattice ℝ L]

/-- A `ℤ`-basis of the lattice `L`, indexed by `Fin d`. -/
def integralLatticeBasis : Module.Basis (Fin d) ℤ L := by
  have : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  have hfinrank : Module.finrank ℤ L = d := (ZLattice.rank (K := ℝ) (L := L)).trans (by simp)
  exact (Module.Free.chooseBasis ℤ L).reindex (Fintype.equivOfCardEq (by
    simpa [hfinrank] using (Module.finrank_eq_card_chooseBasisIndex (R := ℤ) (M := L)).symm))

/-- The `ℤ`-basis `integralLatticeBasis L` of `L`, viewed as an `ℝ`-basis of `ℝ^d`. -/
def realLatticeBasis : Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
  (integralLatticeBasis L).ofZLatticeBasis ℝ L

/-- The standard orthonormal basis of `ℝ^d`, as a `Module.Basis`. -/
def referenceEuclideanBasis : Module.Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
  (EuclideanSpace.basisFun (Fin d) ℝ).toBasis

/-- The linear automorphism of `ℝ^d` sending the standard basis to a basis of `L`; it maps the
standard lattice `ℤ^d` onto `L`. -/
def latticeCoordinateEquiv : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
  referenceEuclideanBasis.equiv (realLatticeBasis L) (Equiv.refl (Fin d))

@[simp] lemma latticeCoordinateEquiv_referenceEuclideanBasis (i : Fin d) :
    latticeCoordinateEquiv L (referenceEuclideanBasis i) = realLatticeBasis L i :=
  referenceEuclideanBasis.equiv_apply (b' := realLatticeBasis L) (e := Equiv.refl _) i

/-- `latticeCoordinateEquiv L` maps the standard lattice `ℤ^d` onto `L`. -/
lemma map_referenceIntegerLattice :
    Submodule.map ((latticeCoordinateEquiv L).toLinearMap.restrictScalars ℤ)
      (referenceIntegerLattice d) = L := by
  have himage : (fun a ↦ latticeCoordinateEquiv L a) ''
      Set.range (referenceEuclideanBasis (d := d)) = Set.range (realLatticeBasis L) := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun i ↦ by simp [Function.comp])
  calc Submodule.map ((latticeCoordinateEquiv L).toLinearMap.restrictScalars ℤ)
        (referenceIntegerLattice d)
      = Submodule.span ℤ ((fun a ↦ latticeCoordinateEquiv L a) ''
          Set.range (referenceEuclideanBasis (d := d))) := by
        simp [referenceIntegerLattice, referenceEuclideanBasis, Submodule.map_span]
    _ = Submodule.span ℤ (Set.range (realLatticeBasis L)) := by rw [himage]
    _ = L := Module.Basis.ofZLatticeBasis_span (K := ℝ) (L := L) (b := integralLatticeBasis L)

/-- The covolume of `L` is the absolute value of the determinant of `latticeCoordinateEquiv L`. -/
lemma lattice_covolume_eq_coordinate_determinant : ZLattice.covolume L =
    |(LinearMap.det : (EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) →* ℝ)
      ((latticeCoordinateEquiv L).toLinearMap)| := by
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin d))).real
      (ZSpan.fundamentalDomain (referenceEuclideanBasis (d := d))) = 1 := by
    have hdomain : ZSpan.fundamentalDomain (referenceEuclideanBasis (d := d)) =
        (fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) ⁻¹'
          (Set.pi Set.univ fun _ : Fin d ↦ Set.Ico (0 : ℝ) 1) := by
      ext x; simp [ZSpan.mem_fundamentalDomain, referenceEuclideanBasis, Set.mem_pi]
    rw [Measure.real, hdomain, (PiLp.volume_preserving_ofLp (ι := Fin d)).measure_preimage
      (MeasurableSet.pi Set.countable_univ fun _ _ ↦ measurableSet_Ico).nullMeasurableSet,
      volume_pi, Measure.pi_pi]
    simp [Real.volume_Ico]
  have hbasis : ⇑(realLatticeBasis L) =
      fun i : Fin d ↦ ((integralLatticeBasis L i : L) : EuclideanSpace ℝ (Fin d)) :=
    funext fun i ↦ by simp [realLatticeBasis]
  have hdetA : (LinearMap.det : (EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) →* ℝ)
      ((latticeCoordinateEquiv L).toLinearMap) =
      (referenceEuclideanBasis (d := d)).det ⇑(realLatticeBasis L) := by
    simp [latticeCoordinateEquiv, referenceEuclideanBasis]
  have hcovol := ZLattice.covolume_eq_det_mul_measureReal (L := L) (b := integralLatticeBasis L)
    (b₀ := referenceEuclideanBasis (d := d)) (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
  rw [hvol, mul_one] at hcovol
  rw [hcovol, Function.comp_def, ← hbasis, ← hdetA]

/-- The adjoint of the inverse of `latticeCoordinateEquiv L`; it maps `ℤ^d` onto the polar
lattice of `L`. -/
def dualCoordinateTransport : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
  ((latticeCoordinateEquiv L).symm.toLinearMap).adjoint

/-- `dualCoordinateTransport L` as a linear equivalence, with inverse the adjoint of
`latticeCoordinateEquiv L`. -/
def dualAdjointCoordinateEquiv : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d) where
  __ := dualCoordinateTransport L
  invFun := ((latticeCoordinateEquiv L).toLinearMap).adjoint
  left_inv x := by
    have h : ((latticeCoordinateEquiv L).toLinearMap).adjoint ∘ₗ
        ((latticeCoordinateEquiv L).symm.toLinearMap).adjoint = LinearMap.id := by
      rw [← LinearMap.adjoint_comp]
      simp
    simpa [dualCoordinateTransport] using LinearMap.congr_fun h x
  right_inv x := by
    have h : ((latticeCoordinateEquiv L).symm.toLinearMap).adjoint ∘ₗ
        ((latticeCoordinateEquiv L).toLinearMap).adjoint = LinearMap.id := by
      rw [← LinearMap.adjoint_comp]
      simp
    simpa [dualCoordinateTransport] using LinearMap.congr_fun h x

/-- `dualCoordinateTransport L` maps the standard lattice `ℤ^d` onto the polar lattice of `L`. -/
lemma map_referenceIntegerLattice_dual :
    Submodule.map ((dualCoordinateTransport L).restrictScalars ℤ) (referenceIntegerLattice d) =
      polarIntegerLattice L := by
  have hdualStd : polarIntegerLattice (d := d) (referenceIntegerLattice d) =
      referenceIntegerLattice d := dualSubmodule_referenceIntegerLattice
  have hinnerL (y w : EuclideanSpace ℝ (Fin d)) :
      inner ℝ (dualCoordinateTransport L y) (latticeCoordinateEquiv L w) = inner ℝ y w := by
    simpa [dualCoordinateTransport] using LinearMap.adjoint_inner_left
      ((latticeCoordinateEquiv L).symm.toLinearMap) ((latticeCoordinateEquiv L) w) y
  have hinnerR (x w : EuclideanSpace ℝ (Fin d)) :
      inner ℝ (((latticeCoordinateEquiv L).toLinearMap.adjoint) x) w =
        inner ℝ x (latticeCoordinateEquiv L w) :=
    LinearMap.adjoint_inner_left ((latticeCoordinateEquiv L).toLinearMap) w x
  have hmapL (w : EuclideanSpace ℝ (Fin d)) (hw : w ∈ referenceIntegerLattice d) :
      (latticeCoordinateEquiv L) w ∈ L := by
    have hmem : (latticeCoordinateEquiv L) w ∈
        Submodule.map ((latticeCoordinateEquiv L).toLinearMap.restrictScalars ℤ)
          (referenceIntegerLattice d) := ⟨w, hw, rfl⟩
    rwa [map_referenceIntegerLattice] at hmem
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ z hz
    obtain ⟨w, hw, rfl⟩ : (z : EuclideanSpace ℝ (Fin d)) ∈
        Submodule.map ((latticeCoordinateEquiv L).toLinearMap.restrictScalars ℤ)
          (referenceIntegerLattice d) := by rw [map_referenceIntegerLattice]; exact hz
    have hy' : y ∈ polarIntegerLattice (d := d) (referenceIntegerLattice d) := by
      simpa [hdualStd] using hy
    simpa [innerₗ_apply_apply, hinnerL] using hy' w hw
  · intro hx
    refine ⟨((latticeCoordinateEquiv L).toLinearMap.adjoint) x, ?_, ?_⟩
    · have hy' : ((latticeCoordinateEquiv L).toLinearMap.adjoint) x ∈
          polarIntegerLattice (d := d) (referenceIntegerLattice d) := fun w hw ↦ by
        simpa [innerₗ_apply_apply, hinnerR] using hx _ (hmapL w hw)
      simpa [hdualStd] using hy'
    · exact (dualAdjointCoordinateEquiv L).right_inv x

/-- `latticeCoordinateEquiv L` restricts to an isomorphism `ℤ^d ≃ₗ[ℤ] L`. -/
def referenceLatticeEquiv : referenceIntegerLattice d ≃ₗ[ℤ] L :=
  (LinearEquiv.restrictScalars ℤ (latticeCoordinateEquiv L)).ofSubmodules _ _
    (map_referenceIntegerLattice L)

@[simp] lemma referenceLatticeEquiv_coe (x : referenceIntegerLattice d) :
    ((referenceLatticeEquiv L x : L) : EuclideanSpace ℝ (Fin d)) =
      latticeCoordinateEquiv L x := rfl

/-- Integer vectors parametrise the polar lattice of `L`. -/
def integerVectorPolarEquiv : (Fin d → ℤ) ≃ polarIntegerLattice (d := d) L :=
  integerVectorLatticeEquiv.trans
    (((LinearEquiv.restrictScalars ℤ (dualAdjointCoordinateEquiv L)).ofSubmodules _ _
      (map_referenceIntegerLattice_dual L)).toEquiv)

@[simp] lemma integerVectorPolarEquiv_coe (n : Fin d → ℤ) :
    ((integerVectorPolarEquiv L n : polarIntegerLattice (d := d) L) :
        EuclideanSpace ℝ (Fin d)) = dualCoordinateTransport L (embeddedIntegerVector n) := by
  simp [integerVectorPolarEquiv, dualAdjointCoordinateEquiv]

variable (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))

/-- The pullback of `f` along `latticeCoordinateEquiv L`; its `ℤ^d`-Poisson summation formula is
the `L`-Poisson summation formula for `f`. -/
def latticePullback : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (latticeCoordinateEquiv L).toContinuousLinearEquiv f

@[simp] lemma latticePullback_apply (x : EuclideanSpace ℝ (Fin d)) :
    latticePullback L f x = f (latticeCoordinateEquiv L x) := rfl

/-- `Real.fourier_comp_linearEquiv` for `latticeCoordinateEquiv L`: the Jacobian is the covolume. -/
lemma fourier_latticePullback (w : EuclideanSpace ℝ (Fin d)) : 𝓕 ⇑(latticePullback L f) w =
    ((ZLattice.covolume L)⁻¹ : ℝ) * 𝓕 ⇑f (dualCoordinateTransport L w) := by
  have h := Real.fourier_comp_linearEquiv (latticeCoordinateEquiv L) (⇑f) w
  rw [← lattice_covolume_eq_coordinate_determinant L] at h
  simpa [latticePullback, dualCoordinateTransport, Function.comp_def, Complex.real_smul] using h

lemma wInner_latticeCoordinateEquiv_symm (v w : EuclideanSpace ℝ (Fin d)) :
    ⟪(latticeCoordinateEquiv L).symm v, w⟫_[ℝ] = ⟪v, dualCoordinateTransport L w⟫_[ℝ] := by
  have h : inner ℝ ((latticeCoordinateEquiv L).symm v) w =
      inner ℝ v (dualCoordinateTransport L w) := by
    simpa [dualCoordinateTransport] using
      (LinearMap.adjoint_inner_right ((latticeCoordinateEquiv L).symm.toLinearMap) v w).symm
  simpa [RCLike.inner_eq_wInner_one] using h

end Lattice

/-- **Poisson summation** over a lattice `Λ ⊆ ℝ^d`: the sum of a Schwartz function over the
translated lattice `v + Λ` equals `(covolume Λ)⁻¹` times the sum of `𝓕 f` twisted by
`exp (2πi⟪v, ·⟫)` over the polar lattice of `Λ`. -/
theorem latticePoissonSummationFormula (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ)
    (v : EuclideanSpace ℝ (Fin d)) : ∑' ℓ : Λ, f (v + ℓ) = (1 / ZLattice.covolume Λ) *
      ∑' m : polarIntegerLattice (d := d) Λ, (𝓕 ⇑f m) *
        Complex.exp (2 * π * I * ⟪v, m⟫_[ℝ]) := by
  have hlhs : (∑' ℓ : referenceIntegerLattice d, latticePullback Λ f
      ((latticeCoordinateEquiv Λ).symm v + (ℓ : EuclideanSpace ℝ (Fin d)))) =
      ∑' ℓ : Λ, f (v + (ℓ : EuclideanSpace ℝ (Fin d))) := by
    calc (∑' ℓ : referenceIntegerLattice d, latticePullback Λ f
            ((latticeCoordinateEquiv Λ).symm v + (ℓ : EuclideanSpace ℝ (Fin d))))
        = ∑' ℓ : referenceIntegerLattice d,
            f (v + latticeCoordinateEquiv Λ (ℓ : EuclideanSpace ℝ (Fin d))) :=
          tsum_congr fun ℓ ↦ by simp [map_add]
      _ = ∑' ℓ : Λ, f (v + (ℓ : EuclideanSpace ℝ (Fin d))) := by
          simpa using (referenceLatticeEquiv Λ).toEquiv.tsum_eq
            fun ℓ : Λ ↦ f (v + (ℓ : EuclideanSpace ℝ (Fin d)))
  rw [← hlhs, poissonSummation_referenceIntegerLattice,
    ← (integerVectorPolarEquiv Λ).tsum_eq fun m ↦ 𝓕 ⇑f (m : EuclideanSpace ℝ (Fin d)) *
      Complex.exp (2 * π * I * ⟪v, (m : EuclideanSpace ℝ (Fin d))⟫_[ℝ]), ← tsum_mul_left]
  refine tsum_congr fun n ↦ ?_
  rw [fourier_latticePullback, wInner_latticeCoordinateEquiv_symm, integerVectorPolarEquiv_coe,
    one_div]
  push_cast
  ring

end SchwartzMap

end
