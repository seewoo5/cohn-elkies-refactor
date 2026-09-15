import CohnElkies.SignUncertainty.Basic
import CohnElkies.Radial
import CohnElkies.LowerBound.Balanced
import CohnElkies.Radialization
import CohnElkiesForMathlib.Analysis.Fourier.CompactSupport

/-! # Rotational averages of sign eigenfunctions (report §2.1)

The rotational average `ℛg(x) = ∫_{O(d)} g(U⁻¹x) dU` and its `L¹` theory are in
`CohnElkies.Radialization`. Here is what is specific to sign eigenfunctions: `ℛg ≠ 0` whenever `g`
is a nonzero eventually nonnegative Fourier eigenfunction, since otherwise `g` vanishes outside a
ball, its Fourier transform is entire along every ray
(`Real.fourierIntegral_eq_zero_of_eq_zero_outside_ball`, specialized to `ℝ^d` as
`fourier_eq_zero_of_eq_zero_outside`), and `𝓕 g = ς g` forces `g = 0`. The upshot is
`SignEigenfunction.radialize`: a radial sign eigenfunction with the same exterior sign condition,
and with `r(ℛg) ≤ r(g)` and `‖ℛg‖₁ ≤ ‖g‖₁`; hence the infimum defining `A_ς(d)` may be restricted
to radial eigenfunctions (`signUncertaintyConstant_eq_radial`).
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform Topology RealInnerProductSpace

variable {d : ℕ}

/-! ### Nonvanishing of the average of an eventually nonnegative eigenfunction

Report §2.1: if `ℛg = 0` and `g ≥ 0` outside a ball, then `g` vanishes outside that ball
(nonnegative continuous functions with zero spherical averages vanish); the Fourier transform of a
compactly supported integrable function is entire along every ray
(`CohnElkiesForMathlib.Analysis.Fourier.CompactSupport`), so `𝓕 g = ς g` vanishing outside the same
ball forces `𝓕 g = 0` and `g = 0`. -/

theorem eq_zero_of_rotationalAverage_eq_zero {g : Euclidean d → ℝ} (hg : Continuous g) {R : ℝ}
    (hR : ∀ x : Euclidean d, R ≤ ‖x‖ → 0 ≤ g x) (h0 : rotationalAverage g = 0)
    {x : Euclidean d} (hx : R ≤ ‖x‖) : g x = 0 := by
  set φ : OrthogonalGroup d → ℝ := fun U ↦ g (orthogonalAction U⁻¹ x) with hφdef
  have hφ : Continuous φ := hg.comp ((continuous_orthogonalAction x).comp continuous_inv)
  have hφ0 : 0 ≤ φ := fun U ↦ hR _ (by rw [norm_orthogonalAction]; exact hx)
  have hint : Integrable φ (radialOrthogonalHaar d) := integrable_comp_orthogonalAction_inv hg x
  have hzero : ∫ U, φ U ∂radialOrthogonalHaar d = 0 := congrFun h0 x
  have heq : φ = 0 := (hφ.ae_eq_iff_eq (radialOrthogonalHaar d) continuous_const).1
    ((integral_eq_zero_iff_of_nonneg hφ0 hint).1 hzero)
  simpa [hφdef] using congrFun heq 1

/-- `ℝ^d` is nontrivial for `d > 0`. -/
theorem nontrivial_euclidean (hd : 0 < d) : Nontrivial (Euclidean d) :=
  ⟨⟨radialUnitDirection hd, 0, fun h ↦ by simpa [h] using norm_radialUnitDirection hd⟩⟩

/-- Report §2.1: an integrable function vanishing outside a ball whose Fourier transform also
vanishes outside a ball has identically vanishing Fourier transform (`d ≥ 1`), since `𝓕 f` is
entire along every ray through the origin: the specialization to `ℝ^d` of
`Real.fourierIntegral_eq_zero_of_eq_zero_outside_ball`. -/
theorem fourier_eq_zero_of_eq_zero_outside (hd : 0 < d) {f : Euclidean d → ℂ} (hf : Integrable f)
    {R : ℝ} (hsupp : ∀ x : Euclidean d, R < ‖x‖ → f x = 0)
    (hfourier : ∀ x : Euclidean d, R < ‖x‖ → 𝓕 f x = 0) : 𝓕 f = 0 :=
  haveI := nontrivial_euclidean hd
  Real.fourierIntegral_eq_zero_of_eq_zero_outside_ball hf hsupp hfourier

/-- Report §2.1: the rotational average of a sign eigenfunction that is nonnegative outside a
ball does not vanish. -/
theorem SignEigenfunction.rotationalAverage_ne_zero (hd : 0 < d) {ς : ℤˣ}
    (g : SignEigenfunction d ς) {R : ℝ} (hR : ∀ x : Euclidean d, R ≤ ‖x‖ → 0 ≤ g x) :
    rotationalAverage (g : Euclidean d → ℝ) ≠ 0 := by
  intro h0
  have hvan : ∀ x : Euclidean d, R ≤ ‖x‖ → g x = 0 := fun x hx ↦
    eq_zero_of_rotationalAverage_eq_zero g.continuous hR h0 hx
  have hsupp : ∀ x : Euclidean d, R < ‖x‖ → g.toComplex x = 0 := fun x hx ↦ by
    simp [hvan x hx.le]
  have hfour : ∀ x : Euclidean d, R < ‖x‖ → 𝓕 g.toComplex x = 0 := fun x hx ↦ by
    rw [g.fourier_toComplex, hvan x hx.le]
    simp
  have hzero := fourier_eq_zero_of_eq_zero_outside hd g.integrable_toComplex hsupp hfour
  exact g.ne_zero (funext fun x ↦ by simpa [congrFun hzero x] using g.coe_eq_fourier x)

/-- The rotational average `ℛg` of a sign eigenfunction `g` nonnegative outside a ball, as a sign
eigenfunction (report §2.1: `𝓕(ℛg) = ς ℛg`, `ℛg(0) = g(0) = 0`, `ℛg ≠ 0`). -/
def SignEigenfunction.radialize (hd : 0 < d) {ς : ℤˣ} (g : SignEigenfunction d ς) {R : ℝ}
    (hR : ∀ x : Euclidean d, R ≤ ‖x‖ → 0 ≤ g x) : SignEigenfunction d ς where
  toFun := rotationalAverage (g : Euclidean d → ℝ)
  integrable := integrable_rotationalAverage g.continuous g.integrable
  fourier_eq ξ := by
    have h : (fun x ↦ ((rotationalAverage (g : Euclidean d → ℝ) x : ℝ) : ℂ)) =
        rotationalAverage g.toComplex :=
      funext fun x ↦ (rotationalAverage_ofReal g x).symm
    rw [h, fourier_rotationalAverage g.continuous_toComplex g.integrable_toComplex]
    unfold rotationalAverage
    simp only [g.fourier_toComplex]
    rw [integral_const_mul, integral_complex_ofReal]
  ne_zero := g.rotationalAverage_ne_zero hd hR
  zero := by rw [rotationalAverage_zero, g.zero]

namespace SignEigenfunction

variable (hd : 0 < d) {ς : ℤˣ} (g : SignEigenfunction d ς) {R : ℝ}
  (hR : ∀ x : Euclidean d, R ≤ ‖x‖ → 0 ≤ g x)

@[simp] theorem radialize_apply (x : Euclidean d) :
    g.radialize hd hR x = rotationalAverage (g : Euclidean d → ℝ) x :=
  rfl

theorem radialize_eq_of_norm_eq : IsRadial (g.radialize hd hR) :=
  rotationalAverage_eq_of_norm_eq _

theorem radialize_nonneg {x : Euclidean d} (hx : R ≤ ‖x‖) : 0 ≤ g.radialize hd hR x :=
  rotationalAverage_nonneg_of_norm_le hR hx

/-- `r(ℛg) ≤ r(g)`. -/
theorem signRadius_radialize_le : signRadius (g.radialize hd hR) ≤ signRadius g :=
  signRadius_le_signRadius fun _ hR' _ hx ↦ rotationalAverage_nonneg_of_norm_le hR' hx

/-- `‖ℛg‖₁ ≤ ‖g‖₁`. -/
theorem integral_norm_radialize_le : ∫ x, ‖g.radialize hd hR x‖ ≤ ∫ x, ‖g x‖ :=
  integral_norm_rotationalAverage_le g.continuous g.integrable

end SignEigenfunction

/-! ### Radial reduction for the sign-uncertainty constants -/

/-- A function with a finite last-sign radius really is nonnegative outside some ball: the
infimum defining `r(g)` is over a nonempty set of radii. -/
theorem exists_nonneg_outside_of_signRadius_lt_top {g : Euclidean d → ℝ} (h : signRadius g < ⊤) :
    ∃ R : ℝ, ∀ x : Euclidean d, R ≤ ‖x‖ → 0 ≤ g x := by
  by_contra hcon
  exact h.ne (top_le_iff.1 (le_signRadius fun R hR ↦ absurd ⟨(R : ℝ), hR⟩ hcon))

/-- Report §2.1: the infimum defining `A_ς(d)` may be taken over radial eigenfunctions only. -/
theorem signUncertaintyConstant_eq_radial (hd : 0 < d) (ς : ℤˣ) :
    signUncertaintyConstant ς d =
      ⨅ (g : SignEigenfunction d ς) (_ : IsRadial (g : Euclidean d → ℝ)), signRadius g := by
  refine le_antisymm (le_iInf₂ fun g _ ↦ signUncertaintyConstant_le g) (le_iInf fun g ↦ ?_)
  rcases eq_or_ne (signRadius (g : Euclidean d → ℝ)) ⊤ with htop | hne
  · rw [htop]
    exact le_top
  · obtain ⟨R, hR⟩ := exists_nonneg_outside_of_signRadius_lt_top (lt_top_iff_ne_top.2 hne)
    exact (iInf₂_le (g.radialize hd hR) (g.radialize_eq_of_norm_eq hd hR)).trans
      (g.signRadius_radialize_le hd hR)

end

end CohnElkies
