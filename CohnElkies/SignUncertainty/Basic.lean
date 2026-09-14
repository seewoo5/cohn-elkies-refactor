import CohnElkies.Basic

/-! # The sign-uncertainty constants `A₊(d)`, `A₋(d)`: basic API

The objects of report (5)–(6) — the class `SignEigenfunction d ς` of nonzero real integrable `g`
with `𝓕 g = ς g` and `g(0) = 0`, the last-sign radius `signRadius g = r(g)` and the constants
`signUncertaintyConstant ς d = A_ς(d)` — are defined in the comparator block of `CohnElkies.Basic`.
This module provides their basic API: a sign eigenfunction is automatically continuous and bounded
(it is `ς` times the Fourier transform of an integrable function, i.e. its own Fourier-inversion
representative), its integral vanishes, and the elementary inequalities for `r(g)` and `A_ς(d)`. -/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory
open scoped ENNReal NNReal FourierTransform Topology

/-- `A₊(d)`: the sign-uncertainty constant of eigenvalue `+1` (report (6)). -/
scoped notation "A₊" => signUncertaintyConstant 1

/-- `A₋(d)`: the sign-uncertainty constant of eigenvalue `-1` (report (6)). -/
scoped notation "A₋" => signUncertaintyConstant (-1)

/-- `ς² = 1` for `ς ∈ {±1}`, as complex numbers. -/
theorem units_coe_mul_self (ς : ℤˣ) : ((ς : ℤ) : ℂ) * ((ς : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or ς with rfl | rfl <;> simp

theorem norm_units_coe (ς : ℤˣ) : ‖((ς : ℤ) : ℂ)‖ = 1 := by
  rcases Int.units_eq_one_or ς with rfl | rfl <;> simp

namespace SignEigenfunction

variable {d : ℕ} {ς : ℤˣ}

instance : CoeFun (SignEigenfunction d ς) fun _ ↦ Euclidean d → ℝ := ⟨toFun⟩

/-- The complex-valued function `x ↦ (g x : ℂ)` underlying a sign eigenfunction. -/
def toComplex (g : SignEigenfunction d ς) : Euclidean d → ℂ := fun x ↦ (g x : ℂ)

@[simp] theorem toComplex_apply (g : SignEigenfunction d ς) (x : Euclidean d) :
    g.toComplex x = (g x : ℂ) := rfl

theorem integrable_toComplex (g : SignEigenfunction d ς) : Integrable g.toComplex :=
  g.integrable.ofReal

/-- `𝓕 g = ς g` (the defining eigenvalue equation, report (6)). -/
theorem fourier_toComplex (g : SignEigenfunction d ς) (ξ : Euclidean d) :
    𝓕 g.toComplex ξ = ((ς : ℤ) : ℂ) * g ξ :=
  g.fourier_eq ξ

/-- `g = ς 𝓕 g`: a sign eigenfunction is the continuous Fourier-inversion representative of its
`L¹` class. -/
theorem coe_eq_fourier (g : SignEigenfunction d ς) (ξ : Euclidean d) :
    (g ξ : ℂ) = ((ς : ℤ) : ℂ) * 𝓕 g.toComplex ξ := by
  rw [fourier_toComplex, ← mul_assoc, units_coe_mul_self, one_mul]

theorem apply_eq_re_fourier (g : SignEigenfunction d ς) (ξ : Euclidean d) :
    g ξ = ((ς : ℤ) : ℝ) * (𝓕 g.toComplex ξ).re := by
  simpa using congrArg Complex.re (coe_eq_fourier g ξ)

theorem continuous_fourier_toComplex (g : SignEigenfunction d ς) : Continuous (𝓕 g.toComplex) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by exact continuous_inner)
    g.integrable_toComplex

/-- A sign eigenfunction is continuous (it is `ς` times the Fourier transform of an integrable
function). -/
protected theorem continuous (g : SignEigenfunction d ς) : Continuous g :=
  (continuous_const.mul (Complex.continuous_re.comp g.continuous_fourier_toComplex)).congr
    fun ξ ↦ (apply_eq_re_fourier g ξ).symm

theorem continuous_toComplex (g : SignEigenfunction d ς) : Continuous g.toComplex :=
  Complex.continuous_ofReal.comp g.continuous

/-- A sign eigenfunction is bounded by its `L¹` norm: `|g(x)| = |𝓕 g (x)| ≤ ‖g‖₁`. -/
theorem norm_apply_le (g : SignEigenfunction d ς) (x : Euclidean d) : ‖g x‖ ≤ ∫ y, ‖g y‖ := by
  rw [← Complex.norm_real, coe_eq_fourier, norm_mul, norm_units_coe, one_mul]
  refine (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ x).trans (le_of_eq ?_)
  simp

theorem bddAbove_range_norm (g : SignEigenfunction d ς) :
    BddAbove (Set.range fun x ↦ ‖g.toComplex x‖) :=
  ⟨∫ y, ‖g y‖, by rintro _ ⟨x, rfl⟩; simpa using g.norm_apply_le x⟩

/-- `∫ g = 𝓕 g (0) = ς g(0) = 0`. -/
theorem integral_toComplex (g : SignEigenfunction d ς) : ∫ x, g.toComplex x = 0 := by
  have h := g.fourier_toComplex 0
  rw [Real.fourier_eq'] at h
  simpa [g.zero] using h

theorem integral_eq_zero (g : SignEigenfunction d ς) : ∫ x, g x = 0 :=
  Complex.ofReal_eq_zero.1 (integral_complex_ofReal.symm.trans g.integral_toComplex)

/-- `∫ |g| > 0` for a (nonzero) sign eigenfunction. -/
theorem integral_norm_pos (g : SignEigenfunction d ς) : 0 < ∫ x, ‖g x‖ := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 g.ne_zero
  exact integral_pos_of_integrable_nonneg_nonzero g.continuous.norm g.integrable.norm
    (fun _ ↦ norm_nonneg _) (norm_ne_zero_iff.2 hx)

end SignEigenfunction

/-! ### The last-sign radius `r(g)` and the constants `A_ς(d)` -/

section signRadius

variable {d : ℕ}

theorem signRadius_le {g : Euclidean d → ℝ} {R : ℝ≥0}
    (hR : ∀ x : Euclidean d, (R : ℝ) ≤ ‖x‖ → 0 ≤ g x) : signRadius g ≤ R :=
  iInf_le (fun R : {R : ℝ≥0 // ∀ x : Euclidean d, (R : ℝ) ≤ ‖x‖ → 0 ≤ g x} ↦ (R : ℝ≥0∞)) ⟨R, hR⟩

theorem le_signRadius {g : Euclidean d → ℝ} {a : ℝ≥0∞}
    (h : ∀ R : ℝ≥0, (∀ x : Euclidean d, (R : ℝ) ≤ ‖x‖ → 0 ≤ g x) → a ≤ R) : a ≤ signRadius g :=
  le_iInf fun R ↦ h R.1 R.2

/-- If `g` fails to be nonnegative outside the ball of radius `R`, then `r(g) ≥ R`. -/
theorem le_signRadius_of_not_nonneg_outside {g : Euclidean d → ℝ} {R : ℝ}
    (h : ¬ ∀ x : Euclidean d, R ≤ ‖x‖ → 0 ≤ g x) : ENNReal.ofReal R ≤ signRadius g := by
  refine le_signRadius fun R' hR' ↦ ?_
  rw [ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top, ENNReal.coe_toReal]
  by_contra! hlt
  exact h fun x hx ↦ hR' x (hlt.le.trans hx)

/-- `r(h) ≤ r(g)` whenever every sign radius of `g` is a sign radius of `h` (e.g. for the
rotational average `h = Rg`, report §2.1). -/
theorem signRadius_le_signRadius {g h : Euclidean d → ℝ}
    (hgh : ∀ R : ℝ, (∀ x : Euclidean d, R ≤ ‖x‖ → 0 ≤ g x) →
      ∀ x : Euclidean d, R ≤ ‖x‖ → 0 ≤ h x) :
    signRadius h ≤ signRadius g :=
  le_signRadius fun R hR ↦ signRadius_le (hgh R hR)

theorem signUncertaintyConstant_le {ς : ℤˣ} (g : SignEigenfunction d ς) :
    signUncertaintyConstant ς d ≤ signRadius g :=
  iInf_le (fun g : SignEigenfunction d ς ↦ signRadius g.toFun) g

/-- If no sign eigenfunction is nonnegative outside the ball of radius `R`, then `A_ς(d) ≥ R`. -/
theorem le_signUncertaintyConstant {ς : ℤˣ} {R : ℝ}
    (h : ∀ g : SignEigenfunction d ς, ¬ ∀ x : Euclidean d, R ≤ ‖x‖ → 0 ≤ g x) :
    ENNReal.ofReal R ≤ signUncertaintyConstant ς d :=
  le_iInf fun g ↦ le_signRadius_of_not_nonneg_outside (h g)

end signRadius

end

end CohnElkies
