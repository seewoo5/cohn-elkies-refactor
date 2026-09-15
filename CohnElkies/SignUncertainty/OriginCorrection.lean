import CohnElkies.SignUncertainty.Mollifiers
import CohnElkies.Radial

/-! # Origin correction of anti-self-Fourier functions (Cohn–Gonçalves, Lemma 3.1)

The last paragraph of the proof of Lemma 3.1 of Cohn–Gonçalves, *An optimal uncertainty principle
in twelve dimensions via modular forms* (Invent. Math. 2019): an integrable `g` with `𝓕 g = -g`
pointwise (hence continuous), `g ≠ 0`, `g ≥ 0` outside the ball of radius `R > 0` and `g(0) ≥ 0`
is corrected at the origin without losing any of these properties. The tool is the Gaussian
difference (their (3.1))
```
  φ_t(x) = (e^{-tπ|x|²} - e^{-2tπ|x|²}) / (t^{-d/2} - (2t)^{-d/2}),   t > 0,
```
with `φ_t ≥ 0`, `φ_t(0) = 0`, `𝓕φ_t(0) = 1`, `𝓕𝓕φ_t = φ_t` and `𝓕φ_t(ξ) < 0` for
`|ξ|² > t d log 2 / π`. Choosing `t` with `t d log 2 / π = R²`, the function
`h = g + g(0) (φ_t - 𝓕φ_t)` satisfies `𝓕 h = -h`, `h(0) = 0`, `h ≥ 0` outside the ball of radius
`R` (so `r(h) ≤ R`) and `h ≠ 0` (`h = g` if `g(0) = 0`, and `h(x) > g(x) ≥ 0` for `|x| > R` if
`g(0) > 0`): `h ∈ 𝓔₋(d)` (`originCorrection`). This is the step of the existence proof for
extremizers of `A₋(d)` (Cohn–Gonçalves, Theorem 1.4) that forces the limit function to vanish at
the origin. -/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform Topology

variable {d : ℕ}

/-! ### Linearity of the Fourier transform of plain integrable functions -/

theorem fourier_add_apply {f g : Euclidean d → ℂ} (hf : Integrable f) (hg : Integrable g)
    (w : Euclidean d) : 𝓕 (fun x ↦ f x + g x) w = 𝓕 f w + 𝓕 g w := by
  simp only [Real.fourier_eq, smul_add]
  exact integral_add ((Real.fourierIntegral_convergent_iff w).2 hf)
    ((Real.fourierIntegral_convergent_iff w).2 hg)

theorem fourier_sub_apply {f g : Euclidean d → ℂ} (hf : Integrable f) (hg : Integrable g)
    (w : Euclidean d) : 𝓕 (fun x ↦ f x - g x) w = 𝓕 f w - 𝓕 g w := by
  simp only [Real.fourier_eq, smul_sub]
  exact integral_sub ((Real.fourierIntegral_convergent_iff w).2 hf)
    ((Real.fourierIntegral_convergent_iff w).2 hg)

/-- The Fourier transform of a real combination `(a G_p - b G_q) / c` of Gaussians
`G_b(x) = e^{-π b ‖x‖²}`, `p, q > 0`: by Gaussian duality `𝓕 G_b = b^{-d/2} G_{1/b}`. -/
theorem fourier_gaussianReal_combination {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (a b c : ℝ)
    (w : Euclidean d) :
    𝓕 (fun x ↦ (((a * gaussianReal p x - b * gaussianReal q x) / c : ℝ) : ℂ)) w =
      ((a * (p ^ (d / 2 : ℝ))⁻¹ * gaussianReal p⁻¹ w -
        b * (q ^ (d / 2 : ℝ))⁻¹ * gaussianReal q⁻¹ w) / c : ℝ) := by
  have h : (fun x : Euclidean d ↦ (((a * gaussianReal p x - b * gaussianReal q x) / c : ℝ) : ℂ)) =
      fun x ↦ ((c⁻¹ : ℝ) : ℂ) *
        ((a : ℂ) * (gaussianReal p x : ℂ) - (b : ℂ) * (gaussianReal q x : ℂ)) := by
    funext x
    push_cast
    ring
  rw [h, fourier_const_mul_apply,
    fourier_sub_apply ((integrable_ofReal_gaussianReal hp).const_mul _)
      ((integrable_ofReal_gaussianReal hq).const_mul _),
    fourier_const_mul_apply, fourier_const_mul_apply, fourier_gaussianReal hp,
    fourier_gaussianReal hq]
  push_cast
  ring

/-! ### The Gaussian difference `φ_t` (Cohn–Gonçalves (3.1)) -/

/-- The normalizing constant `t^{-d/2} - (2t)^{-d/2}` of `φ_t`. -/
def gaussianDifferenceDenom (d : ℕ) (t : ℝ) : ℝ :=
  (t ^ (d / 2 : ℝ))⁻¹ - ((2 * t) ^ (d / 2 : ℝ))⁻¹

theorem gaussianDifferenceDenom_pos (hd : 0 < d) {t : ℝ} (ht : 0 < t) :
    0 < gaussianDifferenceDenom d t := by
  have hd' : (0 : ℝ) < d / 2 := by positivity
  exact sub_pos.2 (inv_strictAnti₀ (Real.rpow_pos_of_pos ht _)
    (Real.rpow_lt_rpow ht.le (by linarith) hd'))

/-- Cohn–Gonçalves (3.1): the Gaussian difference
`φ_t(x) = (e^{-tπ|x|²} - e^{-2tπ|x|²}) / (t^{-d/2} - (2t)^{-d/2})`. -/
def gaussianDifference (d : ℕ) (t : ℝ) (x : Euclidean d) : ℝ :=
  (gaussianReal t x - gaussianReal (2 * t) x) / gaussianDifferenceDenom d t

/-- The Fourier transform of `φ_t`, explicitly:
`𝓕φ_t(ξ) = (t^{-d/2} e^{-π|ξ|²/t} - (2t)^{-d/2} e^{-π|ξ|²/(2t)}) / (t^{-d/2} - (2t)^{-d/2})`
(`fourier_gaussianDifference`). -/
def fourierGaussianDifference (d : ℕ) (t : ℝ) (ξ : Euclidean d) : ℝ :=
  ((t ^ (d / 2 : ℝ))⁻¹ * gaussianReal t⁻¹ ξ -
    ((2 * t) ^ (d / 2 : ℝ))⁻¹ * gaussianReal (2 * t)⁻¹ ξ) / gaussianDifferenceDenom d t

/-- `φ_t ≥ 0` for `t > 0`, `d ≥ 1`. -/
theorem gaussianDifference_nonneg (hd : 0 < d) {t : ℝ} (ht : 0 < t) (x : Euclidean d) :
    0 ≤ gaussianDifference d t x := by
  refine div_nonneg (sub_nonneg.2 ?_) (gaussianDifferenceDenom_pos hd ht).le
  refine Real.exp_le_exp.2 ?_
  have : 0 ≤ π * t * ‖x‖ ^ 2 := by positivity
  linarith

@[simp] theorem gaussianDifference_apply_zero (t : ℝ) : gaussianDifference d t 0 = 0 := by
  simp [gaussianDifference]

theorem continuous_gaussianDifference (t : ℝ) : Continuous (gaussianDifference d t) :=
  ((continuous_gaussianReal t).sub (continuous_gaussianReal _)).div_const _

theorem integrable_gaussianDifference {t : ℝ} (ht : 0 < t) :
    Integrable (gaussianDifference d t) :=
  ((integrable_gaussianReal ht).sub (integrable_gaussianReal (by positivity))).div_const _

theorem integrable_ofReal_gaussianDifference {t : ℝ} (ht : 0 < t) :
    Integrable fun x : Euclidean d ↦ (gaussianDifference d t x : ℂ) :=
  (integrable_gaussianDifference ht).ofReal

theorem isRadial_gaussianDifference (t : ℝ) : IsRadial (gaussianDifference d t) :=
  fun x y h ↦ by
    simp only [gaussianDifference, gaussianReal_eq_of_norm_eq _ x y h]

theorem continuous_fourierGaussianDifference (t : ℝ) :
    Continuous (fourierGaussianDifference d t) :=
  ((continuous_const.mul (continuous_gaussianReal _)).sub
    (continuous_const.mul (continuous_gaussianReal _))).div_const _

theorem integrable_fourierGaussianDifference {t : ℝ} (ht : 0 < t) :
    Integrable (fourierGaussianDifference d t) :=
  (((integrable_gaussianReal (inv_pos.2 ht)).const_mul _).sub
    ((integrable_gaussianReal (inv_pos.2 (by positivity))).const_mul _)).div_const _

theorem integrable_ofReal_fourierGaussianDifference {t : ℝ} (ht : 0 < t) :
    Integrable fun x : Euclidean d ↦ (fourierGaussianDifference d t x : ℂ) :=
  (integrable_fourierGaussianDifference ht).ofReal

theorem isRadial_fourierGaussianDifference (t : ℝ) :
    IsRadial (fourierGaussianDifference d t) :=
  fun x y h ↦ by
    simp only [fourierGaussianDifference, gaussianReal_eq_of_norm_eq _ x y h]

/-- `𝓕φ_t(ξ) = (t^{-d/2} e^{-π|ξ|²/t} - (2t)^{-d/2} e^{-π|ξ|²/(2t)}) / (t^{-d/2} - (2t)^{-d/2})`. -/
theorem fourier_gaussianDifference {t : ℝ} (ht : 0 < t) (ξ : Euclidean d) :
    𝓕 (fun x ↦ (gaussianDifference d t x : ℂ)) ξ = fourierGaussianDifference d t ξ := by
  have h := fourier_gaussianReal_combination (d := d) ht (by positivity : 0 < 2 * t) 1 1
    (gaussianDifferenceDenom d t) ξ
  simp only [one_mul] at h
  exact h

/-- `𝓕 (𝓕 φ_t) = φ_t`: the explicit transform is again a combination of Gaussians. -/
theorem fourier_fourierGaussianDifference {t : ℝ} (ht : 0 < t) (ξ : Euclidean d) :
    𝓕 (fun x ↦ (fourierGaussianDifference d t x : ℂ)) ξ = gaussianDifference d t ξ := by
  have h2t : 0 < 2 * t := by positivity
  have h := fourier_gaussianReal_combination (d := d) (inv_pos.2 ht) (inv_pos.2 h2t)
    (t ^ (d / 2 : ℝ))⁻¹ ((2 * t) ^ (d / 2 : ℝ))⁻¹ (gaussianDifferenceDenom d t) ξ
  rw [Real.inv_rpow ht.le, Real.inv_rpow h2t.le, inv_inv, inv_inv, inv_inv, inv_inv,
    inv_mul_cancel₀ (Real.rpow_pos_of_pos ht _).ne',
    inv_mul_cancel₀ (Real.rpow_pos_of_pos h2t _).ne', one_mul, one_mul] at h
  exact h

/-- `𝓕 (𝓕 φ_t) = φ_t` (`φ_t` is even). -/
theorem fourier_fourier_gaussianDifference {t : ℝ} (ht : 0 < t) (ξ : Euclidean d) :
    𝓕 (𝓕 (fun x ↦ (gaussianDifference d t x : ℂ))) ξ = gaussianDifference d t ξ := by
  have h : 𝓕 (fun x ↦ (gaussianDifference d t x : ℂ)) =
      fun x ↦ (fourierGaussianDifference d t x : ℂ) :=
    funext (fourier_gaussianDifference ht)
  rw [h, fourier_fourierGaussianDifference ht]

@[simp] theorem fourierGaussianDifference_apply_zero (hd : 0 < d) {t : ℝ} (ht : 0 < t) :
    fourierGaussianDifference d t 0 = 1 := by
  simp only [fourierGaussianDifference, gaussianReal_zero, mul_one]
  exact div_self (gaussianDifferenceDenom_pos hd ht).ne'

/-- `𝓕φ_t(0) = 1`. -/
theorem fourier_gaussianDifference_zero (hd : 0 < d) {t : ℝ} (ht : 0 < t) :
    𝓕 (fun x ↦ (gaussianDifference d t x : ℂ)) 0 = 1 := by
  rw [fourier_gaussianDifference ht, fourierGaussianDifference_apply_zero hd ht, Complex.ofReal_one]

/-- `t^{-d/2} e^{-π|ξ|²/t} = exp (-(d/2) log t - π|ξ|²/t)`. -/
theorem inv_rpow_mul_gaussianReal_inv {t : ℝ} (ht : 0 < t) (ξ : Euclidean d) :
    (t ^ (d / 2 : ℝ))⁻¹ * gaussianReal t⁻¹ ξ =
      Real.exp (-(Real.log t * (d / 2)) - π * t⁻¹ * ‖ξ‖ ^ 2) := by
  rw [gaussianReal, Real.rpow_def_of_pos ht, ← Real.exp_neg, ← Real.exp_add, sub_eq_add_neg]

/-- The sign condition of Cohn–Gonçalves: `t d log 2 / π < |ξ|²` forces
`t^{-d/2} e^{-π|ξ|²/t} < (2t)^{-d/2} e^{-π|ξ|²/(2t)}`. -/
theorem gaussianDifference_numerator_lt {t : ℝ} (ht : 0 < t) {ξ : Euclidean d}
    (h : t * d * Real.log 2 / π < ‖ξ‖ ^ 2) :
    (t ^ (d / 2 : ℝ))⁻¹ * gaussianReal t⁻¹ ξ <
      ((2 * t) ^ (d / 2 : ℝ))⁻¹ * gaussianReal (2 * t)⁻¹ ξ := by
  rw [inv_rpow_mul_gaussianReal_inv ht, inv_rpow_mul_gaussianReal_inv (by positivity),
    Real.exp_lt_exp, Real.log_mul two_ne_zero ht.ne']
  rw [div_lt_iff₀ Real.pi_pos] at h
  have key : π * t⁻¹ * ‖ξ‖ ^ 2 - π * (2 * t)⁻¹ * ‖ξ‖ ^ 2 = π * ‖ξ‖ ^ 2 / (2 * t) := by
    field_simp
    ring
  have : Real.log 2 * (d / 2) < π * t⁻¹ * ‖ξ‖ ^ 2 - π * (2 * t)⁻¹ * ‖ξ‖ ^ 2 := by
    rw [key, lt_div_iff₀ (by positivity)]
    linarith
  linarith

theorem gaussianDifference_numerator_le {t : ℝ} (ht : 0 < t) {ξ : Euclidean d}
    (h : t * d * Real.log 2 / π ≤ ‖ξ‖ ^ 2) :
    (t ^ (d / 2 : ℝ))⁻¹ * gaussianReal t⁻¹ ξ ≤
      ((2 * t) ^ (d / 2 : ℝ))⁻¹ * gaussianReal (2 * t)⁻¹ ξ := by
  rw [inv_rpow_mul_gaussianReal_inv ht, inv_rpow_mul_gaussianReal_inv (by positivity),
    Real.exp_le_exp, Real.log_mul two_ne_zero ht.ne']
  rw [div_le_iff₀ Real.pi_pos] at h
  have key : π * t⁻¹ * ‖ξ‖ ^ 2 - π * (2 * t)⁻¹ * ‖ξ‖ ^ 2 = π * ‖ξ‖ ^ 2 / (2 * t) := by
    field_simp
    ring
  have : Real.log 2 * (d / 2) ≤ π * t⁻¹ * ‖ξ‖ ^ 2 - π * (2 * t)⁻¹ * ‖ξ‖ ^ 2 := by
    rw [key, le_div_iff₀ (by positivity)]
    linarith
  linarith

/-- `𝓕φ_t(ξ) < 0` when `|ξ|² > t d log 2 / π` (Cohn–Gonçalves, proof of Lemma 3.1). -/
theorem fourierGaussianDifference_neg_of_lt (hd : 0 < d) {t : ℝ} (ht : 0 < t) {ξ : Euclidean d}
    (h : t * d * Real.log 2 / π < ‖ξ‖ ^ 2) : fourierGaussianDifference d t ξ < 0 :=
  div_neg_of_neg_of_pos (sub_neg.2 (gaussianDifference_numerator_lt ht h))
    (gaussianDifferenceDenom_pos hd ht)

/-- `𝓕φ_t(ξ) ≤ 0` when `|ξ|² ≥ t d log 2 / π`. -/
theorem fourierGaussianDifference_nonpos_of_le (hd : 0 < d) {t : ℝ} (ht : 0 < t)
    {ξ : Euclidean d} (h : t * d * Real.log 2 / π ≤ ‖ξ‖ ^ 2) :
    fourierGaussianDifference d t ξ ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (gaussianDifference_numerator_le ht h))
    (gaussianDifferenceDenom_pos hd ht).le

/-- `(𝓕φ_t)(ξ) < 0` when `|ξ|² > t d log 2 / π`, for the Fourier transform of `φ_t` as a complex
function. -/
theorem fourier_gaussianDifference_neg_of_lt (hd : 0 < d) {t : ℝ} (ht : 0 < t)
    {ξ : Euclidean d} (h : t * d * Real.log 2 / π < ‖ξ‖ ^ 2) :
    (𝓕 (fun x ↦ (gaussianDifference d t x : ℂ)) ξ).re < 0 := by
  rw [fourier_gaussianDifference ht, Complex.ofReal_re]
  exact fourierGaussianDifference_neg_of_lt hd ht h

theorem fourier_gaussianDifference_nonpos_of_le (hd : 0 < d) {t : ℝ} (ht : 0 < t)
    {ξ : Euclidean d} (h : t * d * Real.log 2 / π ≤ ‖ξ‖ ^ 2) :
    (𝓕 (fun x ↦ (gaussianDifference d t x : ℂ)) ξ).re ≤ 0 := by
  rw [fourier_gaussianDifference ht, Complex.ofReal_re]
  exact fourierGaussianDifference_nonpos_of_le hd ht h

/-! ### The perturbation `ψ_t = φ_t - 𝓕φ_t` -/

/-- `ψ_t = φ_t - 𝓕φ_t` (Cohn–Gonçalves, proof of Lemma 3.1 and §3.3): `𝓕ψ_t = -ψ_t`,
`ψ_t(0) = -1`, and `ψ_t > 0` outside the ball of radius `√(t d log 2 / π)`. -/
def gaussianPerturbation (d : ℕ) (t : ℝ) (x : Euclidean d) : ℝ :=
  gaussianDifference d t x - fourierGaussianDifference d t x

theorem continuous_gaussianPerturbation (t : ℝ) : Continuous (gaussianPerturbation d t) :=
  (continuous_gaussianDifference t).sub (continuous_fourierGaussianDifference t)

theorem integrable_gaussianPerturbation {t : ℝ} (ht : 0 < t) :
    Integrable (gaussianPerturbation d t) :=
  (integrable_gaussianDifference ht).sub (integrable_fourierGaussianDifference ht)

theorem integrable_ofReal_gaussianPerturbation {t : ℝ} (ht : 0 < t) :
    Integrable fun x : Euclidean d ↦ (gaussianPerturbation d t x : ℂ) :=
  (integrable_gaussianPerturbation ht).ofReal

theorem isRadial_gaussianPerturbation (t : ℝ) : IsRadial (gaussianPerturbation d t) :=
  fun x y h ↦ by
    simp only [gaussianPerturbation, isRadial_gaussianDifference t x y h,
      isRadial_fourierGaussianDifference t x y h]

@[simp] theorem gaussianPerturbation_apply_zero (hd : 0 < d) {t : ℝ} (ht : 0 < t) :
    gaussianPerturbation d t 0 = -1 := by
  simp [gaussianPerturbation, fourierGaussianDifference_apply_zero hd ht]

/-- `𝓕ψ_t = -ψ_t`. -/
theorem fourier_gaussianPerturbation {t : ℝ} (ht : 0 < t) (ξ : Euclidean d) :
    𝓕 (fun x ↦ (gaussianPerturbation d t x : ℂ)) ξ = -gaussianPerturbation d t ξ := by
  have h : (fun x ↦ (gaussianPerturbation d t x : ℂ)) =
      fun x ↦ (gaussianDifference d t x : ℂ) - (fourierGaussianDifference d t x : ℂ) := by
    funext x
    simp [gaussianPerturbation]
  rw [h, fourier_sub_apply (integrable_ofReal_gaussianDifference ht)
    (integrable_ofReal_fourierGaussianDifference ht), fourier_gaussianDifference ht,
    fourier_fourierGaussianDifference ht, gaussianPerturbation]
  push_cast
  ring

/-- `ψ_t > 0` when `|ξ|² > t d log 2 / π`. -/
theorem gaussianPerturbation_pos (hd : 0 < d) {t : ℝ} (ht : 0 < t) {x : Euclidean d}
    (h : t * d * Real.log 2 / π < ‖x‖ ^ 2) : 0 < gaussianPerturbation d t x :=
  sub_pos.2 ((fourierGaussianDifference_neg_of_lt hd ht h).trans_le
    (gaussianDifference_nonneg hd ht x))

/-- `ψ_t ≥ 0` when `|ξ|² ≥ t d log 2 / π`. -/
theorem gaussianPerturbation_nonneg (hd : 0 < d) {t : ℝ} (ht : 0 < t) {x : Euclidean d}
    (h : t * d * Real.log 2 / π ≤ ‖x‖ ^ 2) : 0 ≤ gaussianPerturbation d t x :=
  sub_nonneg_of_le ((fourierGaussianDifference_nonpos_of_le hd ht h).trans
    (gaussianDifference_nonneg hd ht x))

/-! ### Lemma 3.1: the origin correction -/

/-- The scale `t = π R² / (d log 2)` with `t d log 2 / π = R²`. -/
def originCorrectionScale (d : ℕ) (R : ℝ) : ℝ := π * R ^ 2 / (d * Real.log 2)

theorem originCorrectionScale_pos (hd : 0 < d) {R : ℝ} (hR : 0 < R) :
    0 < originCorrectionScale d R := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.2 hd
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  unfold originCorrectionScale
  positivity

theorem originCorrectionScale_mul (hd : 0 < d) (R : ℝ) :
    originCorrectionScale d R * d * Real.log 2 / π = R ^ 2 := by
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  unfold originCorrectionScale
  field_simp

/-- The corrected function `h = g + g(0) ψ_t`, `ψ_t = φ_t - 𝓕φ_t`, `t = π R² / (d log 2)`. -/
def originCorrectionFun (g : Euclidean d → ℝ) (R : ℝ) (x : Euclidean d) : ℝ :=
  g x + g 0 * gaussianPerturbation d (originCorrectionScale d R) x

/-- `h ≥ 0` outside the ball of radius `R`: all three terms `g`, `g(0) φ_t`, `-g(0) 𝓕φ_t` are. -/
theorem originCorrectionFun_nonneg_outside (hd : 0 < d) {g : Euclidean d → ℝ} {R : ℝ} (hR : 0 < R)
    (hpos : ∀ x : Euclidean d, R ≤ ‖x‖ → 0 ≤ g x) (h0 : 0 ≤ g 0) (x : Euclidean d)
    (hx : R ≤ ‖x‖) : 0 ≤ originCorrectionFun g R x := by
  refine add_nonneg (hpos x hx) (mul_nonneg h0 (gaussianPerturbation_nonneg hd
    (originCorrectionScale_pos hd hR) ?_))
  rw [originCorrectionScale_mul hd]
  exact pow_le_pow_left₀ hR.le hx 2

/-- `h(x) > g(x) ≥ 0` for `|x| > R` when `g(0) > 0`. -/
theorem originCorrectionFun_pos (hd : 0 < d) {g : Euclidean d → ℝ} {R : ℝ} (hR : 0 < R)
    (hpos : ∀ x : Euclidean d, R ≤ ‖x‖ → 0 ≤ g x) (h0 : 0 < g 0) (x : Euclidean d)
    (hx : R < ‖x‖) : 0 < originCorrectionFun g R x := by
  refine add_pos_of_nonneg_of_pos (hpos x hx.le) (mul_pos h0 (gaussianPerturbation_pos hd
    (originCorrectionScale_pos hd hR) ?_))
  rw [originCorrectionScale_mul hd]
  exact pow_lt_pow_left₀ hx hR.le two_ne_zero

section originCorrection

variable (hd : 0 < d) (g : Euclidean d → ℝ) (hint : Integrable g)
  (hfour : ∀ ξ : Euclidean d, 𝓕 (fun x ↦ (g x : ℂ)) ξ = -(g ξ : ℂ)) (hne : g ≠ 0) {R : ℝ}
  (hR : 0 < R) (hpos : ∀ x : Euclidean d, R ≤ ‖x‖ → 0 ≤ g x) (h0 : 0 ≤ g 0)

/-- Cohn–Gonçalves, proof of Lemma 3.1 (last paragraph): the corrected function
`h = g + g(0) (φ_t - 𝓕φ_t)`, `t d log 2 / π = R²`, is a sign eigenfunction of eigenvalue `-1`:
`𝓕 h = -h` (since `𝓕 g = -g`, `𝓕𝓕φ_t = φ_t`), `h(0) = g(0) + g(0)(0 - 1) = 0`, and `h ≠ 0`
(`h = g` if `g(0) = 0`; `h(x) > g(x) ≥ 0` for `|x| > R` if `g(0) > 0`). -/
def originCorrection : SignEigenfunction d (-1) where
  toFun := originCorrectionFun g R
  integrable := hint.add ((integrable_gaussianPerturbation
    (originCorrectionScale_pos hd hR)).const_mul _)
  fourier_eq ξ := by
    have ht := originCorrectionScale_pos hd hR
    have h : (fun x ↦ (originCorrectionFun g R x : ℂ)) = fun x ↦ (g x : ℂ) +
        (g 0 : ℂ) * (gaussianPerturbation d (originCorrectionScale d R) x : ℂ) := by
      funext x
      simp [originCorrectionFun]
    have hg : Integrable fun x : Euclidean d ↦ (g x : ℂ) := hint.ofReal
    rw [h, fourier_add_apply hg ((integrable_ofReal_gaussianPerturbation ht).const_mul _),
      fourier_const_mul_apply, fourier_gaussianPerturbation ht, hfour ξ, originCorrectionFun]
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
    push_cast
    ring
  ne_zero h := by
    rcases h0.lt_or_eq with h0' | h0'
    · set x : Euclidean d := (R + 1) • radialUnitDirection hd with hx
      have hxn : ‖x‖ = R + 1 := by
        rw [hx, norm_smul, norm_radialUnitDirection hd, mul_one, Real.norm_of_nonneg (by linarith)]
      have := originCorrectionFun_pos hd hR hpos h0' x (by rw [hxn]; linarith)
      rw [congrFun h x, Pi.zero_apply] at this
      exact lt_irrefl _ this
    · refine hne (funext fun x ↦ ?_)
      have := congrFun h x
      simpa [originCorrectionFun, ← h0'] using this
  zero := by
    simp [originCorrectionFun, gaussianPerturbation_apply_zero hd (originCorrectionScale_pos hd hR)]

theorem originCorrection_apply (x : Euclidean d) :
    originCorrection hd g hint hfour hne hR hpos h0 x =
      g x + g 0 * (gaussianDifference d (originCorrectionScale d R) x -
        fourierGaussianDifference d (originCorrectionScale d R) x) :=
  rfl

/-- `h(x) = g(x) + g(0) (φ_t(x) - 𝓕φ_t(x))`, with `𝓕φ_t` the Fourier transform of `φ_t` as a
complex function. -/
theorem originCorrection_apply_fourier (x : Euclidean d) :
    originCorrection hd g hint hfour hne hR hpos h0 x =
      g x + g 0 * (gaussianDifference d (originCorrectionScale d R) x -
        (𝓕 (fun y ↦ (gaussianDifference d (originCorrectionScale d R) y : ℂ)) x).re) := by
  rw [originCorrection_apply, fourier_gaussianDifference (originCorrectionScale_pos hd hR),
    Complex.ofReal_re]

/-- `h ≥ 0` outside the ball of radius `R`. -/
theorem originCorrection_nonneg_outside (x : Euclidean d) (hx : R ≤ ‖x‖) :
    0 ≤ originCorrection hd g hint hfour hne hR hpos h0 x :=
  originCorrectionFun_nonneg_outside hd hR hpos h0 x hx

/-- `r(h) ≤ R`. -/
theorem signRadius_originCorrection_le :
    signRadius (originCorrection hd g hint hfour hne hR hpos h0) ≤ ENNReal.ofReal R :=
  signRadius_le (R := Real.toNNReal R) fun x hx ↦
    originCorrection_nonneg_outside hd g hint hfour hne hR hpos h0 x
      ((Real.le_coe_toNNReal R).trans hx)

/-- `h = g` when `g(0) = 0`. -/
theorem originCorrection_eq_of_zero (h0' : g 0 = 0) :
    (originCorrection hd g hint hfour hne hR hpos h0 : Euclidean d → ℝ) = g :=
  funext fun x ↦ by simp [originCorrection_apply, h0']

end originCorrection

end

end CohnElkies
