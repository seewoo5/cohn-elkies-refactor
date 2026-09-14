import Mathlib

/-!
# Integrability of the Fourier transform of a twice differentiable function

A function `g : ℝ → ℂ` with two integrable derivatives has an integrable Fourier transform, since
`𝓕 g (t) = O((1 + t²)⁻¹)` (`Real.integrable_fourierIntegral_of_deriv_deriv`).
-/

open MeasureTheory Real
open scoped FourierTransform
open Complex (I)

/-- A function with two integrable derivatives has an integrable Fourier transform: its transform
is `O((1 + t²)⁻¹)`. -/
theorem Real.integrable_fourierIntegral_of_deriv_deriv (g : ℝ → ℂ) (hg : Integrable g)
    (hgdiff : Differentiable ℝ g)
    (hg' : Integrable (deriv g))
    (hg'diff : Differentiable ℝ (deriv g))
    (hg'' : Integrable (deriv (deriv g))) :
    Integrable (𝓕 g : ℝ → ℂ) := by
  have hA : 0 ≤ ∫ v : ℝ, ‖g v‖ := integral_nonneg fun _ ↦ norm_nonneg _
  have hD : 0 ≤ ∫ v : ℝ, ‖deriv (deriv g) v‖ := integral_nonneg fun _ ↦ norm_nonneg _
  have hzero (t : ℝ) : ‖(𝓕 g : ℝ → ℂ) t‖ ≤ ∫ v : ℝ, ‖g v‖ :=
    VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume (innerₗ ℝ) g t
  have hsecond (t : ℝ) : (2 * π) ^ 2 * t ^ 2 * ‖(𝓕 g : ℝ → ℂ) t‖ ≤
      ∫ v : ℝ, ‖deriv (deriv g) v‖ := by
    have hident : (𝓕 (deriv (deriv g)) : ℝ → ℂ) t =
        (2 * (π : ℂ) * I * (t : ℂ)) ^ 2 * (𝓕 g : ℝ → ℂ) t := by
      rw [congrFun (Real.fourier_deriv hg' hg'diff hg'') t,
        congrFun (Real.fourier_deriv hg hgdiff hg') t]
      simp only [smul_eq_mul]
      ring
    have hcoef : ‖(2 * (π : ℂ) * I * (t : ℂ)) ^ 2‖ = (2 * π) ^ 2 * t ^ 2 := by
      rw [norm_pow, norm_mul, norm_mul, norm_mul, Complex.norm_two, Complex.norm_I, mul_one,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos pi_pos, mul_pow, sq_abs]
    calc (2 * π) ^ 2 * t ^ 2 * ‖(𝓕 g : ℝ → ℂ) t‖ = ‖(𝓕 (deriv (deriv g)) : ℝ → ℂ) t‖ := by
          rw [hident, norm_mul, hcoef]
      _ ≤ _ := VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
          (innerₗ ℝ) (deriv (deriv g)) t
  refine (integrable_inv_one_add_sq.const_mul ((∫ v : ℝ, ‖g v‖) +
    (∫ v : ℝ, ‖deriv (deriv g) v‖) / (2 * π) ^ 2)).mono'
      ((VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ hg).aestronglyMeasurable) (.of_forall fun t ↦ ?_)
  have hquadratic : t ^ 2 * ‖(𝓕 g : ℝ → ℂ) t‖ ≤ (∫ v : ℝ, ‖deriv (deriv g) v‖) / (2 * π) ^ 2 :=
    (le_div_iff₀ (by positivity)).2 (by nlinarith [hsecond t, pi_pos])
  change ‖(𝓕 g : ℝ → ℂ) t‖ ≤ ((∫ v : ℝ, ‖g v‖) +
    (∫ v : ℝ, ‖deriv (deriv g) v‖) / (2 * π) ^ 2) / (1 + t ^ 2)
  rw [le_div_iff₀ (by positivity)]
  nlinarith [hzero t, hquadratic, norm_nonneg ((𝓕 g : ℝ → ℂ) t)]
