import Mathlib

/-!
# The Fourier transform under a linear change of variables

`Real.fourier_comp_linearEquiv`: precomposing `f : V → E` with a linear equivalence
`A : W ≃ₗ[ℝ] V` of finite-dimensional real inner product spaces rescales `𝓕 f` by
`(LinearMap.normDet A)⁻¹` and precomposes it with the adjoint of `A⁻¹`. This generalises
`Real.fourier_comp_linearIsometry`, for which `LinearMap.normDet A = 1`.
`Real.fourier_comp_linearEquiv'` is the case `W = V`, where `LinearMap.normDet A = |det A|`.
-/

open MeasureTheory
open scoped FourierTransform Real
open Complex (I)

noncomputable section

namespace Real

variable {V W E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] [NormedAddCommGroup E]
  [NormedSpace ℂ E]

/-- Precomposing with a linear equivalence `A : W ≃ₗ[ℝ] V` rescales the Fourier transform by
`(LinearMap.normDet A)⁻¹` and precomposes it with the adjoint of `A⁻¹`. This generalises
`Real.fourier_comp_linearIsometry`, for which `LinearMap.normDet A = 1`; see
`Real.fourier_comp_linearEquiv'` for the case `W = V`. -/
theorem fourier_comp_linearEquiv (A : W ≃ₗ[ℝ] V) (f : V → E) (w : W) :
    𝓕 (f ∘ A) w = (A : W →ₗ[ℝ] V).normDet⁻¹ • 𝓕 f ((A.symm : V →ₗ[ℝ] W).adjoint w) := by
  have hpos : 0 < (A : W →ₗ[ℝ] V).normDet := by
    refine (LinearMap.normDet_nonneg _).lt_of_ne' ?_
    rw [Ne, LinearMap.normDet_eq_zero_iff_ker_ne_bot, not_not]
    exact LinearEquiv.ker A
  have hemb : MeasurableEmbedding A := A.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have hmap : Measure.map A (volume : Measure W) =
      ENNReal.ofReal (A : W →ₗ[ℝ] V).normDet⁻¹ • volume := by
    ext s _
    have h := (A : W →ₗ[ℝ] V).euclideanHausdorffMeasure_image_eq_normDet_mul_volume (A ⁻¹' s)
    rw [A.finrank_eq, InnerProductSpace.euclideanHausdorffMeasure_eq_volume, LinearEquiv.coe_coe,
      Set.image_preimage_eq s A.surjective] at h
    rw [hemb.map_apply, Measure.smul_apply, smul_eq_mul, h, ← mul_assoc,
      ENNReal.ofReal_inv_of_pos hpos,
      ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hpos).ne' ENNReal.ofReal_ne_top, one_mul]
  rw [fourier_eq', fourier_eq']
  set g : V → E := fun v ↦
    Complex.exp ((-2 * π * inner ℝ v ((A.symm : V →ₗ[ℝ] W).adjoint w) : ℝ) * I) • f v with hg
  have hcomp (x : W) : Complex.exp ((-2 * π * inner ℝ x w : ℝ) * I) • (f ∘ A) x = g (A x) := by
    simp [hg, LinearMap.adjoint_inner_right]
  simp only [hcomp]
  rw [← hemb.integral_map g, hmap, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.2 hpos.le)]

/-- The case `W = V` of `Real.fourier_comp_linearEquiv`: precomposing with a linear automorphism `A`
rescales the Fourier transform by `|det A|⁻¹` and precomposes it with the adjoint of `A⁻¹`. -/
theorem fourier_comp_linearEquiv' (A : V ≃ₗ[ℝ] V) (f : V → E) (w : V) :
    𝓕 (fun x ↦ f (A x)) w =
      |LinearMap.det (A : V →ₗ[ℝ] V)|⁻¹ • 𝓕 f ((A.symm : V ≃ₗ[ℝ] V).toLinearMap.adjoint w) := by
  rw [← LinearMap.normDet_eq_abs_det]
  exact fourier_comp_linearEquiv A f w

end Real

end
