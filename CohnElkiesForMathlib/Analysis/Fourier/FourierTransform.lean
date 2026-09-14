import Mathlib

/-!
# The Fourier transform under a linear change of variables

`Real.fourier_comp_linearEquiv`: precomposing `f : V → ℂ` with a linear automorphism `A` of a
finite-dimensional real inner product space rescales `𝓕 f` by `|det A|⁻¹` and precomposes it with
the adjoint of `A⁻¹`. This generalises `Real.fourier_comp_linearIsometry`.
-/

open MeasureTheory
open scoped FourierTransform Real
open Complex (I)

noncomputable section

namespace Real

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- Precomposing with a linear equivalence `A` rescales the Fourier transform by `|det A|⁻¹` and
precomposes it with the adjoint of `A⁻¹`.  This generalises `Real.fourier_comp_linearIsometry`. -/
theorem fourier_comp_linearEquiv (A : V ≃ₗ[ℝ] V) (f : V → ℂ) (w : V) :
    𝓕 (fun x ↦ f (A x)) w =
      |LinearMap.det (A : V →ₗ[ℝ] V)|⁻¹ • 𝓕 f ((A.symm : V ≃ₗ[ℝ] V).toLinearMap.adjoint w) := by
  rw [Real.fourier_eq', Real.fourier_eq']
  set B : V →L[ℝ] V := A.toContinuousLinearEquiv.toContinuousLinearMap
  set g : V → ℂ := fun x ↦
    Complex.exp ((-2 * π * inner ℝ x ((A.symm : V ≃ₗ[ℝ] V).toLinearMap.adjoint w) : ℝ) * I) • f x
    with hg
  have hdetB : B.det = LinearMap.det (A : V →ₗ[ℝ] V) := rfl
  have hdet : LinearMap.det (A : V →ₗ[ℝ] V) ≠ 0 := A.isUnit_det'.ne_zero
  have hcomp (x : V) : Complex.exp ((-2 * π * inner ℝ x w : ℝ) * I) • f (A x) = g (A x) := by
    have h : inner ℝ (A x) ((A.symm : V ≃ₗ[ℝ] V).toLinearMap.adjoint w) = inner ℝ x w := by
      rw [LinearMap.adjoint_inner_right]
      simp
    simp [hg, h]
  have hchange : (∫ x : V, g x) = |LinearMap.det (A : V →ₗ[ℝ] V)| • ∫ x : V, g (A x) := by
    rw [← integral_smul]
    simpa [Set.image_univ, A.surjective.range_eq, hdetB] using
      MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure V)
        (s := Set.univ) (f := fun x : V ↦ A x) (f' := fun _ : V ↦ B) MeasurableSet.univ
        (fun _ _ ↦ B.hasFDerivAt.hasFDerivWithinAt) (Set.injOn_of_injective A.injective) g
  simp only [hcomp]
  rw [hchange, smul_smul, inv_mul_cancel₀ (abs_ne_zero.mpr hdet), one_smul]

end Real

end
