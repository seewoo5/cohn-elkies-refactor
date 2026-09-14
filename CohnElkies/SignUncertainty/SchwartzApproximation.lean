import CohnElkies.SignUncertainty.Mollifiers

/-! # Schwartz approximation of radial `L¹` eigenfunctions (report §2.1)

For a radial sign eigenfunction `h` (`𝓕 h = ς h`, `h(0) = 0`) we construct real radial test
functions `g_n` with `𝓕 g_n = ς g_n`, `g_n(0) = 0` and `g_n → h` in `L¹`, following report §2.1:
* `q_n = (η_n h) ⋆ φ_n` is a test function (`schwartzConvolution`), real and radial, with
  `𝓕 q_n = ς (h ⋆ κ_n) 𝓕 φ_n` (convolution theorem, Gaussian duality `𝓕 κ_n = η_n` and Fourier
  inversion), and `q_n → h`, `𝓕 q_n → ς h` in `L¹` (`approximant`);
* `p_n = (q_n + ς 𝓕 q_n)/2` is a `ς`-eigenfunction with `p_n → h` in `L¹` and `p_n(0) → 0`
  (`projected`);
* `g_n = p_n - (p_n(0)/ψ(0)) ψ` for a fixed real radial `ς`-eigenfunction `ψ` with `ψ(0) ≠ 0`
  (`exists_eigenTest`; we use `ψ = P_ς(bump)` or `P_ς(bump(2·))` instead of the report's
  `ψ₊ = e^{-π|x|²}`, `ψ₋ = (|x|² - d/(4π)) e^{-π|x|²}`).
The report mollifies with the Gaussian `κ_n`; we mollify with the compactly supported bump `φ_n`
(see `CohnElkies.SignUncertainty.Mollifiers`). -/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform Topology Convolution

variable {d : ℕ}

theorem tendsto_integral_of_tendsto_integral_norm_sub {F : ℕ → Euclidean d → ℂ}
    {G : Euclidean d → ℂ} (hF : ∀ n, Integrable (F n)) (hG : Integrable G)
    (hlim : Tendsto (fun n ↦ ∫ x, ‖F n x - G x‖) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, F n x) atTop (𝓝 (∫ x, G x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) hlim
  rw [← integral_sub (hF n) hG]
  exact norm_integral_le_integral_norm _

theorem fourier_smul_testFunction (c : ℂ) (f : TestFunction d) :
    (𝓕 (c • f) : TestFunction d) = c • 𝓕 f :=
  map_smul _ _ _

theorem fourier_add_testFunction (f g : TestFunction d) :
    (𝓕 (f + g) : TestFunction d) = 𝓕 f + 𝓕 g :=
  map_add _ _ _

theorem fourier_sub_testFunction (f g : TestFunction d) :
    (𝓕 (f - g) : TestFunction d) = 𝓕 f - 𝓕 g :=
  map_sub _ _ _

variable {ς : ℤˣ} (h : SignEigenfunction d ς)

/-! ### The cutoff eigenfunction `H_n = η_n h` -/

/-- `H_n = η_n h` (complex-valued), report §2.1. -/
def cutoffEigen (n : ℕ) (x : Euclidean d) : ℂ := (gaussianCutoff n x : ℂ) * h x

theorem continuous_cutoffEigen (n : ℕ) : Continuous (cutoffEigen h n) :=
  (Complex.continuous_ofReal.comp (continuous_gaussianCutoff n)).mul h.continuous_toComplex

theorem cutoffEigen_eq_of_norm_eq (hrad : IsRadial h) (n : ℕ) : IsRadial (cutoffEigen h n) :=
  fun x y hxy ↦ by
    simp [cutoffEigen, gaussianCutoff_eq_of_norm_eq n _ _ hxy, hrad x y hxy]

theorem norm_cutoff_le (n : ℕ) (x : Euclidean d) : ‖(gaussianCutoff n x : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_of_nonneg (gaussianCutoff_nonneg n x)]
  exact gaussianCutoff_le_one n x

theorem integrable_cutoffEigen (n : ℕ) : Integrable (cutoffEigen h n) :=
  h.integrable_toComplex.bdd_mul (c := 1)
    (Complex.continuous_ofReal.comp (continuous_gaussianCutoff n)).aestronglyMeasurable
    (.of_forall fun x ↦ norm_cutoff_le n x)

/-- All moments of `η_n h` are integrable (the Gaussian cutoff beats every polynomial). -/
theorem integrable_pow_mul_norm_cutoffEigen (n k : ℕ) :
    Integrable fun a ↦ (1 + ‖a‖) ^ k * ‖cutoffEigen h n a‖ := by
  refine (h.integrable.norm.const_mul
    (Real.exp ((k : ℝ) ^ 2 / (4 * (π * ((n + 1 : ℝ) ^ 2)⁻¹))))).mono'
    (((continuous_const.add continuous_norm).pow k).mul
      (continuous_cutoffEigen h n).norm).aestronglyMeasurable (.of_forall fun a ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity), cutoffEigen, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (gaussianCutoff_nonneg n a), ← mul_assoc, Complex.norm_real]
  exact mul_le_mul_of_nonneg_right (pow_mul_gaussianCutoff_le n k a) (norm_nonneg _)

/-! ### The approximants `q_n = (η_n h) ⋆ φ_n` -/

/-- `q_n = (η_n h) ⋆ φ_n` (report §2.1, with the bump mollifier `φ_n`), as a test function. -/
def approximant (n : ℕ) : TestFunction d :=
  schwartzConvolution (cutoffEigen h n) (continuous_cutoffEigen h n).aestronglyMeasurable
    (integrable_pow_mul_norm_cutoffEigen h n) (bumpKernel n)

theorem approximant_apply (n : ℕ) (x : Euclidean d) :
    approximant h n x =
      (cutoffEigen h n ⋆[ContinuousLinearMap.mul ℂ ℂ] (bumpKernel n : Euclidean d → ℂ)) x :=
  schwartzConvolution_apply _ _ _ _ x

theorem approximant_real (n : ℕ) : IsRealValued (approximant h n) := fun x ↦ by
  rw [approximant_apply, convolution_def]
  have heq : (fun t ↦ (ContinuousLinearMap.mul ℂ ℂ) (cutoffEigen h n t) (bumpKernel n (x - t))) =
      fun t ↦ ((gaussianCutoff n t * h t * bumpKernelReal n (x - t) : ℝ) : ℂ) := by
    funext t
    simp [cutoffEigen, bumpKernel_apply]
  rw [heq, integral_complex_ofReal, Complex.ofReal_im]

theorem approximant_comp_isometry (hrad : IsRadial h) (n : ℕ)
    (A : Euclidean d ≃ₗᵢ[ℝ] Euclidean d) (x : Euclidean d) :
    approximant h n (A x) = approximant h n x := by
  rw [approximant_apply, approximant_apply, convolution_def, convolution_def]
  calc ∫ t, (ContinuousLinearMap.mul ℂ ℂ) (cutoffEigen h n t) (bumpKernel n (A x - t))
      = ∫ t, (ContinuousLinearMap.mul ℂ ℂ) (cutoffEigen h n (A t)) (bumpKernel n (A x - A t)) :=
        (A.measurePreserving.integral_comp A.toHomeomorph.measurableEmbedding
          fun t ↦ (ContinuousLinearMap.mul ℂ ℂ) (cutoffEigen h n t) (bumpKernel n (A x - t))).symm
    _ = ∫ t, (ContinuousLinearMap.mul ℂ ℂ) (cutoffEigen h n t) (bumpKernel n (x - t)) := by
        refine integral_congr_ae (.of_forall fun t ↦ ?_)
        dsimp only
        rw [← map_sub, cutoffEigen_eq_of_norm_eq h hrad n _ _ (A.norm_map t),
          bumpKernel_radial n _ _ (A.norm_map (x - t))]

theorem approximant_radial (hrad : IsRadial h) (n : ℕ) :
    IsRadial (approximant h n) := fun x y hxy ↦ by
  let A : Euclidean d ≃ₗᵢ[ℝ] Euclidean d := Submodule.reflection (ℝ ∙ (x - y))ᗮ
  have hA : A x = y := Submodule.reflection_sub hxy
  calc approximant h n x = approximant h n (A x) := (approximant_comp_isometry h hrad n A x).symm
    _ = approximant h n y := by rw [hA]

/-! ### The Fourier transform of `q_n` -/

/-- `h ⋆ κ_n`, the Gaussian smoothing of `h`. -/
def gaussianSmoothing (n : ℕ) : Euclidean d → ℂ :=
  h.toComplex ⋆[ContinuousLinearMap.mul ℂ ℂ] fun x ↦ (gaussianKernel n x : ℂ)

theorem integrable_gaussianSmoothing (n : ℕ) : Integrable (gaussianSmoothing h n) :=
  h.integrable_toComplex.integrable_convolution _ (integrable_gaussianKernel n).ofReal

theorem continuous_gaussianSmoothing (n : ℕ) : Continuous (gaussianSmoothing h n) :=
  BddAbove.continuous_convolution_right_of_integrable _
    ⟨(n + 1 : ℝ) ^ d, by
      rintro _ ⟨x, rfl⟩
      dsimp only
      rw [Complex.norm_real, Real.norm_of_nonneg (gaussianKernel_nonneg n x)]
      exact gaussianKernel_le n x⟩
    h.integrable_toComplex (Complex.continuous_ofReal.comp (continuous_gaussianKernel n))

/-- `𝓕 (h ⋆ κ_n) = 𝓕 h · 𝓕 κ_n = ς η_n h`. -/
theorem fourier_gaussianSmoothing (n : ℕ) (ξ : Euclidean d) :
    𝓕 (gaussianSmoothing h n) ξ = ((ς : ℤ) : ℂ) * cutoffEigen h n ξ :=
  calc 𝓕 (gaussianSmoothing h n) ξ
      = 𝓕 h.toComplex ξ * 𝓕 (fun x ↦ (gaussianKernel n x : ℂ)) ξ :=
        Real.fourier_mul_convolution_eq h.integrable_toComplex
          (integrable_gaussianKernel n).ofReal ξ
    _ = ((ς : ℤ) : ℂ) * cutoffEigen h n ξ := by
        rw [h.fourier_toComplex, fourier_gaussianKernel, cutoffEigen]
        ring

theorem integrable_fourier_gaussianSmoothing (n : ℕ) :
    Integrable (𝓕 (gaussianSmoothing h n)) :=
  ((integrable_cutoffEigen h n).const_mul _).congr
    (.of_forall fun ξ ↦ (fourier_gaussianSmoothing h n ξ).symm)

theorem gaussianSmoothing_neg (hrad : IsRadial h) (n : ℕ) (ξ : Euclidean d) :
    gaussianSmoothing h n (-ξ) = gaussianSmoothing h n ξ :=
  convolution_neg_of_neg_eq _ (.of_forall fun x ↦ by simp [hrad (-x) x (norm_neg x)])
    (.of_forall fun x ↦ by simp [gaussianKernel_neg])

/-- `𝓕 (η_n h) = ς (h ⋆ κ_n)`: Fourier inversion applied to `𝓕 (h ⋆ κ_n) = ς η_n h`. -/
theorem fourier_cutoffEigen (hrad : IsRadial h) (n : ℕ) (ξ : Euclidean d) :
    𝓕 (cutoffEigen h n) ξ = ((ς : ℤ) : ℂ) * gaussianSmoothing h n ξ := by
  have hH : cutoffEigen h n = fun x ↦ ((ς : ℤ) : ℂ) * 𝓕 (gaussianSmoothing h n) x := by
    funext x
    rw [fourier_gaussianSmoothing, ← mul_assoc, units_coe_mul_self, one_mul]
  rw [hH, fourier_const_mul_apply]
  congr 1
  calc 𝓕 (𝓕 (gaussianSmoothing h n)) ξ = 𝓕⁻ (𝓕 (gaussianSmoothing h n)) (-ξ) := by
        rw [Real.fourierInv_eq_fourier_neg, neg_neg]
    _ = gaussianSmoothing h n (-ξ) := by
        rw [(continuous_gaussianSmoothing h n).fourierInv_fourier_eq
          (integrable_gaussianSmoothing h n) (integrable_fourier_gaussianSmoothing h n)]
    _ = gaussianSmoothing h n ξ := gaussianSmoothing_neg h hrad n ξ

/-- `𝓕 q_n = ς (h ⋆ κ_n) 𝓕 φ_n` (report §2.1). -/
theorem fourier_approximant_apply (hrad : IsRadial h) (n : ℕ) (ξ : Euclidean d) :
    (𝓕 (approximant h n) : TestFunction d) ξ =
      ((ς : ℤ) : ℂ) * (gaussianSmoothing h n ξ * (𝓕 (bumpKernel n) : TestFunction d) ξ) := by
  have hq : (approximant h n : Euclidean d → ℂ) =
      cutoffEigen h n ⋆[ContinuousLinearMap.mul ℂ ℂ] (bumpKernel n : Euclidean d → ℂ) :=
    funext (approximant_apply h n)
  calc (𝓕 (approximant h n) : TestFunction d) ξ
      = 𝓕 (cutoffEigen h n ⋆[ContinuousLinearMap.mul ℂ ℂ] (bumpKernel n : Euclidean d → ℂ)) ξ := by
        rw [SchwartzMap.fourier_coe, hq]
    _ = 𝓕 (cutoffEigen h n) ξ * 𝓕 (bumpKernel n : Euclidean d → ℂ) ξ :=
        Real.fourier_mul_convolution_eq (integrable_cutoffEigen h n) (bumpKernel n).integrable ξ
    _ = ((ς : ℤ) : ℂ) * (gaussianSmoothing h n ξ * (𝓕 (bumpKernel n) : TestFunction d) ξ) := by
        rw [fourier_cutoffEigen h hrad n, SchwartzMap.fourier_coe, mul_assoc]

/-! ### `L¹` convergence of `q_n` and `𝓕 q_n` -/

/-- `q_n → h` in `L¹` (report §2.1). -/
theorem tendsto_approximant :
    Tendsto (fun n ↦ ∫ x, ‖approximant h n x - (h x : ℂ)‖) atTop (𝓝 0) := by
  simp_rw [approximant_apply]
  refine tendsto_integral_norm_convolution_sub_of_tendsto h.integrable_toComplex
    (integrable_cutoffEigen h) (fun n ↦ (bumpKernel n).integrable) integral_norm_bumpKernel ?_ ?_
  · exact tendsto_integral_norm_mul_sub h.integrable_toComplex
      (fun n ↦ (Complex.continuous_ofReal.comp (continuous_gaussianCutoff n)).aestronglyMeasurable)
      (fun n x ↦ norm_cutoff_le n x)
      (fun x ↦ by
        simpa [Function.comp_def] using
          (Complex.continuous_ofReal.tendsto 1).comp (tendsto_gaussianCutoff x))
  · simp_rw [bumpKernel_eq_scaledKernel]
    exact (tendsto_add_atTop_iff_nat 1).2 (tendsto_integral_norm_convolution_scaledKernel_sub
      h.integrable_toComplex (bumpUnit d).integrable (integral_bumpUnit d))

/-- `𝓕 q_n → ς h` in `L¹` (report §2.1). -/
theorem tendsto_fourier_approximant (hrad : IsRadial h) :
    Tendsto (fun n ↦ ∫ x, ‖(𝓕 (approximant h n) : TestFunction d) x - ((ς : ℤ) : ℂ) * h x‖)
      atTop (𝓝 0) := by
  have hsm : Tendsto (fun n ↦ ∫ x, ‖gaussianSmoothing h n x - h.toComplex x‖) atTop (𝓝 0) := by
    have heq : ∀ n, gaussianSmoothing h n = h.toComplex ⋆[ContinuousLinearMap.mul ℂ ℂ]
        scaledKernel (fun x ↦ (gaussianReal 1 x : ℂ)) (n + 1) := fun n ↦ by
      rw [gaussianSmoothing, gaussianKernel_eq_scaledKernel]
    simp_rw [heq]
    exact (tendsto_add_atTop_iff_nat 1).2 (tendsto_integral_norm_convolution_scaledKernel_sub
      h.integrable_toComplex (integrable_ofReal_gaussianReal one_pos)
      integral_ofReal_gaussianReal_one)
  have key := tendsto_integral_norm_mul_sub_of_tendsto (G := h.toComplex)
    (A := fun n ↦ gaussianSmoothing h n) (m := fun n ↦ (𝓕 (bumpKernel n) : TestFunction d))
    h.integrable_toComplex (integrable_gaussianSmoothing h)
    (fun n ↦ (𝓕 (bumpKernel n) : TestFunction d).continuous.aestronglyMeasurable)
    norm_fourier_bumpKernel_le tendsto_fourier_bumpKernel hsm
  refine key.congr' (.of_forall fun n ↦ integral_congr_ae (.of_forall fun x ↦ ?_))
  dsimp only
  rw [fourier_approximant_apply h hrad n x, ← mul_sub, norm_mul, norm_units_coe, one_mul]
  rfl

/-! ### The projections `p_n = (q_n + ς 𝓕 q_n)/2` -/

/-- `p_n = (q_n + ς 𝓕 q_n)/2` (report §2.1). -/
def projected (n : ℕ) : TestFunction d :=
  (2⁻¹ : ℂ) • (approximant h n + ((ς : ℤ) : ℂ) • 𝓕 (approximant h n))

theorem projected_apply (n : ℕ) (x : Euclidean d) :
    projected h n x = 2⁻¹ * (approximant h n x +
      ((ς : ℤ) : ℂ) * (𝓕 (approximant h n) : TestFunction d) x) := by
  simp only [projected, smul_apply, add_apply, smul_eq_mul]

theorem fourier_approximant_real (hrad : IsRadial h) (n : ℕ) :
    IsRealValued (𝓕 (approximant h n) : TestFunction d) :=
  (approximant_real h n).fourier_of_radial (approximant_radial h hrad n)

theorem projected_real (hrad : IsRadial h) (n : ℕ) : IsRealValued (projected h n) := fun x ↦ by
  rw [projected_apply]
  simp [Complex.mul_im, Complex.add_im, approximant_real h n x, fourier_approximant_real h hrad n x]

theorem projected_radial (hrad : IsRadial h) (n : ℕ) : IsRadial (projected h n) := fun x y hxy ↦ by
  rw [projected_apply, projected_apply, approximant_radial h hrad n x y hxy,
    (approximant_radial h hrad n).fourier x y hxy]

/-- `𝓕 p_n = ς p_n` (report §2.1). -/
theorem fourier_projected (hrad : IsRadial h) (n : ℕ) :
    (𝓕 (projected h n) : TestFunction d) = ((ς : ℤ) : ℂ) • projected h n := by
  have hsq : (𝓕 (𝓕 (approximant h n)) : TestFunction d) = approximant h n := by
    ext x
    rw [fourier_sq_apply]
    exact approximant_radial h hrad n _ _ (norm_neg x)
  have e1 : (𝓕 (projected h n) : TestFunction d) =
      (2⁻¹ : ℂ) • (𝓕 (approximant h n) + ((ς : ℤ) : ℂ) • 𝓕 (𝓕 (approximant h n))) := by
    rw [projected, fourier_smul_testFunction, fourier_add_testFunction, fourier_smul_testFunction]
  ext x
  rw [e1, hsq, smul_apply, add_apply, smul_apply, smul_apply, projected_apply]
  simp only [smul_eq_mul]
  linear_combination (-(2⁻¹ * (𝓕 (approximant h n) : TestFunction d) x)) * units_coe_mul_self ς

/-- `p_n(0) → 0`: `q_n(0) = ∫ 𝓕 q_n → ∫ ς h = 0` and `𝓕 q_n(0) = ∫ q_n → ∫ h = 0`. -/
theorem tendsto_projected_zero (hrad : IsRadial h) :
    Tendsto (fun n ↦ projected h n 0) atTop (𝓝 0) := by
  have h1 : ∀ n, approximant h n 0 = ∫ x, (𝓕 (approximant h n) : TestFunction d) x := fun n ↦ by
    have := fourier_sq_apply (approximant h n) 0
    rw [neg_zero] at this
    rw [← this, SchwartzMap.fourier_coe, fourier_zero_eq_integral]
  have h2 : ∀ n, (𝓕 (approximant h n) : TestFunction d) 0 = ∫ x, approximant h n x := fun n ↦ by
    rw [SchwartzMap.fourier_coe, fourier_zero_eq_integral]
  have hG : ∫ x, h.toComplex x = 0 := h.integral_toComplex
  have hq : Tendsto (fun n ↦ ∫ x, approximant h n x) atTop (𝓝 0) := by
    have := tendsto_integral_of_tendsto_integral_norm_sub (fun n ↦ (approximant h n).integrable)
      h.integrable_toComplex (tendsto_approximant h)
    rwa [hG] at this
  have hfq : Tendsto (fun n ↦ ∫ x, (𝓕 (approximant h n) : TestFunction d) x) atTop (𝓝 0) := by
    have := tendsto_integral_of_tendsto_integral_norm_sub
      (fun n ↦ (𝓕 (approximant h n) : TestFunction d).integrable)
      (h.integrable_toComplex.const_mul ((ς : ℤ) : ℂ)) (tendsto_fourier_approximant h hrad)
    rwa [integral_const_mul, hG, mul_zero] at this
  have heq : (fun n ↦ projected h n 0) = fun n ↦ 2⁻¹ *
      ((∫ x, (𝓕 (approximant h n) : TestFunction d) x) +
        ((ς : ℤ) : ℂ) * ∫ x, approximant h n x) := by
    funext n
    rw [projected_apply, h1, h2]
  rw [heq]
  simpa using (hfq.add (hq.const_mul _)).const_mul (2⁻¹ : ℂ)

/-- `p_n → h` in `L¹` (report §2.1). -/
theorem tendsto_projected (hrad : IsRadial h) :
    Tendsto (fun n ↦ ∫ x, ‖projected h n x - (h x : ℂ)‖) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n ↦ 2⁻¹ * ((∫ x, ‖approximant h n x - (h x : ℂ)‖) +
      ∫ x, ‖(𝓕 (approximant h n) : TestFunction d) x - ((ς : ℤ) : ℂ) * h x‖)) atTop (𝓝 0) := by
    simpa using ((tendsto_approximant h).add (tendsto_fourier_approximant h hrad)).const_mul
      (2⁻¹ : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n ↦ integral_nonneg fun _ ↦ norm_nonneg _) fun n ↦ ?_
  have h1 : Integrable fun x ↦ approximant h n x - (h x : ℂ) :=
    (approximant h n).integrable.sub h.integrable_toComplex
  have h2 : Integrable fun x ↦ (𝓕 (approximant h n) : TestFunction d) x - ((ς : ℤ) : ℂ) * h x :=
    (𝓕 (approximant h n) : TestFunction d).integrable.sub (h.integrable_toComplex.const_mul _)
  calc ∫ x, ‖projected h n x - (h x : ℂ)‖
      ≤ ∫ x, 2⁻¹ * (‖approximant h n x - (h x : ℂ)‖ +
          ‖(𝓕 (approximant h n) : TestFunction d) x - ((ς : ℤ) : ℂ) * h x‖) := by
        refine integral_mono_of_nonneg (.of_forall fun _ ↦ norm_nonneg _)
          ((h1.norm.add h2.norm).const_mul _) (.of_forall fun x ↦ ?_)
        dsimp only
        rw [projected_apply]
        have hx : (2⁻¹ : ℂ) * (approximant h n x +
            ((ς : ℤ) : ℂ) * (𝓕 (approximant h n) : TestFunction d) x) - h x =
            2⁻¹ * ((approximant h n x - h x) + ((ς : ℤ) : ℂ) *
              ((𝓕 (approximant h n) : TestFunction d) x - ((ς : ℤ) : ℂ) * h x)) := by
          linear_combination (2⁻¹ * (h x : ℂ)) * units_coe_mul_self ς
        rw [hx, norm_mul, norm_inv, Complex.norm_two]
        gcongr
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_units_coe, one_mul]
    _ = 2⁻¹ * ((∫ x, ‖approximant h n x - (h x : ℂ)‖) +
          ∫ x, ‖(𝓕 (approximant h n) : TestFunction d) x - ((ς : ℤ) : ℂ) * h x‖) := by
        rw [integral_const_mul, integral_add h1.norm h2.norm]

/-! ### The eigenfunction corrector `ψ_ς` -/

/-- `P_ς φ = φ + ς 𝓕 φ`: for radial `φ` this is (twice) the projection onto the
`ς`-eigenspace of `𝓕`. -/
def eigenProjection (ς : ℤˣ) (φ : TestFunction d) : TestFunction d := φ + ((ς : ℤ) : ℂ) • 𝓕 φ

theorem eigenProjection_apply (φ : TestFunction d) (x : Euclidean d) :
    eigenProjection ς φ x = φ x + ((ς : ℤ) : ℂ) * (𝓕 φ : TestFunction d) x := by
  simp [eigenProjection, add_apply, smul_apply]

theorem fourier_eigenProjection {φ : TestFunction d} (hφ : IsRadial φ) :
    (𝓕 (eigenProjection ς φ) : TestFunction d) = ((ς : ℤ) : ℂ) • eigenProjection ς φ := by
  have hsq : (𝓕 (𝓕 φ) : TestFunction d) = φ := by
    ext x
    rw [fourier_sq_apply]
    exact hφ _ _ (norm_neg x)
  have e1 : (𝓕 (eigenProjection ς φ) : TestFunction d) = 𝓕 φ + ((ς : ℤ) : ℂ) • 𝓕 (𝓕 φ) := by
    rw [eigenProjection, fourier_add_testFunction, fourier_smul_testFunction]
  ext x
  rw [e1, hsq, add_apply, smul_apply, smul_apply, eigenProjection_apply]
  simp only [smul_eq_mul]
  linear_combination (-((𝓕 φ : TestFunction d) x)) * units_coe_mul_self ς

theorem eigenProjection_real {φ : TestFunction d} (hr : IsRealValued φ) (hφ : IsRadial φ) :
    IsRealValued (eigenProjection ς φ) := fun x ↦ by
  rw [eigenProjection_apply]
  simp [Complex.add_im, Complex.mul_im, hr x, hr.fourier_of_radial hφ x]

theorem eigenProjection_radial {φ : TestFunction d} (hφ : IsRadial φ) :
    IsRadial (eigenProjection ς φ) := fun x y hxy ↦ by
  rw [eigenProjection_apply, eigenProjection_apply, hφ x y hxy, hφ.fourier x y hxy]

/-- A real radial test function `ψ` with `𝓕 ψ = ς ψ` and `ψ(0) ≠ 0` (the corrector `ψ_ς` of
report §2.1): `P_ς(bump)` or `P_ς(bump(2·))`, at least one of which does not vanish at `0`
since `𝓕 bump (0) = ∫ bump > 0` and `2^{-d} ≠ 1`. -/
theorem exists_eigenTest (hd : 0 < d) (ς : ℤˣ) :
    ∃ ψ : TestFunction d, IsRealValued ψ ∧ IsRadial ψ ∧
      (𝓕 ψ : TestFunction d) = ((ς : ℤ) : ℂ) • ψ ∧ ψ 0 ≠ 0 := by
  set B : ℝ := ∫ x, bumpReal d x with hBdef
  by_cases h1 : eigenProjection ς (bump d) 0 = 0
  · refine ⟨eigenProjection ς (dilate (bump d) 2 two_pos),
      eigenProjection_real ((bump_real d).dilate 2 two_pos) ((bump_radial d).dilate 2 two_pos),
      eigenProjection_radial ((bump_radial d).dilate 2 two_pos),
      fourier_eigenProjection ((bump_radial d).dilate 2 two_pos), fun h2 ↦ ?_⟩
    rw [eigenProjection_apply, fourier_dilate_zero, dilate_zero, Complex.real_smul] at h2
    rw [eigenProjection_apply] at h1
    have hF : (𝓕 (bump d) : TestFunction d) 0 = (B : ℂ) := by
      rw [SchwartzMap.fourier_coe, fourier_zero_eq_integral, hBdef, ← integral_complex_ofReal]
      rfl
    rw [hF] at h1 h2
    have hς : ((ς : ℤ) : ℂ) ≠ 0 := by rcases Int.units_eq_one_or ς with rfl | rfl <;> simp
    have hB : (B : ℂ) ≠ 0 := by
      exact_mod_cast (hBdef ▸ integral_bumpReal_pos d : (0 : ℝ) < B).ne'
    have hc : (1 : ℂ) - (((2 : ℝ) ^ d)⁻¹ : ℝ) ≠ 0 := by
      rw [sub_ne_zero]
      have : ((2 : ℝ) ^ d)⁻¹ ≠ 1 := by
        rw [ne_eq, inv_eq_one]
        exact (one_lt_pow₀ one_lt_two hd.ne').ne'
      exact_mod_cast this.symm
    have key : ((ς : ℤ) : ℂ) * (B : ℂ) * ((1 : ℂ) - (((2 : ℝ) ^ d)⁻¹ : ℝ)) = 0 := by
      linear_combination h1 - h2
    exact mul_ne_zero (mul_ne_zero hς hB) hc key
  · exact ⟨eigenProjection ς (bump d), eigenProjection_real (bump_real d) (bump_radial d),
      eigenProjection_radial (bump_radial d), fourier_eigenProjection (bump_radial d), h1⟩

/-! ### The approximation theorem -/

/-- Report §2.1: a radial sign eigenfunction `h` (`𝓕 h = ς h`, `h(0) = 0`) is the `L¹` limit of
real radial test functions `g_n` with `𝓕 g_n = ς g_n` and `g_n(0) = 0`. -/
theorem exists_schwartz_approximation (hd : 0 < d) (h : SignEigenfunction d ς) (hrad : IsRadial h) :
    ∃ q : ℕ → TestFunction d, (∀ n, IsRealValued (q n) ∧ IsRadial (q n) ∧
      (𝓕 (q n) : TestFunction d) = ((ς : ℤ) : ℂ) • q n ∧ q n 0 = 0) ∧
      Tendsto (fun n ↦ ∫ x, ‖q n x - (h x : ℂ)‖) atTop (𝓝 0) := by
  obtain ⟨ψ, hψr, hψrad, hψf, hψ0⟩ := exists_eigenTest hd ς
  refine ⟨fun n ↦ projected h n - (projected h n 0 / ψ 0) • ψ, fun n ↦ ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x
    simp [sub_apply, smul_apply, Complex.sub_im, Complex.mul_im, Complex.div_im,
      projected_real h hrad n x, projected_real h hrad n 0, hψr 0, hψr x]
  · intro x y hxy
    simp only [sub_apply, smul_apply, projected_radial h hrad n x y hxy, hψrad x y hxy]
  · have e1 : (𝓕 (projected h n - (projected h n 0 / ψ 0) • ψ) : TestFunction d) =
        𝓕 (projected h n) - (projected h n 0 / ψ 0) • 𝓕 ψ := by
      rw [fourier_sub_testFunction, fourier_smul_testFunction]
    rw [e1, fourier_projected h hrad, hψf, smul_sub, smul_comm]
  · simp only [sub_apply, smul_apply, smul_eq_mul]
    rw [div_mul_cancel₀ _ hψ0, sub_self]
  · have hc : Tendsto (fun n ↦ projected h n 0 / ψ 0) atTop (𝓝 0) := by
      simpa using (tendsto_projected_zero h hrad).div_const (ψ 0)
    have hlim : Tendsto (fun n ↦ (∫ x, ‖projected h n x - (h x : ℂ)‖) +
        ‖projected h n 0 / ψ 0‖ * ∫ x, ‖ψ x‖) atTop (𝓝 0) := by
      simpa using (tendsto_projected h hrad).add (hc.norm.mul_const (∫ x, ‖ψ x‖))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n ↦ integral_nonneg fun _ ↦ norm_nonneg _) fun n ↦ ?_
    have h1 : Integrable fun x ↦ projected h n x - (h x : ℂ) :=
      (projected h n).integrable.sub h.integrable_toComplex
    have h2 : Integrable fun x ↦ (projected h n 0 / ψ 0) * ψ x := ψ.integrable.const_mul _
    calc ∫ x, ‖(projected h n - (projected h n 0 / ψ 0) • ψ) x - (h x : ℂ)‖
        ≤ ∫ x, (‖projected h n x - (h x : ℂ)‖ + ‖(projected h n 0 / ψ 0) * ψ x‖) := by
          refine integral_mono_of_nonneg (.of_forall fun _ ↦ norm_nonneg _) (h1.norm.add h2.norm)
            (.of_forall fun x ↦ ?_)
          dsimp only
          rw [sub_apply, smul_apply, smul_eq_mul, sub_right_comm]
          exact norm_sub_le _ _
      _ = (∫ x, ‖projected h n x - (h x : ℂ)‖) + ∫ x, ‖(projected h n 0 / ψ 0) * ψ x‖ :=
          integral_add h1.norm h2.norm
      _ = (∫ x, ‖projected h n x - (h x : ℂ)‖) + ‖projected h n 0 / ψ 0‖ * ∫ x, ‖ψ x‖ := by
          congr 1
          simp_rw [norm_mul]
          exact integral_const_mul _ _

end

end CohnElkies
