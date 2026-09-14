import CohnElkies.SignUncertainty.Basic

/-! # Integrals of families of test functions; mollifications are test functions

`x ↦ ∫ g a x ∂μ` is a test function whenever `a ↦ g a` is a family of test functions whose
Schwartz seminorms are dominated by integrable functions of `a` (differentiation under the
integral sign; this generalizes the probability average `CohnElkies.schwartzAverage` of
`CohnElkies.Radialization`). Applied to the family `a ↦ h(a) f(· - a)` this shows that `h ⋆ f` is
a test function for every test function `f` and every measurable `h` with
`(1 + ‖a‖)^k h(a) ∈ L¹` for all `k` — the mechanism behind `q_n ∈ S_rad(ℝ^d)` in report §2.1. -/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff Topology Convolution

section IntegrableFamily

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) {d : ℕ} (g : α → TestFunction d)
  (B : ℕ → ℕ → α → ℝ)

theorem integrable_iteratedFDeriv_family
    (hmeas : ∀ (n : ℕ) (x : Euclidean d),
      AEStronglyMeasurable (fun a ↦ iteratedFDeriv ℝ n (g a : Euclidean d → ℂ) x) μ)
    (hbound : ∀ (a : α) (k n : ℕ), SchwartzMap.seminorm ℂ k n (g a) ≤ B k n a)
    (hB : ∀ k n, Integrable (B k n) μ) (n : ℕ) (x : Euclidean d) :
    Integrable (fun a ↦ iteratedFDeriv ℝ n (g a : Euclidean d → ℂ) x) μ :=
  (hB 0 n).mono' (hmeas n x) (.of_forall fun a ↦
    (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ (g a) n x).trans (hbound a 0 n))

theorem hasFDerivAt_integral_iteratedFDeriv_family
    (hmeas : ∀ (n : ℕ) (x : Euclidean d),
      AEStronglyMeasurable (fun a ↦ iteratedFDeriv ℝ n (g a : Euclidean d → ℂ) x) μ)
    (hbound : ∀ (a : α) (k n : ℕ), SchwartzMap.seminorm ℂ k n (g a) ≤ B k n a)
    (hB : ∀ k n, Integrable (B k n) μ) (n : ℕ) (x : Euclidean d) :
    HasFDerivAt (fun y : Euclidean d ↦ ∫ a, iteratedFDeriv ℝ n (g a : Euclidean d → ℂ) y ∂μ)
      (∫ a, fderiv ℝ (iteratedFDeriv ℝ n (g a : Euclidean d → ℂ)) x ∂μ) x := by
  have hderiv_meas : AEStronglyMeasurable
      (fun a ↦ fderiv ℝ (iteratedFDeriv ℝ n (g a : Euclidean d → ℂ)) x) μ := by
    simpa only [fderiv_iteratedFDeriv, Function.comp_apply] using
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ Euclidean d)
        ℂ).continuous.comp_aestronglyMeasurable (hmeas (n + 1) x)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (F := fun y : Euclidean d ↦ fun a ↦ iteratedFDeriv ℝ n (g a : Euclidean d → ℂ) y)
    (F' := fun y : Euclidean d ↦ fun a ↦ fderiv ℝ (iteratedFDeriv ℝ n (g a : Euclidean d → ℂ)) y)
    (bound := B 0 (n + 1)) (s := Set.univ) Filter.univ_mem
    (.of_forall fun y ↦ hmeas n y) (integrable_iteratedFDeriv_family μ g B hmeas hbound hB n x)
    hderiv_meas (.of_forall fun a y _ ↦ ?_) (hB 0 (n + 1))
  · exact .of_forall fun a y _ ↦ (((g a).smooth ⊤).differentiable_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop (le_refl _) n)).differentiableAt.hasFDerivAt
  · calc ‖fderiv ℝ (iteratedFDeriv ℝ n (g a : Euclidean d → ℂ)) y‖
        = ‖iteratedFDeriv ℝ (n + 1) (g a : Euclidean d → ℂ) y‖ := norm_fderiv_iteratedFDeriv
      _ ≤ SchwartzMap.seminorm ℂ 0 (n + 1) (g a) :=
          SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ (g a) (n + 1) y
      _ ≤ B 0 (n + 1) a := hbound a 0 (n + 1)

/-- Differentiation under the integral sign: iterated derivatives of a family of test functions
with integrable seminorm bounds commute with integration in the parameter. -/
theorem iteratedFDeriv_integral_family
    (hmeas : ∀ (n : ℕ) (x : Euclidean d),
      AEStronglyMeasurable (fun a ↦ iteratedFDeriv ℝ n (g a : Euclidean d → ℂ) x) μ)
    (hbound : ∀ (a : α) (k n : ℕ), SchwartzMap.seminorm ℂ k n (g a) ≤ B k n a)
    (hB : ∀ k n, Integrable (B k n) μ) (n : ℕ) (x : Euclidean d) :
    iteratedFDeriv ℝ n (fun y : Euclidean d ↦ ∫ a, (g a) y ∂μ) x =
      ∫ a, iteratedFDeriv ℝ n (g a : Euclidean d → ℂ) x ∂μ := by
  induction n generalizing x with
  | zero =>
      ext v
      rw [ContinuousMultilinearMap.integral_apply
        (integrable_iteratedFDeriv_family μ g B hmeas hbound hB 0 x)]
      simp
  | succ n ih =>
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply,
        show iteratedFDeriv ℝ n (fun y : Euclidean d ↦ ∫ a, (g a) y ∂μ) =
          fun y : Euclidean d ↦ ∫ a, iteratedFDeriv ℝ n (g a : Euclidean d → ℂ) y ∂μ from
          funext ih,
        (hasFDerivAt_integral_iteratedFDeriv_family μ g B hmeas hbound hB n x).fderiv]
      calc (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ Euclidean d) ℂ).symm
            (∫ a, fderiv ℝ (iteratedFDeriv ℝ n (g a : Euclidean d → ℂ)) x ∂μ)
          = ∫ a,
              (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ Euclidean d) ℂ).symm
                (fderiv ℝ (iteratedFDeriv ℝ n (g a : Euclidean d → ℂ)) x) ∂μ :=
            (LinearIsometry.integral_comp_comm (𝕜 := ℝ)
              (LinearIsometryEquiv.toLinearIsometry
                ((continuousMultilinearCurryLeftEquiv ℝ
                  (fun _ : Fin (n + 1) ↦ Euclidean d) ℂ).symm))
              fun a ↦ fderiv ℝ (iteratedFDeriv ℝ n (g a : Euclidean d → ℂ)) x).symm
        _ = ∫ a, iteratedFDeriv ℝ (n + 1) (g a : Euclidean d → ℂ) x ∂μ := by
            apply integral_congr_ae
            filter_upwards [] with a
            rw [iteratedFDeriv_succ_eq_comp_left]
            rfl

theorem pow_mul_norm_iteratedFDeriv_integral_le_family
    (hmeas : ∀ (n : ℕ) (x : Euclidean d),
      AEStronglyMeasurable (fun a ↦ iteratedFDeriv ℝ n (g a : Euclidean d → ℂ) x) μ)
    (hbound : ∀ (a : α) (k n : ℕ), SchwartzMap.seminorm ℂ k n (g a) ≤ B k n a)
    (hB : ∀ k n, Integrable (B k n) μ) (k n : ℕ) (x : Euclidean d) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y : Euclidean d ↦ ∫ a, g a y ∂μ) x‖ ≤
      ∫ a, B k n a ∂μ := by
  rw [iteratedFDeriv_integral_family μ g B hmeas hbound hB n x]
  calc ‖x‖ ^ k * ‖∫ a, iteratedFDeriv ℝ n (g a : Euclidean d → ℂ) x ∂μ‖
      ≤ ‖x‖ ^ k * ∫ a, ‖iteratedFDeriv ℝ n (g a : Euclidean d → ℂ) x‖ ∂μ :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = ∫ a, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (g a : Euclidean d → ℂ) x‖ ∂μ := by
        rw [integral_const_mul]
    _ ≤ ∫ a, B k n a ∂μ :=
        integral_mono_of_nonneg (.of_forall fun _ ↦ by positivity) (hB k n)
          (.of_forall fun a ↦ (SchwartzMap.le_seminorm ℂ k n (g a) x).trans (hbound a k n))

/-- The integral `x ↦ ∫ g a x ∂μ` of a family of test functions whose Schwartz seminorms are
dominated by integrable functions of the parameter, as a test function. -/
def schwartzIntegral
    (hmeas : ∀ (n : ℕ) (x : Euclidean d),
      AEStronglyMeasurable (fun a ↦ iteratedFDeriv ℝ n (g a : Euclidean d → ℂ) x) μ)
    (hbound : ∀ (a : α) (k n : ℕ), SchwartzMap.seminorm ℂ k n (g a) ≤ B k n a)
    (hB : ∀ k n, Integrable (B k n) μ) : TestFunction d where
  toFun x := ∫ a, g a x ∂μ
  smooth' := by
    refine contDiff_of_differentiable_iteratedFDeriv fun n _ ↦ ?_
    rw [funext fun x ↦ iteratedFDeriv_integral_family μ g B hmeas hbound hB n x]
    exact fun x ↦
      (hasFDerivAt_integral_iteratedFDeriv_family μ g B hmeas hbound hB n x).differentiableAt
  decay' k n :=
    ⟨∫ a, B k n a ∂μ, pow_mul_norm_iteratedFDeriv_integral_le_family μ g B hmeas hbound hB k n⟩

@[simp] theorem schwartzIntegral_apply
    (hmeas : ∀ (n : ℕ) (x : Euclidean d),
      AEStronglyMeasurable (fun a ↦ iteratedFDeriv ℝ n (g a : Euclidean d → ℂ) x) μ)
    (hbound : ∀ (a : α) (k n : ℕ), SchwartzMap.seminorm ℂ k n (g a) ≤ B k n a)
    (hB : ∀ k n, Integrable (B k n) μ) (x : Euclidean d) :
    schwartzIntegral μ g B hmeas hbound hB x = ∫ a, g a x ∂μ :=
  rfl

end IntegrableFamily

/-! ### Translates of test functions -/

section Translate

variable {d : ℕ}

theorem translate_decay_bound (f : TestFunction d) (y : Euclidean d) (k n : ℕ) (x : Euclidean d) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun z ↦ f (z - y)) x‖ ≤
      (1 + ‖y‖) ^ k *
        (2 ^ k * (Finset.Iic (k, n)).sup (fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) f) := by
  rw [iteratedFDeriv_comp_sub]
  have hx : ‖x‖ ≤ (1 + ‖y‖) * (1 + ‖x - y‖) := by
    have h1 : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by simpa using norm_add_le (x - y) y
    nlinarith [norm_nonneg y, norm_nonneg (x - y)]
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f (x - y)‖
      ≤ ((1 + ‖y‖) * (1 + ‖x - y‖)) ^ k * ‖iteratedFDeriv ℝ n f (x - y)‖ := by gcongr
    _ = (1 + ‖y‖) ^ k * ((1 + ‖x - y‖) ^ k * ‖iteratedFDeriv ℝ n f (x - y)‖) := by
        rw [mul_pow, mul_assoc]
    _ ≤ (1 + ‖y‖) ^ k *
          (2 ^ k * (Finset.Iic (k, n)).sup (fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) f) :=
        mul_le_mul_of_nonneg_left
          (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, n)) le_rfl le_rfl f (x - y))
          (by positivity)

/-- The translate `x ↦ f (x - y)` of a test function. -/
def translate (f : TestFunction d) (y : Euclidean d) : TestFunction d where
  toFun x := f (x - y)
  smooth' := (f.smooth ⊤).comp (contDiff_id.sub contDiff_const)
  decay' k n := ⟨_, translate_decay_bound f y k n⟩

@[simp] theorem translate_apply (f : TestFunction d) (y x : Euclidean d) :
    translate f y x = f (x - y) :=
  rfl

theorem iteratedFDeriv_translate (f : TestFunction d) (y : Euclidean d) (n : ℕ) (x : Euclidean d) :
    iteratedFDeriv ℝ n (translate f y : Euclidean d → ℂ) x =
      iteratedFDeriv ℝ n (f : Euclidean d → ℂ) (x - y) :=
  iteratedFDeriv_comp_sub n y x

theorem seminorm_translate_le (f : TestFunction d) (y : Euclidean d) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (translate f y) ≤
      (1 + ‖y‖) ^ k *
        (2 ^ k * (Finset.Iic (k, n)).sup (fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) f) :=
  SchwartzMap.seminorm_le_bound ℂ k n _
    (mul_nonneg (by positivity) (mul_nonneg (by positivity) (apply_nonneg _ _)))
    (translate_decay_bound f y k n)

end Translate

/-! ### Mollification by a test function -/

section Mollify

variable {d : ℕ}

/-- `h ⋆ f`, for a test function `f` and a measurable `h` with `(1 + ‖a‖)^k h(a) ∈ L¹` for all
`k`, as a test function (the family `a ↦ h(a) f(· - a)` has integrable seminorm bounds). -/
def schwartzConvolution (h : Euclidean d → ℂ) (hh : AEStronglyMeasurable h volume)
    (hmom : ∀ k : ℕ, Integrable fun a ↦ (1 + ‖a‖) ^ k * ‖h a‖) (f : TestFunction d) :
    TestFunction d :=
  schwartzIntegral volume (fun a ↦ h a • translate f a)
    (fun k n a ↦ ‖h a‖ * ((1 + ‖a‖) ^ k *
      (2 ^ k * (Finset.Iic (k, n)).sup (fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) f)))
    (fun n x ↦ by
      have heq : ∀ a, iteratedFDeriv ℝ n ((h a • translate f a : TestFunction d) :
          Euclidean d → ℂ) x = h a • iteratedFDeriv ℝ n (f : Euclidean d → ℂ) (x - a) := fun a ↦ by
        change iteratedFDeriv ℝ n (h a • (translate f a : Euclidean d → ℂ)) x = _
        rw [iteratedFDeriv_const_smul_apply (((translate f a).smooth ⊤).of_le
          (mod_cast le_top)).contDiffAt, iteratedFDeriv_translate]
      simp_rw [heq]
      exact hh.smul (((f.smooth ⊤).continuous_iteratedFDeriv (mod_cast le_top)).comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (fun a k n ↦ by
      rw [map_smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (seminorm_translate_le f a k n) (norm_nonneg _))
    (fun k n ↦ by
      refine ((hmom k).mul_const
        (2 ^ k * (Finset.Iic (k, n)).sup (fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) f)).congr
        (.of_forall fun a ↦ ?_)
      ring)

theorem schwartzConvolution_apply (h : Euclidean d → ℂ) (hh : AEStronglyMeasurable h volume)
    (hmom : ∀ k : ℕ, Integrable fun a ↦ (1 + ‖a‖) ^ k * ‖h a‖) (f : TestFunction d)
    (x : Euclidean d) :
    schwartzConvolution h hh hmom f x = (h ⋆[ContinuousLinearMap.mul ℂ ℂ] f) x := by
  simp only [schwartzConvolution, schwartzIntegral_apply, convolution_def,
    ContinuousLinearMap.mul_apply', smul_apply, translate_apply, smul_eq_mul]

end Mollify

end

end CohnElkies
