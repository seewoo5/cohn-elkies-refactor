import Mathlib

/-!
# A function and its Fourier transform cannot both be compactly supported

Let `V` be a nontrivial finite-dimensional real inner product space and `f : V → ℂ` an integrable
function. The Fourier–Laplace transform `z ↦ ∫ f x * exp (z * ⟪x, ξ⟫)` of `f` along a direction
`ξ` (`Real.fourierLaplaceRay`) restricts on the imaginary axis to the Fourier transform of `f`
along the ray `ℝ ξ`: `𝓕 f (t • ξ) = fourierLaplaceRay f ξ (-2 * π * t * I)`. If `f` vanishes
outside a ball, this transform is entire (`Real.differentiable_fourierLaplaceRay`, differentiation
under the integral sign); an entire function vanishing on a ray of the imaginary axis vanishes
identically (`AnalyticOnNhd.eq_zero_of_forall_ofReal_mul_I_eq_zero`). Hence if `𝓕 f` also vanishes
outside a ball, then `𝓕 f = 0` (`Real.fourierIntegral_eq_zero_of_eq_zero_outside_ball`), and `f`
vanishes almost everywhere (`Real.ae_eq_zero_of_hasCompactSupport_fourierIntegral`), everywhere if
`f` is continuous (`Real.eq_zero_of_hasCompactSupport_fourierIntegral`).

The last step uses the injectivity of the Fourier transform on `L¹`
(`MeasureTheory.Integrable.ae_eq_zero_of_fourierIntegral_eq_zero`): if `𝓕 f = 0` then `f` pairs to
zero against every Schwartz function, hence against every smooth compactly supported function.

## Main results

* `AnalyticOnNhd.eq_zero_of_forall_ofReal_mul_I_eq_zero`: an entire function vanishing on
  `{t * I | T < t}` vanishes identically.
* `Real.fourierIntegral_eq_zero_of_eq_zero_outside_ball`: if an integrable `f` and `𝓕 f` both
  vanish outside the ball of radius `R`, then `𝓕 f = 0`.
* `MeasureTheory.Integrable.ae_eq_zero_of_fourierIntegral_eq_zero`: `𝓕 f = 0 → f =ᵐ[volume] 0`.
* `Real.ae_eq_zero_of_hasCompactSupport_fourierIntegral`,
  `Real.eq_zero_of_hasCompactSupport_fourierIntegral`: an integrable function with compactly
  supported Fourier transform and compact support vanishes (a.e., resp. everywhere if continuous).
-/

open MeasureTheory Set
open scoped FourierTransform Real RealInnerProductSpace Topology
open Complex (I)

noncomputable section

/-- An entire function vanishing on a ray `{t * I | T < t}` of the imaginary axis vanishes
identically (identity theorem). -/
theorem AnalyticOnNhd.eq_zero_of_forall_ofReal_mul_I_eq_zero {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F univ) (T : ℝ) (hvanish : ∀ t : ℝ, T < t → F (t * I) = 0) : F = 0 := by
  have hclosure : (T + 1 : ℝ) * I ∈ closure ({z | F z = 0} \ {(T + 1 : ℝ) * I}) := by
    refine mem_closure_of_tendsto (b := 𝓝[>] (T + 1)) (f := fun t : ℝ ↦ (t : ℂ) * I)
      (tendsto_nhdsWithin_of_tendsto_nhds
        (by fun_prop : Continuous fun t : ℝ ↦ (t : ℂ) * I).continuousAt) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    refine ⟨hvanish t (by linarith [mem_Ioi.1 ht]), fun h ↦ (mem_Ioi.1 ht).ne' ?_⟩
    exact Complex.ofReal_injective (mul_left_injective₀ Complex.I_ne_zero h)
  exact funext fun z ↦ hF.eqOn_zero_of_preconnected_of_mem_closure isPreconnected_univ (mem_univ _)
    hclosure (mem_univ z)

namespace Real

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- `F(z) = ∫ f(x) e^{z ⟪x, ξ⟫} dx`: the Fourier–Laplace transform of `f` along the direction `ξ`;
`𝓕 f (t • ξ) = F(-2πit)` (`Real.fourierIntegral_smul_eq_fourierLaplaceRay`). -/
def fourierLaplaceRay (f : V → ℂ) (ξ : V) (z : ℂ) : ℂ :=
  ∫ x, f x * Complex.exp (z * ⟪x, ξ⟫)

theorem fourierIntegral_smul_eq_fourierLaplaceRay (f : V → ℂ) (ξ : V) (t : ℝ) :
    𝓕 f (t • ξ) = fourierLaplaceRay f ξ (-2 * π * t * I) := by
  rw [Real.fourier_eq', fourierLaplaceRay]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  simp only [real_inner_smul_right, smul_eq_mul]
  rw [mul_comm (Complex.exp _)]
  congr 2
  push_cast
  ring

/-- For an integrable `f` vanishing outside a ball, the Fourier–Laplace transform along any
direction is entire (differentiation under the integral sign). -/
theorem differentiable_fourierLaplaceRay {f : V → ℂ} (hf : Integrable f) {R : ℝ}
    (hsupp : ∀ x : V, R < ‖x‖ → f x = 0) (ξ : V) :
    Differentiable ℂ (fourierLaplaceRay f ξ) := by
  intro z₀
  set M : ℝ := max R 0 * ‖ξ‖ with hM
  have hM0 : 0 ≤ M := by positivity
  have hinner : ∀ x : V, f x ≠ 0 → |⟪x, ξ⟫| ≤ M := fun x hx ↦ by
    have hxR : ‖x‖ ≤ max R 0 := le_max_of_le_left (le_of_not_gt fun h ↦ hx (hsupp x h))
    exact (abs_real_inner_le_norm x ξ).trans (mul_le_mul_of_nonneg_right hxR (norm_nonneg ξ))
  have hre : ∀ (z : ℂ) (x : V), f x ≠ 0 → (z * ⟪x, ξ⟫).re ≤ ‖z‖ * M := fun z x hx ↦
    calc (z * ⟪x, ξ⟫).re ≤ ‖z * ⟪x, ξ⟫‖ := Complex.re_le_norm _
      _ = ‖z‖ * |⟪x, ξ⟫| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖z‖ * M := by gcongr; exact hinner x hx
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable
      (fun x : V ↦ f x * Complex.exp (z * ⟪x, ξ⟫)) volume := fun z ↦
    hf.aestronglyMeasurable.mul
      (by fun_prop : Continuous fun x : V ↦ Complex.exp (z * ⟪x, ξ⟫)).aestronglyMeasurable
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (𝕜 := ℂ)
    (F := fun z x ↦ f x * Complex.exp (z * ⟪x, ξ⟫))
    (F' := fun z x ↦ f x * ((⟪x, ξ⟫ : ℂ) * Complex.exp (z * ⟪x, ξ⟫)))
    (bound := fun x ↦ ‖f x‖ * (M * Real.exp ((‖z₀‖ + 1) * M)))
    (Metric.ball_mem_nhds z₀ one_pos) (.of_forall hmeas) ?_ ?_ ?_ ?_ ?_).2.differentiableAt
  · refine (hf.norm.mul_const (Real.exp (‖z₀‖ * M))).mono' (hmeas z₀) (.of_forall fun x ↦ ?_)
    by_cases hx : f x = 0
    · simp [hx]
    · rw [norm_mul, Complex.norm_exp]
      gcongr
      exact hre z₀ x hx
  · exact hf.aestronglyMeasurable.mul (by fun_prop : Continuous fun x : V ↦
      (⟪x, ξ⟫ : ℂ) * Complex.exp (z₀ * ⟪x, ξ⟫)).aestronglyMeasurable
  · refine .of_forall fun x z hz ↦ ?_
    by_cases hx : f x = 0
    · simp [hx]
    · have hz' : ‖z‖ ≤ ‖z₀‖ + 1 :=
        (norm_le_norm_add_norm_sub' z z₀).trans (by linarith [mem_ball_iff_norm.1 hz])
      rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
      have h1 := hinner x hx
      have h2 : (z * ⟪x, ξ⟫).re ≤ (‖z₀‖ + 1) * M := (hre z x hx).trans (by gcongr)
      gcongr
  · exact hf.norm.mul_const _
  · refine .of_forall fun x z _ ↦ ?_
    have h := (((hasDerivAt_id z).mul_const (⟪x, ξ⟫ : ℂ)).cexp).const_mul (f x)
    simpa [mul_comm, mul_left_comm, mul_assoc] using h

/-- An integrable function vanishing outside a ball whose Fourier transform also vanishes outside
a ball has identically vanishing Fourier transform, since `𝓕 f` is entire along every ray through
the origin. -/
theorem fourierIntegral_eq_zero_of_eq_zero_outside_ball [Nontrivial V] {f : V → ℂ}
    (hf : Integrable f) {R : ℝ} (hsupp : ∀ x : V, R < ‖x‖ → f x = 0)
    (hfourier : ∀ x : V, R < ‖x‖ → 𝓕 f x = 0) : 𝓕 f = 0 := by
  have key : ∀ ξ : V, ξ ≠ 0 → ∀ t : ℝ, 𝓕 f (t • ξ) = 0 := by
    intro ξ hξ t
    have hξ' : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    set G : ℂ → ℂ := fun z ↦ fourierLaplaceRay f ξ (-2 * π * z) with hG
    have hGa : AnalyticOnNhd ℂ G univ := Complex.analyticOnNhd_univ_iff_differentiable.2
      ((differentiable_fourierLaplaceRay hf hsupp ξ).comp (differentiable_id.const_mul _))
    have hvanish : ∀ s : ℝ, max R 0 / ‖ξ‖ < s → G (s * I) = 0 := fun s hs ↦ by
      have hs0 : 0 < s := lt_of_le_of_lt (by positivity) hs
      have hnorm : R < ‖s • ξ‖ := by
        rw [norm_smul, Real.norm_of_nonneg hs0.le]
        exact lt_of_le_of_lt (le_max_left R 0) ((div_lt_iff₀ hξ').1 hs)
      have h := hfourier _ hnorm
      rw [fourierIntegral_smul_eq_fourierLaplaceRay] at h
      simpa [hG, mul_assoc] using h
    have hG0 := congrFun (hGa.eq_zero_of_forall_ofReal_mul_I_eq_zero _ hvanish) (t * I)
    rw [fourierIntegral_smul_eq_fourierLaplaceRay]
    simpa [hG, mul_assoc] using hG0
  funext ξ
  by_cases hξ : ξ = 0
  · obtain ⟨e, he⟩ := exists_ne (0 : V)
    simpa [hξ] using key e he 0
  · simpa using key ξ hξ 1

end Real

/-- The Fourier transform is injective on `L¹`: an integrable function with vanishing Fourier
transform vanishes almost everywhere. -/
theorem MeasureTheory.Integrable.ae_eq_zero_of_fourierIntegral_eq_zero
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {f : V → ℂ} (hf : Integrable f) (h : 𝓕 f = 0) :
    f =ᵐ[volume] 0 := by
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hf.locallyIntegrable fun g hg hgsupp ↦ ?_
  have hG : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgsupp.comp_left rfl
  set G : SchwartzMap V ℂ := hG.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hg) with hGdef
  set H : SchwartzMap V ℂ := 𝓕⁻ G with hHdef
  have hpair := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ V)
    Real.continuous_fourierChar continuous_inner (H.integrable (μ := volume)) hf
  have hGG : 𝓕 (H : V → ℂ) = G := by
    rw [← SchwartzMap.fourier_coe, hHdef, FourierTransform.fourier_fourierInv_eq]
  simp only [flip_innerₗ] at hpair
  change ∫ ξ, 𝓕 (H : V → ℂ) ξ • f ξ = ∫ x, H x • 𝓕 f x at hpair
  rw [hGG, h] at hpair
  simp only [Pi.zero_apply, smul_zero, integral_zero] at hpair
  rw [← hpair]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  simp [hGdef, Complex.real_smul]

namespace Real

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- An integrable function with compact support whose Fourier transform has compact support
vanishes almost everywhere. -/
theorem ae_eq_zero_of_hasCompactSupport_fourierIntegral [Nontrivial V] {f : V → ℂ}
    (hf : Integrable f) (hsupp : HasCompactSupport f) (hfourier : HasCompactSupport (𝓕 f)) :
    f =ᵐ[volume] 0 := by
  obtain ⟨R₁, -, hR₁⟩ := hsupp.exists_pos_le_norm
  obtain ⟨R₂, -, hR₂⟩ := hfourier.exists_pos_le_norm
  refine hf.ae_eq_zero_of_fourierIntegral_eq_zero
    (fourierIntegral_eq_zero_of_eq_zero_outside_ball hf (R := max R₁ R₂) ?_ ?_)
  · exact fun x hx ↦ hR₁ x ((le_max_left _ _).trans hx.le)
  · exact fun x hx ↦ hR₂ x ((le_max_right _ _).trans hx.le)

/-- A continuous integrable function with compact support whose Fourier transform has compact
support vanishes. -/
theorem eq_zero_of_hasCompactSupport_fourierIntegral [Nontrivial V] {f : V → ℂ}
    (hcont : Continuous f) (hf : Integrable f) (hsupp : HasCompactSupport f)
    (hfourier : HasCompactSupport (𝓕 f)) : f = 0 :=
  (hcont.ae_eq_iff_eq volume continuous_const).1
    (ae_eq_zero_of_hasCompactSupport_fourierIntegral hf hsupp hfourier)

end Real

end
