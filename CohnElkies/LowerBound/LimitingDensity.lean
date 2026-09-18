import CohnElkies.LowerBound.GammaBoundary
import CohnElkiesForMathlib.Analysis.SpecialFunctions.FrullaniIntegral

/-!
# The limiting Poisson density and the endpoint expectation (report §3.3, Lemma 3.4)

The normalized strip Poisson kernel `P_σ/M_σ` as `σ → -1`, its limit `π/(4 cosh²(πT/2))`
(the logistic density), the exponential majorant, the characteristic function of the logistic
distribution `πx/sinh(πx)` (via `Γ(1 + ix) Γ(1 - ix)`), and the endpoint expectation
`∫ (P_σ/M_σ) · lowerEndpointPhase` whose limit `log (π/2) - 1` is computed with the Wallis phase
kernel (Frullani integrals); its sharp coefficient is eventually negative
(`eventually_lowerPoissonEndpointSharpCoefficient_neg`).
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory Real Set
open scoped Interval Topology

/-- The normalized lower-edge harmonic measure `P_σ / M_σ` of the strip; report Lemma 3.4. -/
def stripNormalizedPoissonKernel (σ T : ℝ) : ℝ := P_σ σ T / M_σ σ

/-- The closed form of `P_σ / M_σ` obtained from `θ σ = π - π (1 - σ) / 2`; unlike the quotient
itself it extends continuously to `σ = 1`. -/
def stripNormalizedPoissonExtension (σ T : ℝ) : ℝ :=
  π / 4 * sinc (π * (1 - σ) / 2) / (cosh (π * T / 2) + cos (π * (1 - σ) / 2))

/-- The limit `π / (4 (cosh (π T / 2) + 1))` of `P_σ / M_σ` as `σ ↑ 1`; report Lemma 3.4. -/
def limitingStripPoissonDensity (T : ℝ) : ℝ := π / (4 * (cosh (π * T / 2) + 1))

theorem stripNormalizedPoissonKernel_eq_extension
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) (T : ℝ) :
    stripNormalizedPoissonKernel σ T = stripNormalizedPoissonExtension σ T := by
  have hmass : 0 < 1 - σ := sub_pos.mpr habove
  have hsmall : 0 < π * (1 - σ) / 2 := div_pos (mul_pos pi_pos hmass) zero_lt_two
  have hden : 0 < cosh (π * T / 2) + cos (π * (1 - σ) / 2) := by
    have h := cos_lt_cos_of_nonneg_of_le_pi hsmall.le le_rfl (by nlinarith [pi_pos])
    rw [cos_pi] at h
    linarith [one_le_cosh (π * T / 2)]
  unfold stripNormalizedPoissonKernel stripNormalizedPoissonExtension P_σ M_σ
  rw [show θ σ = π - π * (1 - σ) / 2 by unfold θ; ring, sin_pi_sub, cos_pi_sub,
    sinc_of_ne_zero hsmall.ne']
  field_simp [hmass.ne', hsmall.ne', hden.ne']
  ring

theorem stripNormalizedPoissonExtension_one (T : ℝ) :
    stripNormalizedPoissonExtension 1 T = limitingStripPoissonDensity T := by
  unfold stripNormalizedPoissonExtension limitingStripPoissonDensity
  simp only [sub_self, mul_zero, zero_div, sinc_zero, cos_zero, mul_one, div_div]

theorem tendsto_stripNormalizedPoissonKernel (T : ℝ) :
    Tendsto (fun σ : ℝ ↦ stripNormalizedPoissonKernel σ T) (𝓝[<] 1)
      (𝓝 (limitingStripPoissonDensity T)) := by
  have hangle : Continuous fun σ : ℝ ↦ π * (1 - σ) / 2 := by fun_prop
  have hden : cosh (π * T / 2) + cos (π * (1 - (1 : ℝ)) / 2) ≠ 0 := by
    simp only [sub_self, mul_zero, zero_div, cos_zero]
    linarith [one_le_cosh (π * T / 2)]
  have hext : Tendsto (fun σ : ℝ ↦ stripNormalizedPoissonExtension σ T) (𝓝[<] 1)
      (𝓝 (limitingStripPoissonDensity T)) := by
    rw [← stripNormalizedPoissonExtension_one T]
    exact (((continuous_const.mul (continuous_sinc.comp hangle)).continuousAt.div
      ((continuous_const.add (continuous_cos.comp hangle)).continuousAt) hden)).mono_left
      nhdsWithin_le_nhds
  refine hext.congr' ?_
  filter_upwards [(eventually_gt_nhds (by norm_num : (-1 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with σ h1 h2
  exact (stripNormalizedPoissonKernel_eq_extension h1 h2 T).symm

theorem stripNormalizedPoissonKernel_integrable {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) :
    Integrable (stripNormalizedPoissonKernel σ) :=
  (stripPoissonKernel_integrable hbelow habove).div_const _

/-- The `σ`-uniform exponential majorant `(π/2) e^{-π|T|/2}` of `P_σ / M_σ`. -/
def stripPoissonExponentialMajorant (T : ℝ) : ℝ := π / 2 * exp (-(π / 2) * |T|)

theorem stripNormalizedPoissonExtension_le_majorant
    {σ : ℝ} (hzero : 0 ≤ σ) (hone : σ ≤ 1) (T : ℝ) :
    0 ≤ stripNormalizedPoissonExtension σ T ∧
      stripNormalizedPoissonExtension σ T ≤ stripPoissonExponentialMajorant T := by
  have hpi := pi_pos
  have hq0 : 0 ≤ π * (1 - σ) / 2 := by nlinarith
  have hcos : 0 ≤ cos (π * (1 - σ) / 2) := cos_nonneg_of_mem_Icc ⟨by nlinarith, by nlinarith⟩
  have hsinc : 0 ≤ sinc (π * (1 - σ) / 2) := by
    rcases eq_or_ne (π * (1 - σ) / 2) 0 with h | h
    · simp [h]
    · rw [sinc_of_ne_zero h]
      exact div_nonneg (sin_nonneg_of_nonneg_of_le_pi hq0 (by nlinarith)) hq0
  have hden : 0 < cosh (π * T / 2) + cos (π * (1 - σ) / 2) :=
    add_pos_of_pos_of_nonneg (cosh_pos _) hcos
  have hmul : exp (-|π * T / 2|) * exp |π * T / 2| = 1 := by rw [← exp_add]; simp
  have hhalf : exp |π * T / 2| / 2 ≤ cosh (π * T / 2) := by
    rw [← cosh_abs, cosh_eq]
    linarith [(exp_pos (-|π * T / 2|)).le]
  have habs : exp (-(π / 2) * |T|) = exp (-|π * T / 2|) := by
    rw [abs_div, abs_mul, abs_of_pos hpi, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    ring_nf
  have hkey : sinc (π * (1 - σ) / 2) ≤
      2 * exp (-|π * T / 2|) * (cosh (π * T / 2) + cos (π * (1 - σ) / 2)) := by
    have h1 : (1 : ℝ) ≤ 2 * exp (-|π * T / 2|) * cosh (π * T / 2) := by
      nlinarith [exp_pos (-|π * T / 2|)]
    have h2 : 0 ≤ 2 * exp (-|π * T / 2|) * cos (π * (1 - σ) / 2) :=
      mul_nonneg (by positivity) hcos
    linarith [sinc_le_one (π * (1 - σ) / 2)]
  unfold stripNormalizedPoissonExtension stripPoissonExponentialMajorant
  refine ⟨div_nonneg (mul_nonneg (by positivity) hsinc) hden.le, ?_⟩
  rw [div_le_iff₀ hden, habs]
  nlinarith [hkey]

theorem stripPoissonExponentialMajorant_integrable : Integrable stripPoissonExponentialMajorant :=
  (integrable_exp_neg_mul_abs (half_pos pi_pos)).const_mul (π / 2)

theorem limitingStripPoissonDensity_integrable : Integrable limitingStripPoissonDensity := by
  have hcont : Continuous limitingStripPoissonDensity := by
    unfold limitingStripPoissonDensity
    exact continuous_const.div (by fun_prop) fun T ↦
      ne_of_gt (by linarith [one_le_cosh (π * T / 2)])
  refine stripPoissonExponentialMajorant_integrable.mono' hcont.aestronglyMeasurable
    (.of_forall fun T ↦ ?_)
  have h := stripNormalizedPoissonExtension_le_majorant (σ := 1) zero_le_one le_rfl T
  rw [stripNormalizedPoissonExtension_one] at h
  rw [Real.norm_eq_abs, abs_of_nonneg h.1]
  exact h.2

/-- The logistic distribution function `e^{πu} / (1 + e^{πu})`, whose density is `p` below. -/
def poissonLogistic (u : ℝ) : ℝ := exp (π * u) / (1 + exp (π * u))

/-- The limiting density `p(u) = (π/4) sech²(πu/2) = π e^{πu} / (1 + e^{πu})²`; report Lemma 3.4. -/
def poissonLogisticDensity (u : ℝ) : ℝ := π * exp (π * u) / (1 + exp (π * u)) ^ 2

theorem poissonLogisticDensity_pos (u : ℝ) : 0 < poissonLogisticDensity u := by
  unfold poissonLogisticDensity
  positivity

theorem poissonLogisticDensity_eq_limitingStripPoissonDensity (u : ℝ) :
    poissonLogisticDensity u = 2 * limitingStripPoissonDensity (2 * u) := by
  have he : exp (π * u) ≠ 0 := (exp_pos _).ne'
  unfold poissonLogisticDensity limitingStripPoissonDensity
  rw [show π * (2 * u) / 2 = π * u by ring, cosh_eq, exp_neg]
  field_simp
  ring

theorem range_poissonLogistic : range poissonLogistic = Ioo (0 : ℝ) 1 := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    have he : 0 < exp (π * u) := exp_pos _
    unfold poissonLogistic
    exact ⟨by positivity, (div_lt_one (by positivity)).2 (by linarith)⟩
  · intro hx
    refine ⟨log (x / (1 - x)) / π, ?_⟩
    unfold poissonLogistic
    rw [mul_div_cancel₀ _ pi_ne_zero, exp_log (div_pos hx.1 (sub_pos.mpr hx.2))]
    field_simp [(sub_pos.mpr hx.2).ne']
    ring

theorem poissonLogistic_hasDerivAt (u : ℝ) :
    HasDerivAt poissonLogistic (poissonLogisticDensity u) u := by
  have he := (Real.hasDerivAt_exp (π * u)).comp u ((hasDerivAt_id u).const_mul π)
  have hden : 1 + exp (π * u) ≠ 0 := by positivity
  convert! he.div ((hasDerivAt_const u 1).add he) hden using 1
  unfold poissonLogisticDensity
  simp only [Function.comp_apply, Pi.add_apply, mul_one, zero_add]
  field_simp
  ring

theorem poissonLogistic_injective : Function.Injective poissonLogistic := by
  intro u v huv
  unfold poissonLogistic at huv
  rw [div_eq_div_iff (by positivity) (by positivity)] at huv
  exact mul_left_cancel₀ pi_ne_zero (exp_injective (by linarith))

theorem poissonLogistic_cpow_ratio (u : ℝ) (w : ℂ) :
    (poissonLogistic u : ℂ) ^ w * (1 - poissonLogistic u : ℂ) ^ (-w) =
      Complex.exp ((π * u : ℂ) * w) := by
  have hx : poissonLogistic u ∈ Ioo (0 : ℝ) 1 := range_poissonLogistic ▸ mem_range_self u
  have hone : 0 < 1 - poissonLogistic u := sub_pos.mpr hx.2
  have hodds : poissonLogistic u / (1 - poissonLogistic u) = exp (π * u) := by
    have hden : 1 + exp (π * u) ≠ 0 := by positivity
    unfold poissonLogistic
    field_simp
    ring
  have hlog : log (poissonLogistic u) - log (1 - poissonLogistic u) = π * u := by
    rw [← log_div hx.1.ne' hone.ne', hodds, log_exp]
  rw [show (1 : ℂ) - (poissonLogistic u : ℂ) = (1 - poissonLogistic u : ℝ) by push_cast; ring,
    show (π : ℂ) * (u : ℂ) = (π * u : ℝ) by push_cast; ring,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.1.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hone.ne'), ← Complex.exp_add,
    ← Complex.ofReal_log hx.1.le, ← Complex.ofReal_log hone.le, ← hlog]
  congr 1
  push_cast
  ring

theorem integral_poissonLogistic_change_Ioo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) :
    (∫ x : ℝ in Ioo 0 1, f x) = ∫ u : ℝ, poissonLogisticDensity u • f (poissonLogistic u) := by
  simpa [image_univ, range_poissonLogistic, abs_of_pos (poissonLogisticDensity_pos _)] using
    integral_image_eq_integral_abs_deriv_smul (f := poissonLogistic) (f' := poissonLogisticDensity)
      MeasurableSet.univ (fun x _ ↦ (poissonLogistic_hasDerivAt x).hasDerivWithinAt)
      poissonLogistic_injective.injOn f

theorem poissonLogisticDensity_integrable : Integrable poissonLogisticDensity :=
  ((limitingStripPoissonDensity_integrable.comp_mul_left' (by norm_num : (2 : ℝ) ≠ 0)).const_mul
    2).congr (.of_forall fun u ↦ (poissonLogisticDensity_eq_limitingStripPoissonDensity u).symm)

theorem integral_poissonLogisticDensity : (∫ u : ℝ, poissonLogisticDensity u) = 1 := by
  simpa [smul_eq_mul] using (integral_poissonLogistic_change_Ioo fun _ : ℝ ↦ (1 : ℝ)).symm

theorem poissonLogistic_betaIntegral (w : ℂ) : Complex.betaIntegral (1 + w) (1 - w) =
    ∫ u : ℝ, (poissonLogisticDensity u : ℂ) * Complex.exp ((π * u : ℂ) * w) := by
  calc Complex.betaIntegral (1 + w) (1 - w)
      = ∫ x : ℝ in Ioo 0 1, (x : ℂ) ^ w * (1 - x : ℂ) ^ (-w) := by
        unfold Complex.betaIntegral
        rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
        refine setIntegral_congr_fun measurableSet_Ioo fun x _ ↦ ?_
        congr 1 <;> ring_nf
    _ = ∫ u : ℝ, poissonLogisticDensity u • ((poissonLogistic u : ℂ) ^ w *
          (1 - poissonLogistic u : ℂ) ^ (-w)) :=
        integral_poissonLogistic_change_Ioo _
    _ = ∫ u : ℝ, (poissonLogisticDensity u : ℂ) * Complex.exp ((π * u : ℂ) * w) := by
        simp_rw [Complex.real_smul, poissonLogistic_cpow_ratio]

/-- The characteristic function of `p`: `∫ p(u) e^{itu} du = t / sinh t`; report (21). -/
theorem poissonLogistic_characteristic (t : ℝ) :
    (∫ u : ℝ, (poissonLogisticDensity u : ℂ) * Complex.exp (I * (t : ℂ) * (u : ℂ))) =
      if t = 0 then 1 else (t / sinh t : ℂ) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one, ↓reduceIte]
    rw [← Complex.ofReal_one, ← integral_poissonLogisticDensity]
    exact integral_ofReal
  rw [ite_eq_right ht]
  set w : ℂ := I * (t / π : ℝ) with hw
  calc (∫ u : ℝ, (poissonLogisticDensity u : ℂ) * Complex.exp (I * (t : ℂ) * (u : ℂ)))
      = Complex.betaIntegral (1 + w) (1 - w) := by
        rw [poissonLogistic_betaIntegral w]
        refine integral_congr_ae (.of_forall fun u ↦ ?_)
        rw [hw]
        push_cast
        field_simp
    _ = Complex.Gamma (1 + w) * Complex.Gamma (1 - w) := by
        rw [Complex.betaIntegral_eq_Gamma_mul_div (1 + w) (1 - w) (by rw [hw]; norm_num)
          (by rw [hw]; norm_num), show 1 + w + (1 - w) = (2 : ℂ) by ring]
        norm_num
    _ = (π * (t / π) / sinh (π * (t / π)) : ℝ) := by
        rw [hw, Complex.Gamma_one_add_I_mul_mul_Gamma_one_sub_I_mul (div_ne_zero ht pi_ne_zero)]
        push_cast
        ring
    _ = (t / sinh t : ℂ) := by
        rw [show π * (t / π) = t by field_simp, Complex.ofReal_div]

theorem poissonLogistic_characteristic_integrable (t : ℝ) : Integrable fun u : ℝ ↦
    (poissonLogisticDensity u : ℂ) * Complex.exp (I * (t : ℂ) * (u : ℂ)) := by
  refine poissonLogisticDensity_integrable.mono'
    (poissonLogisticDensity_integrable.ofReal.aestronglyMeasurable.mul
      (by fun_prop : Continuous fun u : ℝ ↦
        Complex.exp (I * (t : ℂ) * (u : ℂ))).aestronglyMeasurable) (.of_forall fun u ↦ ?_)
  have hd := poissonLogisticDensity_pos u
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd,
    show I * (t : ℂ) * (u : ℂ) = I * (t * u : ℝ) by push_cast; ring,
    Complex.norm_exp_I_mul_ofReal]
  simp

/-- The cosine transform of `p`: `∫ p(u) cos (tu) du = t / sinh t`; real form of report (21). -/
theorem poissonLogistic_cosine_transform (t : ℝ) :
    (∫ u : ℝ, poissonLogisticDensity u * cos (t * u)) = if t = 0 then 1 else t / sinh t := by
  have h (u : ℝ) : poissonLogisticDensity u * cos (t * u) =
      ((poissonLogisticDensity u : ℂ) * Complex.exp (I * (t : ℂ) * (u : ℂ))).re := by
    rw [show I * (t : ℂ) * (u : ℂ) = (t * u : ℝ) * I by push_cast; ring, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re]
    ring
  calc (∫ u : ℝ, poissonLogisticDensity u * cos (t * u))
      = ∫ u : ℝ, ((poissonLogisticDensity u : ℂ) * Complex.exp (I * (t : ℂ) * (u : ℂ))).re :=
        integral_congr_ae (.of_forall h)
    _ = (∫ u : ℝ, (poissonLogisticDensity u : ℂ) * Complex.exp (I * (t : ℂ) * (u : ℂ))).re :=
        integral_re (poissonLogistic_characteristic_integrable t)
    _ = if t = 0 then 1 else t / sinh t := by
        rw [poissonLogistic_characteristic t]
        split
        · simp
        · rw [Complex.div_ofReal_re, Complex.ofReal_re]

theorem lowerEndpointPhase_continuous : Continuous lowerEndpointPhase := by
  have hlog : Continuous fun T : ℝ ↦ log (1 + T ^ 2 / 4) :=
    (by fun_prop : Continuous fun T : ℝ ↦ 1 + T ^ 2 / 4).log fun T ↦ by positivity
  have habs : Continuous fun T : ℝ ↦ |T| / 2 := continuous_abs.div_const 2
  exact ((by fun_prop : Continuous fun T : ℝ ↦ -π * |T| / 4).sub
    (continuous_const.mul hlog)).add (habs.mul (continuous_arctan.comp habs))

theorem abs_lowerEndpointPhase_le (T : ℝ) : |lowerEndpointPhase T| ≤ π * |T| + T ^ 2 := by
  have hlog0 : 0 ≤ log (1 + T ^ 2 / 4) := log_nonneg (by nlinarith [sq_nonneg T])
  have hlog1 : log (1 + T ^ 2 / 4) ≤ T ^ 2 / 4 := by
    linarith [log_le_sub_one_of_pos (show (0 : ℝ) < 1 + T ^ 2 / 4 by positivity)]
  have hmul0 : 0 ≤ |T| / 2 * arctan (|T| / 2) :=
    mul_nonneg (by positivity) (arctan_nonneg.mpr (by positivity))
  have hmul1 : |T| / 2 * arctan (|T| / 2) ≤ |T| / 2 * (π / 2) :=
    mul_le_mul_of_nonneg_left (arctan_lt_pi_div_two _).le (by positivity)
  have hpi : 0 ≤ π * |T| := mul_nonneg pi_pos.le (abs_nonneg T)
  unfold lowerEndpointPhase
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg T]

theorem stripPoissonExponentialMajorant_mul_lowerEndpointPhase_integrable :
    Integrable fun T : ℝ ↦ stripPoissonExponentialMajorant T * ‖lowerEndpointPhase T‖ := by
  have hmeas : AEStronglyMeasurable
      (fun T : ℝ ↦ stripPoissonExponentialMajorant T * ‖lowerEndpointPhase T‖) volume := by
    unfold stripPoissonExponentialMajorant
    exact ((continuous_const.mul (continuous_exp.comp (continuous_const.mul continuous_abs))).mul
      lowerEndpointPhase_continuous.norm).aestronglyMeasurable
  have ha : 0 < π / 2 := half_pos pi_pos
  refine (((integrable_abs_pow_mul_exp_neg_mul_abs 1 ha).const_mul (π / 2 * π)).add
    ((integrable_abs_pow_mul_exp_neg_mul_abs 2 ha).const_mul (π / 2))).mono' hmeas
    (.of_forall fun T ↦ ?_)
  have hfac : 0 ≤ π / 2 * exp (-(π / 2) * |T|) := by positivity
  unfold stripPoissonExponentialMajorant
  rw [Real.norm_of_nonneg (mul_nonneg hfac (norm_nonneg _)), Real.norm_eq_abs]
  calc π / 2 * exp (-(π / 2) * |T|) * |lowerEndpointPhase T|
      ≤ π / 2 * exp (-(π / 2) * |T|) * (π * |T| + T ^ 2) :=
        mul_le_mul_of_nonneg_left (abs_lowerEndpointPhase_le T) hfac
    _ = π / 2 * π * (|T| ^ 1 * exp (-(π / 2) * |T|)) +
        π / 2 * (|T| ^ 2 * exp (-(π / 2) * |T|)) := by rw [pow_one, sq_abs]; ring

/-- Dominated convergence for the normalized kernels: `∫ (P_σ/M_σ) f → ∫ p f` as `σ ↑ 1`. -/
theorem tendsto_integral_stripNormalizedPoissonKernel_mul (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f volume)
    (hmajor : Integrable fun T : ℝ ↦ stripPoissonExponentialMajorant T * ‖f T‖) :
    Tendsto (fun σ : ℝ ↦ ∫ T : ℝ, stripNormalizedPoissonKernel σ T * f T) (𝓝[<] 1)
      (𝓝 (∫ T : ℝ, limitingStripPoissonDensity T * f T)) := by
  have hlow : ∀ᶠ σ : ℝ in 𝓝[<] (1 : ℝ), 0 < σ :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hlt : ∀ᶠ σ : ℝ in 𝓝[<] (1 : ℝ), σ < 1 := self_mem_nhdsWithin
  refine tendsto_integral_filter_of_dominated_convergence
    (fun T : ℝ ↦ stripPoissonExponentialMajorant T * ‖f T‖) ?_ ?_ hmajor
    (.of_forall fun T ↦ (tendsto_stripNormalizedPoissonKernel T).mul tendsto_const_nhds)
  · filter_upwards [hlow, hlt] with σ h0 h1
    exact (stripNormalizedPoissonKernel_integrable (by linarith) h1).aestronglyMeasurable.mul hf
  · filter_upwards [hlow, hlt] with σ h0 h1
    refine .of_forall fun T ↦ ?_
    have hb := stripNormalizedPoissonExtension_le_majorant h0.le h1.le T
    rw [norm_mul, Real.norm_eq_abs, stripNormalizedPoissonKernel_eq_extension (by linarith) h1 T,
      abs_of_nonneg hb.1]
    exact mul_le_mul_of_nonneg_right hb.2 (norm_nonneg _)

/-- `J_σ`, the expectation of the endpoint phase against `P_σ / M_σ`; report Lemma 3.3. -/
def lowerPoissonEndpointExpectation (σ : ℝ) : ℝ :=
  ∫ T : ℝ, stripNormalizedPoissonKernel σ T * lowerEndpointPhase T

/-- The limit of `J_σ` as `σ ↑ 1`; report Lemma 3.4. -/
def limitingPoissonEndpointExpectation : ℝ :=
  ∫ T : ℝ, limitingStripPoissonDensity T * lowerEndpointPhase T

theorem tendsto_lowerPoissonEndpointExpectation : Tendsto lowerPoissonEndpointExpectation (𝓝[<] 1)
    (𝓝 limitingPoissonEndpointExpectation) :=
  tendsto_integral_stripNormalizedPoissonKernel_mul lowerEndpointPhase
    lowerEndpointPhase_continuous.aestronglyMeasurable
    stripPoissonExponentialMajorant_mul_lowerEndpointPhase_integrable

theorem poissonLogistic_cosine_integrable (t : ℝ) :
    Integrable fun u : ℝ ↦ poissonLogisticDensity u * cos (t * u) := by
  refine poissonLogisticDensity_integrable.mono'
    (poissonLogisticDensity_integrable.aestronglyMeasurable.mul
      (by fun_prop : Continuous fun u : ℝ ↦ cos (t * u)).aestronglyMeasurable)
    (.of_forall fun u ↦ ?_)
  have hd := poissonLogisticDensity_pos u
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hd]
  exact mul_le_of_le_one_right hd.le (abs_cos_le_one _)

theorem poissonLogisticDensity_le_pi_exp (u : ℝ) :
    poissonLogisticDensity u ≤ π * exp (-π * |u|) := by
  have hb := stripNormalizedPoissonExtension_le_majorant (σ := 1) zero_le_one le_rfl (2 * u)
  rw [stripNormalizedPoissonExtension_one] at hb
  calc poissonLogisticDensity u = 2 * limitingStripPoissonDensity (2 * u) :=
        poissonLogisticDensity_eq_limitingStripPoissonDensity u
    _ ≤ 2 * stripPoissonExponentialMajorant (2 * u) :=
        mul_le_mul_of_nonneg_left hb.2 (by norm_num)
    _ = π * exp (-π * |u|) := by
        unfold stripPoissonExponentialMajorant
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        ring_nf

theorem poissonLogisticDensity_abs_moment_integrable (n : ℕ) :
    Integrable fun u : ℝ ↦ poissonLogisticDensity u * |u| ^ n := by
  refine ((integrable_abs_pow_mul_exp_neg_mul_abs n pi_pos).const_mul π).mono'
    (poissonLogisticDensity_integrable.aestronglyMeasurable.mul
      (continuous_abs.pow n).aestronglyMeasurable) (.of_forall fun u ↦ ?_)
  have hd := poissonLogisticDensity_pos u
  have hm : (0 : ℝ) ≤ |u| ^ n := pow_nonneg (abs_nonneg _) _
  rw [Real.norm_of_nonneg (mul_nonneg hd.le hm)]
  calc poissonLogisticDensity u * |u| ^ n ≤ π * exp (-π * |u|) * |u| ^ n :=
        mul_le_mul_of_nonneg_right (poissonLogisticDensity_le_pi_exp u) hm
    _ = π * (|u| ^ n * exp (-π * |u|)) := by ring

/-- The regularized Frullani phase kernel `((1 - e^{-t}) e^{-at} cos (ut) - t e^{-t}) / t²`,
the real part of `Frullani.shiftedCexpKernel` at `z = a - iu`.  The case `a = 0` is the kernel
whose `t`-integral produces the endpoint phase; report (22). -/
def wallisPhaseKernel (a u t : ℝ) : ℝ :=
  ((1 - exp (-t)) * exp (-a * t) * cos (u * t) - t * exp (-t)) / t ^ 2

theorem wallisPhaseKernel_re (a u t : ℝ) :
    (Frullani.shiftedCexpKernel ((a : ℂ) - I * (u : ℂ)) t).re = wallisPhaseKernel a u t := by
  unfold Frullani.shiftedCexpKernel wallisPhaseKernel
  rw [← Complex.ofReal_pow, Complex.div_ofReal_re]
  simp [Complex.mul_re, Complex.exp_re, Complex.exp_im]
  ring

theorem abs_wallisPhaseKernel_le_moment {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) (u : ℝ) {t : ℝ}
    (ht : 0 < t) : |wallisPhaseKernel a u t| ≤ |u| + 2 := by
  have hq0 : (0 : ℝ) < exp (-t) := exp_pos _
  have hr0 : (0 : ℝ) < exp (-a * t) := exp_pos _
  have hq1 : exp (-t) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have hr1 : exp (-a * t) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
  have hq : (0 : ℝ) ≤ 1 - exp (-t) := by linarith
  have hr : (0 : ℝ) ≤ 1 - exp (-a * t) := by linarith
  have hqt : 1 - exp (-t) ≤ t := by linarith [Real.add_one_le_exp (-t)]
  have hrt : 1 - exp (-a * t) ≤ t := by nlinarith [Real.add_one_le_exp (-a * t)]
  have hsq : (0 : ℝ) < t ^ 2 := by positivity
  have b1 : |(1 - exp (-t)) * exp (-a * t) * (cos (u * t) - 1)| ≤ |u| * t ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hq, abs_of_pos hr0]
    calc (1 - exp (-t)) * exp (-a * t) * |cos (u * t) - 1| ≤ t * 1 * (|u| * t) :=
          mul_le_mul (mul_le_mul hqt hr1 hr0.le ht.le)
            (by simpa [abs_mul, abs_of_pos ht] using abs_cos_sub_cos_le (u * t) 0)
            (abs_nonneg _) (by linarith)
      _ = |u| * t ^ 2 := by ring
  have b2 : |1 - exp (-t) - t * exp (-t)| ≤ t ^ 2 := by
    rw [abs_of_nonneg (by nlinarith [Real.add_one_le_exp t, hq0,
      (by rw [← exp_add]; simp : exp t * exp (-t) = 1)] : (0 : ℝ) ≤ 1 - exp (-t) - t * exp (-t))]
    nlinarith
  have b3 : |(1 - exp (-t)) * (1 - exp (-a * t))| ≤ t ^ 2 := by
    rw [abs_of_nonneg (mul_nonneg hq hr)]
    nlinarith [mul_le_mul hqt hrt hr ht.le]
  unfold wallisPhaseKernel
  rw [abs_div, abs_of_pos hsq, div_le_iff₀ hsq,
    show (1 - exp (-t)) * exp (-a * t) * cos (u * t) - t * exp (-t) =
      (1 - exp (-t)) * exp (-a * t) * (cos (u * t) - 1) + (1 - exp (-t) - t * exp (-t)) -
        (1 - exp (-t)) * (1 - exp (-a * t)) by ring]
  calc |(1 - exp (-t)) * exp (-a * t) * (cos (u * t) - 1) + (1 - exp (-t) - t * exp (-t)) -
          (1 - exp (-t)) * (1 - exp (-a * t))|
      ≤ |(1 - exp (-t)) * exp (-a * t) * (cos (u * t) - 1)| + |1 - exp (-t) - t * exp (-t)| +
          |(1 - exp (-t)) * (1 - exp (-a * t))| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ |u| * t ^ 2 + t ^ 2 + t ^ 2 := add_le_add (add_le_add b1 b2) b3
    _ = (|u| + 2) * t ^ 2 := by ring

theorem abs_wallisPhaseKernel_le_tail {a : ℝ} (h0 : 0 ≤ a) (u : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    |wallisPhaseKernel a u t| ≤ 1 / t ^ 2 + exp (-t) := by
  have htp : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hq0 : (0 : ℝ) < exp (-t) := exp_pos _
  have hq1 : exp (-t) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have hr0 : (0 : ℝ) < exp (-a * t) := exp_pos _
  have hr1 : exp (-a * t) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
  have hsq : (0 : ℝ) < t ^ 2 := by positivity
  have hts : t ≤ t ^ 2 := by nlinarith
  have hone : (1 - exp (-t)) * exp (-a * t) ≤ 1 := by nlinarith [mul_pos hq0 hr0]
  have hprod : 0 ≤ (1 - exp (-t)) * exp (-a * t) := mul_nonneg (by linarith) hr0.le
  unfold wallisPhaseKernel
  rw [abs_div, abs_of_pos hsq, div_le_iff₀ hsq]
  calc |(1 - exp (-t)) * exp (-a * t) * cos (u * t) - t * exp (-t)|
      ≤ |(1 - exp (-t)) * exp (-a * t) * cos (u * t)| + |t * exp (-t)| := abs_sub _ _
    _ = (1 - exp (-t)) * exp (-a * t) * |cos (u * t)| + t * exp (-t) := by
        rw [abs_mul, abs_of_nonneg hprod, abs_mul, abs_of_pos htp, abs_of_pos hq0]
    _ ≤ (1 / t ^ 2 + exp (-t)) * t ^ 2 := by
        rw [show (1 / t ^ 2 + exp (-t)) * t ^ 2 = 1 + exp (-t) * t ^ 2 by field_simp]
        nlinarith [abs_cos_le_one (u * t), abs_nonneg (cos (u * t)),
          mul_nonneg hq0.le (sub_nonneg.mpr hts)]

theorem wallisPhaseTail_integrable : IntegrableOn (fun t : ℝ ↦ 1 / t ^ 2 + exp (-t)) (Ioi 1) := by
  have hpow : IntegrableOn (fun t : ℝ ↦ 1 / t ^ 2) (Ioi 1) := by
    refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(2 : ℝ)) < -1) zero_lt_one).congr_fun
      (fun t ht ↦ ?_) measurableSet_Ioi
    change t ^ (-(2 : ℝ)) = 1 / t ^ 2
    rw [Real.rpow_neg (zero_lt_one.trans (mem_Ioi.mp ht)).le, Real.rpow_ofNat]
    simp [one_div]
  refine hpow.add ?_
  simpa using (integrableOn_exp_neg_mul_Ioi (a := (1 : ℝ)) zero_lt_one).mono_set
    (Ioi_subset_Ioi zero_le_one)

theorem poissonLogistic_wallisPhase_integrable :
    Integrable (fun p : ℝ × ℝ ↦ poissonLogisticDensity p.1 * wallisPhaseKernel 0 p.1 p.2)
      (volume.prod (volume.restrict (Ioi 0))) := by
  set F : ℝ × ℝ → ℝ := fun p ↦ poissonLogisticDensity p.1 * wallisPhaseKernel 0 p.1 p.2 with hF
  have hmeas : Measurable F := by
    rw [hF]
    unfold poissonLogisticDensity wallisPhaseKernel
    fun_prop
  have key (s : Set ℝ) : Integrable F (volume.prod (volume.restrict s)) ↔
      IntegrableOn F (univ ×ˢ s) (volume.prod volume) := by
    change _ ↔ Integrable F ((volume.prod volume).restrict (univ ×ˢ s))
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hnear : Integrable F (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    have hfreq : Integrable fun u : ℝ ↦ poissonLogisticDensity u * (|u| + 2) := by
      simpa [Pi.add_apply, pow_one, mul_add, mul_two] using!
        (poissonLogisticDensity_abs_moment_integrable 1).add
          (poissonLogisticDensity_integrable.add poissonLogisticDensity_integrable)
    have hconst : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Ioc (0 : ℝ) 1) :=
      integrableOn_const measure_Ioc_lt_top.ne
    refine (hfreq.mul_prod hconst).mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [(Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_snd)).2
      (.of_forall fun _ ↦ ae_restrict_mem measurableSet_Ioc)] with p hp
    have hd := poissonLogisticDensity_pos p.1
    rw [hF, Real.norm_eq_abs, abs_mul, abs_of_pos hd, mul_one]
    exact mul_le_mul_of_nonneg_left
      (abs_wallisPhaseKernel_le_moment le_rfl zero_le_one p.1 hp.1) hd.le
  have hfar : Integrable F (volume.prod (volume.restrict (Ioi (1 : ℝ)))) := by
    refine (poissonLogisticDensity_integrable.mul_prod wallisPhaseTail_integrable).mono'
      hmeas.aestronglyMeasurable ?_
    filter_upwards [(Measure.ae_prod_iff_ae_ae (measurableSet_Ioi.preimage measurable_snd)).2
      (.of_forall fun _ ↦ ae_restrict_mem measurableSet_Ioi)] with p hp
    have hd := poissonLogisticDensity_pos p.1
    rw [hF, Real.norm_eq_abs, abs_mul, abs_of_pos hd]
    exact mul_le_mul_of_nonneg_left
      (abs_wallisPhaseKernel_le_tail le_rfl p.1 (mem_Ioi.mp hp).le) hd.le
  have hunion : (univ : Set ℝ) ×ˢ Ioi (0 : ℝ) =
      univ ×ˢ Ioc (0 : ℝ) 1 ∪ univ ×ˢ Ioi (1 : ℝ) := by
    rw [← prod_union, Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine (key _).2 ?_
  rw [hunion]
  exact ((key _).1 hnear).union ((key _).1 hfar)

/-- Averaging the Frullani kernel against `p` produces the Wallis Laplace kernel; report (22). -/
theorem integral_poissonLogistic_mul_wallisPhaseKernel {t : ℝ} (ht : 0 < t) :
    (∫ u : ℝ, poissonLogisticDensity u * wallisPhaseKernel 0 u t) =
      Real.Wallis.laplaceKernel t := by
  have h1 : Integrable fun u : ℝ ↦ (1 - exp (-t)) * (poissonLogisticDensity u * cos (t * u)) :=
    (poissonLogistic_cosine_integrable t).const_mul _
  have h2 : Integrable fun u : ℝ ↦ t * exp (-t) * poissonLogisticDensity u :=
    poissonLogisticDensity_integrable.const_mul _
  calc (∫ u : ℝ, poissonLogisticDensity u * wallisPhaseKernel 0 u t)
      = ∫ u : ℝ, ((1 - exp (-t)) * (poissonLogisticDensity u * cos (t * u)) -
          t * exp (-t) * poissonLogisticDensity u) / t ^ 2 := by
        refine integral_congr_ae ?_
        filter_upwards with u
        unfold wallisPhaseKernel
        rw [neg_zero, zero_mul, exp_zero, mul_one, mul_comm u t]
        ring
    _ = ((1 - exp (-t)) * (∫ u : ℝ, poissonLogisticDensity u * cos (t * u)) -
          t * exp (-t) * ∫ u : ℝ, poissonLogisticDensity u) / t ^ 2 := by
        rw [integral_div, integral_sub h1 h2, integral_const_mul, integral_const_mul]
    _ = ((1 - exp (-t)) * (t / sinh t) - t * exp (-t)) / t ^ 2 := by
        rw [poissonLogistic_cosine_transform t, ite_eq_right ht.ne',
          integral_poissonLogisticDensity]
        ring
    _ = Real.Wallis.laplaceKernel t := by
        have hsinh : sinh t ≠ 0 := sinh_ne_zero.mpr ht.ne'
        have hexp : exp t * exp (-t) = 1 := by rw [← exp_add]; simp
        have hdiff : exp t - exp (-t) ≠ 0 := fun h ↦ hsinh (by rw [sinh_eq, h]; norm_num)
        unfold Real.Wallis.laplaceKernel
        rw [sinh_eq]
        field_simp [ht.ne', (exp_pos (-t)).ne', hdiff, (by positivity : 1 + exp (-t) ≠ 0)]
        nlinarith [hexp]

/-- The dominating function for the regularized Frullani kernels on `(0, ∞)`. -/
def wallisPhaseMajorant (u t : ℝ) : ℝ := if t ≤ 1 then |u| + 2 else 1 / t ^ 2 + exp (-t)

theorem wallisPhaseMajorant_integrable (u : ℝ) : IntegrableOn (wallisPhaseMajorant u) (Ioi 0) := by
  have hconst : IntegrableOn (fun _ : ℝ ↦ |u| + 2) (Ioc (0 : ℝ) 1) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hnear : IntegrableOn (wallisPhaseMajorant u) (Ioc (0 : ℝ) 1) :=
    hconst.congr_fun (fun t ht ↦ by simp [wallisPhaseMajorant, ht.2]) measurableSet_Ioc
  have hfar : IntegrableOn (wallisPhaseMajorant u) (Ioi (1 : ℝ)) :=
    wallisPhaseTail_integrable.congr_fun
      (fun t ht ↦ by simp [wallisPhaseMajorant, not_le.mpr (mem_Ioi.mp ht)]) measurableSet_Ioi
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact hnear.union hfar

theorem tendsto_integral_wallisPhaseKernel (u : ℝ) :
    Tendsto (fun n : ℕ ↦ ∫ t : ℝ in Ioi 0, wallisPhaseKernel (1 / ((n : ℝ) + 1)) u t) atTop
      (𝓝 (∫ t : ℝ in Ioi 0, wallisPhaseKernel 0 u t)) := by
  refine tendsto_integral_of_dominated_convergence (wallisPhaseMajorant u)
    (fun n ↦ (by unfold wallisPhaseKernel; fun_prop :
      Measurable fun t : ℝ ↦ wallisPhaseKernel (1 / ((n : ℝ) + 1)) u t).aestronglyMeasurable)
    (wallisPhaseMajorant_integrable u) (fun n ↦ ?_)
    (.of_forall fun t ↦ (by unfold wallisPhaseKernel; fun_prop :
      Continuous fun a : ℝ ↦ wallisPhaseKernel a u t).continuousAt.tendsto.comp
        tendsto_one_div_add_atTop_nhds_zero_nat)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have h0 : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
  have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  rw [Real.norm_eq_abs]
  by_cases hone : t ≤ 1
  · simpa only [wallisPhaseMajorant, ite_eq_left hone] using
      abs_wallisPhaseKernel_le_moment h0 h1 u ht
  · simpa only [wallisPhaseMajorant, ite_eq_right hone] using
      abs_wallisPhaseKernel_le_tail h0 u (not_le.mp hone).le

/-- The real part of the Frullani antiderivative `1 + z log z - (z + 1) log (z + 1)`. -/
def wallisComplexLogPhase (z : ℂ) : ℝ := (1 + z * Complex.log z - (z + 1) * Complex.log (z + 1)).re

theorem integral_wallisPhaseKernel {a : ℝ} (ha : 0 < a) (u : ℝ) :
    (∫ t : ℝ in Ioi 0, wallisPhaseKernel a u t) =
      wallisComplexLogPhase ((a : ℂ) - I * (u : ℂ)) := by
  have hz : 0 < ((a : ℂ) - I * (u : ℂ)).re := by simpa using ha
  calc (∫ t : ℝ in Ioi 0, wallisPhaseKernel a u t)
      = ∫ t : ℝ in Ioi 0, (Frullani.shiftedCexpKernel ((a : ℂ) - I * (u : ℂ)) t).re :=
        setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ (wallisPhaseKernel_re a u t).symm
    _ = (∫ t : ℝ in Ioi 0, Frullani.shiftedCexpKernel ((a : ℂ) - I * (u : ℂ)) t).re :=
        integral_re (Frullani.integrableOn_shiftedCexpKernel hz)
    _ = wallisComplexLogPhase ((a : ℂ) - I * (u : ℂ)) := by
        rw [Frullani.integral_shiftedCexpKernel hz, wallisComplexLogPhase]

theorem arg_one_sub_I_mul (u : ℝ) : Complex.arg (1 - I * (u : ℂ)) = -arctan u := by
  have hrange : |Complex.arg (1 - I * (u : ℂ))| < π / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by simp))
  rw [← arctan_tan (abs_lt.mp hrange).1 (abs_lt.mp hrange).2,
    show tan (Complex.arg (1 - I * (u : ℂ))) = -u by simp, arctan_neg]

theorem neg_I_mul_log_re (u : ℝ) :
    ((-I * (u : ℂ)) * Complex.log (-I * (u : ℂ))).re = -π * |u| / 2 := by
  rcases lt_trichotomy u 0 with h | rfl | h
  · rw [Complex.mul_re, Complex.log_im, show Complex.arg (-I * (u : ℂ)) = π / 2 from
      Complex.arg_eq_pi_div_two_iff.mpr ⟨by simp, by simpa using neg_pos.mpr h⟩, abs_of_neg h]
    simp
    ring
  · simp
  · rw [Complex.mul_re, Complex.log_im, show Complex.arg (-I * (u : ℂ)) = -(π / 2) from
      Complex.arg_eq_neg_pi_div_two_iff.mpr ⟨by simp, by simpa using neg_neg_of_pos h⟩,
      abs_of_pos h]
    simp
    ring

theorem one_sub_I_mul_log_re (u : ℝ) : ((1 - I * (u : ℂ)) * Complex.log (1 - I * (u : ℂ))).re =
    log (1 + u ^ 2) / 2 - u * arctan u := by
  have hnorm : ‖1 - I * (u : ℂ)‖ = √(1 + u ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    simp
    ring
  rw [Complex.mul_re, Complex.log_re, Complex.log_im, hnorm, arg_one_sub_I_mul,
    Real.log_sqrt (by positivity)]
  simp

theorem abs_mul_arctan_abs (u : ℝ) : |u| * arctan |u| = u * arctan u := by
  rcases abs_cases u with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
  · rw [h, arctan_neg]; ring

theorem wallisComplexLogPhase_neg_I_mul (u : ℝ) :
    wallisComplexLogPhase (-I * (u : ℂ)) = 1 + lowerEndpointPhase (2 * u) := by
  unfold wallisComplexLogPhase
  rw [show -I * (u : ℂ) + 1 = 1 - I * (u : ℂ) by ring, Complex.sub_re, Complex.add_re,
    neg_I_mul_log_re, one_sub_I_mul_log_re]
  simp only [Complex.one_re]
  unfold lowerEndpointPhase
  rw [show |(2 : ℝ) * u| = 2 * |u| by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)],
    show 1 + (2 * u) ^ 2 / 4 = 1 + u ^ 2 by ring, show 2 * |u| / 2 = |u| by ring,
    abs_mul_arctan_abs]
  ring

theorem wallisComplexLogPhase_ofReal {a : ℝ} (ha : 0 ≤ a) :
    wallisComplexLogPhase (a : ℂ) = 1 + a * log a - (a + 1) * log (a + 1) := by
  have hnorm : ‖(a : ℂ) + 1‖ = a + 1 := by
    rw [show (a : ℂ) + 1 = (a + 1 : ℝ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ a + 1)]
  unfold wallisComplexLogPhase
  simp [Complex.mul_re, Complex.log_re, hnorm, abs_of_nonneg ha]

theorem tendsto_wallisComplexLogPhase (u : ℝ) :
    Tendsto (fun n : ℕ ↦ wallisComplexLogPhase ((1 / ((n : ℝ) + 1) : ℝ) - I * (u : ℂ)))
      atTop (𝓝 (1 + lowerEndpointPhase (2 * u))) := by
  have hparam : Tendsto (fun n : ℕ ↦ (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  rcases eq_or_ne u 0 with rfl | hu
  · have hreal : ContinuousAt (fun a : ℝ ↦ 1 + a * log a - (a + 1) * log (a + 1)) 0 :=
      ((continuous_const.add continuous_mul_log).sub
        (continuous_mul_log.comp (by fun_prop : Continuous fun a : ℝ ↦ a + 1))).continuousAt
    have hlimit : Tendsto (fun n : ℕ ↦ 1 + (1 / ((n : ℝ) + 1) : ℝ) * log (1 / ((n : ℝ) + 1)) -
        ((1 / ((n : ℝ) + 1) : ℝ) + 1) * log ((1 / ((n : ℝ) + 1) : ℝ) + 1)) atTop (𝓝 (1 : ℝ)) := by
      simpa only [Function.comp_apply, zero_mul, mul_zero, zero_add, add_zero, one_mul,
        Real.log_one, sub_zero] using! hreal.tendsto.comp hparam
    have hcomputed : Tendsto (fun n : ℕ ↦ wallisComplexLogPhase (1 / ((n : ℝ) + 1) : ℝ))
        atTop (𝓝 (1 : ℝ)) :=
      hlimit.congr fun n ↦ (wallisComplexLogPhase_ofReal (by positivity)).symm
    simpa [lowerEndpointPhase] using! hcomputed
  · have hmain : ∀ {v : ℕ → ℂ} {z : ℂ}, Tendsto v atTop (𝓝 z) → z ∈ Complex.slitPlane →
        z + 1 ∈ Complex.slitPlane →
        Tendsto (fun n ↦ wallisComplexLogPhase (v n)) atTop (𝓝 (wallisComplexLogPhase z)) := by
      intro v z hv h1 h2
      simpa only [wallisComplexLogPhase, Function.comp_apply] using!
        Complex.continuous_re.continuousAt.tendsto.comp
          ((tendsto_const_nhds.add (hv.mul (hv.clog h1))).sub
            ((hv.add_const 1).mul ((hv.add_const 1).clog h2)))
    have hz : Tendsto (fun n : ℕ ↦ (1 / ((n : ℝ) + 1) : ℝ) - I * (u : ℂ)) atTop
        (𝓝 (-I * (u : ℂ))) := by
      simpa using (Complex.continuous_ofReal.continuousAt.tendsto.comp hparam).sub
        (tendsto_const_nhds (x := I * (u : ℂ)))
    rw [← wallisComplexLogPhase_neg_I_mul u]
    exact hmain hz (Complex.mem_slitPlane_iff.mpr (Or.inr (by simpa using hu)))
      (Complex.mem_slitPlane_iff.mpr (Or.inl (by simp)))

/-- Report (22) at `a = 0`: the Frullani kernel integrates to `1 + φ(2u)`. -/
theorem integral_wallisPhaseKernel_zero (u : ℝ) :
    (∫ t : ℝ in Ioi 0, wallisPhaseKernel 0 u t) = 1 + lowerEndpointPhase (2 * u) := by
  refine tendsto_nhds_unique (tendsto_integral_wallisPhaseKernel u) ?_
  have hid (n : ℕ) : (∫ t : ℝ in Ioi 0, wallisPhaseKernel (1 / ((n : ℝ) + 1)) u t) =
      wallisComplexLogPhase ((1 / ((n : ℝ) + 1) : ℝ) - I * (u : ℂ)) :=
    integral_wallisPhaseKernel (by positivity) u
  simp_rw [hid]
  exact tendsto_wallisComplexLogPhase u

theorem integral_poissonLogistic_one_add_lowerEndpointPhase :
    (∫ u : ℝ, poissonLogisticDensity u * (1 + lowerEndpointPhase (2 * u))) = log (π / 2) := by
  calc (∫ u : ℝ, poissonLogisticDensity u * (1 + lowerEndpointPhase (2 * u)))
      = ∫ u : ℝ, ∫ t : ℝ in Ioi 0, poissonLogisticDensity u * wallisPhaseKernel 0 u t := by
        refine integral_congr_ae ?_
        filter_upwards with u
        rw [integral_const_mul, integral_wallisPhaseKernel_zero]
    _ = ∫ t : ℝ in Ioi 0, ∫ u : ℝ, poissonLogisticDensity u * wallisPhaseKernel 0 u t :=
        integral_integral_swap poissonLogistic_wallisPhase_integrable
    _ = ∫ t : ℝ in Ioi 0, Real.Wallis.laplaceKernel t :=
        setIntegral_congr_fun measurableSet_Ioi fun t ht ↦
          integral_poissonLogistic_mul_wallisPhaseKernel ht
    _ = log (π / 2) := Real.Wallis.integral_laplaceKernel

theorem poissonLogistic_lowerEndpointPhase_integrable :
    Integrable fun u : ℝ ↦ poissonLogisticDensity u * lowerEndpointPhase (2 * u) := by
  have hone : Integrable fun u : ℝ ↦
      poissonLogisticDensity u * (1 + lowerEndpointPhase (2 * u)) := by
    refine poissonLogistic_wallisPhase_integrable.integral_prod_left.congr ?_
    filter_upwards with u
    rw [integral_const_mul, integral_wallisPhaseKernel_zero]
  refine (hone.sub poissonLogisticDensity_integrable).congr ?_
  filter_upwards with u
  change poissonLogisticDensity u * (1 + lowerEndpointPhase (2 * u)) - poissonLogisticDensity u =
    poissonLogisticDensity u * lowerEndpointPhase (2 * u)
  ring

theorem integral_poissonLogistic_lowerEndpointPhase :
    (∫ u : ℝ, poissonLogisticDensity u * lowerEndpointPhase (2 * u)) = log (π / 2) - 1 := by
  have hsplit : (∫ u : ℝ, poissonLogisticDensity u * (1 + lowerEndpointPhase (2 * u))) =
      (∫ u : ℝ, poissonLogisticDensity u) +
        ∫ u : ℝ, poissonLogisticDensity u * lowerEndpointPhase (2 * u) := by
    rw [← integral_add poissonLogisticDensity_integrable
      poissonLogistic_lowerEndpointPhase_integrable]
    exact integral_congr_ae (.of_forall fun u ↦ by ring)
  have h := integral_poissonLogistic_one_add_lowerEndpointPhase
  rw [hsplit, integral_poissonLogisticDensity] at h
  linarith

/-- Lemma 3.4 of the report: `J_σ → log (π/2) - 1` as `σ ↑ 1`. -/
theorem limitingPoissonEndpointExpectation_eq_log_pi_div_two_sub_one :
    limitingPoissonEndpointExpectation = log (π / 2) - 1 := by
  have hscale : (∫ u : ℝ, limitingStripPoissonDensity (2 * u) * lowerEndpointPhase (2 * u)) =
      (1 / 2 : ℝ) * limitingPoissonEndpointExpectation := by
    unfold limitingPoissonEndpointExpectation
    simpa [smul_eq_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ)⁻¹)] using!
      Measure.integral_comp_mul_left
        (fun T : ℝ ↦ limitingStripPoissonDensity T * lowerEndpointPhase T) 2
  have hlogistic : (∫ u : ℝ, poissonLogisticDensity u * lowerEndpointPhase (2 * u)) =
      2 * ∫ u : ℝ, limitingStripPoissonDensity (2 * u) * lowerEndpointPhase (2 * u) := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards with u
    rw [poissonLogisticDensity_eq_limitingStripPoissonDensity]
    ring
  linarith [integral_poissonLogistic_lowerEndpointPhase]

/-- The sharp threshold of report (23): `log (2πe c²) + lim J_σ = log (π² c²)`. -/
theorem lowerPoissonEndpointSharpCoefficient_eq {c : ℝ} (hc : 0 < c) :
    log (2 * π * exp 1 * c ^ 2) + limitingPoissonEndpointExpectation = log (π ^ 2 * c ^ 2) := by
  rw [limitingPoissonEndpointExpectation_eq_log_pi_div_two_sub_one]
  have h1 : log (2 * π * exp 1 * c ^ 2) + log (π / 2) = log (π ^ 2 * c ^ 2 * exp 1) := by
    rw [← Real.log_mul (by positivity) (by positivity : π / 2 ≠ 0)]
    ring_nf
  rw [Real.log_mul (by positivity : π ^ 2 * c ^ 2 ≠ 0) (exp_ne_zero 1), Real.log_exp] at h1
  linarith

theorem lowerPoissonEndpointSharpCoefficient_neg {c : ℝ} (hc : 0 < c) (hsharp : c < π⁻¹) :
    log (2 * π * exp 1 * c ^ 2) + limitingPoissonEndpointExpectation < 0 := by
  have hpc : π * c < 1 := by
    have h := mul_lt_mul_of_pos_left hsharp pi_pos
    rwa [mul_inv_cancel₀ pi_ne_zero] at h
  rw [lowerPoissonEndpointSharpCoefficient_eq hc]
  exact Real.log_neg (by positivity) (by nlinarith [mul_pos pi_pos hc])

theorem tendsto_lowerPoissonEndpointSharpCoefficient {c : ℝ} (hc : 0 < c) :
    Tendsto (fun σ : ℝ ↦ log (2 * π * exp 1 * c ^ 2) + lowerPoissonEndpointExpectation σ)
      (𝓝[<] 1) (𝓝 (log (π ^ 2 * c ^ 2))) := by
  rw [← lowerPoissonEndpointSharpCoefficient_eq hc]
  exact tendsto_const_nhds.add tendsto_lowerPoissonEndpointExpectation

/-- Report (23): for `c < 1/π` the sharp coefficient is eventually negative as `σ ↑ 1`. -/
theorem eventually_lowerPoissonEndpointSharpCoefficient_neg {c : ℝ} (hc : 0 < c)
    (hsharp : c < π⁻¹) : ∀ᶠ σ : ℝ in 𝓝[<] 1,
      log (2 * π * exp 1 * c ^ 2) + lowerPoissonEndpointExpectation σ < 0 := by
  refine tendsto_lowerPoissonEndpointSharpCoefficient hc (Iio_mem_nhds ?_)
  rw [← lowerPoissonEndpointSharpCoefficient_eq hc]
  exact lowerPoissonEndpointSharpCoefficient_neg hc hsharp

end

end CohnElkies
