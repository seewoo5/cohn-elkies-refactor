import CohnElkies.LowerBound.CappedMajorization

/-!
# The Poisson majorant is maximal at the centre and negative (report §3.3, Lemmas 3.3–3.4)

The Poisson convolution `∫ P_σ(s - x) f(x) dx` of an even weight antitone on `[0, ∞)` is maximal
at `s = 0`, hence the majorant of the strip function is controlled by its value at the centre;
the rescaled Gamma boundary function is compared with its Riemann sum, and the central bound is
split into a core and a logarithmic tail. The upshot is an integrable majorant of `|Z|` on the
line `Im z = -σ d/2` with total mass at most `1/2 + o(1)`, uniformly for large `d`
(`exists_lowerStripPoissonMajorant_integrable_majorant`, `norm_Z_g_le_exp_H_σ`).
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory Metric Real Set
open scoped ENNReal Interval Topology

theorem measurable_stripPoissonKernel_sub (σ s : ℝ) : Measurable fun x : ℝ ↦ P_σ σ (s - x) := by
  unfold P_σ θ
  fun_prop

/-- The measure `P_σ σ (s - x) dx`, used to compare the Poisson convolution at `s` with the
one at the centre `s = 0`. -/
def stripPoissonWeightedMeasure (σ s : ℝ) : Measure ℝ :=
  volume.withDensity fun x : ℝ ↦ ENNReal.ofReal (P_σ σ (s - x))

theorem stripPoissonWeightedMeasure_centered_interval_max {σ : ℝ} (hbelow : -1 < σ)
    (habove : σ < 1) {r : ℝ} (hr : 0 ≤ r) (s : ℝ) :
    stripPoissonWeightedMeasure σ s (Icc (-r) r) ≤
      stripPoissonWeightedMeasure σ 0 (Icc (-r) r) := by
  have happly (t : ℝ) : stripPoissonWeightedMeasure σ t (Icc (-r) r) =
      ENNReal.ofReal (∫ x in Icc (-r) r, P_σ σ (t - x)) := by
    unfold stripPoissonWeightedMeasure
    rw [withDensity_apply _ measurableSet_Icc]
    exact (ofReal_integral_eq_lintegral_ofReal
      ((stripPoissonKernel_integrable hbelow habove).comp_sub_left t).integrableOn
      (Eventually.of_forall fun x ↦ (stripPoissonKernel_pos hbelow habove (t - x)).le)).symm
  have hshift : (∫ x in Icc (-r) r, P_σ σ (s - x)) = ∫ x in Icc (s - r) (s + r), P_σ σ x := by
    rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -r ≤ r),
      ← intervalIntegral.integral_of_le (by linarith : s - r ≤ s + r),
      intervalIntegral.integral_comp_sub_left]
    congr 1
    ring
  have hcentre : (∫ x in Icc (-r) r, P_σ σ (0 - x)) = ∫ x in Icc (-r) r, P_σ σ x :=
    setIntegral_congr_fun measurableSet_Icc fun x _ ↦ by rw [zero_sub, stripPoissonKernel_neg]
  rw [happly, happly, hshift, hcentre]
  exact ENNReal.ofReal_le_ofReal (stripPoissonKernel_centered_interval_max hbelow habove hr s)

theorem stripPoissonKernel_weighted_product_integrable {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    {f : ℝ → ℝ} (hf : Integrable f) (s : ℝ) : Integrable fun x : ℝ ↦ P_σ σ (s - x) * f x := by
  refine (hf.norm.const_mul (P_σ σ 0)).mono'
    ((measurable_stripPoissonKernel_sub σ s).aestronglyMeasurable.mul hf.aestronglyMeasurable) ?_
  filter_upwards with x
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (stripPoissonKernel_pos hbelow habove (s - x))]
  exact mul_le_mul_of_nonneg_right
    (stripPoissonKernel_antitone_abs hbelow habove (x := 0) (y := s - x) (by simp)) (norm_nonneg _)

theorem stripPoissonWeightedMeasure_integrable {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    {f : ℝ → ℝ} (hf : Integrable f) (s : ℝ) :
    Integrable f (stripPoissonWeightedMeasure σ s) := by
  change Integrable f (volume.withDensity fun x : ℝ ↦ ((P_σ σ (s - x)).toNNReal : ℝ≥0∞))
  refine (integrable_withDensity_iff_integrable_smul
    (measurable_stripPoissonKernel_sub σ s).real_toNNReal).2
      ((stripPoissonKernel_weighted_product_integrable hbelow habove hf s).congr ?_)
  filter_upwards with x
  simp [NNReal.smul_def, Real.coe_toNNReal _ (stripPoissonKernel_pos hbelow habove (s - x)).le]

theorem stripPoissonWeightedMeasure_integral {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    (f : ℝ → ℝ) (s : ℝ) :
    (∫ x : ℝ, f x ∂stripPoissonWeightedMeasure σ s) = ∫ x : ℝ, P_σ σ (s - x) * f x := by
  unfold stripPoissonWeightedMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_stripPoissonKernel_sub σ s).ennreal_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [ENNReal.toReal_ofReal (stripPoissonKernel_pos hbelow habove (s - x)).le, smul_eq_mul]

/-- An even, nonnegative, compactly supported weight that is antitone on `[0, ∞)` has its
Poisson convolution maximal at the centre. -/
theorem even_antitone_poisson_convolution_max {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    {f : ℝ → ℝ} {B : ℝ} (hf : Integrable f) (hfmeas : Measurable f) (hfnonneg : ∀ x : ℝ, 0 ≤ f x)
    (heven : ∀ x : ℝ, f (-x) = f x) (hanti : AntitoneOn f (Ici (0 : ℝ)))
    (hsupport : Function.support f ⊆ Icc (-B) B) (s : ℝ) :
    (∫ x : ℝ, P_σ σ (s - x) * f x) ≤ ∫ x : ℝ, P_σ σ (0 - x) * f x := by
  have hsuperlevel : ∀ t : ℝ, 0 < t → stripPoissonWeightedMeasure σ s {x : ℝ | t < f x} ≤
      stripPoissonWeightedMeasure σ 0 {x : ℝ | t < f x} := by
    intro t ht
    obtain ⟨r, hr, hinner, houter⟩ := even_antitone_superlevel_interval heven hanti hsupport ht
    calc stripPoissonWeightedMeasure σ s {x : ℝ | t < f x}
        ≤ stripPoissonWeightedMeasure σ s (Icc (-r) r) := measure_mono houter
      _ ≤ stripPoissonWeightedMeasure σ 0 (Icc (-r) r) :=
          stripPoissonWeightedMeasure_centered_interval_max hbelow habove hr s
      _ = stripPoissonWeightedMeasure σ 0 (Ioo (-r) r) := by
          unfold stripPoissonWeightedMeasure
          exact (measure_congr Ioo_ae_eq_Icc).symm
      _ ≤ stripPoissonWeightedMeasure σ 0 {x : ℝ | t < f x} := measure_mono hinner
  have hlin : (∫⁻ x : ℝ, ENNReal.ofReal (f x) ∂stripPoissonWeightedMeasure σ s) ≤
      ∫⁻ x : ℝ, ENNReal.ofReal (f x) ∂stripPoissonWeightedMeasure σ 0 := by
    rw [lintegral_eq_lintegral_meas_lt _ (Eventually.of_forall hfnonneg) hfmeas.aemeasurable,
      lintegral_eq_lintegral_meas_lt _ (Eventually.of_forall hfnonneg) hfmeas.aemeasurable]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hsuperlevel t ht
  rw [← ofReal_integral_eq_lintegral_ofReal
      (stripPoissonWeightedMeasure_integrable hbelow habove hf s) (Eventually.of_forall hfnonneg),
    ← ofReal_integral_eq_lintegral_ofReal
      (stripPoissonWeightedMeasure_integrable hbelow habove hf 0) (Eventually.of_forall hfnonneg),
    stripPoissonWeightedMeasure_integral hbelow habove,
    stripPoissonWeightedMeasure_integral hbelow habove] at hlin
  refine (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun x ↦ ?_)).mp hlin
  exact mul_nonneg (stripPoissonKernel_pos hbelow habove (0 - x)).le (hfnonneg x)

/-- Report Lemma 3.5: far from the origin the scaled boundary majorant is below any level. -/
theorem lowerGammaBoundaryLog_dimension_scaled_le_neg_of_large {d : ℕ} (hd : 2 ≤ d) {c Y n : ℝ}
    (hc : 0 < c) (hn : 0 ≤ n) (hlarge : max 1 (8 * π * c ^ 2 * exp n) ≤ |Y|) :
    h_ℓ ((d : ℝ) / 2) (c * √d) ((d : ℝ) / 2 * Y) ≤ -n := by
  have hyone : 1 ≤ |Y| := (le_max_left 1 _).trans hlarge
  have hY : Y ≠ 0 := by
    rintro rfl
    rw [abs_zero] at hyone
    linarith
  have hden : 0 < |Y| := by linarith
  have hA : 0 < 4 * π * c ^ 2 := by positivity
  have hexpcancel : exp n * exp (-n) = 1 := by
    rw [Real.exp_neg, mul_inv_cancel₀ (Real.exp_ne_zero n)]
  have hscaled := mul_le_mul_of_nonneg_right ((le_max_right 1 _).trans hlarge)
    (Real.exp_pos (-n)).le
  have hratio : 4 * π * c ^ 2 / |Y| ≤ 1 / 2 * exp (-n) := by
    rw [div_le_iff₀ hden]
    nlinarith
  have hlogratio : log (4 * π * c ^ 2 / |Y|) ≤ -log 2 - n := by
    calc log (4 * π * c ^ 2 / |Y|) ≤ log (1 / 2 * exp (-n)) :=
          Real.log_le_log (by positivity) hratio
      _ = -log 2 - n := by
          rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp, one_div, Real.log_inv]
          ring
  have hℓ : 1 ≤ (d : ℝ) / 2 := (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by exact_mod_cast hd)
  have hlogtwo : (1 : ℝ) / 2 ≤ log 2 := by linarith [Real.log_two_gt_d9]
  have hmain : (d : ℝ) / 2 * log (4 * π * c ^ 2 / |Y|) ≤ -log 2 - n := by
    linarith [mul_le_mul_of_nonneg_left hlogratio (by positivity : (0 : ℝ) ≤ (d : ℝ) / 2),
      mul_nonneg (sub_nonneg.mpr hℓ) (by linarith : (0 : ℝ) ≤ log 2 + n)]
  linarith [lowerGammaBoundaryLog_dimension_scaled_log_tail_uniform hd hc hY,
    log_coth_pi_mul_abs_div_two_le_one hyone]

/-- The scaled capped majorant, shifted up by `n` and clipped at `0`: an even, nonnegative,
compactly supported weight. -/
def lowerGammaScaledCappedClipped (d : ℕ) (c D n Y : ℝ) : ℝ :=
  max (h_ℓD ((d : ℝ) / 2) (c * √d) D ((d : ℝ) / 2 * Y) + n) 0

theorem lowerGammaScaledCappedClipped_continuous {d : ℕ} (hd : 0 < d) (c D n : ℝ) :
    Continuous (lowerGammaScaledCappedClipped d c D n) :=
  (((lowerGammaBoundaryCapped_continuous (half_pos (Nat.cast_pos.mpr hd)) (c * √d) D).comp
    (continuous_const.mul continuous_id)).add continuous_const).max continuous_const

theorem lowerGammaScaledCappedClipped_neg (d : ℕ) (c D n Y : ℝ) :
    lowerGammaScaledCappedClipped d c D n (-Y) = lowerGammaScaledCappedClipped d c D n Y := by
  have hcap (y : ℝ) : h_ℓD ((d : ℝ) / 2) (c * √d) D (-y) = h_ℓD ((d : ℝ) / 2) (c * √d) D y := by
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · simp [h_ℓD, hy, lowerGammaBoundaryLog_dimension_neg (c * √d) hy]
  unfold lowerGammaScaledCappedClipped
  rw [show (d : ℝ) / 2 * -Y = -((d : ℝ) / 2 * Y) by ring, hcap]

theorem lowerGammaScaledCappedClipped_antitoneOn (d : ℕ) (c D n : ℝ) :
    AntitoneOn (lowerGammaScaledCappedClipped d c D n) (Ici (0 : ℝ)) := by
  have hcap : AntitoneOn (h_ℓD ((d : ℝ) / 2) (c * √d) D) (Ici (0 : ℝ)) := by
    intro x hx y hy hxy
    simp only [mem_Ici] at hx hy
    rcases hx.eq_or_lt with rfl | hxpos
    · simp only [h_ℓD]
      split_ifs
      · exact le_rfl
      · exact min_le_right _ _
    · have hypos : 0 < y := hxpos.trans_le hxy
      simp only [h_ℓD, if_neg hxpos.ne', if_neg hypos.ne']
      exact min_le_min (lowerGammaBoundaryLog_dimension_antitoneOn _ (mem_Ioi.mpr hxpos)
        (mem_Ioi.mpr hypos) hxy) le_rfl
  intro x hx y hy hxy
  simp only [mem_Ici] at hx hy
  have hℓ : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have h := hcap (mem_Ici.mpr (mul_nonneg hℓ hx)) (mem_Ici.mpr (mul_nonneg hℓ hy))
    (mul_le_mul_of_nonneg_left hxy hℓ)
  exact max_le_max (by linarith) le_rfl

theorem lowerGammaScaledCappedClipped_support {d : ℕ} (hd : 2 ≤ d) {c D n : ℝ} (hc : 0 < c)
    (hn : 0 ≤ n) :
    Function.support (lowerGammaScaledCappedClipped d c D n) ⊆
      Icc (-(max 1 (8 * π * c ^ 2 * exp n))) (max 1 (8 * π * c ^ 2 * exp n)) := by
  intro Y hY
  have hsmall : |Y| < max 1 (8 * π * c ^ 2 * exp n) := by
    by_contra! hlarge
    have hyone : 1 ≤ |Y| := (le_max_left 1 _).trans hlarge
    have hℓ : 0 < (d : ℝ) / 2 := by positivity
    have harg : (d : ℝ) / 2 * Y ≠ 0 := mul_ne_zero hℓ.ne' fun h ↦ by
      rw [h, abs_zero] at hyone; linarith
    refine hY ?_
    unfold lowerGammaScaledCappedClipped
    rw [h_ℓD, if_neg harg]
    exact max_eq_right (by
      linarith [min_le_left (h_ℓ ((d : ℝ) / 2) (c * √d) ((d : ℝ) / 2 * Y)) D,
        lowerGammaBoundaryLog_dimension_scaled_le_neg_of_large hd hc hn hlarge])
  exact ⟨(neg_lt_of_abs_lt hsmall).le, (lt_of_abs_lt hsmall).le⟩

theorem lowerGammaScaledCappedClipped_poisson_convolution_max {d : ℕ} (hd : 2 ≤ d) {c D n σ : ℝ}
    (hc : 0 < c) (hn : 0 ≤ n) (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    (∫ Y : ℝ, P_σ σ (s - Y) * lowerGammaScaledCappedClipped d c D n Y) ≤
      ∫ Y : ℝ, P_σ σ (0 - Y) * lowerGammaScaledCappedClipped d c D n Y := by
  have hcont := lowerGammaScaledCappedClipped_continuous (d := d) (by omega) c D n
  exact even_antitone_poisson_convolution_max hbelow habove
    (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_support_subset_isCompact
      isCompact_Icc (lowerGammaScaledCappedClipped_support hd hc hn)))
    hcont.measurable (fun _ ↦ le_max_right _ _) (lowerGammaScaledCappedClipped_neg d c D n)
    (lowerGammaScaledCappedClipped_antitoneOn d c D n)
    (lowerGammaScaledCappedClipped_support hd hc hn) s

/-- Transfer of an integrability statement for the holomorphic kernel `K'_λ` on the line
`Im z = σλ` into the real Poisson convolution with boundary datum `g`. -/
theorem scaled_poisson_product_integrable {d : ℕ} (hd : 0 < d) {σ s : ℝ} {g : ℝ → ℝ}
    (hbelow : -1 < σ) (habove : σ < 1)
    (houter : ∀ z ∈ Complex.im ⁻¹' Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2),
      Integrable fun y : ℝ ↦ K'_ℓ ((d : ℝ) / 2) z y * (g y : ℂ)) :
    Integrable fun Y : ℝ ↦ P_σ σ (s - Y) * g ((d : ℝ) / 2 * Y) := by
  have hℓ : 0 < (d : ℝ) / 2 := half_pos (Nat.cast_pos.mpr hd)
  have hz : ((d : ℝ) / 2 * s : ℝ) + I * ((σ : ℂ) * ((d : ℝ) / 2 : ℝ)) ∈
      Complex.im ⁻¹' Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2) := by
    simp only [mem_preimage, mem_Ioo, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul, Complex.I_im, one_mul, zero_add,
      mul_zero, sub_zero, add_zero]
    exact ⟨by nlinarith [mul_pos (show 0 < 1 + σ by linarith) hℓ],
      by nlinarith [mul_pos (show 0 < 1 - σ by linarith) hℓ]⟩
  refine (((houter _ hz).re.comp_mul_left' hℓ.ne').const_mul ((d : ℝ) / 2)).congr ?_
  filter_upwards with Y
  rw [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, stripRegularizedHolomorphicPoissonKernel_re hℓ hbelow habove,
    show ((d : ℝ) / 2 * s - (d : ℝ) / 2 * Y) / ((d : ℝ) / 2) = s - Y by field_simp]
  field_simp

theorem lowerGammaScaledCapped_poisson_product_integrable {d : ℕ} (hd : 0 < d) {R D σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    Integrable fun Y : ℝ ↦ P_σ σ (s - Y) * h_ℓD ((d : ℝ) / 2) R D ((d : ℝ) / 2 * Y) :=
  scaled_poisson_product_integrable hd hbelow habove fun _ hz ↦
    lowerStripCappedGammaOuter_integrable_dimension hd hz

theorem lowerGammaScaled_poisson_product_integrable {d : ℕ} (hd : 0 < d) {R σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    Integrable fun Y : ℝ ↦ P_σ σ (s - Y) * h_ℓ ((d : ℝ) / 2) R ((d : ℝ) / 2 * Y) :=
  scaled_poisson_product_integrable hd hbelow habove fun _ hz ↦
    lowerStripGammaOuter_integrable_dimension hd hz

/-- The scaled capped majorant clipped from below at `-n`. -/
def lowerGammaScaledCappedLowerClip (d : ℕ) (c D n Y : ℝ) : ℝ :=
  max (h_ℓD ((d : ℝ) / 2) (c * √d) D ((d : ℝ) / 2 * Y)) (-n)

theorem lowerGammaScaledCappedClipped_eq_lowerClip_add (d : ℕ) (c D n Y : ℝ) :
    lowerGammaScaledCappedClipped d c D n Y = lowerGammaScaledCappedLowerClip d c D n Y + n := by
  unfold lowerGammaScaledCappedClipped lowerGammaScaledCappedLowerClip
  rw [← max_add_add_right]
  norm_num

theorem lowerGammaScaledCappedLowerClip_poisson_integrable {d : ℕ} (hd : 0 < d) {c D n σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    Integrable fun Y : ℝ ↦ P_σ σ (s - Y) * lowerGammaScaledCappedLowerClip d c D n Y := by
  have hmax := (lowerGammaScaledCapped_poisson_product_integrable hd (R := c * √d) (D := D)
    hbelow habove s).sup
      (((stripPoissonKernel_integrable hbelow habove).comp_sub_left s).const_mul (-n))
  refine hmax.congr ?_
  filter_upwards with Y
  change max (P_σ σ (s - Y) * h_ℓD ((d : ℝ) / 2) (c * √d) D ((d : ℝ) / 2 * Y))
      (-n * P_σ σ (s - Y)) = P_σ σ (s - Y) * lowerGammaScaledCappedLowerClip d c D n Y
  unfold lowerGammaScaledCappedLowerClip
  rw [mul_max_of_nonneg _ _ (stripPoissonKernel_pos hbelow habove (s - Y)).le]
  ring_nf

theorem lowerGammaScaledCappedClipped_integral_eq {d : ℕ} (hd : 0 < d) {c D n σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    (∫ Y : ℝ, P_σ σ (s - Y) * lowerGammaScaledCappedClipped d c D n Y) =
      (∫ Y : ℝ, P_σ σ (s - Y) * lowerGammaScaledCappedLowerClip d c D n Y) + n * M_σ σ := by
  have hclip := lowerGammaScaledCappedLowerClip_poisson_integrable hd (c := c) (D := D) (n := n)
    hbelow habove s
  have hkernel := ((stripPoissonKernel_integrable hbelow habove).comp_sub_left s).const_mul n
  rw [show (fun Y : ℝ ↦ P_σ σ (s - Y) * lowerGammaScaledCappedClipped d c D n Y) =
        fun Y : ℝ ↦ P_σ σ (s - Y) * lowerGammaScaledCappedLowerClip d c D n Y +
          n * P_σ σ (s - Y) from
      funext fun Y ↦ by rw [lowerGammaScaledCappedClipped_eq_lowerClip_add]; ring,
    integral_add hclip hkernel, integral_const_mul, integral_sub_left_eq_self (P_σ σ) volume s,
    integral_stripPoissonKernel hbelow habove]

theorem lowerGammaScaledCappedLowerClip_poisson_convolution_max {d : ℕ} (hd : 2 ≤ d) {c D n σ : ℝ}
    (hc : 0 < c) (hn : 0 ≤ n) (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    (∫ Y : ℝ, P_σ σ (s - Y) * lowerGammaScaledCappedLowerClip d c D n Y) ≤
      ∫ Y : ℝ, P_σ σ (0 - Y) * lowerGammaScaledCappedLowerClip d c D n Y := by
  have h := lowerGammaScaledCappedClipped_poisson_convolution_max (D := D) hd hc hn hbelow habove s
  rw [lowerGammaScaledCappedClipped_integral_eq (by omega) hbelow habove s,
    lowerGammaScaledCappedClipped_integral_eq (by omega) hbelow habove 0] at h
  linarith

/-- Clipping from below at `-c ≤ 0`, or from above at `c ≥ 0`, does not increase `|·|`. -/
theorem abs_clip_le_abs {x c : ℝ} (hc : 0 ≤ c) : |max x (-c)| ≤ |x| ∧ |min x c| ≤ |x| := by
  constructor
  · rcases le_total x (-c) with h | h
    · rw [max_eq_right h, abs_of_nonpos (neg_nonpos.mpr hc),
        abs_of_nonpos (h.trans (neg_nonpos.mpr hc))]
      linarith
    · rw [max_eq_left h]
  · rcases le_total x c with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, abs_of_nonneg hc, abs_of_nonneg (hc.trans h)]
      exact h

/-- Dominated convergence for Poisson convolutions against weights `B n` clipped from `b`. -/
theorem tendsto_integral_poisson_clip {σ : ℝ} {b : ℝ → ℝ} {B : ℕ → ℝ → ℝ} {s : ℝ}
    (hbase : Integrable fun Y : ℝ ↦ P_σ σ (s - Y) * b Y)
    (hmeas : ∀ n : ℕ, AEStronglyMeasurable fun Y : ℝ ↦ P_σ σ (s - Y) * B n Y)
    (hdom : ∀ n : ℕ, ∀ᵐ Y : ℝ, |B n Y| ≤ |b Y|)
    (hlim : ∀ᵐ Y : ℝ, ∀ᶠ n : ℕ in atTop, B n Y = b Y) :
    Tendsto (fun n : ℕ ↦ ∫ Y : ℝ, P_σ σ (s - Y) * B n Y) atTop
      (𝓝 (∫ Y : ℝ, P_σ σ (s - Y) * b Y)) := by
  refine tendsto_integral_of_dominated_convergence (fun Y : ℝ ↦ |P_σ σ (s - Y) * b Y|) hmeas
    hbase.abs (fun n ↦ ?_) ?_
  · filter_upwards [hdom n] with Y hY
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left hY (abs_nonneg _)
  · filter_upwards [hlim] with Y hY
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hY] with n hn
    rw [hn]

theorem lowerGammaScaledCappedLowerClip_poisson_tendsto {d : ℕ} (hd : 0 < d) {c D σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    Tendsto (fun n : ℕ ↦ ∫ Y : ℝ, P_σ σ (s - Y) * lowerGammaScaledCappedLowerClip d c D (n : ℝ) Y)
      atTop (𝓝 (∫ Y : ℝ, P_σ σ (s - Y) * h_ℓD ((d : ℝ) / 2) (c * √d) D ((d : ℝ) / 2 * Y))) := by
  refine tendsto_integral_poisson_clip
    (lowerGammaScaledCapped_poisson_product_integrable hd (R := c * √d) (D := D) hbelow habove s)
    (fun n ↦ (lowerGammaScaledCappedLowerClip_poisson_integrable hd (c := c) (D := D)
      (n := (n : ℝ)) hbelow habove s).aestronglyMeasurable) (fun n ↦ ?_) ?_
  · exact Eventually.of_forall fun Y ↦ (abs_clip_le_abs (Nat.cast_nonneg n)).1
  · filter_upwards with Y
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
      (-h_ℓD ((d : ℝ) / 2) (c * √d) D ((d : ℝ) / 2 * Y))] with n hn
    exact max_eq_left (by linarith)

theorem lowerGammaScaledCapped_poisson_convolution_max {d : ℕ} (hd : 2 ≤ d) {c D σ : ℝ}
    (hc : 0 < c) (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    (∫ Y : ℝ, P_σ σ (s - Y) * h_ℓD ((d : ℝ) / 2) (c * √d) D ((d : ℝ) / 2 * Y)) ≤
      ∫ Y : ℝ, P_σ σ (0 - Y) * h_ℓD ((d : ℝ) / 2) (c * √d) D ((d : ℝ) / 2 * Y) :=
  le_of_tendsto_of_tendsto
    (lowerGammaScaledCappedLowerClip_poisson_tendsto (by omega) hbelow habove s)
    (lowerGammaScaledCappedLowerClip_poisson_tendsto (by omega) hbelow habove 0)
    (Eventually.of_forall fun n : ℕ ↦ lowerGammaScaledCappedLowerClip_poisson_convolution_max hd hc
      (Nat.cast_nonneg n) hbelow habove s)

theorem lowerGammaScaledCapped_poisson_tendsto {d : ℕ} (hd : 0 < d) {c σ : ℝ} (hbelow : -1 < σ)
    (habove : σ < 1) (s : ℝ) :
    Tendsto (fun n : ℕ ↦ ∫ Y : ℝ, P_σ σ (s - Y) * h_ℓD ((d : ℝ) / 2) (c * √d) (n : ℝ)
        ((d : ℝ) / 2 * Y)) atTop
      (𝓝 (∫ Y : ℝ, P_σ σ (s - Y) * h_ℓ ((d : ℝ) / 2) (c * √d) ((d : ℝ) / 2 * Y))) := by
  have hℓ : 0 < (d : ℝ) / 2 := half_pos (Nat.cast_pos.mpr hd)
  refine tendsto_integral_poisson_clip
    (lowerGammaScaled_poisson_product_integrable hd (R := c * √d) hbelow habove s)
    (fun n ↦ (lowerGammaScaledCapped_poisson_product_integrable hd (R := c * √d) (D := (n : ℝ))
      hbelow habove s).aestronglyMeasurable) (fun n ↦ ?_) ?_
  · filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with Y hY
    rw [h_ℓD, if_neg (mul_ne_zero hℓ.ne' hY)]
    exact (abs_clip_le_abs (Nat.cast_nonneg n)).2
  · filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with Y hY
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
      (h_ℓ ((d : ℝ) / 2) (c * √d) ((d : ℝ) / 2 * Y))] with n hn
    rw [h_ℓD, if_neg (mul_ne_zero hℓ.ne' hY), min_eq_left hn]

theorem lowerGammaScaled_poisson_convolution_max {d : ℕ} (hd : 2 ≤ d) {c σ : ℝ} (hc : 0 < c)
    (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    (∫ Y : ℝ, P_σ σ (s - Y) * h_ℓ ((d : ℝ) / 2) (c * √d) ((d : ℝ) / 2 * Y)) ≤
      ∫ Y : ℝ, P_σ σ (0 - Y) * h_ℓ ((d : ℝ) / 2) (c * √d) ((d : ℝ) / 2 * Y) :=
  le_of_tendsto_of_tendsto
    (lowerGammaScaledCapped_poisson_tendsto (c := c) (by omega) hbelow habove s)
    (lowerGammaScaledCapped_poisson_tendsto (c := c) (by omega) hbelow habove 0)
    (Eventually.of_forall fun n : ℕ ↦
      lowerGammaScaledCapped_poisson_convolution_max (D := (n : ℝ)) hd hc hbelow habove s)

/-- `H_σ` as a Poisson convolution in the rescaled variable `Y = T / λ`. -/
theorem lowerStripPoissonMajorant_scaled_convolution {ℓ : ℝ} (hℓ : 0 < ℓ) (R σ s : ℝ) :
    H_σ ℓ R σ s = ∫ Y : ℝ, P_σ σ (s / ℓ - Y) * h_ℓ ℓ R (ℓ * Y) := by
  rw [← integral_sub_left_eq_self (fun Y : ℝ ↦ P_σ σ (s / ℓ - Y) * h_ℓ ℓ R (ℓ * Y)) volume (s / ℓ)]
  unfold H_σ
  refine integral_congr_ae (Eventually.of_forall fun T ↦ ?_)
  change P_σ σ T * h_ℓ ℓ R (s - ℓ * T) = P_σ σ (s / ℓ - (s / ℓ - T)) * h_ℓ ℓ R (ℓ * (s / ℓ - T))
  rw [show s / ℓ - (s / ℓ - T) = T by ring]
  congr 1
  field_simp

/-- Report Lemma 3.3: `H_σ(s) ≤ H_σ(0)`. -/
theorem lowerStripPoissonMajorant_dimension_centered_max {d : ℕ} (hd : 2 ≤ d) {c σ : ℝ}
    (hc : 0 < c) (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    H_σ ((d : ℝ) / 2) (c * √d) σ s ≤ H_σ ((d : ℝ) / 2) (c * √d) σ 0 := by
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  rw [lowerStripPoissonMajorant_scaled_convolution hℓ (c * √d) σ s,
    lowerStripPoissonMajorant_scaled_convolution hℓ (c * √d) σ 0, zero_div]
  exact lowerGammaScaled_poisson_convolution_max hd hc hbelow habove (s / ((d : ℝ) / 2))

theorem lowerRiemannLog_zero (T : ℝ) : f_T T 0 = log (|T| / 2) := by
  unfold f_T
  rw [show (0 : ℝ) ^ 2 + T ^ 2 / 4 = (T / 2) ^ 2 by ring, Real.sqrt_sq_eq_abs, abs_div]
  norm_num

/-- Rescaling the Riemann integrand: `log √(j² + (λT/2)²) = log λ + f_T T (j / λ)`. -/
theorem log_sqrt_scaled {ℓ T : ℝ} (hℓ : 0 < ℓ) (hT : T ≠ 0) (j : ℝ) :
    log (√(j ^ 2 + (ℓ * T / 2) ^ 2)) = log ℓ + f_T T (j / ℓ) := by
  have hrad : 0 < (j / ℓ) ^ 2 + T ^ 2 / 4 := by positivity
  rw [show j ^ 2 + (ℓ * T / 2) ^ 2 = ℓ ^ 2 * ((j / ℓ) ^ 2 + T ^ 2 / 4) by field_simp; ring,
    Real.sqrt_mul (sq_nonneg ℓ), Real.sqrt_sq_eq_abs, abs_of_pos hℓ,
    Real.log_mul hℓ.ne' (Real.sqrt_pos.mpr hrad).ne']
  rfl

theorem lowerGammaBoundaryLog_integer_scaled {k : ℕ} (hk : 0 < k) {R T : ℝ} (hR : 0 < R)
    (hT : T ≠ 0) :
    h_ℓ (k : ℝ) R ((k : ℝ) * T) =
      (k : ℝ) * log (π * R ^ 2 / (k : ℝ)) - ∑ j ∈ Finset.range k, f_T T ((j : ℝ) / (k : ℝ)) := by
  have hk' : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  rw [lowerGammaBoundaryLog_integer k R (mul_ne_zero hk'.ne' hT)]
  simp_rw [log_sqrt_scaled hk' hT]
  rw [Finset.sum_add_distrib, show (∑ _j ∈ Finset.range k, log (k : ℝ)) = (k : ℝ) * log k by simp,
    Real.log_div (by positivity) hk'.ne']
  ring

theorem lowerGammaBoundaryLog_halfInteger_scaled (k : ℕ) {ℓ R T : ℝ} (hℓeq : ℓ = (k : ℝ) + 1 / 2)
    (hR : 0 < R) (hT : T ≠ 0) :
    h_ℓ ℓ R (ℓ * T) = ℓ * log (π * R ^ 2 / ℓ) -
        ∑ j ∈ Finset.range k, f_T T (((j : ℝ) + 1 / 2) / ℓ) +
        1 / 2 * log (coth (π * ℓ * |T| / 2)) - 1 / 2 * log (|T| / 2) := by
  have hℓ : 0 < ℓ := by rw [hℓeq]; positivity
  have ht : 0 < |T| / 2 := by positivity
  have hcoth : 0 < coth (π * ℓ * |T| / 2) := coth_pos (by positivity)
  have hraw := lowerGammaBoundaryLog_halfInteger k R (mul_ne_zero hℓ.ne' hT)
  rw [← hℓeq] at hraw
  rw [hraw]
  simp_rw [log_sqrt_scaled hℓ hT]
  rw [Finset.sum_add_distrib, show (∑ _j ∈ Finset.range k, log ℓ) = (k : ℝ) * log ℓ by simp,
    abs_mul, abs_of_pos hℓ, show π * (ℓ * |T|) / 2 = π * ℓ * |T| / 2 by ring,
    show ℓ * |T| / 2 = ℓ * (|T| / 2) by ring,
    Real.log_div hcoth.ne' (mul_ne_zero hℓ.ne' ht.ne'), Real.log_mul hℓ.ne' ht.ne',
    Real.log_div (by positivity) hℓ.ne', hℓeq]
  ring

theorem lowerRiemannLog_continuous {T : ℝ} (hT : T ≠ 0) : Continuous (f_T T) := by
  have hrad (x : ℝ) : 0 < x ^ 2 + T ^ 2 / 4 := by positivity
  unfold f_T
  exact (by fun_prop : Continuous fun x : ℝ ↦ √(x ^ 2 + T ^ 2 / 4)).log fun x ↦
    (Real.sqrt_pos.mpr (hrad x)).ne'

/-- The error majorant `3|f_T T 0| + 2|f_T T 1| + ½ log coth(π|T|/2)` of report Lemma 3.3. -/
def lowerRiemannErrorMajorant (T : ℝ) : ℝ :=
  3 * |f_T T 0| + 2 * |f_T T 1| + 1 / 2 * log (coth (π * |T| / 2))

theorem lowerGammaBoundaryLog_integer_riemann_le {k : ℕ} (hk : 0 < k) {R T : ℝ} (hR : 0 < R)
    (hT : T ≠ 0) :
    h_ℓ (k : ℝ) R ((k : ℝ) * T) ≤
      (k : ℝ) * (log (π * R ^ 2 / (k : ℝ)) + 1 + lowerEndpointPhase T) +
        lowerRiemannErrorMajorant T := by
  rw [lowerGammaBoundaryLog_integer_scaled hk hR hT]
  unfold lowerRiemannErrorMajorant
  nlinarith [(lower_integer_leftRiemann_error hT hk).2, integral_lowerRiemannLog hT,
    log_coth_nonneg (show 0 < π * |T| / 2 by positivity), le_abs_self (f_T T 1),
    neg_le_abs (f_T T 0), abs_nonneg (f_T T 0), abs_nonneg (f_T T 1)]

theorem lowerRiemannLog_halfInteger_tail_integral_le (k : ℕ) {ℓ T : ℝ}
    (hℓeq : ℓ = (k : ℝ) + 1 / 2) (hT : T ≠ 0) :
    ℓ * (∫ x in ((k : ℝ) / ℓ)..1, f_T T x) ≤ 1 / 2 * f_T T 1 := by
  have hℓ : 0 < ℓ := by rw [hℓeq]; positivity
  have hratio_nonneg : 0 ≤ (k : ℝ) / ℓ := by positivity
  have hratio_le : (k : ℝ) / ℓ ≤ 1 := by
    rw [div_le_one hℓ, hℓeq]
    linarith
  have hmono : (∫ x in ((k : ℝ) / ℓ)..1, f_T T x) ≤ ∫ _x in ((k : ℝ) / ℓ)..1, f_T T 1 :=
    intervalIntegral.integral_mono_on hratio_le
      ((lowerRiemannLog_continuous hT).intervalIntegrable (μ := volume) _ _)
      intervalIntegrable_const
      fun x hx ↦ lowerRiemannLog_monotoneOn hT (mem_Ici.mpr (hratio_nonneg.trans hx.1))
        (mem_Ici.mpr zero_le_one) hx.2
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hfactor : ℓ * (1 - (k : ℝ) / ℓ) = 1 / 2 := by
    field_simp [hℓ.ne']
    rw [hℓeq]
    ring
  calc ℓ * (∫ x in ((k : ℝ) / ℓ)..1, f_T T x) ≤ ℓ * ((1 - (k : ℝ) / ℓ) * f_T T 1) :=
        mul_le_mul_of_nonneg_left hmono hℓ.le
    _ = 1 / 2 * f_T T 1 := by rw [← mul_assoc, hfactor]

theorem lowerGammaBoundaryLog_halfInteger_riemann_le (k : ℕ) {ℓ R T : ℝ}
    (hℓeq : ℓ = (k : ℝ) + 1 / 2) (hℓone : 1 ≤ ℓ) (hR : 0 < R) (hT : T ≠ 0) :
    h_ℓ ℓ R (ℓ * T) ≤
      ℓ * (log (π * R ^ 2 / ℓ) + 1 + lowerEndpointPhase T) + lowerRiemannErrorMajorant T := by
  have hℓ : 0 < ℓ := by linarith
  have hratio_nonneg : 0 ≤ (k : ℝ) / ℓ := by positivity
  have hratio_le : (k : ℝ) / ℓ ≤ 1 := by
    rw [div_le_one hℓ, hℓeq]
    linarith
  have hcont := lowerRiemannLog_continuous hT
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) 0 ((k : ℝ) / ℓ))
    (hcont.intervalIntegrable (μ := volume) ((k : ℝ) / ℓ) 1)
  have hmidupper := (le_abs_self _).trans (lower_halfInteger_midpointRiemann_error hT hℓ k)
  have htail := lowerRiemannLog_halfInteger_tail_integral_le k hℓeq hT
  have hsumupper : -(∑ j ∈ Finset.range k, f_T T (((j : ℝ) + 1 / 2) / ℓ)) ≤
      -ℓ * (∫ x in (0 : ℝ)..1, f_T T x) + (f_T T ((k : ℝ) / ℓ) - f_T T 0) +
        1 / 2 * f_T T 1 := by
    nlinarith
  have hqk : f_T T ((k : ℝ) / ℓ) ≤ f_T T 1 := lowerRiemannLog_monotoneOn hT
    (mem_Ici.mpr hratio_nonneg) (mem_Ici.mpr zero_le_one) hratio_le
  have hcoth := antitoneOn_log_coth (mem_Ioi.mpr (by positivity : 0 < π * |T| / 2))
    (mem_Ioi.mpr (by positivity : 0 < π * ℓ * |T| / 2))
    (by nlinarith [mul_nonneg (sub_nonneg.mpr hℓone) (mul_nonneg Real.pi_pos.le (abs_nonneg T))])
  have hphase := integral_lowerRiemannLog hT
  rw [lowerGammaBoundaryLog_halfInteger_scaled k hℓeq hR hT, ← lowerRiemannLog_zero T]
  unfold lowerRiemannErrorMajorant
  nlinarith [le_abs_self (f_T T 1), neg_le_abs (f_T T 0), abs_nonneg (f_T T 0),
    abs_nonneg (f_T T 1)]

theorem lowerGammaBoundaryLog_dimension_riemann_le {d : ℕ} (hd : 2 ≤ d) {R T : ℝ} (hR : 0 < R)
    (hT : T ≠ 0) :
    h_ℓ ((d : ℝ) / 2) R ((d : ℝ) / 2 * T) ≤
      (d : ℝ) / 2 * (log (π * R ^ 2 / ((d : ℝ) / 2)) + 1 + lowerEndpointPhase T) +
        lowerRiemannErrorMajorant T := by
  rcases d.even_or_odd with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [show ((k + k : ℕ) : ℝ) / 2 = (k : ℝ) by push_cast; ring]
    exact lowerGammaBoundaryLog_integer_riemann_le (by omega) hR hT
  · rw [show ((2 * k + 1 : ℕ) : ℝ) / 2 = (k : ℝ) + 1 / 2 by push_cast; ring]
    refine lowerGammaBoundaryLog_halfInteger_riemann_le k rfl ?_ hR hT
    have hk : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
    linarith

/-- Report Lemma 3.3 at the critical radius `R = c√d`. -/
theorem lowerGammaBoundaryLog_dimension_scaled_riemann_le {d : ℕ} (hd : 2 ≤ d) {c T : ℝ}
    (hc : 0 < c) (hT : T ≠ 0) :
    h_ℓ ((d : ℝ) / 2) (c * √d) ((d : ℝ) / 2 * T) ≤
      (d : ℝ) / 2 * (log (2 * π * exp 1 * c ^ 2) + lowerEndpointPhase T) +
        lowerRiemannErrorMajorant T := by
  have hdreal : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  have h := lowerGammaBoundaryLog_dimension_riemann_le hd (mul_pos hc (Real.sqrt_pos.mpr hdreal)) hT
  have hratio : π * (c * √d) ^ 2 / ((d : ℝ) / 2) = 2 * π * c ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hdreal.le]
    field_simp [hdreal.ne']
  rw [hratio] at h
  rw [show 2 * π * exp 1 * c ^ 2 = 2 * π * c ^ 2 * exp 1 by ring,
    Real.log_mul (by positivity) (Real.exp_ne_zero 1), Real.log_exp]
  linarith

theorem stripPoissonKernel_le_mass_mul_exponential {σ : ℝ} (hzero : 0 ≤ σ) (habove : σ < 1)
    (T : ℝ) : P_σ σ T ≤ M_σ σ * stripPoissonExponentialMajorant T := by
  have h := (stripNormalizedPoissonExtension_le_majorant hzero habove.le T).2
  rw [← stripNormalizedPoissonKernel_eq_extension (by linarith : (-1 : ℝ) < σ) habove] at h
  unfold stripNormalizedPoissonKernel at h
  rw [div_le_iff₀ (stripBottomMass_pos habove)] at h
  linarith

theorem stripPoissonKernel_abs_moment_integrable {σ : ℝ} (hzero : 0 ≤ σ) (habove : σ < 1) :
    Integrable fun T : ℝ ↦ P_σ σ T * |T| := by
  have hbelow : (-1 : ℝ) < σ := by linarith
  have hexp : Integrable fun T : ℝ ↦ stripPoissonExponentialMajorant T * |T| := by
    convert! (integrable_abs_pow_mul_exp_neg_mul_abs 1 (half_pos Real.pi_pos)).const_mul (π / 2)
      using 1
    ext T
    simp [stripPoissonExponentialMajorant]
    ring
  refine (hexp.const_mul (M_σ σ)).mono'
    ((stripPoissonKernel_integrable hbelow habove).aestronglyMeasurable.mul
      (by fun_prop : Measurable fun T : ℝ ↦ |T|).aestronglyMeasurable) ?_
  filter_upwards with T
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (stripPoissonKernel_pos hbelow habove T), abs_abs]
  calc P_σ σ T * |T| ≤ M_σ σ * stripPoissonExponentialMajorant T * |T| :=
        mul_le_mul_of_nonneg_right (stripPoissonKernel_le_mass_mul_exponential hzero habove T)
          (abs_nonneg T)
    _ = M_σ σ * (stripPoissonExponentialMajorant T * |T|) := by ring

theorem stripPoissonKernel_mul_lowerRiemannLog_zero_integrable {σ : ℝ} (hbelow : -1 < σ)
    (habove : σ < 1) : Integrable fun T : ℝ ↦ P_σ σ T * f_T T 0 := by
  have hgamma : Integrable fun T : ℝ ↦ P_σ σ T * h_ℓ 1 1 T := by
    refine (lowerGammaScaled_poisson_product_integrable (d := 2) (by norm_num) (R := (1 : ℝ))
      hbelow habove 0).congr ?_
    filter_upwards with T
    norm_num [stripPoissonKernel_neg]
  refine (((stripPoissonKernel_integrable hbelow habove).const_mul (log π)).sub hgamma).congr ?_
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with T hT
  have hidentity : h_ℓ 1 1 T = log π - f_T T 0 := by
    simpa using lowerGammaBoundaryLog_integer_scaled (k := 1) (by norm_num) (R := (1 : ℝ))
      (by norm_num) hT
  change log π * P_σ σ T - P_σ σ T * h_ℓ 1 1 T = P_σ σ T * f_T T 0
  rw [hidentity]
  ring

theorem lowerRiemannLog_one_nonneg_le (T : ℝ) : 0 ≤ f_T T 1 ∧ f_T T 1 ≤ |T| / 2 := by
  have hrad : (0 : ℝ) < 1 + T ^ 2 / 4 := by positivity
  unfold f_T
  rw [one_pow]
  refine ⟨Real.log_nonneg ((Real.le_sqrt (by norm_num) hrad.le).2 (by nlinarith [sq_nonneg T])), ?_⟩
  have hupper : √(1 + T ^ 2 / 4) ≤ 1 + |T| / 2 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [abs_nonneg T, sq_abs T]⟩
  linarith [Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hrad)]

end

noncomputable section
open Filter MeasureTheory Metric Real Set
open scoped ENNReal Interval Topology

theorem tendsto_natCast_half_atTop : Tendsto (fun d : ℕ ↦ (d : ℝ) / 2) atTop atTop := by
  convert! (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const
    (by norm_num : (0 : ℝ) < 1 / 2) using 1
  ext d
  ring

theorem stripPoissonKernel_mul_abs_lowerRiemannLog_one_integrable {σ : ℝ} (hzero : 0 ≤ σ)
    (habove : σ < 1) : Integrable fun T : ℝ ↦ P_σ σ T * |f_T T 1| := by
  have hbelow : (-1 : ℝ) < σ := by linarith
  have hcont : Continuous fun T : ℝ ↦ f_T T 1 := by
    have hrad (T : ℝ) : (0 : ℝ) < 1 + T ^ 2 / 4 := by positivity
    simpa [f_T] using (by fun_prop : Continuous fun T : ℝ ↦ √(1 + T ^ 2 / 4)).log
      fun T ↦ (Real.sqrt_pos.mpr (hrad T)).ne'
  refine ((stripPoissonKernel_abs_moment_integrable hzero habove).const_mul (1 / 2)).mono'
    ((stripPoissonKernel_integrable hbelow habove).aestronglyMeasurable.mul
      hcont.abs.aestronglyMeasurable) ?_
  filter_upwards with T
  have hq := lowerRiemannLog_one_nonneg_le T
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (stripPoissonKernel_pos hbelow habove T), abs_abs,
    abs_of_nonneg hq.1]
  nlinarith [mul_nonneg (stripPoissonKernel_pos hbelow habove T).le (sub_nonneg.mpr hq.2)]

theorem lowerRiemannErrorMajorant_poisson_integrable {σ : ℝ} (hzero : 0 ≤ σ) (habove : σ < 1) :
    Integrable fun T : ℝ ↦ P_σ σ T * lowerRiemannErrorMajorant T := by
  have hbelow : (-1 : ℝ) < σ := by linarith
  have hlog : Integrable fun T : ℝ ↦ P_σ σ T * |f_T T 0| := by
    refine (stripPoissonKernel_mul_lowerRiemannLog_zero_integrable hbelow habove).abs.congr ?_
    filter_upwards with T
    rw [abs_mul, abs_of_pos (stripPoissonKernel_pos hbelow habove T)]
  have hcoth : Integrable fun T : ℝ ↦ P_σ σ T * log (coth (π * |T| / 2)) := by
    refine (stripPoissonKernel_weighted_product_integrable hbelow habove
      integrable_log_coth_pi_mul_abs_div_two 0).congr ?_
    filter_upwards with T
    rw [zero_sub, stripPoissonKernel_neg]
  refine ((hlog.const_mul 3).add (((stripPoissonKernel_mul_abs_lowerRiemannLog_one_integrable
    hzero habove).const_mul 2).add (hcoth.const_mul (1 / 2)))).congr ?_
  filter_upwards with T
  change 3 * (P_σ σ T * |f_T T 0|) + (2 * (P_σ σ T * |f_T T 1|) +
      1 / 2 * (P_σ σ T * log (coth (π * |T| / 2)))) = P_σ σ T * lowerRiemannErrorMajorant T
  unfold lowerRiemannErrorMajorant
  ring

theorem stripPoissonKernel_mul_lowerEndpointPhase_integrable {σ : ℝ} (hzero : 0 ≤ σ)
    (habove : σ < 1) : Integrable fun T : ℝ ↦ P_σ σ T * lowerEndpointPhase T := by
  have hbelow : (-1 : ℝ) < σ := by linarith
  refine (stripPoissonExponentialMajorant_mul_lowerEndpointPhase_integrable.const_mul
    (M_σ σ)).mono' ((stripPoissonKernel_integrable hbelow habove).aestronglyMeasurable.mul
      lowerEndpointPhase_continuous.aestronglyMeasurable) ?_
  filter_upwards with T
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (stripPoissonKernel_pos hbelow habove T)]
  calc P_σ σ T * ‖lowerEndpointPhase T‖ ≤
        M_σ σ * stripPoissonExponentialMajorant T * ‖lowerEndpointPhase T‖ :=
        mul_le_mul_of_nonneg_right (stripPoissonKernel_le_mass_mul_exponential hzero habove T)
          (norm_nonneg _)
    _ = M_σ σ * (stripPoissonExponentialMajorant T * ‖lowerEndpointPhase T‖) := by ring

theorem integral_stripPoissonKernel_mul_lowerEndpointPhase {σ : ℝ} (habove : σ < 1) :
    (∫ T : ℝ, P_σ σ T * lowerEndpointPhase T) = M_σ σ * lowerPoissonEndpointExpectation σ := by
  have hmass : M_σ σ ≠ 0 := (stripBottomMass_pos habove).ne'
  unfold lowerPoissonEndpointExpectation stripNormalizedPoissonKernel
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards with T
  field_simp

/-- The Poisson average `∫ P_σ(T) E(T) dT` of the Riemann error majorant of Lemma 3.3. -/
def lowerRiemannPoissonError (σ : ℝ) : ℝ := ∫ T : ℝ, P_σ σ T * lowerRiemannErrorMajorant T

/-- Report Lemma 3.3 at the centre: `H_σ(0)` is at most `(d/2) M_σ (log(2πe c²) + J_σ)` plus the
Poisson average of the Riemann error. -/
theorem lowerStripPoissonMajorant_dimension_central_bound {d : ℕ} (hd : 2 ≤ d) {c σ : ℝ}
    (hc : 0 < c) (hzero : 0 ≤ σ) (habove : σ < 1) :
    H_σ ((d : ℝ) / 2) (c * √d) σ 0 ≤
      (d : ℝ) / 2 * M_σ σ * (log (2 * π * exp 1 * c ^ 2) + lowerPoissonEndpointExpectation σ) +
        lowerRiemannPoissonError σ := by
  have hbelow : (-1 : ℝ) < σ := by linarith
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  have hleft : Integrable fun T : ℝ ↦ P_σ σ T * h_ℓ ((d : ℝ) / 2) (c * √d) ((d : ℝ) / 2 * T) := by
    simpa only [zero_sub, stripPoissonKernel_neg] using
      lowerGammaScaled_poisson_product_integrable (by omega) (R := c * √d) hbelow habove 0
  have hk := (stripPoissonKernel_integrable hbelow habove).const_mul
    ((d : ℝ) / 2 * log (2 * π * exp 1 * c ^ 2))
  have hq := (stripPoissonKernel_mul_lowerEndpointPhase_integrable hzero habove).const_mul
    ((d : ℝ) / 2)
  have hE := lowerRiemannErrorMajorant_poisson_integrable hzero habove
  have hkq : Integrable fun T : ℝ ↦ (d : ℝ) / 2 * log (2 * π * exp 1 * c ^ 2) * P_σ σ T +
      (d : ℝ) / 2 * (P_σ σ T * lowerEndpointPhase T) := hk.add hq
  have hsplit : (fun T : ℝ ↦ P_σ σ T * ((d : ℝ) / 2 * (log (2 * π * exp 1 * c ^ 2) +
        lowerEndpointPhase T) + lowerRiemannErrorMajorant T)) =
      fun T : ℝ ↦ (d : ℝ) / 2 * log (2 * π * exp 1 * c ^ 2) * P_σ σ T +
        (d : ℝ) / 2 * (P_σ σ T * lowerEndpointPhase T) + P_σ σ T * lowerRiemannErrorMajorant T :=
    funext fun T ↦ by ring
  have hright : Integrable fun T : ℝ ↦ P_σ σ T * ((d : ℝ) / 2 * (log (2 * π * exp 1 * c ^ 2) +
      lowerEndpointPhase T) + lowerRiemannErrorMajorant T) := by
    rw [hsplit]
    exact hkq.add hE
  rw [lowerStripPoissonMajorant_scaled_convolution hℓ (c * √d) σ 0]
  simp only [zero_div, zero_sub, stripPoissonKernel_neg]
  calc (∫ T : ℝ, P_σ σ T * h_ℓ ((d : ℝ) / 2) (c * √d) ((d : ℝ) / 2 * T))
      ≤ ∫ T : ℝ, P_σ σ T * ((d : ℝ) / 2 * (log (2 * π * exp 1 * c ^ 2) + lowerEndpointPhase T) +
          lowerRiemannErrorMajorant T) := by
        refine integral_mono_ae hleft hright ?_
        filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with T hT
        exact mul_le_mul_of_nonneg_left (lowerGammaBoundaryLog_dimension_scaled_riemann_le hd hc hT)
          (stripPoissonKernel_pos hbelow habove T).le
    _ = (d : ℝ) / 2 * M_σ σ * (log (2 * π * exp 1 * c ^ 2) +
          lowerPoissonEndpointExpectation σ) + lowerRiemannPoissonError σ := by
        rw [hsplit, integral_add hkq hE, integral_add hk hq, integral_const_mul,
          integral_const_mul, integral_stripPoissonKernel hbelow habove,
          integral_stripPoissonKernel_mul_lowerEndpointPhase habove]
        unfold lowerRiemannPoissonError
        ring

/-- Report Lemma 3.5: for a subcritical radius the majorant is uniformly negative of order `d`. -/
theorem exists_lowerStripPoissonMajorant_uniform_negative {c : ℝ} (hc : 0 < c) (hsharp : c < π⁻¹) :
    ∃ σ γ : ℝ, 0 < σ ∧ σ < 1 ∧ 0 < γ ∧ ∀ᶠ d : ℕ in atTop, ∀ s : ℝ,
      H_σ ((d : ℝ) / 2) (c * √d) σ s ≤ -γ * ((d : ℝ) / 2) := by
  have hpositive : ∀ᶠ σ : ℝ in 𝓝[<] (1 : ℝ), 0 < σ :=
    Eventually.filter_mono nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  have hless : ∀ᶠ σ : ℝ in 𝓝[<] (1 : ℝ), σ < 1 := self_mem_nhdsWithin
  obtain ⟨σ, hσpos, hσless, hσneg⟩ := (hpositive.and (hless.and
    (eventually_lowerPoissonEndpointSharpCoefficient_neg hc hsharp))).exists
  set A : ℝ := log (2 * π * exp 1 * c ^ 2) + lowerPoissonEndpointExpectation σ with hA
  have hmass := stripBottomMass_pos hσless
  have hγ : 0 < -(M_σ σ * A) / 2 := by nlinarith [mul_neg_of_pos_of_neg hmass hσneg]
  refine ⟨σ, -(M_σ σ * A) / 2, hσpos, hσless, hγ, ?_⟩
  have hγscale : Tendsto (fun d : ℕ ↦ -(M_σ σ * A) / 2 * ((d : ℝ) / 2)) atTop atTop := by
    simpa [mul_comm] using tendsto_natCast_half_atTop.atTop_mul_const hγ
  filter_upwards [eventually_ge_atTop 2, hγscale.eventually
    (Ici_mem_atTop (lowerRiemannPoissonError σ))] with d hd hderr
  intro s
  have hcentre := lowerStripPoissonMajorant_dimension_centered_max hd hc (by linarith) hσless s
  have hbound := lowerStripPoissonMajorant_dimension_central_bound hd hc hσpos.le hσless
  nlinarith

theorem lowerGammaBoundaryLog_dimension_scaled_log_tail_simple {d : ℕ} (hd : 2 ≤ d) {c Y : ℝ}
    (hc : 0 < c) (hY : 1 ≤ |Y|) :
    h_ℓ ((d : ℝ) / 2) (c * √d) ((d : ℝ) / 2 * Y) ≤
      (d : ℝ) / 2 * log (4 * π * exp 1 * c ^ 2 / |Y|) := by
  have hyzero : Y ≠ 0 := by
    rintro rfl
    rw [abs_zero] at hY
    linarith
  have hℓ : 1 ≤ (d : ℝ) / 2 := (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by exact_mod_cast hd)
  rw [show 4 * π * exp 1 * c ^ 2 / |Y| = 4 * π * c ^ 2 / |Y| * exp 1 by
      field_simp [abs_ne_zero.mpr hyzero],
    Real.log_mul (by positivity) (Real.exp_ne_zero 1), Real.log_exp]
  nlinarith [lowerGammaBoundaryLog_dimension_scaled_log_tail_uniform hd hc hyzero,
    log_coth_pi_mul_abs_div_two_le_one hY]

/-- The Poisson mass `∫_{-1}^{1} P_σ` of the core interval. -/
def stripPoissonCoreMass (σ : ℝ) : ℝ := ∫ T in Icc (-1 : ℝ) 1, P_σ σ T

theorem stripPoissonCoreMass_pos {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) :
    0 < stripPoissonCoreMass σ := by
  have hconst : IntegrableOn (fun _T : ℝ ↦ P_σ σ 1) (Icc (-1 : ℝ) 1) :=
    (continuous_const : Continuous fun _T : ℝ ↦ P_σ σ 1).integrableOn_Icc
  have hcompare : (∫ _T in Icc (-1 : ℝ) 1, P_σ σ 1) ≤ ∫ T in Icc (-1 : ℝ) 1, P_σ σ T := by
    refine setIntegral_mono_on hconst (stripPoissonKernel_integrable hbelow habove).integrableOn
      measurableSet_Icc fun T hT ↦ stripPoissonKernel_antitone_abs hbelow habove ?_
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1)]
    exact abs_le.mpr hT
  rw [show (∫ _T in Icc (-1 : ℝ) 1, P_σ σ 1) = 2 * P_σ σ 1 by norm_num] at hcompare
  unfold stripPoissonCoreMass
  nlinarith [stripPoissonKernel_pos hbelow habove 1]

/-- Outside the support radius `C` of the positive part, its Poisson convolution decays
exponentially in the distance to the centre. -/
theorem lowerGammaScaledPositivePart_poisson_exponential_tail {d : ℕ} (hd : 2 ≤ d) {c σ C S : ℝ}
    (hc : 0 < c) (hσ : 0 ≤ σ) (hσone : σ < 1)
    (hsupport : Function.support (lowerGammaScaledPositivePart d c) ⊆ Icc (-C) C)
    (hmass : (∫ Y : ℝ, lowerGammaScaledPositivePart d c Y) ≤ C * ((d : ℝ) / 2)) (hS : C ≤ S) :
    (∫ Y : ℝ, P_σ σ (S - Y) * lowerGammaScaledPositivePart d c Y) ≤
      M_σ σ * (π / 2) * exp (-(π / 2) * (S - C)) * (C * ((d : ℝ) / 2)) := by
  have hbelow : (-1 : ℝ) < σ := by linarith
  have hmassσ := stripBottomMass_pos hσone
  have hp := lowerGammaScaledPositivePart_integrable hd hc
  calc (∫ Y : ℝ, P_σ σ (S - Y) * lowerGammaScaledPositivePart d c Y)
      ≤ ∫ Y : ℝ, M_σ σ * (π / 2) * exp (-(π / 2) * (S - C)) *
          lowerGammaScaledPositivePart d c Y := by
        refine integral_mono_ae (stripPoissonKernel_weighted_product_integrable hbelow hσone hp S)
          (hp.const_mul _) ?_
        filter_upwards with Y
        rcases eq_or_ne (lowerGammaScaledPositivePart d c Y) 0 with hzero | hzero
        · simp [hzero]
        · refine mul_le_mul_of_nonneg_right ?_ (le_max_right _ _)
          refine (stripPoissonKernel_le_mass_mul_exponential hσ hσone (S - Y)).trans ?_
          unfold stripPoissonExponentialMajorant
          rw [← mul_assoc]
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
          rw [abs_of_nonneg (by linarith [(hsupport hzero).2] : (0 : ℝ) ≤ S - Y)]
          nlinarith [Real.pi_pos, (hsupport hzero).2]
    _ = M_σ σ * (π / 2) * exp (-(π / 2) * (S - C)) *
          ∫ Y : ℝ, lowerGammaScaledPositivePart d c Y := integral_const_mul _ _
    _ ≤ M_σ σ * (π / 2) * exp (-(π / 2) * (S - C)) * (C * ((d : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hmass (by positivity)

private theorem integral_stripPoissonKernel_mul_indicator (σ a : ℝ) :
    (∫ T : ℝ, P_σ σ T * (Icc (-1 : ℝ) 1).indicator (fun _ : ℝ ↦ a) T) =
      a * stripPoissonCoreMass σ := by
  rw [show (fun T : ℝ ↦ P_σ σ T * (Icc (-1 : ℝ) 1).indicator (fun _ : ℝ ↦ a) T) =
      (Icc (-1 : ℝ) 1).indicator fun T : ℝ ↦ a * P_σ σ T from
    funext fun T ↦ by by_cases hT : T ∈ Icc (-1 : ℝ) 1 <;> simp [hT, mul_comm],
    integral_indicator measurableSet_Icc, integral_const_mul]
  rfl

/-- Pointwise, the Poisson integrand of `H_σ(λS)` is below the core term on `[-1, 1]` plus the
positive part. -/
private theorem stripPoissonKernel_mul_h_ℓ_le_core_add_positivePart {d : ℕ} (hd : 2 ≤ d)
    {c σ S : ℝ} (hc : 0 < c) (hσ : 0 ≤ σ) (hσone : σ < 1) (hS : 2 ≤ S) (T : ℝ) :
    P_σ σ T * h_ℓ ((d : ℝ) / 2) (c * √d) ((d : ℝ) / 2 * (S - T)) ≤
      P_σ σ T * (Icc (-1 : ℝ) 1).indicator
          (fun _ : ℝ ↦ (d : ℝ) / 2 * log (8 * π * exp 1 * c ^ 2 / S)) T +
        P_σ σ T * lowerGammaScaledPositivePart d c (S - T) := by
  have hkernel := (stripPoissonKernel_pos (by linarith) hσone T).le
  have hle : h_ℓ ((d : ℝ) / 2) (c * √d) ((d : ℝ) / 2 * (S - T)) ≤
      lowerGammaScaledPositivePart d c (S - T) := le_max_left _ _
  have hnonneg : (0 : ℝ) ≤ lowerGammaScaledPositivePart d c (S - T) := le_max_right _ _
  by_cases hT : T ∈ Icc (-1 : ℝ) 1
  · have hℓ : 0 < (d : ℝ) / 2 := by positivity
    have hSpos : (0 : ℝ) < S := by linarith
    have hP : (0 : ℝ) < 4 * π * exp 1 * c ^ 2 := by positivity
    have hdiff : (0 : ℝ) < S - T := by linarith [hT.2]
    have hnear : h_ℓ ((d : ℝ) / 2) (c * √d) ((d : ℝ) / 2 * (S - T)) ≤
        (d : ℝ) / 2 * log (8 * π * exp 1 * c ^ 2 / S) := by
      refine (lowerGammaBoundaryLog_dimension_scaled_log_tail_simple hd hc (by
        rw [abs_of_pos hdiff]; linarith [hT.2])).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) ?_) hℓ.le
      rw [div_le_div_iff₀ (abs_pos.mpr hdiff.ne') hSpos, abs_of_pos hdiff]
      nlinarith [mul_nonneg hP.le (show (0 : ℝ) ≤ S - 2 * T by linarith [hT.2])]
    rw [indicator_of_mem hT]
    nlinarith [mul_nonneg hkernel hnonneg, mul_nonneg hkernel (sub_nonneg.mpr hnear)]
  · rw [indicator_of_notMem hT, mul_zero, zero_add]
    exact mul_le_mul_of_nonneg_left hle hkernel

/-- Report Lemma 3.6: splitting `H_σ(λS)` into the logarithmic core term and the positive-part
tail. -/
theorem lowerStripPoissonMajorant_core_tail_split {d : ℕ} (hd : 2 ≤ d) {c σ S : ℝ} (hc : 0 < c)
    (hσ : 0 ≤ σ) (hσone : σ < 1) (hS : 2 ≤ S) :
    H_σ ((d : ℝ) / 2) (c * √d) σ ((d : ℝ) / 2 * S) ≤
      (d : ℝ) / 2 * log (8 * π * exp 1 * c ^ 2 / S) * stripPoissonCoreMass σ +
        ∫ Y : ℝ, P_σ σ (S - Y) * lowerGammaScaledPositivePart d c Y := by
  have hbelow : (-1 : ℝ) < σ := by linarith
  have hb : Integrable fun T : ℝ ↦
      P_σ σ T * h_ℓ ((d : ℝ) / 2) (c * √d) ((d : ℝ) / 2 * (S - T)) := by
    refine ((lowerGammaScaled_poisson_product_integrable (d := d) (by omega) (R := c * √d) hbelow
      hσone S).comp_sub_left S).congr ?_
    filter_upwards with T
    rw [show S - (S - T) = T by ring]
  have hp : Integrable fun T : ℝ ↦ P_σ σ T * lowerGammaScaledPositivePart d c (S - T) := by
    refine ((stripPoissonKernel_weighted_product_integrable hbelow hσone
      (lowerGammaScaledPositivePart_integrable hd hc) S).comp_sub_left S).congr ?_
    filter_upwards with T
    rw [show S - (S - T) = T by ring]
  have hcore : Integrable fun T : ℝ ↦ P_σ σ T * (Icc (-1 : ℝ) 1).indicator
      (fun _ : ℝ ↦ (d : ℝ) / 2 * log (8 * π * exp 1 * c ^ 2 / S)) T := by
    refine (((stripPoissonKernel_integrable hbelow hσone).const_mul
      ((d : ℝ) / 2 * log (8 * π * exp 1 * c ^ 2 / S))).indicator (s := Icc (-1 : ℝ) 1)
      measurableSet_Icc).congr ?_
    filter_upwards with T
    by_cases hT : T ∈ Icc (-1 : ℝ) 1 <;> simp [hT, mul_comm]
  have hpval : (∫ T : ℝ, P_σ σ T * lowerGammaScaledPositivePart d c (S - T)) =
      ∫ Y : ℝ, P_σ σ (S - Y) * lowerGammaScaledPositivePart d c Y := by
    rw [← integral_sub_left_eq_self
      (fun T : ℝ ↦ P_σ σ T * lowerGammaScaledPositivePart d c (S - T)) volume S]
    refine integral_congr_ae ?_
    filter_upwards with Y
    rw [show S - (S - Y) = Y by ring]
  have hrep : H_σ ((d : ℝ) / 2) (c * √d) σ ((d : ℝ) / 2 * S) =
      ∫ T : ℝ, P_σ σ T * h_ℓ ((d : ℝ) / 2) (c * √d) ((d : ℝ) / 2 * (S - T)) := by
    unfold H_σ
    refine integral_congr_ae ?_
    filter_upwards with T
    rw [show (d : ℝ) / 2 * S - (d : ℝ) / 2 * T = (d : ℝ) / 2 * (S - T) by ring]
  rw [hrep, ← integral_stripPoissonKernel_mul_indicator σ _, ← hpval, ← integral_add hcore hp]
  exact integral_mono_ae hb (hcore.add hp)
    (Eventually.of_forall (stripPoissonKernel_mul_h_ℓ_le_core_add_positivePart hd hc hσ hσone hS))

theorem lowerStripPoissonMajorant_dimension_neg {d : ℕ} (hd : 0 < d) (R σ s : ℝ) :
    H_σ ((d : ℝ) / 2) R σ (-s) = H_σ ((d : ℝ) / 2) R σ s := by
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  unfold H_σ
  rw [← integral_neg_eq_self
    (fun T : ℝ ↦ P_σ σ T * h_ℓ ((d : ℝ) / 2) R (s - (d : ℝ) / 2 * T)) volume]
  refine integral_congr_ae ?_
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) (-s / ((d : ℝ) / 2))] with T hT
  have hy : s + (d : ℝ) / 2 * T ≠ 0 := fun hzero ↦ hT ((eq_div_iff hℓ.ne').2 (by linarith))
  rw [stripPoissonKernel_neg, show -s - (d : ℝ) / 2 * T = -(s + (d : ℝ) / 2 * T) by ring,
    lowerGammaBoundaryLog_dimension_neg R hy,
    show s - (d : ℝ) / 2 * -T = s + (d : ℝ) / 2 * T by ring]

private theorem tendsto_mul_exp_neg_sub_atTop (a C : ℝ) :
    Tendsto (fun S : ℝ ↦ a * exp (-(π / 2) * (S - C))) atTop (𝓝 0) := by
  have hexponential : Tendsto (fun S : ℝ ↦ exp (-(S * (π / 2)))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (tendsto_id.atTop_mul_const (by positivity : (0 : ℝ) < π / 2)))
  have hmul : Tendsto (fun S : ℝ ↦ a * exp (π / 2 * C) * exp (-(S * (π / 2)))) atTop (𝓝 0) := by
    simpa using hexponential.const_mul (a * exp (π / 2 * C))
  refine Tendsto.congr (fun S ↦ ?_) hmul
  rw [mul_assoc, ← Real.exp_add, show π / 2 * C + -(S * (π / 2)) = -(π / 2) * (S - C) by ring]

/-- Report Lemma 3.6: a logarithmically decreasing bound for `H_σ` far from the centre. -/
theorem exists_lowerStripPoissonMajorant_positive_logarithmic_tail {c σ : ℝ} (hc : 0 < c)
    (hσ : 0 ≤ σ) (hσone : σ < 1) :
    ∃ A B κ : ℝ, 0 < A ∧ 0 < B ∧ 0 < κ ∧ ∀ d : ℕ, 2 ≤ d → ∀ S : ℝ, B ≤ S →
      H_σ ((d : ℝ) / 2) (c * √d) σ ((d : ℝ) / 2 * S) ≤ -κ * ((d : ℝ) / 2) * log (S / A) := by
  have hbelow : (-1 : ℝ) < σ := by linarith
  obtain ⟨C, hC, huniform⟩ := exists_lowerGammaScaledPositivePart_uniform_bound hc
  have hA : (0 : ℝ) < 8 * π * exp 1 * c ^ 2 := by positivity
  have hm : 0 < stripPoissonCoreMass σ := stripPoissonCoreMass_pos hbelow hσone
  have hmassσ := stripBottomMass_pos hσone
  have hdecay := tendsto_mul_exp_neg_sub_atTop (M_σ σ * (π / 2) * C) C
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.1 ((hdecay.eventually (Iio_mem_nhds
    (by positivity : 0 < stripPoissonCoreMass σ / 4))).and
      (eventually_ge_atTop (max 2 (max C (2 * (8 * π * exp 1 * c ^ 2))))))
  refine ⟨8 * π * exp 1 * c ^ 2, max 1 B₀, stripPoissonCoreMass σ / 2, hA,
    lt_of_lt_of_le one_pos (le_max_left 1 B₀), by positivity, ?_⟩
  intro d hd S hSB
  obtain ⟨hsmallS, hlargeS⟩ := hB₀ S ((le_max_right 1 B₀).trans hSB)
  have hStwo : (2 : ℝ) ≤ S := (le_max_left 2 _).trans hlargeS
  have hSC : C ≤ S := ((le_max_left C _).trans (le_max_right 2 _)).trans hlargeS
  have hSratio : 2 * (8 * π * exp 1 * c ^ 2) ≤ S :=
    ((le_max_right C _).trans (le_max_right 2 _)).trans hlargeS
  have hSpos : (0 : ℝ) < S := by linarith
  have hℓ : (0 : ℝ) < (d : ℝ) / 2 := by positivity
  obtain ⟨hsupport, hpositive⟩ := huniform d hd
  have hpositive_bound := lowerGammaScaledPositivePart_poisson_exponential_tail hd hc hσ hσone
    hsupport hpositive hSC
  have hlogratio : (1 : ℝ) / 2 ≤ log (S / (8 * π * exp 1 * c ^ 2)) := by
    have h2 : (2 : ℝ) ≤ S / (8 * π * exp 1 * c ^ 2) := (le_div_iff₀ hA).2 hSratio
    linarith [Real.log_two_gt_d9, Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2]
  have hflip : log (8 * π * exp 1 * c ^ 2 / S) = -log (S / (8 * π * exp 1 * c ^ 2)) := by
    rw [Real.log_div hA.ne' hSpos.ne', Real.log_div hSpos.ne' hA.ne']
    ring
  refine (lowerStripPoissonMajorant_core_tail_split hd hc hσ hσone hStwo).trans ?_
  rw [hflip]
  nlinarith [mul_nonneg hℓ.le (show (0 : ℝ) ≤ stripPoissonCoreMass σ *
    log (S / (8 * π * exp 1 * c ^ 2)) / 2 - M_σ σ * (π / 2) * C * exp (-(π / 2) * (S - C)) by
      nlinarith [mul_nonneg hm.le (show (0 : ℝ) ≤ log (S / (8 * π * exp 1 * c ^ 2)) - 1 / 2 by
        linarith)])]

theorem exists_lowerStripPoissonMajorant_logarithmic_tail {c σ : ℝ} (hc : 0 < c) (hσ : 0 ≤ σ)
    (hσone : σ < 1) :
    ∃ A B κ : ℝ, 0 < A ∧ 0 < B ∧ 0 < κ ∧ ∀ d : ℕ, 2 ≤ d → ∀ S : ℝ, B ≤ |S| →
      H_σ ((d : ℝ) / 2) (c * √d) σ ((d : ℝ) / 2 * S) ≤ -κ * ((d : ℝ) / 2) * log (|S| / A) := by
  obtain ⟨A, B, κ, hA, hB, hκ, htail⟩ :=
    exists_lowerStripPoissonMajorant_positive_logarithmic_tail hc hσ hσone
  refine ⟨A, B, κ, hA, hB, hκ, fun d hd S hS ↦ ?_⟩
  rcases le_or_gt 0 S with hnonneg | hnegative
  · rw [abs_of_nonneg hnonneg] at hS ⊢
    exact htail d hd S hS
  · rw [abs_of_neg hnegative] at hS ⊢
    rw [show (d : ℝ) / 2 * S = -((d : ℝ) / 2 * -S) by ring,
      lowerStripPoissonMajorant_dimension_neg (by omega) (c * √d) σ ((d : ℝ) / 2 * -S)]
    exact htail d hd (-S) hS

theorem inverseQuadraticAbs_integrable : Integrable fun S : ℝ ↦ 1 / (1 + |S|) ^ 2 := by
  convert! integrable_one_add_norm (E := ℝ) (μ := volume) (r := (2 : ℝ)) (by norm_num) using 1
  ext S
  rw [Real.norm_eq_abs, Real.rpow_neg (by positivity)]
  simp [one_div]

/-- Report Lemma 3.6: a Cauchy-type integrable majorant for `exp H_σ`, uniform in the
dimension. -/
theorem exists_lowerStripPoissonMajorant_integrable_majorant {c : ℝ} (hc : 0 < c)
    (hsharp : c < π⁻¹) :
    ∃ σ γ C : ℝ, 0 < σ ∧ σ < 1 ∧ 0 < γ ∧ 0 < C ∧ ∀ᶠ d : ℕ in atTop, ∀ S : ℝ,
      exp (H_σ ((d : ℝ) / 2) (c * √d) σ ((d : ℝ) / 2 * S)) ≤
        C * exp (-γ * ((d : ℝ) / 2)) / (1 + |S|) ^ 2 := by
  obtain ⟨σ, γ₀, hσpos, hσone, hγ₀, hcentral⟩ :=
    exists_lowerStripPoissonMajorant_uniform_negative hc hsharp
  obtain ⟨A, B, κ, hA, hB, hκ, htail⟩ :=
    exists_lowerStripPoissonMajorant_logarithmic_tail hc hσpos.le hσone
  obtain ⟨T, hT, hTA, hTB⟩ : ∃ T : ℝ, 1 ≤ T ∧ A ≤ T ∧ B ≤ T :=
    ⟨max B (max A 1), (le_max_right A 1).trans (le_max_right B _),
      (le_max_left A 1).trans (le_max_right B _), le_max_left B _⟩
  obtain ⟨C, hC, hCnear, hCfar⟩ : ∃ C : ℝ, 0 < C ∧ (1 + T) ^ 2 ≤ C ∧ 4 * A ^ 2 ≤ C :=
    ⟨max ((1 + T) ^ 2) (4 * A ^ 2), lt_of_lt_of_le (by positivity) (le_max_left _ _),
      le_max_left _ _, le_max_right _ _⟩
  refine ⟨σ, γ₀ / 2, C, hσpos, hσone, by positivity, hC, ?_⟩
  filter_upwards [eventually_ge_atTop 2,
    tendsto_natCast_half_atTop.eventually (Ici_mem_atTop (4 / κ)), hcentral] with d hd hdim hcen
  intro S
  have hℓ : (0 : ℝ) < (d : ℝ) / 2 := by positivity
  have hden : (0 : ℝ) < (1 + |S|) ^ 2 := by positivity
  by_cases hfar : T ≤ |S|
  · have hu : (1 : ℝ) ≤ |S| := hT.trans hfar
    have habspos : (0 : ℝ) < |S| := lt_of_lt_of_le hA (hTA.trans hfar)
    have hlog : 0 ≤ log (|S| / A) := Real.log_nonneg ((one_le_div hA).2 (hTA.trans hfar))
    have hκscale : (4 : ℝ) ≤ κ * ((d : ℝ) / 2) := by linarith [(div_le_iff₀ hκ).1 hdim]
    have haverage : H_σ ((d : ℝ) / 2) (c * √d) σ ((d : ℝ) / 2 * S) ≤
        -(γ₀ / 2) * ((d : ℝ) / 2) - 2 * log (|S| / A) := by
      have h₁ := hcen ((d : ℝ) / 2 * S)
      have h₂ := htail d hd S (hTB.trans hfar)
      nlinarith [mul_nonneg (sub_nonneg.mpr hκscale) hlog]
    have hpow : exp (-(2 : ℝ) * log (|S| / A)) = (A / |S|) ^ 2 := by
      rw [show -(2 : ℝ) * log (|S| / A) = -log (|S| / A) + -log (|S| / A) by ring, Real.exp_add,
        Real.exp_neg, Real.exp_log (div_pos habspos hA), inv_div, ← pow_two]
    have hprofile : (A / |S|) ^ 2 ≤ C / (1 + |S|) ^ 2 := by
      rw [le_div_iff₀ hden]
      calc (A / |S|) ^ 2 * (1 + |S|) ^ 2 ≤ (A / |S|) ^ 2 * (4 * |S| ^ 2) :=
            mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (|S| - 1)]) (sq_nonneg _)
        _ = 4 * A ^ 2 := by field_simp [habspos.ne']
        _ ≤ C := hCfar
    calc exp (H_σ ((d : ℝ) / 2) (c * √d) σ ((d : ℝ) / 2 * S))
        ≤ exp (-(γ₀ / 2) * ((d : ℝ) / 2) - 2 * log (|S| / A)) := Real.exp_le_exp.mpr haverage
      _ = exp (-(γ₀ / 2) * ((d : ℝ) / 2)) * (A / |S|) ^ 2 := by
          rw [show -(γ₀ / 2) * ((d : ℝ) / 2) - 2 * log (|S| / A) = -(γ₀ / 2) * ((d : ℝ) / 2) +
            -(2 : ℝ) * log (|S| / A) by ring, Real.exp_add, hpow]
      _ ≤ exp (-(γ₀ / 2) * ((d : ℝ) / 2)) * (C / (1 + |S|) ^ 2) :=
          mul_le_mul_of_nonneg_left hprofile (Real.exp_pos _).le
      _ = C * exp (-(γ₀ / 2) * ((d : ℝ) / 2)) / (1 + |S|) ^ 2 := by ring
  · rw [le_div_iff₀ hden]
    have hnear : |S| ≤ T := le_of_not_ge hfar
    calc exp (H_σ ((d : ℝ) / 2) (c * √d) σ ((d : ℝ) / 2 * S)) * (1 + |S|) ^ 2 ≤
          exp (-(γ₀ / 2) * ((d : ℝ) / 2)) * C :=
          mul_le_mul (Real.exp_le_exp.mpr (by
              nlinarith [hcen ((d : ℝ) / 2 * S), mul_nonneg hγ₀.le hℓ.le]))
            (by nlinarith [abs_nonneg S]) (by positivity) (Real.exp_pos _).le
      _ = C * exp (-(γ₀ / 2) * ((d : ℝ) / 2)) := by ring

/-- The mass `∫ (1 + |S|)⁻² dS` of the Cauchy-type profile. -/
def lowerInverseQuadraticMass : ℝ := ∫ S : ℝ, 1 / (1 + |S|) ^ 2

theorem integral_norm_le_of_quadratic_majorant {ℓ C γ : ℝ} (hℓ : 0 < ℓ) {Z : ℝ → ℂ}
    (hZ : Integrable Z)
    (hbound : ∀ S : ℝ, ‖Z (ℓ * S)‖ ≤ C * exp (-γ * ℓ) / (1 + |S|) ^ 2) :
    (∫ s : ℝ, ‖Z s‖) ≤ C * lowerInverseQuadraticMass * ℓ * exp (-γ * ℓ) := by
  have hscaled : Integrable fun S : ℝ ↦ ‖Z (ℓ * S)‖ := hZ.norm.comp_mul_left' hℓ.ne'
  have hprofile : Integrable fun S : ℝ ↦ C * exp (-γ * ℓ) / (1 + |S|) ^ 2 := by
    simpa [div_eq_mul_inv] using inverseQuadraticAbs_integrable.const_mul (C * exp (-γ * ℓ))
  have hchange : (∫ s : ℝ, ‖Z s‖) = ℓ * ∫ S : ℝ, ‖Z (ℓ * S)‖ := by
    have h := Measure.integral_comp_mul_left (fun s : ℝ ↦ ‖Z s‖) ℓ
    rw [abs_of_pos (inv_pos.mpr hℓ), smul_eq_mul] at h
    rw [h, ← mul_assoc, mul_inv_cancel₀ hℓ.ne', one_mul]
  rw [hchange]
  calc ℓ * ∫ S : ℝ, ‖Z (ℓ * S)‖ ≤ ℓ * ∫ S : ℝ, C * exp (-γ * ℓ) / (1 + |S|) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (integral_mono_ae hscaled hprofile (Eventually.of_forall hbound)) hℓ.le
    _ = C * lowerInverseQuadraticMass * ℓ * exp (-γ * ℓ) := by
        rw [show (fun S : ℝ ↦ C * exp (-γ * ℓ) / (1 + |S|) ^ 2) =
              fun S : ℝ ↦ C * exp (-γ * ℓ) * (1 / (1 + |S|) ^ 2) from funext fun S ↦ by ring,
          integral_const_mul]
        unfold lowerInverseQuadraticMass
        ring

/-- Report Lemma 3.6: the `L¹` norm of `Z` on the interior line `Im z = σλ`, under a pointwise
Poisson majorization and a Cauchy-type majorant for `exp H_σ`. -/
theorem integral_norm_Z_g_le_of_majorant {d : ℕ} {ς : ℤˣ} (hd : 0 < d)
    (g : RadialEigenfunction d ς) {R σ γ C : ℝ} (hR : 0 < R) (hσbelow : -1 < σ) (hσabove : σ < 1)
    (hpoint : ∀ s : ℝ, ‖Z_g hd g.toFun R ((s : ℂ) + I * (σ * ((d : ℂ) / 2)))‖ ≤
      exp (H_σ ((d : ℝ) / 2) R σ s))
    (hmajor : ∀ S : ℝ, exp (H_σ ((d : ℝ) / 2) R σ ((d : ℝ) / 2 * S)) ≤
      C * exp (-γ * ((d : ℝ) / 2)) / (1 + |S|) ^ 2) :
    (∫ s : ℝ, ‖Z_g hd g.toFun R ((s : ℂ) + I * (σ * ((d : ℂ) / 2)))‖) ≤
      C * lowerInverseQuadraticMass * ((d : ℝ) / 2) * exp (-γ * ((d : ℝ) / 2)) := by
  have hℓ : (0 : ℝ) < (d : ℝ) / 2 := half_pos (Nat.cast_pos.mpr hd)
  have hσ' : (0 : ℝ) < 1 - σ := sub_pos.mpr hσabove
  have ha : (1 - σ) * ((d : ℝ) / 2) < (d : ℝ) := by
    nlinarith [mul_pos (show (0 : ℝ) < 1 + σ by linarith) hℓ, mul_pos hσ' hℓ]
  refine integral_norm_le_of_quadratic_majorant hℓ ?_ fun S ↦ (hpoint _).trans (hmajor S)
  refine (g.integrable_Z_g_shifted hd hR ha).congr ?_
  filter_upwards with s
  rw [show (d : ℂ) / 2 - ((1 - σ) * ((d : ℝ) / 2) : ℝ) = σ * ((d : ℂ) / 2) by push_cast; ring]

theorem lowerStripCappedPoisson_tendsto {d : ℕ} (hd : 0 < d) {R σ : ℝ} (hσbelow : -1 < σ)
    (hσabove : σ < 1) (s : ℝ) :
    Tendsto (fun n : ℕ ↦ ∫ T : ℝ, P_σ σ T * h_ℓD ((d : ℝ) / 2) R (n : ℝ)
        (s - (d : ℝ) / 2 * T)) atTop (𝓝 (H_σ ((d : ℝ) / 2) R σ s)) := by
  have hℓ : (0 : ℝ) < (d : ℝ) / 2 := by positivity
  have hsqrt : 0 < √(d : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
  have h := lowerGammaScaledCapped_poisson_tendsto (c := R / √(d : ℝ)) hd hσbelow hσabove
    (s / ((d : ℝ) / 2))
  rw [div_mul_cancel₀ R hsqrt.ne'] at h
  rw [lowerStripPoissonMajorant_scaled_convolution hℓ R σ s]
  refine Tendsto.congr (fun n ↦ ?_) h
  rw [← integral_sub_left_eq_self (fun Y : ℝ ↦ P_σ σ (s / ((d : ℝ) / 2) - Y) *
    h_ℓD ((d : ℝ) / 2) R (n : ℝ) ((d : ℝ) / 2 * Y)) volume (s / ((d : ℝ) / 2))]
  refine integral_congr_ae ?_
  filter_upwards with T
  rw [show s / ((d : ℝ) / 2) - (s / ((d : ℝ) / 2) - T) = T by ring,
    show (d : ℝ) / 2 * (s / ((d : ℝ) / 2) - T) = s - (d : ℝ) / 2 * T by field_simp]

/-- Report Lemma 3.2 with (18): `|Z(s + iσλ)| ≤ exp H_σ(s)` on every interior line of the
strip, by letting the cap `D → ∞` in `exists_capped_poisson_majorization`. -/
theorem norm_Z_g_le_exp_H_σ {d : ℕ} {ς : ℤˣ} (hd : 0 < d) (g : RadialEigenfunction d ς) {R : ℝ}
    (hR : 0 < R) {σ : ℝ} (hσbelow : -1 < σ) (hσabove : σ < 1) (s : ℝ) :
    ‖Z_g hd g.toFun R ((s : ℂ) + I * (σ * ((d : ℂ) / 2)))‖ ≤
      exp (H_σ ((d : ℝ) / 2) R σ s) := by
  obtain ⟨D₀, hD⟩ := exists_capped_poisson_majorization hd g hR
  refine le_of_tendsto_of_tendsto tendsto_const_nhds
    (Real.continuous_exp.continuousAt.tendsto.comp
      (lowerStripCappedPoisson_tendsto hd hσbelow hσabove s)) ?_
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually (Ici_mem_atTop D₀)] with n hn
  exact hD (n : ℝ) hn hσbelow hσabove s

end

end CohnElkies
