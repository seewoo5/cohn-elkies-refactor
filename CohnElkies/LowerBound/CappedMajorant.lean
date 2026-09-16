import CohnElkies.LowerBound.GammaBoundary

/-!
# The capped Gamma boundary function and its holomorphic Poisson extension (report §3.2)

The capped boundary function `h_{λ,D} = min (h_λ) D`, its continuity and limits, the
holomorphic Poisson integral `W[b](z) = ∫ K'_ℓ(z, y) b(y) dy` of a boundary datum `b` built from
the regularized Schwarz kernel of the strip, its differentiability and real part (the general
Poisson principle for the strip is proved in `CohnElkies.LowerBound.CappedMajorization`), and the
comparison of the strip Poisson kernel with its value at the centre.
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Asymptotics Filter Function MeasureTheory Metric Real Set
open scoped FourierTransform SchwartzMap Topology

/-- The capped lower-boundary majorant `h_{λ,D}(y) = min (h_λ y) D` for `y ≠ 0`, with the
removable singularity at `y = 0` filled in by the cap `D`; Lemma 3.2 of the report. -/
def h_ℓD (ℓ R D y : ℝ) : ℝ :=
  if y = 0 then D else min (h_ℓ ℓ R y) D

/-- Away from the origin `h_λ` splits as a function continuous at `0` minus the logarithmic
pole `log(|y|/2)`, via `Γ(s + 1) = s Γ(s)` at `s = -iy/2`. -/
theorem h_ℓ_eq_of_ne_zero (ℓ R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    h_ℓ ℓ R y = ℓ * log (π * R ^ 2) + log ‖Complex.Gamma (1 - I * (y : ℂ) / 2)‖ -
      log ‖Complex.Gamma ((ℓ : ℂ) + I * (y : ℂ) / 2)‖ - log (|y| / 2) := by
  have hs : -I * (y : ℂ) / 2 ≠ 0 := fun h ↦ hy (by
    have him := congrArg Complex.im h
    norm_num at him
    linarith)
  have hgamma : Complex.Gamma (-I * (y : ℂ) / 2) ≠ 0 := Complex.Gamma_ne_zero fun m hm ↦ hy (by
    have him := congrArg Complex.im hm
    norm_num at him
    linarith)
  have hlog : log ‖Complex.Gamma (-I * (y : ℂ) / 2)‖ =
      log ‖Complex.Gamma (1 - I * (y : ℂ) / 2)‖ - log (|y| / 2) := by
    rw [show (1 : ℂ) - I * (y : ℂ) / 2 = -I * (y : ℂ) / 2 + 1 by ring,
      Complex.Gamma_add_one _ hs, norm_mul,
      log_mul (norm_ne_zero_iff.mpr hs) (norm_ne_zero_iff.mpr hgamma),
      show ‖-I * (y : ℂ) / 2‖ = |y| / 2 by simp]
    ring
  unfold h_ℓ
  rw [hlog]
  ring

/-- `h_λ(y) → +∞` as `y → 0` with `y ≠ 0`: the pole `-log(|y|/2)` dominates. -/
theorem tendsto_h_ℓ_atTop {ℓ : ℝ} (hℓ : 0 < ℓ) (R : ℝ) :
    Tendsto (h_ℓ ℓ R) (𝓝[≠] (0 : ℝ)) atTop := by
  have hpole : Tendsto (fun y : ℝ ↦ log (|y| / 2)) (𝓝[≠] (0 : ℝ)) atBot := by
    refine (tendsto_log_nhdsNE_zero.atBot_add (tendsto_const_nhds (x := -log 2))).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [log_div (abs_ne_zero.mpr hy) two_ne_zero, log_abs]
    ring
  have key : ∀ f : ℝ → ℂ, Continuous f → 0 < (f 0).re →
      ContinuousAt (fun y : ℝ ↦ log ‖Complex.Gamma (f y)‖) 0 := by
    intro f hf hre
    have hnopole : ∀ m : ℕ, f 0 ≠ -(m : ℂ) := fun m hm ↦ by
      rw [hm] at hre
      simp only [Complex.neg_re, Complex.natCast_re] at hre
      linarith [Nat.cast_nonneg (α := ℝ) m]
    exact ((Complex.continuousAt_Gamma _ hnopole).comp_of_eq hf.continuousAt rfl).norm.log
      (norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero hnopole))
  have hregular : ContinuousAt (fun y : ℝ ↦ ℓ * log (π * R ^ 2) +
      log ‖Complex.Gamma (1 - I * (y : ℂ) / 2)‖ -
      log ‖Complex.Gamma ((ℓ : ℂ) + I * (y : ℂ) / 2)‖) 0 :=
    (continuousAt_const.add (key _ (by fun_prop) (by norm_num))).sub
      (key _ (by fun_prop) (by simpa using hℓ))
  refine ((tendsto_neg_atTop_iff.mpr hpole).atTop_add
    (hregular.tendsto.mono_left nhdsWithin_le_nhds)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [h_ℓ_eq_of_ne_zero ℓ R hy]
  ring

/-- The capped majorant `h_{λ,D}` is continuous: near `y = 0` the cap wins since `h_λ → +∞`. -/
theorem lowerGammaBoundaryCapped_continuous {ℓ : ℝ} (hℓ : 0 < ℓ) (R D : ℝ) :
    Continuous (h_ℓD ℓ R D) := by
  rw [continuous_iff_continuousAt]
  intro y
  rcases eq_or_ne y 0 with rfl | hy
  · refine (continuousAt_const (y := D)).congr_of_eventuallyEq ?_
    filter_upwards [eventually_nhdsWithin_iff.mp
      ((tendsto_h_ℓ_atTop hℓ R).eventually_ge_atTop D)] with x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · simp [h_ℓD]
    · simp [h_ℓD, hx0, min_eq_right (hx hx0)]
  · have hmin : ContinuousAt (fun x : ℝ ↦ min (h_ℓ ℓ R x) D) y :=
      ((lowerGammaBoundaryLog_continuousOn hℓ R (S := {(0 : ℝ)}ᶜ) fun _ hx ↦ hx).continuousAt
        (isClosed_singleton.isOpen_compl.mem_nhds hy)).min continuousAt_const
    refine hmin.congr_of_eventuallyEq ?_
    filter_upwards [eventually_ne_nhds hy] with x hx
    simp [h_ℓD, hx]

/-- Capping preserves the exponentially weighted integrability of the boundary profile. -/
theorem integrable_exp_mul_h_ℓD {ℓ a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) (R D : ℝ)
    (hgamma : Integrable fun y : ℝ ↦ exp (-a * |y|) * h_ℓ ℓ R y) :
    Integrable fun y : ℝ ↦ exp (-a * |y|) * h_ℓD ℓ R D y := by
  have habs : Integrable fun y : ℝ ↦ exp (-a * |y|) * |h_ℓ ℓ R y| := by
    simpa [abs_mul, abs_of_pos (exp_pos _)] using hgamma.norm
  refine (habs.add ((integrable_exp_neg_mul_abs ha).const_mul |D|)).mono'
    (((by fun_prop : Continuous fun y : ℝ ↦ exp (-a * |y|)).mul
      (lowerGammaBoundaryCapped_continuous hℓ R D)).aestronglyMeasurable) ?_
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with y hy
  have hcap : |h_ℓD ℓ R D y| ≤ |h_ℓ ℓ R y| + |D| := by
    rw [h_ℓD, if_neg hy]
    rcases le_total (h_ℓ ℓ R y) D with h | h
    · rw [min_eq_left h]; exact le_add_of_nonneg_right (abs_nonneg D)
    · rw [min_eq_right h]; exact le_add_of_nonneg_left (abs_nonneg _)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
  calc exp (-a * |y|) * |h_ℓD ℓ R D y| ≤ exp (-a * |y|) * (|h_ℓ ℓ R y| + |D|) := by gcongr
    _ = exp (-a * |y|) * |h_ℓ ℓ R y| + |D| * exp (-a * |y|) := by ring

/-- If `b` is continuous and `exp(-π|y|/(2λ)) b(y)` is integrable, then `K̃_λ(z, ·) b` is
integrable for every `z` in the open strip. -/
theorem integrable_K'_ℓ_mul {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ} (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ)
    (b : ℝ → ℝ) (hb : Continuous b)
    (hboundary : Integrable fun y : ℝ ↦ exp (-(π / (2 * ℓ)) * |y|) * b y) :
    Integrable fun y : ℝ ↦ K'_ℓ ℓ z y * (b y : ℂ) := by
  have habs : Integrable fun y : ℝ ↦ exp (-(π / (2 * ℓ)) * |y|) * |b y| := by
    simpa [abs_mul, abs_of_pos (exp_pos _)] using hboundary.norm
  have main : ∀ S : Set ℝ, MeasurableSet S → ContinuousOn (fun y : ℝ ↦ K'_ℓ ℓ z y) S →
      ∀ C : ℝ, (∀ y ∈ S, ‖K'_ℓ ℓ z y‖ ≤ C * exp (-(π / (2 * ℓ)) * |y|)) →
        IntegrableOn (fun y : ℝ ↦ K'_ℓ ℓ z y * (b y : ℂ)) S := by
    intro S hS hcont C hC
    refine (habs.const_mul C).integrableOn.mono' ((hcont.mul
      (by fun_prop : Continuous fun y : ℝ ↦ (b y : ℂ)).continuousOn).aestronglyMeasurable hS) ?_
    filter_upwards [ae_restrict_mem hS] with y hy
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖K'_ℓ ℓ z y‖ * |b y| ≤ C * exp (-(π / (2 * ℓ)) * |y|) * |b y| := by
          gcongr; exact hC y hy
      _ = C * (exp (-(π / (2 * ℓ)) * |y|) * |b y|) := by ring
  rw [← integrableOn_univ, ← @Iio_union_Ici ℝ _ 0, integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨main (Iio 0) measurableSet_Iio
      (stripRegularizedHolomorphicPoissonKernel_continuousOn_Iio hℓ hz)
      (exp (-(π / (2 * ℓ)) * z.re) / (2 * ℓ * sin (π * (z.im + ℓ) / (2 * ℓ)))) fun y hy ↦ ?_,
    main (Ioi 0) measurableSet_Ioi
      (stripRegularizedHolomorphicPoissonKernel_continuousOn_Ioi hℓ hz)
      (exp (π / (2 * ℓ) * z.re) / (2 * ℓ * sin (π * (z.im + ℓ) / (2 * ℓ)))) fun y hy ↦ ?_⟩
  · refine (norm_stripRegularizedHolomorphicPoissonKernel_of_neg hℓ hz hy).trans_eq ?_
    rw [abs_of_neg hy, div_mul_eq_mul_div, ← exp_add,
      show -(π / (2 * ℓ)) * z.re + -(π / (2 * ℓ)) * -y = -(π * (z.re - y) / (2 * ℓ)) by ring]
  · refine (norm_stripRegularizedHolomorphicPoissonKernel_of_nonneg hℓ hz hy.le).trans_eq ?_
    rw [abs_of_pos hy, div_mul_eq_mul_div, ← exp_add,
      show π / (2 * ℓ) * z.re + -(π / (2 * ℓ)) * y = π * (z.re - y) / (2 * ℓ) by ring]

/-- The outer function `W[b](z) = ∫ K̃_λ(z, y) b(y) dy` of the strip; Lemma 3.2. -/
def W_b (ℓ : ℝ) (b : ℝ → ℝ) (z : ℂ) : ℂ := ∫ y : ℝ, K'_ℓ ℓ z y * (b y : ℂ)

/-- `W[b]` is holomorphic in the open strip: differentiate under the integral sign. -/
theorem differentiableAt_W_b {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ} (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ)
    (b : ℝ → ℝ) (hb : Continuous b)
    (hboundary : Integrable fun y : ℝ ↦ exp (-(π / (2 * ℓ)) * |y|) * b y) :
    DifferentiableAt ℂ (W_b ℓ b) z := by
  obtain ⟨S, hS, C, _, hderiv⟩ := stripRegularizedHolomorphicPoissonKernelDeriv_local_bound hℓ hz
  have hstrip : Complex.im ⁻¹' Ioo (-ℓ) ℓ ∈ 𝓝 z :=
    (isOpen_Ioo.preimage Complex.continuous_im).mem_nhds hz
  have habs : Integrable fun y : ℝ ↦ exp (-(π / (2 * ℓ)) * |y|) * |b y| := by
    simpa [abs_mul, abs_of_pos (exp_pos _)] using hboundary.norm
  have hmeas : ∀ᶠ w : ℂ in 𝓝 z,
      AEStronglyMeasurable fun y : ℝ ↦ K'_ℓ ℓ w y * (b y : ℂ) := by
    filter_upwards [hstrip] with w hw
    exact (integrable_K'_ℓ_mul hℓ hw b hb hboundary).aestronglyMeasurable
  have hbound : ∀ᵐ y : ℝ, ∀ w ∈ S ∩ Complex.im ⁻¹' Ioo (-ℓ) ℓ,
      ‖stripRegularizedHolomorphicPoissonKernelDeriv ℓ w y * (b y : ℂ)‖ ≤
        C * (exp (-(π / (2 * ℓ)) * |y|) * |b y|) := .of_forall fun y w hw ↦ by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ← mul_assoc]
    gcongr
    exact hderiv w hw.1 y
  unfold W_b
  refine HasDerivAt.differentiableAt (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w : ℂ ↦ fun y : ℝ ↦ K'_ℓ ℓ w y * (b y : ℂ))
    (F' := fun w : ℂ ↦ fun y : ℝ ↦
      stripRegularizedHolomorphicPoissonKernelDeriv ℓ w y * (b y : ℂ))
    (bound := fun y : ℝ ↦ C * (exp (-(π / (2 * ℓ)) * |y|) * |b y|))
    (inter_mem hS hstrip) hmeas (integrable_K'_ℓ_mul hℓ hz b hb hboundary)
    (((stripRegularizedHolomorphicPoissonKernelDeriv_continuous hℓ hz).measurable.mul
      (Complex.continuous_ofReal.comp hb).measurable).aestronglyMeasurable)
    hbound (habs.const_mul C) (.of_forall fun y w hw ↦
      (stripRegularizedHolomorphicPoissonKernel_hasDerivAt_deriv hℓ hw.2 y).mul_const _)).2

theorem integrable_exp_mul_h_ℓD_dim {d : ℕ} (hd : 0 < d) {a : ℝ} (ha : 0 < a) (R D : ℝ) :
    Integrable fun y : ℝ ↦ exp (-a * |y|) * h_ℓD ((d : ℝ) / 2) R D y :=
  integrable_exp_mul_h_ℓD (half_pos (Nat.cast_pos.mpr hd)) ha R D
    (lowerGammaBoundaryLog_dimension_exp_integrable hd ha R)

/-- The integrand of `W[h_{λ,D}]` is integrable in dimension `d`. -/
theorem lowerStripCappedGammaOuter_integrable_dimension {d : ℕ} (hd : 0 < d) {R D : ℝ} {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2)) :
    Integrable fun y : ℝ ↦ K'_ℓ ((d : ℝ) / 2) z y * (h_ℓD ((d : ℝ) / 2) R D y : ℂ) := by
  have hℓ : 0 < (d : ℝ) / 2 := half_pos (Nat.cast_pos.mpr hd)
  exact integrable_K'_ℓ_mul hℓ hz _ (lowerGammaBoundaryCapped_continuous hℓ R D)
    (integrable_exp_mul_h_ℓD_dim hd (div_pos pi_pos (by linarith)) R D)

/-- On the horizontal line `Im z = σλ` the real part of `W[b]` is the Poisson integral of `b`. -/
theorem W_b_re {ℓ σ : ℝ} (hℓ : 0 < ℓ) (hσbelow : -1 < σ) (hσabove : σ < 1) (s : ℝ) (b : ℝ → ℝ)
    (houter : Integrable fun y : ℝ ↦ K'_ℓ ℓ ((s : ℂ) + I * (σ * ℓ : ℂ)) y * (b y : ℂ)) :
    (W_b ℓ b ((s : ℂ) + I * (σ * ℓ : ℂ))).re = ∫ T : ℝ, P_σ σ T * b (s - ℓ * T) := by
  unfold W_b
  rw [← stripPoisson_integral_changeVariables hℓ σ s b]
  refine (integral_re houter).symm.trans (integral_congr_ae (.of_forall fun y ↦ ?_))
  change (K'_ℓ ℓ ((s : ℂ) + I * (σ * ℓ : ℂ)) y * (b y : ℂ)).re =
    P_σ σ ((s - y) / ℓ) / ℓ * b y
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    stripRegularizedHolomorphicPoissonKernel_re hℓ hσbelow hσabove]

/-- As `σ → -1` the strip Poisson kernel vanishes away from `T = 0`. -/
theorem stripPoissonKernel_tendsto_zero_bottom_of_ne {T : ℝ} (hT : T ≠ 0) :
    Tendsto (fun σ : ℝ ↦ P_σ σ T) (𝓝 (-1 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hcosh : 1 < cosh (π * T / 2) :=
    one_lt_cosh.mpr (div_ne_zero (mul_ne_zero pi_ne_zero hT) two_ne_zero)
  have hangle : Continuous θ := by unfold θ; fun_prop
  have hcontinuous : ContinuousAt (fun σ : ℝ ↦ P_σ σ T) (-1 : ℝ) := by
    unfold P_σ
    refine (continuous_sin.comp hangle).continuousAt.div (continuousAt_const.mul
      (continuousAt_const.sub (continuous_cos.comp hangle).continuousAt)) ?_
    simp only [θ]
    norm_num
    linarith
  convert hcontinuous.tendsto using 1
  all_goals simp [P_σ, θ]

/-- Comparison with the central kernel: any `c > 0` with `c cosh(πT/2) ≤ cosh(πT/2) - cos θ_σ`
gives `P_σ(T) ≤ P_0(T)/c`. -/
theorem stripPoissonKernel_le_center_of_mul_cosh_le {σ c T : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    (hc : 0 < c) (hcompare : c * cosh (π * T / 2) ≤ cosh (π * T / 2) - cos (θ σ)) :
    P_σ σ T ≤ 1 / c * P_σ 0 T := by
  have hangle := stripAngle_mem_Ioo hbelow habove
  have hsin : 0 < sin (θ σ) := sin_pos_of_pos_of_lt_pi hangle.1 hangle.2
  have hcosh : 0 < cosh (π * T / 2) := cosh_pos _
  have hcA : 0 < 4 * (c * cosh (π * T / 2)) := by positivity
  calc
    P_σ σ T = sin (θ σ) / (4 * (cosh (π * T / 2) - cos (θ σ))) := rfl
    _ ≤ sin (θ σ) / (4 * (c * cosh (π * T / 2))) :=
      div_le_div_of_nonneg_left hsin.le hcA (by linarith)
    _ ≤ 1 / (4 * (c * cosh (π * T / 2))) := div_le_div_of_nonneg_right (sin_le_one (θ σ)) hcA.le
    _ = 1 / c * P_σ 0 T := by
      rw [show P_σ 0 T = 1 / (4 * cosh (π * T / 2)) by simp [P_σ, θ]]
      field_simp

/-- `cos θ_σ < 1` for `-1 < σ < 1`. -/
theorem cos_stripAngle_lt_one {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) : cos (θ σ) < 1 := by
  have hangle := stripAngle_mem_Ioo hbelow habove
  simpa using cos_lt_cos_of_nonneg_of_le_pi le_rfl hangle.2.le hangle.1

/-- Away from `T = 0` the kernels `P_σ` with `-1 < σ ≤ 0` are dominated by the central kernel
with a constant depending only on the gap `δ ≤ |T|`. -/
theorem stripPoissonKernel_le_center_of_lower_of_abs_ge {σ δ T : ℝ}
    (hbelow : -1 < σ) (hnonpos : σ ≤ 0) (hδ : 0 < δ) (hT : δ ≤ |T|) :
    P_σ σ T ≤ 1 / (1 - (cosh (π * δ / 2))⁻¹) * P_σ 0 T := by
  have hC : 1 < cosh (π * δ / 2) :=
    one_lt_cosh.mpr (div_pos (mul_pos pi_pos hδ) two_pos).ne'
  have hCA : cosh (π * δ / 2) ≤ cosh (π * T / 2) := by
    refine cosh_le_cosh.mpr ?_
    rw [abs_div, abs_div, abs_mul, abs_mul, abs_of_pos pi_pos, abs_of_pos hδ]
    norm_num
    gcongr
  have hratio : 1 ≤ cosh (π * T / 2) / cosh (π * δ / 2) :=
    (one_le_div (by linarith)).mpr hCA
  refine stripPoissonKernel_le_center_of_mul_cosh_le hbelow (by linarith)
    (by linarith [(inv_lt_one₀ (by linarith : (0 : ℝ) < cosh (π * δ / 2))).mpr hC]) ?_
  rw [sub_mul, one_mul, inv_mul_eq_div]
  linarith [cos_le_one (θ σ)]

/-- For `-1 < σ ≤ 0` the kernel `P_σ` is dominated by the central kernel `P_0`. -/
theorem stripPoissonKernel_le_center_of_lower {σ : ℝ} (hbelow : -1 < σ) (hnonpos : σ ≤ 0)
    (T : ℝ) : P_σ σ T ≤ 1 / (1 - cos (θ σ)) * P_σ 0 T := by
  have habove : σ < 1 := by linarith
  have hcos : 0 ≤ cos (θ σ) := by
    refine cos_nonneg_of_mem_Icc ⟨?_, ?_⟩ <;> unfold θ <;>
      nlinarith [pi_pos, mul_nonpos_of_nonneg_of_nonpos pi_pos.le hnonpos]
  refine stripPoissonKernel_le_center_of_mul_cosh_le hbelow habove
    (by linarith [cos_stripAngle_lt_one hbelow habove]) ?_
  nlinarith [mul_nonneg hcos (sub_nonneg.mpr (one_le_cosh (π * T / 2)))]

/-- Integrability against the central kernel transfers to every `P_σ` with `-1 < σ ≤ 0`. -/
theorem stripPoissonKernel_lower_product_integrable {σ : ℝ} (hbelow : -1 < σ) (hnonpos : σ ≤ 0)
    {g : ℝ → ℝ} (hg : Continuous g) (hbase : Integrable fun T : ℝ ↦ P_σ 0 T * g T) :
    Integrable fun T : ℝ ↦ P_σ σ T * g T := by
  have habove : σ < 1 := by linarith
  have hmeas : Measurable fun T : ℝ ↦ P_σ σ T * g T :=
    (by unfold P_σ θ; fun_prop : Measurable fun T : ℝ ↦ P_σ σ T).mul hg.measurable
  refine (hbase.norm.const_mul (1 / (1 - cos (θ σ)))).mono' hmeas.aestronglyMeasurable
    (.of_forall fun T ↦ ?_)
  have hpos := stripPoissonKernel_pos hbelow habove T
  have hcenter := stripPoissonKernel_pos (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1) T
  calc
    ‖P_σ σ T * g T‖ = P_σ σ T * ‖g T‖ := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos hpos]
    _ ≤ 1 / (1 - cos (θ σ)) * P_σ 0 T * ‖g T‖ := by
      gcongr
      exact stripPoissonKernel_le_center_of_lower hbelow hnonpos T
    _ = 1 / (1 - cos (θ σ)) * ‖P_σ 0 T * g T‖ := by
      rw [norm_mul, Real.norm_of_nonneg hcenter.le]
      ring

end

end CohnElkies
