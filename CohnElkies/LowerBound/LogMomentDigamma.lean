import CohnElkies.LowerBound.LimitingDensity
import CohnElkiesForMathlib.Analysis.SpecialFunctions.Gamma.DigammaIntegral

/-!
# The logarithmic moment of the logistic density (report (22))

For `x ≥ 0`, `∫ p(u) log √(x² + u²) du = ψ((x + 1) / 2) + log 2`, where `p` is the logistic
density `poissonLogisticDensity` and `ψ` the digamma function
(`CohnElkies.integral_poissonLogisticDensity_mul_log_sqrt`; equation (22) of the report, in the
proof of Lemma 3.4).

For `x > 0` the complex Frullani formula with parameters `1` and `x + iu` gives
`log √(x² + u²) = Re log (x + iu) = ∫₀^∞ (e^{-t} - e^{-xt} cos (ut)) / t dt`. Integrating against
`p` and swapping the integrals (Fubini; the kernel is bounded by `1 + x + |u|` for `t ≤ 1` and by
`e^{-t} + e^{-xt}` for `t ≥ 1`), the inner `u`-integral is
`(e^{-t} - e^{-xt} t / sinh t) / t = e^{-t} / t - e^{-xt} / sinh t` by the cosine transform of `p`.
Gauss's integral for `ψ((x + 1) / 2)` becomes `∫₀^∞ (e^{-2s} / s - e^{-xs} / sinh s) ds` after the
substitution `t = 2s`, and the difference of the two integrands is the Frullani kernel
`(e^{-s} - e^{-2s}) / s`, whose integral is `log 2`. The case `x = 0` follows by dominated
convergence along `x = 1 / (n + 1) ↓ 0`, with the majorant `p(u) |u| + π 𝟙_{[-1, 1]}(u) |log u|`,
and the continuity of `ψ` on `(0, ∞)`.
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory Real Set
open scoped Topology

/-! ### The Frullani kernel of `log √(x² + u²)` -/

/-- The Frullani kernel `(e^{-t} - e^{-xt} cos (ut)) / t` of `log √(x² + u²)`: the real part of
`Frullani.cexpKernel 1 (x + iu)`. -/
def logSqrtKernel (x u t : ℝ) : ℝ := (exp (-t) - exp (-x * t) * cos (u * t)) / t

theorem logSqrtKernel_re (x u t : ℝ) :
    (Frullani.cexpKernel 1 ((x : ℂ) + I * (u : ℂ)) t).re = logSqrtKernel x u t := by
  unfold Frullani.cexpKernel logSqrtKernel
  rw [Complex.div_ofReal_re]
  simp [Complex.exp_re, Complex.mul_re, Complex.mul_im]

theorem norm_ofReal_add_I_mul_ofReal (x u : ℝ) : ‖(x : ℂ) + I * (u : ℂ)‖ = √(x ^ 2 + u ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp
  ring

/-- `log √(x² + u²) = ∫₀^∞ (e^{-t} - e^{-xt} cos (ut)) / t dt` for `x > 0`: the real part of the
complex Frullani formula `∫₀^∞ (e^{-t} - e^{-(x + iu) t}) / t dt = log (x + iu)`. -/
theorem integral_logSqrtKernel {x : ℝ} (hx : 0 < x) (u : ℝ) :
    ∫ t in Ioi (0 : ℝ), logSqrtKernel x u t = log (√(x ^ 2 + u ^ 2)) := by
  have hw : 0 < ((x : ℂ) + I * (u : ℂ)).re := by simpa using hx
  have h1 : (0 : ℝ) < (1 : ℂ).re := by norm_num
  calc ∫ t in Ioi (0 : ℝ), logSqrtKernel x u t
      = ∫ t in Ioi (0 : ℝ), (Frullani.cexpKernel 1 ((x : ℂ) + I * (u : ℂ)) t).re :=
        setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ (logSqrtKernel_re x u t).symm
    _ = (∫ t in Ioi (0 : ℝ), Frullani.cexpKernel 1 ((x : ℂ) + I * (u : ℂ)) t).re :=
        integral_re (Frullani.integrableOn_cexpKernel h1 hw)
    _ = log (√(x ^ 2 + u ^ 2)) := by
        rw [Frullani.integral_cexpKernel h1 hw, Complex.log_one, sub_zero, Complex.log_re,
          norm_ofReal_add_I_mul_ofReal]

/-- `|(e^{-t} - e^{-xt} cos (ut)) / t| ≤ 1 + x + |u|` for `t > 0` and `x ≥ 0`, from
`|e^{-t} - e^{-xt}| ≤ (1 - e^{-t}) + (1 - e^{-xt}) ≤ (1 + x) t` and `|1 - cos (ut)| ≤ |u| t`. -/
theorem abs_logSqrtKernel_le {x : ℝ} (hx : 0 ≤ x) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    |logSqrtKernel x u t| ≤ 1 + x + |u| := by
  have hr0 : 0 < exp (-x * t) := exp_pos _
  have hq1 : exp (-t) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have hr1 : exp (-x * t) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
  have hqt : 1 - exp (-t) ≤ t := by linarith [add_one_le_exp (-t)]
  have hrt : 1 - exp (-x * t) ≤ x * t := by linarith [add_one_le_exp (-x * t)]
  have hcos : |cos (u * t) - 1| ≤ |u| * t := by
    simpa [abs_mul, abs_of_pos ht] using abs_cos_sub_cos_le (u * t) 0
  have h1 : |(1 - exp (-x * t)) - (1 - exp (-t))| ≤ x * t + t :=
    calc |(1 - exp (-x * t)) - (1 - exp (-t))| ≤ |1 - exp (-x * t)| + |1 - exp (-t)| := abs_sub _ _
      _ = (1 - exp (-x * t)) + (1 - exp (-t)) := by
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      _ ≤ x * t + t := by linarith
  have h2 : |exp (-x * t) * (cos (u * t) - 1)| ≤ |u| * t := by
    rw [abs_mul, abs_of_pos hr0]
    calc exp (-x * t) * |cos (u * t) - 1| ≤ 1 * (|u| * t) :=
          mul_le_mul hr1 hcos (abs_nonneg _) zero_le_one
      _ = |u| * t := one_mul _
  unfold logSqrtKernel
  rw [abs_div, abs_of_pos ht, div_le_iff₀ ht,
    show exp (-t) - exp (-x * t) * cos (u * t) =
      ((1 - exp (-x * t)) - (1 - exp (-t))) - exp (-x * t) * (cos (u * t) - 1) by ring]
  calc |((1 - exp (-x * t)) - (1 - exp (-t))) - exp (-x * t) * (cos (u * t) - 1)|
      ≤ |(1 - exp (-x * t)) - (1 - exp (-t))| + |exp (-x * t) * (cos (u * t) - 1)| :=
        abs_sub _ _
    _ ≤ (x * t + t) + |u| * t := add_le_add h1 h2
    _ = (1 + x + |u|) * t := by ring

/-- `|(e^{-t} - e^{-xt} cos (ut)) / t| ≤ e^{-t} + e^{-xt}` for `t ≥ 1`. -/
theorem abs_logSqrtKernel_le_tail (x u : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    |logSqrtKernel x u t| ≤ exp (-t) + exp (-x * t) := by
  have htp : 0 < t := by linarith
  unfold logSqrtKernel
  rw [abs_div, abs_of_pos htp, div_le_iff₀ htp]
  calc |exp (-t) - exp (-x * t) * cos (u * t)|
      ≤ |exp (-t)| + |exp (-x * t) * cos (u * t)| := abs_sub _ _
    _ ≤ exp (-t) + exp (-x * t) := by
        rw [abs_of_pos (exp_pos _), abs_mul, abs_of_pos (exp_pos _)]
        exact add_le_add le_rfl (mul_le_of_le_one_right (exp_pos _).le (abs_cos_le_one _))
    _ ≤ (exp (-t) + exp (-x * t)) * t := le_mul_of_one_le_right (by positivity) ht

theorem logSqrtTail_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ ↦ exp (-t) + exp (-x * t)) (Ioi 1) := by
  have h1 : IntegrableOn (fun t : ℝ ↦ exp (-t)) (Ioi 1) := by
    simpa using (integrableOn_exp_neg_mul_Ioi (a := (1 : ℝ)) zero_lt_one).mono_set
      (Ioi_subset_Ioi zero_le_one)
  exact h1.add ((integrableOn_exp_neg_mul_Ioi hx).mono_set (Ioi_subset_Ioi zero_le_one))

/-- Fubini's hypothesis: `p(u) (e^{-t} - e^{-xt} cos (ut)) / t` is integrable on `ℝ × (0, ∞)`. -/
theorem poissonLogistic_logSqrtKernel_integrable {x : ℝ} (hx : 0 < x) :
    Integrable (fun p : ℝ × ℝ ↦ poissonLogisticDensity p.1 * logSqrtKernel x p.1 p.2)
      (volume.prod (volume.restrict (Ioi 0))) := by
  set F : ℝ × ℝ → ℝ := fun p ↦ poissonLogisticDensity p.1 * logSqrtKernel x p.1 p.2 with hF
  have hmeas : Measurable F := by
    rw [hF]
    unfold poissonLogisticDensity logSqrtKernel
    fun_prop
  have key (s : Set ℝ) : Integrable F (volume.prod (volume.restrict s)) ↔
      IntegrableOn F (univ ×ˢ s) (volume.prod volume) := by
    change _ ↔ Integrable F ((volume.prod volume).restrict (univ ×ˢ s))
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hnear : Integrable F (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    have hfreq : Integrable fun u : ℝ ↦ poissonLogisticDensity u * (1 + x + |u|) := by
      refine ((poissonLogisticDensity_integrable.const_mul (1 + x)).add
        (poissonLogisticDensity_abs_moment_integrable 1)).congr (.of_forall fun u ↦ ?_)
      simp only [Pi.add_apply, pow_one]
      ring
    have hconst : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Ioc (0 : ℝ) 1) :=
      integrableOn_const measure_Ioc_lt_top.ne
    refine (hfreq.mul_prod hconst).mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [(Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_snd)).2
      (.of_forall fun _ ↦ ae_restrict_mem measurableSet_Ioc)] with p hp
    have hd := poissonLogisticDensity_pos p.1
    rw [hF, Real.norm_eq_abs, abs_mul, abs_of_pos hd, mul_one]
    exact mul_le_mul_of_nonneg_left (abs_logSqrtKernel_le hx.le p.1 hp.1) hd.le
  have hfar : Integrable F (volume.prod (volume.restrict (Ioi (1 : ℝ)))) := by
    refine (poissonLogisticDensity_integrable.mul_prod (logSqrtTail_integrable hx)).mono'
      hmeas.aestronglyMeasurable ?_
    filter_upwards [(Measure.ae_prod_iff_ae_ae (measurableSet_Ioi.preimage measurable_snd)).2
      (.of_forall fun _ ↦ ae_restrict_mem measurableSet_Ioi)] with p hp
    have hd := poissonLogisticDensity_pos p.1
    rw [hF, Real.norm_eq_abs, abs_mul, abs_of_pos hd]
    exact mul_le_mul_of_nonneg_left (abs_logSqrtKernel_le_tail x p.1 (mem_Ioi.mp hp).le) hd.le
  have hunion : (univ : Set ℝ) ×ˢ Ioi (0 : ℝ) =
      univ ×ˢ Ioc (0 : ℝ) 1 ∪ univ ×ˢ Ioi (1 : ℝ) := by
    rw [← prod_union, Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine (key _).2 ?_
  rw [hunion]
  exact ((key _).1 hnear).union ((key _).1 hfar)

/-! ### The averaged kernel and Gauss's integral -/

/-- The `p`-average `e^{-t} / t - e^{-xt} / sinh t` of the kernel
`(e^{-t} - e^{-xt} cos (ut)) / t`. -/
def logMomentKernel (x t : ℝ) : ℝ := exp (-t) / t - exp (-x * t) / sinh t

/-- Averaging the kernel against `p`, using `∫ p = 1` and `∫ p(u) cos (tu) du = t / sinh t`:
`∫ p(u) (e^{-t} - e^{-xt} cos (ut)) / t du = e^{-t} / t - e^{-xt} / sinh t`. -/
theorem integral_poissonLogisticDensity_mul_logSqrtKernel (x : ℝ) {t : ℝ} (ht : 0 < t) :
    ∫ u : ℝ, poissonLogisticDensity u * logSqrtKernel x u t = logMomentKernel x t := by
  have h1 : Integrable fun u : ℝ ↦ exp (-t) * poissonLogisticDensity u :=
    poissonLogisticDensity_integrable.const_mul _
  have h2 : Integrable fun u : ℝ ↦ exp (-x * t) * (poissonLogisticDensity u * cos (t * u)) :=
    (poissonLogistic_cosine_integrable t).const_mul _
  have hsinh : sinh t ≠ 0 := (sinh_pos_iff.mpr ht).ne'
  calc ∫ u : ℝ, poissonLogisticDensity u * logSqrtKernel x u t
      = ∫ u : ℝ, (exp (-t) * poissonLogisticDensity u -
          exp (-x * t) * (poissonLogisticDensity u * cos (t * u))) / t := by
        refine integral_congr_ae ?_
        filter_upwards with u
        unfold logSqrtKernel
        rw [mul_comm u t]
        ring
    _ = (exp (-t) * (∫ u : ℝ, poissonLogisticDensity u) -
          exp (-x * t) * ∫ u : ℝ, poissonLogisticDensity u * cos (t * u)) / t := by
        rw [integral_div, integral_sub h1 h2, integral_const_mul, integral_const_mul]
    _ = logMomentKernel x t := by
        rw [integral_poissonLogisticDensity, poissonLogistic_cosine_transform t, if_neg ht.ne']
        unfold logMomentKernel
        field_simp

/-- Gauss's integrand at `(x + 1) / 2` after the substitution `t = 2s`:
`2 (e^{-2s} / (2s) - e^{-(x+1)s} / (1 - e^{-2s})) = e^{-2s} / s - e^{-xs} / sinh s`. -/
def digammaHalfKernel (x s : ℝ) : ℝ := exp (-2 * s) / s - exp (-x * s) / sinh s

theorem two_mul_digammaKernel_two_mul (x : ℝ) {s : ℝ} (hs : 0 < s) :
    2 * digammaKernel ((x + 1) / 2) (2 * s) = digammaHalfKernel x s := by
  have hs0 : s ≠ 0 := hs.ne'
  have hb0 : 0 < exp (-s) := exp_pos _
  have hb1 : exp (-s) < 1 := exp_lt_one_iff.mpr (by linarith)
  have hab : exp s * exp (-s) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  have hsinh : (exp s - exp (-s)) / 2 ≠ 0 := by
    rw [← sinh_eq]
    exact (sinh_pos_iff.mpr hs).ne'
  have h2s : exp (-(2 * s)) = exp (-s) ^ 2 := by
    rw [sq, ← exp_add]
    ring_nf
  have h2s' : exp (-2 * s) = exp (-s) ^ 2 := by
    rw [sq, ← exp_add]
    ring_nf
  have hxs : exp (-((x + 1) / 2) * (2 * s)) = exp (-x * s) * exp (-s) := by
    rw [← exp_add]
    ring_nf
  have hden : 1 - exp (-s) ^ 2 ≠ 0 := by nlinarith
  have key : 2 * (exp (-x * s) * exp (-s) / (1 - exp (-s) ^ 2)) =
      exp (-x * s) / ((exp s - exp (-s)) / 2) := by
    rw [mul_div_assoc', div_eq_div_iff hden hsinh]
    linear_combination exp (-x * s) * hab
  unfold digammaKernel digammaHalfKernel
  rw [h2s, h2s', hxs, sinh_eq, mul_sub, key]
  congr 1
  field_simp

/-- Gauss's integral for `ψ((x + 1) / 2)` after the substitution `t = 2s`:
`ψ((x + 1) / 2) = ∫₀^∞ (e^{-2s} / s - e^{-xs} / sinh s) ds`. -/
theorem digamma_half_eq_integral_digammaHalfKernel {x : ℝ} (hx : 0 ≤ x) :
    digamma ((x + 1) / 2) = ∫ s in Ioi (0 : ℝ), digammaHalfKernel x s := by
  have hm : 0 < (x + 1) / 2 := by positivity
  have hsub := integral_comp_mul_left_Ioi' (digammaKernel ((x + 1) / 2)) 0 two_pos
  rw [mul_zero, smul_eq_mul, ← integral_const_mul] at hsub
  rw [digamma_eq_integral_digammaKernel hm, ← hsub]
  exact setIntegral_congr_fun measurableSet_Ioi fun s hs ↦ two_mul_digammaKernel_two_mul x hs

theorem integrableOn_digammaHalfKernel {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (digammaHalfKernel x) (Ioi 0) := by
  have hm : 0 < (x + 1) / 2 := by positivity
  have h : IntegrableOn (fun s : ℝ ↦ digammaKernel ((x + 1) / 2) (2 * s)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff (digammaKernel ((x + 1) / 2)) 0 two_pos).2
      (by simpa using integrableOn_digammaKernel hm)
  exact IntegrableOn.congr_fun (h.const_mul 2) (fun s hs ↦ two_mul_digammaKernel_two_mul x hs)
    measurableSet_Ioi

/-- The averaged kernel is Gauss's (substituted) integrand plus the Frullani kernel of `log 2`. -/
theorem logMomentKernel_eq (x s : ℝ) :
    logMomentKernel x s = digammaHalfKernel x s + Frullani.expKernel 1 2 s := by
  unfold logMomentKernel digammaHalfKernel Frullani.expKernel
  rw [show exp (-1 * s) = exp (-s) by rw [neg_one_mul]]
  ring

/-- Report (22) for `x > 0`: `∫ p(u) log √(x² + u²) du = ψ((x + 1) / 2) + log 2`. -/
theorem integral_poissonLogisticDensity_mul_log_sqrt_of_pos {x : ℝ} (hx : 0 < x) :
    ∫ u : ℝ, poissonLogisticDensity u * log (√(x ^ 2 + u ^ 2)) =
      digamma ((x + 1) / 2) + log 2 := by
  calc ∫ u : ℝ, poissonLogisticDensity u * log (√(x ^ 2 + u ^ 2))
      = ∫ u : ℝ, ∫ t in Ioi (0 : ℝ), poissonLogisticDensity u * logSqrtKernel x u t := by
        refine integral_congr_ae ?_
        filter_upwards with u
        rw [integral_const_mul, integral_logSqrtKernel hx]
    _ = ∫ t in Ioi (0 : ℝ), ∫ u : ℝ, poissonLogisticDensity u * logSqrtKernel x u t :=
        integral_integral_swap (poissonLogistic_logSqrtKernel_integrable hx)
    _ = ∫ t in Ioi (0 : ℝ), logMomentKernel x t :=
        setIntegral_congr_fun measurableSet_Ioi fun t ht ↦
          integral_poissonLogisticDensity_mul_logSqrtKernel x ht
    _ = ∫ t in Ioi (0 : ℝ), (digammaHalfKernel x t + Frullani.expKernel 1 2 t) :=
        setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ logMomentKernel_eq x t
    _ = digamma ((x + 1) / 2) + log 2 := by
        rw [integral_add (integrableOn_digammaHalfKernel hx.le)
            (Frullani.integrableOn_expKernel one_pos one_le_two),
          digamma_half_eq_integral_digammaHalfKernel hx.le,
          Frullani.integral_expKernel one_pos one_le_two, div_one]

/-! ### The case `x = 0` by dominated convergence -/

/-- `|u| ≤ √(x² + u²) ≤ |u| + x` for `x ≥ 0`. -/
theorem abs_le_sqrt_sq_add_sq_and_le {x : ℝ} (hx : 0 ≤ x) (u : ℝ) :
    |u| ≤ √(x ^ 2 + u ^ 2) ∧ √(x ^ 2 + u ^ 2) ≤ |u| + x := by
  refine ⟨Real.abs_le_sqrt (by nlinarith), ?_⟩
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [abs_nonneg u, sq_abs u]

/-- For `0 ≤ x ≤ 1` and `u ≠ 0`, `log |u| ≤ log √(x² + u²) ≤ |u|`. -/
theorem log_abs_le_log_sqrt_and_le {x u : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hu : u ≠ 0) :
    log |u| ≤ log (√(x ^ 2 + u ^ 2)) ∧ log (√(x ^ 2 + u ^ 2)) ≤ |u| := by
  have hu0 : 0 < |u| := abs_pos.mpr hu
  obtain ⟨hlow, hupp⟩ := abs_le_sqrt_sq_add_sq_and_le hx0 u
  refine ⟨log_le_log hu0 hlow, ?_⟩
  calc log (√(x ^ 2 + u ^ 2)) ≤ log (|u| + 1) :=
        log_le_log (hu0.trans_le hlow) (hupp.trans (by linarith))
    _ ≤ |u| + 1 - 1 := log_le_sub_one_of_pos (by positivity)
    _ = |u| := by ring

/-- The majorant `p(u) |u| + π 𝟙_{[-1, 1]}(u) |log u|` of `p(u) log √(x² + u²)` for `0 ≤ x ≤ 1`. -/
def logSqrtMajorant (u : ℝ) : ℝ :=
  poissonLogisticDensity u * |u| + π * (Icc (-1 : ℝ) 1).indicator (fun v ↦ |log v|) u

theorem logSqrtMajorant_integrable : Integrable logSqrtMajorant := by
  have hlog : IntegrableOn (fun v : ℝ ↦ |log v|) (Icc (-1 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).1
      (IntervalIntegrable.abs intervalIntegral.intervalIntegrable_log')
  have h1 : Integrable fun u : ℝ ↦ poissonLogisticDensity u * |u| := by
    simpa using poissonLogisticDensity_abs_moment_integrable 1
  exact h1.add (((integrable_indicator_iff measurableSet_Icc).2 hlog).const_mul π)

theorem poissonLogisticDensity_le_pi (u : ℝ) : poissonLogisticDensity u ≤ π :=
  (poissonLogisticDensity_le_pi_exp u).trans (mul_le_of_le_one_right pi_pos.le
    (exp_le_one_iff.mpr (by rw [neg_mul, neg_nonpos]; positivity)))

/-- The pointwise domination `|p(u) log √(x² + u²)| ≤ p(u) |u| + π 𝟙_{[-1, 1]}(u) |log u|` for
`0 ≤ x ≤ 1` and `u ≠ 0`. -/
theorem abs_poissonLogisticDensity_mul_log_sqrt_le {x u : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hu : u ≠ 0) :
    |poissonLogisticDensity u * log (√(x ^ 2 + u ^ 2))| ≤ logSqrtMajorant u := by
  obtain ⟨hlow, hupp⟩ := log_abs_le_log_sqrt_and_le hx0 hx1 hu
  have hd := poissonLogisticDensity_pos u
  have hple := poissonLogisticDensity_le_pi u
  rw [abs_mul, abs_of_pos hd]
  unfold logSqrtMajorant
  by_cases hmem : u ∈ Icc (-1 : ℝ) 1
  · rw [indicator_of_mem hmem]
    have hlow' : log u ≤ log (√(x ^ 2 + u ^ 2)) := by rwa [log_abs] at hlow
    have h1 : |log (√(x ^ 2 + u ^ 2))| ≤ |log u| + |u| :=
      abs_le.mpr ⟨by linarith [neg_abs_le (log u), abs_nonneg u], by linarith [abs_nonneg (log u)]⟩
    calc poissonLogisticDensity u * |log (√(x ^ 2 + u ^ 2))|
        ≤ poissonLogisticDensity u * (|log u| + |u|) := mul_le_mul_of_nonneg_left h1 hd.le
      _ = poissonLogisticDensity u * |u| + poissonLogisticDensity u * |log u| := by ring
      _ ≤ poissonLogisticDensity u * |u| + π * |log u| := by gcongr
  · rw [indicator_of_notMem hmem, mul_zero, add_zero]
    have hu1 : 1 ≤ |u| := by
      simp only [mem_Icc, not_and_or, not_le] at hmem
      rcases hmem with h | h
      · exact le_abs.mpr (Or.inr (by linarith))
      · exact le_abs.mpr (Or.inl h.le)
    rw [abs_of_nonneg ((log_nonneg hu1).trans hlow)]
    exact mul_le_mul_of_nonneg_left hupp hd.le

/-- Dominated convergence along `x = 1 / (n + 1) ↓ 0` for the left side of report (22). -/
theorem tendsto_integral_poissonLogisticDensity_mul_log_sqrt :
    Tendsto (fun n : ℕ ↦ ∫ u : ℝ,
        poissonLogisticDensity u * log (√((1 / ((n : ℝ) + 1)) ^ 2 + u ^ 2))) atTop
      (𝓝 (∫ u : ℝ, poissonLogisticDensity u * log (√((0 : ℝ) ^ 2 + u ^ 2)))) := by
  have hae : ∀ᵐ u : ℝ, u ≠ 0 := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with u hu
    simpa using hu
  refine tendsto_integral_of_dominated_convergence logSqrtMajorant (fun n ↦ ?_)
    logSqrtMajorant_integrable (fun n ↦ ?_) ?_
  · exact (by unfold poissonLogisticDensity; fun_prop : Measurable fun u : ℝ ↦
      poissonLogisticDensity u * log (√((1 / ((n : ℝ) + 1)) ^ 2 + u ^ 2))).aestronglyMeasurable
  · filter_upwards [hae] with u hu
    have h0 : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    rw [Real.norm_eq_abs]
    exact abs_poissonLogisticDensity_mul_log_sqrt_le h0 h1 hu
  · filter_upwards [hae] with u hu
    have hcont :
        ContinuousAt (fun x : ℝ ↦ poissonLogisticDensity u * log (√(x ^ 2 + u ^ 2))) 0 := by
      refine continuousAt_const.mul (ContinuousAt.log ?_ ?_)
      · exact (by fun_prop : Continuous fun x : ℝ ↦ √(x ^ 2 + u ^ 2)).continuousAt
      · exact (Real.sqrt_pos.mpr (by positivity)).ne'
    exact hcont.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat

/-- Report (22): `∫ p(u) log √(x² + u²) du = ψ((x + 1) / 2) + log 2` for `x ≥ 0`. -/
theorem integral_poissonLogisticDensity_mul_log_sqrt {x : ℝ} (hx : 0 ≤ x) :
    ∫ u : ℝ, poissonLogisticDensity u * Real.log (√(x ^ 2 + u ^ 2)) =
      Real.digamma ((x + 1) / 2) + Real.log 2 := by
  rcases hx.lt_or_eq with hx | rfl
  · exact integral_poissonLogisticDensity_mul_log_sqrt_of_pos hx
  · refine tendsto_nhds_unique tendsto_integral_poissonLogisticDensity_mul_log_sqrt ?_
    have hcont : ContinuousAt (fun x : ℝ ↦ digamma ((x + 1) / 2) + log 2) 0 := by
      have hf : ContinuousAt (fun x : ℝ ↦ (x + 1) / 2) 0 := by fun_prop
      have hg : ContinuousAt digamma ((0 + 1) / 2) :=
        continuousOn_digamma_Ioi.continuousAt (Ioi_mem_nhds (by norm_num))
      exact (hg.comp_of_eq hf rfl).add continuousAt_const
    refine (hcont.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat).congr fun n ↦ ?_
    exact (integral_poissonLogisticDensity_mul_log_sqrt_of_pos (by positivity)).symm

end

end CohnElkies
