import CohnElkies.UpperBound.Envelope
import CohnElkies.Basic
import CohnElkiesForMathlib.Analysis.SpecialFunctions.FrullaniIntegral

/-!
# The limiting saddle radius `α_ε → 1/π` (report §4, (32)–(33))

The normalized radius `α_ε = exp (-(log π)/2 + ∫ shell contributions)` of the saddle-point
construction and its limit as `ε → 0⁺`: the positive-shell contribution tends to zero, the
short-shell contribution tends to the Laplace integral of report (33), which equals `log (π/2)`
by the Wallis product, so that `α_ε → 1/π` (`tendsto_limitingSaddleRadius`).
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory Real
open scoped Topology

/-! ### The limiting saddle radius `α_ε → 1 / π`, report (32)–(33) -/

theorem tendsto_cubic_gaussian_atTop :
    Tendsto (fun x : ℝ ↦ (x ^ 3 + 1) * exp (-(x ^ 2) / 8)) atTop (𝓝 0) := by
  have hlinear : Tendsto (fun x : ℝ ↦ (x ^ 3 + 1) * exp (-(1 / 8 : ℝ) * x)) atTop (𝓝 0) := by
    have hpoly : Tendsto (fun x : ℝ ↦ x ^ 3 * exp (-(1 / 8 : ℝ) * x)) atTop (𝓝 0) := by
      simpa [Real.rpow_natCast] using
        tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3 : ℝ) (1 / 8 : ℝ) (by norm_num)
    have hone : Tendsto (fun x : ℝ ↦ exp (-(1 / 8 : ℝ) * x)) atTop (𝓝 0) := by
      simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0 : ℝ) (1 / 8 : ℝ) (by norm_num)
    convert! hpoly.add hone using 1
    · ext x
      ring
    · norm_num
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := (0 : ℝ))) hlinear ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)

/-- The exponentially small majorant of Lemma 4.2 for the positive shell. -/
def shellRadiusMajorant (ε : ℝ) : ℝ := (Bε ε + 1) * Qε ε * exp (ε / 4 * (Bε ε + 1))

theorem shellRadiusMajorant_inv {x : ℝ} (hx : x ≠ 0) :
    shellRadiusMajorant x⁻¹ = ((x ^ 3 + 1) * exp (-(x ^ 2) / 8)) * exp (x⁻¹ / 4) := by
  unfold shellRadiusMajorant Qε Bε
  simp only [inv_inv, mul_assoc]
  congr 1
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  field_simp
  ring

theorem tendsto_shellRadiusMajorant : Tendsto shellRadiusMajorant (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  refine tendsto_nhdsGT_zero_of_comp_inv_tendsto_atTop ?_
  have hsmall : Tendsto (fun x : ℝ ↦ x⁻¹ / 4) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.div_const (4 : ℝ)
  have hzero : Tendsto (fun x : ℝ ↦ ((x ^ 3 + 1) * exp (-(x ^ 2) / 8)) * exp (x⁻¹ / 4))
      atTop (𝓝 0) := by
    simpa using tendsto_cubic_gaussian_atTop.mul (by simpa using hsmall.rexp)
  refine hzero.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
  exact (shellRadiusMajorant_inv hx).symm

theorem tendsto_positiveShellRadiusContribution :
    Tendsto positiveShellRadiusContribution (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds (x := (0 : ℝ)))
    tendsto_shellRadiusMajorant ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (positiveShellRadiusContribution_bounds hε).1
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (positiveShellRadiusContribution_bounds hε).2

/-- `tanh a ≤ a` for `a ≥ 0`, in the form needed for the hyperbolic ratio bound. -/
theorem sinh_le_mul_cosh {a : ℝ} (ha : 0 ≤ a) : sinh a ≤ a * cosh a := by
  have hderiv (x : ℝ) : HasDerivAt (fun u : ℝ ↦ u * cosh u - sinh u) (x * sinh x) x := by
    convert! ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub (Real.hasDerivAt_sinh x) using 1
    simp [id]
  have hdiff : Differentiable ℝ fun u : ℝ ↦ u * cosh u - sinh u := fun x ↦
    (hderiv x).differentiableAt
  have h := monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hdiff.continuous.continuousOn
    hdiff.differentiableOn (fun x hx ↦ by
      rw [interior_Ici] at hx
      rw [(hderiv x).deriv]
      exact mul_nonneg hx.le (Real.sinh_nonneg_iff.mpr hx.le))
    (Set.mem_Ici.mpr le_rfl) ha ha
  norm_num at h
  linarith

/-- The integrand `w_s(a) · a · sinh ((1 + ε/4) a)` of the short-shell radius contribution. -/
def shortShellRadiusIntegrand (ε a : ℝ) : ℝ := w_s ε a * a * sinh ((1 + ε / 4) * a)

/-- Its `ε → 0` limit `-e^{-2a} tanh a / (2a)`, the integrand of report (33). -/
def wallisRadiusIntegrand (a : ℝ) : ℝ := -(exp (-2 * a) * tanh a / (2 * a))

theorem tendsto_shortShellRadiusIntegrand {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε : ℝ ↦ shortShellRadiusIntegrand ε a) (𝓝[>] (0 : ℝ))
      (𝓝 (wallisRadiusIntegrand a)) := by
  have hc : Continuous fun ε : ℝ ↦ shortShellRadiusIntegrand ε a := by
    unfold shortShellRadiusIntegrand w_s bε
    fun_prop
  have hvalue : shortShellRadiusIntegrand 0 a = wallisRadiusIntegrand a := by
    unfold shortShellRadiusIntegrand w_s bε wallisRadiusIntegrand
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [ha.ne', (cosh_pos a).ne']
    ring_nf
  simpa [hvalue] using
    (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))

theorem shortMargin_abs_le_exp {ε a : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (ha : 0 ≤ a) :
    |bε ε a| ≤ 11 * exp a := by
  calc |bε ε a| = |1 - 2 * ε * (1 + a)| := rfl
    _ ≤ |(1 : ℝ)| + |2 * ε * (1 + a)| := abs_sub _ _
    _ = 1 + 2 * ε * (1 + a) := by
        rw [abs_of_pos (by norm_num : (0 : ℝ) < 1), abs_of_nonneg (by positivity)]
    _ ≤ 11 * (1 + a) := by
        nlinarith [mul_le_mul_of_nonneg_right hε1 (show 0 ≤ 1 + a by linarith)]
    _ ≤ 11 * exp a := by
        gcongr
        nlinarith [Real.add_one_le_exp a]

theorem shortShellHyperbolicRatio_le {ε a : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (ha : 0 ≤ a) :
    sinh ((1 + ε / 4) * a) / cosh a ≤ (5 / 4 : ℝ) * a * exp (a / 4) := by
  have hδ : 0 ≤ ε / 4 := by positivity
  have harg : 0 ≤ (1 + ε / 4) * a := by positivity
  calc sinh ((1 + ε / 4) * a) / cosh a
      ≤ ((1 + ε / 4) * a) * (cosh ((1 + ε / 4) * a) / cosh a) := by
        rw [← mul_div_assoc]
        exact (div_le_div_iff_of_pos_right (cosh_pos a)).2 (sinh_le_mul_cosh harg)
    _ ≤ ((5 / 4 : ℝ) * a) * exp (ε / 4 * a) := by
        gcongr
        · nlinarith
        · exact cosh_ratio_upper ha hδ
    _ ≤ ((5 / 4 : ℝ) * a) * exp (a / 4) := by
        gcongr
        nlinarith [mul_le_mul_of_nonneg_right hε1 ha]

theorem shortShellRadiusIntegrand_eq_ratio {ε a : ℝ} (ha : a ≠ 0) :
    shortShellRadiusIntegrand ε a =
      -(bε ε a * exp (-2 * a) * (sinh ((1 + ε / 4) * a) / cosh a) / (2 * a)) := by
  unfold shortShellRadiusIntegrand w_s
  field_simp [ha, (cosh_pos a).ne']

theorem shortShellRadiusIntegrand_abs_le {ε a : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (ha : 0 < a) :
    |shortShellRadiusIntegrand ε a| ≤ 7 * exp (-(3 / 4 : ℝ) * a) := by
  have harg : 0 ≤ (1 + ε / 4) * a := by positivity
  have hratio0 : 0 ≤ sinh ((1 + ε / 4) * a) / cosh a :=
    div_nonneg (Real.sinh_nonneg_iff.mpr harg) (cosh_pos a).le
  rw [shortShellRadiusIntegrand_eq_ratio ha.ne', abs_neg, abs_div, abs_mul, abs_mul,
    abs_of_pos (exp_pos (-2 * a)), abs_of_nonneg hratio0,
    abs_of_pos (by positivity : 0 < (2 : ℝ) * a)]
  calc |bε ε a| * exp (-2 * a) * (sinh ((1 + ε / 4) * a) / cosh a) / (2 * a)
      ≤ (11 * exp a) * exp (-2 * a) * ((5 / 4 : ℝ) * a * exp (a / 4)) / (2 * a) := by
        gcongr
        · exact shortMargin_abs_le_exp hε0 hε1 ha.le
        · exact shortShellHyperbolicRatio_le hε0 hε1 ha.le
    _ = (55 / 8 : ℝ) * exp (-(3 / 4 : ℝ) * a) := by
        rw [show -(3 / 4 : ℝ) * a = a + -2 * a + a / 4 by ring, Real.exp_add, Real.exp_add]
        field_simp [ha.ne']
        ring
    _ ≤ 7 * exp (-(3 / 4 : ℝ) * a) :=
        mul_le_mul_of_nonneg_right (by norm_num) (exp_pos _).le

/-- The integrable majorant `7 e^{-3a/4}` of the short-shell integrand. -/
def shortShellRadiusMajorant (a : ℝ) : ℝ := 7 * exp (-(3 / 4 : ℝ) * a)

theorem shortShellRadiusMajorant_integrable :
    IntegrableOn shortShellRadiusMajorant (Set.Ioi (0 : ℝ)) := by
  change Integrable (fun a : ℝ ↦ 7 * exp (-(3 / 4 : ℝ) * a)) (volume.restrict (Set.Ioi (0 : ℝ)))
  simpa only [neg_div] using
    (integrableOn_exp_mul_Ioi (a := (-3 / 4 : ℝ)) (by norm_num) 0).const_mul 7

theorem shortShellRadiusIntegrand_measurable (ε : ℝ) :
    Measurable (shortShellRadiusIntegrand ε) := by
  unfold shortShellRadiusIntegrand w_s bε
  fun_prop

theorem tendsto_shortCutoff : Tendsto a₀ε (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have ht : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  change Tendsto (fun ε : ℝ ↦ ε ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0)
  simpa using ht.pow 2

theorem tendsto_shortEndpoint : Tendsto Aε (𝓝[>] (0 : ℝ)) atTop := by
  have ht : Tendsto (fun ε : ℝ ↦ log ε⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  change Tendsto (fun ε : ℝ ↦ log (1 / ε)) (𝓝[>] (0 : ℝ)) atTop
  simpa only [one_div] using ht

/-- The short-shell contribution `∫_{a₀}^{A} w_s(a) a sinh ((1 + ε/4) a) da` to `log α_ε`. -/
def shortShellRadiusContribution (ε : ℝ) : ℝ := ∫ a in a₀ε ε..Aε ε, shortShellRadiusIntegrand ε a

/-- The same integrand extended by zero to `(0, ∞)`, for dominated convergence. -/
def supportedShortShellRadiusIntegrand (ε a : ℝ) : ℝ :=
  (Set.Ioc (a₀ε ε) (Aε ε)).indicator (shortShellRadiusIntegrand ε) a

theorem tendsto_supportedShortShellRadiusIntegrand {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε : ℝ ↦ supportedShortShellRadiusIntegrand ε a) (𝓝[>] (0 : ℝ))
      (𝓝 (wallisRadiusIntegrand a)) := by
  refine (tendsto_shortShellRadiusIntegrand ha).congr' ?_
  filter_upwards [tendsto_shortCutoff.eventually (Iio_mem_nhds ha),
    tendsto_shortEndpoint.eventually_ge_atTop a] with ε hlower hupper
  simp [supportedShortShellRadiusIntegrand,
    Set.indicator_of_mem (show a ∈ Set.Ioc (a₀ε ε) (Aε ε) from ⟨hlower, hupper⟩)]

theorem tendsto_supportedShortShellRadiusIntegral :
    Tendsto (fun ε : ℝ ↦ ∫ a in Set.Ioi (0 : ℝ), supportedShortShellRadiusIntegrand ε a)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ a in Set.Ioi (0 : ℝ), wallisRadiusIntegrand a)) := by
  refine tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    shortShellRadiusMajorant (Eventually.of_forall fun ε ↦
      ((shortShellRadiusIntegrand_measurable ε).indicator measurableSet_Ioc).aestronglyMeasurable)
    ?_ shortShellRadiusMajorant_integrable ?_
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with ε hε hsmall
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    unfold supportedShortShellRadiusIntegrand shortShellRadiusMajorant
    by_cases hmem : a ∈ Set.Ioc (a₀ε ε) (Aε ε)
    · rw [Set.indicator_of_mem hmem, Real.norm_eq_abs]
      exact shortShellRadiusIntegrand_abs_le hε.le hsmall.le ha
    · rw [Set.indicator_of_notMem hmem, norm_zero]
      positivity
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    exact tendsto_supportedShortShellRadiusIntegrand ha

theorem shortShellRadiusContribution_eq_supported {ε : ℝ} (hε : 0 < ε) (horder : a₀ε ε ≤ Aε ε) :
    shortShellRadiusContribution ε =
      ∫ a in Set.Ioi (0 : ℝ), supportedShortShellRadiusIntegrand ε a := by
  have hsubset : Set.Ioc (a₀ε ε) (Aε ε) ⊆ Set.Ioi (0 : ℝ) := fun a ha ↦
    lt_of_le_of_lt (by unfold a₀ε; positivity) ha.1
  unfold shortShellRadiusContribution supportedShortShellRadiusIntegrand
  rw [intervalIntegral.integral_of_le horder, MeasureTheory.integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict_of_subset hsubset]

theorem tendsto_shortShellRadiusContribution :
    Tendsto shortShellRadiusContribution (𝓝[>] (0 : ℝ))
      (𝓝 (∫ a in Set.Ioi (0 : ℝ), wallisRadiusIntegrand a)) := by
  refine tendsto_supportedShortShellRadiusIntegral.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    tendsto_shortCutoff.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    tendsto_shortEndpoint.eventually_ge_atTop (1 : ℝ)] with ε hε hcutoff hendpoint
  exact (shortShellRadiusContribution_eq_supported hε (hcutoff.le.trans hendpoint)).symm

theorem wallisRadiusIntegrand_eq_laplace (a : ℝ) :
    wallisRadiusIntegrand a = -Real.Wallis.laplaceKernel (2 * a) := by
  by_cases ha : a = 0
  · simp [wallisRadiusIntegrand, Real.Wallis.laplaceKernel, ha]
  have hexp : exp (-2 * a) = exp (-a) / exp a := by
    rw [← Real.exp_sub]
    congr 1
    ring
  unfold wallisRadiusIntegrand Real.Wallis.laplaceKernel
  rw [Real.tanh_eq a, show -(2 * a) = -2 * a by ring, hexp]
  field_simp [ha, (exp_pos a).ne', (by positivity : exp a + exp (-a) ≠ 0),
    (by positivity : 1 + exp (-a) / exp a ≠ 0)]

/-- Report (33): the limiting short-shell contribution is `-(1/2) log (π / 2)`. -/
theorem integral_wallisRadiusIntegrand :
    (∫ a in Set.Ioi (0 : ℝ), wallisRadiusIntegrand a) = -(1 / 2 : ℝ) * log (π / 2) := by
  have hscale : (∫ a in Set.Ioi (0 : ℝ), Real.Wallis.laplaceKernel (2 * a)) =
      (2 : ℝ)⁻¹ * log (π / 2) := by
    simpa [smul_eq_mul, Real.Wallis.integral_laplaceKernel] using
      integral_comp_mul_left_Ioi Real.Wallis.laplaceKernel 0 (by norm_num : (0 : ℝ) < 2)
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun a _ ↦ wallisRadiusIntegrand_eq_laplace a), integral_neg, hscale]
  ring

/-- The saddle radius `α_ε = √((2 + ε/4) / (4π)) · exp (shell contributions)`, report (32). -/
def α_ε (ε : ℝ) : ℝ :=
  √((2 + ε / 4) / (4 * π)) *
    exp (shortShellRadiusContribution ε + positiveShellRadiusContribution ε)

theorem tendsto_limitingSaddleRadius_wallisIntegral : Tendsto α_ε (𝓝[>] (0 : ℝ))
    (𝓝 (√(1 / (2 * π)) * exp (∫ a in Set.Ioi (0 : ℝ), wallisRadiusIntegrand a))) := by
  have hε : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hratio : Tendsto (fun ε : ℝ ↦ (2 + ε / 4) / (4 * π)) (𝓝[>] (0 : ℝ)) (𝓝 (1 / (2 * π))) := by
    have hvalue : (2 : ℝ) / (4 * π) = 1 / (2 * π) := by
      field_simp [Real.pi_ne_zero]
      norm_num
    simpa only [zero_div, add_zero, hvalue] using
      ((tendsto_const_nhds (x := (2 : ℝ))).add (hε.div_const 4)).div_const (4 * π)
  have hshell : Tendsto (fun ε : ℝ ↦ shortShellRadiusContribution ε +
      positiveShellRadiusContribution ε) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ a in Set.Ioi (0 : ℝ), wallisRadiusIntegrand a)) := by
    simpa using tendsto_shortShellRadiusContribution.add tendsto_positiveShellRadiusContribution
  exact (Real.continuous_sqrt.continuousAt.tendsto.comp hratio).mul hshell.rexp

theorem saddleRadius_wallis_constant :
    √(1 / (2 * π)) * exp (-(1 / 2 : ℝ) * log (π / 2)) = criticalRadius := by
  have hexpsq : exp (-(1 / 2 : ℝ) * log (π / 2)) ^ 2 = (π / 2)⁻¹ := by
    rw [sq, ← Real.exp_add, show -(1 / 2 : ℝ) * log (π / 2) + -(1 / 2 : ℝ) * log (π / 2) =
      -log (π / 2) by ring, Real.exp_neg, Real.exp_log (by positivity)]
  have hsquare : (√(1 / (2 * π)) * exp (-(1 / 2 : ℝ) * log (π / 2))) ^ 2 = (π⁻¹) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), hexpsq]
    field_simp [Real.pi_ne_zero]
  have hleft : 0 ≤ √(1 / (2 * π)) * exp (-(1 / 2 : ℝ) * log (π / 2)) := by positivity
  have hright : 0 ≤ π⁻¹ := (inv_pos.mpr Real.pi_pos).le
  unfold criticalRadius
  nlinarith

/-- Report (32)–(33): the saddle radius tends to the critical radius `1 / π` as `ε → 0⁺`. -/
theorem tendsto_limitingSaddleRadius : Tendsto α_ε (𝓝[>] (0 : ℝ)) (𝓝 criticalRadius) := by
  simpa only [integral_wallisRadiusIntegrand, saddleRadius_wallis_constant] using
    tendsto_limitingSaddleRadius_wallisIntegral

end

end CohnElkies
