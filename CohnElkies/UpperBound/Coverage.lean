import CohnElkies.UpperBound.SmallRadius
import CohnElkiesForMathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Every large radius is a saddle radius (report §4.3, Corollary 4.9)

Differentiating the shell contribution to `log r(u)`, the continuity and eventual monotonicity of
the log-radius `u ↦ log r(u)` on `u ≥ u_*`, hence its coverage of every radius `≥ r_*`
(`eventually_saddleLogRadius_covers_Ici`), and the location of `r_*` relative to `R_{ε,d}`.
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory Real Set
open scoped Topology BigOperators

/-! ### Differentiating the shell contribution to `log R` -/

/-- Differentiation under the integral sign for `v ↦ ∫ w(x) x sinh(xv)`. -/
theorem sinhShellInterval_hasDerivAt (w : ℝ → ℝ) (hw : Continuous w) {a b : ℝ} (hab : a ≤ b)
    (u : ℝ) :
    HasDerivAt (fun v : ℝ ↦ ∫ x in a..b, w x * x * sinh (x * v))
      (∫ x in a..b, w x * x ^ 2 * cosh (x * u)) u := by
  let F : ℝ → ℝ → ℝ := fun v x ↦ w x * x * sinh (x * v)
  let F' : ℝ → ℝ → ℝ := fun v x ↦ w x * x ^ 2 * cosh (x * v)
  have hF (v : ℝ) : Continuous (F v) :=
    (hw.mul continuous_id).mul (Real.continuous_sinh.comp (continuous_id.mul continuous_const))
  have hF' (v : ℝ) : Continuous (F' v) :=
    (hw.mul (continuous_id.pow 2)).mul
      (Real.continuous_cosh.comp (continuous_id.mul continuous_const))
  have hF'joint : Continuous (Function.uncurry F') :=
    ((hw.comp continuous_snd).mul (continuous_snd.pow 2)).mul
      (Real.continuous_cosh.comp (continuous_snd.mul continuous_fst))
  have hderiv (x v : ℝ) : HasDerivAt (fun z : ℝ ↦ F z x) (F' v x) v := by
    have hlinear : HasDerivAt (fun z : ℝ ↦ x * z) x v := by
      simpa using (hasDerivAt_id v).const_mul x
    simpa [F, F', pow_two, mul_assoc, mul_left_comm, mul_comm] using
      ((Real.hasDerivAt_sinh (x * v)).comp v hlinear).const_mul (w x * x)
  have hrewrite : (fun v : ℝ ↦ ∫ x in a..b, w x * x * sinh (x * v)) =
      fun v : ℝ ↦ ∫ x in Icc a b, F v x := by
    funext v
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  have hderivrewrite : (∫ x in a..b, w x * x ^ 2 * cosh (x * u)) = ∫ x in Icc a b, F' u x := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  rw [hrewrite, hderivrewrite]
  obtain ⟨C, hC⟩ := ((isCompact_closedBall u 1).prod (isCompact_Icc (a := a) (b := b)))
    |>.bddAbove_image hF'joint.norm.continuousOn
  have hbound : ∀ᵐ x ∂volume.restrict (Icc a b), ∀ v ∈ Metric.ball u 1, ‖F' v x‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx v hv
    have hpair : (v, x) ∈ Metric.closedBall u 1 ×ˢ Icc a b :=
      ⟨Metric.ball_subset_closedBall hv, hx⟩
    exact hC (mem_image_of_mem (fun p : ℝ × ℝ ↦ ‖F' p.1 p.2‖) hpair)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Icc a b))
    (s := Metric.ball u 1) (bound := fun _ : ℝ ↦ C) (Metric.ball_mem_nhds u zero_lt_one)
    (Eventually.of_forall fun v ↦ (hF v).aestronglyMeasurable) (hF u).integrableOn_Icc
    (hF' u).aestronglyMeasurable hbound (integrableOn_const isCompact_Icc.measure_ne_top)
    (Eventually.of_forall fun x v _ ↦ hderiv x v)).2

theorem saddleSourceShellDerivative_hasDerivAt {ε : ℝ} (hε : 0 < ε) (horder : a₀ε ε ≤ Aε ε)
    (u : ℝ) :
    HasDerivAt (saddleSourceShellDerivative ε) (upperNetShellVariance ε (u - 1)) u := by
  have hcutoff : 0 < a₀ε ε := by unfold a₀ε; positivity
  have hmax (a : ℝ) : 0 < max a (a₀ε ε) := hcutoff.trans_le (le_max_right _ _)
  have hw : Continuous fun a : ℝ ↦ w_s ε (max a (a₀ε ε)) := by
    have hn : Continuous fun a : ℝ ↦ bε ε (max a (a₀ε ε)) * exp (-2 * max a (a₀ε ε)) := by
      unfold bε; fun_prop
    have hd : Continuous fun a : ℝ ↦ 2 * max a (a₀ε ε) ^ 2 * cosh (max a (a₀ε ε)) := by fun_prop
    unfold w_s
    exact (hn.div hd fun a ↦ by positivity [hmax a]).neg
  have hshort : HasDerivAt (fun v : ℝ ↦ ∫ a in a₀ε ε..Aε ε, w_s ε a * a * sinh (v * a))
      (∫ a in a₀ε ε..Aε ε, w_s ε a * a ^ 2 * cosh (u * a)) u := by
    convert! sinhShellInterval_hasDerivAt _ hw horder u using 1
    · funext v
      refine intervalIntegral.integral_congr fun a ha ↦ ?_
      rw [uIcc_of_le horder] at ha
      rw [max_eq_left ha.1]
      ring_nf
    · refine intervalIntegral.integral_congr fun a ha ↦ ?_
      rw [uIcc_of_le horder] at ha
      rw [max_eq_left ha.1]
      ring_nf
  have hpositive : HasDerivAt (fun v : ℝ ↦ ∫ a in Bε ε..Bε ε + 1, w_B ε a * a * sinh (v * a))
      (∫ a in Bε ε..Bε ε + 1, w_B ε a * a ^ 2 * cosh (u * a)) u := by
    convert! sinhShellInterval_hasDerivAt (w_B ε) (positiveShellDensity_continuous ε)
      (by linarith : Bε ε ≤ Bε ε + 1) u using 1
    · funext v
      exact intervalIntegral.integral_congr fun a _ ↦ by ring_nf
    · exact intervalIntegral.integral_congr fun a _ ↦ by ring_nf
  have hshortvariance : (∫ a in a₀ε ε..Aε ε, w_s ε a * a ^ 2 * cosh (u * a)) = -V_s ε (u - 1) := by
    unfold V_s
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun a _ ↦ by ring_nf
  have hpositivevariance : (∫ a in Bε ε..Bε ε + 1, w_B ε a * a ^ 2 * cosh (u * a)) =
      V_B ε (u - 1) := by
    unfold V_B
    exact intervalIntegral.integral_congr fun a _ ↦ by ring_nf
  unfold saddleSourceShellDerivative
  convert! hshort.add hpositive using 1
  rw [hshortvariance, hpositivevariance]
  unfold upperNetShellVariance
  ring

theorem eventually_saddleSourceShellDerivative_monotoneOn : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    MonotoneOn (saddleSourceShellDerivative ε) (Ici (1 + ε / 2)) := by
  filter_upwards [self_mem_nhdsWithin, eventually_upper_shortCutoff_le_shortEndpoint,
      eventually_upper_netShellVariance_bounds] with ε hε horder hnet
  change 0 < ε at hε
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (1 + ε / 2))
    (saddleSourceShellDerivative_contDiff_one hε horder).continuous.continuousOn
    fun u _ ↦ (saddleSourceShellDerivative_hasDerivAt hε horder u).hasDerivWithinAt
  intro u hu
  have hthreshold : 1 + ε / 2 ≤ u := interior_subset hu
  have hpositive : 0 ≤ V_B ε (u - 1) :=
    (show 0 ≤ 1 / 2 * Bε ε ^ 2 * Qε ε * exp ((u - 1) * Bε ε) by
      positivity [shellWeight_pos ε]).trans
      (upperPositiveShellVariance_bounds hε (by linarith : (0 : ℝ) ≤ u - 1)).1
  linarith [(hnet (u - 1) (by linarith : ε / 2 ≤ u - 1)).1]

/-! ### Corollary 4.9: `u ↦ log R_{ε,d}(u)` covers every large radius -/

theorem logRadius_continuousOn_Ici {ε : ℝ} (hε : 0 < ε) (horder : a₀ε ε ≤ Aε ε) {d : ℕ}
    (hd : 0 < d) {u₀ : ℝ} (hu₀ : -1 < u₀) : ContinuousOn (logRadius ε d) (Ici u₀) := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hmap : MapsTo (fun u : ℝ ↦ (d : ℝ) / 2 * (1 + u) / 2) (Ici u₀) (Ioi (0 : ℝ)) :=
    fun u hu ↦ by
      have h1 : (0 : ℝ) < 1 + u := by linarith [mem_Ici.1 hu]
      exact mem_Ioi.2 (by positivity)
  have hdigamma : ContinuousOn (fun u : ℝ ↦ Real.digamma ((d : ℝ) / 2 * (1 + u) / 2)) (Ici u₀) :=
    Real.continuousOn_digamma_Ioi.comp (by fun_prop : Continuous fun u : ℝ ↦
      (d : ℝ) / 2 * (1 + u) / 2).continuousOn hmap
  exact ((continuousOn_const.add (hdigamma.div_const 2)).add
    (saddleSourceShellDerivative_contDiff_one hε horder).continuous.continuousOn).congr
    fun u _ ↦ saddleLogRadius_eq_digamma_add_shellDerivative ε d u

/-- Report Corollary 4.9: every radius above `e^{v(u₀)}` is attained by some `u ≥ u₀`. -/
theorem eventually_saddleLogRadius_covers_Ici : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ d : ℕ, 0 < d →
    ∀ u₀ : ℝ, -1 < u₀ → ∀ r : ℝ, exp (logRadius ε d u₀) ≤ r →
      ∃ u : ℝ, u₀ ≤ u ∧ logRadius ε d u = log r := by
  filter_upwards [self_mem_nhdsWithin, eventually_upper_shortCutoff_le_shortEndpoint,
      eventually_saddleSourceShellDerivative_monotoneOn] with ε hε horder hmono
  change 0 < ε at hε
  intro d hd u₀ hu₀ r hr
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hdigamma : Tendsto Real.digamma atTop atTop :=
    (Real.tendsto_log_atTop.atTop_add Real.tendsto_digamma_sub_log_atTop).congr fun x ↦ by ring
  have hargument : Tendsto (fun u : ℝ ↦ (d : ℝ) / 2 * (1 + u) / 2) atTop atTop :=
    ((tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < (d : ℝ) / 4)).atTop_add
      (tendsto_const_nhds (x := (d : ℝ) / 4))).congr fun u ↦ by simp only [id_eq]; ring
  have htop : Tendsto (logRadius ε d) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_
      (((hdigamma.comp hargument).atTop_div_const (by norm_num : (0 : ℝ) < 2)).atTop_add
        (tendsto_const_nhds (x := -log π / 2 + saddleSourceShellDerivative ε (1 + ε / 2))))
    filter_upwards [eventually_ge_atTop (1 + ε / 2)] with u hu
    rw [saddleLogRadius_eq_digamma_add_shellDerivative]
    simp only [Function.comp_apply]
    linarith [hmono (Set.mem_Ici.2 le_rfl) hu hu]
  exact (isPreconnected_Ici.intermediate_value_Ici (Set.mem_Ici.2 le_rfl)
    (Filter.le_principal_iff.mpr (eventually_ge_atTop u₀))
    (logRadius_continuousOn_Ici hε horder hd hu₀) htop)
    (Real.exp_le_exp.mp (by rwa [Real.exp_log ((Real.exp_pos _).trans_le hr)]))

theorem eventually_saddleSmallRadiusStarOrdinate_gt_neg_one (ε : ℝ) :
    ∀ᶠ d : ℕ in atTop, -1 < u_star ε d := by
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with d hd
  have hdreal : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hratio : 0 < log ((d : ℝ) / 2) / (4 * ((d : ℝ) / 2)) :=
    div_pos (Real.log_pos (by linarith)) (by linarith)
  unfold u_star
  linarith

theorem eventually_saddleSmallRadiusStar_log_coverage : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    ∀ᶠ d : ℕ in atTop, ∀ r : ℝ, r_star ε d ≤ r →
      ∃ u : ℝ, u_star ε d ≤ u ∧ logRadius ε d u = log r := by
  filter_upwards [eventually_saddleLogRadius_covers_Ici] with ε hcoverage
  filter_upwards [eventually_saddleSmallRadiusStarOrdinate_gt_neg_one ε,
      eventually_gt_atTop (0 : ℕ)] with d hstar hd r hr
  exact hcoverage d hd (u_star ε d) hstar r hr

theorem eventually_saddleSourceRadius_log_coverage : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ d : ℕ, 0 < d →
    ∀ r : ℝ, R_ε ε d ≤ r → ∃ u : ℝ, 1 + ε / 4 ≤ u ∧ logRadius ε d u = log r := by
  filter_upwards [self_mem_nhdsWithin, eventually_saddleLogRadius_covers_Ici] with ε hε hcoverage
  change 0 < ε at hε
  exact fun d hd r hr ↦ hcoverage d hd (1 + ε / 4) (by linarith) r hr

end

end CohnElkies
