import CohnElkiesForMathlib.Analysis.Complex.Subharmonic.Defs

/-!
# Subharmonic functions in the complex plane

This file develops the theory of the subharmonic functions `SubharmonicOn u U` of
`CohnElkiesForMathlib.Analysis.Complex.Subharmonic.Defs`: `u : ℂ → EReal` is upper semicontinuous
on `U`, never takes the value `⊤` on `U`, and satisfies the local sub-mean-value inequality
`u z ≤ ⨍ u` over all sufficiently small circles around every `z ∈ U`, where the circle average is
understood through the truncations `EReal.truncateToReal a ∘ u`, `a : ℝ`.

## Main results

* `HarmonicOnNhd.subharmonicOn`: harmonic functions are subharmonic;
* `SubharmonicOn.add_harmonic`: the sum of a subharmonic and a harmonic function is subharmonic;
* `AnalyticOnNhd.subharmonicOn_log_norm`: `log ‖f‖` is subharmonic for `f` analytic (via Jensen's
  formula);
* `SubharmonicOn.eqOn_const_of_isMaxOn`: the strong maximum principle;
* `SubharmonicOn.le_zero_of_limsup_frontier`: the weak maximum principle on a bounded open
  preconnected set, with the boundary condition `limsup u (𝓝[Ω] ζ) ≤ 0` at every boundary point.
-/

open Filter InnerProductSpace MeasureTheory Metric Real Set Topology

namespace SubharmonicOn

variable {u : ℂ → EReal} {U : Set ℂ}

/-!
### Harmonic functions
-/

/-- A real harmonic function on `U` (coerced to `EReal`) is subharmonic on `U`: by the mean value
property, `h z = ⨍ h ≤ ⨍ max h a` over small circles around `z`. -/
theorem _root_.InnerProductSpace.HarmonicOnNhd.subharmonicOn {h : ℂ → ℝ}
    (hh : HarmonicOnNhd h U) : SubharmonicOn (fun z ↦ (h z : EReal)) U where
  upperSemicontinuousOn :=
    (continuous_coe_real_ereal.comp_continuousOn hh.continuousOn).upperSemicontinuousOn
  ne_top z _ := EReal.coe_ne_top _
  le_circleAverage z hz := by
    filter_upwards [(eventually_closedBall_subset (hh z hz).eventually).filter_mono
      nhdsWithin_le_nhds, self_mem_nhdsWithin] with r hr hr0 a
    have hball : HarmonicOnNhd h (closedBall z |r|) := by rwa [abs_of_pos hr0]
    have hcont : ContinuousOn h (sphere z |r|) := hball.continuousOn.mono sphere_subset_closedBall
    simp only [EReal.truncateToReal_coe, EReal.coe_le_coe_iff, ← hball.circleAverage_eq]
    exact circleAverage_mono hcont.circleIntegrable'
      (hcont.sup continuousOn_const).circleIntegrable' fun w _ ↦ le_max_left _ _

/-- Constant real functions are subharmonic. -/
theorem _root_.subharmonicOn_const (c : ℝ) : SubharmonicOn (fun _ ↦ (c : EReal)) U :=
  (harmonicOnNhd_const c).subharmonicOn

/-- The sum of a subharmonic function on an open set `U` and a real harmonic function on `U` is
subharmonic on `U`. Upper semicontinuity of the sum uses the continuity of the addition of
`EReal` away from `(⊤, ⊥)`; for the sub-mean-value inequality, if `|h| ≤ H` on a small circle,
then `truncateToReal (a - H) u + h ≤ truncateToReal a (u + h)` on it, so the mean value property
of `h` gives `u z + h z ≤ ⨍ truncateToReal (a - H) u + ⨍ h ≤ ⨍ truncateToReal a (u + h)`. -/
theorem add_harmonic (hU : IsOpen U) (hu : SubharmonicOn u U) {h : ℂ → ℝ}
    (hh : HarmonicOnNhd h U) : SubharmonicOn (fun z ↦ u z + (h z : EReal)) U := by
  have husc : UpperSemicontinuousOn (fun z ↦ u z + (h z : EReal)) U :=
    hu.upperSemicontinuousOn.add'
      (continuous_coe_real_ereal.comp_continuousOn hh.continuousOn).upperSemicontinuousOn
      fun z hz ↦ EReal.continuousAt_add (Or.inl (hu.ne_top z hz)) (Or.inr (EReal.coe_ne_top _))
  have hne : ∀ z ∈ U, u z + (h z : EReal) ≠ ⊤ := fun z hz ↦
    EReal.add_ne_top (hu.ne_top z hz) (EReal.coe_ne_top _)
  refine ⟨husc, hne, fun z hz ↦ ?_⟩
  filter_upwards [hu.eventually_closedBall_subset_and_le_circleAverage hU hz,
    self_mem_nhdsWithin] with r ⟨hcb, hsub⟩ hr a
  have hcb' : closedBall z |r| ⊆ U := by rwa [abs_of_pos hr]
  have hsph : sphere z |r| ⊆ U := sphere_subset_closedBall.trans hcb'
  obtain ⟨H, hH⟩ :=
    (isCompact_sphere z |r|).exists_bound_of_continuousOn (hh.continuousOn.mono hsph)
  have hT₁ := hu.circleIntegrable_truncateToReal hsph (a - H)
  have hhI : CircleIntegrable h z r := (hh.continuousOn.mono hsph).circleIntegrable'
  have hpt (w : ℂ) (hw : w ∈ sphere z |r|) :
      EReal.truncateToReal (a - H) (u w) + h w ≤ EReal.truncateToReal a (u w + h w) := by
    rw [EReal.truncateToReal_add_coe _ _ (hu.ne_top w (hsph hw))]
    exact add_le_add (EReal.truncateToReal_le_truncateToReal_of_le
      (sub_le_sub_left ((le_abs_self _).trans (hH w hw)) a) (hu.ne_top w (hsph hw))) le_rfl
  refine (add_le_add (hsub (a - H)) le_rfl).trans ?_
  rw [← (hh.mono hcb').circleAverage_eq, ← EReal.coe_add, ← circleAverage_fun_add hT₁ hhI]
  exact EReal.coe_le_coe_iff.2
    (circleAverage_mono (hT₁.add hhI) (husc.circleIntegrable_truncateToReal hne hsph a) hpt)

/-- The difference of a subharmonic function on an open set `U` and a real harmonic function on
`U` is subharmonic on `U`. -/
theorem sub_harmonic (hU : IsOpen U) (hu : SubharmonicOn u U) {h : ℂ → ℝ}
    (hh : HarmonicOnNhd h U) : SubharmonicOn (fun z ↦ u z - (h z : EReal)) U := by
  simpa [sub_eq_add_neg, EReal.coe_neg] using hu.add_harmonic hU hh.neg

/-- Adding a real constant to a subharmonic function on an open set preserves subharmonicity. -/
theorem add_const (hU : IsOpen U) (hu : SubharmonicOn u U) (c : ℝ) :
    SubharmonicOn (fun z ↦ u z + (c : EReal)) U :=
  hu.add_harmonic hU (harmonicOnNhd_const c)

/-- Adding a real constant to a subharmonic function on an open set preserves subharmonicity. -/
theorem const_add (hU : IsOpen U) (hu : SubharmonicOn u U) (c : ℝ) :
    SubharmonicOn (fun z ↦ (c : EReal) + u z) U := by
  simpa [add_comm] using hu.add_const hU c

/-- Subtracting a real constant from a subharmonic function on an open set preserves
subharmonicity. -/
theorem sub_const (hU : IsOpen U) (hu : SubharmonicOn u U) (c : ℝ) :
    SubharmonicOn (fun z ↦ u z - (c : EReal)) U :=
  hu.sub_harmonic hU (harmonicOnNhd_const c)

/-!
### The logarithm of the modulus of an analytic function
-/

/-- **`log ‖f‖` is subharmonic**: for `f : ℂ → ℂ` analytic on the open set `U`, the function
`ENNReal.log ‖f ·‖ₑ` (which is `log ‖f z‖` where `f z ≠ 0` and `⊥` at the zeros of `f`) is
subharmonic on `U`. Upper semicontinuity is the continuity of `ENNReal.log`; the sub-mean-value
inequality at a point `z` with `f z ≠ 0` is Jensen's formula, in which the contribution of the
zeros of `f` in the closed disc is nonnegative, together with the fact that `log ‖f ·‖` and the
truncation of `ENNReal.log ‖f ·‖ₑ` differ only on the discrete zero set of `f`. -/
theorem _root_.AnalyticOnNhd.subharmonicOn_log_enorm {f : ℂ → ℂ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) : SubharmonicOn (fun z ↦ ENNReal.log ‖f z‖ₑ) U := by
  have husc : UpperSemicontinuousOn (fun z ↦ ENNReal.log ‖f z‖ₑ) U :=
    (ENNReal.continuous_log.comp_continuousOn
      (continuous_enorm.comp_continuousOn hf.continuousOn)).upperSemicontinuousOn
  have hne : ∀ z ∈ U, ENNReal.log ‖f z‖ₑ ≠ ⊤ := fun z _ ↦
    ENNReal.log_eq_top_iff.not.2 enorm_ne_top
  refine ⟨husc, hne, fun z hz ↦ ?_⟩
  filter_upwards [(eventually_closedBall_subset (hU.mem_nhds hz)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with r hcb (hr : 0 < r) a
  by_cases hfz : f z = 0
  · simp [hfz]
  rw [← abs_of_pos hr] at hcb
  have hfr : AnalyticOnNhd ℂ f (closedBall z |r|) := hf.mono hcb
  have hsph : sphere z |r| ⊆ U := sphere_subset_closedBall.trans hcb
  -- Jensen's formula: `log ‖f z‖ ≤ ⨍ log ‖f ·‖`, as the divisor term is nonnegative
  have hjensen : Real.log ‖f z‖ ≤ circleAverage (fun w ↦ Real.log ‖f w‖) z r := by
    rw [hfr.circleAverage_log_norm hr.ne' hfz]
    refine le_add_of_nonneg_left (finsum_nonneg fun w ↦ ?_)
    by_cases hw : w ∈ closedBall z |r|
    · refine mul_nonneg (mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfr w) ?_
      rcases eq_or_ne w z with rfl | hwz
      · simp
      · rw [mem_closedBall, dist_eq_norm', abs_of_pos hr] at hw
        exact Real.log_nonneg ((one_le_div (norm_pos_iff.2 (sub_ne_zero.2 hwz.symm))).2 hw)
    · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hw]
  -- the truncation of `ENNReal.log ‖f ·‖ₑ` agrees with `max (log ‖f ·‖) a` off the zeros of `f`
  have hcod : (fun w ↦ EReal.truncateToReal a (ENNReal.log ‖f w‖ₑ))
      =ᶠ[codiscreteWithin (sphere z |r|)] fun w ↦ max (Real.log ‖f w‖) a := by
    filter_upwards [codiscreteWithin_mono sphere_subset_closedBall
      (hfr.preimage_zero_mem_codiscreteWithin hfz (mem_closedBall_self (abs_nonneg r))
        ⟨nonempty_closedBall.2 (abs_nonneg r), (convex_closedBall z |r|).isPreconnected⟩)] with w hw
    rw [← ofReal_norm, ENNReal.log_ofReal_of_pos (norm_pos_iff.2 hw), EReal.truncateToReal_coe]
  rw [← ofReal_norm, ENNReal.log_ofReal_of_pos (norm_pos_iff.2 hfz),
    circleAverage_congr_codiscreteWithin hcod hr.ne', EReal.coe_le_coe_iff]
  exact hjensen.trans (circleAverage_mono
    (hfr.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
    ((husc.circleIntegrable_truncateToReal hne hsph a).congr_codiscreteWithin hcod)
    fun w _ ↦ le_max_left _ _)

/-- **`log ‖f‖` is subharmonic**: for `f : ℂ → ℂ` analytic on the open set `U`, the function
`log ‖f ·‖` extended by `⊥ = -∞` at the zeros of `f` is subharmonic on `U`. -/
theorem _root_.AnalyticOnNhd.subharmonicOn_log_norm {f : ℂ → ℂ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) :
    SubharmonicOn (fun z ↦ if f z = 0 then ⊥ else ((Real.log ‖f z‖ : ℝ) : EReal)) U := by
  convert hf.subharmonicOn_log_enorm hU using 2 with z
  rw [← ofReal_norm, ENNReal.log_ofReal]
  simp

end SubharmonicOn

/-!
### The maximum principle
-/

/-- For any function `u` and any set `s`, the function `x ↦ limsup u (𝓝[s] x)` (the upper
semicontinuous regularization of `u` relative to `s`) is upper semicontinuous. -/
theorem upperSemicontinuous_limsup_nhdsWithin {α β : Type*} [TopologicalSpace α]
    [CompleteLinearOrder β] [DenselyOrdered β] (u : α → β) (s : Set α) :
    UpperSemicontinuous fun x ↦ limsup u (𝓝[s] x) := by
  intro x y hy
  obtain ⟨y', hy'₁, hy'₂⟩ := exists_between hy
  filter_upwards [eventually_nhds_nhdsWithin.2 (eventually_lt_of_limsup_lt hy'₁)] with w hw
  exact (limsup_le_of_le (by isBoundedDefault) (hw.mono fun _ ↦ le_of_lt)).trans_lt hy'₂

/-- At a point `x ∈ s`, the upper semicontinuous regularization `limsup u (𝓝[s] x)` of a function
`u` that is upper semicontinuous on `s` is `u x`. -/
theorem UpperSemicontinuousOn.limsup_nhdsWithin_eq {α β : Type*} [TopologicalSpace α]
    [CompleteLinearOrder β] {u : α → β} {s : Set α} (hu : UpperSemicontinuousOn u s) {x : α}
    (hx : x ∈ s) : limsup u (𝓝[s] x) = u x :=
  le_antisymm (hu.limsup_le x hx) <| le_limsup_of_frequently_le <|
    Frequently.filter_mono (frequently_pure.2 le_rfl) (pure_le_nhdsWithin hx)

namespace SubharmonicOn

variable {u : ℂ → EReal} {U : Set ℂ}

/-- If a subharmonic function on an open set `U` is bounded by a real number `M` on `U` and
attains the value `M` at `z ∈ U`, then it is equal to `M` in a neighbourhood of `z`.

Proof: otherwise there is `w` arbitrarily close to `z` with `u w < M`; by upper semicontinuity
`u < M` on a neighbourhood of `w`. The circle around `z` through `w` lies in `U`, and the
truncation `T = truncateToReal (M - 1) ∘ u` satisfies `T ≤ M` on it and `T < M` on the nonempty
open arc inside that neighbourhood, so `⨍ T < M = u z`, contradicting the sub-mean-value
inequality. -/
theorem eventually_eq_of_isMaxOn (hU : IsOpen U) (hu : SubharmonicOn u U) {z : ℂ} (hz : z ∈ U)
    {M : ℝ} (hM : ∀ w ∈ U, u w ≤ M) (hzM : u z = M) : ∀ᶠ w in 𝓝 z, u w = M := by
  obtain ⟨r₀, hr₀, hr₀'⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.1
    (hu.eventually_closedBall_subset_and_le_circleAverage hU hz)
  filter_upwards [ball_mem_nhds z hr₀] with w hw
  by_cases hwz : w = z
  · rw [hwz, hzM]
  -- the circle of radius `r = dist w z` around `z` passes through `w` and lies in `U`
  obtain ⟨hcb, hsub⟩ := hr₀' ⟨dist_pos.2 hwz, hw⟩
  have hrabs : |dist w z| = dist w z := abs_of_nonneg dist_nonneg
  have hsph : sphere z |dist w z| ⊆ U := by rw [hrabs]; exact sphere_subset_closedBall.trans hcb
  have hwU : w ∈ U := hcb (mem_closedBall.2 le_rfl)
  obtain ⟨θ₀, hθ₀⟩ : w ∈ range (circleMap z (dist w z)) := by
    rw [range_circleMap, hrabs]; exact mem_sphere.2 rfl
  by_contra hne
  -- by upper semicontinuity, `u < M` in a neighbourhood of `w`
  have hev : ∀ᶠ w' in 𝓝 w, u w' < M :=
    (hu.upperSemicontinuousOn w hwU (M : EReal) (lt_of_le_of_ne (hM w hwU) hne)).filter_mono
      (nhdsWithin_eq_nhds.2 (hU.mem_nhds hwU)).ge
  -- the sub-mean-value inequality at level `M - 1` for the truncation `T` gives `2π M ≤ ∫ T` over
  -- the period `[θ₀ - π, θ₀ + π]` around the angle `θ₀` of `w`
  set T : ℂ → ℝ := fun w' ↦ EReal.truncateToReal (M - 1) (u w')
  have hper : Function.Periodic (fun θ ↦ T (circleMap z (dist w z) θ)) (2 * π) :=
    (periodic_circleMap z (dist w z)).comp T
  have h₁ := hsub (M - 1)
  rw [hzM, EReal.coe_le_coe_iff, circleAverage_def, smul_eq_mul, le_inv_mul_iff₀ two_pi_pos,
    ← zero_add (2 * π), hper.intervalIntegral_add_eq 0 (θ₀ - π), zero_add] at h₁
  -- but `∫ T < 2π M`, as `T ≤ M` on the circle and `T < M` on a neighbourhood of `θ₀`
  refine h₁.not_gt ((intervalIntegral.integral_lt_integral_of_ae_le_of_measure_setOfPred_lt_ne_zero
    (by linarith [pi_pos]) (hper.intervalIntegrable₀ two_pi_pos.ne'
      (hu.circleIntegrable_truncateToReal hsph (M - 1)) _ _) intervalIntegrable_const
    (ae_of_all _ fun θ ↦ EReal.truncateToReal_le_of_le
      (hM _ (hsph (circleMap_mem_sphere' z _ θ))) (by linarith)) ?_).trans_eq (by simp))
  rw [Measure.restrict_apply' measurableSet_Ioc]
  refine (Measure.measure_pos_of_mem_nhds volume (x := θ₀) (Filter.inter_mem ?_
    (Ioc_mem_nhds (by linarith [pi_pos]) (by linarith [pi_pos])))).ne'
  exact (((continuous_circleMap z _).tendsto θ₀).eventually (hθ₀ ▸ hev)).mono fun θ hθ ↦
    EReal.truncateToReal_lt_of_lt hθ (by linarith)

/-- **Strong maximum principle**: a subharmonic function on an open preconnected set `Ω` that
attains its supremum over `Ω` at a point `z₀ ∈ Ω` is constant on `Ω`. -/
theorem eqOn_const_of_isMaxOn {Ω : Set ℂ} (hΩ : IsOpen Ω) (hc : IsPreconnected Ω)
    (hu : SubharmonicOn u Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (hmax : IsMaxOn u Ω z₀) :
    EqOn u (fun _ ↦ u z₀) Ω := by
  -- if the maximum is `⊥`, then `u = ⊥` on `Ω`
  rcases eq_or_ne (u z₀) ⊥ with hbot | hbot
  · exact fun z hz ↦ (le_bot_iff.1 ((hmax hz).trans_eq hbot)).trans hbot.symm
  -- otherwise the maximum is a real number `M`
  obtain ⟨M, hM⟩ : ∃ M : ℝ, u z₀ = M :=
    ⟨(u z₀).toReal, (EReal.coe_toReal (hu.ne_top z₀ hz₀) hbot).symm⟩
  have hle : ∀ w ∈ Ω, u w ≤ M := fun w hw ↦ hM ▸ hmax hw
  -- the set where `u = M` is open, closed in `Ω` (upper semicontinuity), and nonempty
  have hopen : IsOpen {z | z ∈ Ω ∧ u z = M} := isOpen_iff_mem_nhds.2 fun z ⟨hzΩ, hzM⟩ ↦
    Filter.inter_mem (hΩ.mem_nhds hzΩ) (hu.eventually_eq_of_isMaxOn hΩ hzΩ hle hzM)
  refine fun z hz ↦ ((hc.subset_of_closure_inter_subset hopen ⟨z₀, hz₀, hz₀, hM⟩
    fun x ⟨hxcl, hxΩ⟩ ↦ ⟨hxΩ, le_antisymm (hle x hxΩ) ?_⟩) hz).2.trans hM.symm
  exact UpperSemicontinuousWithinAt.frequently (hu.upperSemicontinuousOn x hxΩ) (M : EReal)
    (frequently_nhdsWithin_iff.2
      ((mem_closure_iff_frequently.1 hxcl).mono fun y ⟨hyΩ, hyM⟩ ↦ ⟨hyM.ge, hyΩ⟩))

/-- **Weak maximum principle** for subharmonic functions: if `u` is subharmonic on a bounded open
preconnected set `Ω ⊆ ℂ` and `limsup u (𝓝[Ω] ζ) ≤ 0` at every boundary point `ζ` of `Ω`, then
`u ≤ 0` on `Ω`.

Proof: the function `ζ ↦ limsup u (𝓝[Ω] ζ)` is upper semicontinuous, agrees with `u` on `Ω`, and
attains its maximum on the compact set `closure Ω`. If `u` were positive somewhere, this maximum
would be positive, hence attained at a point of `Ω` rather than of `frontier Ω`; by the strong
maximum principle `u` would be a positive constant on `Ω`, contradicting the boundary condition
at a point of the (nonempty) frontier of `Ω`. -/
theorem le_zero_of_limsup_frontier {Ω : Set ℂ} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hc : IsPreconnected Ω) (hu : SubharmonicOn u Ω)
    (hfr : ∀ ζ ∈ frontier Ω, limsup u (𝓝[Ω] ζ) ≤ 0) : ∀ z ∈ Ω, u z ≤ 0 := by
  intro z₁ hz₁
  by_contra! hz₁pos
  set g : ℂ → EReal := fun ζ ↦ limsup u (𝓝[Ω] ζ)
  have hgu : ∀ z ∈ Ω, g z = u z := fun z hz ↦ hu.upperSemicontinuousOn.limsup_nhdsWithin_eq hz
  -- the maximum of `g` on `closure Ω` is positive, hence attained in `Ω`
  obtain ⟨ζ₀, hζ₀, hmax⟩ :=
    ((upperSemicontinuous_limsup_nhdsWithin u Ω).upperSemicontinuousOn _).exists_isMaxOn
      ⟨z₁, subset_closure hz₁⟩ hb.isCompact_closure
  have hζ₀pos : 0 < g ζ₀ := hz₁pos.trans_le ((hgu z₁ hz₁).ge.trans (hmax (subset_closure hz₁)))
  have hζ₀Ω : ζ₀ ∈ Ω :=
    not_not.1 fun h ↦ (hfr ζ₀ ⟨hζ₀, hΩ.interior_eq.symm ▸ h⟩).not_gt hζ₀pos
  -- `u` attains its maximum over `Ω` at `ζ₀`, hence is constant on `Ω`
  have hmaxΩ : IsMaxOn u Ω ζ₀ := isMaxOn_iff.2 fun z hz ↦
    (hgu z hz).ge.trans ((hmax (subset_closure hz)).trans (hgu ζ₀ hζ₀Ω).le)
  -- contradiction with the boundary condition at a point of the frontier
  obtain ⟨ζ, hζ⟩ := nonempty_frontier_iff.2
    ⟨⟨z₁, hz₁⟩, fun h ↦ NormedSpace.unbounded_univ ℂ ℂ (h ▸ hb)⟩
  have hne : (𝓝[Ω] ζ).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (frontier_subset_closure hζ)
  have hlim : limsup u (𝓝[Ω] ζ) = u ζ₀ := by
    rw [limsup_congr (eventually_nhdsWithin_of_forall fun z hz ↦
      hu.eqOn_const_of_isMaxOn hΩ hc hζ₀Ω hmaxΩ hz), limsup_const]
  exact (hlim ▸ hfr ζ hζ).not_gt (hgu ζ₀ hζ₀Ω ▸ hζ₀pos)

end SubharmonicOn
