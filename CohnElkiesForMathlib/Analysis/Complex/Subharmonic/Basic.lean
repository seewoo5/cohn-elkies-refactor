import Mathlib

/-!
# Subharmonic functions in the complex plane

A function `u : ℂ → EReal` is *subharmonic* on a set `U ⊆ ℂ` (`SubharmonicOn u U`) if it is upper
semicontinuous on `U`, never takes the value `⊤` on `U`, and satisfies the local sub-mean-value
inequality `u z ≤ ⨍ u` over all sufficiently small circles around every `z ∈ U`. Since `u` may take
the value `⊥ = -∞` (as `log ‖f‖` does at the zeros of an analytic function `f`), the circle average
is understood through the truncations `max u a`, `a : ℝ` (`EReal.truncateToReal`), which are
bounded and measurable on circles: the inequality is required for every level `a`.

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

/-!
### Truncations of extended real numbers
-/

namespace EReal

/-- `EReal.truncateToReal a x = (max x a).toReal` is `x : EReal` truncated from below at the real
level `a`, as a real number: it equals `x` for real `x ≥ a` and `a` for `x ≤ a` (in particular
for `x = ⊥`). The junk value `truncateToReal a ⊤ = 0` is never used, as truncations are only
applied to functions that do not take the value `⊤`. -/
noncomputable def truncateToReal (a : ℝ) (x : EReal) : ℝ := (max x a).toReal

variable {a b t : ℝ} {x y : EReal}

private theorem max_coe_ne_top (hx : x ≠ ⊤) : max x (a : EReal) ≠ ⊤ :=
  (max_lt (lt_top_iff_ne_top.2 hx) (coe_lt_top a)).ne

private theorem max_coe_ne_bot (x : EReal) : max x (a : EReal) ≠ ⊥ :=
  ((bot_lt_coe a).trans_le (le_max_right x a)).ne'

@[simp] theorem truncateToReal_bot (a : ℝ) : truncateToReal a ⊥ = a := by
  simp [truncateToReal]

@[simp] theorem truncateToReal_top (a : ℝ) : truncateToReal a ⊤ = 0 := by
  simp [truncateToReal]

@[simp] theorem truncateToReal_coe (a b : ℝ) : truncateToReal a b = max b a := by
  rw [truncateToReal, ← coe_strictMono.monotone.map_max, toReal_coe]

theorem truncateToReal_of_le (h : x ≤ a) : truncateToReal a x = a := by
  rw [truncateToReal, max_eq_right h, toReal_coe]

/-- For `x ≠ ⊤`, the truncation `truncateToReal a x` is `max x a`. -/
theorem coe_truncateToReal (hx : x ≠ ⊤) : (truncateToReal a x : EReal) = max x a :=
  coe_toReal (max_coe_ne_top hx) (max_coe_ne_bot x)

theorem le_truncateToReal (hx : x ≠ ⊤) : a ≤ truncateToReal a x :=
  EReal.coe_le_coe_iff.1 (by rw [coe_truncateToReal hx]; exact le_max_right _ _)

theorem le_coe_truncateToReal (hx : x ≠ ⊤) : x ≤ truncateToReal a x := by
  rw [coe_truncateToReal hx]; exact le_max_left _ _

/-- `truncateToReal a` is monotone on `{x | x ≠ ⊤}`. -/
theorem truncateToReal_le_truncateToReal (h : x ≤ y) (hy : y ≠ ⊤) :
    truncateToReal a x ≤ truncateToReal a y :=
  EReal.coe_le_coe_iff.1 (by
    rw [coe_truncateToReal (ne_top_of_le_ne_top hy h), coe_truncateToReal hy]
    exact max_le_max h le_rfl)

/-- `truncateToReal a x` is monotone in the level `a` (for `x ≠ ⊤`). -/
theorem truncateToReal_le_truncateToReal_of_le (hab : a ≤ b) (hx : x ≠ ⊤) :
    truncateToReal a x ≤ truncateToReal b x :=
  EReal.coe_le_coe_iff.1 (by
    rw [coe_truncateToReal hx, coe_truncateToReal hx]
    exact max_le_max le_rfl (EReal.coe_le_coe_iff.2 hab))

theorem truncateToReal_le_of_le (hx : x ≤ b) (hab : a ≤ b) : truncateToReal a x ≤ b :=
  EReal.coe_le_coe_iff.1 (by
    rw [coe_truncateToReal (ne_top_of_le_ne_top (coe_ne_top b) hx)]
    exact max_le hx (EReal.coe_le_coe_iff.2 hab))

theorem truncateToReal_lt_of_lt (hx : x < b) (hab : a < b) : truncateToReal a x < b :=
  EReal.coe_lt_coe_iff.1 (by
    rw [coe_truncateToReal hx.ne_top]
    exact max_lt hx (EReal.coe_lt_coe_iff.2 hab))

/-- Truncating `x + t` at level `a` is truncating `x` at level `a - t` and adding `t`. -/
theorem truncateToReal_add_coe (a t : ℝ) (hx : x ≠ ⊤) :
    truncateToReal a (x + t) = truncateToReal (a - t) x + t := by
  induction x with
  | bot => simp
  | coe ξ =>
    simp only [← coe_add, truncateToReal_coe]
    rw [← max_add_add_right, _root_.sub_add_cancel]
  | top => exact absurd rfl hx

theorem measurable_truncateToReal (a : ℝ) : Measurable (truncateToReal a) :=
  measurable_ereal_toReal.comp (measurable_id.max measurable_const)

end EReal

/-!
### Definition and basic properties
-/

/-- A function `u : ℂ → EReal` is *subharmonic* on a set `U` if it is upper semicontinuous on `U`,
never takes the value `⊤` on `U`, and satisfies the local sub-mean-value inequality at every
`z ∈ U`: for all sufficiently small radii `r > 0` and every level `a : ℝ`, `u z` is at most the
circle average of the truncation `EReal.truncateToReal a ∘ u = (max u a).toReal` over the circle
of radius `r` around `z`. The truncated averages are the standard way to give a meaning to the
circle average of a function bounded above with values in `[-∞, ∞)`; the notion is intended for
open sets `U` (for non-open `U`, the sub-mean-value condition involves values of `u` outside
`U`). -/
structure SubharmonicOn (u : ℂ → EReal) (U : Set ℂ) : Prop where
  /-- `u` is upper semicontinuous on `U`. -/
  upperSemicontinuousOn : UpperSemicontinuousOn u U
  /-- `u` does not take the value `⊤ = +∞` on `U`. -/
  ne_top : ∀ z ∈ U, u z ≠ ⊤
  /-- The sub-mean-value inequality: for every `z ∈ U`, all sufficiently small radii `r > 0` and
  every level `a : ℝ`, `u z` is at most the circle average of the truncation `(max u a).toReal`
  over the circle of radius `r` around `z`. -/
  le_circleAverage : ∀ z ∈ U, ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ a : ℝ,
    u z ≤ ((circleAverage (fun w ↦ EReal.truncateToReal a (u w)) z r : ℝ) : EReal)

/-- The truncations of an upper semicontinuous function `u : ℂ → EReal` with `u ≠ ⊤` on `U` are
circle integrable over every circle contained in `U`: they are measurable (`u` is upper
semicontinuous on the circle) and bounded (the truncation is at least the level and at most its
value at a maximum point of `u` on the compact circle). -/
theorem UpperSemicontinuousOn.circleIntegrable_truncateToReal {u : ℂ → EReal} {U : Set ℂ}
    (hu : UpperSemicontinuousOn u U) (hu' : ∀ z ∈ U, u z ≠ ⊤) {z : ℂ} {r : ℝ}
    (hr : sphere z |r| ⊆ U) (a : ℝ) :
    CircleIntegrable (fun w ↦ EReal.truncateToReal a (u w)) z r := by
  have hmem (θ : ℝ) : circleMap z r θ ∈ U := hr (circleMap_mem_sphere' z r θ)
  have hg : UpperSemicontinuous fun θ ↦ u (circleMap z r θ) :=
    upperSemicontinuousOn_univ_iff.1
      (hu.comp (continuous_circleMap z r).continuousOn fun θ _ ↦ hmem θ)
  have hmeas : Measurable fun θ ↦ EReal.truncateToReal a (u (circleMap z r θ)) :=
    (EReal.measurable_truncateToReal a).comp hg.measurable
  obtain ⟨w₀, hw₀, hmax⟩ := (hu.mono hr).exists_isMaxOn
    (NormedSpace.sphere_nonempty.2 (abs_nonneg r)) (isCompact_sphere z |r|)
  refine IntervalIntegrable.mono_fun' (g := fun _ ↦ max |a| |EReal.truncateToReal a (u w₀)|)
    intervalIntegrable_const hmeas.aestronglyMeasurable.restrict (ae_of_all _ fun θ ↦ ?_)
  simp only [Real.norm_eq_abs]
  refine abs_le.2 ⟨?_, ?_⟩
  · have h₁ := EReal.le_truncateToReal (a := a) (hu' _ (hmem θ))
    have h₂ := neg_abs_le a
    have h₃ := le_max_left |a| |EReal.truncateToReal a (u w₀)|
    linarith
  · calc EReal.truncateToReal a (u (circleMap z r θ))
        ≤ EReal.truncateToReal a (u w₀) :=
          EReal.truncateToReal_le_truncateToReal (hmax (circleMap_mem_sphere' z r θ))
            (hu' _ (hr hw₀))
      _ ≤ |EReal.truncateToReal a (u w₀)| := le_abs_self _
      _ ≤ max |a| |EReal.truncateToReal a (u w₀)| := le_max_right _ _

namespace SubharmonicOn

variable {u : ℂ → EReal} {U V : Set ℂ}

/-- A subharmonic function on `U` is subharmonic on every subset of `U`. -/
theorem mono (hu : SubharmonicOn u U) (hVU : V ⊆ U) : SubharmonicOn u V where
  upperSemicontinuousOn := hu.upperSemicontinuousOn.mono hVU
  ne_top z hz := hu.ne_top z (hVU hz)
  le_circleAverage z hz := hu.le_circleAverage z (hVU hz)

/-- The truncations of a subharmonic function are circle integrable over every circle contained
in its domain. -/
theorem circleIntegrable_truncateToReal (hu : SubharmonicOn u U) {z : ℂ} {r : ℝ}
    (hr : sphere z |r| ⊆ U) (a : ℝ) :
    CircleIntegrable (fun w ↦ EReal.truncateToReal a (u w)) z r :=
  hu.upperSemicontinuousOn.circleIntegrable_truncateToReal hu.ne_top hr a

/-- On an open set `U`, the sub-mean-value inequality at `z ∈ U` holds for all sufficiently small
radii `r`, together with the inclusion `closedBall z r ⊆ U`. -/
theorem eventually_closedBall_subset_and_le_circleAverage (hU : IsOpen U)
    (hu : SubharmonicOn u U) {z : ℂ} (hz : z ∈ U) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), closedBall z r ⊆ U ∧ ∀ a : ℝ,
      u z ≤ ((circleAverage (fun w ↦ EReal.truncateToReal a (u w)) z r : ℝ) : EReal) := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU z hz
  filter_upwards [Ioo_mem_nhdsGT hε, hu.le_circleAverage z hz] with r hr h
  exact ⟨(closedBall_subset_ball hr.2).trans hεU, h⟩

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
    obtain ⟨ε, hε, hεh⟩ := Metric.eventually_nhds_iff_ball.1 (hh z hz).eventually
    filter_upwards [Ioo_mem_nhdsGT hε] with r hr a
    have hball : HarmonicOnNhd h (closedBall z |r|) := fun y hy ↦
      hεh y (closedBall_subset_ball (by rw [abs_of_pos hr.1]; exact hr.2) hy)
    have hcont : ContinuousOn h (sphere z |r|) :=
      hball.continuousOn.mono sphere_subset_closedBall
    simp only [EReal.truncateToReal_coe]
    rw [EReal.coe_le_coe_iff, ← hball.circleAverage_eq]
    exact circleAverage_mono hcont.circleIntegrable'
      (hcont.sup continuousOn_const).circleIntegrable' fun w _ ↦ le_max_left _ _

/-- Constant real functions are subharmonic. -/
theorem _root_.subharmonicOn_const (c : ℝ) : SubharmonicOn (fun _ ↦ (c : EReal)) U :=
  (harmonicOnNhd_const c).subharmonicOn

/-- The sum of a subharmonic function on an open set `U` and a real harmonic function on `U` is
subharmonic on `U`. Upper semicontinuity of the sum uses the continuity of the addition of
`EReal` away from `(⊤, ⊥)`; for the sub-mean-value inequality, if `|h| ≤ H` on a small disc, then
`truncateToReal (a - H) u + h ≤ truncateToReal a (u + h)` pointwise, so the mean value property of
`h` gives `u z + h z ≤ ⨍ truncateToReal (a - H) u + ⨍ h ≤ ⨍ truncateToReal a (u + h)`. -/
theorem add_harmonic (hU : IsOpen U) (hu : SubharmonicOn u U) {h : ℂ → ℝ}
    (hh : HarmonicOnNhd h U) : SubharmonicOn (fun z ↦ u z + (h z : EReal)) U := by
  have hhusc : UpperSemicontinuousOn (fun z ↦ (h z : EReal)) U :=
    (continuous_coe_real_ereal.comp_continuousOn hh.continuousOn).upperSemicontinuousOn
  have husc : UpperSemicontinuousOn (fun z ↦ u z + (h z : EReal)) U :=
    hu.upperSemicontinuousOn.add' hhusc fun z hz ↦
      EReal.continuousAt_add (Or.inl (hu.ne_top z hz)) (Or.inr (EReal.coe_ne_top _))
  have hne : ∀ z ∈ U, u z + (h z : EReal) ≠ ⊤ := fun z hz ↦
    EReal.add_ne_top (hu.ne_top z hz) (EReal.coe_ne_top _)
  refine ⟨husc, hne, fun z hz ↦ ?_⟩
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU z hz
  have hcb : closedBall z (ε / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hεU
  obtain ⟨H, hH⟩ := (isCompact_closedBall z (ε / 2)).exists_bound_of_continuousOn
    (hh.continuousOn.mono hcb)
  filter_upwards [Ioo_mem_nhdsGT (half_pos hε), hu.le_circleAverage z hz] with r hr hsub a
  have hcb' : closedBall z |r| ⊆ closedBall z (ε / 2) := by
    rw [abs_of_pos hr.1]; exact closedBall_subset_closedBall hr.2.le
  have hsph : sphere z |r| ⊆ U := sphere_subset_closedBall.trans (hcb'.trans hcb)
  have hT₁ := hu.circleIntegrable_truncateToReal hsph (a - H)
  have hT₂ := husc.circleIntegrable_truncateToReal hne hsph a
  have hhI : CircleIntegrable h z r :=
    ((hh.continuousOn.mono hcb).mono (sphere_subset_closedBall.trans hcb')).circleIntegrable'
  have hpt : ∀ w ∈ sphere z |r|,
      EReal.truncateToReal (a - H) (u w) + h w ≤ EReal.truncateToReal a (u w + h w) := by
    intro w hw
    have hw' : ‖h w‖ ≤ H := hH w (hcb' (sphere_subset_closedBall hw))
    rw [Real.norm_eq_abs] at hw'
    rw [EReal.truncateToReal_add_coe _ _ (hu.ne_top w (hsph hw))]
    exact add_le_add (EReal.truncateToReal_le_truncateToReal_of_le
      (by linarith [le_abs_self (h w)]) (hu.ne_top w (hsph hw))) le_rfl
  have hmv : circleAverage h z r = h z := (hh.mono (hcb'.trans hcb)).circleAverage_eq
  calc u z + (h z : EReal)
      ≤ ((circleAverage (fun w ↦ EReal.truncateToReal (a - H) (u w)) z r : ℝ) : EReal)
          + (h z : EReal) := add_le_add (hsub (a - H)) le_rfl
    _ = ((circleAverage (fun w ↦ EReal.truncateToReal (a - H) (u w)) z r
          + circleAverage h z r : ℝ) : EReal) := by rw [EReal.coe_add, hmv]
    _ = ((circleAverage (fun w ↦ EReal.truncateToReal (a - H) (u w) + h w) z r : ℝ) : EReal) := by
        rw [circleAverage_fun_add hT₁ hhI]
    _ ≤ _ := EReal.coe_le_coe_iff.2 (circleAverage_mono (hT₁.add hhI) hT₂ hpt)

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
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU z hz
  filter_upwards [Ioo_mem_nhdsGT hε] with r hr a
  by_cases hfz : f z = 0
  · simp [hfz]
  have hrabs : |r| = r := abs_of_pos hr.1
  have hcb : closedBall z |r| ⊆ U := by rw [hrabs]; exact (closedBall_subset_ball hr.2).trans hεU
  have hfr : AnalyticOnNhd ℂ f (closedBall z |r|) := hf.mono hcb
  have hsph : sphere z |r| ⊆ U := sphere_subset_closedBall.trans hcb
  -- Jensen's formula: `log ‖f z‖ ≤ ⨍ log ‖f ·‖`, as the divisor term is nonnegative
  have hjensen : Real.log ‖f z‖ ≤ circleAverage (fun w ↦ Real.log ‖f w‖) z r := by
    rw [hfr.circleAverage_log_norm hr.1.ne' hfz]
    refine le_add_of_nonneg_left (finsum_nonneg fun w ↦ ?_)
    by_cases hw : w ∈ closedBall z |r|
    · have h0 : (0 : ℤ) ≤ MeromorphicOn.divisor f (closedBall z |r|) w := by
        simpa using MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfr w
      refine mul_nonneg (mod_cast h0) ?_
      by_cases hwz : w = z
      · simp [hwz]
      · apply Real.log_nonneg
        rw [← div_eq_mul_inv, one_le_div (norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hwz)))]
        rwa [mem_closedBall, dist_eq_norm', hrabs] at hw
    · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hw]
  -- the truncation of `ENNReal.log ‖f ·‖ₑ` agrees with `max (log ‖f ·‖) a` off the zeros of `f`
  have hL : CircleIntegrable (fun w ↦ Real.log ‖f w‖) z r :=
    (hfr.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
  have hT := husc.circleIntegrable_truncateToReal hne hsph a
  have hcod : (fun w ↦ EReal.truncateToReal a (ENNReal.log ‖f w‖ₑ))
      =ᶠ[codiscreteWithin (sphere z |r|)] fun w ↦ max (Real.log ‖f w‖) a := by
    have h₀ := hfr.preimage_zero_mem_codiscreteWithin hfz (mem_closedBall_self (abs_nonneg r))
      ⟨nonempty_closedBall.2 (abs_nonneg r), (convex_closedBall z |r|).isPreconnected⟩
    filter_upwards [codiscreteWithin_mono sphere_subset_closedBall h₀] with w hw
    simp only [mem_preimage, mem_compl_iff, mem_singleton_iff] at hw
    rw [← ofReal_norm, ENNReal.log_ofReal_of_pos (norm_pos_iff.2 hw), EReal.truncateToReal_coe]
  calc ENNReal.log ‖f z‖ₑ = ((Real.log ‖f z‖ : ℝ) : EReal) := by
        rw [← ofReal_norm, ENNReal.log_ofReal_of_pos (norm_pos_iff.2 hfz)]
    _ ≤ ((circleAverage (fun w ↦ max (Real.log ‖f w‖) a) z r : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.2 (hjensen.trans (circleAverage_mono hL
          (hT.congr_codiscreteWithin hcod) fun w _ ↦ le_max_left _ _))
    _ = _ := by rw [circleAverage_congr_codiscreteWithin hcod hr.1.ne']

/-- **`log ‖f‖` is subharmonic**: for `f : ℂ → ℂ` analytic on the open set `U`, the function
`log ‖f ·‖` extended by `⊥ = -∞` at the zeros of `f` is subharmonic on `U`. -/
theorem _root_.AnalyticOnNhd.subharmonicOn_log_norm {f : ℂ → ℂ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) :
    SubharmonicOn (fun z ↦ if f z = 0 then ⊥ else ((Real.log ‖f z‖ : ℝ) : EReal)) U := by
  have : (fun z ↦ if f z = 0 then ⊥ else ((Real.log ‖f z‖ : ℝ) : EReal)) =
      fun z ↦ ENNReal.log ‖f z‖ₑ := by
    funext z
    rw [← ofReal_norm, ENNReal.log_ofReal]
    by_cases hfz : f z = 0 <;> simp [hfz]
  rw [this]
  exact hf.subharmonicOn_log_enorm hU

end SubharmonicOn

/-!
### The maximum principle
-/

/-- For any function `u` and any set `s`, the function `x ↦ limsup u (𝓝[s] x)` (the upper
semicontinuous regularization of `u` relative to `s`) is upper semicontinuous. -/
theorem upperSemicontinuous_limsup_nhdsWithin {α β : Type*} [TopologicalSpace α]
    [CompleteLinearOrder β] [DenselyOrdered β] (u : α → β) (s : Set α) :
    UpperSemicontinuous fun x ↦ limsup u (𝓝[s] x) := by
  refine fun x y hy ↦ ?_
  obtain ⟨y', hy'₁, hy'₂⟩ := exists_between hy
  obtain ⟨V, hVo, hxV, hV⟩ := mem_nhdsWithin.1 (eventually_lt_of_limsup_lt hy'₁)
  filter_upwards [hVo.mem_nhds hxV] with w hw
  have hw' : ∀ᶠ w' in 𝓝[s] w, u w' ≤ y' := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (hVo.mem_nhds hw),
      self_mem_nhdsWithin] with w' hw' hw's
    exact (hV ⟨hw', hw's⟩).le
  exact lt_of_le_of_lt (limsup_le_of_le (by isBoundedDefault) hw') hy'₂

/-- At a point `x ∈ s`, the upper semicontinuous regularization `limsup u (𝓝[s] x)` of a function
`u` that is upper semicontinuous on `s` is `u x`. -/
theorem UpperSemicontinuousOn.limsup_nhdsWithin_eq {α β : Type*} [TopologicalSpace α]
    [CompleteLinearOrder β] {u : α → β} {s : Set α} (hu : UpperSemicontinuousOn u s) {x : α}
    (hx : x ∈ s) : limsup u (𝓝[s] x) = u x := by
  refine le_antisymm (UpperSemicontinuousWithinAt.limsup_le (hu x hx))
    (le_limsup_of_frequently_le ?_)
  exact (frequently_pure.2 (le_refl (u x)) : ∃ᶠ w in pure x, u x ≤ u w).filter_mono
    (pure_le_nhdsWithin hx)

namespace SubharmonicOn

variable {u : ℂ → EReal} {U : Set ℂ}

/-- If a subharmonic function on an open set `U` is bounded by a real number `M` on `U` and
attains the value `M` at `z ∈ U`, then it is equal to `M` in a neighbourhood of `z`.

Proof: otherwise there is `w` arbitrarily close to `z` with `u w < M`; by upper semicontinuity
`u < M` on a ball around `w`. The circle around `z` through `w` lies in `U`, and the truncation
`T = truncateToReal (M - 1) ∘ u` satisfies `T ≤ M` on it and `T < M` on the nonempty open arc
inside that ball, so `⨍ T < M = u z`, contradicting the sub-mean-value inequality. -/
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
  have hsph : sphere z |dist w z| ⊆ U := by
    rw [hrabs]; exact sphere_subset_closedBall.trans hcb
  have hwU : w ∈ U := hcb (mem_closedBall.2 le_rfl)
  by_contra hne
  have hlt : u w < M := lt_of_le_of_ne (hM w hwU) hne
  -- by upper semicontinuity, `u < M` on a ball around `w`
  have hev := hu.upperSemicontinuousOn w hwU (M : EReal) hlt
  rw [nhdsWithin_eq_nhds.2 (hU.mem_nhds hwU), Metric.eventually_nhds_iff_ball] at hev
  obtain ⟨δ, hδ, hδlt⟩ := hev
  -- the truncation `T` at level `M - 1`: `T ≤ M` on the circle, `T < M` on the arc in the ball
  set T : ℂ → ℝ := fun w' ↦ EReal.truncateToReal (M - 1) (u w') with hT
  have hTint : CircleIntegrable T z (dist w z) :=
    hu.circleIntegrable_truncateToReal hsph (M - 1)
  have hTle (θ : ℝ) : T (circleMap z (dist w z) θ) ≤ M :=
    EReal.truncateToReal_le_of_le (hM _ (hsph (circleMap_mem_sphere' z _ θ))) (by linarith)
  have hTlt (θ : ℝ) (hθ : circleMap z (dist w z) θ ∈ ball w δ) :
      T (circleMap z (dist w z) θ) < M :=
    EReal.truncateToReal_lt_of_lt (hδlt _ hθ) (by linarith)
  -- the sub-mean-value inequality at level `M - 1` gives `2π M ≤ ∫ T`
  have hMle : 2 * π * M ≤ ∫ θ in (0 : ℝ)..2 * π, T (circleMap z (dist w z) θ) := by
    have h₁ := hsub (M - 1)
    rw [hzM, EReal.coe_le_coe_iff, circleAverage_def, smul_eq_mul,
      le_inv_mul_iff₀ two_pi_pos] at h₁
    exact h₁
  -- but `∫ (M - T) > 0`, integrating over a period around the angle of `w`
  obtain ⟨θ₀, hθ₀⟩ : w ∈ range (circleMap z (dist w z)) := by
    rw [range_circleMap, hrabs]; exact mem_sphere.2 rfl
  have hper : Function.Periodic (fun θ ↦ T (circleMap z (dist w z) θ)) (2 * π) :=
    (periodic_circleMap z (dist w z)).comp T
  have hint : IntervalIntegrable (fun θ ↦ T (circleMap z (dist w z) θ)) volume (θ₀ - π)
      (θ₀ - π + 2 * π) :=
    (hper.intervalIntegrable_iff (t₂ := 0)).2 (by rw [zero_add]; exact hTint)
  have hpos : 0 < ∫ θ in (θ₀ - π)..(θ₀ - π + 2 * π), (M - T (circleMap z (dist w z) θ)) := by
    rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae'
      (ae_of_all _ fun θ ↦ sub_nonneg.2 (hTle θ)) (intervalIntegrable_const.sub hint)]
    refine ⟨by linarith [Real.pi_pos], ?_⟩
    have hopen : IsOpen (circleMap z (dist w z) ⁻¹' ball w δ ∩ Ioo (θ₀ - π) (θ₀ - π + 2 * π)) :=
      ((continuous_circleMap z _).isOpen_preimage _ isOpen_ball).inter isOpen_Ioo
    have hne : (circleMap z (dist w z) ⁻¹' ball w δ ∩ Ioo (θ₀ - π) (θ₀ - π + 2 * π)).Nonempty :=
      ⟨θ₀, by simp [hθ₀, hδ], by constructor <;> linarith [Real.pi_pos]⟩
    refine lt_of_lt_of_le (hopen.measure_pos volume hne)
      (measure_mono fun θ ⟨hθ₁, hθ₂⟩ ↦ ⟨?_, Ioo_subset_Ioc_self hθ₂⟩)
    exact sub_ne_zero.2 (hTlt θ hθ₁).ne'
  rw [intervalIntegral.integral_sub intervalIntegrable_const hint, intervalIntegral.integral_const,
    hper.intervalIntegral_add_eq (θ₀ - π) 0, zero_add, smul_eq_mul,
    show θ₀ - π + 2 * π - (θ₀ - π) = 2 * π by ring] at hpos
  linarith

/-- **Strong maximum principle**: a subharmonic function on an open preconnected set `Ω` that
attains its supremum over `Ω` at a point `z₀ ∈ Ω` is constant on `Ω`. -/
theorem eqOn_const_of_isMaxOn {Ω : Set ℂ} (hΩ : IsOpen Ω) (hc : IsPreconnected Ω)
    (hu : SubharmonicOn u Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (hmax : IsMaxOn u Ω z₀) :
    EqOn u (fun _ ↦ u z₀) Ω := by
  -- if the maximum is `⊥`, then `u = ⊥` on `Ω`
  rcases eq_or_ne (u z₀) ⊥ with hbot | hbot
  · intro z hz
    exact le_bot_iff.1 ((hmax hz).trans_eq hbot) |>.trans hbot.symm
  -- otherwise the maximum is a real number `M`
  obtain ⟨M, hM⟩ : ∃ M : ℝ, u z₀ = M :=
    ⟨(u z₀).toReal, (EReal.coe_toReal (hu.ne_top z₀ hz₀) hbot).symm⟩
  have hle : ∀ w ∈ Ω, u w ≤ M := fun w hw ↦ hM ▸ hmax hw
  -- the set where `u = M` is open, closed in `Ω` (upper semicontinuity), and nonempty
  have hopen : IsOpen {z | z ∈ Ω ∧ u z = M} := by
    refine isOpen_iff_mem_nhds.2 fun z ⟨hzΩ, hzM⟩ ↦ ?_
    filter_upwards [hΩ.mem_nhds hzΩ, hu.eventually_eq_of_isMaxOn hΩ hzΩ hle hzM] with w hw hw'
    exact ⟨hw, hw'⟩
  have hsub : Ω ⊆ {z | z ∈ Ω ∧ u z = M} := by
    refine hc.subset_of_closure_inter_subset hopen ⟨z₀, hz₀, hz₀, hM⟩ fun z ⟨hzcl, hzΩ⟩ ↦
      ⟨hzΩ, le_antisymm (hle z hzΩ) ?_⟩
    refine UpperSemicontinuousWithinAt.frequently (hu.upperSemicontinuousOn z hzΩ) (M : EReal) ?_
    exact frequently_nhdsWithin_iff.2
      ((mem_closure_iff_frequently.1 hzcl).mono fun x ⟨hxΩ, hxM⟩ ↦ ⟨hxM.ge, hxΩ⟩)
  exact fun z hz ↦ (hsub hz).2.trans hM.symm

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
  by_contra! hpos
  obtain ⟨z₁, hz₁, hz₁pos⟩ := hpos
  set g : ℂ → EReal := fun ζ ↦ limsup u (𝓝[Ω] ζ)
  have hgu : ∀ z ∈ Ω, g z = u z := fun z hz ↦ hu.upperSemicontinuousOn.limsup_nhdsWithin_eq hz
  -- the maximum of `g` on `closure Ω` is positive, hence attained in `Ω`
  obtain ⟨ζ₀, hζ₀, hmax⟩ :=
    ((upperSemicontinuous_limsup_nhdsWithin u Ω).upperSemicontinuousOn _).exists_isMaxOn
      ⟨z₁, subset_closure hz₁⟩ hb.isCompact_closure
  have hζ₀pos : 0 < g ζ₀ :=
    hz₁pos.trans_le ((hgu z₁ hz₁).symm.le.trans (hmax (subset_closure hz₁)))
  have hζ₀Ω : ζ₀ ∈ Ω := by
    by_contra h
    exact absurd hζ₀pos (not_lt.2 (hfr ζ₀ ⟨hζ₀, by rwa [hΩ.interior_eq]⟩))
  -- `u` attains its maximum over `Ω` at `ζ₀`, hence is constant on `Ω`
  have hmaxΩ : IsMaxOn u Ω ζ₀ := isMaxOn_iff.2 fun z hz ↦
    (hgu z hz).symm.le.trans ((hmax (subset_closure hz)).trans (hgu ζ₀ hζ₀Ω).le)
  have hconst := hu.eqOn_const_of_isMaxOn hΩ hc hζ₀Ω hmaxΩ
  -- contradiction with the boundary condition at a point of the frontier
  obtain ⟨ζ, hζ⟩ := nonempty_frontier_iff.2
    ⟨⟨z₁, hz₁⟩, fun h ↦ NormedSpace.unbounded_univ ℂ ℂ (h ▸ hb)⟩
  have hne : (𝓝[Ω] ζ).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (frontier_subset_closure hζ)
  have hlim : limsup u (𝓝[Ω] ζ) = u ζ₀ := by
    rw [limsup_congr (eventually_nhdsWithin_of_forall fun z hz ↦ hconst hz), limsup_const]
  have h₁ : u ζ₀ ≤ 0 := hlim ▸ hfr ζ hζ
  have h₂ : 0 < u ζ₀ := (hgu ζ₀ hζ₀Ω) ▸ hζ₀pos
  exact absurd h₂ (not_lt.2 h₁)

end SubharmonicOn
