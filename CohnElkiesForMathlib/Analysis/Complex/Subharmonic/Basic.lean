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
  max_ne_top hx (coe_ne_top a)

private theorem max_coe_ne_bot (x : EReal) : max x (a : EReal) ≠ ⊥ :=
  ne_bot_of_le_ne_bot (coe_ne_bot a) (le_max_right x a)

@[simp] theorem truncateToReal_bot (a : ℝ) : truncateToReal a ⊥ = a := by simp [truncateToReal]

@[simp] theorem truncateToReal_top (a : ℝ) : truncateToReal a ⊤ = 0 := by simp [truncateToReal]

@[simp] theorem truncateToReal_coe (a b : ℝ) : truncateToReal a b = max b a := by
  rw [truncateToReal, ← coe_strictMono.monotone.map_max, toReal_coe]

theorem truncateToReal_of_le (h : x ≤ a) : truncateToReal a x = a := by
  rw [truncateToReal, max_eq_right h, toReal_coe]

/-- For `x ≠ ⊤`, the truncation `truncateToReal a x` is `max x a`. -/
theorem coe_truncateToReal (hx : x ≠ ⊤) : (truncateToReal a x : EReal) = max x a :=
  coe_toReal (max_coe_ne_top hx) (max_coe_ne_bot x)

theorem le_truncateToReal (hx : x ≠ ⊤) : a ≤ truncateToReal a x :=
  EReal.coe_le_coe_iff.1 ((le_max_right x a).trans_eq (coe_truncateToReal hx).symm)

theorem le_coe_truncateToReal (hx : x ≠ ⊤) : x ≤ truncateToReal a x :=
  (le_max_left x a).trans_eq (coe_truncateToReal hx).symm

/-- `truncateToReal a` is monotone on `{x | x ≠ ⊤}`. -/
theorem truncateToReal_le_truncateToReal (h : x ≤ y) (hy : y ≠ ⊤) :
    truncateToReal a x ≤ truncateToReal a y :=
  toReal_le_toReal (max_le_max_right _ h) (max_coe_ne_bot x) (max_coe_ne_top hy)

/-- `truncateToReal a x` is monotone in the level `a` (for `x ≠ ⊤`). -/
theorem truncateToReal_le_truncateToReal_of_le (hab : a ≤ b) (hx : x ≠ ⊤) :
    truncateToReal a x ≤ truncateToReal b x :=
  toReal_le_toReal (max_le_max_left x (EReal.coe_le_coe hab)) (max_coe_ne_bot x) (max_coe_ne_top hx)

theorem truncateToReal_le_of_le (hx : x ≤ b) (hab : a ≤ b) : truncateToReal a x ≤ b :=
  EReal.coe_le_coe_iff.1 ((coe_truncateToReal (ne_top_of_le_ne_top (coe_ne_top b) hx)).trans_le
    (max_le hx (EReal.coe_le_coe hab)))

theorem truncateToReal_lt_of_lt (hx : x < b) (hab : a < b) : truncateToReal a x < b :=
  EReal.coe_lt_coe_iff.1
    ((coe_truncateToReal hx.ne_top).trans_lt (max_lt hx (EReal.coe_lt_coe hab)))

/-- Truncating `x + t` at level `a` is truncating `x` at level `a - t` and adding `t`. -/
theorem truncateToReal_add_coe (a t : ℝ) (hx : x ≠ ⊤) :
    truncateToReal a (x + t) = truncateToReal (a - t) x + t := by
  induction x <;> simp_all [← coe_add, ← max_add_add_right]

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
  obtain ⟨w₀, hw₀, hmax⟩ := (hu.mono hr).exists_isMaxOn
    (NormedSpace.sphere_nonempty.2 (abs_nonneg r)) (isCompact_sphere z |r|)
  exact IntervalIntegrable.mono_fun' (g := fun _ ↦ max |a| |EReal.truncateToReal a (u w₀)|)
    intervalIntegrable_const
    ((EReal.measurable_truncateToReal a).comp hg.measurable).aestronglyMeasurable.restrict
    (ae_of_all _ fun θ ↦ abs_le_max_abs_abs (EReal.le_truncateToReal (hu' _ (hmem θ)))
      (EReal.truncateToReal_le_truncateToReal (hmax (circleMap_mem_sphere' z r θ))
        (hu' _ (hr hw₀))))

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
      u z ≤ ((circleAverage (fun w ↦ EReal.truncateToReal a (u w)) z r : ℝ) : EReal) :=
  ((eventually_closedBall_subset (hU.mem_nhds hz)).filter_mono nhdsWithin_le_nhds).and
    (hu.le_circleAverage z hz)

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
