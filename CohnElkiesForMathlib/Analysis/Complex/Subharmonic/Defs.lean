import Mathlib

/-!
# Subharmonic functions in the complex plane: definitions

A function `u : ℂ → EReal` is *subharmonic* on a set `U ⊆ ℂ` (`SubharmonicOn u U`) if it is upper
semicontinuous on `U`, never takes the value `⊤` on `U`, and satisfies the local sub-mean-value
inequality `u z ≤ ⨍ u` over all sufficiently small circles around every `z ∈ U`. Since `u` may take
the value `⊥ = -∞` (as `log ‖f‖` does at the zeros of an analytic function `f`), the circle average
is understood through the truncations `max u a`, `a : ℝ` (`EReal.truncateToReal`), which are
bounded and measurable on circles: the inequality is required for every level `a`.

This file contains the definitions and the bare minimum of supporting lemmas; the theory (harmonic
functions are subharmonic, `log ‖f‖` is subharmonic for `f` analytic, the maximum principles) is
developed in `CohnElkiesForMathlib.Analysis.Complex.Subharmonic.Basic`.

## Main definitions

* `EReal.truncateToReal a x = (max x a).toReal`: `x : EReal` truncated from below at the real
  level `a`, as a real number, with its order and measurability API;
* `SubharmonicOn u U`: `u : ℂ → EReal` is subharmonic on `U ⊆ ℂ`.

## Main results

* `UpperSemicontinuousOn.circleIntegrable_truncateToReal`,
  `SubharmonicOn.circleIntegrable_truncateToReal`: the truncations of an upper semicontinuous
  function with values in `[-∞, ∞)` are circle integrable over every circle in its domain, so the
  circle averages in the definition are averages of integrable functions;
* `SubharmonicOn.mono`: a subharmonic function on `U` is subharmonic on every subset of `U`;
* `SubharmonicOn.eventually_closedBall_subset_and_le_circleAverage`: on an open set `U`, the
  sub-mean-value inequality at `z ∈ U` holds for all sufficiently small radii `r` together with
  `closedBall z r ⊆ U`.
-/

open Filter MeasureTheory Metric Real Set Topology

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

end SubharmonicOn
