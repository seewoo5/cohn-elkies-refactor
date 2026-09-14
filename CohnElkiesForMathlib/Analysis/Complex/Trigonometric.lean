import Mathlib
import CohnElkiesForMathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Trigonometric and hyperbolic trigonometric functions

This file defines the hyperbolic cotangent `coth x = cosh x / sinh x`, the reciprocal of
`Real.tanh` (with the junk value `coth 0 = 0`), and proves its elementary properties on
`(0, ∞)` together with the integrability of the weights built from `log ∘ coth`.

## Main definitions

* `Real.coth`: the hyperbolic cotangent, `coth x = cosh x / sinh x`.

## Main results

* `Real.coth_pos`, `Real.log_coth_nonneg`: `coth` is positive and `log ∘ coth` is nonnegative
  on `(0, ∞)`.
* `Real.hasDerivAt_coth`, `Real.antitoneOn_coth`, `Real.antitoneOn_log_coth`: `coth` is
  differentiable with derivative `-(sinh x)⁻¹ ^ 2`, and both `coth` and `log ∘ coth` are
  antitone on `(0, ∞)`.
* `Real.abs_log_coth_div_le`, `Real.log_coth_le_four_mul_exp_neg_two_mul`,
  `Real.log_coth_pi_mul_abs_div_two_le_one`, `Real.log_coth_pi_mul_abs_div_two_le`:
  quantitative bounds on `log (coth x)`, near the pole at `0` and at infinity.
* `Real.integrable_log_coth_pi_mul_abs_div_two`,
  `Real.integrable_exp_neg_mul_abs_mul_log_coth_div`: `y ↦ log (coth (π|y|/2))` and the damped
  weight `y ↦ e^{-a|y|} log (coth (π|y|/2) / (|y|/2))` are integrable on `ℝ`.

## Tags

coth, hyperbolic cotangent, hyperbolic function
-/

open Filter MeasureTheory Set

namespace Real

/-- The hyperbolic cotangent `coth x = cosh x / sinh x`. -/
@[pp_nodot]
noncomputable def coth (x : ℝ) : ℝ := cosh x / sinh x

theorem coth_eq_cosh_div_sinh (x : ℝ) : coth x = cosh x / sinh x := rfl

theorem coth_eq_inv_tanh (x : ℝ) : coth x = (tanh x)⁻¹ := by
  rw [coth_eq_cosh_div_sinh, tanh_eq_sinh_div_cosh, inv_div]

@[simp]
theorem coth_zero : coth 0 = 0 := by simp [coth]

/-- `coth` is positive on `(0, ∞)`. -/
theorem coth_pos {x : ℝ} (hx : 0 < x) : 0 < coth x :=
  div_pos (cosh_pos x) (Real.sinh_pos_iff.mpr hx)

/-- `coth x ≥ 1` for `x > 0`, hence `log (coth x)` is nonnegative there. -/
theorem log_coth_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ log (coth x) := by
  refine Real.log_nonneg ?_
  have hsinh : 0 < sinh x := Real.sinh_pos_iff.mpr hx
  unfold coth
  rw [le_div_iff₀ hsinh, one_mul, Real.sinh_eq, Real.cosh_eq]
  linarith [exp_pos (-x)]

/-- The derivative of `coth` at a point `x > 0` is `-(sinh x)⁻¹ ^ 2`. -/
theorem hasDerivAt_coth {x : ℝ} (hx : 0 < x) : HasDerivAt coth (-(sinh x)⁻¹ ^ 2) x := by
  have hsinh : sinh x ≠ 0 := (Real.sinh_pos_iff.mpr hx).ne'
  unfold coth
  convert! (Real.hasDerivAt_cosh x).div (Real.hasDerivAt_sinh x) hsinh using 1
  rw [div_eq_mul_inv]
  have hidentity := Real.cosh_sq_sub_sinh_sq x
  field_simp [hsinh]
  nlinarith

/-- `coth` is antitone on `(0, ∞)`. -/
theorem antitoneOn_coth : AntitoneOn coth (Ioi (0 : ℝ)) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    (fun x hx ↦ (hasDerivAt_coth hx).continuousAt.continuousWithinAt)
    (fun x hx ↦ (hasDerivAt_coth (by simpa using hx)).differentiableAt.differentiableWithinAt)
    fun x hx ↦ ?_
  rw [(hasDerivAt_coth (by simpa using hx)).deriv]
  exact neg_nonpos.mpr (sq_nonneg _)

/-- `fun x ↦ log (coth x)` is antitone on `(0, ∞)`. -/
theorem antitoneOn_log_coth : AntitoneOn (fun x : ℝ ↦ log (coth x)) (Ioi (0 : ℝ)) :=
  fun _x hx _y hy hxy ↦ Real.log_le_log (coth_pos hy) (antitoneOn_coth hx hy hxy)

/-- A crude bound for `log (coth (π x) / x)` on `(0, ∞)`, linear in `x` and in `log x`. -/
theorem abs_log_coth_div_le {x : ℝ} (hx : 0 < x) :
    |log (coth (π * x) / x)| ≤ 2 * (π * x) + |log π| + 2 * |log x| := by
  have ht : 0 < π * x := mul_pos pi_pos hx
  have hsinh : 0 < sinh (π * x) := Real.sinh_pos_iff.mpr ht
  have hcosh : 0 < cosh (π * x) := cosh_pos _
  have hcoshbound : |log (cosh (π * x))| ≤ π * x := by
    rw [abs_of_nonneg (Real.log_nonneg (Real.one_le_cosh _))]
    have h : cosh (π * x) ≤ exp (π * x) := by
      rw [Real.cosh_eq]
      linarith [Real.exp_le_exp.mpr (by linarith : -(π * x) ≤ π * x)]
    simpa using Real.log_le_log hcosh h
  have hsinhbound : |log (sinh (π * x))| ≤ π * x + |log (π * x)| := by
    have hlower : π * x ≤ sinh (π * x) := Real.self_le_sinh_iff.mpr ht.le
    rcases le_total 1 (sinh (π * x)) with hlarge | hsmall
    · rw [abs_of_nonneg (Real.log_nonneg hlarge)]
      have h : sinh (π * x) ≤ exp (π * x) := by
        rw [Real.sinh_eq]
        linarith [exp_pos (-(π * x)), exp_pos (π * x)]
      have hlog := Real.log_le_log hsinh h
      rw [Real.log_exp] at hlog
      linarith [abs_nonneg (log (π * x))]
    · rw [abs_of_nonpos (Real.log_nonpos hsinh.le hsmall)]
      linarith [Real.log_le_log ht hlower, neg_le_abs (log (π * x))]
  have hlogpi : |log (π * x)| ≤ |log π| + |log x| := by
    rw [Real.log_mul pi_ne_zero hx.ne']
    simpa [sub_neg_eq_add] using abs_sub (log π) (-(log x))
  unfold coth
  rw [Real.log_div (div_ne_zero hcosh.ne' hsinh.ne') hx.ne', Real.log_div hcosh.ne' hsinh.ne']
  have h1 := abs_sub (log (cosh (π * x))) (log (sinh (π * x)))
  have h2 := abs_sub (log (cosh (π * x)) - log (sinh (π * x))) (log x)
  linarith

/-- `log (coth x)` decays exponentially: it is at most `4 e^{-2x}` for `x ≥ 1`. -/
theorem log_coth_le_four_mul_exp_neg_two_mul {x : ℝ} (hx : 1 ≤ x) :
    log (coth x) ≤ 4 * exp (-2 * x) := by
  have hxpos : 0 < x := by linarith
  have hsinh : 0 < sinh x := Real.sinh_pos_iff.mpr hxpos
  have hquarter : exp x / 4 ≤ sinh x := by
    have hbig : 2 ≤ exp x := by nlinarith [Real.add_one_le_exp x]
    rw [Real.sinh_eq]
    linarith [Real.exp_le_one_iff.mpr (by linarith : -x ≤ 0)]
  calc log (coth x) ≤ coth x - 1 := Real.log_le_sub_one_of_pos (coth_pos hxpos)
    _ = exp (-x) / sinh x := by
        unfold coth
        field_simp [hsinh.ne']
        rw [Real.cosh_eq, Real.sinh_eq]
        ring
    _ ≤ exp (-x) / (exp x / 4) :=
        div_le_div_of_nonneg_left (exp_pos _).le (by positivity) hquarter
    _ = 4 * exp (-2 * x) := by
        rw [show -2 * x = -x - x by ring, Real.exp_sub]
        field_simp

/-- For `1 ≤ |y|` the hyperbolic cotangent correction `log (coth (π|y|/2))` is at most `1`. -/
theorem log_coth_pi_mul_abs_div_two_le_one {Y : ℝ} (hY : 1 ≤ |Y|) :
    log (coth (π * |Y| / 2)) ≤ 1 := by
  have hpiabs : 3 ≤ π * |Y| := by
    nlinarith [Real.pi_gt_three, mul_nonneg (by linarith [Real.pi_gt_three] : (0 : ℝ) ≤ π - 3)
      (sub_nonneg.mpr hY)]
  have hcoth := log_coth_le_four_mul_exp_neg_two_mul (by linarith : (1 : ℝ) ≤ π * |Y| / 2)
  have hexpthree : (4 : ℝ) ≤ exp 3 := by nlinarith [Real.add_one_le_exp (3 : ℝ)]
  have hexpsmall : exp (-2 * (π * |Y| / 2)) ≤ 1 / 4 := by
    calc exp (-2 * (π * |Y| / 2)) ≤ exp (-3 : ℝ) := Real.exp_le_exp.mpr (by linarith)
      _ = (exp 3)⁻¹ := Real.exp_neg 3
      _ ≤ 1 / 4 := by
        simpa [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hexpthree
  linarith

/-- For `0 < |y| ≤ 1` the logarithmic singularity of `log (coth (π|y|/2))` at the origin is
controlled by `3 |log |y||` up to an additive constant. -/
theorem log_coth_pi_mul_abs_div_two_le {y : ℝ} (hy : y ≠ 0) (hsmall : |y| ≤ 1) :
    log (coth (π * |y| / 2)) ≤
      π + |log π| + 3 * (|log (|y|)| + |log (2 : ℝ)|) := by
  have hu : 0 < |y| / 2 := by positivity
  have hcoth : 0 < coth (π * (|y| / 2)) := coth_pos (mul_pos pi_pos hu)
  have hloghalf : |log (|y| / 2)| ≤ |log (|y|)| + |log (2 : ℝ)| := by
    rw [Real.log_div (abs_ne_zero.mpr hy) two_ne_zero]
    exact abs_sub _ _
  have hpibound : 2 * (π * (|y| / 2)) ≤ π := by
    nlinarith [mul_nonneg pi_pos.le (sub_nonneg.mpr hsmall)]
  rw [show π * |y| / 2 = π * (|y| / 2) by ring,
    show log (coth (π * (|y| / 2))) =
      log (coth (π * (|y| / 2)) / (|y| / 2)) + log (|y| / 2) by
      rw [Real.log_div hcoth.ne' hu.ne']; ring]
  linarith [abs_log_coth_div_le hu, le_abs_self (log (coth (π * (|y| / 2)) / (|y| / 2))),
    le_abs_self (log (|y| / 2))]

/-- `y ↦ log (coth (π|y|/2))` is integrable on `ℝ`. -/
theorem integrable_log_coth_pi_mul_abs_div_two :
    Integrable (fun y : ℝ ↦ log (coth (π * |y| / 2))) := by
  set A : ℝ := π + |log π| + 3 * |log (2 : ℝ)| with hA
  have hAnonneg : 0 ≤ A := by rw [hA]; positivity
  have hnear : Integrable (fun y : ℝ ↦ A * exp ((-1 : ℝ) * |y|) +
      3 * (exp ((-1 : ℝ) * |y|) * |log (|y|)|)) :=
    ((integrable_exp_neg_mul_abs one_pos).const_mul A).add
      ((integrable_exp_neg_mul_abs_mul_abs_log_abs one_pos).const_mul 3)
  have hmajor : Integrable (fun y : ℝ ↦ exp 1 * (A * exp ((-1 : ℝ) * |y|) +
      3 * (exp ((-1 : ℝ) * |y|) * |log (|y|)|)) + 4 * exp ((-π) * |y|)) :=
    (hnear.const_mul (exp 1)).add ((integrable_exp_neg_mul_abs pi_pos).const_mul 4)
  refine hmajor.mono' ?_ ?_
  · have harg : Measurable fun y : ℝ ↦ π * |y| / 2 := by fun_prop
    have hcoth : Measurable fun y : ℝ ↦ coth (π * |y| / 2) := by
      unfold coth
      exact (Real.continuous_cosh.measurable.comp harg).div
        (Real.continuous_sinh.measurable.comp harg)
    exact hcoth.log.aestronglyMeasurable
  · filter_upwards with y
    have hfar_nonneg : 0 ≤ 4 * exp ((-π) * |y|) := by positivity
    have hnear_nonneg : 0 ≤ exp 1 * (A * exp ((-1 : ℝ) * |y|) +
        3 * (exp ((-1 : ℝ) * |y|) * |log (|y|)|)) := by positivity
    by_cases hy : y = 0
    · subst y
      simp only [coth, abs_zero, mul_zero, zero_div, cosh_zero, sinh_zero, div_zero, log_zero,
        norm_zero, hA, exp_zero, mul_one, add_zero, ge_iff_le]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (log_coth_nonneg (by positivity))]
    by_cases hsmall : |y| ≤ 1
    · have hfactor : 1 ≤ exp 1 * exp ((-1 : ℝ) * |y|) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp_iff.2 (by linarith [abs_nonneg y])
      have hpolynonneg : 0 ≤ A + 3 * |log (|y|)| := by positivity
      have hproduct : A + 3 * |log (|y|)| ≤
          (exp 1 * exp ((-1 : ℝ) * |y|)) * (A + 3 * |log (|y|)|) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hfactor) hpolynonneg]
      have hrewrite : (exp 1 * exp ((-1 : ℝ) * |y|)) * (A + 3 * |log (|y|)|) =
          exp 1 * (A * exp ((-1 : ℝ) * |y|) +
            3 * (exp ((-1 : ℝ) * |y|) * |log (|y|)|)) := by ring
      have hsb : log (coth (π * |y| / 2)) ≤ A + 3 * |log (|y|)| := by
        rw [hA]
        linarith [log_coth_pi_mul_abs_div_two_le hy hsmall]
      linarith
    · have harg : 1 ≤ π * |y| / 2 := by
        nlinarith [Real.pi_gt_three, lt_of_not_ge hsmall,
          mul_nonneg (by linarith [Real.pi_gt_three] : (0 : ℝ) ≤ π - 2)
            (sub_nonneg.mpr (lt_of_not_ge hsmall).le)]
      have hbound := log_coth_le_four_mul_exp_neg_two_mul harg
      rw [show -2 * (π * |y| / 2) = (-π) * |y| by ring] at hbound
      linarith

/-- The damped weight `exp (-a y) * log (coth (πy/2) / (y/2))` is integrable on `(0, ∞)`. -/
private theorem integrableOn_exp_neg_mul_mul_log_coth_div_Ioi {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y : ℝ ↦ exp ((-a) * y) * log (coth (π * y / 2) / (y / 2)))
      (Ioi (0 : ℝ)) := by
  have hlinear : IntegrableOn (fun y : ℝ ↦ y * exp ((-a) * y)) (Ioi (0 : ℝ)) := by
    simpa [Real.rpow_one] using integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ))
      (s := (1 : ℝ)) (b := a) (by norm_num) (by norm_num) ha
  have hmaj : IntegrableOn (fun y : ℝ ↦ π * (y * exp ((-a) * y)) + |log π| * exp ((-a) * y) +
      2 * (exp ((-a) * y) * |log (y / 2)|)) (Ioi (0 : ℝ)) :=
    ((hlinear.const_mul π).add ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) 0).const_mul
      |log π|)).add ((integrableOn_exp_neg_mul_mul_abs_log_div_two_Ioi ha).const_mul 2)
  have hratio : ∀ y ∈ Ioi (0 : ℝ), 0 < coth (π * y / 2) / (y / 2) := fun y hy ↦ by
    have hy' : 0 < y := hy
    exact div_pos (coth_pos (by positivity)) (by positivity)
  have hcont : ContinuousOn (fun y : ℝ ↦ coth (π * y / 2) / (y / 2)) (Ioi (0 : ℝ)) := by
    unfold coth
    exact ContinuousOn.div (ContinuousOn.div (by fun_prop) (by fun_prop)
      (fun y hy ↦ Real.sinh_ne_zero.mpr (by have hy' : 0 < y := hy; positivity)))
      (by fun_prop) fun y hy ↦ by have hy' : 0 < y := hy; positivity
  refine hmaj.mono' ((ContinuousOn.mul (by fun_prop)
    (hcont.log fun y hy ↦ (hratio y hy).ne')).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hy' : 0 < y := hy
  have hlog : |log (coth (π * y / 2) / (y / 2))| ≤ π * y + |log π| + 2 * |log (y / 2)| := by
    convert abs_log_coth_div_le (half_pos hy') using 1 <;> ring_nf
  calc ‖exp ((-a) * y) * log (coth (π * y / 2) / (y / 2))‖
      = exp ((-a) * y) * |log (coth (π * y / 2) / (y / 2))| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
    _ ≤ exp ((-a) * y) * (π * y + |log π| + 2 * |log (y / 2)|) :=
        mul_le_mul_of_nonneg_left hlog (exp_pos _).le
    _ = π * (y * exp ((-a) * y)) + |log π| * exp ((-a) * y) +
          2 * (exp ((-a) * y) * |log (y / 2)|) := by ring

/-- The damped weight `exp (-a|y|) * log (coth (π|y|/2) / (|y|/2))` is integrable on the line. -/
theorem integrable_exp_neg_mul_abs_mul_log_coth_div {a : ℝ} (ha : 0 < a) :
    Integrable fun y : ℝ ↦ exp ((-a) * |y|) * log (coth (π * |y| / 2) / (|y| / 2)) := by
  have hright : IntegrableOn (fun y : ℝ ↦ exp ((-a) * |y|) *
      log (coth (π * |y| / 2) / (|y| / 2))) (Ioi (0 : ℝ)) :=
    (integrableOn_exp_neg_mul_mul_log_coth_div_Ioi ha).congr_fun
      (fun y hy ↦ by simp only [abs_of_pos (mem_Ioi.mp hy)]) measurableSet_Ioi
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding).mp ?_, hright⟩
  simpa [Function.comp_def, neg_preimage, neg_Iio, abs_neg] using hright

end Real
