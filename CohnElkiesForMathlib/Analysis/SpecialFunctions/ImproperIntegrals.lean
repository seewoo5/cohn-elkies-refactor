import Mathlib

/-!
# Integrability of `e^{-a|x|}` and related functions on `ℝ`

An even function integrable on `(0, ∞)` is integrable on `ℝ` (`MeasureTheory.integrable_of_even`);
`e^{-a|x|}`, `|x|^n e^{-a|x|}` and `e^{-a|x|} |log |x||` are integrable on `ℝ` for `a > 0`,
and `e^{-ax} |log x|`, `e^{-ax} |log (x / 2)|` are integrable on `(0, ∞)`.
-/

open Filter MeasureTheory Real Set
open scoped Topology

/-- Integrability on `(-∞, 0)` from integrability of the reflected function on `(0, ∞)`. -/
theorem MeasureTheory.integrableOn_Iio_of_comp_neg {f : ℝ → ℝ}
    (h : IntegrableOn (fun x : ℝ ↦ f (-x)) (Ioi 0)) :
    IntegrableOn f (Iio 0) := by
  have hreflected : IntegrableOn (f ∘ (fun x : ℝ ↦ -x)) ((fun x : ℝ ↦ -x) ⁻¹' Iio (0 : ℝ)) := by
    simpa [Function.comp_def, neg_preimage, neg_Iio] using h
  exact ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding).mp hreflected

/-- An even function integrable on `(0, ∞)` is integrable on `ℝ`. -/
theorem MeasureTheory.integrable_of_even {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x)
    (h : IntegrableOn f (Ioi 0)) :
    Integrable f := by
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  exact ⟨integrableOn_Iio_of_comp_neg (by simpa only [hf] using h), h⟩

/-- `e^{-a|x|}` is integrable on `ℝ` for `a > 0`. -/
theorem integrable_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun y : ℝ ↦ exp ((-a) * |y|)) := by
  refine integrable_of_even (fun y ↦ by rw [abs_neg]) ?_
  refine (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) 0).congr_fun
    (fun y hy ↦ ?_) measurableSet_Ioi
  simp only [abs_of_pos (mem_Ioi.mp hy)]

/-- `|x|^n e^{-a|x|}` is integrable on `ℝ` for `a > 0`. -/
theorem integrable_abs_pow_mul_exp_neg_mul_abs (n : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable fun T : ℝ ↦ |T| ^ n * exp (-a * |T|) := by
  refine integrable_of_even (fun T ↦ by rw [abs_neg]) ?_
  refine (integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (n : ℝ)) (b := a)
    (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n)) one_pos ha).congr_fun
    (fun T hT ↦ ?_) measurableSet_Ioi
  rw [abs_of_pos hT]
  simp [Real.rpow_natCast, Real.rpow_one]

theorem integrableOn_exp_neg_mul_mul_abs_log_Ioi {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ exp ((-a) * x) * |log x|) (Ioi (0 : ℝ)) := by
  have hbound : ∀ x : ℝ, 0 < x → |log x| ≤ x + 2 * x ^ (-(1 / 2 : ℝ)) := by
    intro x hx
    have hpower := rpow_pos_of_pos hx (-(1 / 2 : ℝ))
    rcases le_total 1 x with hlarge | hsmall
    · rw [abs_of_nonneg (log_nonneg hlarge)]
      nlinarith [log_le_sub_one_of_pos hx]
    · rw [abs_of_nonpos (log_nonpos hx.le hsmall)]
      have h := log_le_sub_one_of_pos hpower
      rw [log_rpow hx] at h
      nlinarith
  have hlinear : IntegrableOn (fun x : ℝ ↦ x * exp ((-a) * x)) (Ioi (0 : ℝ)) := by
    simpa [rpow_one] using integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (1 : ℝ))
      (b := a) (by norm_num) (by norm_num) ha
  have hhalf : IntegrableOn (fun x : ℝ ↦ x ^ (-(1 / 2 : ℝ)) * exp ((-a) * x)) (Ioi (0 : ℝ)) := by
    simpa [rpow_one] using integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ))
      (s := -(1 / 2 : ℝ)) (b := a) (by norm_num) (by norm_num) ha
  refine (hlinear.add (hhalf.const_mul 2)).mono' (ContinuousOn.aestronglyMeasurable
    ((by fun_prop : ContinuousOn (fun x : ℝ ↦ exp ((-a) * x)) (Ioi (0 : ℝ))).mul
      (continuousOn_id.log fun x hx ↦ (mem_Ioi.mp hx).ne').abs) measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  calc ‖exp ((-a) * x) * |log x|‖ = exp ((-a) * x) * |log x| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _), abs_abs]
    _ ≤ exp ((-a) * x) * (x + 2 * x ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (hbound x (mem_Ioi.mp hx)) (exp_pos _).le
    _ = x * exp ((-a) * x) + 2 * (x ^ (-(1 / 2 : ℝ)) * exp ((-a) * x)) := by ring

/-- `e^{-ax} |log (x / 2)|` is integrable on `(0, ∞)` for `a > 0`. -/
theorem integrableOn_exp_neg_mul_mul_abs_log_div_two_Ioi {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y : ℝ ↦ exp ((-a) * y) * |log (y / 2)|) (Ioi (0 : ℝ)) := by
  have hmajorant : IntegrableOn
      (fun y : ℝ ↦ exp ((-a) * y) * |log y| + |log (2 : ℝ)| * exp ((-a) * y)) (Ioi (0 : ℝ)) :=
    (integrableOn_exp_neg_mul_mul_abs_log_Ioi ha).add
      ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) 0).const_mul |log (2 : ℝ)|)
  have hcontinuous : ContinuousOn (fun y : ℝ ↦ exp ((-a) * y) * |log (y / 2)|)
      (Ioi (0 : ℝ)) := by
    refine ContinuousOn.mul (by fun_prop) (ContinuousOn.abs (ContinuousOn.log (by fun_prop) ?_))
    exact fun y hy ↦ div_ne_zero (mem_Ioi.mp hy).ne' two_ne_zero
  refine hmajorant.mono' (hcontinuous.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hlog : |log (y / 2)| ≤ |log y| + |log (2 : ℝ)| := by
    rw [Real.log_div (mem_Ioi.mp hy).ne' two_ne_zero]
    exact abs_sub _ _
  calc ‖exp ((-a) * y) * |log (y / 2)|‖ = exp ((-a) * y) * |log (y / 2)| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _), abs_abs]
    _ ≤ exp ((-a) * y) * (|log y| + |log (2 : ℝ)|) :=
        mul_le_mul_of_nonneg_left hlog (exp_pos _).le
    _ = exp ((-a) * y) * |log y| + |log (2 : ℝ)| * exp ((-a) * y) := by ring

/-- `e^{-a|x|} |log |x||` is integrable on `ℝ` for `a > 0`. -/
theorem integrable_exp_neg_mul_abs_mul_abs_log_abs {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ ↦ exp ((-a) * |x|) * |log (|x|)|) := by
  refine integrable_of_even (fun x ↦ by rw [abs_neg]) ?_
  refine (integrableOn_exp_neg_mul_mul_abs_log_Ioi ha).congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
  simp only [abs_of_pos (mem_Ioi.mp hx)]
