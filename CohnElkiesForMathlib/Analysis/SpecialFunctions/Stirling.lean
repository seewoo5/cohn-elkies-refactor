import Mathlib

/-!
# Logarithmic forms of Stirling's formula

`log x / x → 0`, and Stirling's formula in the form `log (k!) / k - log k → -1`
(`Stirling.tendsto_log_factorial_div_sub_log`), from `Stirling.tendsto_stirlingSeq_sqrt_pi`.
-/

open Filter Real
open scoped Nat Topology

/-- `log x / x → 0`. -/
theorem Real.tendsto_log_div_self_atTop : Tendsto (fun x : ℝ ↦ log x / x) atTop (𝓝 0) :=
  isLittleO_log_id_atTop.tendsto_div_nhds_zero

theorem Real.tendsto_log_natCast_div_natCast : Tendsto (fun k : ℕ ↦ log k / k) atTop (𝓝 0) :=
  Real.tendsto_log_div_self_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))

/-- Stirling's formula in the form `log (k!)/k - log k → -1`. -/
theorem Stirling.tendsto_log_factorial_div_sub_log :
    Tendsto (fun k : ℕ ↦ log (k ! : ℝ) / k - log k) atTop (𝓝 (-1)) := by
  have hseq : Tendsto (fun k : ℕ ↦ log (Stirling.stirlingSeq k) / k) atTop (𝓝 0) :=
    ((continuousAt_log (by positivity)).tendsto.comp
      Stirling.tendsto_stirlingSeq_sqrt_pi).div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have htwo : Tendsto (fun k : ℕ ↦ log (2 * k) / (2 * (k : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_log_div_self_atTop.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop two_pos)
  have key := (hseq.add htwo).sub (tendsto_const_nhds (x := (1 : ℝ)))
  rw [zero_add, zero_sub] at key
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have h := Stirling.log_stirlingSeq_formula k
  rw [log_div hk0 (exp_ne_zero 1), log_exp, mul_comm (2 : ℝ) (k : ℝ)] at h
  rw [mul_comm (2 : ℝ) (k : ℝ)]
  field_simp
  linarith
