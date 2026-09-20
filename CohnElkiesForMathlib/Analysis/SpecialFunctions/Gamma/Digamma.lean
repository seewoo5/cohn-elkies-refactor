import Mathlib

/-!
# The real digamma function

`Real.digamma x := (Complex.digamma x).re` is the real digamma function `ψ = Γ'/Γ`, the real part
of Mathlib's `Complex.digamma` (as `Real.Gamma` is the real part of `Complex.Gamma`). It is the
logarithmic derivative of the real Gamma function (`Real.digamma_eq_logDeriv_Gamma`; in fact
`Complex.digamma` is real on the real axis, `Complex.digamma_ofReal`), and for `x > 0` it agrees
with `(log ∘ Γ)' x`. We prove the recurrence `ψ(x + 1) = ψ(x) + 1/x`, the bounds
`log (x - 1) ≤ ψ(x) ≤ log x` for `x > 1` (from the log-convexity of `Γ`), the asymptotics
`ψ(x) - log x → 0` as `x → ∞`, the harmonic representation
`ψ(m) = lim (log n - ∑_{k ≤ n} (m + k)⁻¹)` and the continuity of `ψ` on `(0, ∞)`.
-/

open Filter Real Set
open scoped Topology

namespace Real

/-- The real digamma function `ψ = Γ'/Γ`, the real part of `Complex.digamma`. -/
noncomputable def digamma (x : ℝ) : ℝ := (Complex.digamma x).re

theorem digamma_def (x : ℝ) : digamma x = (Complex.digamma x).re := rfl

/-- On the real axis and away from the poles, the derivative of `Complex.Gamma` is the derivative
of `Real.Gamma`. -/
theorem _root_.Complex.deriv_Gamma_ofReal {x : ℝ} (hx : ∀ m : ℕ, x ≠ -m) :
    deriv Complex.Gamma (x : ℂ) = deriv Gamma x := by
  have hx' : ∀ m : ℕ, (x : ℂ) ≠ -m := by
    simp_rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, Ne, Complex.ofReal_inj]
    exact hx
  have h : HasDerivAt (fun y : ℝ ↦ (Gamma y : ℂ)) (deriv Complex.Gamma (x : ℂ)) x := by
    simpa only [Complex.Gamma_ofReal] using
      (Complex.differentiableAt_Gamma _ hx').hasDerivAt.comp_ofReal
  exact h.unique (differentiableAt_Gamma hx).hasDerivAt.ofReal_comp

/-- On the real axis, `Complex.digamma` is the logarithmic derivative of `Real.Gamma` (at the poles
`0, -1, -2, …` both sides are `0`, as `Γ` vanishes there by convention). -/
theorem _root_.Complex.digamma_ofReal_eq_logDeriv_Gamma (x : ℝ) :
    Complex.digamma x = ((logDeriv Gamma x : ℝ) : ℂ) := by
  rw [Complex.digamma_def, logDeriv_apply, logDeriv_apply, Complex.ofReal_div,
    ← Complex.Gamma_ofReal]
  by_cases hx : ∀ m : ℕ, x ≠ -m
  · rw [Complex.deriv_Gamma_ofReal hx]
  · push Not at hx
    obtain ⟨m, rfl⟩ := hx
    push_cast
    rw [Complex.Gamma_neg_nat_eq_zero, div_zero, div_zero]

/-- The real digamma function is the logarithmic derivative of the real Gamma function. -/
theorem digamma_eq_logDeriv_Gamma (x : ℝ) : digamma x = logDeriv Gamma x := by
  rw [digamma_def, Complex.digamma_ofReal_eq_logDeriv_Gamma, Complex.ofReal_re]

/-- `Complex.digamma` is real on the real axis. -/
theorem _root_.Complex.digamma_ofReal (x : ℝ) : Complex.digamma x = digamma x := by
  rw [Complex.digamma_ofReal_eq_logDeriv_Gamma, digamma_eq_logDeriv_Gamma]

theorem differentiableAt_Gamma_of_pos {x : ℝ} (hx : 0 < x) : DifferentiableAt ℝ Gamma x :=
  differentiableAt_Gamma fun n ↦ ((neg_nonpos.2 (Nat.cast_nonneg n)).trans_lt hx).ne'

theorem log_comp_Gamma_add_one {x : ℝ} (hx : 0 < x) :
    (log ∘ Gamma) (x + 1) = (log ∘ Gamma) x + log x := by
  simp only [Function.comp_apply, Gamma_add_one hx.ne', log_mul hx.ne' (Gamma_pos_of_pos hx).ne']
  ring

theorem differentiableAt_log_comp_Gamma {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (log ∘ Gamma) x :=
  (differentiableAt_Gamma_of_pos hx).log (Gamma_pos_of_pos hx).ne'

/-- For `x > 0`, `ψ x = (log Γ)' x`. -/
theorem digamma_eq_deriv_log_comp_Gamma {x : ℝ} (hx : 0 < x) :
    digamma x = deriv (log ∘ Gamma) x := by
  rw [digamma_eq_logDeriv_Gamma]
  exact (deriv_log_comp_eq_logDeriv (differentiableAt_Gamma_of_pos hx)
    (Gamma_pos_of_pos hx).ne').symm

/-- `log (x - 1) ≤ ψ(x) ≤ log x` for `x > 1`, from the convexity of `log Γ`. -/
theorem log_sub_one_le_digamma_le_log {x : ℝ} (hx : 1 < x) :
    log (x - 1) ≤ digamma x ∧ digamma x ≤ log x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hprev : (0 : ℝ) < x - 1 := by linarith
  have hdiff := differentiableAt_log_comp_Gamma hx0
  rw [digamma_eq_deriv_log_comp_Gamma hx0]
  constructor
  · have hrec := log_comp_Gamma_add_one hprev
    rw [show x - 1 + 1 = x by ring] at hrec
    have hconv := convexOn_log_Gamma.slope_le_deriv (mem_Ioi.2 hprev) (mem_Ioi.2 hx0)
      (by linarith) hdiff
    rw [slope_def_field, show x - (x - 1) = (1 : ℝ) by ring, div_one, hrec] at hconv
    simpa using hconv
  · have hrec := log_comp_Gamma_add_one hx0
    have hconv := convexOn_log_Gamma.deriv_le_slope (mem_Ioi.2 hx0)
      (mem_Ioi.2 (by linarith : (0 : ℝ) < x + 1)) (by linarith) hdiff
    rw [slope_def_field, show x + 1 - x = (1 : ℝ) by ring, div_one, hrec] at hconv
    simpa using hconv

/-- `ψ(x) - log x → 0` as `x → ∞`. -/
theorem tendsto_digamma_sub_log_atTop :
    Tendsto (fun x : ℝ ↦ digamma x - log x) atTop (𝓝 (0 : ℝ)) := by
  have hlower : Tendsto (fun x : ℝ ↦ log (x - 1) - log x) atTop (𝓝 (0 : ℝ)) := by
    have hargument : Tendsto (fun x : ℝ ↦ 1 - x⁻¹) atTop (𝓝 (1 : ℝ)) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_inv_atTop_zero
    have hlog : Tendsto (fun x : ℝ ↦ log (1 - x⁻¹)) atTop (𝓝 (0 : ℝ)) := by
      convert! (continuousAt_log one_ne_zero).tendsto.comp hargument using 1
      all_goals simp
    refine hlog.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [← log_div (by linarith) (by linarith)]
    congr 1
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower
    (tendsto_const_nhds (x := (0 : ℝ))) ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact sub_le_sub_right (log_sub_one_le_digamma_le_log hx).1 _
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact sub_nonpos.2 (log_sub_one_le_digamma_le_log hx).2

theorem digamma_add_one {m : ℝ} (hm : 0 < m) : digamma (m + 1) = digamma m + m⁻¹ := by
  rw [digamma_eq_deriv_log_comp_Gamma (show (0 : ℝ) < m + 1 by linarith),
    digamma_eq_deriv_log_comp_Gamma hm, ← deriv_comp_add_const, ← Real.deriv_log,
    ← deriv_add (differentiableAt_log_comp_Gamma hm) (Real.differentiableAt_log hm.ne')]
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [eventually_gt_nhds hm] with x hx
  exact log_comp_Gamma_add_one hx

theorem digamma_add_nat {m : ℝ} (hm : 0 < m) (n : ℕ) :
    digamma (m + (n : ℝ)) = digamma m + ∑ k ∈ Finset.range n, (m + (k : ℝ))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, digamma_add_one (by positivity), ih, Finset.sum_range_succ]
    ring

/-- The Euler/harmonic representation `ψ(m) = lim (log n - ∑_{k ≤ n} (m + k)⁻¹)`. -/
theorem tendsto_digamma_harmonic {m : ℝ} (hm : 0 < m) :
    Tendsto (fun n : ℕ ↦ log (n : ℝ) - ∑ k ∈ Finset.range (n + 1), (m + (k : ℝ))⁻¹) atTop
      (𝓝 (digamma m)) := by
  have h₁ : Tendsto (fun n : ℕ ↦ digamma (m + (n : ℝ) + 1) - log (m + (n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_digamma_sub_log_atTop.comp (tendsto_atTop_add_const_right _ 1
      (tendsto_atTop_add_const_left _ m tendsto_natCast_atTop_atTop))
  have hratio : Tendsto (fun n : ℕ ↦ (m + (n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 1) := by
    have h : Tendsto (fun n : ℕ ↦ 1 + (m + 1) * (n : ℝ)⁻¹) atTop (𝓝 1) := by
      simpa using ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (m + 1)).const_add 1
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    field_simp
    ring
  have h₂ : Tendsto (fun n : ℕ ↦ log (m + (n : ℝ) + 1) - log (n : ℝ)) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ ↦ log ((m + (n : ℝ) + 1) / (n : ℝ))) atTop (𝓝 0) := by
      simpa using hratio.log one_ne_zero
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact log_div (by positivity) (Nat.cast_ne_zero.mpr hn.ne')
  have hzero : Tendsto (fun n : ℕ ↦ -((digamma (m + (n : ℝ) + 1) - log (m + (n : ℝ) + 1)) +
      (log (m + (n : ℝ) + 1) - log (n : ℝ))) + digamma m) atTop (𝓝 (digamma m)) := by
    simpa using (h₁.add h₂).neg.add_const (digamma m)
  refine hzero.congr' ?_
  filter_upwards [] with n
  have hrec := digamma_add_nat hm (n + 1)
  push_cast at hrec
  rw [show m + ((n : ℝ) + 1) = m + (n : ℝ) + 1 by ring] at hrec
  linarith

theorem _root_.Complex.continuousOn_digamma_re_pos :
    ContinuousOn Complex.digamma {z : ℂ | 0 < z.re} := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hgamma : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := fun z hz ↦ by
    refine (Complex.differentiableAt_Gamma _ fun n h ↦ ?_).differentiableWithinAt
    have hre := congrArg Complex.re h
    have hz' : 0 < z.re := hz
    simp at hre
    linarith [Nat.cast_nonneg (α := ℝ) n]
  refine ContinuousOn.congr ((hgamma.deriv hopen).continuousOn.div hgamma.continuousOn
    fun z hz ↦ Complex.Gamma_ne_zero_of_re_pos hz) fun z _ ↦ ?_
  rw [Complex.digamma_def, logDeriv_apply]
  rfl

theorem continuousOn_digamma_Ioi : ContinuousOn digamma (Ioi (0 : ℝ)) := by
  have hmap : MapsTo (fun x : ℝ ↦ (x : ℂ)) (Ioi (0 : ℝ)) {z : ℂ | 0 < z.re} :=
    fun x hx ↦ by simpa using hx
  exact Complex.continuous_re.continuousOn.comp (Complex.continuousOn_digamma_re_pos.comp
    Complex.continuous_ofReal.continuousOn hmap) fun x _ ↦ mem_univ _

end Real
