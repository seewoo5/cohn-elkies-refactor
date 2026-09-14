import Mathlib

/-!
# The real digamma function

`Real.digamma := logDeriv Real.Gamma` is the logarithmic derivative `ψ = Γ'/Γ` of the real Gamma
function. For `x > 0` it agrees with `(log ∘ Γ)' x` and with the real part of `Complex.digamma x`.
We prove the recurrence `ψ(x + 1) = ψ(x) + 1/x`, the bounds `log (x - 1) ≤ ψ(x) ≤ log x` for
`x > 1` (from the log-convexity of `Γ`), the asymptotics `ψ(x) - log x → 0` as `x → ∞`, the
harmonic representation `ψ(m) = lim (log n - ∑_{k ≤ n} (m + k)⁻¹)` and the continuity of `ψ` on
`(0, ∞)`.
-/

open Filter Real Set
open scoped Topology

namespace Real

/-- The digamma function `ψ = Γ'/Γ = (log Γ)'`. -/
noncomputable def digamma : ℝ → ℝ := logDeriv Gamma

theorem digamma_def : digamma = logDeriv Gamma := rfl

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
    digamma x = deriv (log ∘ Gamma) x :=
  (deriv_log_comp_eq_logDeriv (differentiableAt_Gamma_of_pos hx) (Gamma_pos_of_pos hx).ne').symm

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

/-- For `x > 0`, the real digamma function is the real part of the complex one. -/
theorem digamma_eq_complex_re {x : ℝ} (hx : 0 < x) : digamma x = (Complex.digamma (x : ℂ)).re := by
  have hcomplex : DifferentiableAt ℂ Complex.Gamma (x : ℂ) := by
    refine Complex.differentiableAt_Gamma _ fun n h ↦ ?_
    have hre := congrArg Complex.re h
    simp at hre
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hreal : HasDerivAt Real.Gamma (deriv Complex.Gamma (x : ℂ)).re x := by
    simpa only [Complex.Gamma_ofReal, Complex.ofReal_re] using hcomplex.hasDerivAt.real_of_complex
  unfold digamma
  rw [logDeriv_apply, hreal.deriv, Complex.digamma_def, logDeriv_apply, Complex.Gamma_ofReal,
    Complex.div_ofReal_re]

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
  exact (Complex.continuous_re.continuousOn.comp (Complex.continuousOn_digamma_re_pos.comp
    Complex.continuous_ofReal.continuousOn hmap) fun x _ ↦ mem_univ _).congr
    fun x hx ↦ digamma_eq_complex_re hx

end Real
