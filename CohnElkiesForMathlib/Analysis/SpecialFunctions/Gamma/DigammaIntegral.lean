import CohnElkiesForMathlib.Analysis.SpecialFunctions.FrullaniIntegral
import CohnElkiesForMathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Gauss's integral representation of the digamma function

For `m > 0`, `ψ(m) = ∫₀^∞ (e^{-t} / t - e^{-mt} / (1 - e^{-t})) dt` (`Real.digamma_eq_integral`;
a TODO of Mathlib's `Mathlib.Analysis.SpecialFunctions.Gamma.Digamma`).

The proof starts from the harmonic representation
`ψ(m) = lim_n (log n - ∑_{k ≤ n} (m + k)⁻¹)` (`Real.tendsto_digamma_harmonic`). By the Frullani
formula `log n = ∫₀^∞ (e^{-t} - e^{-nt}) / t dt` and the Laplace integrals
`(m + k)⁻¹ = ∫₀^∞ e^{-(m+k)t} dt`, the `n`-th term is the integral over `(0, ∞)` of the
approximant `(e^{-t} - e^{-nt}) / t - ∑_{k ≤ n} e^{-(m+k)t}`. Summing the geometric series, the
approximant is Gauss's integrand minus `e^{-nt} g(t)` with the remainder
`g(t) = 1 / t - e^{-(m+1)t} / (1 - e^{-t})`, which satisfies `0 ≤ g ≤ m + 1` on `(0, ∞)`; the
error term is therefore at most `(m + 1) / n` in absolute value, and letting `n → ∞` gives the
integral representation (and the integrability of Gauss's integrand).
-/

open Filter MeasureTheory Set
open scoped Topology

namespace Real

noncomputable section

/-- The integrand `e^{-t} / t - e^{-mt} / (1 - e^{-t})` of Gauss's digamma integral. -/
def digammaKernel (m t : ℝ) : ℝ := exp (-t) / t - exp (-m * t) / (1 - exp (-t))

/-- The remainder `1 / t - e^{-(m+1)t} / (1 - e^{-t})`, bounded by `m + 1` on `(0, ∞)`. -/
def digammaRemainder (m t : ℝ) : ℝ := t⁻¹ - exp (-(m + 1) * t) / (1 - exp (-t))

/-- The `n`-th approximant `(e^{-t} - e^{-nt}) / t - ∑_{k ≤ n} e^{-(m+k)t}` of Gauss's integrand;
its integral over `(0, ∞)` is `log n - ∑_{k ≤ n} (m + k)⁻¹`. -/
def digammaApproximant (m : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  Frullani.expKernel 1 n t - ∑ k ∈ Finset.range (n + 1), exp (-(m + k) * t)

/-- `0 ≤ 1 / t - e^{-(m+1)t} / (1 - e^{-t}) ≤ m + 1` for `t > 0` and `m ≥ 0`: writing
`q = e^{-t}`, `r = e^{-mt}`, the remainder is `(1 - q - t q r) / (t (1 - q))`, and
`1 - q - t q r = (1 - q - q t) + q t (1 - r)` with `1 - q - q t ≤ t (1 - q)` (from `1 - t ≤ q`)
and `q t (1 - r) ≤ m t (1 - q)` (from `1 - r ≤ m t` and `q t ≤ 1 - q`). -/
theorem digammaRemainder_nonneg_and_le {m t : ℝ} (hm : 0 ≤ m) (ht : 0 < t) :
    0 ≤ digammaRemainder m t ∧ digammaRemainder m t ≤ m + 1 := by
  have hq0 : 0 < exp (-t) := exp_pos _
  have hq1 : exp (-t) < 1 := exp_lt_one_iff.mpr (by linarith)
  have hqt : 1 - t ≤ exp (-t) := by linarith [add_one_le_exp (-t)]
  have hqt' : exp (-t) * t ≤ 1 - exp (-t) := by
    have h := mul_le_mul_of_nonneg_left (add_one_le_exp t) hq0.le
    rw [← exp_add, neg_add_cancel, exp_zero] at h
    linarith
  have hr1 : exp (-m * t) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
  have hrt : 1 - m * t ≤ exp (-m * t) := by linarith [add_one_le_exp (-m * t)]
  have hE : exp (-(m + 1) * t) = exp (-m * t) * exp (-t) := by
    rw [← exp_add]
    ring_nf
  have hden : 0 < t * (1 - exp (-t)) := mul_pos ht (sub_pos.mpr hq1)
  have hkey : digammaRemainder m t =
      (1 - exp (-t) - t * (exp (-m * t) * exp (-t))) / (t * (1 - exp (-t))) := by
    have hne : 1 - exp (-t) ≠ 0 := (sub_pos.mpr hq1).ne'
    unfold digammaRemainder
    rw [hE]
    field_simp
  rw [hkey]
  constructor
  · refine div_nonneg ?_ hden.le
    have h := mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hq0.le hr1) ht.le
    linarith
  · rw [div_le_iff₀ hden]
    have h2 : exp (-t) * t * (1 - exp (-m * t)) ≤ m * t * (1 - exp (-t)) :=
      calc exp (-t) * t * (1 - exp (-m * t)) ≤ exp (-t) * t * (m * t) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = m * t * (exp (-t) * t) := by ring
        _ ≤ m * t * (1 - exp (-t)) := mul_le_mul_of_nonneg_left hqt' (by positivity)
    linarith

/-- The finite geometric sum
`∑_{k ≤ n} e^{-(m+k)t} = e^{-mt} (1 - (e^{-t})^(n+1)) / (1 - e^{-t})`. -/
theorem sum_exp_neg_add_mul {t : ℝ} (ht : 0 < t) (m : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), exp (-(m + k) * t) =
      exp (-m * t) * (1 - exp (-t) ^ (n + 1)) / (1 - exp (-t)) := by
  have hq1 : exp (-t) ≠ 1 := (exp_lt_one_iff.mpr (by linarith)).ne
  have hterm (k : ℕ) : exp (-(m + k) * t) = exp (-m * t) * exp (-t) ^ k := by
    rw [← exp_nat_mul, ← exp_add]
    ring_nf
  simp_rw [hterm]
  rw [← Finset.mul_sum, geom_sum_eq hq1, mul_div_assoc, ← neg_div_neg_eq, neg_sub, neg_sub]

/-- The `n`-th approximant is Gauss's integrand minus `e^{-nt}` times the remainder. -/
theorem digammaApproximant_eq {t : ℝ} (ht : 0 < t) (m : ℝ) (n : ℕ) :
    digammaApproximant m n t = digammaKernel m t - exp (-n * t) * digammaRemainder m t := by
  have hq1 : 1 - exp (-t) ≠ 0 := (sub_pos.mpr (exp_lt_one_iff.mpr (by linarith))).ne'
  have hn : exp (-(n : ℝ) * t) = exp (-t) ^ n := by
    rw [← exp_nat_mul]
    ring_nf
  have hE : exp (-(m + 1) * t) = exp (-m * t) * exp (-t) := by
    rw [← exp_add]
    ring_nf
  unfold digammaApproximant digammaKernel digammaRemainder Frullani.expKernel
  rw [sum_exp_neg_add_mul ht m n, hn, hE, neg_one_mul]
  field_simp
  ring

theorem integrableOn_digammaApproximant {m : ℝ} (hm : 0 < m) {n : ℕ} (hn : 1 ≤ n) :
    IntegrableOn (digammaApproximant m n) (Ioi 0) :=
  (Frullani.integrableOn_expKernel one_pos (by exact_mod_cast hn)).sub
    (integrable_finsetSum _ fun k _ ↦ integrableOn_exp_neg_mul_Ioi (by positivity))

/-- `∫₀^∞ ((e^{-t} - e^{-nt}) / t - ∑_{k ≤ n} e^{-(m+k)t}) dt = log n - ∑_{k ≤ n} (m + k)⁻¹`, by
the Frullani formula and the Laplace integrals. -/
theorem integral_digammaApproximant {m : ℝ} (hm : 0 < m) {n : ℕ} (hn : 1 ≤ n) :
    ∫ t in Ioi (0 : ℝ), digammaApproximant m n t =
      log n - ∑ k ∈ Finset.range (n + 1), (m + k)⁻¹ := by
  have hk (k : ℕ) : (0 : ℝ) < m + k := by positivity
  unfold digammaApproximant
  rw [integral_sub (Frullani.integrableOn_expKernel one_pos (by exact_mod_cast hn))
      (integrable_finsetSum _ fun k _ ↦ integrableOn_exp_neg_mul_Ioi (hk k)),
    Frullani.integral_expKernel one_pos (by exact_mod_cast hn), div_one,
    integral_finsetSum _ fun k _ ↦ integrableOn_exp_neg_mul_Ioi (hk k)]
  congr 1
  exact Finset.sum_congr rfl fun k _ ↦ integral_exp_neg_mul_Ioi (hk k)

theorem norm_exp_neg_mul_mul_digammaRemainder_le {m t : ℝ} (hm : 0 ≤ m) (ht : 0 < t) (a : ℝ) :
    ‖exp (-a * t) * digammaRemainder m t‖ ≤ (m + 1) * exp (-a * t) := by
  obtain ⟨h0, h1⟩ := digammaRemainder_nonneg_and_le hm ht
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (exp_pos _).le h0), mul_comm]
  exact mul_le_mul_of_nonneg_right h1 (exp_pos _).le

theorem integrableOn_exp_neg_mul_mul_digammaRemainder {m a : ℝ} (hm : 0 ≤ m) (ha : 0 < a) :
    IntegrableOn (fun t ↦ exp (-a * t) * digammaRemainder m t) (Ioi 0) := by
  refine ((integrableOn_exp_neg_mul_Ioi ha).const_mul (m + 1)).mono' ?_ ?_
  · exact (by unfold digammaRemainder; fun_prop :
      Measurable fun t : ℝ ↦ exp (-a * t) * digammaRemainder m t).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_exp_neg_mul_mul_digammaRemainder_le hm ht a

/-- The error term is small: `|∫₀^∞ e^{-at} g(t) dt| ≤ (m + 1) / a`. -/
theorem norm_integral_exp_neg_mul_mul_digammaRemainder_le {m a : ℝ} (hm : 0 ≤ m) (ha : 0 < a) :
    ‖∫ t in Ioi (0 : ℝ), exp (-a * t) * digammaRemainder m t‖ ≤ (m + 1) * a⁻¹ := by
  rw [← integral_exp_neg_mul_Ioi ha, ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((integrableOn_exp_neg_mul_Ioi ha).const_mul (m + 1)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_exp_neg_mul_mul_digammaRemainder_le hm ht a

/-- Gauss's integrand `e^{-t} / t - e^{-mt} / (1 - e^{-t})` is integrable on `(0, ∞)`. -/
theorem integrableOn_digammaKernel {m : ℝ} (hm : 0 < m) :
    IntegrableOn (digammaKernel m) (Ioi 0) := by
  refine ((integrableOn_digammaApproximant hm le_rfl).add
    (integrableOn_exp_neg_mul_mul_digammaRemainder hm.le (Nat.cast_pos.mpr one_pos))).congr_fun
    (fun t ht ↦ ?_) measurableSet_Ioi
  simp only [Pi.add_apply]
  rw [digammaApproximant_eq ht]
  ring

/-- Gauss's integral representation of the digamma function, in terms of `digammaKernel`. -/
theorem digamma_eq_integral_digammaKernel {m : ℝ} (hm : 0 < m) :
    digamma m = ∫ t in Ioi (0 : ℝ), digammaKernel m t := by
  refine tendsto_nhds_unique (tendsto_digamma_harmonic hm) ?_
  have hbound : Tendsto (fun n : ℕ ↦ (m + 1) * (n : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (m + 1)
  have hrem : Tendsto (fun n : ℕ ↦ ∫ t in Ioi (0 : ℝ), exp (-(n : ℝ) * t) * digammaRemainder m t)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact norm_integral_exp_neg_mul_mul_digammaRemainder_le hm.le (Nat.cast_pos.mpr hn)
  have hlim := (tendsto_const_nhds (x := ∫ t in Ioi (0 : ℝ), digammaKernel m t)).sub hrem
  rw [sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [← integral_digammaApproximant hm hn,
    ← integral_sub (integrableOn_digammaKernel hm)
      (integrableOn_exp_neg_mul_mul_digammaRemainder hm.le (Nat.cast_pos.mpr hn))]
  exact setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ (digammaApproximant_eq ht m n).symm

/-- Gauss's integral representation of the digamma function. -/
theorem digamma_eq_integral {m : ℝ} (hm : 0 < m) :
    digamma m = ∫ t in Ioi (0 : ℝ), (exp (-t) / t - exp (-m * t) / (1 - exp (-t))) :=
  digamma_eq_integral_digammaKernel hm

/-- The integrand of Gauss's digamma integral is integrable on `(0, ∞)`. -/
theorem integrableOn_digamma_integrand {m : ℝ} (hm : 0 < m) :
    IntegrableOn (fun t : ℝ ↦ exp (-t) / t - exp (-m * t) / (1 - exp (-t))) (Ioi 0) :=
  integrableOn_digammaKernel hm

end

end Real
