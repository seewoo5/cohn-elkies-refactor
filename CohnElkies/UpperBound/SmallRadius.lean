import CohnElkies.UpperBound.SaddleDamping
import CohnElkies.UpperBound.FourierPair
import CohnElkiesForMathlib.Analysis.SpecialFunctions.FrullaniIntegral
import CohnElkiesForMathlib.Analysis.SpecialFunctions.Gamma.Beta
import CohnElkiesForMathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The sign of `f₊` at small radii (report §4.3, Lemmas 4.4 and 4.7)

The saddle contour `z = λ(1 + u) - iλT` with its shell and Gamma arguments, the small-radius
ordinate `u_*` and radius `r_*`, the truncation `N_λ` of the residue series and the relative error
of the truncated residue sum on `r ≤ r_*`, the negative-contour estimates (Gamma reflection,
short-shell damping on the negative contour), the Laplace-type identities for the Gamma damping
(via complex Frullani integrals), and the conclusion `Re f₊(r) > 0` for `0 ≤ r ≤ r_*`, eventually
in `d` (`eventually_plusSaddleProfile_re_pos_on_star`).
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory Real Set
open scoped Topology

/-- The Mellin contour point `z = λ(1 + u) - iλT` of the saddle-point analysis. -/
def z_contour (ℓ u T : ℝ) : ℂ := (ℓ * (1 + u) : ℝ) - I * (ℓ * T : ℝ)

theorem saddleSourceMellinContour_shellArgument {ℓ : ℝ} (hℓ : 0 < ℓ) (u T : ℝ) :
    I * (z_contour ℓ u T - (ℓ : ℂ)) / (ℓ : ℂ) = (T : ℂ) + I * (u : ℂ) := by
  have hℓcomplex : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  unfold z_contour
  push_cast
  field_simp
  ring_nf
  simp [Complex.I_sq]

theorem saddleSourceMellinContour_gammaArgument (ℓ u T : ℝ) :
    z_contour ℓ u T / 2 = (ℓ * (1 + u) / 2 : ℂ) - I * (ℓ * T / 2 : ℂ) := by
  unfold z_contour
  push_cast
  ring

/-- Report (81): on the contour, `|e^{λ h_ε}| = e^{λ h_ε(iu)} e^{-(D_B - D_s)}`. -/
theorem norm_saddleShellExponential_eq_exp_neg_damping {ε : ℝ} (hε : 0 < ε)
    (horder : a₀ε ε ≤ Aε ε) (ℓ T u : ℝ) :
    ‖Complex.exp ((ℓ : ℂ) * h_ε ε ((T : ℂ) + I * (u : ℂ)))‖ =
      exp (ℓ * h_εI ε u) * exp (-(D_B ε ℓ (u - 1) T - D_s ε ℓ (u - 1) T)) := by
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [← exp_add]
  congr 1
  linarith [saddleShellPhase_damping_identity hε horder ℓ T u]

/-- The derivative `h_ε'(u)` of the real shell phase, report (79). -/
def saddleSourceShellDerivative (ε u : ℝ) : ℝ :=
  (∫ a in a₀ε ε..Aε ε, w_s ε a * a * sinh (u * a)) +
    ∫ a in Bε ε..Bε ε + 1, w_B ε a * a * sinh (u * a)

theorem saddleSourceShellDerivative_neg_one (ε : ℝ) :
    saddleSourceShellDerivative ε (-1) = -h₁' ε := by
  simp only [saddleSourceShellDerivative, h₁', neg_one_mul, sinh_neg, mul_neg,
    intervalIntegral.integral_neg]
  ring

theorem saddleLogRadius_eq_digamma_add_shellDerivative (ε : ℝ) (d : ℕ) (u : ℝ) :
    logRadius ε d u =
      -log π / 2 + Real.digamma ((d / 2 : ℝ) * (1 + u) / 2) / 2 +
        saddleSourceShellDerivative ε u := by
  unfold logRadius saddleSourceShellDerivative
  ring

/-- Report Lemma 4.10: the near-optimal contour height `u_* = -1 + (log λ)/(4λ)`, `λ = d/2`. -/
def u_star (_ε : ℝ) (d : ℕ) : ℝ := -1 + log (d / 2 : ℝ) / (4 * (d / 2 : ℝ))

/-- Report Lemma 4.10: the small radius `r_*` at which positivity of `f₊` is proved. -/
def r_star (ε : ℝ) (d : ℕ) : ℝ := exp (logRadius ε d (u_star ε d))

theorem saddleSmallRadiusStar_pos (ε : ℝ) (d : ℕ) : 0 < r_star ε d := exp_pos _

theorem saddleSmallRadiusStar_gammaArgument {d : ℕ} (hd : 0 < d) (ε : ℝ) :
    (d / 2 : ℝ) * (1 + u_star ε d) / 2 = log (d / 2 : ℝ) / 8 := by
  have hdreal : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  unfold u_star
  field_simp
  ring

theorem saddleSourceShellDerivative_contDiff_one {ε : ℝ} (hε : 0 < ε) (horder : a₀ε ε ≤ Aε ε) :
    ContDiff ℝ (1 : WithTop ℕ∞) (saddleSourceShellDerivative ε) := by
  have hphase : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) (h_εI ε) :=
    realHyperbolicShellPhase_contDiff hε horder _
  have heq : saddleSourceShellDerivative ε = deriv (h_εI ε) := by
    funext u
    unfold saddleSourceShellDerivative
    simpa [mul_comm] using (realHyperbolicShellPhase_hasDerivAt hε horder u).deriv.symm
  rw [heq]
  exact (contDiff_succ_iff_deriv.mp hphase).2.2

theorem saddleSmallRadiusVariable_star_eq {ε : ℝ} {d : ℕ} (hd : 0 < d) :
    y_r ε (r_star ε d) = exp (Real.digamma (log (d / 2 : ℝ) / 8) +
      2 * (h₁' ε + saddleSourceShellDerivative ε (u_star ε d))) := by
  have hpi : π = exp (log π) := (exp_log pi_pos).symm
  have hsq : ∀ x : ℝ, exp x ^ 2 = exp (2 * x) := fun x ↦ by rw [two_mul, exp_add, sq]
  unfold y_r r_star
  rw [saddleLogRadius_eq_digamma_add_shellDerivative, saddleSmallRadiusStar_gammaArgument hd ε]
  nth_rw 1 [hpi]
  rw [hsq, ← exp_add, ← exp_add]
  congr 1
  ring

theorem exists_saddleSourceShellDerivative_endpoint_bound {ε : ℝ} (hε : 0 < ε)
    (horder : a₀ε ε ≤ Aε ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Icc (-1 : ℝ) 0,
      |h₁' ε + saddleSourceShellDerivative ε u| ≤ C * (u + 1) := by
  have hcont : ContDiffOn ℝ ((0 : WithTop ℕ∞) + 1) (saddleSourceShellDerivative ε)
      (Icc (-1 : ℝ) 0) := by
    simpa using (saddleSourceShellDerivative_contDiff_one hε horder).contDiffOn
  obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound (f := saddleSourceShellDerivative ε)
    (n := 0) (by norm_num : (-1 : ℝ) ≤ 0) hcont
  refine ⟨max C 0, le_max_right _ _, fun u hu ↦ ?_⟩
  have hbound := hC u hu
  simp only [taylor_within_zero_eval, Real.norm_eq_abs, Nat.zero_add, pow_one,
    saddleSourceShellDerivative_neg_one, sub_neg_eq_add] at hbound
  rw [add_comm (h₁' ε)]
  exact hbound.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith [hu.1]))

theorem saddle_log_sq_le_four_mul {x : ℝ} (hx : 1 ≤ x) : log x ^ 2 ≤ 4 * x := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hhalf : log x / 2 ≤ √x - 1 := by
    rw [← log_sqrt hxpos.le]
    exact log_le_sub_one_of_pos (sqrt_pos.2 hxpos)
  nlinarith [log_nonneg hx, sq_sqrt hxpos.le, sqrt_nonneg x]

/-- Report Lemma 4.10: on `[0, r_*]` the variable `y_r` stays below `(log λ)/8 + C`. -/
theorem exists_eventually_y_star_le_log_eighth_add {ε : ℝ} (hε : 0 < ε)
    (horder : a₀ε ε ≤ Aε ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ d : ℕ in atTop, ∀ r : ℝ, 0 ≤ r → r ≤ r_star ε d →
      y_r ε r ≤ log (d / 2 : ℝ) / 8 + C := by
  obtain ⟨K, hK, hKbound⟩ := exists_saddleSourceShellDerivative_endpoint_bound hε horder
  have key : ∀ m q : ℝ, 0 ≤ q → q ≤ 1 / 4 → 0 < m → m * (2 * K * q) ≤ K / 4 →
      m * exp (2 * K * q) ≤ m + K / 4 * exp (K / 2) := by
    intro m q hq0 hq4 hm hmz
    have hz : (0 : ℝ) ≤ 2 * K * q := by positivity
    have hzu : 2 * K * q ≤ K / 2 := by nlinarith
    have hexp : exp (2 * K * q) - 1 ≤ 2 * K * q * exp (2 * K * q) := by
      have h := abs_exp_sub_one_le_abs_mul_exp_abs (2 * K * q)
      rwa [abs_of_nonneg (by simpa using exp_le_exp.mpr hz), abs_of_nonneg hz] at h
    have h1 := mul_le_mul_of_nonneg_left hexp hm.le
    have h2 : m * (2 * K * q) * exp (2 * K * q) ≤ K / 4 * exp (K / 2) :=
      mul_le_mul hmz (exp_le_exp.mpr hzu) (exp_pos _).le (by linarith)
    linarith
  refine ⟨K / 4 * exp (K / 2), by positivity, ?_⟩
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_gt_atTop (2 * exp 8))] with d hd r hr hrstar
  have he8 : (9 : ℝ) ≤ exp 8 := by linarith [add_one_le_exp (8 : ℝ)]
  have hℓone : (1 : ℝ) < (d : ℝ) / 2 := by linarith
  have hℓ : (0 : ℝ) < (d : ℝ) / 2 := by linarith
  have hℓne : ((d : ℝ) / 2) ≠ 0 := hℓ.ne'
  have hd0 : 0 < d := by exact_mod_cast (by linarith : (0 : ℝ) < (d : ℝ))
  have hlog : 8 < log (d / 2 : ℝ) := (lt_log_iff_exp_lt hℓ).2 (by linarith)
  have hq0 : 0 ≤ log (d / 2 : ℝ) / (4 * (d / 2 : ℝ)) :=
    div_nonneg (log_nonneg hℓone.le) (by linarith)
  have hq4 : log (d / 2 : ℝ) / (4 * (d / 2 : ℝ)) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 4 * ((d : ℝ) / 2))]
    linarith [log_le_sub_one_of_pos hℓ]
  have hstar : u_star ε d + 1 = log (d / 2 : ℝ) / (4 * (d / 2 : ℝ)) := by unfold u_star; ring
  have hshell : h₁' ε + saddleSourceShellDerivative ε (u_star ε d) ≤
      K * (log (d / 2 : ℝ) / (4 * (d / 2 : ℝ))) := by
    have h := (le_abs_self _).trans (hKbound _ ⟨by linarith, by linarith⟩)
    rwa [hstar] at h
  have hmz : log (d / 2 : ℝ) / 8 * (2 * K * (log (d / 2 : ℝ) / (4 * (d / 2 : ℝ)))) ≤ K / 4 := by
    rw [show log (d / 2 : ℝ) / 8 * (2 * K * (log (d / 2 : ℝ) / (4 * (d / 2 : ℝ)))) =
        K * log (d / 2 : ℝ) ^ 2 / (16 * (d / 2 : ℝ)) by field_simp; ring,
      div_le_iff₀ (by linarith : (0 : ℝ) < 16 * ((d : ℝ) / 2))]
    linarith [mul_le_mul_of_nonneg_left (saddle_log_sq_le_four_mul hℓone.le) hK]
  calc y_r ε r ≤ y_r ε (r_star ε d) := by unfold y_r; gcongr
    _ = exp (Real.digamma (log (d / 2 : ℝ) / 8) +
          2 * (h₁' ε + saddleSourceShellDerivative ε (u_star ε d))) :=
        saddleSmallRadiusVariable_star_eq hd0
    _ ≤ exp (log (log (d / 2 : ℝ) / 8) + 2 * K * (log (d / 2 : ℝ) / (4 * (d / 2 : ℝ)))) :=
        exp_le_exp.2 (by
          linarith [(Real.log_sub_one_le_digamma_le_log (by linarith : 1 < log (d / 2 : ℝ) / 8)).2])
    _ = log (d / 2 : ℝ) / 8 * exp (2 * K * (log (d / 2 : ℝ) / (4 * (d / 2 : ℝ)))) := by
        rw [exp_add, exp_log (by linarith)]
    _ ≤ log (d / 2 : ℝ) / 8 + K / 4 * exp (K / 2) := key _ _ hq0 hq4 (by linarith) hmz

/-- Report Lemma 4.10: the truncation order `N_λ = ⌈log λ⌉` of the residue series. -/
def N_ℓ (ℓ : ℝ) : ℕ := ⌈log ℓ⌉₊

theorem saddleSmallResidueTruncation_lower (ℓ : ℝ) : log ℓ ≤ (N_ℓ ℓ : ℝ) := Nat.le_ceil _

theorem saddleSmallResidueTruncation_upper {ℓ : ℝ} (hℓ : 1 ≤ ℓ) : (N_ℓ ℓ : ℝ) ≤ log ℓ + 1 :=
  (Nat.ceil_lt_add_one (log_nonneg hℓ)).le

theorem tendsto_log_pow_div_atTop (n : ℕ) : Tendsto (fun ℓ : ℝ ↦ log ℓ ^ n / ℓ) atTop (𝓝 0) := by
  simpa using tendsto_pow_log_div_mul_add_atTop 1 0 n one_ne_zero

theorem tendsto_saddleSmallResidueTruncation_div :
    Tendsto (fun ℓ : ℝ ↦ (N_ℓ ℓ : ℝ) / ℓ) atTop (𝓝 0) := by
  have h : Tendsto (fun ℓ : ℝ ↦ (log ℓ + 1) / ℓ) atTop (𝓝 0) := by
    have h := (tendsto_log_pow_div_atTop 1).add (tendsto_log_pow_div_atTop 0)
    simp only [add_zero] at h
    exact h.congr fun ℓ ↦ by ring
  refine squeeze_zero' ?_ ?_ h
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with ℓ hℓ
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with ℓ hℓ
    exact div_le_div_of_nonneg_right (saddleSmallResidueTruncation_upper hℓ) (by linarith)

theorem tendsto_saddleSmallResidueTruncation_sq_div :
    Tendsto (fun ℓ : ℝ ↦ (N_ℓ ℓ : ℝ) ^ 2 / ℓ) atTop (𝓝 0) := by
  have h : Tendsto (fun ℓ : ℝ ↦ (log ℓ + 1) ^ 2 / ℓ) atTop (𝓝 0) := by
    have h := ((tendsto_log_pow_div_atTop 2).add
      ((tendsto_log_pow_div_atTop 1).const_mul 2)).add (tendsto_log_pow_div_atTop 0)
    simp only [mul_zero, add_zero] at h
    exact h.congr fun ℓ ↦ by ring
  refine squeeze_zero' ?_ ?_ h
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with ℓ hℓ
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with ℓ hℓ
    refine div_le_div_of_nonneg_right ?_ (by linarith)
    exact (sq_le_sq₀ (Nat.cast_nonneg _) (by nlinarith [log_nonneg hℓ])).mpr
      (saddleSmallResidueTruncation_upper hℓ)

theorem eventually_saddleSmallResidueTruncation_succ_double_le :
    ∀ᶠ ℓ : ℝ in atTop, 2 * ((N_ℓ ℓ + 1 : ℕ) : ℝ) ≤ ℓ := by
  filter_upwards [tendsto_saddleSmallResidueTruncation_div.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)), eventually_ge_atTop (4 : ℝ)] with ℓ hratio hℓ
  have h := (div_lt_iff₀ (by linarith : (0 : ℝ) < ℓ)).mp hratio
  push_cast
  linarith

theorem eventually_saddleSmallResidueTruncation_dominates_window {C : ℝ} :
    ∀ᶠ ℓ : ℝ in atTop, ∀ y : ℝ, 0 ≤ y → y ≤ log ℓ / 8 + C → 2 * y ≤ (N_ℓ ℓ : ℝ) + 2 := by
  filter_upwards [tendsto_log_atTop.eventually (eventually_ge_atTop (8 * C / 3))]
    with ℓ hlog y hy hyupper
  linarith [saddleSmallResidueTruncation_lower ℓ]

theorem saddleExpSeries_term_le_exp_mul_half_pow {y : ℝ} (hy : 0 ≤ y) (m : ℕ) :
    y ^ m / (m.factorial : ℝ) ≤ exp (2 * y) * (1 / 2 : ℝ) ^ m := by
  have hterm : (2 * y) ^ m / (m.factorial : ℝ) ≤ exp (2 * y) := by
    simpa using sum_le_hasSum ({m} : Finset ℕ) (fun n _ ↦ by positivity)
      (saddleExpSeries_hasSum (2 * y))
  calc y ^ m / (m.factorial : ℝ) = (2 * y) ^ m / (m.factorial : ℝ) * (1 / 2 : ℝ) ^ m := by
        rw [div_mul_eq_mul_div, ← mul_pow]
        ring_nf
    _ ≤ exp (2 * y) * (1 / 2 : ℝ) ^ m := mul_le_mul_of_nonneg_right hterm (by positivity)

theorem saddleSmallResidueTruncation_half_pow_le (ℓ : ℝ) :
    (1 / 2 : ℝ) ^ (N_ℓ ℓ + 1) ≤ exp (-1 / 2 * log ℓ) := by
  have hhalf : log (1 / 2 : ℝ) ≤ -(1 / 2 : ℝ) := by
    linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hlower : log ℓ ≤ ((N_ℓ ℓ + 1 : ℕ) : ℝ) := by
    push_cast
    linarith [saddleSmallResidueTruncation_lower ℓ]
  have hnonneg : (0 : ℝ) ≤ ((N_ℓ ℓ + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [show ((1 : ℝ) / 2) ^ (N_ℓ ℓ + 1) = exp (((N_ℓ ℓ + 1 : ℕ) : ℝ) * log (1 / 2 : ℝ)) by
    rw [exp_nat_mul, exp_log (by norm_num)]]
  exact exp_le_exp.mpr (by nlinarith)

/-- Majorant for the factorial tail of the truncated residue series. -/
def saddleSmallResidueTailMajorant (C ℓ : ℝ) : ℝ := exp (3 * C - 1 / 8 * log ℓ)

theorem saddleSmallResidue_tail_le_majorant {C ℓ y c : ℝ} {m : ℕ} (hy : 0 ≤ y)
    (hyupper : y ≤ log ℓ / 8 + C) (hcm : (1 / 2 : ℝ) ^ m ≤ c * exp (-1 / 2 * log ℓ)) :
    exp y * (y ^ m / (m.factorial : ℝ)) ≤ c * saddleSmallResidueTailMajorant C ℓ := by
  calc exp y * (y ^ m / (m.factorial : ℝ)) ≤ exp y * (exp (2 * y) * (1 / 2 : ℝ) ^ m) :=
        mul_le_mul_of_nonneg_left (saddleExpSeries_term_le_exp_mul_half_pow hy m) (exp_pos _).le
    _ = exp (3 * y) * (1 / 2 : ℝ) ^ m := by
        rw [← mul_assoc, ← exp_add]
        ring_nf
    _ ≤ exp (3 * (log ℓ / 8 + C)) * (c * exp (-1 / 2 * log ℓ)) :=
        mul_le_mul (exp_le_exp.mpr (by linarith)) hcm (by positivity) (exp_pos _).le
    _ = c * saddleSmallResidueTailMajorant C ℓ := by
        unfold saddleSmallResidueTailMajorant
        rw [show 3 * C - 1 / 8 * log ℓ = 3 * (log ℓ / 8 + C) + -1 / 2 * log ℓ by ring, exp_add]
        ring

theorem tendsto_saddleSmallResidueTailMajorant (C : ℝ) :
    Tendsto (saddleSmallResidueTailMajorant C) atTop (𝓝 0) := by
  have h := (tendsto_exp_atBot.comp (tendsto_log_atTop.const_mul_atTop_of_neg
    (by norm_num : -(1 / 8 : ℝ) < 0))).const_mul (exp (3 * C))
  rw [mul_zero] at h
  refine h.congr fun ℓ ↦ ?_
  simp only [Function.comp_apply, saddleSmallResidueTailMajorant]
  rw [show 3 * C - 1 / 8 * log ℓ = 3 * C + -(1 / 8 : ℝ) * log ℓ by ring, exp_add]

/-- Majorant for the `1/λ` coefficient error of the truncated residue series. -/
def saddleSmallResidueCoefficientMajorant (K C ℓ : ℝ) : ℝ :=
  K * exp (K * (N_ℓ ℓ : ℝ) ^ 2 / ℓ) * (2 * (log ℓ / 8 + C) + (log ℓ / 8 + C) ^ 2) *
    exp (2 * C - 3 / 4 * log ℓ)

theorem saddleSmallResidue_coefficient_le_majorant {K C ℓ y : ℝ} (hK : 0 ≤ K) (hℓ : 1 ≤ ℓ)
    (hy : 0 ≤ y) (hyupper : y ≤ log ℓ / 8 + C) :
    K / ℓ * exp (K * (N_ℓ ℓ : ℝ) ^ 2 / ℓ) * (2 * y + y ^ 2) * exp (2 * y) ≤
      saddleSmallResidueCoefficientMajorant K C ℓ := by
  have hℓpos : 0 < ℓ := lt_of_lt_of_le zero_lt_one hℓ
  have hY : 0 ≤ log ℓ / 8 + C := by linarith [log_nonneg hℓ]
  have hbase : 0 ≤ K / ℓ * exp (K * (N_ℓ ℓ : ℝ) ^ 2 / ℓ) := by positivity
  have hrat : exp (2 * (log ℓ / 8 + C)) / ℓ = exp (2 * C - 3 / 4 * log ℓ) := by
    rw [show 2 * C - 3 / 4 * log ℓ = 2 * (log ℓ / 8 + C) - log ℓ by ring, exp_sub, exp_log hℓpos]
  calc K / ℓ * exp (K * (N_ℓ ℓ : ℝ) ^ 2 / ℓ) * (2 * y + y ^ 2) * exp (2 * y) ≤
        K / ℓ * exp (K * (N_ℓ ℓ : ℝ) ^ 2 / ℓ) *
          (2 * (log ℓ / 8 + C) + (log ℓ / 8 + C) ^ 2) * exp (2 * (log ℓ / 8 + C)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (by nlinarith) hbase)
          (exp_le_exp.mpr (by linarith)) (exp_pos _).le (mul_nonneg hbase (by nlinarith))
    _ = saddleSmallResidueCoefficientMajorant K C ℓ := by
        unfold saddleSmallResidueCoefficientMajorant
        rw [← hrat]
        ring

theorem tendsto_pow_mul_exp_neg_mul_atTop {c : ℝ} (hc : 0 < c) (n : ℕ) :
    Tendsto (fun t : ℝ ↦ t ^ n * exp (-c * t)) atTop (𝓝 0) := by
  have h := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp
    (tendsto_id.const_mul_atTop hc)).const_mul ((c ^ n)⁻¹)
  rw [mul_zero] at h
  refine h.congr fun t ↦ ?_
  simp only [Function.comp_apply, id_eq, mul_pow, neg_mul, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero n hc.ne'), one_mul]

theorem tendsto_saddleLogWindowPolynomial_exp_neg (C : ℝ) :
    Tendsto (fun t : ℝ ↦ (2 * (t / 8 + C) + (t / 8 + C) ^ 2) * exp (-(3 / 4 : ℝ) * t))
      atTop (𝓝 0) := by
  have h := (((tendsto_pow_mul_exp_neg_mul_atTop (by norm_num : (0 : ℝ) < 3 / 4) 2).const_mul
      (1 / 64 : ℝ)).add ((tendsto_pow_mul_exp_neg_mul_atTop
        (by norm_num : (0 : ℝ) < 3 / 4) 1).const_mul (C / 4 + 1 / 4))).add
    ((tendsto_pow_mul_exp_neg_mul_atTop (by norm_num : (0 : ℝ) < 3 / 4) 0).const_mul
      (C ^ 2 + 2 * C))
  simp only [mul_zero, add_zero] at h
  exact h.congr fun t ↦ by ring

theorem tendsto_saddleSmallResidueCoefficientMajorant (K C : ℝ) :
    Tendsto (saddleSmallResidueCoefficientMajorant K C) atTop (𝓝 0) := by
  have hfactor : Tendsto (fun ℓ : ℝ ↦ exp (K * (N_ℓ ℓ : ℝ) ^ 2 / ℓ)) atTop (𝓝 1) := by
    have h := tendsto_saddleSmallResidueTruncation_sq_div.const_mul K
    rw [mul_zero] at h
    simpa using (h.congr fun ℓ ↦ by ring : Tendsto (fun ℓ : ℝ ↦
      K * (N_ℓ ℓ : ℝ) ^ 2 / ℓ) atTop (𝓝 0)).rexp
  have htotal := (hfactor.const_mul K).mul (((tendsto_saddleLogWindowPolynomial_exp_neg C).comp
    tendsto_log_atTop).const_mul (exp (2 * C)))
  simp only [mul_zero] at htotal
  refine htotal.congr fun ℓ ↦ ?_
  simp only [Function.comp_apply, saddleSmallResidueCoefficientMajorant]
  rw [show 2 * C - 3 / 4 * log ℓ = 2 * C + -(3 / 4 : ℝ) * log ℓ by ring, exp_add]
  ring

/-- Majorant for the total relative error of the truncated residue series. -/
def saddleSmallResidueRelativeErrorMajorant (K C ℓ : ℝ) : ℝ :=
  saddleSmallResidueCoefficientMajorant K C ℓ + 2 * saddleSmallResidueTailMajorant C ℓ

theorem tendsto_saddleSmallResidueRelativeErrorMajorant (K C : ℝ) :
    Tendsto (saddleSmallResidueRelativeErrorMajorant K C) atTop (𝓝 0) := by
  have h := (tendsto_saddleSmallResidueCoefficientMajorant K C).add
    ((tendsto_saddleSmallResidueTailMajorant C).const_mul 2)
  simp only [mul_zero, add_zero] at h
  exact h.congr fun ℓ ↦ rfl

/-- Report (79): eventually in `λ` the relative error of the truncated residue series is `< 1/2`. -/
theorem eventually_plusSaddleSmallRadius_relativeFiniteResidue_lt_half {ε : ℝ} (hε : 0 < ε)
    (horder : a₀ε ε ≤ Aε ε) {C : ℝ} :
    ∀ᶠ ℓ : ℝ in atTop, ∀ y : ℝ, 0 ≤ y → y ≤ log ℓ / 8 + C →
      exp y * |(∑ n ∈ Finset.range (N_ℓ ℓ + 1), ((-y) ^ n / (n.factorial : ℝ)) * A_ℓn ε ℓ n) -
        exp (-y)| < 1 / 2 := by
  obtain ⟨K, hK, hfinite⟩ := exists_plusSaddleSmallRadius_relativeFiniteResidue_error hε horder
  filter_upwards [(tendsto_saddleSmallResidueRelativeErrorMajorant K C).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    eventually_saddleSmallResidueTruncation_succ_double_le,
    eventually_saddleSmallResidueTruncation_dominates_window (C := C),
    eventually_ge_atTop (1 : ℝ)] with ℓ hsmall hN hwindow hℓ y hy hyupper
  have hℓpos : 0 < ℓ := lt_of_lt_of_le zero_lt_one hℓ
  have hN' : 2 * (N_ℓ ℓ : ℝ) ≤ ℓ := by push_cast at hN; linarith
  have htail := saddleSmallResidue_tail_le_majorant (m := N_ℓ ℓ + 1) (c := 1) hy hyupper
    (by simpa using saddleSmallResidueTruncation_half_pow_le ℓ)
  rw [one_mul] at htail
  refine lt_of_le_of_lt ((hfinite ℓ hℓpos (N_ℓ ℓ) hN' y hy (hwindow y hy hyupper)).trans ?_) hsmall
  unfold saddleSmallResidueRelativeErrorMajorant
  linarith [saddleSmallResidue_coefficient_le_majorant hK hℓ hy hyupper]

theorem tendsto_saddleResidue_dimension_half : Tendsto (fun d : ℕ ↦ (d : ℝ) / 2) atTop atTop :=
  ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const (by norm_num : (0 : ℝ) < 1 / 2)).congr
    fun d ↦ by ring

theorem eventually_plusSaddleSmallRadius_relativeFiniteResidue_lt_half_on_star {ε : ℝ}
    (hε : 0 < ε) (horder : a₀ε ε ≤ Aε ε) :
    ∀ᶠ d : ℕ in atTop, ∀ r : ℝ, 0 ≤ r → r ≤ r_star ε d → let ℓ : ℝ := (d : ℝ) / 2
      let y : ℝ := y_r ε r
      exp y * |(∑ n ∈ Finset.range (N_ℓ ℓ + 1), ((-y) ^ n / (n.factorial : ℝ)) * A_ℓn ε ℓ n) -
        exp (-y)| < 1 / 2 := by
  obtain ⟨C, -, hstar⟩ := exists_eventually_y_star_le_log_eighth_add hε horder
  filter_upwards [tendsto_saddleResidue_dimension_half.eventually
      (eventually_plusSaddleSmallRadius_relativeFiniteResidue_lt_half hε horder (C := C)), hstar]
    with d hres hcut r hr hrstar
  exact hres (y_r ε r) (saddleSmallRadiusVariable_nonneg ε r) (hcut r hr hrstar)

end

noncomputable section

open Filter MeasureTheory Real Set
open scoped Topology BigOperators

theorem gamma_half_factorial_lower (N : ℕ) :
    Gamma (3 / 2 : ℝ) * (N.factorial : ℝ) ≤ Gamma ((N : ℝ) + 3 / 2) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hq : (0 : ℝ) < (N : ℝ) + 3 / 2 := by positivity
    have hrec : Gamma (((N + 1 : ℕ) : ℝ) + 3 / 2) =
        ((N : ℝ) + 3 / 2) * Gamma ((N : ℝ) + 3 / 2) := by
      rw [show (((N + 1 : ℕ) : ℝ) + 3 / 2) = ((N : ℝ) + 3 / 2) + 1 by push_cast; ring,
        Gamma_add_one hq.ne']
    rw [hrec, Nat.factorial_succ]
    push_cast
    nlinarith [ih, (Gamma_pos_of_pos hq).le, Nat.cast_nonneg (α := ℝ) N]

theorem saddleNegative_factorialTail_le_majorant {C ℓ y : ℝ} (hy : 0 ≤ y)
    (hyupper : y ≤ log ℓ / 8 + C) :
    exp y * (y ^ N_ℓ ℓ / ((N_ℓ ℓ).factorial : ℝ)) ≤ 2 * saddleSmallResidueTailMajorant C ℓ := by
  refine saddleSmallResidue_tail_le_majorant hy hyupper ?_
  have h := saddleSmallResidueTruncation_half_pow_le ℓ
  rw [pow_succ] at h
  linarith

theorem saddleNegative_relativeGammaTail_le {C Kε ℓ y E : ℝ} (hKε : 0 ≤ Kε) (hC : 0 ≤ C)
    (hℓ : 1 ≤ ℓ) (hy : 0 ≤ y) (hyupper : y ≤ log ℓ / 8 + C) (hE : 0 ≤ E) :
    exp y * (Kε * √y * y ^ N_ℓ ℓ / Gamma ((N_ℓ ℓ : ℝ) + 3 / 2) * E) ≤
      2 * Kε / Gamma (3 / 2 : ℝ) * (1 + (log ℓ / 8 + C)) *
        saddleSmallResidueTailMajorant C ℓ * E := by
  have hlog : 0 ≤ log ℓ := log_nonneg hℓ
  have hΓ : 0 < Gamma (3 / 2 : ℝ) := Gamma_pos_of_pos (by norm_num)
  have hfactorial : (0 : ℝ) < ((N_ℓ ℓ).factorial : ℝ) := by exact_mod_cast (N_ℓ ℓ).factorial_pos
  have hmajor : (0 : ℝ) ≤ saddleSmallResidueTailMajorant C ℓ := (exp_pos _).le
  have hfrac : y ^ N_ℓ ℓ / Gamma ((N_ℓ ℓ : ℝ) + 3 / 2) ≤
      y ^ N_ℓ ℓ / ((N_ℓ ℓ).factorial : ℝ) / Gamma (3 / 2 : ℝ) := by
    rw [div_div, mul_comm]
    exact div_le_div_of_nonneg_left (pow_nonneg hy _) (mul_pos hΓ hfactorial)
      (gamma_half_factorial_lower _)
  have hsqrt : √y ≤ 1 + (log ℓ / 8 + C) := by
    nlinarith [sq_sqrt hy, sqrt_nonneg y, sq_nonneg (√y - 1)]
  have htail := saddleNegative_factorialTail_le_majorant hy hyupper
  calc exp y * (Kε * √y * y ^ N_ℓ ℓ / Gamma ((N_ℓ ℓ : ℝ) + 3 / 2) * E) =
        Kε * √y * (exp y * (y ^ N_ℓ ℓ / Gamma ((N_ℓ ℓ : ℝ) + 3 / 2))) * E := by ring
    _ ≤ Kε * √y * (exp y * (y ^ N_ℓ ℓ / ((N_ℓ ℓ).factorial : ℝ) / Gamma (3 / 2 : ℝ))) * E := by
        gcongr
    _ = Kε / Gamma (3 / 2 : ℝ) * √y * (exp y * (y ^ N_ℓ ℓ / ((N_ℓ ℓ).factorial : ℝ))) * E := by
        ring
    _ ≤ Kε / Gamma (3 / 2 : ℝ) * (1 + (log ℓ / 8 + C)) *
          (2 * saddleSmallResidueTailMajorant C ℓ) * E := by gcongr
    _ = 2 * Kε / Gamma (3 / 2 : ℝ) * (1 + (log ℓ / 8 + C)) *
          saddleSmallResidueTailMajorant C ℓ * E := by ring

/-- Majorant for the Gamma-tail of the residue series relative to the main term. -/
def saddleNegativeRelativeGammaTailMajorant (C K Kε ℓ : ℝ) : ℝ :=
  2 * Kε / Gamma (3 / 2 : ℝ) * (1 + (log ℓ / 8 + C)) * saddleSmallResidueTailMajorant C ℓ *
    exp (K * (2 * (N_ℓ ℓ : ℝ) + 1) ^ 2 / ℓ)

theorem tendsto_saddleNegativeTruncation_odd_sq_div :
    Tendsto (fun ℓ : ℝ ↦ (2 * (N_ℓ ℓ : ℝ) + 1) ^ 2 / ℓ) atTop (𝓝 0) := by
  have h := ((tendsto_saddleSmallResidueTruncation_sq_div.const_mul 4).add
    (tendsto_saddleSmallResidueTruncation_div.const_mul 4)).add (tendsto_log_pow_div_atTop 0)
  simp only [mul_zero, add_zero] at h
  exact h.congr fun ℓ ↦ by ring

theorem tendsto_saddleNegativeLogWindowTailMajorant (C : ℝ) :
    Tendsto (fun ℓ : ℝ ↦ (1 + (log ℓ / 8 + C)) * saddleSmallResidueTailMajorant C ℓ)
      atTop (𝓝 0) := by
  have h := ((((tendsto_pow_mul_exp_neg_mul_atTop (by norm_num : (0 : ℝ) < 1 / 8) 1).const_mul
      (1 / 8 : ℝ)).add ((tendsto_pow_mul_exp_neg_mul_atTop
        (by norm_num : (0 : ℝ) < 1 / 8) 0).const_mul (1 + C))).comp
    tendsto_log_atTop).const_mul (exp (3 * C))
  simp only [mul_zero, add_zero] at h
  refine h.congr fun ℓ ↦ ?_
  simp only [Function.comp_apply, saddleSmallResidueTailMajorant]
  rw [show 3 * C - 1 / 8 * log ℓ = 3 * C + -(1 / 8 : ℝ) * log ℓ by ring, exp_add]
  ring

theorem tendsto_saddleNegativeRelativeGammaTailMajorant (C K Kε : ℝ) :
    Tendsto (saddleNegativeRelativeGammaTailMajorant C K Kε) atTop (𝓝 0) := by
  have herror : Tendsto (fun ℓ : ℝ ↦ exp (K * (2 * (N_ℓ ℓ : ℝ) + 1) ^ 2 / ℓ)) atTop (𝓝 1) := by
    have h := tendsto_saddleNegativeTruncation_odd_sq_div.const_mul K
    rw [mul_zero] at h
    simpa using (h.congr fun ℓ ↦ by ring : Tendsto (fun ℓ : ℝ ↦
      K * (2 * (N_ℓ ℓ : ℝ) + 1) ^ 2 / ℓ) atTop (𝓝 0)).rexp
  have h := ((tendsto_saddleNegativeLogWindowTailMajorant C).const_mul
    (2 * Kε / Gamma (3 / 2 : ℝ))).mul herror
  simp only [mul_zero, zero_mul] at h
  refine h.congr fun ℓ ↦ ?_
  unfold saddleNegativeRelativeGammaTailMajorant
  ring

/-- Report (82): eventually in `λ` the Gamma tail of the residue series is `< 1/2`. -/
theorem eventually_saddleNegative_relativeGammaTail_lt_half (C K Kε : ℝ) (hC : 0 ≤ C)
    (hKε : 0 ≤ Kε) :
    ∀ᶠ ℓ : ℝ in atTop, ∀ y : ℝ, 0 ≤ y → y ≤ log ℓ / 8 + C →
      exp y * (Kε * √y * y ^ N_ℓ ℓ / Gamma ((N_ℓ ℓ : ℝ) + 3 / 2) *
        exp (K * (2 * (N_ℓ ℓ : ℝ) + 1) ^ 2 / ℓ)) < 1 / 2 := by
  filter_upwards [(tendsto_saddleNegativeRelativeGammaTailMajorant C K Kε).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)), eventually_ge_atTop (1 : ℝ)]
    with ℓ hsmall hℓ y hy hyupper
  exact lt_of_le_of_lt (saddleNegative_relativeGammaTail_le hKε hC hℓ hy hyupper (exp_pos _).le)
    hsmall

end

noncomputable section

open Filter MeasureTheory Real Set
open scoped Topology BigOperators

/-- The Frullani kernel `(1 - cos (aT)) e^{-ca}/a`, whose integral is `log (|c + iT|/c)`. -/
def upperCosLaplaceKernel (c T a : ℝ) : ℝ := (1 - cos (a * T)) * exp (-c * a) / a

theorem upperCosLaplaceKernel_eq_frullani_re (c T a : ℝ) :
    upperCosLaplaceKernel c T a = (Frullani.cexpKernel (c : ℂ) ((c : ℂ) + I * (T : ℂ)) a).re := by
  simp [upperCosLaplaceKernel, Frullani.cexpKernel, Complex.exp_re, cos_neg]
  ring_nf

theorem upperCosLaplaceKernel_integrable {c : ℝ} (hc : 0 < c) (T : ℝ) :
    IntegrableOn (upperCosLaplaceKernel c T) (Ioi 0) :=
  (Frullani.integrableOn_cexpKernel (z := (c : ℂ)) (w := (c : ℂ) + I * (T : ℂ))
    (by simpa using hc) (by simpa using hc)).re.congr
    (Eventually.of_forall fun a ↦ (upperCosLaplaceKernel_eq_frullani_re c T a).symm)

theorem integral_upperCosLaplaceKernel {c : ℝ} (hc : 0 < c) (T : ℝ) :
    (∫ a : ℝ in Ioi 0, upperCosLaplaceKernel c T a) = log (‖(c : ℂ) + I * (T : ℂ)‖ / c) := by
  have hz : 0 < (c : ℂ).re := by simpa using hc
  have hw : 0 < ((c : ℂ) + I * (T : ℂ)).re := by simpa using hc
  calc (∫ a : ℝ in Ioi 0, upperCosLaplaceKernel c T a) =
        ∫ a : ℝ in Ioi 0, (Frullani.cexpKernel (c : ℂ) ((c : ℂ) + I * (T : ℂ)) a).re :=
        setIntegral_congr_fun measurableSet_Ioi fun a _ ↦
          upperCosLaplaceKernel_eq_frullani_re c T a
    _ = (∫ a : ℝ in Ioi 0, Frullani.cexpKernel (c : ℂ) ((c : ℂ) + I * (T : ℂ)) a).re :=
        integral_re (Frullani.integrableOn_cexpKernel hz hw)
    _ = (Complex.log ((c : ℂ) + I * (T : ℂ)) - Complex.log (c : ℂ)).re := by
        rw [Frullani.integral_cexpKernel hz hw]
    _ = log (‖(c : ℂ) + I * (T : ℂ)‖ / c) := by
        rw [Complex.sub_re, Complex.log_re, Complex.log_re, log_div]
        · simp [abs_of_pos hc]
        · exact (norm_pos_iff.mpr (ne_of_apply_ne Complex.re (by simpa using hc.ne'))).ne'
        · exact hc.ne'

/-- The `n`-th geometric truncation of the gamma damping integrand of report (45). -/
def upperGammaTruncatedDampingIntegrand (ℓ η T : ℝ) (n : ℕ) (a : ℝ) : ℝ :=
  upperCosLaplaceKernel η T a * ∑ k ∈ Finset.range (n + 1), exp (-(2 * a / ℓ)) ^ k

theorem upperGammaTruncatedDampingIntegrand_eq_sum (ℓ η T : ℝ) (n : ℕ) (a : ℝ) :
    upperGammaTruncatedDampingIntegrand ℓ η T n a =
      ∑ k ∈ Finset.range (n + 1), upperCosLaplaceKernel (η + 2 * (k : ℝ) / ℓ) T a := by
  unfold upperGammaTruncatedDampingIntegrand upperCosLaplaceKernel
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have he : exp (-η * a) * exp (-(2 * a / ℓ)) ^ k = exp (-(η + 2 * (k : ℝ) / ℓ) * a) := by
    rw [← exp_nat_mul, ← exp_add]
    congr 1
    ring
  rw [div_mul_eq_mul_div, mul_assoc, he]

theorem upperGammaGeometricLimit_eq_integrand (ℓ η T a : ℝ) :
    upperCosLaplaceKernel η T a * (1 - exp (-(2 * a / ℓ)))⁻¹ =
      upperGammaDampingIntegrand ℓ η T a := by
  simp [upperCosLaplaceKernel, upperGammaDampingIntegrand, μ_ℓ, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc]

theorem tendsto_integral_upperGammaTruncatedDampingIntegrand {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (T : ℝ) :
    Tendsto (fun n : ℕ ↦ ∫ a : ℝ in Ioi 0, upperGammaTruncatedDampingIntegrand ℓ η T n a)
      atTop (𝓝 (D_γ ℓ η T)) := by
  have hq : ∀ a : ℝ, 0 < a → exp (-(2 * a / ℓ)) < 1 := fun a ha ↦
    exp_lt_one_iff.mpr (neg_lt_zero.mpr (by positivity))
  have hq0 : ∀ a : ℝ, (0 : ℝ) ≤ exp (-(2 * a / ℓ)) := fun a ↦ (exp_pos _).le
  have hbase : ∀ a : ℝ, 0 < a → 0 ≤ upperCosLaplaceKernel η T a := fun a ha ↦
    div_nonneg (mul_nonneg (sub_nonneg.mpr (cos_le_one _)) (exp_pos _).le) ha.le
  unfold D_γ
  refine tendsto_integral_of_dominated_convergence (upperGammaDampingIntegrand ℓ η T) ?_
    (upperGammaDampingIntegrand_integrable hℓ hη T) ?_ ?_
  · intro n
    apply Measurable.aestronglyMeasurable
    unfold upperGammaTruncatedDampingIntegrand upperCosLaplaceKernel
    fun_prop
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    have hpartial : 0 ≤ upperGammaTruncatedDampingIntegrand ℓ η T n a :=
      mul_nonneg (hbase a ha) (Finset.sum_nonneg fun k _ ↦ pow_nonneg (hq0 a) k)
    rw [Real.norm_eq_abs, abs_of_nonneg hpartial, ← upperGammaGeometricLimit_eq_integrand]
    exact mul_le_mul_of_nonneg_left (sum_le_hasSum _ (fun k _ ↦ pow_nonneg (hq0 a) k)
      (hasSum_geometric_of_lt_one (hq0 a) (hq a ha))) (hbase a ha)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    have hgeo := (hasSum_geometric_of_lt_one (hq0 a) (hq a ha)).tendsto_sum_nat.comp
      (tendsto_add_atTop_nat 1)
    simpa [upperGammaTruncatedDampingIntegrand, upperGammaGeometricLimit_eq_integrand] using
      (tendsto_const_nhds (x := upperCosLaplaceKernel η T a)).mul hgeo

theorem upperGammaLaplaceRate_pos {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) (k : ℕ) :
    0 < η + 2 * (k : ℝ) / ℓ :=
  add_pos_of_pos_of_nonneg hη (by positivity)

theorem integral_upperGammaTruncatedDampingIntegrand {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (T : ℝ) (n : ℕ) :
    (∫ a : ℝ in Ioi 0, upperGammaTruncatedDampingIntegrand ℓ η T n a) =
      ∑ k ∈ Finset.range (n + 1),
        log (‖(η + 2 * (k : ℂ) / ℓ : ℂ) + I * (T : ℂ)‖ / (η + 2 * (k : ℝ) / ℓ)) := by
  calc (∫ a : ℝ in Ioi 0, upperGammaTruncatedDampingIntegrand ℓ η T n a) =
        ∫ a : ℝ in Ioi 0, ∑ k ∈ Finset.range (n + 1),
          upperCosLaplaceKernel (η + 2 * (k : ℝ) / ℓ) T a :=
        setIntegral_congr_fun measurableSet_Ioi fun a _ ↦
          upperGammaTruncatedDampingIntegrand_eq_sum ℓ η T n a
    _ = ∑ k ∈ Finset.range (n + 1),
          ∫ a : ℝ in Ioi 0, upperCosLaplaceKernel (η + 2 * (k : ℝ) / ℓ) T a :=
        integral_finsetSum _ fun k _ ↦
          upperCosLaplaceKernel_integrable (upperGammaLaplaceRate_pos hℓ hη k) T
    _ = _ := Finset.sum_congr rfl fun k _ ↦ by
        rw [integral_upperCosLaplaceKernel (upperGammaLaplaceRate_pos hℓ hη k) T]
        push_cast
        rfl

theorem upperGammaLaplaceRate_log_ratio {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) (T : ℝ) (k : ℕ) :
    log (‖(η + 2 * (k : ℂ) / ℓ : ℂ) + I * (T : ℂ)‖ / (η + 2 * (k : ℝ) / ℓ)) =
      log (‖(ℓ * η / 2 : ℂ) + I * (ℓ * T / 2 : ℂ) + (k : ℂ)‖ /
        (ℓ * η / 2 + (k : ℝ))) := by
  have hc := upperGammaLaplaceRate_pos hℓ hη k
  have hℓ' : (ℓ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hℓ.ne'
  have hhalf : ‖(ℓ / 2 : ℂ)‖ = ℓ / 2 := by simp [abs_of_pos hℓ]
  have hscale : ‖(ℓ / 2 * (η + 2 * (k : ℂ) / ℓ) : ℂ) + I * (ℓ / 2 * T : ℂ)‖ /
      (ℓ / 2 * (η + 2 * (k : ℝ) / ℓ)) = ‖(η + 2 * (k : ℂ) / ℓ : ℂ) + I * (T : ℂ)‖ /
        (η + 2 * (k : ℝ) / ℓ) := by
    rw [show (ℓ / 2 * (η + 2 * (k : ℂ) / ℓ) : ℂ) + I * (ℓ / 2 * T : ℂ) =
      (ℓ / 2 : ℂ) * ((η + 2 * (k : ℂ) / ℓ : ℂ) + I * (T : ℂ)) by ring, norm_mul, hhalf]
    field_simp
  rw [← hscale, show ℓ / 2 * (η + 2 * (k : ℝ) / ℓ) = ℓ * η / 2 + (k : ℝ) by field_simp [hℓ.ne'],
    show (ℓ / 2 * (η + 2 * (k : ℂ) / ℓ) : ℂ) + I * (ℓ / 2 * T : ℂ) =
      (ℓ * η / 2 : ℂ) + I * (ℓ * T / 2 : ℂ) + (k : ℂ) by field_simp; ring]

theorem upperGammaEuler_log_norm_ratio {m : ℝ} (hm : 0 < m) (b : ℝ) {n : ℕ} (hn : 0 < n) :
    log (‖Complex.GammaSeq ((m : ℂ) + I * (b : ℂ)) n‖ / ‖Complex.GammaSeq (m : ℂ) n‖) =
      -∑ k ∈ Finset.range (n + 1), log (‖(m : ℂ) + I * (b : ℂ) + (k : ℂ)‖ / (m + (k : ℝ))) := by
  classical
  have hreal : ∀ k : ℕ, 0 < m + (k : ℝ) := fun k ↦ by positivity
  have hnormreal : ∀ k : ℕ, ‖(m : ℂ) + (k : ℂ)‖ = m + (k : ℝ) := fun k ↦ by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hreal k)]
  have hcomplex : ∀ k : ℕ, 0 < ‖(m : ℂ) + I * (b : ℂ) + (k : ℂ)‖ := fun k ↦
    norm_pos_iff.mpr (ne_of_apply_ne Complex.re (by simpa using (hreal k).ne'))
  have hpow : ‖(n : ℂ) ^ ((m : ℂ) + I * (b : ℂ))‖ = ‖(n : ℂ) ^ (m : ℂ)‖ := by
    rw [Complex.norm_natCast_cpow_of_pos hn, Complex.norm_natCast_cpow_of_pos hn]
    simp
  have hpown : ‖(n : ℂ) ^ (m : ℂ)‖ ≠ 0 := (Complex.norm_natCast_cpow_pos_of_pos hn (m : ℂ)).ne'
  have hfactorial : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hprodreal : (∏ k ∈ Finset.range (n + 1), (m + (k : ℝ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ (hreal k).ne'
  have hprodcomplex : (∏ k ∈ Finset.range (n + 1), ‖(m : ℂ) + I * (b : ℂ) + (k : ℂ)‖) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ (hcomplex k).ne'
  have hratio : ‖Complex.GammaSeq ((m : ℂ) + I * (b : ℂ)) n‖ / ‖Complex.GammaSeq (m : ℂ) n‖ =
      (∏ k ∈ Finset.range (n + 1), ‖(m : ℂ) + I * (b : ℂ) + (k : ℂ)‖ / (m + (k : ℝ)))⁻¹ := by
    rw [Complex.GammaSeq, Complex.GammaSeq, norm_div, norm_div, norm_mul, norm_mul,
      norm_prod, norm_prod, hpow]
    simp_rw [hnormreal]
    rw [Finset.prod_div_distrib]
    field_simp [norm_natCast, hpown, hfactorial, hprodreal, hprodcomplex]
  rw [hratio, log_inv, log_prod]
  exact fun k _ ↦ div_ne_zero (hcomplex k).ne' (hreal k).ne'

theorem tendsto_upperGammaEuler_log_norm_ratio {m : ℝ} (hm : 0 < m) (b : ℝ) :
    Tendsto (fun n : ℕ ↦ log (‖Complex.GammaSeq ((m : ℂ) + I * (b : ℂ)) n‖ /
        ‖Complex.GammaSeq (m : ℂ) n‖))
      atTop (𝓝 (log (‖Complex.Gamma ((m : ℂ) + I * (b : ℂ))‖ / ‖Complex.Gamma (m : ℂ)‖))) := by
  have hnum : ‖Complex.Gamma ((m : ℂ) + I * (b : ℂ))‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simpa using hm))
  have hden : ‖Complex.Gamma (m : ℂ)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simpa using hm))
  exact ((Complex.GammaSeq_tendsto_Gamma _).norm.div (Complex.GammaSeq_tendsto_Gamma _).norm
    hden).log (div_ne_zero hnum hden)

theorem upperGammaPositiveShifted_log_norm_eq_neg_damping {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (T : ℝ) :
    log (‖Complex.Gamma ((ℓ * η / 2 : ℂ) + I * (ℓ * T / 2 : ℂ))‖ /
      Gamma (ℓ * η / 2)) = -D_γ ℓ η T := by
  have hm : 0 < ℓ * η / 2 := by positivity
  have hfinite : (fun n : ℕ ↦ log (‖Complex.GammaSeq ((ℓ * η / 2 : ℂ) +
        I * (ℓ * T / 2 : ℂ)) n‖ / ‖Complex.GammaSeq (ℓ * η / 2 : ℂ) n‖)) =ᶠ[atTop]
      fun n : ℕ ↦ -∫ a : ℝ in Ioi 0, upperGammaTruncatedDampingIntegrand ℓ η T n a := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have heuler := upperGammaEuler_log_norm_ratio hm (ℓ * T / 2) hn
    push_cast at heuler
    rw [heuler, integral_upperGammaTruncatedDampingIntegrand hℓ hη T n]
    exact congrArg Neg.neg (Finset.sum_congr rfl fun k _ ↦ by
      simpa using (upperGammaLaplaceRate_log_ratio hℓ hη T k).symm)
  have hlimit := tendsto_upperGammaEuler_log_norm_ratio hm (ℓ * T / 2)
  push_cast at hlimit
  have hidentity := tendsto_nhds_unique hlimit
    (Tendsto.congr' hfinite.symm (tendsto_integral_upperGammaTruncatedDampingIntegrand hℓ hη T).neg)
  rwa [show ‖Complex.Gamma (ℓ * η / 2 : ℂ)‖ = Gamma (ℓ * η / 2) by
    rw [show (ℓ * η / 2 : ℂ) = ((ℓ * η / 2 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]
    exact Complex.norm_of_nonneg (Gamma_pos_of_pos hm).le] at hidentity

/-- Report (81): `|Γ(λη/2 - iλT/2)| = Γ(λη/2) e^{-D_γ(T)}`. -/
theorem upperGammaShifted_modulus_eq_exp_neg_damping {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) (T : ℝ) :
    ‖Complex.Gamma ((ℓ * η / 2 : ℂ) - I * (ℓ * T / 2 : ℂ))‖ =
      Gamma (ℓ * η / 2) * exp (-D_γ ℓ η T) := by
  have hm : 0 < ℓ * η / 2 := by positivity
  have hΓ : 0 < Gamma (ℓ * η / 2) := Gamma_pos_of_pos hm
  have hpos : 0 < ‖Complex.Gamma ((ℓ * η / 2 : ℂ) + I * (ℓ * T / 2 : ℂ))‖ :=
    norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simpa using hm))
  have hconj : ‖Complex.Gamma ((ℓ * η / 2 : ℂ) - I * (ℓ * T / 2 : ℂ))‖ =
      ‖Complex.Gamma ((ℓ * η / 2 : ℂ) + I * (ℓ * T / 2 : ℂ))‖ := by
    rw [show (ℓ * η / 2 : ℂ) - I * (ℓ * T / 2 : ℂ) =
      starRingEnd ℂ ((ℓ * η / 2 : ℂ) + I * (ℓ * T / 2 : ℂ)) by
        simp only [map_add, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I,
          Complex.conj_ofNat]
        ring, Complex.Gamma_conj, Complex.norm_conj]
  have key := congrArg exp (upperGammaPositiveShifted_log_norm_eq_neg_damping hℓ hη T)
  rw [exp_log (div_pos hpos hΓ), div_eq_iff hΓ.ne'] at key
  rw [hconj, key]
  exact mul_comm _ _

end

noncomputable section

open Filter MeasureTheory Real Set
open scoped Topology

/-- Report (82): if both relative errors of the residue expansion are `< 1/2`, then `f₊(r)` has
positive real part. -/
theorem plusSaddleProfile_re_pos_of_relative_residue_bounds {ε ℓ r : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : a₀ε ε ≤ Aε ε) (hr : 0 < r) (N : ℕ)
    (hfinite : exp (y_r ε r) * |(∑ n ∈ Finset.range (N + 1),
        (-y_r ε r) ^ n / (n.factorial : ℝ) * A_ℓn ε ℓ n) - exp (-(y_r ε r))| < (1 / 2 : ℝ))
    (hremainder : exp (y_r ε r) *
        ‖plusSaddleTaylorRemainder ε ℓ N r / (originValue ε ℓ : ℂ)‖ < (1 / 2 : ℝ)) :
    0 < (fPlus ε ℓ r).re := by
  have hO : 0 < originValue ε ℓ := saddleOriginValue_pos hε ℓ
  have hexp : 0 < exp (y_r ε r) := exp_pos _
  have hone : exp (y_r ε r) * exp (-(y_r ε r)) = 1 := by rw [← exp_add]; simp
  have key : ∀ S Q : ℝ, exp (y_r ε r) * |S - exp (-(y_r ε r))| < 1 / 2 →
      exp (y_r ε r) * |Q| < 1 / 2 → 0 < S + Q := by
    intro S Q h1 h2
    have h3 := mul_le_mul_of_nonneg_left (neg_abs_le (S - exp (-(y_r ε r)))) hexp.le
    have h4 := mul_le_mul_of_nonneg_left (neg_abs_le Q) hexp.le
    have h5 : 0 < exp (y_r ε r) * (S + Q) := by nlinarith
    nlinarith
  have hnormal : (fPlus ε ℓ r).re / originValue ε ℓ =
      (∑ n ∈ Finset.range (N + 1), (-y_r ε r) ^ n / (n.factorial : ℝ) * A_ℓn ε ℓ n) +
        (plusSaddleTaylorRemainder ε ℓ N r / (originValue ε ℓ : ℂ)).re := by
    have h := congrArg Complex.re (plusSaddleProfile_div_origin_eq_small_radius_residue_series
      hε hℓ horder hr N)
    simpa [Complex.div_ofReal_re, ← Complex.ofReal_neg, ← Complex.ofReal_pow] using h
  have hQ : exp (y_r ε r) *
      |(plusSaddleTaylorRemainder ε ℓ N r / (originValue ε ℓ : ℂ)).re| < 1 / 2 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hexp.le) hremainder
  have hsum := key _ _ hfinite hQ
  rw [← hnormal] at hsum
  exact (div_pos_iff_of_pos_right hO).mp hsum

end

noncomputable section

open Filter MeasureTheory Real Set
open scoped Topology BigOperators

theorem upperPositiveHalfGamma_scaled_sq_le (n : ℕ) (x : ℝ) :
    Gamma ((n : ℝ) + 1 / 2) ^ 2 ≤
      ‖Complex.Gamma (((n : ℂ) + 1 / 2) + I * (x : ℂ))‖ ^ 2 * cosh (π * x) := by
  have key : ∀ a b g t c : ℝ, 0 ≤ a → a ≤ t → 0 ≤ c → b ^ 2 ≤ g ^ 2 * c →
      (a * b) ^ 2 ≤ (t * g) ^ 2 * c := by
    intro a b g t c ha hat hc hb
    have h1 : a ^ 2 * b ^ 2 ≤ a ^ 2 * (g ^ 2 * c) := by nlinarith [sq_nonneg a]
    have h2 : a ^ 2 ≤ t ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg g) hc]
  induction n with
  | zero =>
    norm_num only [Nat.cast_zero, zero_add]
    have hhalf : ‖Complex.Gamma ((1 / 2 : ℂ) + I * (x : ℂ))‖ ^ 2 = π / cosh (π * x) := by
      convert Complex.norm_Gamma_one_half_add_I_mul_sq x using 1
    rw [hhalf, Gamma_one_half_eq, sq_sqrt pi_pos.le]
    field_simp [(cosh_pos (π * x)).ne']
    norm_num
  | succ n ih =>
    have hq : (0 : ℝ) < (n : ℝ) + 1 / 2 := by positivity
    have hz : (((n : ℂ) + 1 / 2) + I * (x : ℂ)) ≠ 0 := fun h ↦
      hq.ne' (by simpa using congrArg Complex.re h)
    rw [show (((n + 1 : ℕ) : ℝ) + 1 / 2) = ((n : ℝ) + 1 / 2) + 1 by push_cast; ring,
      Gamma_add_one hq.ne', show ((n + 1 : ℕ) : ℂ) + 1 / 2 + I * (x : ℂ) =
        (((n : ℂ) + 1 / 2) + I * (x : ℂ)) + 1 by push_cast; ring,
      Complex.Gamma_add_one _ hz, norm_mul]
    refine key _ _ _ _ _ hq.le ?_ (cosh_pos (π * x)).le ih
    have h := Complex.abs_re_le_norm (((n : ℂ) + 1 / 2) + I * (x : ℂ))
    rwa [show (((n : ℂ) + 1 / 2) + I * (x : ℂ)).re = (n : ℝ) + 1 / 2 by simp,
      abs_of_pos hq] at h

theorem upperNegativeContour_shortMeasure_pointwise {ε ℓ κ η a : ℝ} (hε : 0 < ε)
    (hεsmall : ε ≤ 1 / 4) (hℓ : 0 < ℓ) (hκ : 1 ≤ κ) (hκη : κ + η ≤ 3) (ha : 0 < a)
    (hmargin : 0 ≤ bε ε a) :
    ℓ * (-w_s ε a) * cosh (κ * a) ≤ (1 - 2 * ε) * μ_ℓ ℓ η a := by
  have hfactor : 0 ≤ 1 - 2 * ε := by linarith
  have hbase : ℓ / 2 * exp (-η * a) / a ^ 2 ≤ μ_ℓ ℓ η a := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < a ^ 2)]
    nlinarith [(upperGammaVarianceDensity_pointwise_bounds (η := η) hℓ ha).1]
  have hexp : exp ((η - 2) * a) * exp ((κ - 1) * a) ≤ 1 := by
    rw [← exp_add, exp_le_one_iff]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 3 - (κ + η) by linarith) ha.le]
  have hcoefficient : bε ε a * exp ((η - 2) * a) * (cosh (κ * a) / cosh a) ≤ 1 - 2 * ε := by
    have hratio : cosh (κ * a) / cosh a ≤ exp ((κ - 1) * a) := by
      convert cosh_ratio_upper ha.le (sub_nonneg.mpr hκ) using 1
      ring_nf
    have hmargintop : bε ε a ≤ 1 - 2 * ε := by
      unfold bε
      nlinarith [mul_nonneg hε.le ha.le]
    calc bε ε a * exp ((η - 2) * a) * (cosh (κ * a) / cosh a) ≤
          bε ε a * exp ((η - 2) * a) * exp ((κ - 1) * a) := by gcongr
      _ = bε ε a * (exp ((η - 2) * a) * exp ((κ - 1) * a)) := by ring
      _ ≤ bε ε a := by simpa using mul_le_mul_of_nonneg_left hexp hmargin
      _ ≤ 1 - 2 * ε := by linarith
  have hidentity : ℓ * (-w_s ε a) * cosh (κ * a) =
      bε ε a * exp ((η - 2) * a) * (cosh (κ * a) / cosh a) * (ℓ / 2 * exp (-η * a) / a ^ 2) := by
    have he : exp ((η - 2) * a) * exp (-η * a) = exp (-2 * a) := by
      rw [← exp_add]
      congr 1
      ring
    unfold w_s
    field_simp [ha.ne', (cosh_pos a).ne']
    calc bε ε a * exp (-(2 * a)) = bε ε a * (exp ((η - 2) * a) * exp (-η * a)) := by
          rw [he]
          congr 1
          ring_nf
      _ = bε ε a * exp (a * (η - 2)) * exp (-(a * η)) := by
          rw [show a * (η - 2) = (η - 2) * a by ring, show -(a * η) = -η * a by ring]
          ring
  rw [hidentity]
  exact (mul_le_mul_of_nonneg_right hcoefficient (by positivity)).trans
    (mul_le_mul_of_nonneg_left hbase hfactor)

theorem upperNegativeContour_shortDamping_le_gamma {ε ℓ κ η : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (hκ : 1 ≤ κ) (hη : 0 < η) (hκη : κ + η ≤ 3) (horder : a₀ε ε ≤ Aε ε)
    (hmargin : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a) (T : ℝ) :
    D_s ε ℓ (-κ - 1) T ≤ (1 - 2 * ε) * D_γ ℓ η T := by
  have ha₀ := shortCutoff_pos hε
  have hsubset : Ioc (a₀ε ε) (Aε ε) ⊆ Ioi (0 : ℝ) := fun a ha ↦ ha₀.trans ha.1
  have hgamma := upperGammaDampingIntegrand_integrable hℓ hη T
  have hshortOn : IntegrableOn (fun a : ℝ ↦
      ℓ * (-w_s ε a) * cosh (κ * a) * (1 - cos (a * T))) (Ioc (a₀ε ε) (Aε ε)) := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le horder).mp ?_
    exact ((((shortShellDensity_intervalIntegrable hε horder).neg).const_mul ℓ).mul_continuousOn
      (by fun_prop : Continuous fun a : ℝ ↦ cosh (κ * a)).continuousOn).mul_continuousOn
      (by fun_prop : Continuous fun a : ℝ ↦ 1 - cos (a * T)).continuousOn
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] upperGammaDampingIntegrand ℓ η T := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    exact mul_nonneg (sub_nonneg.mpr (cos_le_one _)) (upperGammaMeasureDensity_pos hℓ ha).le
  calc D_s ε ℓ (-κ - 1) T =
        ∫ a : ℝ in Ioc (a₀ε ε) (Aε ε), ℓ * (-w_s ε a) * cosh (κ * a) * (1 - cos (a * T)) := by
        unfold D_s
        rw [show 1 + (-κ - 1) = -κ by ring, ← intervalIntegral.integral_const_mul,
          intervalIntegral.integral_of_le horder]
        refine setIntegral_congr_fun measurableSet_Ioc fun a _ ↦ ?_
        simp only [neg_mul, cosh_neg]
        ring
    _ ≤ ∫ a : ℝ in Ioc (a₀ε ε) (Aε ε), (1 - 2 * ε) * upperGammaDampingIntegrand ℓ η T a := by
        refine setIntegral_mono_on hshortOn ((hgamma.mono_set hsubset).const_mul _)
          measurableSet_Ioc fun a ha ↦ ?_
        simpa [upperGammaDampingIntegrand, mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_right (upperNegativeContour_shortMeasure_pointwise hε hεsmall hℓ hκ
            hκη (ha₀.trans ha.1) (hmargin a ⟨ha.1.le, ha.2⟩)) (sub_nonneg.mpr (cos_le_one (a * T)))
    _ = (1 - 2 * ε) * ∫ a : ℝ in Ioc (a₀ε ε) (Aε ε), upperGammaDampingIntegrand ℓ η T a := by
        rw [integral_const_mul]
    _ ≤ (1 - 2 * ε) * D_γ ℓ η T :=
        mul_le_mul_of_nonneg_left (setIntegral_mono_set hgamma hnonneg
          (Eventually.of_forall hsubset)) (by linarith)

/-- The height `κ = 1 + (2N+1)/λ` of the negative Taylor contour of report (82). -/
def saddleNegativeContourOrdinate (ℓ : ℝ) (N : ℕ) : ℝ := 1 + (2 * (N : ℝ) + 1) / ℓ

/-- The gamma rate `η = (2N+3)/λ` matched to the negative Taylor contour. -/
def saddleNegativeGammaRate (ℓ : ℝ) (N : ℕ) : ℝ := (2 * (N : ℝ) + 3) / ℓ

theorem saddleNegativeGammaRate_pos {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) :
    0 < saddleNegativeGammaRate ℓ N := by
  unfold saddleNegativeGammaRate
  positivity

theorem one_le_saddleNegativeContourOrdinate {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) :
    1 ≤ saddleNegativeContourOrdinate ℓ N := by
  unfold saddleNegativeContourOrdinate
  linarith [show (0 : ℝ) ≤ (2 * (N : ℝ) + 1) / ℓ by positivity]

theorem saddleNegativeContourOrdinate_le_two {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ)
    (hN : 2 * ((N + 1 : ℕ) : ℝ) ≤ ℓ) : saddleNegativeContourOrdinate ℓ N ≤ 2 := by
  unfold saddleNegativeContourOrdinate
  push_cast at hN
  have h : (2 * (N : ℝ) + 1) / ℓ ≤ 1 := by
    rw [div_le_one hℓ]
    linarith
  linarith

theorem saddleNegativeContourOrdinate_add_rate_le_three {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ)
    (hN : 2 * ((N + 1 : ℕ) : ℝ) ≤ ℓ) :
    saddleNegativeContourOrdinate ℓ N + saddleNegativeGammaRate ℓ N ≤ 3 := by
  unfold saddleNegativeContourOrdinate saddleNegativeGammaRate
  push_cast at hN
  have h : (2 * (N : ℝ) + 1) / ℓ + (2 * (N : ℝ) + 3) / ℓ ≤ 2 := by
    rw [← add_div, div_le_iff₀ hℓ]
    linarith
  linarith

theorem upperNegativeContour_reflectedGamma_damping_exp_le_cosh {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ)
    (s : ℝ) :
    exp (2 * D_γ ℓ (saddleNegativeGammaRate ℓ N) (-s / ℓ)) ≤ cosh (π * (s / 2)) := by
  have hq : (0 : ℝ) < (N : ℝ) + 3 / 2 := by positivity
  have hΓ : 0 < Gamma ((N : ℝ) + 3 / 2) := Gamma_pos_of_pos hq
  have hmod : ‖Complex.Gamma (((N : ℂ) + 3 / 2) + I * (s / 2 : ℂ))‖ =
      Gamma ((N : ℝ) + 3 / 2) * exp (-D_γ ℓ (saddleNegativeGammaRate ℓ N) (-s / ℓ)) := by
    have hℓ' : (ℓ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hℓ.ne'
    have h := upperGammaShifted_modulus_eq_exp_neg_damping hℓ (saddleNegativeGammaRate_pos hℓ N)
      (-s / ℓ)
    push_cast at h
    rwa [show ℓ * saddleNegativeGammaRate ℓ N / 2 = (N : ℝ) + 3 / 2 by
        unfold saddleNegativeGammaRate; field_simp [hℓ.ne'],
      show (ℓ * saddleNegativeGammaRate ℓ N / 2 : ℂ) - I * ((ℓ : ℂ) * (-s / ℓ : ℂ) / 2) =
        ((N : ℂ) + 3 / 2) + I * (s / 2 : ℂ) by
        unfold saddleNegativeGammaRate
        push_cast
        field_simp
        ring] at h
  have hhalf := upperPositiveHalfGamma_scaled_sq_le (N + 1) (s / 2)
  rw [show ((N + 1 : ℕ) : ℝ) + 1 / 2 = (N : ℝ) + 3 / 2 by push_cast; ring,
    show ((N + 1 : ℕ) : ℂ) + 1 / 2 + I * ((s / 2 : ℝ) : ℂ) =
      ((N : ℂ) + 3 / 2) + I * (s / 2 : ℂ) by push_cast; ring, hmod, mul_pow] at hhalf
  set D : ℝ := D_γ ℓ (saddleNegativeGammaRate ℓ N) (-s / ℓ) with hD
  have hcancel : 1 ≤ exp (-D) ^ 2 * cosh (π * (s / 2)) := by nlinarith [pow_pos hΓ 2]
  have hinv : exp (2 * D) * (exp (-D) ^ 2 * cosh (π * (s / 2))) = cosh (π * (s / 2)) := by
    rw [← mul_assoc, sq, ← exp_add, ← exp_add, show 2 * D + (-D + -D) = 0 by ring, exp_zero,
      one_mul]
  linarith [mul_le_mul_of_nonneg_left hcancel (exp_pos (2 * D)).le]

theorem upperNegativeHalfGamma_reflection_norm (N : ℕ) (s : ℝ) :
    ‖Complex.Gamma (upperNegativeHalfGammaArgument N s)‖ *
        ‖Complex.Gamma (((N : ℂ) + 3 / 2) + I * (s / 2 : ℂ))‖ =
      π / cosh (π * (s / 2)) := by
  induction N with
  | zero =>
    have hz : ((1 / 2 : ℂ) + I * (s / 2 : ℂ)) ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre
    have hargneg : upperNegativeHalfGammaArgument 0 s = -((1 / 2 : ℂ) + I * (s / 2 : ℂ)) := by
      unfold upperNegativeHalfGammaArgument
      push_cast
      ring
    have hnegNorm : ‖Complex.Gamma ((1 / 2 : ℂ) + I * (s / 2 : ℂ))‖ =
        ‖(1 / 2 : ℂ) + I * (s / 2 : ℂ)‖ *
          ‖Complex.Gamma (-((1 / 2 : ℂ) + I * (s / 2 : ℂ)))‖ := by
      have h := Complex.norm_Gamma_add_one (neg_ne_zero.mpr hz)
      rwa [show -((1 / 2 : ℂ) + I * (s / 2 : ℂ)) + 1 =
          starRingEnd ℂ ((1 / 2 : ℂ) + I * (s / 2 : ℂ)) by
            simp only [map_add, map_div₀, Complex.conj_ofReal, Complex.conj_I, Complex.conj_ofNat,
              map_mul, map_one]
            ring,
        Complex.Gamma_conj, Complex.norm_conj, norm_neg] at h
    rw [hargneg, show (((0 : ℕ) : ℂ) + 3 / 2) + I * (s / 2 : ℂ) =
      ((1 / 2 : ℂ) + I * (s / 2 : ℂ)) + 1 by push_cast; ring, Complex.norm_Gamma_add_one hz]
    calc ‖Complex.Gamma (-((1 / 2 : ℂ) + I * (s / 2 : ℂ)))‖ *
          (‖(1 / 2 : ℂ) + I * (s / 2 : ℂ)‖ *
            ‖Complex.Gamma ((1 / 2 : ℂ) + I * (s / 2 : ℂ))‖) =
          ‖(1 / 2 : ℂ) + I * (s / 2 : ℂ)‖ *
            ‖Complex.Gamma (-((1 / 2 : ℂ) + I * (s / 2 : ℂ)))‖ *
            ‖Complex.Gamma ((1 / 2 : ℂ) + I * (s / 2 : ℂ))‖ := by ring
      _ = ‖Complex.Gamma ((1 / 2 : ℂ) + I * (s / 2 : ℂ))‖ ^ 2 := by rw [← hnegNorm, sq]
      _ = π / cosh (π * (s / 2)) := by
        rw [show (s / 2 : ℂ) = ((s / 2 : ℝ) : ℂ) by push_cast; ring]
        exact Complex.norm_Gamma_one_half_add_I_mul_sq (s / 2)
  | succ N ih =>
    have hq : (0 : ℝ) < (N : ℝ) + 3 / 2 := by positivity
    have hz : (((N : ℂ) + 3 / 2) + I * (s / 2 : ℂ)) ≠ 0 := fun h ↦
      hq.ne' (by simpa using congrArg Complex.re h)
    have hnormarg : ‖upperNegativeHalfGammaArgument (N + 1) s‖ =
        ‖((N : ℂ) + 3 / 2) + I * (s / 2 : ℂ)‖ := by
      rw [show upperNegativeHalfGammaArgument (N + 1) s =
        -(((N : ℂ) + 3 / 2) + I * (s / 2 : ℂ)) by
          unfold upperNegativeHalfGammaArgument; push_cast; ring, norm_neg]
    have hnegNorm : ‖Complex.Gamma (upperNegativeHalfGammaArgument N s)‖ =
        ‖((N : ℂ) + 3 / 2) + I * (s / 2 : ℂ)‖ *
          ‖Complex.Gamma (upperNegativeHalfGammaArgument (N + 1) s)‖ := by
      have h := Complex.norm_Gamma_add_one (upperNegativeHalfGammaArgument_ne_zero (N + 1) s)
      rwa [upperNegativeHalfGammaArgument_succ_add_one, hnormarg] at h
    rw [show (((N + 1 : ℕ) : ℂ) + 3 / 2) + I * (s / 2 : ℂ) =
      (((N : ℂ) + 3 / 2) + I * (s / 2 : ℂ)) + 1 by push_cast; ring,
      Complex.norm_Gamma_add_one hz, ← ih, hnegNorm]
    ring

theorem upperNegativeHalfGamma_norm_eq_reflected_damping {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) (s : ℝ) :
    ‖Complex.Gamma (upperNegativeHalfGammaArgument N s)‖ =
      π / Gamma ((N : ℝ) + 3 / 2) * exp (D_γ ℓ (saddleNegativeGammaRate ℓ N) (-s / ℓ)) /
        cosh (π * (s / 2)) := by
  have hq : (0 : ℝ) < (N : ℝ) + 3 / 2 := by positivity
  have hΓ : 0 < Gamma ((N : ℝ) + 3 / 2) := Gamma_pos_of_pos hq
  have hmod : ‖Complex.Gamma (((N : ℂ) + 3 / 2) + I * (s / 2 : ℂ))‖ =
      Gamma ((N : ℝ) + 3 / 2) * exp (-D_γ ℓ (saddleNegativeGammaRate ℓ N) (-s / ℓ)) := by
    have hℓ' : (ℓ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hℓ.ne'
    have h := upperGammaShifted_modulus_eq_exp_neg_damping hℓ (saddleNegativeGammaRate_pos hℓ N)
      (-s / ℓ)
    push_cast at h
    rwa [show ℓ * saddleNegativeGammaRate ℓ N / 2 = (N : ℝ) + 3 / 2 by
        unfold saddleNegativeGammaRate; field_simp [hℓ.ne'],
      show (ℓ * saddleNegativeGammaRate ℓ N / 2 : ℂ) - I * ((ℓ : ℂ) * (-s / ℓ : ℂ) / 2) =
        ((N : ℂ) + 3 / 2) + I * (s / 2 : ℂ) by
        unfold saddleNegativeGammaRate
        push_cast
        field_simp
        ring] at h
  have href := upperNegativeHalfGamma_reflection_norm N s
  rw [hmod, exp_neg] at href
  field_simp [hΓ.ne', (exp_pos (D_γ ℓ (saddleNegativeGammaRate ℓ N) (-s / ℓ))).ne',
    (cosh_pos (π * (s / 2))).ne'] at href ⊢
  simpa [mul_comm, mul_left_comm, mul_assoc] using href

theorem upper_log_cosh_ge_abs_sub_log_two (x : ℝ) : |x| - log 2 ≤ log (cosh x) := by
  apply exp_le_exp.mp
  rw [exp_log (cosh_pos x), exp_sub, exp_log (by norm_num : (0 : ℝ) < 2), ← cosh_abs, cosh_eq]
  linarith [(exp_pos (-|x|)).le]

theorem upperNegativeContour_gamma_mul_exp_short_le {ε ℓ : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (N : ℕ) (hN : 2 * ((N + 1 : ℕ) : ℝ) ≤ ℓ) (horder : a₀ε ε ≤ Aε ε)
    (hmargin : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a) (s : ℝ) :
    ‖Complex.Gamma (upperNegativeHalfGammaArgument N s)‖ *
        exp (D_s ε ℓ (-saddleNegativeContourOrdinate ℓ N - 1) (-s / ℓ)) ≤
      π / Gamma ((N : ℝ) + 3 / 2) * exp (ε * log 2) * exp (-(ε / 2) * π * |s|) := by
  have hpref : (0 : ℝ) ≤ π / Gamma ((N : ℝ) + 3 / 2) :=
    div_nonneg pi_pos.le (Gamma_pos_of_pos (by positivity)).le
  have hC : 0 < cosh (π * (s / 2)) := cosh_pos _
  set D : ℝ := D_γ ℓ (saddleNegativeGammaRate ℓ N) (-s / ℓ) with hD
  have hDnonneg : 0 ≤ D := upperGammaDamping_nonneg hℓ _
  have hDlog : 2 * D ≤ log (cosh (π * (s / 2))) := by
    apply exp_le_exp.mp
    rw [exp_log hC]
    exact upperNegativeContour_reflectedGamma_damping_exp_le_cosh hℓ N s
  have hlogphase : (2 - 2 * ε) * D - log (cosh (π * (s / 2))) ≤ ε * log 2 - ε / 2 * π * |s| := by
    have hlog := upper_log_cosh_ge_abs_sub_log_two (π * (s / 2))
    rw [show |π * (s / 2)| = π * |s| / 2 by
      rw [abs_mul, abs_of_pos pi_pos, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      ring] at hlog
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 2 - 2 * ε by linarith)
        (show 0 ≤ log (cosh (π * (s / 2))) - 2 * D by linarith),
      mul_nonneg (show (0 : ℝ) ≤ ε by positivity)
        (show 0 ≤ log (cosh (π * (s / 2))) - (π * |s| / 2 - log 2) by linarith)]
  have hshort : D_s ε ℓ (-saddleNegativeContourOrdinate ℓ N - 1) (-s / ℓ) ≤ (1 - 2 * ε) * D :=
    upperNegativeContour_shortDamping_le_gamma hε hεsmall hℓ
      (one_le_saddleNegativeContourOrdinate hℓ N) (saddleNegativeGammaRate_pos hℓ N)
      (saddleNegativeContourOrdinate_add_rate_le_three hℓ N hN) horder hmargin (-s / ℓ)
  rw [upperNegativeHalfGamma_norm_eq_reflected_damping hℓ N s, ← hD]
  calc π / Gamma ((N : ℝ) + 3 / 2) * exp D / cosh (π * (s / 2)) *
        exp (D_s ε ℓ (-saddleNegativeContourOrdinate ℓ N - 1) (-s / ℓ)) ≤
        π / Gamma ((N : ℝ) + 3 / 2) * exp D / cosh (π * (s / 2)) * exp ((1 - 2 * ε) * D) := by
        gcongr
    _ = π / Gamma ((N : ℝ) + 3 / 2) *
          exp ((2 - 2 * ε) * D - log (cosh (π * (s / 2)))) := by
        rw [exp_sub, exp_log hC, show (2 - 2 * ε) * D = D + (1 - 2 * ε) * D by ring, exp_add]
        ring
    _ ≤ π / Gamma ((N : ℝ) + 3 / 2) * exp (ε * log 2 - ε / 2 * π * |s|) := by gcongr
    _ = π / Gamma ((N : ℝ) + 3 / 2) * exp (ε * log 2) * exp (-(ε / 2) * π * |s|) := by
        rw [show ε * log 2 - ε / 2 * π * |s| = ε * log 2 + -(ε / 2) * π * |s| by ring, exp_add]
        ring

theorem upperShortShellDamping_neg_frequency (ε ℓ δ T : ℝ) : D_s ε ℓ δ (-T) = D_s ε ℓ δ T := by
  unfold D_s
  congr 1
  refine intervalIntegral.integral_congr fun a _ ↦ ?_
  simp only [mul_neg, cos_neg]

theorem saddleTaylorContour_gammaArgument (N : ℕ) (s : ℝ) :
    ((saddleTaylorContour N : ℂ) + (s : ℂ) * I) / 2 = upperNegativeHalfGammaArgument N (-s) := by
  unfold saddleTaylorContour upperNegativeHalfGammaArgument
  push_cast
  ring

theorem saddleTaylorContour_shellArgument {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) (s : ℝ) :
    I * ((saddleTaylorContour N : ℂ) + (s : ℂ) * I - (ℓ : ℂ)) / (ℓ : ℂ) =
      (-s / ℓ : ℂ) + I * (-saddleNegativeContourOrdinate ℓ N : ℂ) := by
  unfold saddleTaylorContour saddleNegativeContourOrdinate
  push_cast
  field_simp [hℓ.ne']
  ring_nf
  simp [Complex.I_sq]
  ring

theorem upperNegativeContour_gamma_mul_shellExponential_le {ε ℓ : ℝ} (hε : 0 < ε)
    (hεsmall : ε ≤ 1 / 4) (hℓ : 0 < ℓ) (N : ℕ) (hN : 2 * ((N + 1 : ℕ) : ℝ) ≤ ℓ)
    (horder : a₀ε ε ≤ Aε ε) (hmargin : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a) (s : ℝ) :
    ‖Complex.Gamma (((saddleTaylorContour N : ℂ) + (s : ℂ) * I) / 2) *
        Complex.exp ((ℓ : ℂ) * h_ε ε (I * ((saddleTaylorContour N : ℂ) + (s : ℂ) * I -
          (ℓ : ℂ)) / (ℓ : ℂ)))‖ ≤
      exp (ℓ * h_εI ε (saddleNegativeContourOrdinate ℓ N)) *
        (π / Gamma ((N : ℝ) + 3 / 2) * exp (ε * log 2) * exp (-(ε / 2) * π * |s|)) := by
  have hP : 0 ≤ D_B ε ℓ (-saddleNegativeContourOrdinate ℓ N - 1) (-s / ℓ) :=
    positiveShellDamping_nonneg hℓ.le
  have hgamma' : ‖Complex.Gamma (upperNegativeHalfGammaArgument N (-s))‖ *
      exp (D_s ε ℓ (-saddleNegativeContourOrdinate ℓ N - 1) (-s / ℓ)) ≤
        π / Gamma ((N : ℝ) + 3 / 2) * exp (ε * log 2) * exp (-(ε / 2) * π * |s|) := by
    have h := upperNegativeContour_gamma_mul_exp_short_le hε hεsmall hℓ N hN horder hmargin (-s)
    rwa [show -(-s) / ℓ = -(-s / ℓ) by ring, upperShortShellDamping_neg_frequency, abs_neg] at h
  have hshell : ‖Complex.exp ((ℓ : ℂ) * h_ε ε ((-s / ℓ : ℂ) +
      I * (-saddleNegativeContourOrdinate ℓ N : ℂ)))‖ =
      exp (ℓ * h_εI ε (saddleNegativeContourOrdinate ℓ N)) *
        exp (-(D_B ε ℓ (-saddleNegativeContourOrdinate ℓ N - 1) (-s / ℓ) -
          D_s ε ℓ (-saddleNegativeContourOrdinate ℓ N - 1) (-s / ℓ))) := by
    have h := norm_saddleShellExponential_eq_exp_neg_damping hε horder ℓ (-s / ℓ)
      (-saddleNegativeContourOrdinate ℓ N)
    rw [realHyperbolicShellPhase_neg] at h
    push_cast at h
    exact h
  rw [saddleTaylorContour_gammaArgument, saddleTaylorContour_shellArgument hℓ N s, norm_mul, hshell]
  calc ‖Complex.Gamma (upperNegativeHalfGammaArgument N (-s))‖ *
        (exp (ℓ * h_εI ε (saddleNegativeContourOrdinate ℓ N)) *
          exp (-(D_B ε ℓ (-saddleNegativeContourOrdinate ℓ N - 1) (-s / ℓ) -
            D_s ε ℓ (-saddleNegativeContourOrdinate ℓ N - 1) (-s / ℓ)))) ≤
        ‖Complex.Gamma (upperNegativeHalfGammaArgument N (-s))‖ *
          (exp (ℓ * h_εI ε (saddleNegativeContourOrdinate ℓ N)) *
            exp (D_s ε ℓ (-saddleNegativeContourOrdinate ℓ N - 1) (-s / ℓ))) := by
        gcongr
        linarith
    _ = exp (ℓ * h_εI ε (saddleNegativeContourOrdinate ℓ N)) *
          (‖Complex.Gamma (upperNegativeHalfGammaArgument N (-s))‖ *
            exp (D_s ε ℓ (-saddleNegativeContourOrdinate ℓ N - 1) (-s / ℓ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hgamma' (exp_pos _).le

/-- The frequency majorant `(1 + |s|)³ e^{-επ|s|/2}` of the negative-contour integrand. -/
def saddleNegativeFrequencyMajorant (ε s : ℝ) : ℝ := (1 + |s|) ^ 3 * exp (-(ε / 2) * π * |s|)

theorem saddleNegativeFrequencyMajorant_integrable {ε : ℝ} (hε : 0 < ε) :
    Integrable (saddleNegativeFrequencyMajorant ε) := by
  have hrate : 0 < ε / 2 * π := mul_pos (by positivity) pi_pos
  refine ((integrable_abs_pow_mul_exp_neg_mul_abs 0 hrate).add
    (((integrable_abs_pow_mul_exp_neg_mul_abs 1 hrate).const_mul 3).add
      (((integrable_abs_pow_mul_exp_neg_mul_abs 2 hrate).const_mul 3).add
        (integrable_abs_pow_mul_exp_neg_mul_abs 3 hrate)))).congr ?_
  filter_upwards [] with s
  unfold saddleNegativeFrequencyMajorant
  simp only [Pi.add_apply, pow_zero, pow_one]
  ring_nf

theorem norm_plusPolynomial_negativeContour_le {ε ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ)
    (hN : 2 * ((N + 1 : ℕ) : ℝ) ≤ ℓ) (s : ℝ) :
    ‖PPlus ε (I * ((saddleTaylorContour N : ℂ) + (s : ℂ) * I - (ℓ : ℂ)) / (ℓ : ℂ))‖ ≤
      27 * (1 + |β ε|) * (1 + |s|) ^ 3 := by
  have hκ := one_le_saddleNegativeContourOrdinate hℓ N
  have hκtop := saddleNegativeContourOrdinate_le_two hℓ N hN
  have hℓone : 1 ≤ ℓ := by
    push_cast at hN
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have hbase : 1 + ‖(-s / ℓ : ℂ) + I * (-saddleNegativeContourOrdinate ℓ N : ℂ)‖ ≤
      3 * (1 + |s|) := by
    have hnorm : ‖(-s / ℓ : ℂ) + I * (-saddleNegativeContourOrdinate ℓ N : ℂ)‖ ≤
        |s| / ℓ + saddleNegativeContourOrdinate ℓ N := by
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hℓ,
        abs_of_nonneg (show (0 : ℝ) ≤ saddleNegativeContourOrdinate ℓ N by linarith)]
    have hdivide : |s| / ℓ ≤ |s| := div_le_self (abs_nonneg s) hℓone
    linarith [abs_nonneg s]
  rw [saddleTaylorContour_shellArgument hℓ N s]
  calc ‖PPlus ε ((-s / ℓ : ℂ) + I * (-saddleNegativeContourOrdinate ℓ N : ℂ))‖ ≤
        (1 + |β ε|) * (1 + ‖(-s / ℓ : ℂ) +
          I * (-saddleNegativeContourOrdinate ℓ N : ℂ)‖) ^ 3 := norm_plusPolynomial_le ε _
    _ ≤ (1 + |β ε|) * (3 * (1 + |s|)) ^ 3 := by gcongr
    _ = 27 * (1 + |β ε|) * (1 + |s|) ^ 3 := by ring

/-- The `s`-independent factor of the negative-contour majorant for `M₊`. -/
def saddleNegativeMellinMajorantCoefficient (ε ℓ : ℝ) (N : ℕ) : ℝ :=
  27 * (1 + |β ε|) * exp (ε * log 2) * (π / Gamma ((N : ℝ) + 3 / 2)) *
    exp ((ℓ - saddleTaylorContour N) * log π / 2) *
    exp (ℓ * h_εI ε (saddleNegativeContourOrdinate ℓ N))

theorem plusSaddleMellinData_negativeContour_norm_le {ε ℓ : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (N : ℕ) (hN : 2 * ((N + 1 : ℕ) : ℝ) ≤ ℓ) (horder : a₀ε ε ≤ Aε ε)
    (hmargin : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a) (s : ℝ) :
    ‖MPlus ε ℓ ((saddleTaylorContour N : ℂ) + (s : ℂ) * I)‖ ≤
      saddleNegativeMellinMajorantCoefficient ε ℓ N * saddleNegativeFrequencyMajorant ε s := by
  have hfactor := upperNegativeContour_gamma_mul_shellExponential_le hε hεsmall hℓ N hN horder
    hmargin s
  have hpoly := norm_plusPolynomial_negativeContour_le (ε := ε) hℓ N hN s
  have hpi : ‖Complex.exp (((ℓ : ℂ) - ((saddleTaylorContour N : ℂ) + (s : ℂ) * I)) *
      (log π : ℂ) / 2)‖ = exp ((ℓ - saddleTaylorContour N) * log π / 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  unfold MPlus mellinEnvelope
  rw [norm_mul, norm_mul, norm_mul, hpi]
  calc exp ((ℓ - saddleTaylorContour N) * log π / 2) *
        ‖Complex.Gamma (((saddleTaylorContour N : ℂ) + (s : ℂ) * I) / 2)‖ *
        ‖Complex.exp ((ℓ : ℂ) * h_ε ε (I * ((saddleTaylorContour N : ℂ) + (s : ℂ) * I -
          (ℓ : ℂ)) / (ℓ : ℂ)))‖ *
        ‖PPlus ε (I * ((saddleTaylorContour N : ℂ) + (s : ℂ) * I - (ℓ : ℂ)) / (ℓ : ℂ))‖ =
        exp ((ℓ - saddleTaylorContour N) * log π / 2) *
          (‖Complex.Gamma (((saddleTaylorContour N : ℂ) + (s : ℂ) * I) / 2) *
            Complex.exp ((ℓ : ℂ) * h_ε ε (I * ((saddleTaylorContour N : ℂ) + (s : ℂ) * I -
              (ℓ : ℂ)) / (ℓ : ℂ)))‖) *
          ‖PPlus ε (I * ((saddleTaylorContour N : ℂ) + (s : ℂ) * I - (ℓ : ℂ)) / (ℓ : ℂ))‖ := by
        rw [norm_mul]
        ring
    _ ≤ exp ((ℓ - saddleTaylorContour N) * log π / 2) *
          (exp (ℓ * h_εI ε (saddleNegativeContourOrdinate ℓ N)) *
            (π / Gamma ((N : ℝ) + 3 / 2) * exp (ε * log 2) * exp (-(ε / 2) * π * |s|))) *
          (27 * (1 + |β ε|) * (1 + |s|) ^ 3) := by gcongr
    _ = saddleNegativeMellinMajorantCoefficient ε ℓ N * saddleNegativeFrequencyMajorant ε s := by
        unfold saddleNegativeMellinMajorantCoefficient saddleNegativeFrequencyMajorant
        ring

/-- The total mass `∫ (1 + |s|)³ e^{-επ|s|/2} ds` of the frequency majorant. -/
def saddleNegativeFrequencyMass (ε : ℝ) : ℝ := ∫ s : ℝ, saddleNegativeFrequencyMajorant ε s

theorem saddleNegativeFrequencyMass_nonneg (ε : ℝ) : 0 ≤ saddleNegativeFrequencyMass ε :=
  integral_nonneg fun s ↦ by
    unfold saddleNegativeFrequencyMajorant
    positivity

theorem plusSaddleMellinData_negativeContour_integral_norm_le {ε ℓ : ℝ} (hε : 0 < ε)
    (hεsmall : ε ≤ 1 / 4) (hℓ : 0 < ℓ) (N : ℕ) (hN : 2 * ((N + 1 : ℕ) : ℝ) ≤ ℓ)
    (horder : a₀ε ε ≤ Aε ε) (hmargin : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a) :
    (∫ s : ℝ, ‖MPlus ε ℓ ((saddleTaylorContour N : ℂ) + (s : ℂ) * I)‖) ≤
      saddleNegativeMellinMajorantCoefficient ε ℓ N * saddleNegativeFrequencyMass ε := by
  have hdata : Integrable fun s : ℝ ↦ MPlus ε ℓ ((saddleTaylorContour N : ℂ) + (s : ℂ) * I) := by
    simpa using plusSaddleMellinData_shiftedLine_moment_integrable hε hℓ horder
      (fun n : ℕ ↦ saddleTaylorContour_ne_pole N n) 0
  calc (∫ s : ℝ, ‖MPlus ε ℓ ((saddleTaylorContour N : ℂ) + (s : ℂ) * I)‖) ≤
        ∫ s : ℝ, saddleNegativeMellinMajorantCoefficient ε ℓ N *
          saddleNegativeFrequencyMajorant ε s :=
        integral_mono hdata.norm ((saddleNegativeFrequencyMajorant_integrable hε).const_mul _)
          fun s ↦ plusSaddleMellinData_negativeContour_norm_le hε hεsmall hℓ N hN horder hmargin s
    _ = saddleNegativeMellinMajorantCoefficient ε ℓ N * saddleNegativeFrequencyMass ε := by
        rw [integral_const_mul]
        rfl

theorem plusSaddleTaylorRemainder_negativeContour_bound {ε ℓ : ℝ} (hε : 0 < ε)
    (hεsmall : ε ≤ 1 / 4) (hℓ : 0 < ℓ) (N : ℕ) (hN : 2 * ((N + 1 : ℕ) : ℝ) ≤ ℓ)
    (horder : a₀ε ε ≤ Aε ε) (hmargin : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a) {r : ℝ} (hr : 0 < r) :
    ‖plusSaddleTaylorRemainder ε ℓ N r‖ ≤ 1 / (2 * π) * r ^ (2 * N + 1) *
      saddleNegativeMellinMajorantCoefficient ε ℓ N * saddleNegativeFrequencyMass ε := by
  have hdata : Integrable fun t : ℝ ↦
      MPlus ε ℓ ((saddleTaylorContour N : ℂ) + (t : ℂ) * I) := by
    simpa using plusSaddleMellinData_shiftedLine_moment_integrable hε hℓ horder
      (fun n : ℕ ↦ saddleTaylorContour_ne_pole N n) 0
  have hnorm : ‖(2 * π : ℂ)⁻¹‖ = 1 / (2 * π) := by
    rw [norm_inv, one_div]
    congr 1
    simp [abs_of_pos Real.pi_pos]
  unfold plusSaddleTaylorRemainder
  rw [norm_mul, hnorm]
  calc 1 / (2 * π) * ‖∫ t : ℝ, saddleMellinInversePower r ((saddleTaylorContour N : ℂ) +
        (t : ℂ) * I) * MPlus ε ℓ ((saddleTaylorContour N : ℂ) + (t : ℂ) * I)‖ ≤
        1 / (2 * π) * ∫ t : ℝ, ‖saddleMellinInversePower r ((saddleTaylorContour N : ℂ) +
          (t : ℂ) * I) * MPlus ε ℓ ((saddleTaylorContour N : ℂ) + (t : ℂ) * I)‖ := by
        gcongr
        exact norm_integral_le_integral_norm _
    _ = 1 / (2 * π) * (r ^ (2 * N + 1) *
          ∫ t : ℝ, ‖MPlus ε ℓ ((saddleTaylorContour N : ℂ) + (t : ℂ) * I)‖) := by
        rw [saddleMellinInversePower_shiftedLine_integral_norm hr (MPlus ε ℓ) hdata,
          saddleTaylorContour_rpow]
    _ ≤ 1 / (2 * π) * (r ^ (2 * N + 1) * (saddleNegativeMellinMajorantCoefficient ε ℓ N *
          saddleNegativeFrequencyMass ε)) := by
        gcongr
        exact plusSaddleMellinData_negativeContour_integral_norm_le hε hεsmall hℓ N hN horder
          hmargin
    _ = _ := by ring

theorem saddleSmallRadiusVariable_sqrt_eq_source (ε : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    √(y_r ε r) = r * exp (log π / 2 + h₁' ε) := by
  have hsq : (r * exp (log π / 2 + h₁' ε)) ^ 2 = y_r ε r := by
    rw [mul_pow, ← exp_nat_mul, y_r]
    rw [show ((2 : ℕ) : ℝ) * (log π / 2 + h₁' ε) = log π + 2 * h₁' ε by push_cast; ring, exp_add,
      exp_log pi_pos]
    ring
  rw [← hsq, sqrt_sq (by positivity)]

theorem saddleSmallRadiusVariable_halfIntegerFactor (ε : ℝ) {r : ℝ} (hr : 0 ≤ r) (N : ℕ) :
    r ^ (2 * N + 1) * exp (((2 * N + 1 : ℕ) : ℝ) * (log π / 2 + h₁' ε)) =
      √(y_r ε r) * y_r ε r ^ N := by
  have hsqrt := saddleSmallRadiusVariable_sqrt_eq_source ε hr
  have hsq : (r * exp (log π / 2 + h₁' ε)) ^ 2 = y_r ε r := by
    rw [← hsqrt, sq_sqrt (saddleSmallRadiusVariable_nonneg ε r)]
  rw [exp_nat_mul, ← mul_pow, hsqrt, ← hsq, ← pow_mul, ← pow_succ']

/-- The phase error `λ(h_ε(κ) - h_ε(1)) - (2N+1)h₁'` of the negative Taylor contour. -/
def saddleNegativeContourPhaseError (ε ℓ : ℝ) (N : ℕ) : ℝ :=
  ℓ * (h_εI ε (saddleNegativeContourOrdinate ℓ N) - h_εI ε 1) - ((2 * N + 1 : ℕ) : ℝ) * h₁' ε

theorem mul_exp_mul_exp (k a b : ℝ) : k * exp a * exp b = k * exp (a + b) := by
  rw [mul_assoc, ← exp_add]

theorem mul_exp_div_exp (k a b c d : ℝ) :
    k * exp a * exp b / (exp c * exp d) = k * exp (a + b - c - d) := by
  rw [exp_sub, exp_sub, exp_add]
  field_simp

theorem saddleNegativeContour_sourceNormalizationFactor (ε ℓ : ℝ) (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    r ^ (2 * N + 1) * exp ((ℓ - saddleTaylorContour N) * log π / 2) *
        exp (ℓ * h_εI ε (saddleNegativeContourOrdinate ℓ N)) /
      (exp (ℓ / 2 * log π) * exp (ℓ * h_εI ε 1)) =
      √(y_r ε r) * y_r ε r ^ N * exp (saddleNegativeContourPhaseError ε ℓ N) := by
  rw [← saddleSmallRadiusVariable_halfIntegerFactor ε hr N, mul_exp_div_exp, mul_exp_mul_exp]
  unfold saddleNegativeContourPhaseError saddleTaylorContour
  push_cast
  ring_nf

/-- The relative size of the negative-contour majorant against the origin value `f₊(0)`. -/
def saddleNegativeRelativeCoefficient (ε : ℝ) : ℝ :=
  27 * (1 + |β ε|) * exp (ε * log 2) * saddleNegativeFrequencyMass ε / (4 * β ε)

theorem saddleNegativeRelativeCoefficient_nonneg {ε : ℝ} (hε : 0 < ε) :
    0 ≤ saddleNegativeRelativeCoefficient ε := by
  unfold saddleNegativeRelativeCoefficient
  have := saddleNegativeFrequencyMass_nonneg ε
  have := (beta_pos hε).le
  positivity

theorem saddleNegativeContour_normalizedMajorant_eq {ε : ℝ} (hε : 0 < ε) (ℓ : ℝ) (N : ℕ) {r : ℝ}
    (hr : 0 ≤ r) :
    1 / (2 * π) * r ^ (2 * N + 1) * saddleNegativeMellinMajorantCoefficient ε ℓ N *
        saddleNegativeFrequencyMass ε / originValue ε ℓ =
      saddleNegativeRelativeCoefficient ε * √(y_r ε r) * y_r ε r ^ N /
        Gamma ((N : ℝ) + 3 / 2) * exp (saddleNegativeContourPhaseError ε ℓ N) := by
  have hb : β ε ≠ 0 := (beta_pos hε).ne'
  have hΓ : Gamma ((N : ℝ) + 3 / 2) ≠ 0 := (Gamma_pos_of_pos (by positivity)).ne'
  have horigin : originValue ε ℓ = 2 * (exp (ℓ / 2 * log π) * exp (ℓ * h_εI ε 1)) * β ε := by
    unfold originValue
    rw [rpow_def_of_pos pi_pos, show log π * (ℓ / 2) = ℓ / 2 * log π by ring]
    ring
  calc 1 / (2 * π) * r ^ (2 * N + 1) * saddleNegativeMellinMajorantCoefficient ε ℓ N *
        saddleNegativeFrequencyMass ε / originValue ε ℓ =
        saddleNegativeRelativeCoefficient ε * (r ^ (2 * N + 1) *
          exp ((ℓ - saddleTaylorContour N) * log π / 2) *
          exp (ℓ * h_εI ε (saddleNegativeContourOrdinate ℓ N)) /
          (exp (ℓ / 2 * log π) * exp (ℓ * h_εI ε 1))) / Gamma ((N : ℝ) + 3 / 2) := by
        rw [horigin]
        unfold saddleNegativeMellinMajorantCoefficient saddleNegativeRelativeCoefficient
        field_simp [pi_pos.ne', hb, hΓ]
        ring
    _ = _ := by
        rw [saddleNegativeContour_sourceNormalizationFactor ε ℓ N hr]
        ring

theorem plusSaddleTaylorRemainder_negativeContour_relative_bound {ε ℓ : ℝ} (hε : 0 < ε)
    (hεsmall : ε ≤ 1 / 4) (hℓ : 0 < ℓ) (N : ℕ) (hN : 2 * ((N + 1 : ℕ) : ℝ) ≤ ℓ)
    (horder : a₀ε ε ≤ Aε ε) (hmargin : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a) {r : ℝ} (hr : 0 < r) :
    ‖plusSaddleTaylorRemainder ε ℓ N r / (originValue ε ℓ : ℂ)‖ ≤
      saddleNegativeRelativeCoefficient ε * √(y_r ε r) * y_r ε r ^ N /
        Gamma ((N : ℝ) + 3 / 2) * exp (saddleNegativeContourPhaseError ε ℓ N) := by
  have hO := saddleOriginValue_pos hε ℓ
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hO,
    ← saddleNegativeContour_normalizedMajorant_eq hε ℓ N hr.le]
  exact (div_le_div_iff_of_pos_right hO).mpr
    (plusSaddleTaylorRemainder_negativeContour_bound hε hεsmall hℓ N hN horder hmargin hr)

theorem exists_saddleNegativeContourPhaseError_bound {ε : ℝ} (hε : 0 < ε)
    (horder : a₀ε ε ≤ Aε ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ℓ : ℝ, 0 < ℓ → ∀ N : ℕ, 2 * ((N + 1 : ℕ) : ℝ) ≤ ℓ →
      |saddleNegativeContourPhaseError ε ℓ N| ≤ K * (2 * (N : ℝ) + 1) ^ 2 / ℓ := by
  obtain ⟨K, hK, hTaylor⟩ := exists_realHyperbolicShellPhase_quadratic_remainder hε horder
  refine ⟨K, hK, fun ℓ hℓ N hN ↦ ?_⟩
  have hscale : ℓ * (saddleNegativeContourOrdinate ℓ N - 1) = 2 * (N : ℝ) + 1 := by
    unfold saddleNegativeContourOrdinate
    field_simp
    ring
  have hidentity : saddleNegativeContourPhaseError ε ℓ N =
      ℓ * (h_εI ε (saddleNegativeContourOrdinate ℓ N) - h_εI ε 1 -
        (saddleNegativeContourOrdinate ℓ N - 1) * h₁' ε) := by
    unfold saddleNegativeContourPhaseError
    push_cast
    rw [← hscale]
    ring
  rw [hidentity, abs_mul, abs_of_pos hℓ]
  calc ℓ * |h_εI ε (saddleNegativeContourOrdinate ℓ N) - h_εI ε 1 -
        (saddleNegativeContourOrdinate ℓ N - 1) * h₁' ε| ≤
        ℓ * (K * (saddleNegativeContourOrdinate ℓ N - 1) ^ 2) :=
        mul_le_mul_of_nonneg_left (hTaylor _ ⟨one_le_saddleNegativeContourOrdinate hℓ N,
          saddleNegativeContourOrdinate_le_two hℓ N hN⟩) hℓ.le
    _ = K * (2 * (N : ℝ) + 1) ^ 2 / ℓ := by
        rw [← hscale]
        field_simp

theorem eventually_plusSaddleTaylorRemainder_relative_lt_half_on_star {ε : ℝ} (hε : 0 < ε)
    (hεsmall : ε ≤ 1 / 4) (horder : a₀ε ε ≤ Aε ε)
    (hmargin : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a) :
    ∀ᶠ d : ℕ in atTop, ∀ r : ℝ, 0 < r → r ≤ r_star ε d → let ℓ : ℝ := (d : ℝ) / 2
      let N : ℕ := N_ℓ ℓ
      let y : ℝ := y_r ε r
      exp y * ‖plusSaddleTaylorRemainder ε ℓ N r / (originValue ε ℓ : ℂ)‖ < 1 / 2 := by
  obtain ⟨C, hC, hstar⟩ := exists_eventually_y_star_le_log_eighth_add hε horder
  obtain ⟨K, -, hphase⟩ := exists_saddleNegativeContourPhaseError_bound hε horder
  have hKε := saddleNegativeRelativeCoefficient_nonneg hε
  filter_upwards [hstar, tendsto_saddleResidue_dimension_half.eventually
      (eventually_saddleNegative_relativeGammaTail_lt_half C K (saddleNegativeRelativeCoefficient ε)
        hC hKε),
    tendsto_saddleResidue_dimension_half.eventually
      eventually_saddleSmallResidueTruncation_succ_double_le,
    eventually_gt_atTop (0 : ℕ)] with d hcut htaild hNd hd r hr hrstar
  have hℓ : (0 : ℝ) < (d : ℝ) / 2 := by positivity
  have hy : 0 ≤ y_r ε r := saddleSmallRadiusVariable_nonneg ε r
  have hrelative := plusSaddleTaylorRemainder_negativeContour_relative_bound hε hεsmall hℓ
    (N_ℓ ((d : ℝ) / 2)) hNd horder hmargin hr
  calc exp (y_r ε r) * ‖plusSaddleTaylorRemainder ε ((d : ℝ) / 2) (N_ℓ ((d : ℝ) / 2)) r /
        (originValue ε ((d : ℝ) / 2) : ℂ)‖ ≤
        exp (y_r ε r) * (saddleNegativeRelativeCoefficient ε * √(y_r ε r) *
          y_r ε r ^ N_ℓ ((d : ℝ) / 2) / Gamma ((N_ℓ ((d : ℝ) / 2) : ℝ) + 3 / 2) *
          exp (saddleNegativeContourPhaseError ε ((d : ℝ) / 2) (N_ℓ ((d : ℝ) / 2)))) := by
        gcongr
    _ ≤ exp (y_r ε r) * (saddleNegativeRelativeCoefficient ε * √(y_r ε r) *
          y_r ε r ^ N_ℓ ((d : ℝ) / 2) / Gamma ((N_ℓ ((d : ℝ) / 2) : ℝ) + 3 / 2) *
          exp (K * (2 * (N_ℓ ((d : ℝ) / 2) : ℝ) + 1) ^ 2 / ((d : ℝ) / 2))) := by
        gcongr
        exact (le_abs_self _).trans (hphase _ hℓ _ hNd)
    _ < 1 / 2 := htaild (y_r ε r) hy (hcut r hr.le hrstar)

theorem eventually_plusSaddleProfile_re_pos_on_star_fixed {ε : ℝ} (hε : 0 < ε)
    (hεsmall : ε ≤ 1 / 4) (horder : a₀ε ε ≤ Aε ε)
    (hmargin : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a) :
    ∀ᶠ d : ℕ in atTop, ∀ r : ℝ, 0 ≤ r → r ≤ r_star ε d → 0 < (fPlus ε ((d : ℝ) / 2) r).re := by
  filter_upwards [eventually_plusSaddleSmallRadius_relativeFiniteResidue_lt_half_on_star hε horder,
    eventually_plusSaddleTaylorRemainder_relative_lt_half_on_star hε hεsmall horder hmargin,
    eventually_gt_atTop (0 : ℕ)] with d hfinite_d hrem_d hd r hr hrstar
  rcases eq_or_lt_of_le hr with hzero | hrpos
  · simpa [fPlus, ← hzero] using saddleOriginValue_pos hε ((d : ℝ) / 2)
  · exact plusSaddleProfile_re_pos_of_relative_residue_bounds hε (by positivity) horder hrpos
      (N_ℓ ((d : ℝ) / 2)) (by simpa using hfinite_d r hr hrstar)
      (by simpa using hrem_d r hrpos hrstar)

/-- Report (82): for all small `ε` and large `d`, `f₊` is positive on `[0, r_*]`. -/
theorem eventually_plusSaddleProfile_re_pos_on_star : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    ∀ᶠ d : ℕ in atTop, ∀ r : ℝ, 0 ≤ r → r ≤ r_star ε d → 0 < (fPlus ε ((d : ℝ) / 2) r).re := by
  have hsmall := (tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [self_mem_nhdsWithin, hsmall, eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_upper_shortMargin_positive] with ε hε hεsmall horder hmargin
  exact eventually_plusSaddleProfile_re_pos_on_star_fixed hε hεsmall.le horder
    fun a ha ↦ by linarith [hmargin a ha]

end

end CohnElkies
