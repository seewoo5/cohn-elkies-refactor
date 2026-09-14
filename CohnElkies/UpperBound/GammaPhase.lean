import CohnElkies.UpperBound.SaddleContour
import CohnElkiesForMathlib.Analysis.SpecialFunctions.FrullaniIntegral
import CohnElkiesForMathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# The Taylor expansion of the phase on the saddle contour (report §4.3, (71)–(73))

The phase `e^{iθ}` and its Taylor remainders, the Gamma kernel `G_{λ,η}` and its expansion via
the Euler integral of `log Γ` (Frullani and Laplace integrals, the Real.digamma function), the shell
phase expansion, the stationary point `v_λ` of the log-radius on the contour, and the bound
`|e^{L(T)} - Gaussian| ≤ C |T|³` for the centered integrand
(`centeredIntegrand_centralGaussianError_le`).
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory Real Set intervalIntegral
open scoped Topology

/-- The unimodular phase `x ↦ e^{ix}`. -/
def expI (x : ℝ) : ℂ := Complex.exp (I * x)

theorem norm_expI (x : ℝ) : ‖expI x‖ = 1 := Complex.norm_exp_I_mul_ofReal x

theorem contDiff_expI : ContDiff ℝ (⊤ : WithTop ℕ∞) expI :=
  (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

theorem hasDerivAt_expI (x : ℝ) : HasDerivAt expI (I * expI x) x := by
  have hreal : HasDerivAt (fun t : ℝ ↦ (t : ℂ)) (1 : ℂ) x := by
    simpa using! Complex.ofRealCLM.hasDerivAt
  have hlin : HasDerivAt (fun t : ℝ ↦ I * (t : ℂ)) I x := by
    convert! hreal.const_mul I using 1
    all_goals simp
  convert! hlin.cexp using 1
  all_goals simp [expI, mul_comm]

theorem iteratedDeriv_expI (n : ℕ) (x : ℝ) : iteratedDeriv n expI x = I ^ n * expI x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, funext ih, ((hasDerivAt_expI x).const_mul (I ^ n)).deriv]
    ring

theorem iteratedDerivWithin_expI {x₀ x t : ℝ} (h : x₀ ≠ x) (ht : t ∈ uIcc x₀ x) (n : ℕ) :
    iteratedDerivWithin n expI (uIcc x₀ x) t = I ^ n * expI t := by
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc h)
    (contDiff_expI.contDiffAt.of_le le_top) ht, iteratedDeriv_expI]

/-- Third-order Taylor bound for the phase: `‖e^{ix} - 1 - ix + x²/2‖ ≤ |x|³/6`. -/
theorem norm_expI_sub_taylor_le (x : ℝ) :
    ‖expI x - 1 - I * (x : ℂ) + (x ^ 2 / 2 : ℂ)‖ ≤ |x| ^ 3 / 6 := by
  rcases eq_or_ne (0 : ℝ) x with rfl | hx
  · simp [expI]
  have hint : IntervalIntegrable (fun t : ℝ ↦ (x - t) ^ 2 / 2) volume 0 x :=
    (by fun_prop : Continuous fun t : ℝ ↦ (x - t) ^ 2 / 2).intervalIntegrable 0 x
  have hpoly : taylorWithinEval expI 2 (uIcc (0 : ℝ) x) 0 x =
      1 + I * (x : ℂ) - (x ^ 2 / 2 : ℂ) := by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, taylorWithinEval_succ, taylorWithinEval_succ,
      taylor_within_zero_eval, iteratedDerivWithin_expI hx left_mem_uIcc 1,
      iteratedDerivWithin_expI hx left_mem_uIcc 2]
    simp [expI, Complex.real_smul]
    ring
  have hrem : expI x - 1 - I * (x : ℂ) + (x ^ 2 / 2 : ℂ) =
      ∫ t in (0 : ℝ)..x, ((x - t) ^ 2 / 2 : ℝ) • (I ^ 3 * expI t) := by
    have h := taylor_integral_remainder (f := expI) (x := x) (x₀ := 0) (n := 2)
      (contDiff_expI.of_le le_top).contDiffOn
    rw [hpoly] at h
    rw [show expI x - 1 - I * (x : ℂ) + (x ^ 2 / 2 : ℂ) =
      expI x - (1 + I * (x : ℂ) - (x ^ 2 / 2 : ℂ)) by ring, h]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    simp only [iteratedDerivWithin_expI hx ht]
    norm_num
  have hnorm : (∫ t in (0 : ℝ)..x, ‖((x - t) ^ 2 / 2 : ℝ) • (I ^ 3 * expI t)‖) =
      ∫ t in (0 : ℝ)..x, (x - t) ^ 2 / 2 :=
    intervalIntegral.integral_congr fun t _ ↦ by
      rw [norm_smul, Real.norm_eq_abs, norm_mul, norm_pow, Complex.norm_I, norm_expI,
        abs_of_nonneg (by positivity)]
      simp
  have hprim (t : ℝ) : HasDerivAt (fun z : ℝ ↦ -(x - z) ^ 3 / 6) ((x - t) ^ 2 / 2) t := by
    convert! (((hasDerivAt_const t x).sub (hasDerivAt_id t)).pow 3).neg.div_const 6 using 1
    all_goals
      simp [Pi.sub_apply, id]
      ring
  rw [hrem]
  refine intervalIntegral.norm_integral_le_abs_integral_norm.trans ?_
  rw [hnorm, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hprim t) hint,
    show -(x - x) ^ 3 / 6 - -(x - 0) ^ 3 / 6 = x ^ 3 / 6 by ring, abs_div, abs_pow]
  norm_num

/-- Integrand of `G_ℓη`: the centred phase `e^{iaT} - 1 - iaT` against the density `μ_ℓ`. -/
def Gker (ℓ η T a : ℝ) : ℂ := (expI (a * T) - 1 - I * (a * T : ℂ)) * (μ_ℓ ℓ η a : ℂ)

/-- Report (45): the centred log-gamma phase `G_{ℓ,η}(T) = ∫₀^∞ (e^{iaT} - 1 - iaT) dμ_ℓ(a)`. -/
def G_ℓη (ℓ η T : ℝ) : ℂ := ∫ a : ℝ in Ioi 0, Gker ℓ η T a

end

noncomputable section

open Filter MeasureTheory Real Set intervalIntegral
open scoped Topology

/-- Quadratic Taylor remainder in `T` of the shifted cosine `cos(a(T + iu))`. -/
def cosRem (a u T : ℝ) : ℂ :=
  Complex.cos ((a : ℂ) * ((T : ℂ) + I * (u : ℂ))) - (cosh (u * a) : ℂ) +
    I * (a * T * sinh (u * a) : ℂ) + (a ^ 2 * T ^ 2 / 2 * cosh (u * a) : ℂ)

theorem cosRem_eq (a u T : ℝ) :
    cosRem a u T = (exp (-(u * a)) / 2 : ℂ) *
        (expI (a * T) - 1 - I * (a * T : ℂ) + ((a * T) ^ 2 / 2 : ℂ)) +
      (exp (u * a) / 2 : ℂ) * (expI (-(a * T)) - 1 - I * (-(a * T) : ℂ) +
        ((-(a * T)) ^ 2 / 2 : ℂ)) := by
  have h₁ : Complex.exp ((a : ℂ) * ((T : ℂ) + I * (u : ℂ)) * I) =
      (exp (-(u * a)) : ℂ) * expI (a * T) := by
    rw [Complex.ofReal_exp, expI, ← Complex.exp_add]
    congr 1
    push_cast
    linear_combination ((a : ℂ) * u) * Complex.I_sq
  have h₂ : Complex.exp (-((a : ℂ) * ((T : ℂ) + I * (u : ℂ))) * I) =
      (exp (u * a) : ℂ) * expI (-(a * T)) := by
    rw [Complex.ofReal_exp, expI, ← Complex.exp_add]
    congr 1
    push_cast
    linear_combination (-(a : ℂ) * u) * Complex.I_sq
  unfold cosRem Complex.cos
  rw [h₁, h₂, cosh_eq, sinh_eq]
  push_cast
  ring

theorem norm_cosRem_le (a u T : ℝ) : ‖cosRem a u T‖ ≤ cosh (u * a) * |a * T| ^ 3 / 6 := by
  have h₂ : ‖expI (-(a * T)) - 1 - I * (-(a * T) : ℂ) +
      ((-(a * T)) ^ 2 / 2 : ℂ)‖ ≤ |a * T| ^ 3 / 6 := by
    simpa [abs_neg] using norm_expI_sub_taylor_le (-(a * T))
  have hnorm (x : ℝ) : ‖(exp x / 2 : ℂ)‖ = exp x / 2 := by simp
  have h₁ := norm_expI_sub_taylor_le (a * T)
  push_cast at h₁
  rw [cosRem_eq, cosh_eq]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, hnorm, hnorm]
  linarith [mul_le_mul_of_nonneg_left h₁ (exp_pos (-(u * a))).le,
    mul_le_mul_of_nonneg_left h₂ (exp_pos (u * a)).le]

theorem norm_integral_cosRem_le (w : ℝ → ℝ) {b c : ℝ} (hbc : b ≤ c) (hb : 0 ≤ b)
    (hw : ContinuousOn w (Icc b c)) (hwnonneg : ∀ a ∈ Icc b c, 0 ≤ w a) (u T : ℝ) :
    ‖∫ a in b..c, (w a : ℂ) * cosRem a u T‖ ≤
      |T| ^ 3 / 6 * ∫ a in b..c, w a * a ^ 3 * cosh (u * a) := by
  have hg : IntervalIntegrable (fun a : ℝ ↦ |T| ^ 3 / 6 * (w a * a ^ 3 * cosh (u * a)))
      volume b c :=
    (continuousOn_const.mul ((hw.mul (continuous_id.pow 3).continuousOn).mul
      (by fun_prop))).intervalIntegrable_of_Icc hbc
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.norm_integral_le_of_norm_le hbc ?_ hg
  filter_upwards [] with a ha
  have hwa : 0 ≤ w a := hwnonneg a ⟨ha.1.le, ha.2⟩
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwa]
  calc w a * ‖cosRem a u T‖ ≤ w a * (cosh (u * a) * |a * T| ^ 3 / 6) :=
        mul_le_mul_of_nonneg_left (norm_cosRem_le a u T) hwa
    _ = |T| ^ 3 / 6 * (w a * a ^ 3 * cosh (u * a)) := by
        rw [abs_mul, abs_of_nonneg (hb.trans ha.1.le)]; ring

theorem norm_integral_w_B_cosRem_le {ε : ℝ} (hε : 0 < ε) (u T : ℝ) :
    ‖∫ a in Bε ε..Bε ε + 1, (w_B ε a : ℂ) * cosRem a u T‖ ≤
      |T| ^ 3 / 6 * upperPositiveShellThirdMoment ε (u - 1) := by
  have hB : (0 : ℝ) ≤ Bε ε := by unfold Bε; positivity
  refine (norm_integral_cosRem_le (w_B ε) (by linarith) hB
    (positiveShellDensity_continuous ε).continuousOn
    (fun a _ ↦ by unfold w_B; exact div_nonneg (shellWeight_pos ε).le (cosh_pos a).le) u T).trans_eq
    ?_
  unfold upperPositiveShellThirdMoment
  congr 1
  exact intervalIntegral.integral_congr fun a _ ↦ by ring_nf

theorem norm_integral_w_s_cosRem_le {ε : ℝ} (hε : 0 < ε) (horder : a₀ε ε ≤ Aε ε)
    (hmargin : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a) (u T : ℝ) :
    ‖∫ a in a₀ε ε..Aε ε, (w_s ε a : ℂ) * cosRem a u T‖ ≤
      |T| ^ 3 / 6 * upperShortShellThirdMoment ε (u - 1) := by
  have ha₀ : (0 : ℝ) < a₀ε ε := by unfold a₀ε; positivity
  have hnonneg (a : ℝ) (ha : a ∈ Icc (a₀ε ε) (Aε ε)) : 0 ≤ -w_s ε a := by
    have hapos : 0 < a := ha₀.trans_le ha.1
    unfold w_s
    have hd : 0 < 2 * a ^ 2 * cosh a := by positivity
    simpa using div_nonneg (mul_nonneg (hmargin a ha) (exp_pos _).le) hd.le
  have hbound := norm_integral_cosRem_le (fun a : ℝ ↦ -w_s ε a) horder ha₀.le
    (shortShellDensity_continuousOn_support hε).neg hnonneg u T
  have hneg : (∫ a in a₀ε ε..Aε ε, ((-w_s ε a : ℝ) : ℂ) * cosRem a u T) =
      -∫ a in a₀ε ε..Aε ε, (w_s ε a : ℂ) * cosRem a u T := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun a _ ↦ by push_cast; ring
  rw [hneg, norm_neg] at hbound
  refine hbound.trans_eq ?_
  unfold upperShortShellThirdMoment
  congr 1
  exact intervalIntegral.integral_congr fun a _ ↦ by ring_nf

theorem integral_cosRem_eq (w : ℝ → ℝ) {b c : ℝ} (hbc : b ≤ c) (hw : ContinuousOn w (Icc b c))
    (u T : ℝ) :
    (∫ a in b..c, (w a : ℂ) * cosRem a u T) =
      (∫ a in b..c, (w a : ℂ) * (Complex.cos ((a : ℂ) * ((T : ℂ) + I * (u : ℂ))) - 1)) -
        (∫ a in b..c, (w a : ℂ) * ((cosh (u * a) : ℂ) - 1)) +
        I * ((T * ∫ a in b..c, w a * a * sinh (u * a) : ℝ) : ℂ) +
        ((T ^ 2 / 2 * ∫ a in b..c, w a * a ^ 2 * cosh (u * a) : ℝ) : ℂ) := by
  have hwc : ContinuousOn (fun a : ℝ ↦ (w a : ℂ)) (Icc b c) :=
    Complex.ofRealCLM.continuous.comp_continuousOn hw
  have hF : IntervalIntegrable
      (fun a : ℝ ↦ (w a : ℂ) * (Complex.cos ((a : ℂ) * ((T : ℂ) + I * (u : ℂ))) - 1))
      volume b c :=
    (hwc.mul (by fun_prop : Continuous fun a : ℝ ↦
      Complex.cos ((a : ℂ) * ((T : ℂ) + I * (u : ℂ))) - 1).continuousOn).intervalIntegrable_of_Icc
      hbc
  have hH : IntervalIntegrable (fun a : ℝ ↦ ((w a * (cosh (u * a) - 1) : ℝ) : ℂ)) volume b c :=
    (Complex.ofRealCLM.continuous.comp_continuousOn
      (hw.mul (by fun_prop))).intervalIntegrable_of_Icc hbc
  have hL : IntervalIntegrable (fun a : ℝ ↦ ((w a * a * sinh (u * a) : ℝ) : ℂ)) volume b c :=
    (Complex.ofRealCLM.continuous.comp_continuousOn
      ((hw.mul continuous_id.continuousOn).mul (by fun_prop))).intervalIntegrable_of_Icc hbc
  have hV : IntervalIntegrable (fun a : ℝ ↦ ((w a * a ^ 2 * cosh (u * a) : ℝ) : ℂ)) volume b c :=
    (Complex.ofRealCLM.continuous.comp_continuousOn
      ((hw.mul (continuous_id.pow 2).continuousOn).mul (by fun_prop))).intervalIntegrable_of_Icc hbc
  have hstep : (∫ a in b..c, (w a : ℂ) * cosRem a u T) =
      ∫ a in b..c, ((w a : ℂ) * (Complex.cos ((a : ℂ) * ((T : ℂ) + I * (u : ℂ))) - 1) -
        ((w a * (cosh (u * a) - 1) : ℝ) : ℂ) + I * (T : ℂ) * ((w a * a * sinh (u * a) : ℝ) : ℂ) +
        (T ^ 2 / 2 : ℂ) * ((w a * a ^ 2 * cosh (u * a) : ℝ) : ℂ)) :=
    intervalIntegral.integral_congr fun a _ ↦ by unfold cosRem; push_cast; ring
  have hHc : (∫ a in b..c, ((w a * (cosh (u * a) - 1) : ℝ) : ℂ)) =
      ∫ a in b..c, (w a : ℂ) * ((cosh (u * a) : ℂ) - 1) :=
    intervalIntegral.integral_congr fun a _ ↦ by push_cast; ring
  rw [hstep, intervalIntegral.integral_add ((hF.sub hH).add (hL.const_mul _)) (hV.const_mul _),
    intervalIntegral.integral_add (hF.sub hH) (hL.const_mul _), intervalIntegral.integral_sub hF hH,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hHc,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
  push_cast
  ring

/-- The centred shell phase `ℓ (h_ε(T + iu) - h_ε(iu) + i T h_ε'(u))` of report (46). -/
def shellPhase (ε ℓ u T : ℝ) : ℂ :=
  (ℓ : ℂ) * (h_ε ε ((T : ℂ) + I * (u : ℂ)) - (h_εI ε u : ℂ) +
    I * (T * saddleSourceShellDerivative ε u : ℂ))

/-- The quadratic remainder of the shell phase, integrated over both shells. -/
def shellRem (ε u T : ℝ) : ℂ := (∫ a in a₀ε ε..Aε ε, (w_s ε a : ℂ) * cosRem a u T) +
  ∫ a in Bε ε..Bε ε + 1, (w_B ε a : ℂ) * cosRem a u T

theorem shellRem_eq {ε : ℝ} (hε : 0 < ε) (horder : a₀ε ε ≤ Aε ε) (u T : ℝ) :
    shellRem ε u T = h_ε ε ((T : ℂ) + I * (u : ℂ)) - (h_εI ε u : ℂ) +
      I * (T * saddleSourceShellDerivative ε u : ℂ) +
      (T ^ 2 / 2 * upperNetShellVariance ε (u - 1) : ℂ) := by
  have hVs : (∫ a in a₀ε ε..Aε ε, w_s ε a * a ^ 2 * cosh (u * a)) = -V_s ε (u - 1) := by
    unfold V_s
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun a _ ↦ by ring_nf
  have hVB : (∫ a in Bε ε..Bε ε + 1, w_B ε a * a ^ 2 * cosh (u * a)) = V_B ε (u - 1) := by
    unfold V_B
    exact intervalIntegral.integral_congr fun a _ ↦ by ring_nf
  have hI : (h_εI ε u : ℂ) =
      (∫ a in a₀ε ε..Aε ε, (w_s ε a : ℂ) * ((cosh (u * a) : ℂ) - 1)) +
        ∫ a in Bε ε..Bε ε + 1, (w_B ε a : ℂ) * ((cosh (u * a) : ℂ) - 1) := by
    have harg (a : ℝ) : Complex.cos ((a : ℂ) * (I * (u : ℂ))) = (cosh (u * a) : ℂ) := by
      rw [show (a : ℂ) * (I * (u : ℂ)) = ((u * a : ℝ) : ℂ) * I by push_cast; ring,
        Complex.cos_mul_I, ← Complex.ofReal_cosh]
    rw [← mellinShellPhase_imaginary]
    unfold h_ε
    congr 1 <;> exact intervalIntegral.integral_congr fun a _ ↦ by rw [harg]
  unfold shellRem
  rw [integral_cosRem_eq (w_s ε) horder (shortShellDensity_continuousOn_support hε) u T,
    integral_cosRem_eq (w_B ε) (by linarith : Bε ε ≤ Bε ε + 1)
      (positiveShellDensity_continuous ε).continuousOn u T, hVs, hVB, hI]
  unfold h_ε saddleSourceShellDerivative upperNetShellVariance
  push_cast
  ring

theorem norm_shellPhase_add_le {ε ℓ : ℝ} (hε : 0 < ε) (hℓ : 0 ≤ ℓ) (horder : a₀ε ε ≤ Aε ε)
    (hmargin : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a) (u T : ℝ) :
    ‖shellPhase ε ℓ u T + (ℓ * upperNetShellVariance ε (u - 1) / 2 * T ^ 2 : ℂ)‖ ≤
      ℓ * upperNetShellThirdMoment ε (u - 1) / 6 * |T| ^ 3 := by
  have heq : shellPhase ε ℓ u T + (ℓ * upperNetShellVariance ε (u - 1) / 2 * T ^ 2 : ℂ) =
      (ℓ : ℂ) * shellRem ε u T := by
    rw [shellRem_eq hε horder u T]
    unfold shellPhase
    ring
  have hsum : ‖shellRem ε u T‖ ≤ |T| ^ 3 / 6 * upperNetShellThirdMoment ε (u - 1) := by
    unfold shellRem upperNetShellThirdMoment
    refine (norm_add_le _ _).trans ?_
    linarith [norm_integral_w_s_cosRem_le hε horder hmargin u T,
      norm_integral_w_B_cosRem_le hε u T]
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hℓ]
  calc ℓ * ‖shellRem ε u T‖ ≤ ℓ * (|T| ^ 3 / 6 * upperNetShellThirdMoment ε (u - 1)) :=
        mul_le_mul_of_nonneg_left hsum hℓ
    _ = ℓ * upperNetShellThirdMoment ε (u - 1) / 6 * |T| ^ 3 := by ring

end

noncomputable section

open Filter MeasureTheory Real Set
open scoped Topology

theorem integrableOn_Gker {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) (T : ℝ) :
    IntegrableOn (Gker ℓ η T) (Ioi 0) := by
  have hlin (y : ℝ) : ‖expI y - 1 - I * (y : ℂ)‖ ≤ y ^ 2 / 2 + |y| ^ 3 / 6 := by
    have hq : ‖(y ^ 2 / 2 : ℂ)‖ = y ^ 2 / 2 := by simp [sq_abs]
    have h := norm_sub_le (expI y - 1 - I * (y : ℂ) + (y ^ 2 / 2 : ℂ))
      (y ^ 2 / 2 : ℂ)
    rw [add_sub_cancel_right, hq] at h
    linarith [norm_expI_sub_taylor_le y]
  have hmajor : IntegrableOn (fun a : ℝ ↦ T ^ 2 / 2 * (a ^ 2 * μ_ℓ ℓ η a) +
      |T| ^ 3 / 6 * (a ^ 3 * μ_ℓ ℓ η a)) (Ioi 0) :=
    ((upperGammaVarianceDensity_integrable hℓ hη).const_mul _).add
      ((upperGammaThirdMomentDensity_integrable hℓ hη).const_mul _)
  have hmeas : Measurable (Gker ℓ η T) := by unfold Gker expI μ_ℓ; fun_prop
  refine hmajor.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  have hd := upperGammaMeasureDensity_pos (η := η) hℓ ha
  unfold Gker
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  calc ‖expI (a * T) - 1 - I * (a * T : ℂ)‖ * μ_ℓ ℓ η a
      ≤ ((a * T) ^ 2 / 2 + |a * T| ^ 3 / 6) * μ_ℓ ℓ η a := by
        have h := hlin (a * T)
        push_cast at h
        exact mul_le_mul_of_nonneg_right h hd.le
    _ = T ^ 2 / 2 * (a ^ 2 * μ_ℓ ℓ η a) + |T| ^ 3 / 6 * (a ^ 3 * μ_ℓ ℓ η a) := by
        rw [abs_mul, abs_of_pos ha]; ring

/-- Cubic Taylor remainder of `Gker`. -/
def Gker₃ (ℓ η T a : ℝ) : ℂ :=
  (expI (a * T) - 1 - I * (a * T : ℂ) + ((a * T) ^ 2 / 2 : ℂ)) * (μ_ℓ ℓ η a : ℂ)

theorem norm_Gker₃_le {ℓ η a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) (T : ℝ) :
    ‖Gker₃ ℓ η T a‖ ≤ |T| ^ 3 / 6 * (a ^ 3 * μ_ℓ ℓ η a) := by
  have hd := upperGammaMeasureDensity_pos (η := η) hℓ ha
  unfold Gker₃
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  calc ‖expI (a * T) - 1 - I * (a * T : ℂ) + ((a * T) ^ 2 / 2 : ℂ)‖ * μ_ℓ ℓ η a
      ≤ |a * T| ^ 3 / 6 * μ_ℓ ℓ η a := by
        have h := norm_expI_sub_taylor_le (a * T)
        push_cast at h
        exact mul_le_mul_of_nonneg_right h hd.le
    _ = |T| ^ 3 / 6 * (a ^ 3 * μ_ℓ ℓ η a) := by rw [abs_mul, abs_of_pos ha]; ring

/-- Report (46): `G_{ℓ,η}(T) + ℓ V_γ T²/2` is the cubic remainder, of size `ℓ M₃_γ |T|³/6`. -/
theorem norm_G_ℓη_add_le {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) (T : ℝ) :
    ‖G_ℓη ℓ η T + (ℓ * V_γ ℓ η / 2 * T ^ 2 : ℂ)‖ ≤ ℓ * M₃_γ ℓ η / 6 * |T| ^ 3 := by
  have hquadInt : IntegrableOn
      (fun a : ℝ ↦ ((T ^ 2 / 2 * (a ^ 2 * μ_ℓ ℓ η a) : ℝ) : ℂ)) (Ioi 0) :=
    ((upperGammaVarianceDensity_integrable hℓ hη).const_mul (T ^ 2 / 2)).ofReal
  have hofReal : (∫ a : ℝ in Ioi 0, ((T ^ 2 / 2 * (a ^ 2 * μ_ℓ ℓ η a) : ℝ) : ℂ)) =
      ((∫ a : ℝ in Ioi 0, T ^ 2 / 2 * (a ^ 2 * μ_ℓ ℓ η a) : ℝ) : ℂ) := integral_ofReal (𝕜 := ℂ)
  have hquad : (∫ a : ℝ in Ioi 0, ((T ^ 2 / 2 * (a ^ 2 * μ_ℓ ℓ η a) : ℝ) : ℂ)) =
      (ℓ * V_γ ℓ η / 2 * T ^ 2 : ℂ) := by
    rw [hofReal, MeasureTheory.integral_const_mul,
      show T ^ 2 / 2 * ∫ a : ℝ in Ioi 0, a ^ 2 * μ_ℓ ℓ η a = ℓ * V_γ ℓ η / 2 * T ^ 2 by
        unfold V_γ; field_simp [hℓ.ne']]
    push_cast
    ring
  have hsplit : G_ℓη ℓ η T + (ℓ * V_γ ℓ η / 2 * T ^ 2 : ℂ) =
      ∫ a : ℝ in Ioi 0, Gker₃ ℓ η T a := by
    rw [← hquad]
    unfold G_ℓη
    rw [← MeasureTheory.integral_add (integrableOn_Gker hℓ hη T) hquadInt]
    refine setIntegral_congr_fun measurableSet_Ioi fun a _ ↦ ?_
    unfold Gker Gker₃
    push_cast
    ring
  have hmajor : IntegrableOn (fun a : ℝ ↦ |T| ^ 3 / 6 * (a ^ 3 * μ_ℓ ℓ η a)) (Ioi 0) :=
    (upperGammaThirdMomentDensity_integrable hℓ hη).const_mul _
  rw [hsplit]
  refine (MeasureTheory.norm_integral_le_of_norm_le hmajor ?_).trans_eq ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    exact norm_Gker₃_le hℓ ha T
  · rw [MeasureTheory.integral_const_mul]
    unfold M₃_γ
    field_simp [hℓ.ne']

end

noncomputable section

open Filter MeasureTheory Real Set
open scoped Topology BigOperators

/-- Centred Laplace kernel `(e^{iaT} - 1 - iaT) e^{-ca} / a`. -/
def Lker (c T a : ℝ) : ℂ :=
  (expI (a * T) - 1 - I * (a * T : ℂ)) * (exp (-c * a) / a : ℂ)

theorem Lker_eq (c T : ℝ) {a : ℝ} (ha : a ≠ 0) :
    Lker c T a = Frullani.cexpKernel ((c : ℂ) - I * (T : ℂ)) (c : ℂ) a -
      I * (T : ℂ) * Complex.exp (-(c : ℂ) * (a : ℂ)) := by
  have hbase : Complex.exp (-(c : ℂ) * (a : ℂ)) = (exp (-c * a) : ℂ) := by
    rw [Complex.ofReal_exp]; congr 1; push_cast; ring
  have hosc : Complex.exp (-((c : ℂ) - I * (T : ℂ)) * (a : ℂ)) =
      (exp (-c * a) : ℂ) * expI (a * T) := by
    rw [Complex.ofReal_exp, expI, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hac : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  unfold Lker Frullani.cexpKernel
  rw [hosc, hbase]
  push_cast
  field_simp [hac]

theorem integrableOn_Lker {c : ℝ} (hc : 0 < c) (T : ℝ) : IntegrableOn (Lker c T) (Ioi 0) := by
  have hz : 0 < ((c : ℂ) - I * (T : ℂ)).re := by simpa using hc
  have hw : 0 < (c : ℂ).re := by simpa using hc
  refine ((Frullani.integrableOn_cexpKernel hz hw).sub
    ((integrableOn_cexp_neg_mul_Ioi hw).const_mul (I * (T : ℂ)))).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  exact (Lker_eq c T ha.ne').symm

theorem integral_Lker {c : ℝ} (hc : 0 < c) (T : ℝ) :
    (∫ a : ℝ in Ioi 0, Lker c T a) =
      Complex.log (c : ℂ) - Complex.log ((c : ℂ) - I * (T : ℂ)) - I * (T : ℂ) * (c : ℂ)⁻¹ := by
  have hz : 0 < ((c : ℂ) - I * (T : ℂ)).re := by simpa using hc
  have hw : 0 < (c : ℂ).re := by simpa using hc
  have hcongr : (∫ a : ℝ in Ioi 0, Lker c T a) =
      ∫ a : ℝ in Ioi 0, (Frullani.cexpKernel ((c : ℂ) - I * (T : ℂ)) (c : ℂ) a -
        I * (T : ℂ) * Complex.exp (-(c : ℂ) * (a : ℂ))) :=
    setIntegral_congr_fun measurableSet_Ioi fun a ha ↦ Lker_eq c T ha.ne'
  rw [hcongr, integral_sub (Frullani.integrableOn_cexpKernel hz hw)
      ((integrableOn_cexp_neg_mul_Ioi hw).const_mul (I * (T : ℂ))), integral_const_mul,
    Frullani.integral_cexpKernel hz hw, integral_cexp_neg_mul_Ioi hw]

theorem exp_integral_Lker {c : ℝ} (hc : 0 < c) (T : ℝ) :
    Complex.exp (∫ a : ℝ in Ioi 0, Lker c T a) =
      (c : ℂ) / ((c : ℂ) - I * (T : ℂ)) * Complex.exp (-I * (T / c : ℂ)) := by
  have hcn : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hzn : (c : ℂ) - I * (T : ℂ) ≠ 0 := by
    apply ne_of_apply_ne Complex.re
    simpa using hc.ne'
  rw [integral_Lker hc T, show Complex.log (c : ℂ) - Complex.log ((c : ℂ) - I * (T : ℂ)) -
      I * (T : ℂ) * (c : ℂ)⁻¹ = Complex.log (c : ℂ) - Complex.log ((c : ℂ) - I * (T : ℂ)) +
        -I * (T / c : ℂ) by push_cast [div_eq_mul_inv]; ring,
    Complex.exp_add, Complex.exp_sub, Complex.exp_log hcn, Complex.exp_log hzn]

theorem exp_integral_Lker_shift {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) (T : ℝ) (k : ℕ) :
    Complex.exp (∫ a : ℝ in Ioi 0, Lker (η + 2 * (k : ℝ) / ℓ) T a) =
      (ℓ * η / 2 + (k : ℂ) : ℂ) /
          ((ℓ * η / 2 : ℂ) - I * (ℓ * T / 2 : ℂ) + (k : ℂ)) *
        Complex.exp (-I * (ℓ * T / 2 / (ℓ * η / 2 + (k : ℂ)) : ℂ)) := by
  have hc := upperGammaLaplaceRate_pos hℓ hη k
  have hln : (ℓ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hℓ.ne'
  have hsn : (ℓ / 2 : ℂ) ≠ 0 := div_ne_zero hln two_ne_zero
  have hnum : (ℓ * η / 2 + (k : ℂ) : ℂ) =
      (ℓ / 2 : ℂ) * (η + 2 * (k : ℂ) / ℓ : ℂ) := by
    field_simp [hln]
  have hden : (ℓ * η / 2 : ℂ) - I * (ℓ * T / 2 : ℂ) + (k : ℂ) =
      (ℓ / 2 : ℂ) * ((η + 2 * (k : ℂ) / ℓ : ℂ) - I * (T : ℂ)) := by
    field_simp [hln]
    ring
  have hphase : (ℓ * T / 2 : ℂ) / ((ℓ / 2 : ℂ) * (η + 2 * (k : ℂ) / ℓ : ℂ)) =
      (T : ℂ) / (η + 2 * (k : ℂ) / ℓ : ℂ) := by
    rw [show (ℓ * T / 2 : ℂ) = (ℓ / 2 : ℂ) * (T : ℂ) by ring, mul_div_mul_left _ _ hsn]
  have hL := exp_integral_Lker hc T
  push_cast at hL
  rw [hL, hnum, hden, hphase, mul_div_mul_left _ _ hsn]

/-- Truncation of `Gker` to the first `n + 1` terms of the geometric expansion of `μ_ℓ`. -/
def GkerN (ℓ η T : ℝ) (n : ℕ) (a : ℝ) : ℂ :=
  Lker η T a * ((∑ k ∈ Finset.range (n + 1), exp (-(2 * a / ℓ)) ^ k : ℝ) : ℂ)

theorem GkerN_eq_sum (ℓ η T : ℝ) (n : ℕ) (a : ℝ) :
    GkerN ℓ η T n a = ∑ k ∈ Finset.range (n + 1), Lker (η + 2 * (k : ℝ) / ℓ) T a := by
  unfold GkerN
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have he : Complex.exp (-(η : ℂ) * (a : ℂ)) * Complex.exp (-(2 * (a : ℂ) / (ℓ : ℂ))) ^ k =
      Complex.exp (-((η : ℂ) + 2 * (k : ℂ) / (ℓ : ℂ)) * (a : ℂ)) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    ring
  unfold Lker
  push_cast
  rw [← he]
  ring

theorem Lker_mul_geom_eq_Gker (ℓ η T a : ℝ) :
    Lker η T a * (((1 - exp (-(2 * a / ℓ)))⁻¹ : ℝ) : ℂ) = Gker ℓ η T a := by
  simp [Lker, Gker, μ_ℓ, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

theorem tendsto_integral_GkerN {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) (T : ℝ) :
    Tendsto (fun n : ℕ ↦ ∫ a : ℝ in Ioi 0, GkerN ℓ η T n a) atTop (𝓝 (G_ℓη ℓ η T)) := by
  have hq0 (a : ℝ) : (0 : ℝ) ≤ exp (-(2 * a / ℓ)) := (exp_pos _).le
  have hq1 {a : ℝ} (ha : 0 < a) : exp (-(2 * a / ℓ)) < 1 :=
    exp_lt_one_iff.mpr (neg_lt_zero.mpr (by positivity))
  unfold G_ℓη
  refine tendsto_integral_of_dominated_convergence (fun a ↦ ‖Gker ℓ η T a‖) ?_
    (integrableOn_Gker hℓ hη T).norm ?_ ?_
  · intro n
    refine Measurable.aestronglyMeasurable ?_
    unfold GkerN Lker expI
    fun_prop
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    have hsum : (∑ k ∈ Finset.range (n + 1), exp (-(2 * a / ℓ)) ^ k) ≤
        (1 - exp (-(2 * a / ℓ)))⁻¹ :=
      sum_le_hasSum _ (fun k _ ↦ pow_nonneg (hq0 a) k)
        (hasSum_geometric_of_lt_one (hq0 a) (hq1 ha))
    rw [← Lker_mul_geom_eq_Gker, GkerN, norm_mul, norm_mul,
      Complex.norm_of_nonneg (Finset.sum_nonneg fun k _ ↦ pow_nonneg (hq0 a) k),
      Complex.norm_of_nonneg (inv_nonneg.mpr (sub_nonneg.mpr (hq1 ha).le))]
    exact mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    have hgeo := ((hasSum_geometric_of_lt_one (hq0 a) (hq1 ha)).tendsto_sum_nat).comp
      (tendsto_add_atTop_nat 1)
    simpa only [GkerN, Lker_mul_geom_eq_Gker, Function.comp_apply] using
      (tendsto_const_nhds (x := Lker η T a)).mul hgeo.ofReal

theorem integral_GkerN_eq_sum {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) (T : ℝ) (n : ℕ) :
    (∫ a : ℝ in Ioi 0, GkerN ℓ η T n a) =
      ∑ k ∈ Finset.range (n + 1), ∫ a : ℝ in Ioi 0, Lker (η + 2 * (k : ℝ) / ℓ) T a := by
  rw [setIntegral_congr_fun measurableSet_Ioi fun a _ ↦ GkerN_eq_sum ℓ η T n a]
  exact integral_finsetSum _ fun k _ ↦ integrableOn_Lker (upperGammaLaplaceRate_pos hℓ hη k) T

/-- Euler's product for the ratio `Γ_n(m - ib) / Γ_n(m)` of Gamma partial products. -/
theorem GammaSeq_div {m : ℝ} (hm : 0 < m) (b : ℝ) {n : ℕ} (hn : 0 < n) :
    Complex.GammaSeq ((m : ℂ) - I * (b : ℂ)) n / Complex.GammaSeq (m : ℂ) n =
      Complex.exp (-I * (b * log (n : ℝ) : ℂ)) *
        ∏ k ∈ Finset.range (n + 1), ((m : ℂ) + (k : ℂ)) / ((m : ℂ) - I * (b : ℂ) + (k : ℂ)) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hcpow : (n : ℂ) ^ ((m : ℂ) - I * (b : ℂ)) / (n : ℂ) ^ (m : ℂ) =
      Complex.exp (-I * (b * log (n : ℝ) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hn0, Complex.cpow_def_of_ne_zero hn0, ← Complex.exp_sub,
      ← Complex.natCast_log]
    congr 1
    push_cast
    ring
  have hpow : (n : ℂ) ^ (m : ℂ) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hn0]; exact Complex.exp_ne_zero _
  have hfac : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hre (k : ℕ) : (m : ℂ) + (k : ℂ) ≠ 0 := by
    refine ne_of_apply_ne Complex.re ?_
    simpa using (add_pos_of_pos_of_nonneg hm (Nat.cast_nonneg k)).ne'
  have him (k : ℕ) : (m : ℂ) - I * (b : ℂ) + (k : ℂ) ≠ 0 := by
    refine ne_of_apply_ne Complex.re ?_
    simpa using (add_pos_of_pos_of_nonneg hm (Nat.cast_nonneg k)).ne'
  rw [← hcpow, Finset.prod_div_distrib, Complex.GammaSeq, Complex.GammaSeq]
  field_simp [hpow, hfac, Finset.prod_ne_zero_iff.mpr fun k _ ↦ hre k,
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ him k]

theorem exp_integral_GkerN {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) (T : ℝ) {n : ℕ} (hn : 0 < n) :
    Complex.exp (∫ a : ℝ in Ioi 0, GkerN ℓ η T n a) =
      Complex.GammaSeq ((ℓ * η / 2 : ℂ) - I * (ℓ * T / 2 : ℂ)) n /
          Complex.GammaSeq (ℓ * η / 2 : ℂ) n *
        Complex.exp (I * ((ℓ * T / 2 * (log (n : ℝ) -
          ∑ k ∈ Finset.range (n + 1), (ℓ * η / 2 + (k : ℝ))⁻¹) : ℝ) : ℂ)) := by
  have hm : (0 : ℝ) < ℓ * η / 2 := by positivity
  have hcast : ((ℓ * T / 2 * ∑ k ∈ Finset.range (n + 1), (ℓ * η / 2 + (k : ℝ))⁻¹ : ℝ) : ℂ) =
      ∑ k ∈ Finset.range (n + 1), (ℓ * T / 2 / (ℓ * η / 2 + (k : ℂ)) : ℂ) := by
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  have hexp : (∑ k ∈ Finset.range (n + 1), -I * (ℓ * T / 2 / (ℓ * η / 2 + (k : ℂ)) : ℂ)) =
      -I * (ℓ * T / 2 * log (n : ℝ) : ℂ) + I * ((ℓ * T / 2 * (log (n : ℝ) -
        ∑ k ∈ Finset.range (n + 1), (ℓ * η / 2 + (k : ℝ))⁻¹) : ℝ) : ℂ) := by
    rw [← Finset.mul_sum, ← hcast]
    push_cast
    ring
  rw [integral_GkerN_eq_sum hℓ hη T n, Complex.exp_sum]
  simp_rw [exp_integral_Lker_shift hℓ hη T]
  have hgs := GammaSeq_div hm (ℓ * T / 2) hn
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat] at hgs
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, hexp, Complex.exp_add, hgs]
  ring

/-- Report (45): `exp G_{ℓ,η}(T) = Γ(m - i b)/Γ(m) · e^{i b ψ(m)}` with `m = ℓη/2`, `b = ℓT/2`. -/
theorem exp_G_ℓη {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) (T : ℝ) :
    Complex.exp (G_ℓη ℓ η T) =
      Complex.Gamma ((ℓ * η / 2 : ℂ) - I * (ℓ * T / 2 : ℂ)) /
          (Gamma (ℓ * η / 2) : ℂ) *
        Complex.exp (I * (ℓ * T / 2 * Real.digamma (ℓ * η / 2) : ℂ)) := by
  have hm : (0 : ℝ) < ℓ * η / 2 := by positivity
  have hden : Complex.Gamma (ℓ * η / 2 : ℂ) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simpa using hm)
  have hcorrection : Tendsto (fun n : ℕ ↦ Complex.exp (I * ((ℓ * T / 2 * (log (n : ℝ) -
        ∑ k ∈ Finset.range (n + 1), (ℓ * η / 2 + (k : ℝ))⁻¹) : ℝ) : ℂ))) atTop
      (𝓝 (Complex.exp (I * ((ℓ * T / 2 * Real.digamma (ℓ * η / 2) : ℝ) : ℂ)))) :=
    ((((Real.tendsto_digamma_harmonic hm).const_mul (ℓ * T / 2)).ofReal).const_mul I).cexp
  rw [← Complex.Gamma_ofReal, show ((ℓ * η / 2 : ℝ) : ℂ) = (ℓ * η / 2 : ℂ) by push_cast; ring,
    show (ℓ * T / 2 * Real.digamma (ℓ * η / 2) : ℂ) =
      ((ℓ * T / 2 * Real.digamma (ℓ * η / 2) : ℝ) : ℂ) by push_cast; ring]
  refine tendsto_nhds_unique_of_eventuallyEq (tendsto_integral_GkerN hℓ hη T).cexp
    (((Complex.GammaSeq_tendsto_Gamma ((ℓ * η / 2 : ℂ) - I * (ℓ * T / 2 : ℂ))).div
      (Complex.GammaSeq_tendsto_Gamma (ℓ * η / 2 : ℂ)) hden).mul hcorrection) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact exp_integral_GkerN hℓ hη T hn

end

noncomputable section

open Filter MeasureTheory Real Set intervalIntegral
open scoped Topology

/-- Report (44): the stationary log radius `v_ℓ(u)`. -/
def vℓ (ε ℓ u : ℝ) : ℝ :=
  -(Real.log π) / 2 + Real.digamma (ℓ * (1 + u) / 2) / 2 + saddleSourceShellDerivative ε u

theorem saddleSourceStationaryLogRadius_eq_saddleLogRadius (ε : ℝ) (d : ℕ) (u : ℝ) :
    vℓ ε ((d : ℝ) / 2) u = logRadius ε d u := by
  rw [saddleLogRadius_eq_digamma_add_shellDerivative]; rfl

/-- The centred saddle phase `L_u(T)` of report (46): gamma part plus shell part. -/
def L_u (ε ℓ u T : ℝ) : ℂ := G_ℓη ℓ (1 + u) T + shellPhase ε ℓ u T

theorem norm_L_u_add_le {ε ℓ u : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : a₀ε ε ≤ Aε ε) (hmargin : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a) (T : ℝ) :
    ‖L_u ε ℓ u T + (ℓ * V_u ε ℓ u / 2 * T ^ 2 : ℂ)‖ ≤
      ℓ * M₃ ε ℓ (u - 1) / 6 * |T| ^ 3 := by
  have hη : 0 < 1 + u := by linarith
  have heq : L_u ε ℓ u T + (ℓ * V_u ε ℓ u / 2 * T ^ 2 : ℂ) =
      (G_ℓη ℓ (1 + u) T + (ℓ * V_γ ℓ (1 + u) / 2 * T ^ 2 : ℂ)) +
        (shellPhase ε ℓ u T + (ℓ * upperNetShellVariance ε (u - 1) / 2 * T ^ 2 : ℂ)) := by
    unfold L_u V_u upperSaddleVariance
    rw [show (2 : ℝ) + (u - 1) = 1 + u by ring]
    push_cast
    ring
  rw [heq]
  refine (norm_add_le _ _).trans ?_
  unfold M₃
  rw [show (2 : ℝ) + (u - 1) = 1 + u by ring]
  linarith [norm_G_ℓη_add_le hℓ hη T, norm_shellPhase_add_le hε hℓ.le horder hmargin u T]

theorem expL_eq {ε ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : -1 < u) (v T : ℝ) :
    expL ε ℓ u v T =
      Complex.Gamma ((ℓ * (1 + u) / 2 : ℂ) - I * (ℓ * T / 2 : ℂ)) /
          (Gamma (ℓ * (1 + u) / 2) : ℂ) *
        Complex.exp ((ℓ : ℂ) * (h_ε ε ((T : ℂ) + I * (u : ℂ)) - (h_εI ε u : ℂ))) *
        (Complex.exp (I * (ℓ * T * Real.log π / 2 : ℂ)) *
          Complex.exp (I * (ℓ * T * v : ℂ))) := by
  have hη : 0 < 1 + u := by linarith
  have hm : (0 : ℝ) < ℓ * (1 + u) / 2 := by positivity
  have hG : (Gamma (ℓ * (1 + u) / 2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Gamma_pos_of_pos hm).ne'
  have hπ : (exp (-(ℓ * u) * Real.log π / 2) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (exp_pos _).ne'
  have hs : (exp (ℓ * h_εI ε u) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (exp_pos _).ne'
  have hpi : Complex.exp (((ℓ : ℂ) - z_contour ℓ u T) * (Real.log π : ℂ) / 2) =
      (exp (-(ℓ * u) * Real.log π / 2) : ℂ) *
        Complex.exp (I * (ℓ * T * Real.log π / 2 : ℂ)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    unfold z_contour
    push_cast
    ring
  have hshell : Complex.exp ((ℓ : ℂ) * h_ε ε ((T : ℂ) + I * (u : ℂ))) =
      (exp (ℓ * h_εI ε u) : ℂ) *
        Complex.exp ((ℓ : ℂ) * (h_ε ε ((T : ℂ) + I * (u : ℂ)) - (h_εI ε u : ℂ))) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold expL saddleSourceNormalizedEnvelope mellinEnvelope saddleSourceContourEnvelopeScale
  rw [saddleSourceMellinContour_shellArgument hℓ, saddleSourceMellinContour_gammaArgument, hpi,
    hshell]
  push_cast
  field_simp [hπ, hG, hs]

theorem expL_stationary_eq {ε ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : -1 < u) (T : ℝ) :
    expL ε ℓ u (vℓ ε ℓ u) T = Complex.exp (L_u ε ℓ u T) := by
  have hη : 0 < 1 + u := by linarith
  have hphase : Complex.exp (I * (ℓ * T * Real.log π / 2 : ℂ)) *
      Complex.exp (I * (ℓ * T * vℓ ε ℓ u : ℂ)) =
      Complex.exp (I * (ℓ * T / 2 * Real.digamma (ℓ * (1 + u) / 2) : ℂ)) *
        Complex.exp (I * (ℓ * T * saddleSourceShellDerivative ε u : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    unfold vℓ
    push_cast
    ring
  have hshell : Complex.exp (shellPhase ε ℓ u T) =
      Complex.exp ((ℓ : ℂ) * (h_ε ε ((T : ℂ) + I * (u : ℂ)) - (h_εI ε u : ℂ))) *
        Complex.exp (I * (ℓ * T * saddleSourceShellDerivative ε u : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    unfold shellPhase
    ring
  have hgamma := exp_G_ℓη hℓ hη T
  push_cast at hgamma
  rw [expL_eq hℓ hu, hphase]
  unfold L_u
  rw [Complex.exp_add, hgamma, hshell]
  ring

/-- Report (71): on the stationary contour the envelope is the Gaussian up to `O(M₃ |T|³)`. -/
theorem norm_expL_sub_gaussian_le {ε ℓ u : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : a₀ε ε ≤ Aε ε) (hmargin : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a) (T : ℝ)
    (hsmall : ℓ * M₃ ε ℓ (u - 1) / 6 * |T| ^ 3 ≤ 1) :
    ‖expL ε ℓ u (vℓ ε ℓ u) T - (saddleSourceGaussianKernel ε ℓ u T : ℂ)‖ ≤
      2 * saddleSourceGaussianKernel ε ℓ u T * (ℓ * M₃ ε ℓ (u - 1) / 6 * |T| ^ 3) := by
  have hR := norm_L_u_add_le hε hℓ hu horder hmargin T
  have hg : 0 < saddleSourceGaussianKernel ε ℓ u T := by
    unfold saddleSourceGaussianKernel; positivity
  have hgauss : Complex.exp (L_u ε ℓ u T) = (saddleSourceGaussianKernel ε ℓ u T : ℂ) *
      Complex.exp (L_u ε ℓ u T + (ℓ * V_u ε ℓ u / 2 * T ^ 2 : ℂ)) := by
    unfold saddleSourceGaussianKernel
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [expL_stationary_eq hℓ hu T, hgauss, ← mul_sub_one, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hg]
  refine (mul_le_mul_of_nonneg_left (Complex.norm_exp_sub_one_le (hR.trans hsmall)) hg.le).trans ?_
  linarith [mul_le_mul_of_nonneg_left hR hg.le]

end

noncomputable section

open Filter MeasureTheory Real Set
open scoped Topology

/-- Report (71): the central Gaussian error for the centred integrand `e^{L_u(T)} P(T + iu)`,
for an arbitrary polynomial factor `P`. -/
theorem norm_integral_sub_gaussian_le {ε ℓ u R q p : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : a₀ε ε ≤ Aε ε) (hmargin : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a)
    (hV : 0 < V_u ε ℓ u) (hq : 0 ≤ q) (hqone : q ≤ 1) (hp : 0 ≤ p) (P : ℂ → ℂ)
    (hsource : Integrable fun T : ℝ ↦ expL ε ℓ u (vℓ ε ℓ u) T * P ((T : ℂ) + I * (u : ℂ)))
    (hcubic : ∀ T : ℝ, |T| ≤ R → ℓ * M₃ ε ℓ (u - 1) / 6 * |T| ^ 3 ≤ q)
    (hpoly : ∀ T : ℝ, |T| ≤ R →
      ‖P ((T : ℂ) + I * (u : ℂ)) - P (I * (u : ℂ))‖ ≤ p * ‖P (I * (u : ℂ))‖) :
    ‖∫ T : ℝ in Icc (-R) R, (expL ε ℓ u (vℓ ε ℓ u) T * P ((T : ℂ) + I * (u : ℂ)) -
        (saddleSourceGaussianKernel ε ℓ u T : ℂ) * P (I * (u : ℂ)))‖ ≤
      (2 * q + (1 + 2 * q) * p) * ‖P (I * (u : ℂ))‖ *
        ∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T := by
  have hgpos (T : ℝ) : 0 < saddleSourceGaussianKernel ε ℓ u T := by
    unfold saddleSourceGaussianKernel; positivity
  have hc : 0 ≤ (2 * q + (1 + 2 * q) * p) * ‖P (I * (u : ℂ))‖ :=
    mul_nonneg (by nlinarith) (norm_nonneg _)
  have hgaussian := saddleSourceGaussianKernel_integrable hℓ hV
  have hmajor : Integrable fun T : ℝ ↦
      (2 * q + (1 + 2 * q) * p) * ‖P (I * (u : ℂ))‖ * saddleSourceGaussianKernel ε ℓ u T :=
    hgaussian.const_mul _
  have hintegrable : Integrable fun T : ℝ ↦ expL ε ℓ u (vℓ ε ℓ u) T * P ((T : ℂ) + I * (u : ℂ)) -
      (saddleSourceGaussianKernel ε ℓ u T : ℂ) * P (I * (u : ℂ)) :=
    hsource.sub (hgaussian.ofReal.mul_const _)
  have hpoint : ∀ T ∈ Icc (-R) R,
      ‖expL ε ℓ u (vℓ ε ℓ u) T * P ((T : ℂ) + I * (u : ℂ)) -
          (saddleSourceGaussianKernel ε ℓ u T : ℂ) * P (I * (u : ℂ))‖ ≤
        (2 * q + (1 + 2 * q) * p) * ‖P (I * (u : ℂ))‖ * saddleSourceGaussianKernel ε ℓ u T := by
    intro T hT
    have hg2 : (0 : ℝ) ≤ 2 * saddleSourceGaussianKernel ε ℓ u T := by linarith [hgpos T]
    have hthird := hcubic T (abs_le.mpr ⟨hT.1, hT.2⟩)
    have henv := (norm_expL_sub_gaussian_le hε hℓ hu horder hmargin T (hthird.trans hqone)).trans
      (mul_le_mul_of_nonneg_left hthird hg2)
    have hpolynorm : ‖P ((T : ℂ) + I * (u : ℂ))‖ ≤ (1 + p) * ‖P (I * (u : ℂ))‖ := by
      have h := norm_add_le (P ((T : ℂ) + I * (u : ℂ)) - P (I * (u : ℂ))) (P (I * (u : ℂ)))
      rw [sub_add_cancel] at h
      linarith [hpoly T (abs_le.mpr ⟨hT.1, hT.2⟩)]
    rw [show expL ε ℓ u (vℓ ε ℓ u) T * P ((T : ℂ) + I * (u : ℂ)) -
        (saddleSourceGaussianKernel ε ℓ u T : ℂ) * P (I * (u : ℂ)) =
        (expL ε ℓ u (vℓ ε ℓ u) T - (saddleSourceGaussianKernel ε ℓ u T : ℂ)) *
            P ((T : ℂ) + I * (u : ℂ)) +
          (saddleSourceGaussianKernel ε ℓ u T : ℂ) *
            (P ((T : ℂ) + I * (u : ℂ)) - P (I * (u : ℂ))) by ring]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hgpos T)]
    refine (add_le_add (mul_le_mul henv hpolynorm (norm_nonneg _)
      (by nlinarith [hgpos T]))
      (mul_le_mul_of_nonneg_left (hpoly T (abs_le.mpr ⟨hT.1, hT.2⟩)) (hgpos T).le)).trans_eq ?_
    ring
  refine ((norm_integral_le_integral_norm _).trans (setIntegral_mono_on
    hintegrable.norm.integrableOn hmajor.integrableOn measurableSet_Icc hpoint)).trans ?_
  refine (setIntegral_le_integral hmajor
    (Eventually.of_forall fun T ↦ mul_nonneg hc (hgpos T).le)).trans_eq ?_
  exact integral_const_mul _ _

/-- Report (71) for the centered integrand of a saddle polynomial `P` at the stationary point
`v = v_λ(u)`: the central Gaussian error in terms of `‖P(iu)‖`. -/
theorem centeredIntegrand_centralGaussianError_le {ε ℓ u R q p : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (hu : -1 < u) (horder : a₀ε ε ≤ Aε ε) (hmargin : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a)
    (hV : 0 < V_u ε ℓ u) (hq : 0 ≤ q) (hqone : q ≤ 1) (hp : 0 ≤ p) {P : ℂ → ℂ}
    (hP : IsSaddlePolynomial ε P)
    (hcubic : ∀ T : ℝ, |T| ≤ R → ℓ * M₃ ε ℓ (u - 1) / 6 * |T| ^ 3 ≤ q)
    (hpoly : ∀ T : ℝ, |T| ≤ R →
      ‖P ((T : ℂ) + I * (u : ℂ)) - P (I * (u : ℂ))‖ ≤ p * ‖P (I * (u : ℂ))‖) :
    ‖∫ T : ℝ in Icc (-R) R, (centeredIntegrand ε ℓ P u (vℓ ε ℓ u) T -
        gaussianIntegrand ε ℓ P u T)‖ ≤
      (2 * q + (1 + 2 * q) * p) * ‖P (I * (u : ℂ))‖ *
        ∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T :=
  norm_integral_sub_gaussian_le hε hℓ hu horder hmargin hV hq hqone hp P
    (centeredIntegrand_integrable hε hℓ hu horder hP (vℓ ε ℓ u)) hcubic hpoly

end

end CohnElkies
