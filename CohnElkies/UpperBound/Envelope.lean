import CohnElkies.Parameters
import CohnElkiesForMathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The Gamma envelope `E_λ` and the Mellin data of the saddle-point pair (report §4.1)

The shell densities `w_B`, `w_s` and dampings `D_B`, the shell phase `h_ε(z)` (a Laplace transform
of the shell weights) with its symmetries and analyticity, the perturbed Gamma envelope
`E_λ(t) = π^{it/2} Γ((λ - it)/2) e^{λ h_ε(it)}`, the spectrum `X_P(t) = E_λ(t) P(t/λ)` and the
Mellin data `M_P(z) = E_λ(i(z - λ)) P(i(z - λ)/λ)` of a saddle polynomial `P`
(`IsSaddlePolynomial`, satisfied by `P₊`, `P₋`, `P₀`), the poles `z = -2n` of `M_P` with their
residues `poleResidue`, and the decomposition of `M_P` near a pole.
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter Set MeasureTheory Real intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace Topology

/-- `∫_B^{B+1} (1 - cos(aT)) da`: the frequency-`T` oscillation of the positive shell. -/
def shellOscillation (B T : ℝ) : ℝ := ∫ a in B..B + 1, (1 - cos (a * T))

/-- Report (58): `∫_B^{B+1}(1 - cos(aT)) da = 1 - sinc(T/2) cos((B + 1/2)T)`. -/
theorem shellOscillation_eq_sinc (B T : ℝ) :
    shellOscillation B T = 1 - sinc (T / 2) * cos ((B + 1 / 2) * T) := by
  rcases eq_or_ne T 0 with rfl | hT
  · simp [shellOscillation, Real.sinc_zero]
  have hderiv (a : ℝ) : HasDerivAt (fun y : ℝ ↦ y - sin (y * T) / T) (1 - cos (a * T)) a := by
    convert! (hasDerivAt_id a).sub (((Real.hasDerivAt_sin (a * T)).comp a
      ((hasDerivAt_id a).mul_const T)).div_const T) using 1
    field_simp
  have hint : IntervalIntegrable (fun a : ℝ ↦ 1 - cos (a * T)) volume B (B + 1) :=
    (by fun_prop : Continuous fun a : ℝ ↦ 1 - cos (a * T)).intervalIntegrable _ _
  have hsin : sin ((B + 1) * T) - sin (B * T) = 2 * sin (T / 2) * cos ((B + 1 / 2) * T) := by
    rw [Real.sin_sub_sin]; congr 2 <;> congr 1 <;> ring
  rw [shellOscillation, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun a _ ↦ hderiv a) hint,
    Real.sinc_of_ne_zero (div_ne_zero hT two_ne_zero)]
  field_simp
  ring_nf at hsin ⊢
  linarith

/-- Fourth-order Taylor bound `cos x ≤ 1 - x²/2 + 5x⁴/96` on `[0, 1]`. -/
theorem cos_le_quartic {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 * (5 / 96) := by
  have hbound := Real.cos_bound (x := x) (by rwa [abs_of_nonneg hx0])
  rw [abs_of_nonneg hx0] at hbound
  linarith [le_abs_self (cos x - (1 - x ^ 2 / 2))]

/-- Fifth-order Taylor bound `sin x ≤ x - x³/6 + x⁵/96` on `[0, 1]`. -/
theorem sin_le_quintic {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 96 := by
  have hpoly : Continuous fun t : ℝ ↦ 1 - t ^ 2 / 2 + t ^ 4 * (5 / 96) := by fun_prop
  have hderiv (t : ℝ) : HasDerivAt (fun y : ℝ ↦ y - y ^ 3 / 6 + y ^ 5 / 96)
      (1 - t ^ 2 / 2 + t ^ 4 * (5 / 96)) t := by
    convert! ((hasDerivAt_id t).sub (((hasDerivAt_id t).pow 3).div_const 6)).add
      (((hasDerivAt_id t).pow 5).div_const 96) using 1
    simp [id]; ring
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hx0
    (Real.continuous_cos.intervalIntegrable 0 x) (hpoly.intervalIntegrable 0 x)
    fun t ht ↦ cos_le_quartic ht.1 (ht.2.trans hx1)
  simp only [integral_cos, Real.sin_zero, sub_zero] at hmono
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hderiv t)
    (hpoly.intervalIntegrable 0 x)] at hmono
  norm_num at hmono
  exact hmono

/-- `sin x ≤ x - (4/25) x³` on `[0, 1/2]`. -/
theorem sin_le_linear_sub_cubic {x : ℝ} (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    sin x ≤ x - 4 / 25 * x ^ 3 := by
  have hsq : x ^ 2 ≤ 1 / 4 := by nlinarith [mul_nonneg hx0 (sub_nonneg.2 hxhalf)]
  have hfifth : x ^ 5 ≤ x ^ 3 / 4 := by
    nlinarith [mul_nonneg (pow_nonneg hx0 3) (sub_nonneg.2 hsq), show x ^ 5 = x ^ 3 * x ^ 2 by ring]
  nlinarith [sin_le_quintic hx0 (by linarith : x ≤ 1), pow_nonneg hx0 3]

theorem sinc_abs (x : ℝ) : sinc |x| = sinc x := by
  rcases abs_choice x with h | h <;> simp [h, Real.sinc_neg]

/-- Quadratic gap `(4/25) x² ≤ 1 - |sinc x|` for `0 ≤ x ≤ 1/2`. -/
theorem sinc_quadratic_gap_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    4 / 25 * x ^ 2 ≤ 1 - |sinc x| := by
  rcases hx0.eq_or_lt with rfl | hxpos
  · norm_num [Real.sinc_zero]
  have hsin0 : 0 ≤ sin x :=
    sin_nonneg_of_nonneg_of_le_pi hxpos.le (by linarith [Real.pi_gt_three])
  rw [Real.sinc_of_ne_zero hxpos.ne', abs_of_nonneg (div_nonneg hsin0 hxpos.le)]
  have hfrac : sin x / x ≤ 1 - 4 / 25 * x ^ 2 := by
    rw [div_le_iff₀ hxpos]
    nlinarith [sin_le_linear_sub_cubic hxpos.le hxhalf]
  linarith

/-- Uniform gap `|sinc x| ≤ 24/25` away from the origin. -/
theorem abs_sinc_le_twentyfour_twentyfive {x : ℝ} (hx : 1 / 2 ≤ x) : |sinc x| ≤ 24 / 25 := by
  have hxpos : 0 < x := by linarith
  have hhalf : sin (1 / 2 : ℝ) ≤ 12 / 25 := by
    have h := sin_le_quintic (x := 1 / 2) (by norm_num) (by norm_num)
    norm_num at h ⊢
    linarith
  rw [Real.sinc_of_ne_zero hxpos.ne']
  rcases le_or_gt x π with hxpi | hxpi
  · rw [abs_of_nonneg (div_nonneg (sin_nonneg_of_nonneg_of_le_pi hxpos.le hxpi) hxpos.le)]
    have hend : sin (1 / 2) / (1 / 2) ≤ 24 / 25 := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 1 / 2)]; linarith
    rcases hx.eq_or_lt with rfl | hlt
    · exact hend
    · have hslope := strictConcaveOn_sin_Icc.secant_strict_mono (a := (0 : ℝ)) (x := (1 / 2 : ℝ))
        (y := x) ⟨le_rfl, Real.pi_pos.le⟩ ⟨by norm_num, by linarith [Real.pi_gt_three]⟩
        ⟨hxpos.le, hxpi⟩ (by norm_num) hxpos.ne' hlt
      simp only [Real.sin_zero, sub_zero] at hslope
      exact hslope.le.trans hend
  · rw [abs_div, abs_of_nonneg hxpos.le, div_le_iff₀ hxpos]
    nlinarith [Real.abs_sin_le_one x, Real.pi_gt_three]

/-- The explicit gap `min(T², 1)/25 ≤ 1 - |sinc(T/2)|` behind the positivity of report (58). -/
theorem sinc_explicit (T : ℝ) : 1 / 25 * min (T ^ 2) 1 ≤ 1 - |sinc (T / 2)| := by
  rw [show sinc (T / 2) = sinc (|T| / 2) by rw [← sinc_abs (T / 2), abs_div]; norm_num]
  rcases le_or_gt |T| 1 with hsmall | hlarge
  · have hsq : T ^ 2 ≤ 1 := by
      nlinarith [sq_abs T, mul_nonneg (abs_nonneg T) (sub_nonneg.2 hsmall)]
    have hscale : (|T| / 2) ^ 2 = T ^ 2 / 4 := by rw [div_pow, sq_abs]; norm_num
    rw [min_eq_left hsq]
    linarith [sinc_quadratic_gap_nonneg (x := |T| / 2) (by positivity) (by linarith)]
  · have hsq : (1 : ℝ) ≤ T ^ 2 := by nlinarith [sq_abs T, sq_nonneg (|T| - 1)]
    rw [min_eq_right hsq]
    linarith [abs_sinc_le_twentyfour_twentyfive (x := |T| / 2) (by linarith)]

/-- Positivity of report (58), quantitatively: the shell oscillation is `≥ min(T², 1)/25`. -/
theorem shellOscillation_lower_bound (B T : ℝ) :
    1 / 25 * min (T ^ 2) 1 ≤ shellOscillation B T := by
  have h : sinc (T / 2) * cos ((B + 1 / 2) * T) ≤ |sinc (T / 2)| :=
    (le_abs_self _).trans <| by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  rw [shellOscillation_eq_sinc]
  linarith [sinc_explicit T]

/-- `e^{δa}/2 ≤ cosh((1+δ)a)/cosh a` for `a, δ ≥ 0`. -/
theorem cosh_ratio_lower {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) :
    exp (δ * a) / 2 ≤ cosh ((1 + δ) * a) / cosh a := by
  rw [le_div_iff₀ (cosh_pos a), show (1 + δ) * a = a + δ * a by ring, Real.cosh_add]
  have hq : exp (δ * a) / 2 ≤ cosh (δ * a) := by
    rw [Real.cosh_eq]; linarith [exp_pos (-(δ * a))]
  have hprod : 0 ≤ sinh a * sinh (δ * a) :=
    mul_nonneg (Real.sinh_nonneg_iff.2 ha) (Real.sinh_nonneg_iff.2 (mul_nonneg hδ ha))
  nlinarith [cosh_pos a]

/-- `cosh((1+δ)a)/cosh a ≤ e^{δa}` for `a, δ ≥ 0`. -/
theorem cosh_ratio_upper {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) :
    cosh ((1 + δ) * a) / cosh a ≤ exp (δ * a) := by
  rw [div_le_iff₀ (cosh_pos a), show (1 + δ) * a = a + δ * a by ring, Real.cosh_add,
    show exp (δ * a) = cosh (δ * a) + sinh (δ * a) by rw [Real.cosh_eq, Real.sinh_eq]; ring]
  nlinarith [Real.sinh_lt_cosh (x := a), Real.sinh_nonneg_iff.2 (mul_nonneg hδ ha)]

/-- The positive shell density `w_B(a) = Q_ε / cosh a` of report (35), carried on `[B, B+1]`. -/
def w_B (ε a : ℝ) : ℝ := Qε ε / cosh a

theorem positiveShellDensity_continuous (ε : ℝ) : Continuous (w_B ε) :=
  continuous_const.div Real.continuous_cosh fun a ↦ (cosh_pos a).ne'

/-- Damping `D_B(T)` produced by the positive shell on the contour of height `1 + δ`. -/
def D_B (ε ℓ δ T : ℝ) : ℝ :=
  ℓ * ∫ a in Bε ε..Bε ε + 1, w_B ε a * cosh ((1 + δ) * a) * (1 - cos (a * T))

/-- Report (60): `D_B(T) ≥ c λ Q e^{δB} min(T², 1)`. -/
theorem positiveShellDamping_lower_bound {ε ℓ δ T : ℝ} (hε : 0 < ε) (hℓ : 0 ≤ ℓ) (hδ : 0 ≤ δ) :
    ℓ / 50 * Qε ε * exp (δ * Bε ε) * min (T ^ 2) 1 ≤ D_B ε ℓ δ T := by
  have hB : 0 ≤ Bε ε := by unfold Bε; positivity
  have hQ : 0 < Qε ε := shellWeight_pos ε
  set C : ℝ := Qε ε * exp (δ * Bε ε) / 2 with hC
  have hosc : Continuous fun a : ℝ ↦ 1 - cos (a * T) := by fun_prop
  have hpoint : ∀ a ∈ Icc (Bε ε) (Bε ε + 1),
      C * (1 - cos (a * T)) ≤ w_B ε a * cosh ((1 + δ) * a) * (1 - cos (a * T)) := by
    intro a ha
    have ha0 : 0 ≤ a := hB.trans ha.1
    refine mul_le_mul_of_nonneg_right ?_ (sub_nonneg.2 (Real.cos_le_one _))
    rw [show w_B ε a * cosh ((1 + δ) * a) = Qε ε * (cosh ((1 + δ) * a) / cosh a) by
      rw [w_B]; ring, hC]
    calc Qε ε * exp (δ * Bε ε) / 2 = Qε ε * (exp (δ * Bε ε) / 2) := by ring
      _ ≤ Qε ε * (exp (δ * a) / 2) := by gcongr; exact ha.1
      _ ≤ Qε ε * (cosh ((1 + δ) * a) / cosh a) :=
          mul_le_mul_of_nonneg_left (cosh_ratio_lower ha0 hδ) hQ.le
  have hint₁ : IntervalIntegrable (fun a : ℝ ↦ C * (1 - cos (a * T))) volume (Bε ε) (Bε ε + 1) :=
    (continuous_const.mul hosc).intervalIntegrable _ _
  have hint₂ : IntervalIntegrable (fun a : ℝ ↦ w_B ε a * cosh ((1 + δ) * a) *
      (1 - cos (a * T))) volume (Bε ε) (Bε ε + 1) :=
    (((positiveShellDensity_continuous ε).mul (by fun_prop)).mul hosc).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (by linarith : Bε ε ≤ Bε ε + 1)
    hint₁ hint₂ hpoint
  rw [intervalIntegral.integral_const_mul] at hmono
  have hCpos : 0 ≤ C := by rw [hC]; positivity
  calc ℓ / 50 * Qε ε * exp (δ * Bε ε) * min (T ^ 2) 1
      = ℓ * (C * (1 / 25 * min (T ^ 2) 1)) := by rw [hC]; ring
    _ ≤ ℓ * (C * shellOscillation (Bε ε) T) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (shellOscillation_lower_bound _ _) hCpos) hℓ
    _ ≤ D_B ε ℓ δ T := mul_le_mul_of_nonneg_left hmono hℓ

/-- `∫_B^{B+1} w_B(a) a sinh((1 + ε/4)a) da`: the positive shell's saddle-radius contribution. -/
def positiveShellRadiusContribution (ε : ℝ) : ℝ :=
  ∫ a in Bε ε..Bε ε + 1, w_B ε a * a * sinh ((1 + ε / 4) * a)

/-- Lemma 4.2 of the report: the positive shell's saddle contribution is nonnegative and
exponentially small. -/
theorem positiveShellRadiusContribution_bounds {ε : ℝ} (hε : 0 < ε) :
    0 ≤ positiveShellRadiusContribution ε ∧
      positiveShellRadiusContribution ε ≤ (Bε ε + 1) * Qε ε * exp (ε / 4 * (Bε ε + 1)) := by
  have hB : 0 ≤ Bε ε := by unfold Bε; positivity
  have hQ : 0 < Qε ε := shellWeight_pos ε
  have hδ : (0 : ℝ) ≤ ε / 4 := by positivity
  have hw (a : ℝ) : 0 ≤ w_B ε a := (div_pos hQ (cosh_pos a)).le
  have hcont : Continuous fun a : ℝ ↦ w_B ε a * a * sinh ((1 + ε / 4) * a) :=
    ((positiveShellDensity_continuous ε).mul continuous_id).mul (by fun_prop)
  unfold positiveShellRadiusContribution
  refine ⟨intervalIntegral.integral_nonneg (by linarith) fun a ha ↦
    mul_nonneg (mul_nonneg (hw a) (hB.trans ha.1))
      (Real.sinh_nonneg_iff.2 (mul_nonneg (by linarith) (hB.trans ha.1))), ?_⟩
  have hpoint : ∀ a ∈ Icc (Bε ε) (Bε ε + 1), w_B ε a * a * sinh ((1 + ε / 4) * a) ≤
      (Bε ε + 1) * Qε ε * exp (ε / 4 * (Bε ε + 1)) := by
    intro a ha
    have ha0 : 0 ≤ a := hB.trans ha.1
    calc w_B ε a * a * sinh ((1 + ε / 4) * a) ≤ w_B ε a * a * cosh ((1 + ε / 4) * a) := by
          gcongr
          · exact mul_nonneg (hw a) ha0
          · exact (Real.sinh_lt_cosh (x := (1 + ε / 4) * a)).le
      _ = Qε ε * a * (cosh ((1 + ε / 4) * a) / cosh a) := by rw [w_B]; ring
      _ ≤ Qε ε * (Bε ε + 1) * exp (ε / 4 * (Bε ε + 1)) := by
          gcongr
          · exact ha.2
          · exact (cosh_ratio_upper ha0 hδ).trans
              (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ha.2 hδ))
      _ = (Bε ε + 1) * Qε ε * exp (ε / 4 * (Bε ε + 1)) := by ring
  simpa using intervalIntegral.integral_mono_on (μ := volume) (by linarith)
    (hcont.intervalIntegrable _ _) (intervalIntegrable_const) hpoint

/-- The negative shell density `w_s(a) = -b_ε(a) e^{-2a} / (2a² cosh a)` of report (35), carried
on `[a₀, A]`. -/
def w_s (ε a : ℝ) : ℝ := -(bε ε a * exp (-2 * a) / (2 * a ^ 2 * cosh a))

theorem shortShellDensity_intervalIntegrable {ε : ℝ} (hε : 0 < ε) (horder : a₀ε ε ≤ Aε ε) :
    IntervalIntegrable (w_s ε) volume (a₀ε ε) (Aε ε) := by
  have hn : Continuous fun a : ℝ ↦ bε ε a * exp (-2 * a) := by unfold bε; fun_prop
  have hd : Continuous fun a : ℝ ↦ 2 * a ^ 2 * cosh a := by fun_prop
  refine ContinuousOn.intervalIntegrable_of_Icc horder ?_
  unfold w_s
  refine (hn.continuousOn.div hd.continuousOn fun a ha ↦ ?_).neg
  have hcutoff : 0 < a₀ε ε := by unfold a₀ε; positivity
  have ha0 : 0 < a := hcutoff.trans_le ha.1
  positivity

/-- `w_s ε` frozen at the cutoff below `a₀ε ε`: a globally continuous extension that agrees with
`w_s ε` on the short shell. -/
def shortShellDensityExt (ε a : ℝ) : ℝ := w_s ε (max a (a₀ε ε))

theorem shortShellDensityExt_continuous {ε : ℝ} (hε : 0 < ε) :
    Continuous (shortShellDensityExt ε) := by
  have hcutoff : 0 < a₀ε ε := by unfold a₀ε; positivity
  have hmax (a : ℝ) : 0 < max a (a₀ε ε) := hcutoff.trans_le (le_max_right _ _)
  have hn : Continuous fun a : ℝ ↦ bε ε (max a (a₀ε ε)) * exp (-2 * max a (a₀ε ε)) := by
    unfold bε; fun_prop
  have hd : Continuous fun a : ℝ ↦ 2 * max a (a₀ε ε) ^ 2 * cosh (max a (a₀ε ε)) := by fun_prop
  unfold shortShellDensityExt w_s
  exact (hn.div hd fun a ↦ by positivity [hmax a]).neg

/-- The entire even Mellin perturbation `h_ε(ζ) = ∫ w(a)(cos(aζ) - 1) da` of report (36). -/
def h_ε (ε : ℝ) (z : ℂ) : ℂ :=
  (∫ a in a₀ε ε..Aε ε, (w_s ε a : ℂ) * (Complex.cos ((a : ℂ) * z) - 1)) +
  ∫ a in Bε ε..Bε ε + 1, (w_B ε a : ℂ) * (Complex.cos ((a : ℂ) * z) - 1)

theorem mellinShellPhase_neg (ε : ℝ) (z : ℂ) : h_ε ε (-z) = h_ε ε z := by
  unfold h_ε
  congr 1 <;> exact intervalIntegral.integral_congr fun a _ ↦ by simp

/-- `h_ε` restricted to the real axis. -/
def realOscillatoryShellPhase (ε t : ℝ) : ℝ :=
  (∫ a in a₀ε ε..Aε ε, w_s ε a * (cos (a * t) - 1)) +
  ∫ a in Bε ε..Bε ε + 1, w_B ε a * (cos (a * t) - 1)

/-- `h_ε` restricted to the imaginary axis: `∫ w(a)(cosh(au) - 1) da`. -/
def h_εI (ε u : ℝ) : ℝ :=
  (∫ a in a₀ε ε..Aε ε, w_s ε a * (cosh (a * u) - 1)) +
  ∫ a in Bε ε..Bε ε + 1, w_B ε a * (cosh (a * u) - 1)

/-- A shell integral with a real integrand is the coercion of the corresponding real integral. -/
theorem intervalIntegral_ofReal_shell {w g : ℝ → ℝ} {a b : ℝ} {z : ℂ}
    (hg : ∀ x : ℝ, Complex.cos ((x : ℂ) * z) = (g x : ℂ)) :
    (∫ x in a..b, (w x : ℂ) * (Complex.cos ((x : ℂ) * z) - 1)) =
      ((∫ x in a..b, w x * (g x - 1) : ℝ) : ℂ) := by
  rw [← intervalIntegral.integral_ofReal]
  exact intervalIntegral.integral_congr fun x _ ↦ by rw [hg]; push_cast; ring

theorem mellinShellPhase_ofReal (ε t : ℝ) :
    h_ε ε (t : ℂ) = (realOscillatoryShellPhase ε t : ℂ) := by
  have hg (x : ℝ) : Complex.cos ((x : ℂ) * (t : ℂ)) = (cos (x * t) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_cos]
  unfold h_ε realOscillatoryShellPhase
  rw [intervalIntegral_ofReal_shell hg, intervalIntegral_ofReal_shell hg]
  push_cast
  ring

theorem mellinShellPhase_imaginary (ε u : ℝ) : h_ε ε (I * (u : ℂ)) = (h_εI ε u : ℂ) := by
  have hg (x : ℝ) : Complex.cos ((x : ℂ) * (I * (u : ℂ))) = (cosh (x * u) : ℂ) := by
    rw [show (x : ℂ) * (I * (u : ℂ)) = (x : ℂ) * (u : ℂ) * I by ring, ← Complex.ofReal_mul,
      Complex.cos_mul_I, ← Complex.ofReal_cosh]
  unfold h_ε h_εI
  rw [intervalIntegral_ofReal_shell hg, intervalIntegral_ofReal_shell hg]
  push_cast
  ring

theorem realHyperbolicShellPhase_neg (ε u : ℝ) : h_εI ε (-u) = h_εI ε u := by
  unfold h_εI
  congr 1 <;> exact intervalIntegral.integral_congr fun a _ ↦ by simp

/-- Differentiation under the integral sign: `z ↦ ∫_a^b w(x)(cos(xz) - 1) dx` is entire. -/
theorem shellIntegral_differentiable (w : ℝ → ℝ) (hw : Continuous w) {a b : ℝ} (hab : a ≤ b) :
    Differentiable ℂ fun z : ℂ ↦ ∫ x in a..b, (w x : ℂ) * (Complex.cos ((x : ℂ) * z) - 1) := by
  let F : ℂ → ℝ → ℂ := fun z x ↦ (w x : ℂ) * (Complex.cos ((x : ℂ) * z) - 1)
  let F' : ℂ → ℝ → ℂ := fun z x ↦ (w x : ℂ) * (-Complex.sin ((x : ℂ) * z) * (x : ℂ))
  have hF (z : ℂ) : Continuous (F z) := (Complex.continuous_ofReal.comp hw).mul (by fun_prop)
  have hF' (z : ℂ) : Continuous (F' z) := (Complex.continuous_ofReal.comp hw).mul (by fun_prop)
  have hF'joint : Continuous (Function.uncurry F') :=
    (Complex.continuous_ofReal.comp (hw.comp continuous_snd)).mul (by fun_prop)
  have hderiv (x : ℝ) (z : ℂ) : HasDerivAt (fun u : ℂ ↦ F u x) (F' z x) z := by
    have hlinear : HasDerivAt (fun u : ℂ ↦ (x : ℂ) * u) (x : ℂ) z := by
      simpa using (hasDerivAt_id z).const_mul (x : ℂ)
    simpa [F, F', mul_assoc] using
      ((((Complex.hasDerivAt_cos ((x : ℂ) * z)).comp z hlinear).sub_const 1).const_mul (w x : ℂ))
  have hrw : (fun z : ℂ ↦ ∫ x in a..b, (w x : ℂ) * (Complex.cos ((x : ℂ) * z) - 1)) =
      fun z : ℂ ↦ ∫ x in Icc a b, F z x := by
    funext z
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  rw [hrw]
  intro z₀
  obtain ⟨C, hC⟩ : BddAbove ((fun q : ℂ × ℝ ↦ ‖F' q.1 q.2‖) ''
      (Metric.closedBall z₀ 1 ×ˢ Icc a b)) :=
    ((isCompact_closedBall z₀ 1).prod isCompact_Icc).bddAbove_image hF'joint.norm.continuousOn
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Icc a b))
    (s := Metric.ball z₀ 1) (bound := fun _ : ℝ ↦ C) (Metric.ball_mem_nhds z₀ zero_lt_one)
    (.of_forall fun z ↦ (hF z).aestronglyMeasurable) (hF z₀).integrableOn_Icc
    (hF' z₀).aestronglyMeasurable ?_ (integrableOn_const isCompact_Icc.measure_ne_top)
    (.of_forall fun x z _ ↦ hderiv x z)).2.differentiableAt
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx z hz
  have hpair : (z, x) ∈ Metric.closedBall z₀ 1 ×ˢ Icc a b :=
    ⟨Metric.ball_subset_closedBall hz, hx⟩
  exact hC (Set.mem_image_of_mem (fun q : ℂ × ℝ ↦ ‖F' q.1 q.2‖) hpair)

theorem mellinShellPhase_differentiable {ε : ℝ} (hε : 0 < ε) (horder : a₀ε ε ≤ Aε ε) :
    Differentiable ℂ (h_ε ε) := by
  have heq : (fun z : ℂ ↦ ∫ a in a₀ε ε..Aε ε, (w_s ε a : ℂ) * (Complex.cos ((a : ℂ) * z) - 1)) =
      fun z : ℂ ↦ ∫ a in a₀ε ε..Aε ε,
        (shortShellDensityExt ε a : ℂ) * (Complex.cos ((a : ℂ) * z) - 1) := by
    refine funext fun z ↦ intervalIntegral.integral_congr fun a ha ↦ ?_
    rw [uIcc_of_le horder] at ha
    rw [shortShellDensityExt, max_eq_left ha.1]
  have hshort : Differentiable ℂ fun z : ℂ ↦
      ∫ a in a₀ε ε..Aε ε, (w_s ε a : ℂ) * (Complex.cos ((a : ℂ) * z) - 1) := by
    rw [heq]
    exact shellIntegral_differentiable _ (shortShellDensityExt_continuous hε) horder
  exact hshort.add
    (shellIntegral_differentiable _ (positiveShellDensity_continuous ε) (by linarith))

theorem mellinShellPhase_analyticOnNhd {ε : ℝ} (hε : 0 < ε) (horder : a₀ε ε ≤ Aε ε) :
    AnalyticOnNhd ℂ (h_ε ε) Set.univ :=
  Complex.analyticOnNhd_univ_iff_differentiable.mpr (mellinShellPhase_differentiable hε horder)

/-- Total variation `∫ |w_s| + ∫ |w_B|` of the two shells. -/
def saddleShellTotalVariation (ε : ℝ) : ℝ :=
  (∫ a in a₀ε ε..Aε ε, |w_s ε a|) + ∫ a in Bε ε..Bε ε + 1, |w_B ε a|

/-- A shell integral against `cos(at) - 1` is bounded by twice the weight's total variation. -/
theorem abs_integral_cos_sub_one_le {w : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hw : IntervalIntegrable w volume a b) (t : ℝ) :
    |∫ x in a..b, w x * (cos (x * t) - 1)| ≤ 2 * ∫ x in a..b, |w x| := by
  have hosc : Continuous fun x : ℝ ↦ cos (x * t) - 1 := by fun_prop
  rw [← intervalIntegral.integral_const_mul]
  refine (intervalIntegral.abs_integral_le_integral_abs hab).trans
    (intervalIntegral.integral_mono_on hab (hw.mul_continuousOn hosc.continuousOn).abs
      (hw.abs.const_mul 2) fun x _ ↦ ?_)
  have hcos : |cos (x * t) - 1| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith [Real.neg_one_le_cos (x * t), Real.cos_le_one (x * t)]
  rw [abs_mul]
  nlinarith [abs_nonneg (w x)]

theorem abs_realOscillatoryShellPhase_le {ε : ℝ} (hε : 0 < ε) (horder : a₀ε ε ≤ Aε ε) (t : ℝ) :
    |realOscillatoryShellPhase ε t| ≤ 2 * saddleShellTotalVariation ε := by
  unfold realOscillatoryShellPhase saddleShellTotalVariation
  linarith [abs_integral_cos_sub_one_le horder (shortShellDensity_intervalIntegrable hε horder) t,
    abs_integral_cos_sub_one_le (by linarith : Bε ε ≤ Bε ε + 1)
      ((positiveShellDensity_continuous ε).intervalIntegrable _ _) t,
    abs_add_le (∫ a in a₀ε ε..Aε ε, w_s ε a * (cos (a * t) - 1))
      (∫ a in Bε ε..Bε ε + 1, w_B ε a * (cos (a * t) - 1))]

theorem mellinShellPhase_real_conj (ε t : ℝ) :
    starRingEnd ℂ (h_ε ε (t : ℂ)) = h_ε ε (t : ℂ) := by
  rw [mellinShellPhase_ofReal]
  exact Complex.conj_ofReal _

/-- The perturbed Gamma envelope `E_λ(t) = π^{it/2} Γ((λ - it)/2) e^{λ h_ε(t/λ)}`, report (38). -/
def E (ε ℓ t : ℝ) : ℂ :=
  Complex.exp (I * (t : ℂ) * (log π : ℂ) / 2) * Complex.Gamma (((ℓ : ℂ) - I * (t : ℂ)) / 2) *
    Complex.exp ((ℓ : ℂ) * h_ε ε ((t : ℂ) / (ℓ : ℂ)))

/-- `X₊(t) = E_λ(t) P₊(t/λ)`. -/
def XPlus (ε ℓ t : ℝ) : ℂ := E ε ℓ t * PPlus ε ((t : ℂ) / (ℓ : ℂ))

/-- `X₋(t) = E_λ(t) P₋(t/λ)`. -/
def XMinus (ε ℓ t : ℝ) : ℂ := E ε ℓ t * PMinus ε ((t : ℂ) / (ℓ : ℂ))

theorem E_continuous {ε ℓ : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ) (horder : a₀ε ε ≤ Aε ε) :
    Continuous (E ε ℓ) := by
  have hgamma : Continuous fun t : ℝ ↦ Complex.Gamma (((ℓ : ℂ) - I * (t : ℂ)) / 2) := by
    refine continuous_iff_continuousAt.2 fun t ↦ ?_
    have hpoles : ∀ m : ℕ, ((ℓ : ℂ) - I * (t : ℂ)) / 2 ≠ -(m : ℂ) := fun m hm ↦ by
      have hre := congrArg Complex.re hm
      norm_num at hre
      linarith [Nat.cast_nonneg (α := ℝ) m]
    have harg : ContinuousAt (fun u : ℝ ↦ ((ℓ : ℂ) - I * (u : ℂ)) / 2) t := by fun_prop
    simpa [Function.comp_def] using (Complex.continuousAt_Gamma _ hpoles).comp_of_eq harg rfl
  have hphase : Continuous fun t : ℝ ↦ Complex.exp ((ℓ : ℂ) * h_ε ε ((t : ℂ) / (ℓ : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul
      ((mellinShellPhase_differentiable hε horder).continuous.comp (by fun_prop)))
  exact (((by fun_prop) : Continuous fun t : ℝ ↦
    Complex.exp (I * (t : ℂ) * (log π : ℂ) / 2)).mul hgamma).mul hphase

/-- The spectrum `X_P(t) = E_λ(t) P(t/λ)` of a polynomial factor `P` (report (38)); `XPlus` and
`XMinus` are the cases `P = P₊, P₋`. -/
def spectrum (ε ℓ : ℝ) (P : ℂ → ℂ) (t : ℝ) : ℂ := E ε ℓ t * P ((t : ℂ) / (ℓ : ℂ))

theorem spectrum_continuous {ε ℓ : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ) (horder : a₀ε ε ≤ Aε ε)
    {P : ℂ → ℂ} (hP : Continuous P) : Continuous (spectrum ε ℓ P) :=
  (E_continuous hε hℓ horder).mul (hP.comp (by fun_prop))

/-- The common value `f_±(0) = 2π^{λ/2} e^{λ h_ε(i)} β` at the origin, report (42). -/
def originValue (ε ℓ : ℝ) : ℝ := 2 * π ^ (ℓ / 2) * exp (ℓ * h_εI ε 1) * β ε

theorem saddleOriginValue_pos {ε : ℝ} (hε : 0 < ε) (ℓ : ℝ) : 0 < originValue ε ℓ := by
  unfold originValue
  positivity [beta_pos hε, Real.pi_pos]

/-- `E_λ` in the Mellin coordinate `z = λ - it`. -/
def mellinEnvelope (ε ℓ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (((ℓ : ℂ) - z) * (log π : ℂ) / 2) * Complex.Gamma (z / 2) *
    Complex.exp ((ℓ : ℂ) * h_ε ε (I * (z - (ℓ : ℂ)) / (ℓ : ℂ)))

/-- `M₊(z) = E_λ(i(z - λ)) P₊(i(z - λ)/λ)`. -/
def MPlus (ε ℓ : ℝ) (z : ℂ) : ℂ :=
  mellinEnvelope ε ℓ z * PPlus ε (I * (z - (ℓ : ℂ)) / (ℓ : ℂ))

/-- `M₋(z) = E_λ(i(z - λ)) P₋(i(z - λ)/λ)`. -/
def MMinus (ε ℓ : ℝ) (z : ℂ) : ℂ :=
  mellinEnvelope ε ℓ z * PMinus ε (I * (z - (ℓ : ℂ)) / (ℓ : ℂ))

/-- `mellinEnvelope` with the `Γ(z/2)` factor removed: an entire function of `z`. -/
def saddleRegularMellinFactor (ε ℓ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (((ℓ : ℂ) - z) * (log π : ℂ) / 2) *
    Complex.exp ((ℓ : ℂ) * h_ε ε (I * (z - (ℓ : ℂ)) / (ℓ : ℂ)))

/-- The pole-free factor of the Mellin data for an arbitrary polynomial factor `P`. -/
def regularMellinFactor (ε ℓ : ℝ) (P : ℂ → ℂ) (z : ℂ) : ℂ :=
  saddleRegularMellinFactor ε ℓ z * P (I * (z - (ℓ : ℂ)) / (ℓ : ℂ))

/-- The Mellin data `M_P(z) = E_λ(i(z - λ)) P(i(z - λ)/λ)` for a polynomial factor `P`;
`MPlus` and `MMinus` are the cases `P = P₊, P₋`. -/
def mellinData (ε ℓ : ℝ) (P : ℂ → ℂ) (z : ℂ) : ℂ :=
  mellinEnvelope ε ℓ z * P (I * (z - (ℓ : ℂ)) / (ℓ : ℂ))

/-- The pole-free factor of `M₊`; definitionally `regularMellinFactor ε ℓ (PPlus ε)`. -/
def plusSaddleRegularMellinFactor (ε ℓ : ℝ) (z : ℂ) : ℂ := regularMellinFactor ε ℓ (PPlus ε) z

/-! ### The polynomial factors `P₊`, `P₋` -/

theorem differentiable_PPlus (ε : ℝ) : Differentiable ℂ (PPlus ε) := by unfold PPlus; fun_prop

theorem differentiable_PMinus (ε : ℝ) : Differentiable ℂ (PMinus ε) := by unfold PMinus; fun_prop

theorem minusPolynomial_neg (ε : ℝ) (z : ℂ) : PMinus ε (-z) = PPlus ε z := by
  unfold PMinus PPlus
  ring

theorem plusPolynomial_conj (ε : ℝ) (z : ℂ) :
    starRingEnd ℂ (PPlus ε z) = PMinus ε (starRingEnd ℂ z) := by
  unfold PPlus PMinus
  simp only [map_add, map_mul, map_pow, map_one, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem minusPolynomial_conj (ε : ℝ) (z : ℂ) :
    starRingEnd ℂ (PMinus ε z) = PPlus ε (starRingEnd ℂ z) := by
  unfold PMinus PPlus
  simp only [map_add, map_sub, map_mul, map_pow, map_one, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem norm_plusPolynomial_le (ε : ℝ) (z : ℂ) :
    ‖PPlus ε z‖ ≤ (1 + |β ε|) * (1 + ‖z‖) ^ 3 := by
  have h0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hcube : (1 : ℝ) ≤ (1 + ‖z‖) ^ 3 := one_le_pow₀ (by linarith)
  have hbase : ‖(1 : ℂ) + z ^ 2‖ ≤ (1 + ‖z‖) ^ 2 := by
    refine (norm_add_le _ _).trans ?_
    simp only [norm_one, norm_pow]
    nlinarith
  have hsplit : ‖PPlus ε z‖ ≤ (1 + ‖z‖) ^ 2 + |β ε| + ‖z‖ * (1 + ‖z‖) ^ 2 := by
    unfold PPlus
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) ?_)
    · simp only [Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add hbase le_rfl
    · rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
      gcongr
  nlinarith [mul_le_mul_of_nonneg_left hcube (abs_nonneg (β ε))]

theorem norm_minusPolynomial_le (ε : ℝ) (z : ℂ) :
    ‖PMinus ε z‖ ≤ (1 + |β ε|) * (1 + ‖z‖) ^ 3 := by
  rw [← Complex.conj_conj z, ← plusPolynomial_conj, RCLike.norm_conj]
  simpa using norm_plusPolynomial_le ε (starRingEnd ℂ z)

/-- The properties of the polynomial factors `P₊`, `P₋`, `P₀` used throughout §4 of the report:
entire, of cubic growth `‖P ζ‖ ≤ (1 + |β|)(1 + ‖ζ‖)³`, and with the conjugation symmetry
`conj (P ζ) = P (-conj ζ)` (which makes `P` real on the imaginary axis). -/
structure IsSaddlePolynomial (ε : ℝ) (P : ℂ → ℂ) : Prop where
  differentiable : Differentiable ℂ P
  norm_le : ∀ z : ℂ, ‖P z‖ ≤ (1 + |β ε|) * (1 + ‖z‖) ^ 3
  conj_eq : ∀ z : ℂ, starRingEnd ℂ (P z) = P (-starRingEnd ℂ z)

theorem isSaddlePolynomial_PPlus (ε : ℝ) : IsSaddlePolynomial ε (PPlus ε) where
  differentiable := differentiable_PPlus ε
  norm_le := norm_plusPolynomial_le ε
  conj_eq z := by rw [plusPolynomial_conj, ← minusPolynomial_neg, neg_neg]

theorem isSaddlePolynomial_PMinus (ε : ℝ) : IsSaddlePolynomial ε (PMinus ε) where
  differentiable := differentiable_PMinus ε
  norm_le := norm_minusPolynomial_le ε
  conj_eq z := by rw [minusPolynomial_conj, minusPolynomial_neg]

theorem IsSaddlePolynomial.continuous {ε : ℝ} {P : ℂ → ℂ} (hP : IsSaddlePolynomial ε P) :
    Continuous P :=
  hP.differentiable.continuous

/-- A saddle polynomial is real on the imaginary axis. -/
theorem IsSaddlePolynomial.im_imaginary {ε : ℝ} {P : ℂ → ℂ} (hP : IsSaddlePolynomial ε P)
    (u : ℝ) : (P (I * u)).im = 0 := by
  have h := hP.conj_eq (I * u)
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul, neg_neg] at h
  exact Complex.conj_eq_iff_im.mp h

theorem mellinData_eq_gamma_mul_regular (ε ℓ : ℝ) (P : ℂ → ℂ) (z : ℂ) :
    mellinData ε ℓ P z = Complex.Gamma (z / 2) * regularMellinFactor ε ℓ P z := by
  unfold mellinData mellinEnvelope regularMellinFactor saddleRegularMellinFactor
  ring

theorem mellinData_eq (ε ℓ : ℝ) (P : ℂ → ℂ) :
    mellinData ε ℓ P = fun z ↦ Complex.Gamma (z / 2) * regularMellinFactor ε ℓ P z :=
  funext (mellinData_eq_gamma_mul_regular ε ℓ P)

theorem saddleRegularMellinFactor_differentiable {ε : ℝ} (hε : 0 < ε) (horder : a₀ε ε ≤ Aε ε)
    (ℓ : ℝ) : Differentiable ℂ (saddleRegularMellinFactor ε ℓ) := by
  have harg : Differentiable ℂ fun z : ℂ ↦ I * (z - (ℓ : ℂ)) / (ℓ : ℂ) := by fun_prop
  have hphase : Differentiable ℂ fun z : ℂ ↦
      Complex.exp ((ℓ : ℂ) * h_ε ε (I * (z - (ℓ : ℂ)) / (ℓ : ℂ))) :=
    Complex.differentiable_exp.comp
      (((mellinShellPhase_differentiable hε horder).comp harg).const_mul (ℓ : ℂ))
  exact ((by fun_prop) : Differentiable ℂ fun z : ℂ ↦
    Complex.exp (((ℓ : ℂ) - z) * (log π : ℂ) / 2)).mul hphase

theorem saddleRegularMellinFactor_continuous {ε : ℝ} (hε : 0 < ε) (horder : a₀ε ε ≤ Aε ε)
    (ℓ : ℝ) : Continuous (saddleRegularMellinFactor ε ℓ) :=
  (saddleRegularMellinFactor_differentiable hε horder ℓ).continuous

theorem regularMellinFactor_differentiable {ε : ℝ} (hε : 0 < ε) (horder : a₀ε ε ≤ Aε ε) (ℓ : ℝ)
    {P : ℂ → ℂ} (hP : Differentiable ℂ P) : Differentiable ℂ (regularMellinFactor ε ℓ P) := by
  unfold regularMellinFactor
  exact (saddleRegularMellinFactor_differentiable hε horder ℓ).mul (hP.comp (by fun_prop))

theorem mellinData_meromorphic {ε : ℝ} (hε : 0 < ε) (horder : a₀ε ε ≤ Aε ε) (ℓ : ℝ)
    {P : ℂ → ℂ} (hP : Differentiable ℂ P) : Meromorphic (mellinData ε ℓ P) := by
  rw [mellinData_eq]
  exact Complex.meromorphic_Gamma_div_two.mul (meromorphicOn_univ.mp
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (regularMellinFactor_differentiable hε horder ℓ hP)).meromorphicOn)

theorem saddleMellinGamma_differentiableAt_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ (fun w : ℂ ↦ Complex.Gamma (w / 2)) z := by
  have hhalf : 0 < (z / 2).re := by simpa using half_pos hz
  exact (Complex.differentiableAt_Gamma (z / 2) (by
    intro n hn
    have hnonpos : (-(n : ℂ)).re ≤ 0 := by simp
    exact not_lt_of_ge hnonpos (hn ▸ hhalf))).comp z (by fun_prop)

theorem saddleMellinGamma_differentiableAt_of_not_pole {z : ℂ}
    (hz : ∀ n : ℕ, z ≠ -(2 * n : ℂ)) :
    DifferentiableAt ℂ (fun w : ℂ ↦ Complex.Gamma (w / 2)) z :=
  (Complex.differentiableAt_Gamma (z / 2) fun n hn ↦
    hz n (by linear_combination 2 * hn)).comp z (by fun_prop)

theorem mellinData_differentiableOn_rightHalfPlane {ε : ℝ} (hε : 0 < ε) (horder : a₀ε ε ≤ Aε ε)
    (ℓ : ℝ) {P : ℂ → ℂ} (hP : Differentiable ℂ P) :
    DifferentiableOn ℂ (mellinData ε ℓ P) {z : ℂ | 0 < z.re} := by
  have hgamma : DifferentiableOn ℂ (fun z : ℂ ↦ Complex.Gamma (z / 2)) {z : ℂ | 0 < z.re} :=
    fun z hz ↦ (saddleMellinGamma_differentiableAt_of_re_pos hz).differentiableWithinAt
  rw [mellinData_eq]
  exact hgamma.mul (regularMellinFactor_differentiable hε horder ℓ hP).differentiableOn

theorem mellinData_differentiableAt_of_not_pole {ε : ℝ} (hε : 0 < ε) (horder : a₀ε ε ≤ Aε ε)
    (ℓ : ℝ) {P : ℂ → ℂ} (hP : Differentiable ℂ P) {z : ℂ}
    (hz : ∀ n : ℕ, z ≠ -(2 * n : ℂ)) : DifferentiableAt ℂ (mellinData ε ℓ P) z := by
  rw [mellinData_eq]
  exact (saddleMellinGamma_differentiableAt_of_not_pole hz).mul
    (regularMellinFactor_differentiable hε horder ℓ hP z)

theorem shellArgument_zero {ℓ : ℝ} (hℓ : 0 < ℓ) : I * ((0 : ℂ) - (ℓ : ℂ)) / (ℓ : ℂ) = -I := by
  have hc : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  field_simp [hc]
  ring

theorem shellArgument_neg_even {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) :
    I * (-(2 * n : ℂ) - (ℓ : ℂ)) / (ℓ : ℂ) = I * ((-(1 + 2 * (n : ℝ) / ℓ) : ℝ) : ℂ) := by
  have hc : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  push_cast
  field_simp [hc]
  ring

/-- `h_ε(-i) = h_ε(i)` is real, report (42). -/
theorem mellinShellPhase_neg_I (ε : ℝ) : h_ε ε (-I) = (h_εI ε 1 : ℂ) := by
  rw [mellinShellPhase_neg]
  simpa using mellinShellPhase_imaginary ε 1

/-- `P₊(-i) = β`, report (42). -/
theorem plusPolynomial_neg_I (ε : ℝ) : PPlus ε (-I) = (β ε : ℂ) := by
  simpa using plusPolynomial_imaginary ε (-1)

/-- `P₋(-i) = β`, report (42). -/
theorem minusPolynomial_neg_I (ε : ℝ) : PMinus ε (-I) = (β ε : ℂ) := by
  simpa using minusPolynomial_imaginary ε (-1)

theorem saddleRegularMellinFactor_zero {ε ℓ : ℝ} (hℓ : 0 < ℓ) :
    saddleRegularMellinFactor ε ℓ 0 = ((π ^ (ℓ / 2) * exp (ℓ * h_εI ε 1) : ℝ) : ℂ) := by
  have hpi : Complex.exp (((ℓ : ℂ) - (0 : ℂ)) * (log π : ℂ) / 2) = ((π ^ (ℓ / 2) : ℝ) : ℂ) := by
    rw [Real.rpow_def_of_pos Real.pi_pos, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  unfold saddleRegularMellinFactor
  rw [shellArgument_zero hℓ, hpi, mellinShellPhase_neg_I, ← Complex.ofReal_mul,
    ← Complex.ofReal_exp, ← Complex.ofReal_mul]

/-- Report (41): the regular factor at the `n`-th pole `z = -2n`. -/
theorem saddleRegularMellinFactor_neg_even {ε ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) :
    saddleRegularMellinFactor ε ℓ (-(2 * n : ℂ)) =
      ((π ^ (ℓ / 2 + (n : ℝ)) * exp (ℓ * h_εI ε (1 + 2 * (n : ℝ) / ℓ)) : ℝ) : ℂ) := by
  have hpi : Complex.exp (((ℓ : ℂ) - (-(2 * n : ℂ))) * (log π : ℂ) / 2) =
      ((π ^ (ℓ / 2 + (n : ℝ)) : ℝ) : ℂ) := by
    rw [Real.rpow_def_of_pos Real.pi_pos, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  unfold saddleRegularMellinFactor
  rw [hpi, shellArgument_neg_even hℓ n, mellinShellPhase_imaginary,
    realHyperbolicShellPhase_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
    ← Complex.ofReal_mul]

theorem plusSaddleRegularMellinFactor_neg_even {ε ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) :
    plusSaddleRegularMellinFactor ε ℓ (-(2 * n : ℂ)) =
      ((π ^ (ℓ / 2 + (n : ℝ)) * exp (ℓ * h_εI ε (1 + 2 * (n : ℝ) / ℓ)) : ℝ) : ℂ) *
        PPlus ε (I * ((-(1 + 2 * (n : ℝ) / ℓ) : ℝ) : ℂ)) := by
  unfold plusSaddleRegularMellinFactor regularMellinFactor
  rw [saddleRegularMellinFactor_neg_even hℓ n, shellArgument_neg_even hℓ n]

/-- Report (42): twice the regular factor at `z = 0` is `2π^{λ/2} e^{λ h_ε(i)} P(-i)`. -/
theorem two_mul_regularMellinFactor_zero {ε ℓ : ℝ} (hℓ : 0 < ℓ) (P : ℂ → ℂ) :
    (2 : ℂ) * regularMellinFactor ε ℓ P 0 =
      ((2 * π ^ (ℓ / 2) * exp (ℓ * h_εI ε 1) : ℝ) : ℂ) * P (-I) := by
  unfold regularMellinFactor
  rw [saddleRegularMellinFactor_zero hℓ, shellArgument_zero hℓ]
  push_cast
  ring

/-- The strip `-2(n+1) < Re z < -2n + 1` isolating the `n`-th pole `z = -2n` of `Γ(z/2)`. -/
def saddlePoleStrip (n : ℕ) : Set ℂ :=
  {z : ℂ | -(2 * ((n : ℝ) + 1)) < z.re ∧ z.re < -(2 * (n : ℝ)) + 1}

theorem saddlePole_mem_strip (n : ℕ) : -(2 * n : ℂ) ∈ saddlePoleStrip n := by
  change -(2 * ((n : ℝ) + 1)) < (-(2 * n : ℂ)).re ∧
    (-(2 * n : ℂ)).re < -(2 * (n : ℝ)) + 1
  constructor <;> norm_num [Nat.cast_mul, Complex.mul_re]

theorem isOpen_saddlePoleStrip (n : ℕ) : IsOpen (saddlePoleStrip n) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

/-- `∏_{j < n} (z/2 + j)`: the poles of `Γ(z/2)` lying strictly to the right of the strip. -/
def poleLowerProduct (n : ℕ) (z : ℂ) : ℂ := ∏ j ∈ Finset.range n, (z / 2 + (j : ℂ))

theorem poleLowerProduct_ne_zero {n : ℕ} {z : ℂ} (hz : z ∈ saddlePoleStrip n) :
    poleLowerProduct n z ≠ 0 := by
  obtain ⟨-, hhigh⟩ : -(2 * ((n : ℝ) + 1)) < z.re ∧ z.re < -(2 * (n : ℝ)) + 1 := hz
  refine Finset.prod_ne_zero_iff.2 fun j hj hzero ↦ ?_
  have hjn : (j : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.1 hj)
  have hre := congrArg Complex.re hzero
  norm_num at hre
  linarith

/-- `2 Γ(z/2 + n + 1) / ∏_{j < n} (z/2 + j)`: the numerator of `Γ(z/2)` after the simple pole at
`z = -2n` has been cleared. -/
def gammaPoleNumerator (n : ℕ) (z : ℂ) : ℂ :=
  (2 : ℂ) * Complex.Gamma (z / 2 + (n + 1 : ℂ)) / poleLowerProduct n z

theorem Gamma_half_eq_gammaPoleNumerator_div {n : ℕ} {z : ℂ} (hstrip : z ∈ saddlePoleStrip n)
    (hpole : z ≠ -(2 * n : ℂ)) :
    Complex.Gamma (z / 2) = gammaPoleNumerator n z / (z + (2 * n : ℂ)) := by
  have hprod : (∏ j ∈ Finset.range n, (z / 2 + (j : ℂ))) ≠ 0 := poleLowerProduct_ne_zero hstrip
  have hcoord : z + (2 * n : ℂ) ≠ 0 := fun h ↦ hpole (by linear_combination h)
  obtain ⟨hlow, -⟩ : -(2 * ((n : ℝ) + 1)) < z.re ∧ z.re < -(2 * (n : ℝ)) + 1 := hstrip
  have hall : ∀ j : ℕ, z / 2 + (j : ℂ) ≠ 0 := by
    intro j hzero
    rcases lt_trichotomy j n with hj | hj | hj
    · exact Finset.prod_ne_zero_iff.mp hprod j (Finset.mem_range.2 hj) hzero
    · subst hj
      exact hcoord (by linear_combination 2 * hzero)
    · have hjn : (n : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hj
      have hre := congrArg Complex.re hzero
      norm_num at hre
      linarith
  have hrec := Complex.Gamma_add_nat_eq_mul_prod (z / 2) hall (n + 1)
  rw [Finset.prod_range_succ, Nat.cast_add, Nat.cast_one] at hrec
  have hcancel : (2 : ℂ) * (Complex.Gamma (z / 2) *
      ((∏ j ∈ Finset.range n, (z / 2 + (j : ℂ))) * (z / 2 + (n : ℂ)))) /
      ∏ j ∈ Finset.range n, (z / 2 + (j : ℂ)) =
      Complex.Gamma (z / 2) * (z + (2 * n : ℂ)) := by
    rw [show (2 : ℂ) * (Complex.Gamma (z / 2) *
        ((∏ j ∈ Finset.range n, (z / 2 + (j : ℂ))) * (z / 2 + (n : ℂ)))) =
        Complex.Gamma (z / 2) * (z + (2 * n : ℂ)) *
          ∏ j ∈ Finset.range n, (z / 2 + (j : ℂ)) by ring,
      mul_div_cancel_right₀ _ hprod]
  unfold gammaPoleNumerator poleLowerProduct
  rw [hrec, hcancel, mul_div_assoc, div_self hcoord, mul_one]

theorem gammaPoleNumerator_differentiableOn (n : ℕ) :
    DifferentiableOn ℂ (gammaPoleNumerator n) (saddlePoleStrip n) := by
  intro z hz
  have hpositive : 0 < (z / 2 + (n + 1 : ℂ)).re := by
    norm_num [Nat.cast_add]
    obtain ⟨hlow, -⟩ : -(2 * ((n : ℝ) + 1)) < z.re ∧ z.re < -(2 * (n : ℝ)) + 1 := hz
    linarith
  have hgamma : DifferentiableAt ℂ Complex.Gamma (z / 2 + (n + 1 : ℂ)) :=
    Complex.differentiableAt_Gamma _ (by
      intro m hm
      have hnonpos : (-(m : ℂ)).re ≤ 0 := by simp
      exact not_lt_of_ge hnonpos (hm ▸ hpositive))
  have hden : Differentiable ℂ (poleLowerProduct n) := by unfold poleLowerProduct; fun_prop
  exact (((hgamma.comp z (by fun_prop)).const_mul (2 : ℂ)).div (hden z)
    (poleLowerProduct_ne_zero hz)).differentiableWithinAt

theorem gammaPoleNumerator_at_pole (n : ℕ) :
    gammaPoleNumerator n (-(2 * n : ℂ)) = (2 : ℂ) * (-1 : ℂ) ^ n / (n.factorial : ℂ) := by
  have hnhds : saddlePoleStrip n ∈ 𝓝 (-(2 * n : ℂ)) :=
    (isOpen_saddlePoleStrip n).mem_nhds (saddlePole_mem_strip n)
  have hcontinuous : Tendsto (gammaPoleNumerator n) (𝓝[≠] (-(2 * n : ℂ)))
      (𝓝 (gammaPoleNumerator n (-(2 * n : ℂ)))) :=
    ((gammaPoleNumerator_differentiableOn n).differentiableAt
      hnhds).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine (tendsto_nhds_unique_of_eventuallyEq
    (Complex.tendsto_add_two_mul_natCast_mul_Gamma_div_two_nhdsNE n) hcontinuous ?_).symm
  filter_upwards [nhdsWithin_le_nhds hnhds, self_mem_nhdsWithin] with z hz hne
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hne
  have hcoord : z + (2 * n : ℂ) ≠ 0 := fun h ↦ hne (by linear_combination h)
  rw [Gamma_half_eq_gammaPoleNumerator_div hz hne, ← mul_div_assoc]
  exact mul_div_cancel_left₀ _ hcoord

/-- Numerator of the Mellin data after the simple pole at `z = -2n` has been cleared. -/
def nthPoleNumerator (ε ℓ : ℝ) (P : ℂ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  gammaPoleNumerator n z * regularMellinFactor ε ℓ P z

/-- The residue of the Mellin data at the pole `z = -2n`, report (41). -/
def poleResidue (ε ℓ : ℝ) (P : ℂ → ℂ) (n : ℕ) : ℂ :=
  (2 : ℂ) * (-1 : ℂ) ^ n / (n.factorial : ℂ) *
    regularMellinFactor ε ℓ P (-(2 * n : ℂ))

/-- The regular part of the Mellin data at the pole `z = -2n`. -/
def nthPoleRegularPart (ε ℓ : ℝ) (P : ℂ → ℂ) (n : ℕ) : ℂ → ℂ :=
  dslope (nthPoleNumerator ε ℓ P n) (-(2 * n : ℂ))

/-- The residues `Res_{z = -2n} M₊`; definitionally `poleResidue ε ℓ (PPlus ε) n`. -/
def plusSaddlePoleResidue (ε ℓ : ℝ) (n : ℕ) : ℂ := (2 : ℂ) * (-1 : ℂ) ^ n / (n.factorial : ℂ) *
    plusSaddleRegularMellinFactor ε ℓ (-(2 * n : ℂ))

/-- Report (42): the residue at `z = 0` is `2π^{λ/2} e^{λ h_ε(i)} P(-i)`, the value `f_P(0)`. -/
theorem poleResidue_zero {ε ℓ : ℝ} (hℓ : 0 < ℓ) (P : ℂ → ℂ) :
    poleResidue ε ℓ P 0 = ((2 * π ^ (ℓ / 2) * exp (ℓ * h_εI ε 1) : ℝ) : ℂ) * P (-I) := by
  simpa [poleResidue] using two_mul_regularMellinFactor_zero (ε := ε) hℓ P

/-- Report (42): `f₊(0) = 2π^{λ/2} e^{λ h_ε(i)} β`. -/
theorem poleResidue_PPlus_zero {ε ℓ : ℝ} (hℓ : 0 < ℓ) :
    poleResidue ε ℓ (PPlus ε) 0 = (originValue ε ℓ : ℂ) := by
  rw [poleResidue_zero hℓ, plusPolynomial_neg_I, originValue]
  push_cast
  ring

/-- Report (42): `f₋(0) = 2π^{λ/2} e^{λ h_ε(i)} β`. -/
theorem poleResidue_PMinus_zero {ε ℓ : ℝ} (hℓ : 0 < ℓ) :
    poleResidue ε ℓ (PMinus ε) 0 = (originValue ε ℓ : ℂ) := by
  rw [poleResidue_zero hℓ, minusPolynomial_neg_I, originValue]
  push_cast
  ring

theorem nthPoleRegularPart_differentiableOn {ε : ℝ} (hε : 0 < ε) (horder : a₀ε ε ≤ Aε ε) (ℓ : ℝ)
    {P : ℂ → ℂ} (hP : Differentiable ℂ P) (n : ℕ) :
    DifferentiableOn ℂ (nthPoleRegularPart ε ℓ P n) (saddlePoleStrip n) :=
  (Complex.differentiableOn_dslope
    ((isOpen_saddlePoleStrip n).mem_nhds (saddlePole_mem_strip n))).2
    ((gammaPoleNumerator_differentiableOn n).mul
      (regularMellinFactor_differentiable hε horder ℓ hP).differentiableOn)

theorem nthPoleNumerator_at_pole (ε ℓ : ℝ) (P : ℂ → ℂ) (n : ℕ) :
    nthPoleNumerator ε ℓ P n (-(2 * n : ℂ)) = poleResidue ε ℓ P n := by
  unfold nthPoleNumerator poleResidue
  rw [gammaPoleNumerator_at_pole]

theorem mellinData_eq_nthPoleNumerator_div (ε ℓ : ℝ) (P : ℂ → ℂ) {n : ℕ} {z : ℂ}
    (hstrip : z ∈ saddlePoleStrip n) (hpole : z ≠ -(2 * n : ℂ)) :
    mellinData ε ℓ P z = nthPoleNumerator ε ℓ P n z / (z + (2 * n : ℂ)) := by
  rw [mellinData_eq_gamma_mul_regular, Gamma_half_eq_gammaPoleNumerator_div hstrip hpole,
    nthPoleNumerator]
  ring

/-- Report (41): near the pole `z = -2n` the Mellin data is `residue/(z + 2n)` plus a regular
part. -/
theorem mellinData_nthPole_decomposition (ε ℓ : ℝ) (P : ℂ → ℂ) {n : ℕ} {z : ℂ}
    (hstrip : z ∈ saddlePoleStrip n) (hpole : z ≠ -(2 * n : ℂ)) :
    mellinData ε ℓ P z =
      poleResidue ε ℓ P n / (z + (2 * n : ℂ)) + nthPoleRegularPart ε ℓ P n z := by
  have hcoord : z + (2 * n : ℂ) ≠ 0 := fun h ↦ hpole (by linear_combination h)
  have hslope : (z + (2 * n : ℂ)) * nthPoleRegularPart ε ℓ P n z =
      nthPoleNumerator ε ℓ P n z - poleResidue ε ℓ P n := by
    have hbase := sub_smul_dslope (nthPoleNumerator ε ℓ P n) (-(2 * n : ℂ)) z
    rw [nthPoleNumerator_at_pole] at hbase
    simpa only [nthPoleRegularPart, sub_neg_eq_add, smul_eq_mul] using hbase
  rw [mellinData_eq_nthPoleNumerator_div ε ℓ P hstrip hpole,
    show nthPoleNumerator ε ℓ P n z =
      poleResidue ε ℓ P n + (z + (2 * n : ℂ)) * nthPoleRegularPart ε ℓ P n z by
      rw [hslope]; ring]
  field_simp

/-- The half-plane `Re z > -2(N+1)` containing exactly the poles `z = -2n` with `n ≤ N`. -/
def saddleFinitePoleHalfPlane (N : ℕ) : Set ℂ := {z : ℂ | -(2 * ((N : ℝ) + 1)) < z.re}

theorem saddlePole_mem_finiteHalfPlane_iff (N n : ℕ) :
    -(2 * n : ℂ) ∈ saddleFinitePoleHalfPlane N ↔ n ≤ N := by
  change -(2 * ((N : ℝ) + 1)) < (-(2 * n : ℂ)).re ↔ n ≤ N
  norm_num [Nat.cast_mul, Complex.mul_re]
  constructor
  · intro hreal
    have hn : n < N + 1 := by exact_mod_cast (by linarith : (n : ℝ) < (N : ℝ) + 1)
    lia
  · intro hn
    have hreal : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn
    linarith

end

end CohnElkies
