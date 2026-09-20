import CohnElkies.LowerBound.GammaBoundary
import CohnElkiesForMathlib.Analysis.Complex.PoissonHalfPlane

/-!
# The conformal transfer between the strip and the upper half-plane (report, proof of Lemma 3.2)

The map `t ↦ exp(π(t + iℓ)/(2ℓ))` sends the horizontal strip `|Im t| < ℓ` conformally onto the
upper half-plane `ℍ = {w | 0 < Im w}`: the lower edge `Im t = -ℓ` goes to the positive real axis,
the upper edge `Im t = ℓ` to the negative real axis, and the point `t₀ = s + iσℓ` to
`e^{πs/(2ℓ)} e^{iθ}` with `θ = π(1 + σ)/2` as in (15). Its inverse is `w ↦ (2ℓ/π) log w - iℓ`
(principal branch), which extends continuously to the two boundary half-lines.

A boundary datum `b` on the lower edge becomes the half-plane datum `x ↦ b((2ℓ/π) log x)` on
`(0, ∞)`, extended by `0` on `(-∞, 0]` (the image of the upper edge), and the substitution
`x = e^{πy/(2ℓ)}` in the half-plane Poisson formula at `t₀` produces the lower-edge harmonic
measure `ℓ⁻¹ P_σ((s - y)/ℓ) dy` of the strip; its total mass is `M_σ = (1 - σ)/2`, and the
complementary upper-edge mass is `(1 + σ)/2`.
-/

namespace CohnElkies
open scoped Real Topology
open Complex (I)
open Filter MeasureTheory Set

noncomputable section

open Real

/-! ### The conformal map and its inverse -/

/-- The conformal map `t ↦ exp(π(t + iℓ)/(2ℓ))` of the strip `|Im t| < ℓ` onto the upper
half-plane; it is `E_ℓ ℓ t 0`. -/
def stripToHalfPlane (ℓ : ℝ) (t : ℂ) : ℂ := Complex.exp (π * (t + I * ℓ) / (2 * ℓ))

/-- The inverse map `w ↦ (2ℓ/π) log w - iℓ` (principal branch of the logarithm) of the upper
half-plane onto the strip `|Im t| < ℓ`. -/
def halfPlaneToStrip (ℓ : ℝ) (w : ℂ) : ℂ := 2 * ℓ / π * Complex.log w - I * ℓ

theorem stripToHalfPlane_eq_E_ℓ (ℓ : ℝ) (t : ℂ) : stripToHalfPlane ℓ t = E_ℓ ℓ t 0 := by
  simp [stripToHalfPlane, E_ℓ]

/-- The exponent `π(t + iℓ)/(2ℓ)` is the real multiple `π/(2ℓ)` of `t + iℓ`. -/
theorem stripToHalfPlane_exponent (ℓ : ℝ) (t : ℂ) :
    (π : ℂ) * (t + I * ℓ) / (2 * ℓ) = ((π / (2 * ℓ) : ℝ) : ℂ) * (t + I * ℓ) := by
  push_cast
  ring

theorem stripToHalfPlane_exponent_im (ℓ : ℝ) (t : ℂ) :
    ((π : ℂ) * (t + I * ℓ) / (2 * ℓ)).im = π * (t.im + ℓ) / (2 * ℓ) := by
  rw [stripToHalfPlane_exponent, Complex.im_ofReal_mul, div_mul_eq_mul_div]
  simp

theorem stripToHalfPlane_im (ℓ : ℝ) (t : ℂ) :
    (stripToHalfPlane ℓ t).im = exp (π * t.re / (2 * ℓ)) * sin (π * (t.im + ℓ) / (2 * ℓ)) := by
  rw [stripToHalfPlane_eq_E_ℓ, E_ℓ_im]
  simp

/-- The open strip `|Im t| < ℓ` is mapped into the upper half-plane. -/
theorem stripToHalfPlane_im_pos {ℓ : ℝ} (hℓ : 0 < ℓ) {t : ℂ}
    (ht : t ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) : 0 < (stripToHalfPlane ℓ t).im := by
  obtain ⟨hangle, hangle'⟩ := stripSchwarzAngle_mem_Ioo hℓ ht
  rw [stripToHalfPlane_im]
  exact mul_pos (exp_pos _) (sin_pos_of_pos_of_lt_pi hangle hangle')

theorem halfPlaneToStrip_stripToHalfPlane {ℓ : ℝ} (hℓ : 0 < ℓ) {t : ℂ}
    (ht : t ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) : halfPlaneToStrip ℓ (stripToHalfPlane ℓ t) = t := by
  obtain ⟨hangle, hangle'⟩ := stripSchwarzAngle_mem_Ioo hℓ ht
  unfold halfPlaneToStrip stripToHalfPlane
  rw [Complex.log_exp (by rw [stripToHalfPlane_exponent_im]; linarith [pi_pos])
    (by rw [stripToHalfPlane_exponent_im]; exact hangle'.le)]
  field_simp [hℓ.ne']
  ring

theorem halfPlaneToStrip_im (ℓ : ℝ) (w : ℂ) :
    (halfPlaneToStrip ℓ w).im = 2 * ℓ / π * Complex.arg w - ℓ := by
  simp [halfPlaneToStrip, Complex.log_im]

/-- The upper half-plane is mapped into the open strip `|Im t| < ℓ`. -/
theorem halfPlaneToStrip_mem_strip {ℓ : ℝ} (hℓ : 0 < ℓ) {w : ℂ} (hw : 0 < w.im) :
    halfPlaneToStrip ℓ w ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ := by
  have harg₀ : 0 < Complex.arg w :=
    (Complex.arg_nonneg_iff.2 hw.le).lt_of_ne fun h ↦ hw.ne' (Complex.arg_eq_zero_iff.1 h.symm).2
  have hpos : 0 < 2 * ℓ / π := by positivity
  simp only [mem_preimage, mem_Ioo, halfPlaneToStrip_im]
  constructor <;> linarith [mul_pos hpos harg₀, div_mul_cancel₀ (2 * ℓ) pi_ne_zero,
    mul_lt_mul_of_pos_left (Complex.arg_lt_pi_iff.2 (Or.inr hw.ne')) hpos]

theorem halfPlaneToStrip_analyticAt (ℓ : ℝ) {w : ℂ} (hw : 0 < w.im) :
    AnalyticAt ℂ (halfPlaneToStrip ℓ) w :=
  (analyticAt_const.mul (analyticAt_clog (Complex.mem_slitPlane_iff.2 (Or.inr hw.ne')))).sub
    analyticAt_const

/-! ### The boundary correspondence -/

/-- The point `t₀ = s + iσℓ` of the strip is sent to `e^{πs/(2ℓ)} e^{iθ}` with `θ = θ σ`
the angle `π(1 + σ)/2` of (15). -/
theorem stripToHalfPlane_ofReal_add_I_mul_mul {ℓ : ℝ} (hℓ : 0 < ℓ) (s σ : ℝ) :
    stripToHalfPlane ℓ ((s : ℂ) + I * (σ * ℓ : ℂ)) =
      (exp (π * s / (2 * ℓ)) : ℂ) * Complex.exp (I * (θ σ : ℂ)) := by
  rw [stripToHalfPlane, Complex.ofReal_exp, ← Complex.exp_add, θ]
  congr 1
  push_cast
  field_simp [hℓ.ne']
  ring

theorem stripToHalfPlane_ofReal_add_I_mul_mul_re {ℓ : ℝ} (hℓ : 0 < ℓ) (s σ : ℝ) :
    (stripToHalfPlane ℓ ((s : ℂ) + I * (σ * ℓ : ℂ))).re = exp (π * s / (2 * ℓ)) * cos (θ σ) := by
  rw [stripToHalfPlane_ofReal_add_I_mul_mul hℓ, Complex.re_ofReal_mul, mul_comm I,
    Complex.exp_ofReal_mul_I_re]

theorem stripToHalfPlane_ofReal_add_I_mul_mul_im {ℓ : ℝ} (hℓ : 0 < ℓ) (s σ : ℝ) :
    (stripToHalfPlane ℓ ((s : ℂ) + I * (σ * ℓ : ℂ))).im = exp (π * s / (2 * ℓ)) * sin (θ σ) := by
  rw [stripToHalfPlane_ofReal_add_I_mul_mul hℓ, Complex.im_ofReal_mul, mul_comm I,
    Complex.exp_ofReal_mul_I_im]

/-- The horizontal line `Im t = σℓ`, `-1 < σ < 1`, lies in the open strip. -/
theorem ofReal_add_I_mul_mul_mem_strip {ℓ σ : ℝ} (hℓ : 0 < ℓ) (hbelow : -1 < σ)
    (habove : σ < 1) (s : ℝ) : (s : ℂ) + I * (σ * ℓ : ℂ) ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ := by
  have h : -ℓ < σ * ℓ ∧ σ * ℓ < ℓ := ⟨by nlinarith, by nlinarith⟩
  simpa using h

/-- Continuity of the inverse map up to the positive real axis: as `w → x > 0` in the
half-plane, `halfPlaneToStrip ℓ w → (2ℓ/π) log x - iℓ`, a point of the lower edge. -/
theorem tendsto_halfPlaneToStrip_ofReal_of_pos (ℓ : ℝ) {x : ℝ} (hx : 0 < x) :
    Tendsto (halfPlaneToStrip ℓ) (𝓝[{w : ℂ | 0 < w.im}] (x : ℂ))
      (𝓝 (((2 * ℓ / π * Real.log x : ℝ) : ℂ) - I * ℓ)) := by
  have hcont : ContinuousAt (halfPlaneToStrip ℓ) x :=
    (continuousAt_const.mul (continuousAt_clog (Complex.mem_slitPlane_iff.2 (Or.inl
      (by simpa using hx))))).sub continuousAt_const
  have hval : halfPlaneToStrip ℓ x = ((2 * ℓ / π * Real.log x : ℝ) : ℂ) - I * ℓ := by
    simp [halfPlaneToStrip, Complex.ofReal_log hx.le]
  rw [← hval]
  exact hcont.tendsto.mono_left nhdsWithin_le_nhds

/-- Continuity of the inverse map up to the negative real axis: as `w → x < 0` in the
half-plane, `halfPlaneToStrip ℓ w → (2ℓ/π) log (-x) + iℓ`, a point of the upper edge (the
principal logarithm satisfies `log x = log |x| + iπ` on the negative axis, approached from
above). -/
theorem tendsto_halfPlaneToStrip_ofReal_of_neg (ℓ : ℝ) {x : ℝ} (hx : x < 0) :
    Tendsto (halfPlaneToStrip ℓ) (𝓝[{w : ℂ | 0 < w.im}] (x : ℂ))
      (𝓝 (((2 * ℓ / π * Real.log (-x) : ℝ) : ℂ) + I * ℓ)) := by
  have hlog : Tendsto Complex.log (𝓝[{w : ℂ | 0 < w.im}] (x : ℂ))
      (𝓝 (Real.log ‖(x : ℂ)‖ + π * I)) :=
    (Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero (by simpa using hx)
      (by simp)).mono_left (nhdsWithin_mono _ fun w (hw : 0 < w.im) ↦ show 0 ≤ w.im from hw.le)
  have hval : (2 * ℓ / π : ℂ) * (Real.log ‖(x : ℂ)‖ + π * I) - I * ℓ =
      ((2 * ℓ / π * Real.log (-x) : ℝ) : ℂ) + I * ℓ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg hx]
    push_cast
    field_simp
    ring
  rw [← hval]
  exact (hlog.const_mul _).sub_const _

/-! ### The half-plane boundary datum -/

/-- The boundary datum on the real axis corresponding to a lower-edge datum `b` of the strip:
`x ↦ b((2ℓ/π) log x)` on `(0, ∞)`, the image of the lower edge, and `0` on `(-∞, 0]`, the image
of the upper edge. -/
def halfPlaneDatum (ℓ : ℝ) (b : ℝ → ℝ) (x : ℝ) : ℝ :=
  if 0 < x then b (2 * ℓ / π * Real.log x) else 0

theorem halfPlaneDatum_of_pos {ℓ : ℝ} {b : ℝ → ℝ} {x : ℝ} (hx : 0 < x) :
    halfPlaneDatum ℓ b x = b (2 * ℓ / π * Real.log x) := ite_eq_left hx

theorem halfPlaneDatum_of_nonpos {ℓ : ℝ} {b : ℝ → ℝ} {x : ℝ} (hx : x ≤ 0) :
    halfPlaneDatum ℓ b x = 0 := ite_eq_right (not_lt.2 hx)

theorem halfPlaneDatum_continuousAt {ℓ : ℝ} {b : ℝ → ℝ} (hb : Continuous b) {x : ℝ}
    (hx : x ≠ 0) : ContinuousAt (halfPlaneDatum ℓ b) x := by
  rcases hx.lt_or_gt with hx | hx
  · refine (continuousAt_const (y := 0)).congr ?_
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact (halfPlaneDatum_of_nonpos hy.le).symm
  · refine (hb.continuousAt.comp ((continuousAt_const (y := 2 * ℓ / π)).mul
      (Real.continuousAt_log hx.ne'))).congr ?_
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (halfPlaneDatum_of_pos hy).symm

/-- The weight `e^{u}/(1 + e^{2u})` produced by the substitution `x = e^{u}` in `dx/(1 + x²)`
is at most `e^{-|u|}`. -/
theorem exp_div_one_add_exp_sq_le_exp_neg_abs (u : ℝ) :
    exp u / (1 + exp u ^ 2) ≤ exp (-1 * |u|) := by
  rw [div_le_iff₀ (by positivity), neg_one_mul]
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu, exp_neg, inv_mul_eq_div, le_div_iff₀ (exp_pos u)]
    nlinarith
  · rw [abs_of_nonpos hu, neg_neg]
    nlinarith [exp_pos u, sq_nonneg (exp u)]

/-- The half-plane datum of a continuous, linearly bounded `b` is a Poisson-integrable datum:
`halfPlaneDatum ℓ b x / (1 + x²)` is integrable on `ℝ`. Under `x = e^{u}` the integrand on
`(0, ∞)` becomes `e^{u} b((2ℓ/π) u) / (1 + e^{2u})`, dominated by `A (1 + (2ℓ/π)|u|) e^{-|u|}`. -/
theorem integrable_halfPlaneDatum_div_one_add_sq {ℓ : ℝ} (hℓ : 0 < ℓ) {b : ℝ → ℝ}
    (hb : Continuous b) {A : ℝ} (hbound : ∀ y : ℝ, |b y| ≤ A * (1 + |y|)) :
    Integrable fun x : ℝ ↦ halfPlaneDatum ℓ b x / (1 + x ^ 2) := by
  have hmajor : Integrable fun u : ℝ ↦
      A * exp (-1 * |u|) + A * (2 * ℓ / π) * (|u| ^ 1 * exp (-1 * |u|)) :=
    ((integrable_exp_neg_mul_abs one_pos).const_mul A).add
      ((integrable_abs_pow_mul_exp_neg_mul_abs 1 one_pos).const_mul _)
  have hform : Integrable fun u : ℝ ↦ exp u / (1 + exp u ^ 2) * b (2 * ℓ / π * u) := by
    refine hmajor.mono' (Continuous.aestronglyMeasurable ?_) (.of_forall fun u ↦ ?_)
    · fun_prop (disch := intros; positivity)
    · have hbu := hbound (2 * ℓ / π * u)
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * ℓ / π)] at hbu
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity)]
      exact (mul_le_mul (exp_div_one_add_exp_sq_le_exp_neg_abs u) hbu (abs_nonneg _)
        (exp_pos _).le).trans_eq (by ring)
  have hIoi : IntegrableOn (fun x : ℝ ↦ halfPlaneDatum ℓ b x / (1 + x ^ 2)) (Ioi 0) := by
    refine (integrable_comp_exp _).1 (hform.congr (.of_forall fun u ↦ ?_))
    simp only [halfPlaneDatum_of_pos (exp_pos u), log_exp, smul_eq_mul]
    ring
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact (integrableOn_zero.congr_fun (fun x hx ↦ by
    rw [halfPlaneDatum_of_nonpos (mem_Iic.1 hx), zero_div]) measurableSet_Iic).union hIoi

/-! ### The harmonic measure of the lower edge -/

/-- The algebraic core of the transfer: for `ρ, x > 0` and `0 < sin θ`,
`π⁻¹ ρ sin θ / ((x - ρ cos θ)² + ρ² sin² θ) · (π/(2ℓ)) x = sin θ / (4ℓ ((ρ/x + x/ρ)/2 - cos θ))`,
since `(x - ρ cos θ)² + ρ² sin² θ = x² - 2ρx cos θ + ρ² = ρx (x/ρ + ρ/x - 2 cos θ)`. -/
theorem poissonKernelHalfPlane_transfer_identity {ℓ θ ρ x : ℝ} (hℓ : 0 < ℓ) (hsin : 0 < sin θ)
    (hρ : 0 < ρ) (hx : 0 < x) :
    π⁻¹ * (ρ * sin θ) / ((x - ρ * cos θ) ^ 2 + (ρ * sin θ) ^ 2) * (π / (2 * ℓ) * x) =
      sin θ / (4 * ((ρ / x + x / ρ) / 2 - cos θ)) / ℓ := by
  have hexpand : (x - ρ * cos θ) ^ 2 + (ρ * sin θ) ^ 2 = x ^ 2 - 2 * x * ρ * cos θ + ρ ^ 2 := by
    linear_combination ρ ^ 2 * sin_sq_add_cos_sq θ
  have hden : 0 < x ^ 2 - 2 * x * ρ * cos θ + ρ ^ 2 := by rw [← hexpand]; positivity
  rw [hexpand, show (ρ / x + x / ρ) / 2 - cos θ =
    (x ^ 2 - 2 * x * ρ * cos θ + ρ ^ 2) / (2 * ρ * x) by field_simp; ring]
  field_simp
  ring

/-- Under `x = e^{πy/(2ℓ)}` the half-plane Poisson kernel at the image of `t₀ = s + iσℓ`, times
the Jacobian `dx/dy = (π/(2ℓ)) x`, is the strip kernel `ℓ⁻¹ P_σ((s - y)/ℓ)` of (15). -/
theorem poissonKernelHalfPlane_stripToHalfPlane_mul {ℓ σ : ℝ} (hℓ : 0 < ℓ) (hbelow : -1 < σ)
    (habove : σ < 1) (s y : ℝ) :
    Complex.poissonKernelHalfPlane (stripToHalfPlane ℓ ((s : ℂ) + I * (σ * ℓ : ℂ)))
        (exp (π / (2 * ℓ) * y)) * (π / (2 * ℓ) * exp (π / (2 * ℓ) * y)) =
      P_σ σ ((s - y) / ℓ) / ℓ := by
  obtain ⟨hangle, hangle'⟩ := stripAngle_mem_Ioo hbelow habove
  have hcosh : cosh (π * ((s - y) / ℓ) / 2) =
      (exp (π * s / (2 * ℓ)) / exp (π / (2 * ℓ) * y) +
        exp (π / (2 * ℓ) * y) / exp (π * s / (2 * ℓ))) / 2 := by
    rw [cosh_eq, ← exp_sub, ← exp_sub]
    congr 3 <;> ring
  rw [Complex.poissonKernelHalfPlane, P_σ, stripToHalfPlane_ofReal_add_I_mul_mul_re hℓ,
    stripToHalfPlane_ofReal_add_I_mul_mul_im hℓ, hcosh]
  exact poissonKernelHalfPlane_transfer_identity hℓ (sin_pos_of_pos_of_lt_pi hangle hangle')
    (exp_pos _) (exp_pos _)

/-- The half-plane Poisson formula at `t₀ = s + iσℓ`, pulled back to the lower edge by
`x = e^{πy/(2ℓ)}`: the lower-edge harmonic measure of the strip is `ℓ⁻¹ P_σ((s - y)/ℓ) dy`
(report, proof of Lemma 3.2). -/
theorem poissonIntegralHalfPlane_halfPlaneDatum_eq_integral_P_σ {ℓ σ : ℝ} (hℓ : 0 < ℓ)
    (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) (b : ℝ → ℝ) :
    Complex.poissonIntegralHalfPlane (halfPlaneDatum ℓ b)
        (stripToHalfPlane ℓ ((s : ℂ) + I * (σ * ℓ : ℂ))) =
      ∫ y : ℝ, P_σ σ ((s - y) / ℓ) / ℓ * b y := by
  have hc : 0 < π / (2 * ℓ) := by positivity
  have hkernel := poissonKernelHalfPlane_stripToHalfPlane_mul hℓ hbelow habove s
  generalize stripToHalfPlane ℓ ((s : ℂ) + I * (σ * ℓ : ℂ)) = z at hkernel ⊢
  set F : ℝ → ℝ := fun u ↦ exp u * Complex.poissonKernelHalfPlane z (exp u) * b (2 * ℓ / π * u)
  calc Complex.poissonIntegralHalfPlane (halfPlaneDatum ℓ b) z
      = ∫ x in Ioi (0 : ℝ), Complex.poissonKernelHalfPlane z x * halfPlaneDatum ℓ b x :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
          rw [halfPlaneDatum_of_nonpos (not_lt.1 hx), mul_zero]).symm
    _ = ∫ u : ℝ, F u := by
        rw [← integral_comp_exp]
        refine integral_congr_ae (.of_forall fun u ↦ ?_)
        simp only [F, halfPlaneDatum_of_pos (exp_pos u), log_exp, smul_eq_mul]
        ring
    _ = π / (2 * ℓ) * ∫ y : ℝ, F (π / (2 * ℓ) * y) := by
        rw [Measure.integral_comp_mul_left F, abs_of_pos (inv_pos.2 hc), smul_eq_mul,
          mul_inv_cancel_left₀ hc.ne']
    _ = ∫ y : ℝ, P_σ σ ((s - y) / ℓ) / ℓ * b y := by
        rw [← integral_const_mul]
        refine integral_congr_ae (.of_forall fun y ↦ ?_)
        have hy : 2 * ℓ / π * (π / (2 * ℓ) * y) = y := by field_simp
        simp only [F, hy, ← hkernel y]
        ring

/-- **The harmonic measure identity of the report** (proof of Lemma 3.2): the half-plane Poisson
integral of the transferred datum at the image of `t₀ = s + iσℓ` is the strip Poisson integral
`∫ P_σ(T) b(s - ℓT) dT` of (16). -/
theorem poissonIntegralHalfPlane_halfPlaneDatum {ℓ σ : ℝ} (hℓ : 0 < ℓ) (hbelow : -1 < σ)
    (habove : σ < 1) (s : ℝ) (b : ℝ → ℝ) :
    Complex.poissonIntegralHalfPlane (halfPlaneDatum ℓ b)
        (stripToHalfPlane ℓ ((s : ℂ) + I * (σ * ℓ : ℂ))) =
      ∫ T : ℝ, P_σ σ T * b (s - ℓ * T) :=
  (poissonIntegralHalfPlane_halfPlaneDatum_eq_integral_P_σ hℓ hbelow habove s b).trans
    (stripPoisson_integral_changeVariables hℓ σ s b)

/-- The lower-edge harmonic measure has total mass `M_σ = (1 - σ)/2` (datum `b = 1`). -/
theorem poissonIntegralHalfPlane_halfPlaneDatum_one {ℓ σ : ℝ} (hℓ : 0 < ℓ) (hbelow : -1 < σ)
    (habove : σ < 1) (s : ℝ) :
    Complex.poissonIntegralHalfPlane (halfPlaneDatum ℓ fun _ ↦ 1)
        (stripToHalfPlane ℓ ((s : ℂ) + I * (σ * ℓ : ℂ))) = M_σ σ := by
  rw [poissonIntegralHalfPlane_halfPlaneDatum hℓ hbelow habove s]
  simpa only [mul_one] using integral_stripPoissonKernel hbelow habove

/-- The complementary upper-edge harmonic measure has mass `(1 + σ)/2`: the Poisson integral of
the indicator of `(-∞, 0]`, the image of the upper edge, at the image of `t₀ = s + iσℓ`. -/
theorem poissonIntegralHalfPlane_indicator_Iic {ℓ σ : ℝ} (hℓ : 0 < ℓ) (hbelow : -1 < σ)
    (habove : σ < 1) (s : ℝ) :
    Complex.poissonIntegralHalfPlane (fun x ↦ if x ≤ 0 then 1 else 0)
        (stripToHalfPlane ℓ ((s : ℂ) + I * (σ * ℓ : ℂ))) = (1 + σ) / 2 := by
  have hz : 0 < (stripToHalfPlane ℓ ((s : ℂ) + I * (σ * ℓ : ℂ))).im :=
    stripToHalfPlane_im_pos hℓ (ofReal_add_I_mul_mul_mem_strip hℓ hbelow habove s)
  have h₁ : Integrable fun x : ℝ ↦ halfPlaneDatum ℓ (fun _ ↦ (1 : ℝ)) x / (1 + x ^ 2) :=
    integrable_halfPlaneDatum_div_one_add_sq hℓ continuous_const (A := 1) fun y ↦ by simp
  have h₂ : Integrable fun x : ℝ ↦ (if x ≤ 0 then (1 : ℝ) else 0) / (1 + x ^ 2) :=
    ((Complex.integrable_const_div_one_add_sq 1).indicator
      (measurableSet_Iic : MeasurableSet (Iic (0 : ℝ)))).congr (.of_forall fun x ↦ by
        by_cases hx : x ≤ 0 <;> simp [hx])
  have hsum : (fun _ ↦ (1 : ℝ)) =
      halfPlaneDatum ℓ (fun _ ↦ 1) + fun x ↦ if x ≤ 0 then (1 : ℝ) else 0 := by
    ext x
    simp only [Pi.add_apply, halfPlaneDatum]
    split_ifs <;> linarith
  have h := Complex.poissonIntegralHalfPlane_const hz 1
  rw [hsum, Complex.poissonIntegralHalfPlane_add h₁ h₂ hz,
    poissonIntegralHalfPlane_halfPlaneDatum_one hℓ hbelow habove s, M_σ] at h
  linarith

end

end CohnElkies
