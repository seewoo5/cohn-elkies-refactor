import Mathlib
import CohnElkiesForMathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The Poisson kernel of the strip (report §3.1, (15) and proof of Lemma 3.2)

The strip Poisson kernel `P_σ(T) = sin θ / (4 (cosh (πT/2) - cos θ))`, `θ = π(1 + σ)/2`, of total
mass `M_σ = (1 - σ)/2`, its primitive, evenness, monotonicity in `|T|` and the maximality of its
mass on centred intervals; the conformal map `E_ℓ` of the strip `|Im z| < ℓ` onto the upper
half-plane and the regularized holomorphic Schwarz kernel `K'_ℓ` of the strip, with its bounds,
continuity and derivative on the two boundary half-lines.
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Real

/-- The angle `θ = π(1 + σ)/2` attached to the height `σ` in the strip; report (15). -/
def θ (σ : ℝ) : ℝ := π * (1 + σ) / 2

/-- The strip Poisson kernel `P_σ(T) = sin θ / (4(cosh(πT/2) - cos θ))`; report (15). -/
def P_σ (σ T : ℝ) : ℝ := sin (θ σ) / (4 * (cosh (π * T / 2) - cos (θ σ)))

/-- The total mass `M_σ = (1 - σ)/2` of the kernel `P_σ`; report (15). -/
def M_σ (σ : ℝ) : ℝ := (1 - σ) / 2

theorem stripAngle_mem_Ioo {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) :
    0 < θ σ ∧ θ σ < π := by
  have hπ := pi_pos
  unfold θ
  constructor <;> nlinarith

theorem stripBottomMass_pos {σ : ℝ} (hσ : σ < 1) : 0 < M_σ σ := by unfold M_σ; linarith

theorem stripBottomMass_lt_one {σ : ℝ} (hσ : -1 < σ) : M_σ σ < 1 := by unfold M_σ; linarith

theorem stripPoissonKernel_pos {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) (T : ℝ) :
    0 < P_σ σ T := by
  obtain ⟨hangle, hangle'⟩ := stripAngle_mem_Ioo hbelow habove
  have hsin : 0 < sin (θ σ) := sin_pos_of_pos_of_lt_pi hangle hangle'
  have hcos : cos (θ σ) < 1 := by nlinarith [sin_sq_add_cos_sq (θ σ)]
  have := one_le_cosh (π * T / 2)
  unfold P_σ
  exact div_pos hsin (by linarith)

end

noncomputable section

open Filter MeasureTheory Real Set
open scoped Interval Topology

/-- A primitive of the strip Poisson kernel `P_σ`. -/
def Q_σ (σ T : ℝ) : ℝ := arctan ((exp (π * T / 2) - cos (θ σ)) / sin (θ σ)) / π

theorem stripPoissonKernel_neg (σ T : ℝ) : P_σ σ (-T) = P_σ σ T := by
  unfold P_σ
  rw [show π * -T / 2 = -(π * T / 2) by ring, cosh_neg]

theorem Q_σ_hasDerivAt {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) (T : ℝ) :
    HasDerivAt (Q_σ σ) (P_σ σ T) T := by
  obtain ⟨hangle, hangle'⟩ := stripAngle_mem_Ioo hbelow habove
  have hsin : 0 < sin (θ σ) := sin_pos_of_pos_of_lt_pi hangle hangle'
  have hexp : 0 < exp (π * T / 2) := exp_pos _
  have hderiv : HasDerivAt (fun x : ℝ ↦ (exp (π * x / 2) - cos (θ σ)) / sin (θ σ))
      (exp (π * T / 2) * (π / 2) / sin (θ σ)) T := by
    convert! (((hasDerivAt_exp (π * T / 2)).comp T
      (((hasDerivAt_id T).const_mul π).div_const 2)).sub_const (cos (θ σ))).div_const
      (sin (θ σ)) using 1
    all_goals simp [mul_comm]
  convert! ((hasDerivAt_arctan _).comp T hderiv).div_const π using 1
  unfold P_σ
  rw [cosh_eq, exp_neg]
  have htrig := sin_sq_add_cos_sq (θ σ)
  have hden : 0 < exp (π * T / 2) ^ 2 + 1 - 2 * exp (π * T / 2) * cos (θ σ) := by
    nlinarith [sq_nonneg (exp (π * T / 2) - cos (θ σ)), sq_pos_of_pos hsin]
  field_simp [hsin.ne', pi_ne_zero, hexp.ne', hden.ne']
  nlinarith

theorem Q_σ_zero {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) : Q_σ σ 0 = θ σ / (2 * π) := by
  obtain ⟨hangle, hangle'⟩ := stripAngle_mem_Ioo hbelow habove
  have key : ∀ x : ℝ, 0 < x → x < π / 2 →
      arctan ((1 - cos (2 * x)) / sin (2 * x)) / π = 2 * x / (2 * π) := by
    intro x hx hx'
    have hc : 0 < cos x := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hx'⟩
    have hs : 0 < sin x := sin_pos_of_pos_of_lt_pi hx (by linarith [pi_pos])
    have htan : (1 - cos (2 * x)) / sin (2 * x) = tan x := by
      rw [cos_two_mul_eq_one_sub, sin_two_mul, tan_eq_sin_div_cos]
      field_simp
      ring
    rw [htan, arctan_tan (by linarith [pi_pos]) hx']
    ring
  have h := key (θ σ / 2) (by linarith) (by linarith)
  rw [show 2 * (θ σ / 2) = θ σ by ring] at h
  unfold Q_σ
  rw [mul_zero, zero_div, exp_zero]
  exact h

theorem Q_σ_tendsto_atTop {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) :
    Tendsto (Q_σ σ) atTop (𝓝 (1 / 2 : ℝ)) := by
  obtain ⟨hangle, hangle'⟩ := stripAngle_mem_Ioo hbelow habove
  have hsin : 0 < sin (θ σ) := sin_pos_of_pos_of_lt_pi hangle hangle'
  have hscale : Tendsto (fun T : ℝ ↦ π * T / 2) atTop atTop := by
    have hmul : (fun T : ℝ ↦ π * T / 2) = fun T : ℝ ↦ T * (π / 2) := by ext T; ring
    rw [hmul]
    exact tendsto_id.atTop_mul_const (half_pos pi_pos)
  have hshift : Tendsto (fun T : ℝ ↦ exp (π * T / 2) - cos (θ σ)) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-cos (θ σ))
      (tendsto_exp_atTop.comp hscale)
  have hatan := (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop).comp
    ((tendsto_div_const_atTop_of_pos hsin).2 hshift)
  unfold Q_σ
  convert! hatan.div_const π using 1
  field_simp

theorem stripPoissonKernel_integrable {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) :
    Integrable (P_σ σ) :=
  integrable_of_even (stripPoissonKernel_neg σ)
    (integrableOn_Ioi_deriv_of_nonneg' (fun T _ ↦ Q_σ_hasDerivAt hbelow habove T)
      (fun T _ ↦ (stripPoissonKernel_pos hbelow habove T).le)
      (Q_σ_tendsto_atTop hbelow habove))

theorem integral_stripPoissonKernel {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) :
    (∫ T : ℝ, P_σ σ T) = M_σ σ := by
  have habs : ∀ T : ℝ, P_σ σ |T| = P_σ σ T := fun T ↦ by
    rcases le_total 0 T with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, stripPoissonKernel_neg]
  calc (∫ T : ℝ, P_σ σ T) = ∫ T : ℝ, P_σ σ |T| :=
        integral_congr_ae (.of_forall fun T ↦ (habs T).symm)
    _ = 2 * ∫ T in Ioi (0 : ℝ), P_σ σ T := integral_comp_abs
    _ = 2 * ((1 / 2 : ℝ) - Q_σ σ 0) := by
        congr 1
        exact integral_Ioi_of_hasDerivAt_of_nonneg'
          (fun T _ ↦ Q_σ_hasDerivAt hbelow habove T)
          (fun T _ ↦ (stripPoissonKernel_pos hbelow habove T).le)
          (Q_σ_tendsto_atTop hbelow habove)
    _ = M_σ σ := by
        rw [Q_σ_zero hbelow habove]
        unfold θ M_σ
        field_simp
        ring

theorem stripPoissonKernel_antitone_abs {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) {x y : ℝ}
    (hxy : |x| ≤ |y|) : P_σ σ y ≤ P_σ σ x := by
  obtain ⟨hangle, hangle'⟩ := stripAngle_mem_Ioo hbelow habove
  have hsin : 0 < sin (θ σ) := sin_pos_of_pos_of_lt_pi hangle hangle'
  have hcos : cos (θ σ) < 1 := by nlinarith [sin_sq_add_cos_sq (θ σ)]
  have hxcosh := one_le_cosh (π * x / 2)
  have hcosh : cosh (π * x / 2) ≤ cosh (π * y / 2) := by
    refine cosh_le_cosh.2 ?_
    rw [abs_div, abs_div, abs_mul, abs_mul]
    gcongr
  unfold P_σ
  exact div_le_div_of_nonneg_left hsin.le (by linarith) (by linarith)

theorem Q_σ_centered_hasDerivAt {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) (r x : ℝ) :
    HasDerivAt (fun s : ℝ ↦ Q_σ σ (s + r) - Q_σ σ (s - r))
      (P_σ σ (x + r) - P_σ σ (x - r)) x := by
  have hplus := (Q_σ_hasDerivAt hbelow habove (x + r)).comp x ((hasDerivAt_id x).add_const r)
  have hminus := (Q_σ_hasDerivAt hbelow habove (x - r)).comp x ((hasDerivAt_id x).sub_const r)
  convert! hplus.sub hminus using 1
  all_goals simp

theorem Q_σ_centered_antitoneOn {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) {r : ℝ} (hr : 0 ≤ r) :
    AntitoneOn (fun s : ℝ ↦ Q_σ σ (s + r) - Q_σ σ (s - r)) (Ici (0 : ℝ)) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (fun x _ ↦ (Q_σ_centered_hasDerivAt hbelow habove r x).continuousAt.continuousWithinAt)
    (fun x _ ↦ (Q_σ_centered_hasDerivAt hbelow habove r x).differentiableAt.differentiableWithinAt)
    fun x hx ↦ ?_
  have hxpos : 0 ≤ x := le_of_lt (by simpa using hx)
  rw [(Q_σ_centered_hasDerivAt hbelow habove r x).deriv, sub_nonpos]
  refine stripPoissonKernel_antitone_abs hbelow habove
    ((sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).1 ?_)
  rw [sq_abs, sq_abs]
  nlinarith [mul_nonneg hxpos hr]

theorem intervalIntegral_stripPoissonKernel {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) (a b : ℝ) :
    (∫ x in a..b, P_σ σ x) = Q_σ σ b - Q_σ σ a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ Q_σ_hasDerivAt hbelow habove x)
    (stripPoissonKernel_integrable hbelow habove).intervalIntegrable

theorem Q_σ_centered_le {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) {r : ℝ} (hr : 0 ≤ r) (s : ℝ) :
    Q_σ σ (s + r) - Q_σ σ (s - r) ≤ Q_σ σ r - Q_σ σ (-r) := by
  have hanti := Q_σ_centered_antitoneOn hbelow habove hr
  rcases le_total 0 s with hs | hs
  · simpa using hanti (mem_Ici.2 le_rfl) hs hs
  · have hneg : Q_σ σ (-s + r) - Q_σ σ (-s - r) = Q_σ σ (s + r) - Q_σ σ (s - r) := by
      have h := intervalIntegral.integral_comp_neg (f := P_σ σ) (a := s - r) (b := s + r)
      simp_rw [stripPoissonKernel_neg] at h
      rw [intervalIntegral_stripPoissonKernel hbelow habove,
        intervalIntegral_stripPoissonKernel hbelow habove] at h
      convert! h.symm using 1
      ring_nf
    rw [← hneg]
    simpa using hanti (mem_Ici.2 le_rfl) (neg_nonneg.2 hs) (neg_nonneg.2 hs)

theorem stripPoissonKernel_centered_interval_max {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    {r : ℝ} (hr : 0 ≤ r) (s : ℝ) :
    (∫ x in Icc (s - r) (s + r), P_σ σ x) ≤ ∫ x in Icc (-r) r, P_σ σ x := by
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : s - r ≤ s + r),
    ← intervalIntegral.integral_of_le (by linarith : -r ≤ r),
    intervalIntegral_stripPoissonKernel hbelow habove,
    intervalIntegral_stripPoissonKernel hbelow habove]
  exact Q_σ_centered_le hbelow habove hr s

/-- The conformal map `E_ℓ(z, y) = exp(π(z - y + iℓ)/(2ℓ))` taking the strip `|Im z| < ℓ` onto
the upper half-plane, with the boundary point `y` sent to `1`; report, proof of Lemma 3.2. -/
def E_ℓ (ℓ : ℝ) (z : ℂ) (y : ℝ) : ℂ := Complex.exp (π * (z - y + I * ℓ) / (2 * ℓ))

theorem E_ℓ_continuous (ℓ : ℝ) (z : ℂ) : Continuous fun y : ℝ ↦ E_ℓ ℓ z y := by
  unfold E_ℓ; fun_prop

theorem norm_E_ℓ (ℓ : ℝ) (z : ℂ) (y : ℝ) :
    ‖E_ℓ ℓ z y‖ = exp (π * (z.re - y) / (2 * ℓ)) := by
  unfold E_ℓ
  rw [Complex.norm_exp, ← Complex.ofReal_ofNat (n := 2), ← Complex.ofReal_mul,
    Complex.div_ofReal_re]
  congr 1
  simp [Complex.mul_re]

theorem E_ℓ_re (ℓ : ℝ) (z : ℂ) (y : ℝ) : (E_ℓ ℓ z y).re =
    exp (π * (z.re - y) / (2 * ℓ)) * cos (π * (z.im + ℓ) / (2 * ℓ)) := by
  unfold E_ℓ
  rw [Complex.exp_re, ← Complex.ofReal_ofNat (n := 2), ← Complex.ofReal_mul,
    Complex.div_ofReal_re, Complex.div_ofReal_im]
  congr 1 <;> simp [Complex.mul_re, Complex.mul_im]

theorem E_ℓ_im (ℓ : ℝ) (z : ℂ) (y : ℝ) : (E_ℓ ℓ z y).im =
    exp (π * (z.re - y) / (2 * ℓ)) * sin (π * (z.im + ℓ) / (2 * ℓ)) := by
  unfold E_ℓ
  rw [Complex.exp_im, ← Complex.ofReal_ofNat (n := 2), ← Complex.ofReal_mul,
    Complex.div_ofReal_re, Complex.div_ofReal_im]
  congr 1 <;> simp [Complex.mul_re, Complex.mul_im]

theorem stripSchwarzAngle_mem_Ioo {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) :
    0 < π * (z.im + ℓ) / (2 * ℓ) ∧ π * (z.im + ℓ) / (2 * ℓ) < π := by
  obtain ⟨hlow, hhigh⟩ : -ℓ < z.im ∧ z.im < ℓ := hz
  refine ⟨div_pos (mul_pos pi_pos (by linarith)) (by linarith), ?_⟩
  rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * ℓ)]
  nlinarith [pi_pos]

theorem E_ℓ_sub_one_ne_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ} (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ)
    (y : ℝ) : E_ℓ ℓ z y - 1 ≠ 0 := by
  obtain ⟨hangle, hangle'⟩ := stripSchwarzAngle_mem_Ioo hℓ hz
  intro hzero
  have him := congrArg Complex.im hzero
  simp only [Complex.sub_im, Complex.one_im, sub_zero, Complex.zero_im, E_ℓ_im] at him
  exact (mul_pos (exp_pos _) (sin_pos_of_pos_of_lt_pi hangle hangle')).ne' him

/-- The distance from `E_ℓ` to the boundary point `1`, bounded below by the sine of the angle
`π(Im z + ℓ)/(2ℓ)` times `max 1 ‖E_ℓ‖`. -/
theorem norm_E_ℓ_sub_one_ge {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ} (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ)
    (y : ℝ) : max 1 (exp (π * (z.re - y) / (2 * ℓ))) * sin (π * (z.im + ℓ) / (2 * ℓ)) ≤
      ‖E_ℓ ℓ z y - 1‖ := by
  obtain ⟨hangle, hangle'⟩ := stripSchwarzAngle_mem_Ioo hℓ hz
  have hsin : 0 < sin (π * (z.im + ℓ) / (2 * ℓ)) := sin_pos_of_pos_of_lt_pi hangle hangle'
  have htrig := sin_sq_add_cos_sq (π * (z.im + ℓ) / (2 * ℓ))
  have ht : 0 < exp (π * (z.re - y) / (2 * ℓ)) := exp_pos _
  refine (sq_le_sq₀ (mul_nonneg (zero_le_one.trans (le_max_left _ _)) hsin.le)
    (norm_nonneg _)).1 ?_
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, sub_zero, E_ℓ_re, E_ℓ_im]
  rcases le_total (exp (π * (z.re - y) / (2 * ℓ))) 1 with hle | hle
  · rw [max_eq_left hle]
    nlinarith [sq_nonneg (exp (π * (z.re - y) / (2 * ℓ)) - cos (π * (z.im + ℓ) / (2 * ℓ)))]
  · rw [max_eq_right hle]
    nlinarith [sq_nonneg (exp (π * (z.re - y) / (2 * ℓ)) *
      cos (π * (z.im + ℓ) / (2 * ℓ)) - 1)]

/-- The regularized holomorphic strip kernel `K'_ℓ`: the Schwarz kernel of the strip corrected
by the constant `±i/(4ℓ)`, so that it decays on both boundary halflines. -/
def K'_ℓ (ℓ : ℝ) (z : ℂ) (y : ℝ) : ℂ :=
  I * ((E_ℓ ℓ z y + 1) / (E_ℓ ℓ z y - 1)) / 4 / (ℓ : ℂ) +
    (if 0 ≤ y then I else -I) / (4 * ℓ : ℂ)

/-- Closed form of `K'_ℓ`: the numerator is `E_ℓ` for `y ≥ 0` and `1` for `y < 0`. -/
theorem K'_ℓ_eq {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ} (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) (y : ℝ) :
    K'_ℓ ℓ z y =
      I * (if 0 ≤ y then E_ℓ ℓ z y else 1) / (2 * (ℓ : ℂ) * (E_ℓ ℓ z y - 1)) := by
  have hℓc : (ℓ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hℓ.ne'
  have hw := E_ℓ_sub_one_ne_zero hℓ hz y
  unfold K'_ℓ
  split <;> field_simp <;> ring

theorem norm_stripRegularizedHolomorphicPoissonKernel_of_nonneg {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) {y : ℝ} (hy : 0 ≤ y) :
    ‖K'_ℓ ℓ z y‖ ≤ exp (π * (z.re - y) / (2 * ℓ)) /
      (2 * ℓ * sin (π * (z.im + ℓ) / (2 * ℓ))) := by
  obtain ⟨hangle, hangle'⟩ := stripSchwarzAngle_mem_Ioo hℓ hz
  have hsin : 0 < sin (π * (z.im + ℓ) / (2 * ℓ)) := sin_pos_of_pos_of_lt_pi hangle hangle'
  have hge : sin (π * (z.im + ℓ) / (2 * ℓ)) ≤ ‖E_ℓ ℓ z y - 1‖ :=
    (le_mul_of_one_le_left hsin.le (le_max_left _ _)).trans (norm_E_ℓ_sub_one_ge hℓ hz y)
  have hnorm : ‖K'_ℓ ℓ z y‖ =
      exp (π * (z.re - y) / (2 * ℓ)) / (2 * ℓ * ‖E_ℓ ℓ z y - 1‖) := by
    rw [K'_ℓ_eq hℓ hz, ite_eq_left hy, norm_div, norm_mul, norm_E_ℓ]
    simp [abs_of_pos hℓ]
  rw [hnorm]
  exact div_le_div_of_nonneg_left (exp_pos _).le (by positivity)
    (mul_le_mul_of_nonneg_left hge (by positivity))

theorem norm_stripRegularizedHolomorphicPoissonKernel_of_neg {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) {y : ℝ} (hy : y < 0) :
    ‖K'_ℓ ℓ z y‖ ≤ exp (-(π * (z.re - y) / (2 * ℓ))) /
      (2 * ℓ * sin (π * (z.im + ℓ) / (2 * ℓ))) := by
  obtain ⟨hangle, hangle'⟩ := stripSchwarzAngle_mem_Ioo hℓ hz
  have hsin : 0 < sin (π * (z.im + ℓ) / (2 * ℓ)) := sin_pos_of_pos_of_lt_pi hangle hangle'
  have hexp : 0 < exp (π * (z.re - y) / (2 * ℓ)) := exp_pos _
  have hge : exp (π * (z.re - y) / (2 * ℓ)) * sin (π * (z.im + ℓ) / (2 * ℓ)) ≤
      ‖E_ℓ ℓ z y - 1‖ :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hsin.le).trans (norm_E_ℓ_sub_one_ge hℓ hz y)
  have hnorm : ‖K'_ℓ ℓ z y‖ = 1 / (2 * ℓ * ‖E_ℓ ℓ z y - 1‖) := by
    rw [K'_ℓ_eq hℓ hz, ite_eq_right (not_le.mpr hy), norm_div, norm_mul]
    simp [abs_of_pos hℓ]
  rw [hnorm, exp_neg]
  calc 1 / (2 * ℓ * ‖E_ℓ ℓ z y - 1‖)
      ≤ 1 / (2 * ℓ * (exp (π * (z.re - y) / (2 * ℓ)) *
          sin (π * (z.im + ℓ) / (2 * ℓ)))) :=
        div_le_div_of_nonneg_left zero_le_one (by positivity)
          (mul_le_mul_of_nonneg_left hge (by positivity))
    _ = (exp (π * (z.re - y) / (2 * ℓ)))⁻¹ / (2 * ℓ * sin (π * (z.im + ℓ) / (2 * ℓ))) := by
        field_simp

theorem stripRegularizedHolomorphicPoissonKernel_continuousOn_Ioi {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) :
    ContinuousOn (fun y : ℝ ↦ K'_ℓ ℓ z y) (Ioi (0 : ℝ)) := by
  have hc := E_ℓ_continuous ℓ z
  have hne : ∀ y : ℝ, 2 * (ℓ : ℂ) * (E_ℓ ℓ z y - 1) ≠ 0 := fun y ↦
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr hℓ.ne'))
      (E_ℓ_sub_one_ne_zero hℓ hz y)
  have hform : Continuous fun y : ℝ ↦
      I * E_ℓ ℓ z y / (2 * (ℓ : ℂ) * (E_ℓ ℓ z y - 1)) :=
    (continuous_const.mul hc).div (continuous_const.mul (hc.sub continuous_const)) hne
  refine hform.continuousOn.congr fun y hy ↦ ?_
  rw [K'_ℓ_eq hℓ hz, ite_eq_left (mem_Ioi.mp hy).le]

theorem stripRegularizedHolomorphicPoissonKernel_continuousOn_Iio {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) :
    ContinuousOn (fun y : ℝ ↦ K'_ℓ ℓ z y) (Iio (0 : ℝ)) := by
  have hc := E_ℓ_continuous ℓ z
  have hne : ∀ y : ℝ, 2 * (ℓ : ℂ) * (E_ℓ ℓ z y - 1) ≠ 0 := fun y ↦
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr hℓ.ne'))
      (E_ℓ_sub_one_ne_zero hℓ hz y)
  have hform : Continuous fun y : ℝ ↦ I / (2 * (ℓ : ℂ) * (E_ℓ ℓ z y - 1)) :=
    continuous_const.div (continuous_const.mul (hc.sub continuous_const)) hne
  refine hform.continuousOn.congr fun y hy ↦ ?_
  rw [K'_ℓ_eq hℓ hz, ite_eq_right (not_le.mpr (mem_Iio.mp hy)), mul_one]

/-- The complex derivative of `z ↦ K'_ℓ ℓ z y`. -/
def stripRegularizedHolomorphicPoissonKernelDeriv (ℓ : ℝ) (z : ℂ) (y : ℝ) : ℂ :=
  -(I * (π : ℂ) * E_ℓ ℓ z y) / (4 * (ℓ : ℂ) ^ 2 * (E_ℓ ℓ z y - 1) ^ 2)

theorem stripRegularizedHolomorphicPoissonKernel_hasDerivAt_deriv {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) (y : ℝ) :
    HasDerivAt (fun w : ℂ ↦ K'_ℓ ℓ w y)
      (stripRegularizedHolomorphicPoissonKernelDeriv ℓ z y) z := by
  have hℓc : (ℓ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hℓ.ne'
  have hden := E_ℓ_sub_one_ne_zero hℓ hz y
  have hexp : HasDerivAt (fun w : ℂ ↦ E_ℓ ℓ w y)
      (E_ℓ ℓ z y * ((π : ℂ) / (2 * (ℓ : ℂ)))) z := by
    have haffine := ((((hasDerivAt_id z).sub_const (y : ℂ)).add_const
      (I * (ℓ : ℂ))).const_mul (π : ℂ)).div_const (2 * (ℓ : ℂ))
    unfold E_ℓ
    convert! haffine.cexp using 1
    all_goals simp
  have hratio := (hexp.add_const 1).div (hexp.sub_const 1) hden
  have hkernel := (((hratio.const_mul I).div_const 4).div_const (ℓ : ℂ)).add_const
    ((if 0 ≤ y then I else -I) / (4 * ℓ : ℂ))
  unfold stripRegularizedHolomorphicPoissonKernelDeriv K'_ℓ
  convert! hkernel using 1
  field_simp [hℓc, hden]
  ring

theorem norm_stripRegularizedHolomorphicPoissonKernelDeriv (ℓ : ℝ) (z : ℂ) (y : ℝ) :
    ‖stripRegularizedHolomorphicPoissonKernelDeriv ℓ z y‖ =
      π * exp (π * (z.re - y) / (2 * ℓ)) / (4 * ℓ ^ 2 * ‖E_ℓ ℓ z y - 1‖ ^ 2) := by
  unfold stripRegularizedHolomorphicPoissonKernelDeriv
  rw [norm_div, norm_neg, norm_mul, norm_mul, norm_mul, norm_pow, norm_E_ℓ]
  simp [abs_of_pos pi_pos, sq_abs]

/-- The derivative of the strip kernel decays like `e^{-π|Re z - y|/(2ℓ)}` in the boundary
variable `y`. -/
theorem norm_stripRegularizedHolomorphicPoissonKernelDeriv_le {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) (y : ℝ) :
    ‖stripRegularizedHolomorphicPoissonKernelDeriv ℓ z y‖ ≤
      π * exp (-(π * |z.re - y| / (2 * ℓ))) /
        (4 * ℓ ^ 2 * sin (π * (z.im + ℓ) / (2 * ℓ)) ^ 2) := by
  obtain ⟨hangle, hangle'⟩ := stripSchwarzAngle_mem_Ioo hℓ hz
  have hsin : 0 < sin (π * (z.im + ℓ) / (2 * ℓ)) := sin_pos_of_pos_of_lt_pi hangle hangle'
  have hmax : 0 < max 1 (exp (π * (z.re - y) / (2 * ℓ))) := zero_lt_one.trans_le (le_max_left _ _)
  have habs : π * |z.re - y| / (2 * ℓ) = |π * (z.re - y) / (2 * ℓ)| := by
    rw [abs_div, abs_mul, abs_of_pos pi_pos, abs_of_pos (by positivity : (0 : ℝ) < 2 * ℓ)]
  have hkey : exp (-|π * (z.re - y) / (2 * ℓ)|) =
      exp (π * (z.re - y) / (2 * ℓ)) / max 1 (exp (π * (z.re - y) / (2 * ℓ))) ^ 2 := by
    rcases le_total (π * (z.re - y) / (2 * ℓ)) 0 with h | h
    · rw [abs_of_nonpos h, neg_neg, max_eq_left (exp_le_one_iff.mpr h)]
      simp
    · rw [abs_of_nonneg h, max_eq_right (one_le_exp h), exp_neg, sq]
      field_simp
  rw [norm_stripRegularizedHolomorphicPoissonKernelDeriv, habs]
  calc π * exp (π * (z.re - y) / (2 * ℓ)) / (4 * ℓ ^ 2 * ‖E_ℓ ℓ z y - 1‖ ^ 2)
      ≤ π * exp (π * (z.re - y) / (2 * ℓ)) / (4 * ℓ ^ 2 *
          (max 1 (exp (π * (z.re - y) / (2 * ℓ))) * sin (π * (z.im + ℓ) / (2 * ℓ))) ^ 2) :=
        div_le_div_of_nonneg_left (by positivity)
          (mul_pos (by positivity) (pow_pos (mul_pos hmax hsin) 2))
          (mul_le_mul_of_nonneg_left ((sq_le_sq₀ (mul_nonneg hmax.le hsin.le) (norm_nonneg _)).2
            (norm_E_ℓ_sub_one_ge hℓ hz y)) (by positivity))
    _ = π * exp (-|π * (z.re - y) / (2 * ℓ)|) /
          (4 * ℓ ^ 2 * sin (π * (z.im + ℓ) / (2 * ℓ)) ^ 2) := by
        rw [hkey, mul_pow]
        ring

theorem stripRegularizedHolomorphicPoissonKernelDeriv_continuous {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) :
    Continuous fun y : ℝ ↦ stripRegularizedHolomorphicPoissonKernelDeriv ℓ z y := by
  have hc := E_ℓ_continuous ℓ z
  unfold stripRegularizedHolomorphicPoissonKernelDeriv
  refine ((continuous_const.mul hc).neg.div
    (continuous_const.mul ((hc.sub continuous_const).pow 2)) fun y ↦ ?_)
  exact mul_ne_zero (mul_ne_zero (by norm_num)
    (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hℓ.ne')))
    (pow_ne_zero 2 (E_ℓ_sub_one_ne_zero hℓ hz y))

/-- Exponent comparison for `w` in the unit ball around `z`: `e^{-π|Re w - y|/(2ℓ)}` is at most
`e^{π(|Re z| + 1)/(2ℓ)} e^{-π|y|/(2ℓ)}`. -/
private theorem neg_abs_re_sub_div_le {ℓ : ℝ} (hℓ : 0 < ℓ) {z w : ℂ}
    (hwball : w ∈ Metric.ball z 1) (y : ℝ) :
    -(π * |w.re - y| / (2 * ℓ)) ≤ π * (|z.re| + 1) / (2 * ℓ) + -(π / (2 * ℓ)) * |y| := by
  have hre : |w.re| ≤ |z.re| + 1 := by
    have h1 : |w.re - z.re| ≤ ‖w - z‖ := by simpa using Complex.abs_re_le_norm (w - z)
    have h2 : ‖w - z‖ < 1 := by simpa [dist_eq_norm] using hwball
    have := abs_sub_abs_le_abs_sub w.re z.re
    linarith
  have hab : 0 ≤ |z.re| + 1 - |y| + |w.re - y| := by
    have h := abs_sub_abs_le_abs_sub y w.re
    rw [abs_sub_comm] at h
    linarith
  rw [← sub_nonneg, show π * (|z.re| + 1) / (2 * ℓ) + -(π / (2 * ℓ)) * |y| -
    -(π * |w.re - y| / (2 * ℓ)) = π / (2 * ℓ) * (|z.re| + 1 - |y| + |w.re - y|) from by ring]
  exact mul_nonneg (by positivity) hab

theorem stripRegularizedHolomorphicPoissonKernelDeriv_local_bound {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) :
    ∃ S ∈ 𝓝 z, ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ S, ∀ y : ℝ,
        ‖stripRegularizedHolomorphicPoissonKernelDeriv ℓ w y‖ ≤
          C * exp (-(π / (2 * ℓ)) * |y|) := by
  obtain ⟨hangle, hangle'⟩ := stripSchwarzAngle_mem_Ioo hℓ hz
  have hsin0 : 0 < sin (π * (z.im + ℓ) / (2 * ℓ)) := sin_pos_of_pos_of_lt_pi hangle hangle'
  have hstrip : Complex.im ⁻¹' Ioo (-ℓ) ℓ ∈ 𝓝 z :=
    (isOpen_Ioo.preimage Complex.continuous_im).mem_nhds hz
  have hAset : (fun w : ℂ ↦ sin (π * (w.im + ℓ) / (2 * ℓ))) ⁻¹'
      Ioi (sin (π * (z.im + ℓ) / (2 * ℓ)) / 2) ∈ 𝓝 z :=
    (isOpen_Ioi.preimage (by fun_prop)).mem_nhds (half_lt_self hsin0)
  refine ⟨Metric.ball z 1 ∩ Complex.im ⁻¹' Ioo (-ℓ) ℓ ∩
      (fun w : ℂ ↦ sin (π * (w.im + ℓ) / (2 * ℓ))) ⁻¹'
        Ioi (sin (π * (z.im + ℓ) / (2 * ℓ)) / 2),
    inter_mem (inter_mem (Metric.ball_mem_nhds z one_pos) hstrip) hAset,
    π * exp (π * (|z.re| + 1) / (2 * ℓ)) /
      (4 * ℓ ^ 2 * (sin (π * (z.im + ℓ) / (2 * ℓ)) / 2) ^ 2), by positivity, ?_⟩
  rintro w ⟨⟨hwball, hwstrip⟩, hwsin⟩ y
  have hwsin' : sin (π * (z.im + ℓ) / (2 * ℓ)) / 2 < sin (π * (w.im + ℓ) / (2 * ℓ)) := hwsin
  have hnum := neg_abs_re_sub_div_le hℓ hwball y
  have hden : 4 * ℓ ^ 2 * (sin (π * (z.im + ℓ) / (2 * ℓ)) / 2) ^ 2 ≤
      4 * ℓ ^ 2 * sin (π * (w.im + ℓ) / (2 * ℓ)) ^ 2 :=
    mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (by positivity) ((by positivity : (0 : ℝ) ≤
        sin (π * (z.im + ℓ) / (2 * ℓ)) / 2).trans hwsin'.le)).2 hwsin'.le) (by positivity)
  calc ‖stripRegularizedHolomorphicPoissonKernelDeriv ℓ w y‖
      ≤ π * exp (-(π * |w.re - y| / (2 * ℓ))) /
          (4 * ℓ ^ 2 * sin (π * (w.im + ℓ) / (2 * ℓ)) ^ 2) :=
        norm_stripRegularizedHolomorphicPoissonKernelDeriv_le hℓ hwstrip y
    _ ≤ π * exp (π * (|z.re| + 1) / (2 * ℓ) + -(π / (2 * ℓ)) * |y|) /
          (4 * ℓ ^ 2 * (sin (π * (z.im + ℓ) / (2 * ℓ)) / 2) ^ 2) :=
        div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left (exp_le_exp.mpr hnum) pi_pos.le)
          (mul_pos (by positivity) (pow_pos (by linarith) 2)) hden
    _ = π * exp (π * (|z.re| + 1) / (2 * ℓ)) /
          (4 * ℓ ^ 2 * (sin (π * (z.im + ℓ) / (2 * ℓ)) / 2) ^ 2) *
          exp (-(π / (2 * ℓ)) * |y|) := by
        rw [exp_add]
        ring

/-- The real part of the Cayley transform of the boundary exponential is the kernel `P_σ`. -/
theorem re_cayley {σ T : ℝ} (hbelow : -1 < σ) (habove : σ < 1) :
    (I * ((Complex.exp ((π * T / 2 : ℂ) + I * (θ σ : ℂ)) + 1) /
      (Complex.exp ((π * T / 2 : ℂ) + I * (θ σ : ℂ)) - 1)) / 4).re = P_σ σ T := by
  rw [← Complex.ofReal_ofNat (n := 2), ← Complex.ofReal_mul, ← Complex.ofReal_div]
  obtain ⟨hangle, hangle'⟩ := stripAngle_mem_Ioo hbelow habove
  have hsin : 0 < sin (θ σ) := sin_pos_of_pos_of_lt_pi hangle hangle'
  have hexp : 0 < exp (π * T / 2) := exp_pos _
  have htrig := sin_sq_add_cos_sq (θ σ)
  have hden : 0 < exp (π * T / 2) ^ 2 + 1 - 2 * exp (π * T / 2) * cos (θ σ) := by
    nlinarith [sq_nonneg (exp (π * T / 2) - cos (θ σ)), sq_pos_of_pos hsin]
  unfold P_σ
  rw [cosh_eq, exp_neg]
  simp only [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul,
    one_mul, Complex.add_re, Complex.sub_re, Complex.add_im, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, Complex.exp_re, Complex.exp_im,
    Complex.mul_im, sub_self, add_zero, zero_add, mul_zero, Complex.normSq_apply]
  norm_num
  field_simp [hexp.ne', hden.ne']
  nlinarith

/-- On the horizontal line `Im t = σℓ` the real part of `K'_ℓ` is the Poisson kernel (15). -/
theorem stripRegularizedHolomorphicPoissonKernel_re {ℓ σ : ℝ} (hℓ : 0 < ℓ) (hbelow : -1 < σ)
    (habove : σ < 1) (s y : ℝ) :
    (K'_ℓ ℓ ((s : ℂ) + I * (σ * ℓ : ℂ)) y).re = P_σ σ ((s - y) / ℓ) / ℓ := by
  have hℓc : (ℓ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hℓ.ne'
  set T := (s - y) / ℓ with hT
  have harg : ((π : ℂ) * (((s : ℂ) + I * (σ * ℓ : ℂ)) - (y : ℂ) + I * (ℓ : ℂ))) /
      (2 * (ℓ : ℂ)) = (π * T / 2 : ℂ) + I * (θ σ : ℂ) := by
    rw [hT]
    unfold θ
    push_cast
    field_simp
    ring
  unfold K'_ℓ E_ℓ
  rw [harg, Complex.add_re, Complex.div_ofReal_re, re_cayley hbelow habove]
  split <;> simp [Complex.div_re]

end

end CohnElkies
