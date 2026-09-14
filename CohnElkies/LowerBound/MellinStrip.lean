import CohnElkies.MellinFourier
import CohnElkies.LowerBound.LogProfile

/-!
# The normalized Mellin strip function `Z(z)` (report §3.1, (11)–(12))

The Mellin transform `X_f(z) = M g(d/2 - iz)` of the radial profile of a radial eigenfunction,
the normalized strip function `Z(z) = (S_d/‖g‖₁) R^{d/2 + iz} X_g(z)` on the strip
`|Im z| ≤ d/2`, its continuity up to the boundary, the bound `|Z| ≤ 1` on the upper edge and
the bound `|Z(x - id/2)| ≤ |Γ-ratio|` on the lower edge obtained from the Mellin–Fourier functional
equation, and the Fourier representation of `Z` on the shifted lines (used for the Poisson
majorization).
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Asymptotics Filter Function MeasureTheory Metric Real Set
open scoped FourierTransform SchwartzMap Topology

/-- `X_f(z) = M g(d/2 - i z)`: the Mellin transform `X_g` of the radial profile `g` of `f`
(report (8)), as a function of the complex strip variable `z`. -/
def X_f {d : ℕ} (hd : 0 < d) (f : TestFunction d) (z : ℂ) : ℂ :=
  mellin (radialProfile hd f) ((d : ℂ) / 2 - I * z)

/-- The normalized Mellin strip function `Z(z) = (S_d/‖g‖₁) R^{d/2 + iz} X_g(z)` of report
(12). -/
def Z_g {d : ℕ} (hd : 0 < d) (f : TestFunction d) (R : ℝ) (z : ℂ) : ℂ :=
  (sphereArea d / L1norm f : ℝ) * Complex.exp (((d : ℂ) / 2 + I * z) * (Real.log R : ℂ)) *
    X_f hd f z

/-- Lemma 3.2 of the report: `Z` is holomorphic on the strip `|Im z| < d/2` and continuous on
its closure. -/
theorem normalizedRadialMellinStrip_diffContOnCl {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0) (R : ℝ) :
    DiffContOnCl ℂ (Z_g hd f R) (Complex.im ⁻¹'
        Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2)) := by
  have hhalf : 0 < (d : ℝ) / 2 := half_pos (Nat.cast_pos.mpr hd)
  have hstrip : DiffContOnCl ℂ (X_f hd f)
      (Complex.im ⁻¹' Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2)) := by
    refine DifferentiableOn.diffContOnCl fun z hz ↦ ?_
    rw [Complex.closure_preimage_im, closure_Ioo (ne_of_lt (neg_lt_self hhalf))] at hz
    have hs : -2 < (((d : ℂ) / 2 - I * z).re) := by
      norm_num
      linarith [hz.1]
    exact ((radialProfile_mellin_differentiableAt hd f hf hzero _ hs).comp z
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ ↦ (d : ℂ) / 2 - I * w) z)).differentiableWithinAt
  have hfactor : Differentiable ℂ fun z : ℂ ↦
      (sphereArea d / L1norm f : ℝ) * Complex.exp (((d : ℂ) / 2 + I * z) * (log R : ℂ)) := by
    fun_prop
  exact ⟨hfactor.differentiableOn.mul hstrip.differentiableOn,
    hfactor.continuous.continuousOn.mul hstrip.continuousOn⟩

/-- The modulus of `Z_g`: the phase factor contributes `e^{Re((d/2 + iz) log R)}`. -/
theorem norm_Z_g {d : ℕ} (hd : 0 < d) (f : TestFunction d) (R : ℝ) (z : ℂ) :
    ‖Z_g hd f R z‖ = |sphereArea d / L1norm f| *
      exp ((((d : ℂ) / 2 + I * z) * (log R : ℂ)).re) *
        ‖mellin (radialProfile hd f) ((d : ℂ) / 2 - I * z)‖ := by
  unfold Z_g X_f
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]

/-- The Riesz kernel `|x|^{-it}` has modulus at most `1`, so it does not increase the `L¹` norm. -/
theorem norm_integral_mul_cpow_le_L1norm {d : ℕ} (hd : 0 < d) (f : TestFunction d) (t : ℝ) :
    ‖∫ x : Euclidean d, f x * (‖x‖ : ℂ) ^ (-(I * (t : ℂ)))‖ ≤ L1norm f := by
  have hcpow (r : ℝ) (hr : 0 ≤ r) : ‖(r : ℂ) ^ (-(I * (t : ℂ)))‖ ≤ 1 := by
    rcases hr.eq_or_lt with rfl | hrpos
    · rcases eq_or_ne t 0 with rfl | ht
      · simp
      · rw [Complex.ofReal_zero, Complex.zero_cpow (neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero
          (Complex.ofReal_ne_zero.mpr ht)))]
        simp
    · rw [Complex.norm_cpow_eq_rpow_re_of_pos hrpos]
      norm_num
  have hint : Integrable fun x : Euclidean d ↦ f x * (‖x‖ : ℂ) ^ (-(I * (t : ℂ))) := by
    refine schwartz_mul_norm_cpow_integrable hd f (-(I * (t : ℂ))) ?_ (by norm_num)
    norm_num
    exact Nat.cast_pos.mpr hd
  refine (norm_integral_le_integral_norm _).trans
    (integral_mono hint.norm f.integrable.norm fun x ↦ ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hcpow ‖x‖ (norm_nonneg x))

theorem normalizedRadialMellinStrip_top_norm_eq {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hnonzero : f ≠ 0) (R : ℝ) (y : ℝ) :
    ‖Z_g hd f R ((y : ℂ) + I * ((d : ℂ) / 2))‖ =
      sphereArea d / L1norm f * ‖mellin (radialProfile hd f) ((d : ℂ) - I * (y : ℂ))‖ := by
  have hmellin : (d : ℂ) / 2 - I * ((y : ℂ) + I * ((d : ℂ) / 2)) =
      (d : ℂ) - I * (y : ℂ) := by
    simp [mul_add, ← mul_assoc, Complex.I_mul_I]
    ring
  have hphase : ((((d : ℂ) / 2 + I * ((y : ℂ) + I * ((d : ℂ) / 2))) *
      (log R : ℂ))).re = 0 := by
    norm_num
  rw [norm_Z_g hd f, hmellin, hphase, exp_zero, mul_one,
    abs_of_pos (div_pos (radialSurfaceArea_pos hd) (radialL1Mass_pos f hnonzero))]

/-- Report (16): on the top edge `Im z = d/2` of the strip, `|Z(y + iλ)| ≤ 1`. -/
theorem normalizedRadialMellinStrip_top_norm_le_one {d : ℕ} (hd : 0 < d) (f : TestFunction d)
    (hf : IsRadial f) (hnonzero : f ≠ 0)
    (R : ℝ) (y : ℝ) :
    ‖Z_g hd f R ((y : ℂ) + I * ((d : ℂ) / 2))‖ ≤ 1 := by
  have hpolar : (∫ x : Euclidean d, f x * (‖x‖ : ℂ) ^ (-(I * (y : ℂ)))) =
      sphereArea d • mellin (radialProfile hd f) ((d : ℂ) - I * (y : ℂ)) := by
    simpa only [show ((d : ℂ) - I * (y : ℂ)) - (d : ℂ) = -(I * (y : ℂ)) by ring] using
      integral_radialProfile_cpow hd f hf ((d : ℂ) - I * (y : ℂ))
  rw [normalizedRadialMellinStrip_top_norm_eq hd f hnonzero, div_mul_eq_mul_div,
    div_le_one (radialL1Mass_pos f hnonzero)]
  calc sphereArea d * ‖mellin (radialProfile hd f) ((d : ℂ) - I * (y : ℂ))‖
      = ‖sphereArea d • mellin (radialProfile hd f) ((d : ℂ) - I * (y : ℂ))‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (radialSurfaceArea_pos hd)]
    _ ≤ L1norm f := by
        rw [← hpolar]
        exact norm_integral_mul_cpow_le_L1norm hd f y

/-- The Mellin–Fourier functional equation (9) of the report in regularized form, extended from
the open strip `0 < Re s < d` to its closure by continuity. -/
theorem radial_fourier_mellin_regularized_closed {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0)
    (hhatZero : (𝓕 f : TestFunction d) (0 : Euclidean d) = 0)
    (s : ℂ) (hs : 0 ≤ s.re) (hsd : s.re ≤ (d : ℝ)) :
    mellin (radialProfile hd (𝓕 f : TestFunction d)) s * (Complex.Gamma (s / 2))⁻¹ =
      (π : ℂ) ^ ((d : ℂ) / 2 - s) * (mellin (radialProfile hd f) ((d : ℂ) - s) *
          (Complex.Gamma (((d : ℂ) - s) / 2))⁻¹) := by
  let U : Set ℂ := Complex.re ⁻¹' Ioo (0 : ℝ) (d : ℝ)
  let T : Set ℂ := Complex.re ⁻¹' Icc (0 : ℝ) (d : ℝ)
  let L : ℂ → ℂ := fun w ↦
    mellin (radialProfile hd (𝓕 f : TestFunction d)) w * (Complex.Gamma (w / 2))⁻¹
  let G : ℂ → ℂ := fun w ↦
    (π : ℂ) ^ ((d : ℂ) / 2 - w) * (mellin (radialProfile hd f) ((d : ℂ) - w) *
        (Complex.Gamma (((d : ℂ) - w) / 2))⁻¹)
  have hinv : Continuous fun w : ℂ ↦ (Complex.Gamma w)⁻¹ :=
    Complex.differentiable_one_div_Gamma.continuous
  have hhat : ContinuousOn (fun w : ℂ ↦ mellin (radialProfile hd (𝓕 f : TestFunction d)) w) T :=
    fun w hw ↦ (radialProfile_mellin_differentiableAt hd (𝓕 f : TestFunction d)
      (gaussianMellin_fourier_radial hf) hhatZero w
      (by linarith [hw.1])).continuousAt.continuousWithinAt
  have hprimal : ContinuousOn (fun w : ℂ ↦ mellin (radialProfile hd f) ((d : ℂ) - w)) T := by
    intro w hw
    have hre : -2 < (((d : ℂ) - w).re) := by
      norm_num
      linarith [hw.2]
    exact ((radialProfile_mellin_differentiableAt hd f hf hzero ((d : ℂ) - w) hre).continuousAt.comp
      (by fun_prop : ContinuousAt (fun v : ℂ ↦ (d : ℂ) - v) w)).continuousWithinAt
  have hL : ContinuousOn L T :=
    hhat.mul (hinv.comp (continuous_id.div_const (2 : ℂ))).continuousOn
  have hG : ContinuousOn G T :=
    ((continuous_const.sub continuous_id).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr pi_ne_zero))).continuousOn.mul
      (hprimal.mul
        (hinv.comp ((continuous_const.sub continuous_id).div_const (2 : ℂ))).continuousOn)
  have heq : Set.EqOn L G U := by
    intro w hw
    have hg₁ : Complex.Gamma (w / 2) ≠ 0 := by
      refine Complex.Gamma_ne_zero_of_re_pos ?_
      norm_num
      linarith [hw.1]
    have hg₂ : Complex.Gamma (((d : ℂ) - w) / 2) ≠ 0 := by
      refine Complex.Gamma_ne_zero_of_re_pos ?_
      norm_num
      linarith [hw.2]
    dsimp only [L, G]
    rw [radial_fourier_mellin_strip hd f hf w hw.1 hw.2]
    field_simp
  refine heq.of_subset_closure hL hG (fun w hw ↦ ⟨hw.1.le, hw.2.le⟩) ?_ ⟨hs, hsd⟩
  rw [show T = Complex.re ⁻¹' Icc (0 : ℝ) (d : ℝ) from rfl, show U = Complex.re ⁻¹'
    Ioo (0 : ℝ) (d : ℝ) from rfl, Complex.closure_preimage_re,
    closure_Ioo (ne_of_lt (Nat.cast_pos.mpr hd : (0 : ℝ) < d))]

/-- `‖ς‖ = 1` for a sign `ς ∈ ℤˣ = {±1}`. -/
theorem norm_intUnits_cast (ς : ℤˣ) : ‖((ς : ℤ) : ℂ)‖ = 1 := by
  rcases Int.units_eq_one_or ς with rfl | rfl <;> simp

/-- Report (17): for a Fourier eigenfunction `𝓕 f = ς f`, the functional equation relates the
values of `M g` on the two edges `Re s = 0` and `Re s = d` of the strip. -/
theorem radial_fourier_mellin_eigenfunction_boundary {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0) {ς : ℤˣ}
    (hς : (𝓕 f : TestFunction d) = ((ς : ℤ) : ℂ) • f)
    (y : ℝ) (hy : y ≠ 0) :
    ((ς : ℤ) : ℂ) * (Complex.Gamma ((d : ℂ) / 2 + I * (y : ℂ) / 2) *
        mellin (radialProfile hd f) (-(I * (y : ℂ)))) =
      (π : ℂ) ^ (((d : ℂ) / 2) + I * (y : ℂ)) *
        Complex.Gamma (-(I * (y : ℂ)) / 2) *
        mellin (radialProfile hd f) ((d : ℂ) + I * (y : ℂ)) := by
  set s : ℂ := -(I * (y : ℂ)) with hsdef
  have hhatZero : (𝓕 f : TestFunction d) (0 : Euclidean d) = 0 := by
    rw [hς]
    simp [hzero]
  have hnum : Complex.Gamma (s / 2) ≠ 0 := by
    refine Complex.Gamma_ne_zero fun n hn ↦ ?_
    have him := congrArg Complex.im hn
    rw [hsdef] at him
    norm_num at him
    exact hy (by linarith)
  have hden : Complex.Gamma (((d : ℂ) - s) / 2) ≠ 0 := by
    refine Complex.Gamma_ne_zero_of_re_pos ?_
    rw [hsdef]
    norm_num
    exact Nat.cast_pos.mpr hd
  have heq := radial_fourier_mellin_regularized_closed hd f hf hzero hhatZero s
    (by rw [hsdef]; norm_num) (by rw [hsdef]; norm_num)
  rw [show mellin (radialProfile hd (𝓕 f : TestFunction d)) s =
      ((ς : ℤ) : ℂ) * mellin (radialProfile hd f) s by
    rw [hς, show radialProfile hd (((ς : ℤ) : ℂ) • f) = fun r ↦ ((ς : ℤ) : ℂ) • radialProfile hd f r
      from rfl, mellin_const_smul, smul_eq_mul]] at heq
  have hcross : ((ς : ℤ) : ℂ) *
        (Complex.Gamma (((d : ℂ) - s) / 2) * mellin (radialProfile hd f) s) =
      (π : ℂ) ^ ((d : ℂ) / 2 - s) * Complex.Gamma (s / 2) *
        mellin (radialProfile hd f) ((d : ℂ) - s) := by
    field_simp [hnum, hden] at heq ⊢
    linear_combination heq
  convert hcross using 1 <;> rw [hsdef] <;> ring_nf

theorem radial_fourier_mellin_eigenfunction_boundary_norm {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0) {ς : ℤˣ}
    (hς : (𝓕 f : TestFunction d) = ((ς : ℤ) : ℂ) • f)
    (y : ℝ) (hy : y ≠ 0) :
    ‖mellin (radialProfile hd f) (-(I * (y : ℂ)))‖ = π ^ ((d : ℝ) / 2) *
        (‖Complex.Gamma (-(I * (y : ℂ)) / 2)‖ / ‖Complex.Gamma
            ((d : ℂ) / 2 + I * (y : ℂ) / 2)‖) *
          ‖mellin (radialProfile hd f) ((d : ℂ) + I * (y : ℂ))‖ := by
  have hden : ‖Complex.Gamma ((d : ℂ) / 2 + I * (y : ℂ) / 2)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by norm_num; exact Nat.cast_pos.mpr hd))
  have hnorm :=
    congrArg norm (radial_fourier_mellin_eigenfunction_boundary hd f hf hzero hς y hy)
  simp only [norm_mul, norm_intUnits_cast, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos pi_pos]
    at hnorm
  norm_num at hnorm
  calc ‖mellin (radialProfile hd f) (-(I * (y : ℂ)))‖
      = (π ^ ((d : ℝ) / 2) * ‖Complex.Gamma (-(I * (y : ℂ)) / 2)‖ *
          ‖mellin (radialProfile hd f) ((d : ℂ) + I * (y : ℂ))‖) /
          ‖Complex.Gamma ((d : ℂ) / 2 + I * (y : ℂ) / 2)‖ := by
        refine (eq_div_iff hden).2 ?_
        convert hnorm using 1
        ring
    _ = _ := by ring

theorem radialGammaBoundaryExponent_exp (d : ℕ) (R A B : ℝ) (hR : 0 < R) (hA : 0 < A) (hB : 0 < B) :
    exp (((d : ℝ) / 2) * log (π * R ^ 2) + log A - log B) =
      exp ((d : ℝ) * log R) * π ^ ((d : ℝ) / 2) * (A / B) := by
  rw [log_mul pi_ne_zero (pow_ne_zero 2 hR.ne'), log_pow, mul_add, exp_sub, exp_add, exp_add,
    exp_log hA, exp_log hB, rpow_def_of_pos pi_pos,
    show ((d : ℝ) / 2) * ((2 : ℕ) * log R) = (d : ℝ) * log R by push_cast; ring,
    show ((d : ℝ) / 2) * log π = log π * ((d : ℝ) / 2) by ring]
  ring

private theorem norm_Z_g_bottom {d : ℕ} (hd : 0 < d) (f : TestFunction d) (hnonzero : f ≠ 0)
    (R y : ℝ) :
    ‖Z_g hd f R ((y : ℂ) - I * ((d : ℂ) / 2))‖ =
      sphereArea d / L1norm f * exp ((d : ℝ) * log R) *
        ‖mellin (radialProfile hd f) (-(I * (y : ℂ)))‖ := by
  have hmellin : (d : ℂ) / 2 - I * ((y : ℂ) - I * ((d : ℂ) / 2)) = -(I * (y : ℂ)) := by
    simp [mul_sub, ← mul_assoc, Complex.I_mul_I]
  have hphase : ((((d : ℂ) / 2 + I * ((y : ℂ) - I * ((d : ℂ) / 2))) *
      (log R : ℂ))).re = (d : ℝ) * log R := by
    norm_num
  rw [norm_Z_g hd f, hmellin, hphase,
    abs_of_pos (div_pos (radialSurfaceArea_pos hd) (radialL1Mass_pos f hnonzero))]

/-- Lemma 3.2 of the report: on the bottom edge `Im z = -d/2`, `log |Z(y - iλ)| ≤ h_λ(y)`, the
majorant (14). -/
theorem normalizedRadialMellinStrip_bottom_norm_le_gamma {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0) {ς : ℤˣ}
    (hς : (𝓕 f : TestFunction d) = ((ς : ℤ) : ℂ) • f)
    (hnonzero : f ≠ 0)
    (R : ℝ) (hR : 0 < R) (y : ℝ) (hy : y ≠ 0) :
    ‖Z_g hd f R ((y : ℂ) - I * ((d : ℂ) / 2))‖ ≤ Real.exp
        (((d : ℝ) / 2) * Real.log (π * R ^ 2) + Real.log
            ‖Complex.Gamma (-I * (y : ℂ) / 2)‖ -
          Real.log ‖Complex.Gamma ((d : ℂ) / 2 + I * (y : ℂ) / 2)‖) := by
  have hdual : sphereArea d / L1norm f *
      ‖mellin (radialProfile hd f) ((d : ℂ) + I * (y : ℂ))‖ ≤ 1 := by
    have htop := normalizedRadialMellinStrip_top_norm_le_one hd f hf hnonzero R (-y)
    rw [normalizedRadialMellinStrip_top_norm_eq hd f hnonzero] at htop
    simpa using htop
  have hboundary := radial_fourier_mellin_eigenfunction_boundary_norm hd f hf hzero hς y hy
  rw [show -(I * (y : ℂ)) / 2 = -I * (y : ℂ) / 2 by ring] at hboundary
  set A : ℝ := ‖Complex.Gamma (-I * (y : ℂ) / 2)‖ with hAdef
  set B : ℝ := ‖Complex.Gamma ((d : ℂ) / 2 + I * (y : ℂ) / 2)‖ with hBdef
  have hnum : 0 < A := by
    rw [hAdef]
    refine norm_pos_iff.mpr (Complex.Gamma_ne_zero fun n hn ↦ ?_)
    have him := congrArg Complex.im hn
    norm_num at him
    exact hy (by linarith)
  have hden : 0 < B := by
    rw [hBdef]
    exact norm_pos_iff.mpr
      (Complex.Gamma_ne_zero_of_re_pos (by norm_num; exact Nat.cast_pos.mpr hd))
  calc ‖Z_g hd f R ((y : ℂ) - I * ((d : ℂ) / 2))‖
      = exp ((d : ℝ) * log R) * π ^ ((d : ℝ) / 2) * (A / B) *
          (sphereArea d / L1norm f *
            ‖mellin (radialProfile hd f) ((d : ℂ) + I * (y : ℂ))‖) := by
        rw [norm_Z_g_bottom hd f hnonzero R y, hboundary]
        ring
    _ ≤ exp ((d : ℝ) * log R) * π ^ ((d : ℝ) / 2) * (A / B) * 1 :=
        mul_le_mul_of_nonneg_left hdual
          (mul_nonneg (by positivity) (div_nonneg hnum.le hden.le))
    _ = _ := by
        rw [mul_one]
        exact (radialGammaBoundaryExponent_exp d R A B hR hnum hden).symm

/-- `M g` is bounded on the closed strip `0 ≤ Re s ≤ d`. -/
theorem radialProfile_mellin_uniform_strip_bound {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ (d : ℝ) → ‖mellin (radialProfile hd f) s‖ ≤ C := by
  have hmeas : AEStronglyMeasurable (radialProfile hd f) (volume.restrict (Ioi (0 : ℝ))) :=
    (radialProfile_continuous hd f).aestronglyMeasurable
  have hweight (a : ℝ) (ha : -2 < a) :
      IntegrableOn (fun r : ℝ ↦ r ^ (a - 1) * ‖radialProfile hd f r‖) (Ioi (0 : ℝ)) := by
    simpa using (mellin_convergent_iff_norm (T := Ioi (0 : ℝ)) Subset.rfl measurableSet_Ioi
      hmeas).mp (radialProfile_mellinConvergent hd f hf hzero (a : ℂ) (by simpa using ha))
  have hmajor : IntegrableOn (fun r : ℝ ↦
      (r ^ (-(1 : ℝ)) + r ^ ((d : ℝ) - 1)) * ‖radialProfile hd f r‖) (Ioi (0 : ℝ)) := by
    simpa [Pi.add_apply, add_mul] using! (hweight 0 (by norm_num)).add
      (hweight (d : ℝ) (by linarith [show (0 : ℝ) ≤ (d : ℝ) from Nat.cast_nonneg d]))
  refine ⟨max 0 (∫ r : ℝ in Ioi (0 : ℝ),
    (r ^ (-(1 : ℝ)) + r ^ ((d : ℝ) - 1)) * ‖radialProfile hd f r‖), le_max_left _ _,
    fun s hs hsd ↦ le_max_of_le_right ?_⟩
  refine (norm_integral_le_integral_norm _).trans (integral_mono_ae
    (radialProfile_mellinConvergent hd f hf hzero s (by linarith)).norm hmajor ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr : 0 < r := hr
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hr]
  norm_num
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  by_cases hone : r ≤ 1
  · exact (Real.rpow_le_rpow_of_exponent_ge hr hone (by linarith)).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hr.le _))
  · exact (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hone) (by linarith)).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hr.le _))

/-- Lemma 3.2 of the report: `Z` is bounded on the closed strip `|Im z| ≤ d/2`. -/
theorem normalizedRadialMellinStrip_uniform_bound {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, -((d : ℝ) / 2) ≤ z.im → z.im ≤ (d : ℝ) / 2 →
          ‖Z_g hd f R z‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := radialProfile_mellin_uniform_strip_bound hd f hf hzero
  refine ⟨|sphereArea d / L1norm f| * exp ((d : ℝ) * |log R|) * C,
    mul_nonneg (by positivity) hC, fun z hzlower hzupper ↦ ?_⟩
  have hphase : ((((d : ℂ) / 2 + I * z) * (log R : ℂ))).re ≤ (d : ℝ) * |log R| := by
    norm_num
    calc ((d : ℝ) / 2 - z.im) * log R ≤ ((d : ℝ) / 2 - z.im) * |log R| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)
      _ ≤ (d : ℝ) * |log R| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  rw [norm_Z_g hd f]
  gcongr
  exact hbound _ (by norm_num; linarith) (by norm_num; linarith)

/-- The weighted profile `e^{-a v} φ_g(v)` in terms of the radial profile of `f`. -/
theorem logProfile_weighted_eq {d : ℕ} (hd : 0 < d) (f : TestFunction d) (hreal : IsRealValued f)
    (R a v : ℝ) :
    (exp (-a * v) : ℂ) * (φ_g hd f R v : ℂ) =
      (sphereArea d / L1norm f * R ^ d : ℂ) * (exp (((d : ℝ) - a) * v) : ℂ) *
        radialProfile hd f (R * exp v) := by
  have hvalue : radialProfile hd f (R * exp v) = ((radialProfile hd f (R * exp v)).re : ℂ) :=
    Complex.ext rfl (by simpa using radialProfile_real hd f hreal (R * exp v))
  have hexp := congrArg (fun x : ℝ ↦ (x : ℂ))
    (show exp (-a * v) * (R * exp v) ^ d = R ^ d * exp (((d : ℝ) - a) * v) by
      rw [mul_pow, ← Real.exp_nat_mul, mul_left_comm, ← Real.exp_add]
      congr 2
      ring)
  unfold φ_g
  rw [hvalue]
  simp only [Complex.ofReal_re]
  push_cast at hexp ⊢
  linear_combination ((sphereArea d : ℂ) / (L1norm f : ℂ) *
    ((radialProfile hd f (R * exp v)).re : ℂ)) * hexp

/-- The weighted profile `e^{-a v} φ_g(v)` is a constant multiple of an exponential tilt of the
radial Schwartz profile of `f`. -/
theorem logProfile_weighted_eq_tilt {d : ℕ} (hd : 0 < d) (f : TestFunction d)
    (hreal : IsRealValued f) (R a : ℝ) :
    (fun v : ℝ ↦ (exp (-a * v) : ℂ) * (φ_g hd f R v : ℂ)) =
      fun v : ℝ ↦ (sphereArea d / L1norm f * R ^ d : ℂ) *
        schwartzExponentialTilt (radialSchwartzProfile hd f) ((d : ℝ) - a) R v := by
  funext v
  rw [logProfile_weighted_eq hd f hreal R a v]
  simp only [schwartzExponentialTilt, radialSchwartzProfile_apply]
  ring

theorem logProfile_weighted_integrable {d : ℕ} (hd : 0 < d) (f : TestFunction d)
    (hf : IsRadial f) (hreal : IsRealValued f) (hzero : f (0 : Euclidean d) = 0)
    {R : ℝ} (hR : 0 < R) {a : ℝ} (ha : a < (d : ℝ) + 2) :
    Integrable fun v : ℝ ↦ (exp (-a * v) : ℂ) * (φ_g hd f R v : ℂ) := by
  have hconv : ∀ κ : ℝ, -2 < κ → MellinConvergent (radialProfile hd f) (κ : ℂ) :=
    fun κ hκ ↦ radialProfile_mellinConvergent hd f hf hzero _ (by simpa using hκ)
  refine ((integrable_exp_tilt_of_mellinConvergent hR
    (hconv ((d : ℝ) - a) (by linarith))).const_mul
      (sphereArea d / L1norm f * R ^ d : ℂ)).congr (.of_forall fun v ↦ ?_)
  simp only [logProfile_weighted_eq hd f hreal R a v]
  ring

theorem logProfile_weighted_fourier_integrable {d : ℕ} (hd : 0 < d) (f : TestFunction d)
    (hreal : IsRealValued f) {R : ℝ} (hR : 0 < R) {a : ℝ} (ha : a < (d : ℝ)) :
    Integrable (𝓕 (fun v : ℝ ↦ (exp (-a * v) : ℂ) * (φ_g hd f R v : ℂ)) : ℝ → ℂ) := by
  rw [logProfile_weighted_eq_tilt hd f hreal R a, fourier_const_mul]
  exact (schwartzExponentialTilt_fourier_integrable _ (by linarith : (0 : ℝ) < (d : ℝ) - a)
    hR).const_mul _

private theorem ofReal_pow_mul_cpow_neg {R : ℝ} (hR : 0 < R) {d : ℕ} {a t : ℝ} {s : ℂ}
    (hs : s = ((d : ℂ) - a) - I * (t : ℂ)) :
    (R : ℂ) ^ d * (R : ℂ) ^ (-s) = Complex.exp (((a : ℂ) + I * (t : ℂ)) * (log R : ℂ)) := by
  have hRcomplex : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  rw [← Complex.cpow_natCast (R : ℂ) d,
    ← Complex.cpow_add _ _ hRcomplex, Complex.cpow_def_of_ne_zero hRcomplex,
    ← Complex.ofReal_log hR.le]
  congr 1
  rw [hs]
  ring

/-- Lemma 3.6 of the report: on the horizontal line `Im z = λ - a`, `Z` is the Fourier transform
of the weighted profile `v ↦ e^{-a v} φ(v)`. -/
theorem normalizedRadialMellinStrip_shifted_eq_fourier {d : ℕ} (hd : 0 < d) (f : TestFunction d)
    (hreal : IsRealValued f) (R : ℝ) (hR : 0 < R) (a t : ℝ) :
    Z_g hd f R ((t : ℂ) + I * ((d : ℂ) / 2 - a)) =
      (𝓕 (fun v : ℝ ↦ (exp (-a * v) : ℂ) * (φ_g hd f R v : ℂ)) : ℝ → ℂ) (t / (2 * π)) := by
  set s : ℂ := ((d : ℂ) - a) - I * (t : ℂ) with hs
  set c : ℂ := (sphereArea d / L1norm f * R ^ d : ℂ) with hc
  set g : ℝ → ℂ := fun u ↦ exp (-((d : ℝ) - a) * u) • radialProfile hd f (R * exp (-u)) with hg
  have hweight : (fun v : ℝ ↦ (exp (-a * v) : ℂ) * (φ_g hd f R v : ℂ)) = fun v ↦ c * g (-v) := by
    funext v
    rw [logProfile_weighted_eq hd f hreal R a v, hg, hc]
    simp [Complex.real_smul, mul_neg]
    ring_nf
  have hmellin : mellin (fun r : ℝ ↦ radialProfile hd f (R * r)) s =
      (𝓕 g : ℝ → ℂ) (-(t / (2 * π))) := by
    simpa [hs, hg, neg_div] using
      mellin_eq_fourier (fun r : ℝ ↦ radialProfile hd f (R * r)) (s := s)
  have hfourier : (𝓕 (fun v : ℝ ↦ (exp (-a * v) : ℂ) * (φ_g hd f R v : ℂ)) : ℝ → ℂ)
      (t / (2 * π)) = c * mellin (fun r : ℝ ↦ radialProfile hd f (R * r)) s := by
    rw [hweight, fourier_const_mul, hmellin, ← Real.fourierInv_eq_fourier_neg,
      ← Real.fourierInv_eq_fourier_comp_neg]
  have hpower := ofReal_pow_mul_cpow_neg hR hs
  have hscale : c * mellin (fun r : ℝ ↦ radialProfile hd f (R * r)) s =
      (sphereArea d / L1norm f : ℝ) *
        Complex.exp (((a : ℂ) + I * (t : ℂ)) * (log R : ℂ)) * mellin (radialProfile hd f) s := by
    rw [mellin_comp_mul_left (radialProfile hd f) s hR, hc]
    simp only [smul_eq_mul]
    push_cast
    linear_combination ((sphereArea d : ℂ) / (L1norm f : ℂ) *
      mellin (radialProfile hd f) s) * hpower
  have harg : (d : ℂ) / 2 - I * ((t : ℂ) + I * ((d : ℂ) / 2 - a)) = s := by
    rw [hs]
    simp [mul_add, ← mul_assoc, Complex.I_mul_I]
    ring
  have hphase : (d : ℂ) / 2 + I * ((t : ℂ) + I * ((d : ℂ) / 2 - a)) =
      (a : ℂ) + I * (t : ℂ) := by
    simp [mul_add, ← mul_assoc, Complex.I_mul_I]
    ring
  unfold Z_g X_f
  rw [harg, hphase]
  exact hscale.symm.trans hfourier.symm

/-- Lemma 3.6 of the report: `Z` restricted to a horizontal line of the strip is integrable. -/
theorem normalizedRadialMellinStrip_shifted_integrable
    {d : ℕ} (hd : 0 < d) (f : TestFunction d)
    (hreal : IsRealValued f)
    {R : ℝ} (hR : 0 < R) {a : ℝ}
    (ha : a < (d : ℝ)) :
    Integrable (fun t : ℝ ↦
      Z_g hd f R ((t : ℂ) + I *
          ((d : ℂ) / 2 - a))) := by
  have hscale : ((2 * π)⁻¹ : ℝ) ≠ 0 := inv_ne_zero (mul_ne_zero (by norm_num) pi_ne_zero)
  refine ((logProfile_weighted_fourier_integrable hd f hreal hR ha).comp_mul_right'
    hscale).congr (.of_forall fun t ↦ ?_)
  simpa [div_eq_mul_inv] using (normalizedRadialMellinStrip_shifted_eq_fourier hd f hreal R hR
    a t).symm

/-- Lemma 3.6 of the report: Fourier inversion recovers `φ` from the values of `Z` on the
shifted line `Im z = λ - a`. -/
theorem normalizedRadialMellinStrip_shifted_fourier_inversion
    {d : ℕ} (hd : 0 < d) (f : TestFunction d)
    (hf : IsRadial f) (hreal : IsRealValued f)
    (hzero : f (0 : Euclidean d) = 0)
    {R : ℝ} (hR : 0 < R) {a : ℝ}
    (ha : a < (d : ℝ)) (v : ℝ) :
    (φ_g hd f R v : ℂ) = (Real.exp (a * v) : ℂ) * ((𝓕⁻ (fun ξ : ℝ ↦
          Z_g hd f R ((2 * π * ξ : ℂ) + I *
                ((d : ℂ) / 2 - a))) :
            ℝ → ℂ) v) := by
  have hW : Integrable fun u : ℝ ↦ (exp (-a * u) : ℂ) * (φ_g hd f R u : ℂ) :=
    logProfile_weighted_integrable hd f hf hreal hzero hR (by linarith)
  have hcontinuous : Continuous fun u : ℝ ↦ (exp (-a * u) : ℂ) * (φ_g hd f R u : ℂ) := by
    rw [logProfile_weighted_eq_tilt hd f hreal R a]
    exact (schwartzExponentialTilt_differentiable _ _ _).continuous.const_mul _
  have hfrequency : (fun ξ : ℝ ↦ Z_g hd f R ((2 * π * ξ : ℂ) +
      I * ((d : ℂ) / 2 - a))) =
      (𝓕 (fun u : ℝ ↦ (exp (-a * u) : ℂ) * (φ_g hd f R u : ℂ)) : ℝ → ℂ) := by
    funext ξ
    have h := normalizedRadialMellinStrip_shifted_eq_fourier hd f hreal R hR a (2 * π * ξ)
    rw [show 2 * π * ξ / (2 * π) = ξ by field_simp] at h
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat] at h
    exact h
  rw [hfrequency, hW.fourierInv_fourier_eq (logProfile_weighted_fourier_integrable hd f hreal hR ha)
    hcontinuous.continuousAt, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
    show a * v + -a * v = 0 by ring, Real.exp_zero]
  norm_num

end

end CohnElkies
