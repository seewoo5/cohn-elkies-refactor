import CohnElkies.Radial
import CohnElkies.SchwartzTools

/-!
# The `L¹` norm and the logarithmic profile of a radial eigenfunction (report (13))

For a radial eigenfunction `g` on `ℝ^d` with profile `G`, the weighted profile
`φ_g(v) = (S_d/‖g‖₁) R^d e^{d v} G(R e^v)` on the logarithmic scale `r = R e^v` has total mass
`∫ φ_g = 0`, `∫ |φ_g| = 1`, and the mass of `g` inside the ball of radius `R` is the mass of `φ_g`
on `v < 0`.
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter Function MeasureTheory Metric Real Set
open scoped FourierTransform SchwartzMap Topology ENNReal

/-- The `L¹` norm `‖g‖₁ = ∫_{ℝ^d} |g|` of a test function. -/
def L1norm {d : ℕ} (g : TestFunction d) : ℝ := ∫ x : Euclidean d, ‖g x‖

theorem L1norm_nonneg {d : ℕ} (g : TestFunction d) : 0 ≤ L1norm g :=
  integral_nonneg fun _ ↦ norm_nonneg _

theorem radialL1Mass_pos {d : ℕ} (g : TestFunction d) (hg : g ≠ 0) : 0 < L1norm g := by
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hg
  exact integral_pos_of_integrable_nonneg_nonzero g.continuous.norm g.integrable.norm
    (fun _ ↦ norm_nonneg _) (norm_ne_zero_iff.mpr (by simpa using hx))

/-- Polar integration for a radial test function: `∫ F(g(x)) dx = S_d ∫₀^∞ r^{d-1} F(g(r)) dr`
(report §2.2). -/
theorem integral_comp_radialProfile {d : ℕ} (hd : 0 < d) (g : TestFunction d) (hg : IsRadial g)
    (F : ℂ → ℝ) :
    (∫ x : Euclidean d, F (g x)) =
      sphereArea d * ∫ r : ℝ in Ioi 0, r ^ (d - 1) * F (radialProfile hd g r) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  calc (∫ x : Euclidean d, F (g x)) = ∫ x : Euclidean d, F (radialProfile hd g ‖x‖) :=
        integral_congr_ae (.of_forall fun x ↦ by simp only [radialProfile_norm hd g hg])
    _ = _ := by
        simpa [sphereArea, volume_real_unitBall hd, nsmul_eq_mul, finrank_euclideanSpace_fin,
          mul_assoc, smul_eq_mul] using integral_fun_norm_addHaar
          (volume : Measure (Euclidean d)) fun r : ℝ ↦ F (radialProfile hd g r)

/-- Polar integration over a ball: `∫_{‖x‖<R} F(g(x)) dx = S_d ∫₀^R r^{d-1} F(g(r)) dr`. -/
theorem setIntegral_ball_comp_radialProfile {d : ℕ} (hd : 0 < d) (g : TestFunction d)
    (hg : IsRadial g) (F : ℂ → ℝ) (R : ℝ) :
    (∫ x in ball (0 : Euclidean d) R, F (g x)) =
      sphereArea d * ∫ r : ℝ in Ioo 0 R, r ^ (d - 1) * F (radialProfile hd g r) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  calc (∫ x in ball (0 : Euclidean d) R, F (g x))
      = ∫ x : Euclidean d, (Iio R).indicator (fun r : ℝ ↦ F (radialProfile hd g r)) ‖x‖ := by
        rw [← integral_indicator measurableSet_ball]
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        simp only [indicator, mem_ball_zero_iff, mem_Iio, radialProfile_norm hd g hg]
    _ = sphereArea d * ∫ r : ℝ in Ioi 0,
          (Iio R).indicator (fun r : ℝ ↦ r ^ (d - 1) * F (radialProfile hd g r)) r := by
        rw [integral_fun_norm_addHaar volume, finrank_euclideanSpace_fin, volume_real_unitBall hd]
        simp only [sphereArea, nsmul_eq_mul, smul_eq_mul, mul_assoc, indicator_mul_right]
    _ = _ := by rw [setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio]

/-- The normalized logarithmic profile `φ(v) = (S_d/‖g‖₁) (R e^v)^d g(R e^v)` of report (12),
in the logarithmic coordinate `r = R e^v`. -/
def φ_g {d : ℕ} (hd : 0 < d) (g : TestFunction d) (R v : ℝ) : ℝ :=
  sphereArea d / L1norm g * (R * Real.exp v) ^ d *
    (radialProfile hd g (R * Real.exp v)).re

theorem norm_radialProfile_eq_abs_re {d : ℕ} (hd : 0 < d) (g : TestFunction d)
    (hg : IsRealValued g) (r : ℝ) : ‖radialProfile hd g r‖ = |(radialProfile hd g r).re| := by
  conv_lhs => rw [← Complex.re_add_im (radialProfile hd g r), radialProfile_real hd g hg r]
  simp

theorem integrableOn_radialProfile_re_weight {d : ℕ} (hd : 0 < d) (g : TestFunction d)
    (hg : IsRadial g) :
    IntegrableOn (fun r : ℝ ↦ r ^ (d - 1) * (radialProfile hd g r).re) (Ioi 0) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hre : Integrable fun x : Euclidean d ↦ (radialProfile hd g ‖x‖).re :=
    g.integrable.re.congr (.of_forall fun x ↦ by
      change (g x).re = (radialProfile hd g ‖x‖).re
      rw [radialProfile_norm hd g hg])
  simpa [finrank_euclideanSpace_fin, smul_eq_mul] using (integrable_fun_norm_addHaar
    (volume : Measure (Euclidean d)) (f := fun r : ℝ ↦ (radialProfile hd g r).re)).mp hre

/-- Any weight of the shape of `φ_g` integrates to the corresponding polar integral over `ℝ^d`,
divided by `‖g‖₁`. -/
theorem integral_logProfile_weight {d : ℕ} (hd : 0 < d) (g : TestFunction d) (hg : IsRadial g)
    {R : ℝ} (hR : 0 < R) (F : ℂ → ℝ) (ψ : ℝ → ℝ)
    (hψ : ∀ v : ℝ, ψ v = sphereArea d / L1norm g *
      ((R * exp v) * ((R * exp v) ^ (d - 1) * F (radialProfile hd g (R * exp v))))) :
    (∫ v : ℝ, ψ v) = (∫ x : Euclidean d, F (g x)) / L1norm g := by
  have h := integral_scaled_exp_change_Ioi hR fun r : ℝ ↦ r ^ (d - 1) * F (radialProfile hd g r)
  simp only [smul_eq_mul] at h
  rw [integral_congr_ae (.of_forall hψ), integral_const_mul, ← h,
    integral_comp_radialProfile hd g hg F]
  ring

theorem integrable_logProfile {d : ℕ} (hd : 0 < d) (g : TestFunction d) (hg : IsRadial g)
    {R : ℝ} (hR : 0 < R) : Integrable (φ_g hd g R) := by
  refine (((integrable_scaled_exp_change_Ioi hR _).mp
    (integrableOn_radialProfile_re_weight hd g hg)).const_mul
      (sphereArea d / L1norm g)).congr (.of_forall fun v ↦ ?_)
  simp only [φ_g, smul_eq_mul]
  rw [← mul_pow_sub_one hd.ne' (R * exp v)]
  ring

/-- Report (13): `∫ φ_g = (∫ Re g) / ‖g‖₁`. -/
theorem integral_logProfile {d : ℕ} (hd : 0 < d) (g : TestFunction d) (hg : IsRadial g)
    {R : ℝ} (hR : 0 < R) :
    (∫ v : ℝ, φ_g hd g R v) = (∫ x : Euclidean d, (g x).re) / L1norm g :=
  integral_logProfile_weight hd g hg hR Complex.re _ fun v ↦ by
    simp only [φ_g]
    rw [← mul_pow_sub_one hd.ne' (R * exp v)]
    ring

theorem abs_logProfile {d : ℕ} (hd : 0 < d) (g : TestFunction d) (hreal : IsRealValued g)
    {R : ℝ} (hR : 0 < R) (v : ℝ) :
    |φ_g hd g R v| = sphereArea d / L1norm g *
      ((R * exp v) * ((R * exp v) ^ (d - 1) * ‖radialProfile hd g (R * exp v)‖)) := by
  simp only [φ_g, norm_radialProfile_eq_abs_re hd g hreal, abs_mul, abs_pow]
  rw [abs_of_nonneg (div_nonneg (radialSurfaceArea_pos hd).le (L1norm_nonneg g)), abs_of_pos hR,
    abs_of_pos (exp_pos v), ← mul_pow_sub_one hd.ne' (R * exp v)]
  ring

/-- Report (13): `φ_g` has total variation `1`. -/
theorem integral_abs_logProfile {d : ℕ} (hd : 0 < d) (g : TestFunction d) (hradial : IsRadial g)
    (hreal : IsRealValued g) (hnonzero : g ≠ 0) {R : ℝ} (hR : 0 < R) :
    (∫ v : ℝ, |φ_g hd g R v|) = 1 := by
  rw [integral_logProfile_weight hd g hradial hR (‖·‖) _ (abs_logProfile hd g hreal hR)]
  exact div_self (radialL1Mass_pos g hnonzero).ne'

/-- Report (13): the mass of `φ_g` on `(-∞, 0]` is the mass of `g` in the ball of radius `R`,
relative to `‖g‖₁`. -/
theorem setIntegral_Iic_abs_logProfile {d : ℕ} (hd : 0 < d) (g : TestFunction d)
    (hradial : IsRadial g) (hreal : IsRealValued g) {R : ℝ} (hR : 0 < R) :
    (∫ v in Iic (0 : ℝ), |φ_g hd g R v|) =
      (∫ x in ball (0 : Euclidean d) R, ‖g x‖) / L1norm g := by
  rw [integral_Iic_eq_integral_Iio,
    setIntegral_congr_fun measurableSet_Iio fun v _ ↦ abs_logProfile hd g hreal hR v,
    integral_const_mul, setIntegral_ball_comp_radialProfile hd g hradial (‖·‖) R,
    setIntegral_Ioo_scaled_exp_change hR]
  simp only [smul_eq_mul]
  ring

/-- A test function with `𝓕 g (0) = 0` has `∫ Re g = 0`. -/
theorem integral_re_eq_zero_of_fourier_zero {d : ℕ} (g : TestFunction d)
    (hzero : (𝓕 g : TestFunction d) 0 = 0) : (∫ x : Euclidean d, (g x).re) = 0 := by
  have hfourier : ((𝓕 g : TestFunction d) 0) = ∫ x : Euclidean d, g x := by
    change (𝓕 (g : Euclidean d → ℂ)) 0 = _
    rw [Real.fourier_eq']
    simp
  have hre : (∫ x : Euclidean d, (g x).re) = (∫ x : Euclidean d, g x).re := integral_re g.integrable
  rw [hre, ← hfourier, hzero, Complex.zero_re]

theorem integral_logProfile_eq_zero {d : ℕ} (hd : 0 < d) (g : TestFunction d)
    (hradial : IsRadial g) (hzero : (𝓕 g : TestFunction d) 0 = 0) {R : ℝ} (hR : 0 < R) :
    (∫ v : ℝ, φ_g hd g R v) = 0 := by
  rw [integral_logProfile hd g hradial hR, integral_re_eq_zero_of_fourier_zero g hzero, zero_div]

theorem logProfile_nonneg_of_exterior {d : ℕ} (hd : 0 < d) (g : TestFunction d) (hnonzero : g ≠ 0)
    {R : ℝ} (hR : 0 < R) (houtside : ∀ x : Euclidean d, R ≤ ‖x‖ → 0 ≤ (g x).re) {v : ℝ}
    (hv : 0 ≤ v) : 0 ≤ φ_g hd g R v := by
  have hradius : 0 < R * exp v := mul_pos hR (exp_pos v)
  have hpoint : R ≤ ‖(R * exp v) • radialUnitDirection hd‖ := by
    rw [norm_smul, norm_radialUnitDirection hd, mul_one, Real.norm_eq_abs, abs_of_pos hradius]
    exact le_mul_of_one_le_right hR.le (one_le_exp hv)
  unfold φ_g
  exact mul_nonneg (mul_nonneg (div_pos (radialSurfaceArea_pos hd)
    (radialL1Mass_pos g hnonzero)).le (pow_nonneg hradius.le _)) (houtside _ hpoint)

/-! ### The normalized profile of a radial eigenfunction (report (13)) -/

namespace RadialEigenfunction

variable {d : ℕ} {ς : ℤˣ}

theorem L1norm_pos (g : RadialEigenfunction d ς) : 0 < L1norm g.toFun :=
  radialL1Mass_pos g.toFun g.ne_zero

theorem integrable_logProfile (hd : 0 < d) (g : RadialEigenfunction d ς) {R : ℝ} (hR : 0 < R) :
    Integrable (φ_g hd g.toFun R) :=
  CohnElkies.integrable_logProfile hd g.toFun g.radial hR

/-- Report (13): the profile `φ` of a radial eigenfunction has mean `0`. -/
theorem integral_logProfile (hd : 0 < d) (g : RadialEigenfunction d ς) {R : ℝ} (hR : 0 < R) :
    (∫ v : ℝ, φ_g hd g.toFun R v) = 0 :=
  integral_logProfile_eq_zero hd g.toFun g.radial g.fourier_zero hR

/-- Report (13): the profile `φ` of a radial eigenfunction has total variation `1`. -/
theorem integral_abs_logProfile (hd : 0 < d) (g : RadialEigenfunction d ς) {R : ℝ}
    (hR : 0 < R) : (∫ v : ℝ, |φ_g hd g.toFun R v|) = 1 :=
  CohnElkies.integral_abs_logProfile hd g.toFun g.radial g.real g.ne_zero hR

/-- Report (13): `∫_{v ≤ 0} |φ| = ‖g‖₁⁻¹ ∫_{‖x‖ < R} |g|`. -/
theorem setIntegral_Iic_abs_logProfile (hd : 0 < d) (g : RadialEigenfunction d ς) {R : ℝ}
    (hR : 0 < R) : (∫ v in Iic (0 : ℝ), |φ_g hd g.toFun R v|) =
      (∫ x in ball (0 : Euclidean d) R, ‖g.toFun x‖) / L1norm g.toFun :=
  CohnElkies.setIntegral_Iic_abs_logProfile hd g.toFun g.radial g.real hR

end RadialEigenfunction

end

end CohnElkies
