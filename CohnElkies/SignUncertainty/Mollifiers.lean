import CohnElkies.SignUncertainty.SchwartzFamily
import CohnElkies.SignUncertainty.L1Approximation
import CohnElkies.Admissible.Nonempty

/-! # Gaussian kernels and bump mollifiers (report §2.1)

The Gaussian pair `κ_n(x) = (n+1)^d e^{-π (n+1)² ‖x‖²}`, `η_n(x) = e^{-π ‖x‖²/(n+1)²}` of report
§2.1 (with `𝓕 κ_n = η_n`, `𝓕 η_n = κ_n`, `∫ κ_n = 1`, `0 ≤ η_n ≤ 1`, `η_n → 1`), as plain functions,
and the compactly supported bump mollifiers `φ_n(x) = (n+1)^d φ((n+1) x)` (`φ` the normalized flat
bump of `CohnElkies.bump`) as test functions, with `∫ φ_n = 1`, `|𝓕 φ_n| ≤ 1`, `𝓕 φ_n → 1`.

Design note: the report mollifies with the Gaussian `κ_n` itself. We use the compactly supported
`φ_n` for the convolution step (so that `q_n = (η_n g) ⋆ φ_n` is a test function by
`schwartzConvolution`) and keep the Gaussians `κ_n`, `η_n` for the Fourier-side computation
`𝓕 q_n = ς (g ⋆ κ_n) 𝓕 φ_n`; this avoids building the Gaussian as a Schwartz map. -/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform Topology Convolution RealInnerProductSpace

variable {d : ℕ}

/-! ### Gaussians -/

/-- The Gaussian `G_b(x) = e^{-π b ‖x‖²}`. -/
def gaussianReal (b : ℝ) (x : Euclidean d) : ℝ := Real.exp (-(π * b * ‖x‖ ^ 2))

theorem gaussianReal_pos (b : ℝ) (x : Euclidean d) : 0 < gaussianReal b x := Real.exp_pos _

theorem gaussianReal_le_one {b : ℝ} (hb : 0 ≤ b) (x : Euclidean d) : gaussianReal b x ≤ 1 :=
  Real.exp_le_one_iff.2 (neg_nonpos.2 (by positivity))

theorem continuous_gaussianReal (b : ℝ) : Continuous (gaussianReal (d := d) b) := by
  unfold gaussianReal
  fun_prop

@[simp] theorem gaussianReal_zero (b : ℝ) : gaussianReal b (0 : Euclidean d) = 1 := by
  simp [gaussianReal]

theorem gaussianReal_eq_of_norm_eq (b : ℝ) : IsRadial (gaussianReal (d := d) b) :=
  fun _ _ h ↦ by simp [gaussianReal, h]

theorem gaussianReal_neg (b : ℝ) (x : Euclidean d) : gaussianReal b (-x) = gaussianReal b x :=
  gaussianReal_eq_of_norm_eq b _ _ (norm_neg x)

theorem gaussianReal_smul (b c : ℝ) (x : Euclidean d) :
    gaussianReal b (c • x) = gaussianReal (b * c ^ 2) x := by
  simp only [gaussianReal, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring_nf

theorem ofReal_gaussianReal (b : ℝ) (x : Euclidean d) :
    (gaussianReal b x : ℂ) = Complex.exp (-(π * b : ℂ) * ‖x‖ ^ 2) := by
  rw [gaussianReal, Complex.ofReal_exp]
  push_cast
  congr 1
  ring

theorem integrable_gaussianReal {b : ℝ} (hb : 0 < b) : Integrable (gaussianReal (d := d) b) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Euclidean d)
    (b := (π * b : ℂ)) (by simpa using mul_pos Real.pi_pos hb) 0 0
  simp only [zero_mul, add_zero] at h
  have h2 : (fun v : Euclidean d ↦ Complex.exp (-(π * b : ℂ) * ‖v‖ ^ 2)) =
      fun v ↦ (gaussianReal b v : ℂ) := funext fun v ↦ (ofReal_gaussianReal b v).symm
  rw [h2] at h
  simpa using h.re

theorem integrable_ofReal_gaussianReal {b : ℝ} (hb : 0 < b) :
    Integrable fun x : Euclidean d ↦ (gaussianReal b x : ℂ) :=
  (integrable_gaussianReal hb).ofReal

theorem rpow_sq_half {x : ℝ} (hx : 0 ≤ x) (d : ℕ) : (x ^ 2) ^ (d / 2 : ℝ) = x ^ d := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx, Nat.cast_ofNat,
    show (2 : ℝ) * (d / 2 : ℝ) = d by ring, Real.rpow_natCast]

/-- Gaussian duality: `𝓕 G_b = b^{-d/2} G_{1/b}` (Mathlib's
`fourier_gaussian_innerProductSpace`). -/
theorem fourier_gaussianReal {b : ℝ} (hb : 0 < b) (w : Euclidean d) :
    𝓕 (fun x ↦ (gaussianReal b x : ℂ)) w = ((b ^ (d / 2 : ℝ))⁻¹ : ℝ) * gaussianReal b⁻¹ w := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hb0 : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb.ne'
  have hb' : 0 < (π * b : ℂ).re := by simpa using mul_pos Real.pi_pos hb
  have h := fourier_gaussian_innerProductSpace (V := Euclidean d) hb' w
  simp only [← ofReal_gaussianReal] at h
  have e1 : (↑π / (↑π * ↑b) : ℂ) ^ ((d : ℂ) / 2) = ((b ^ (d / 2 : ℝ))⁻¹ : ℝ) := by
    rw [← Real.inv_rpow hb.le, Complex.ofReal_cpow (by positivity), Complex.ofReal_inv]
    push_cast
    congr 1
    field_simp
  have e2 : Complex.exp (-(π : ℂ) ^ 2 * (‖w‖ : ℂ) ^ 2 / (π * b)) = gaussianReal b⁻¹ w := by
    rw [ofReal_gaussianReal]
    congr 1
    push_cast
    field_simp
  rw [h, finrank_euclideanSpace_fin, e1, e2]

theorem fourier_const_mul_apply (c : ℂ) (f : Euclidean d → ℂ) (w : Euclidean d) :
    𝓕 (fun x ↦ c * f x) w = c * 𝓕 f w := by
  rw [Real.fourier_eq', Real.fourier_eq', ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  simp only [smul_eq_mul]
  ring

theorem fourier_zero_eq_integral (f : Euclidean d → ℂ) : 𝓕 f 0 = ∫ x, f x := by
  simp [Real.fourier_eq']

theorem integral_ofReal_gaussianReal_one : ∫ x : Euclidean d, (gaussianReal 1 x : ℂ) = 1 := by
  have h := fourier_gaussianReal (d := d) one_pos 0
  rw [fourier_zero_eq_integral] at h
  simpa using h

/-- `κ_n(x) = (n+1)^d e^{-π (n+1)² ‖x‖²}`, the Gaussian approximate identity of report §2.1. -/
def gaussianKernel (n : ℕ) (x : Euclidean d) : ℝ :=
  (n + 1 : ℝ) ^ d * gaussianReal ((n + 1 : ℝ) ^ 2) x

/-- `η_n(x) = e^{-π ‖x‖²/(n+1)²}`, the Gaussian cutoff of report §2.1. -/
def gaussianCutoff (n : ℕ) (x : Euclidean d) : ℝ := gaussianReal (((n + 1 : ℝ) ^ 2)⁻¹) x

theorem gaussianKernel_eq_scaledKernel (n : ℕ) :
    (fun x : Euclidean d ↦ (gaussianKernel n x : ℂ)) =
      scaledKernel (fun x ↦ (gaussianReal 1 x : ℂ)) (n + 1) := by
  funext x
  simp [gaussianKernel, scaledKernel, gaussianReal_smul]

theorem continuous_gaussianKernel (n : ℕ) : Continuous (gaussianKernel (d := d) n) :=
  continuous_const.mul (continuous_gaussianReal _)

theorem continuous_gaussianCutoff (n : ℕ) : Continuous (gaussianCutoff (d := d) n) :=
  continuous_gaussianReal _

theorem gaussianKernel_nonneg (n : ℕ) (x : Euclidean d) : 0 ≤ gaussianKernel n x :=
  mul_nonneg (by positivity) (gaussianReal_pos _ _).le

theorem gaussianKernel_le (n : ℕ) (x : Euclidean d) : gaussianKernel n x ≤ (n + 1 : ℝ) ^ d :=
  mul_le_of_le_one_right (by positivity) (gaussianReal_le_one (by positivity) x)

theorem gaussianKernel_neg (n : ℕ) (x : Euclidean d) :
    gaussianKernel n (-x) = gaussianKernel n x := by
  simp [gaussianKernel, gaussianReal_neg]

theorem gaussianCutoff_nonneg (n : ℕ) (x : Euclidean d) : 0 ≤ gaussianCutoff n x :=
  (gaussianReal_pos _ _).le

theorem gaussianCutoff_le_one (n : ℕ) (x : Euclidean d) : gaussianCutoff n x ≤ 1 :=
  gaussianReal_le_one (by positivity) x

theorem gaussianCutoff_eq_of_norm_eq (n : ℕ) : IsRadial (gaussianCutoff (d := d) n) :=
  fun x y h ↦ gaussianReal_eq_of_norm_eq _ x y h

theorem integrable_gaussianKernel (n : ℕ) : Integrable (gaussianKernel (d := d) n) :=
  (integrable_gaussianReal (by positivity)).const_mul _

/-- `η_n → 1` pointwise. -/
theorem tendsto_gaussianCutoff (x : Euclidean d) :
    Tendsto (fun n ↦ gaussianCutoff n x) atTop (𝓝 1) := by
  have h0 : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have h1 : Tendsto (fun n : ℕ ↦ (((n + 1 : ℝ) ^ 2)⁻¹ : ℝ)) atTop (𝓝 0) := by
    simpa [inv_pow] using h0.pow 2
  have h2 : Tendsto (fun n : ℕ ↦ -(π * (((n + 1 : ℝ) ^ 2)⁻¹) * ‖x‖ ^ 2)) atTop (𝓝 0) := by
    simpa using ((h1.const_mul π).mul_const (‖x‖ ^ 2)).neg
  simpa [gaussianCutoff, gaussianReal, Function.comp_def] using
    (Real.continuous_exp.tendsto 0).comp h2

/-- `𝓕 κ_n = η_n`. -/
theorem fourier_gaussianKernel (n : ℕ) (w : Euclidean d) :
    𝓕 (fun x ↦ (gaussianKernel n x : ℂ)) w = gaussianCutoff n w := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have h : (fun x : Euclidean d ↦ (gaussianKernel n x : ℂ)) =
      fun x ↦ ((n : ℂ) + 1) ^ d * (gaussianReal ((n + 1 : ℝ) ^ 2) x : ℂ) := by
    funext x
    simp [gaussianKernel]
  rw [h, fourier_const_mul_apply, fourier_gaussianReal (by positivity), rpow_sq_half hn.le]
  unfold gaussianCutoff
  push_cast
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (Nat.cast_add_one_ne_zero n)), one_mul]

/-- `𝓕 η_n = κ_n`. -/
theorem fourier_gaussianCutoff (n : ℕ) (w : Euclidean d) :
    𝓕 (fun x ↦ (gaussianCutoff n x : ℂ)) w = gaussianKernel n w := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  unfold gaussianCutoff gaussianKernel
  rw [fourier_gaussianReal (by positivity), Real.inv_rpow (by positivity), rpow_sq_half hn.le,
    inv_inv, inv_inv]
  push_cast
  ring

/-- `∫ κ_n = 1`. -/
theorem integral_gaussianKernel (n : ℕ) : ∫ x : Euclidean d, (gaussianKernel n x : ℂ) = 1 := by
  have h := fourier_gaussianKernel (d := d) n 0
  rw [fourier_zero_eq_integral] at h
  simpa [gaussianCutoff] using h

theorem integral_norm_gaussianKernel (n : ℕ) :
    ∫ x : Euclidean d, ‖(gaussianKernel n x : ℂ)‖ = 1 := by
  have h := integral_gaussianKernel (d := d) n
  rw [integral_complex_ofReal] at h
  simp_rw [Complex.norm_real, Real.norm_of_nonneg (gaussianKernel_nonneg n _)]
  exact_mod_cast h

/-! ### The moment bound for Gaussian cutoffs -/

/-- `(1 + r)^k e^{-c r²} ≤ e^{k²/(4c)}` for `r ≥ 0`, `c > 0`. -/
theorem pow_mul_exp_neg_sq_le {c : ℝ} (hc : 0 < c) (k : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (1 + r) ^ k * Real.exp (-(c * r ^ 2)) ≤ Real.exp ((k : ℝ) ^ 2 / (4 * c)) := by
  calc (1 + r) ^ k * Real.exp (-(c * r ^ 2))
      ≤ Real.exp r ^ k * Real.exp (-(c * r ^ 2)) := by
        gcongr
        simpa [add_comm] using Real.add_one_le_exp r
    _ = Real.exp (k * r - c * r ^ 2) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        ring_nf
    _ ≤ Real.exp ((k : ℝ) ^ 2 / (4 * c)) := by
        rw [Real.exp_le_exp, le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg ((k : ℝ) - 2 * c * r)]

/-- The Gaussian cutoff `η_n` beats every polynomial: `(1 + ‖x‖)^k η_n(x)` is bounded. -/
theorem pow_mul_gaussianCutoff_le (n k : ℕ) (x : Euclidean d) :
    (1 + ‖x‖) ^ k * gaussianCutoff n x ≤
      Real.exp ((k : ℝ) ^ 2 / (4 * (π * ((n + 1 : ℝ) ^ 2)⁻¹))) :=
  pow_mul_exp_neg_sq_le (by positivity) k (norm_nonneg x)

/-! ### Bump mollifiers -/

/-- The normalized flat bump `φ = bump / ∫ bump` (real-valued; support in the ball of radius
`1/2`, `∫ φ = 1`). -/
def bumpUnitReal (d : ℕ) (x : Euclidean d) : ℝ := (∫ y, bumpReal d y)⁻¹ * bumpReal d x

/-- The normalized flat bump, as a test function. -/
def bumpUnit (d : ℕ) : TestFunction d := (((∫ y, bumpReal d y)⁻¹ : ℝ) : ℂ) • bump d

theorem bumpUnit_apply (x : Euclidean d) : bumpUnit d x = (bumpUnitReal d x : ℂ) := by
  simp [bumpUnit, bumpUnitReal, smul_apply]

theorem bumpUnitReal_nonneg (x : Euclidean d) : 0 ≤ bumpUnitReal d x :=
  mul_nonneg (inv_nonneg.2 (integral_bumpReal_pos d).le) (expNegInvGlue.nonneg _)

theorem bumpUnitReal_eq_of_norm_eq : IsRadial (bumpUnitReal d) :=
  fun _ _ h ↦ by simp [bumpUnitReal, bumpReal, h]

theorem integrable_bumpReal (d : ℕ) : Integrable (bumpReal d) := by
  simpa using ((bump d).integrable (μ := volume)).re

theorem integral_bumpUnitReal (d : ℕ) : ∫ x, bumpUnitReal d x = 1 := by
  unfold bumpUnitReal
  rw [integral_const_mul, inv_mul_cancel₀ (integral_bumpReal_pos d).ne']

theorem bumpUnit_real (d : ℕ) : IsRealValued (bumpUnit d) := fun x ↦ by simp [bumpUnit_apply]

theorem bumpUnit_radial (d : ℕ) : IsRadial (bumpUnit d) := fun x y hxy ↦ by
  rw [bumpUnit_apply, bumpUnit_apply, bumpUnitReal_eq_of_norm_eq _ _ hxy]

theorem integral_bumpUnit (d : ℕ) : ∫ x, bumpUnit d x = 1 := by
  simp_rw [bumpUnit_apply]
  rw [integral_complex_ofReal, integral_bumpUnitReal]
  simp

/-- `φ_n(x) = (n+1)^d φ((n+1) x)`, the bump mollifier, as a test function. -/
def bumpKernel (n : ℕ) : TestFunction d :=
  ((n : ℂ) + 1) ^ d • dilate (bumpUnit d) (n + 1 : ℝ) (by positivity)

/-- `φ_n` as a real-valued function. -/
def bumpKernelReal (n : ℕ) (x : Euclidean d) : ℝ :=
  (n + 1 : ℝ) ^ d * bumpUnitReal d ((n + 1 : ℝ) • x)

theorem bumpKernel_apply (n : ℕ) (x : Euclidean d) : bumpKernel n x = (bumpKernelReal n x : ℂ) := by
  simp [bumpKernel, bumpKernelReal, smul_apply, dilate_apply, bumpUnit_apply]

theorem bumpKernelReal_nonneg (n : ℕ) (x : Euclidean d) : 0 ≤ bumpKernelReal n x :=
  mul_nonneg (by positivity) (bumpUnitReal_nonneg _)

theorem bumpKernel_real (n : ℕ) : IsRealValued (bumpKernel (d := d) n) := fun x ↦ by
  simp [bumpKernel_apply]

theorem bumpKernelReal_eq_of_norm_eq (n : ℕ) : IsRadial (bumpKernelReal (d := d) n) :=
  fun _ _ h ↦ congrArg ((n + 1 : ℝ) ^ d * ·) (bumpUnitReal_eq_of_norm_eq _ _ (by
    simp [norm_smul, h]))

theorem bumpKernel_radial (n : ℕ) : IsRadial (bumpKernel (d := d) n) := fun x y hxy ↦ by
  rw [bumpKernel_apply, bumpKernel_apply, bumpKernelReal_eq_of_norm_eq n _ _ hxy]

theorem bumpKernel_eq_scaledKernel (n : ℕ) :
    (bumpKernel n : Euclidean d → ℂ) = scaledKernel (bumpUnit d) (n + 1) := by
  funext x
  simp [bumpKernel_apply, bumpKernelReal, scaledKernel, bumpUnit_apply]

theorem integral_bumpKernel (n : ℕ) : ∫ x, bumpKernel (d := d) n x = 1 := by
  rw [bumpKernel_eq_scaledKernel, integral_scaledKernel _ (Nat.succ_pos n), integral_bumpUnit]

theorem integral_norm_bumpKernel (n : ℕ) : ∫ x, ‖bumpKernel (d := d) n x‖ = 1 := by
  have h := integral_bumpKernel (d := d) n
  simp_rw [bumpKernel_apply] at h ⊢
  rw [integral_complex_ofReal] at h
  simp_rw [Complex.norm_real, Real.norm_of_nonneg (bumpKernelReal_nonneg n _)]
  exact_mod_cast h

/-- `|𝓕 φ_n| ≤ ∫ φ_n = 1`. -/
theorem norm_fourier_bumpKernel_le (n : ℕ) (ξ : Euclidean d) :
    ‖(𝓕 (bumpKernel n) : TestFunction d) ξ‖ ≤ 1 := by
  rw [SchwartzMap.fourier_coe]
  exact (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ ξ).trans
    (le_of_eq (integral_norm_bumpKernel n))

/-- `𝓕 φ_n (ξ) = 𝓕 φ (ξ/(n+1))`. -/
theorem fourier_bumpKernel_apply (n : ℕ) (ξ : Euclidean d) :
    (𝓕 (bumpKernel n) : TestFunction d) ξ =
      (𝓕 (bumpUnit d) : TestFunction d) ((n + 1 : ℝ)⁻¹ • ξ) := by
  have hsmul : (𝓕 (bumpKernel n) : TestFunction d) =
      ((n : ℂ) + 1) ^ d • 𝓕 (dilate (bumpUnit d) (n + 1 : ℝ) (by positivity)) :=
    map_smul _ _ _
  rw [hsmul, smul_apply, fourier_dilate_apply, Complex.real_smul, smul_eq_mul, ← mul_assoc]
  push_cast
  rw [mul_inv_cancel₀ (pow_ne_zero _ (Nat.cast_add_one_ne_zero n)), one_mul]

/-- `𝓕 φ_n → 𝓕 φ (0) = 1` pointwise. -/
theorem tendsto_fourier_bumpKernel (ξ : Euclidean d) :
    Tendsto (fun n ↦ (𝓕 (bumpKernel n) : TestFunction d) ξ) atTop (𝓝 1) := by
  simp_rw [fourier_bumpKernel_apply]
  have h0 : (𝓕 (bumpUnit d) : TestFunction d) 0 = 1 := by
    rw [SchwartzMap.fourier_coe, fourier_zero_eq_integral, integral_bumpUnit]
  have h1 : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹ • ξ) atTop (𝓝 0) := by
    simpa using ((tendsto_inv_atTop_zero (𝕜 := ℝ)).comp
      (tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop (R := ℝ)))).smul_const ξ
  rw [← h0]
  exact ((𝓕 (bumpUnit d) : TestFunction d).continuous.tendsto 0).comp h1

end

end CohnElkies
