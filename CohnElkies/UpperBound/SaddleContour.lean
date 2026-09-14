import CohnElkies.UpperBound.SmallRadius
import CohnElkies.UpperBound.Schwartz

/-!
# The Mellin integral on the saddle contour and its Gaussian approximation (report §4.3, (71))

The envelope of `M_P` on the contour `z = λ(1 + u) - iλT`, the rewriting of `f_P(r)` as an
integral over the contour with the centered integrand `e^{L(T)} P(...)`, the Gaussian kernel of
variance `V_u`, the positivity of the variance on the first branch, and the integrability of the
centered integrands; the sign of `f_P` at the saddle point follows once the Gaussian error is small
(`mellinProfile_exp_re_mul_pos_of_gaussian_error`).
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace SchwartzMap Topology
open Real

/-! ### The contour `z = λ(1 + u) - iλT` and its envelope -/

/-- The modulus of `E_λ` at `T = 0` on the contour `z = λ(1+u) - iλT`, report §4.3. -/
def saddleSourceContourEnvelopeScale (ε ℓ u : ℝ) : ℝ :=
  exp (-(ℓ * u) * log π / 2) * Gamma (ℓ * (1 + u) / 2) * exp (ℓ * h_εI ε u)

theorem saddleSourceContourEnvelopeScale_pos {ε ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : -1 < u) :
    0 < saddleSourceContourEnvelopeScale ε ℓ u := by
  have hη : 0 < 1 + u := by linarith
  unfold saddleSourceContourEnvelopeScale
  exact mul_pos (mul_pos (exp_pos _) (Gamma_pos_of_pos (by positivity))) (exp_pos _)

theorem saddleSourceContour_mellinEnvelope_norm {ε ℓ u : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (hu : -1 < u) (horder : a₀ε ε ≤ Aε ε) (T : ℝ) :
    ‖mellinEnvelope ε ℓ (z_contour ℓ u T)‖ =
      saddleSourceContourEnvelopeScale ε ℓ u * exp (-saddleSourceContourDamping ε ℓ u T) := by
  have hπ : ‖Complex.exp (((ℓ : ℂ) - z_contour ℓ u T) * (log π : ℂ) / 2)‖ =
      exp (-(ℓ * u) * log π / 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [z_contour, Complex.mul_re]
    ring
  have hΓ : ‖Complex.Gamma (z_contour ℓ u T / 2)‖ =
      Gamma (ℓ * (1 + u) / 2) * exp (-D_γ ℓ (1 + u) T) := by
    rw [saddleSourceMellinContour_gammaArgument]
    have h := upperGammaShifted_modulus_eq_exp_neg_damping (η := 1 + u) hℓ (by linarith) T
    push_cast at h
    exact h
  have hshell : ‖Complex.exp ((ℓ : ℂ) * h_ε ε (I * (z_contour ℓ u T - (ℓ : ℂ)) / (ℓ : ℂ)))‖ =
      exp (ℓ * h_εI ε u) * exp (-(D_B ε ℓ (u - 1) T - D_s ε ℓ (u - 1) T)) := by
    rw [saddleSourceMellinContour_shellArgument hℓ]
    exact norm_saddleShellExponential_eq_exp_neg_damping hε horder ℓ T u
  have hexp : exp (-D_γ ℓ (1 + u) T) * exp (-(D_B ε ℓ (u - 1) T - D_s ε ℓ (u - 1) T)) =
      exp (-saddleSourceContourDamping ε ℓ u T) := by
    rw [← exp_add]
    congr 1
    unfold saddleSourceContourDamping
    ring
  unfold mellinEnvelope
  rw [norm_mul, norm_mul, hπ, hΓ, hshell]
  unfold saddleSourceContourEnvelopeScale
  rw [← hexp]
  ring

/-- `E_λ` on the contour, normalized to modulus `e^{-D(u,T)}`, report (46). -/
def saddleSourceNormalizedEnvelope (ε ℓ u T : ℝ) : ℂ :=
  mellinEnvelope ε ℓ (z_contour ℓ u T) / (saddleSourceContourEnvelopeScale ε ℓ u : ℂ)

theorem saddleSourceNormalizedEnvelope_norm {ε ℓ u : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : a₀ε ε ≤ Aε ε) (T : ℝ) :
    ‖saddleSourceNormalizedEnvelope ε ℓ u T‖ = exp (-saddleSourceContourDamping ε ℓ u T) := by
  have hscale := saddleSourceContourEnvelopeScale_pos (ε := ε) hℓ hu
  unfold saddleSourceNormalizedEnvelope
  rw [norm_div, saddleSourceContour_mellinEnvelope_norm hε hℓ hu horder T,
    Complex.norm_of_nonneg hscale.le, mul_div_cancel_left₀ _ hscale.ne']

/-- `e^{L_u(v, T)}`: the centered phase of report (46). -/
def expL (ε ℓ u v T : ℝ) : ℂ :=
  saddleSourceNormalizedEnvelope ε ℓ u T * Complex.exp (I * (ℓ * T * v : ℂ))

theorem saddleSourceCenteredEnvelope_norm {ε ℓ u : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : a₀ε ε ≤ Aε ε) (v T : ℝ) :
    ‖expL ε ℓ u v T‖ = exp (-saddleSourceContourDamping ε ℓ u T) := by
  unfold expL
  rw [norm_mul, saddleSourceNormalizedEnvelope_norm hε hℓ hu horder T,
    show ‖Complex.exp (I * (ℓ * T * v : ℂ))‖ = 1 by rw [Complex.norm_exp]; simp, mul_one]

/-- The centered integrand `e^{L_u} P(T + iu)` of report (46) for a polynomial factor `P`. -/
def centeredIntegrand (ε ℓ : ℝ) (P : ℂ → ℂ) (u v T : ℝ) : ℂ :=
  expL ε ℓ u v T * P ((T : ℂ) + I * (u : ℂ))

theorem centeredIntegrand_norm {ε ℓ u : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : a₀ε ε ≤ Aε ε) (P : ℂ → ℂ) (v T : ℝ) :
    ‖centeredIntegrand ε ℓ P u v T‖ =
      exp (-saddleSourceContourDamping ε ℓ u T) * ‖P ((T : ℂ) + I * (u : ℂ))‖ := by
  unfold centeredIntegrand
  rw [norm_mul, saddleSourceCenteredEnvelope_norm hε hℓ hu horder]

@[simp] theorem saddleSourceContourDamping_eq_firstBranch (ε ℓ u T : ℝ) :
    saddleSourceContourDamping ε ℓ u T = saddleSourceContourDamping ε ℓ u T := rfl

@[simp] theorem saddleSourceContourDamping_eq_secondBranch (ε ℓ δ T : ℝ) :
    saddleSourceContourDamping ε ℓ (1 + δ) T = D_u ε ℓ δ T := by
  simp [saddleSourceContourDamping, D_u, show 1 + (1 + δ) = 2 + δ from by ring,
    show 1 + δ - 1 = δ from by ring]

/-! ### Rewriting the Mellin integral on the contour -/

theorem saddleSourceMellinContour_integral_change {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ) (F : ℂ → ℂ) :
    (∫ t : ℝ, F (((ℓ * (1 + u) : ℝ) : ℂ) + (t : ℂ) * I)) =
      (ℓ : ℂ) * ∫ T : ℝ, F (z_contour ℓ u T) := by
  have hpt (T : ℝ) : F (z_contour ℓ u T) =
      F (((ℓ * (1 + u) : ℝ) : ℂ) + (((-ℓ) * T : ℝ) : ℂ) * I) := by
    congr 1
    unfold z_contour
    push_cast
    ring
  have hchange : (∫ T : ℝ, F (z_contour ℓ u T)) =
      (ℓ⁻¹ : ℂ) * ∫ t : ℝ, F (((ℓ * (1 + u) : ℝ) : ℂ) + (t : ℂ) * I) := by
    calc (∫ T : ℝ, F (z_contour ℓ u T))
        = ∫ T : ℝ, F (((ℓ * (1 + u) : ℝ) : ℂ) + (((-ℓ) * T : ℝ) : ℂ) * I) :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = |(-ℓ)⁻¹| • ∫ t : ℝ, F (((ℓ * (1 + u) : ℝ) : ℂ) + (t : ℂ) * I) :=
          Measure.integral_comp_mul_left
            (fun t : ℝ ↦ F (((ℓ * (1 + u) : ℝ) : ℂ) + (t : ℂ) * I)) (-ℓ)
      _ = _ := by
          rw [inv_neg, abs_neg, abs_of_pos (inv_pos.mpr hℓ)]
          simp [Complex.real_smul]
  rw [hchange, ← mul_assoc]
  push_cast
  rw [mul_inv_cancel₀ (by exact_mod_cast hℓ.ne'), one_mul]

/-- Report §4.3: the inverse Mellin integral written on the contour `z = λ(1+u) - iλT`. -/
theorem saddleProfile_eq_sourceContourIntegral {M : ℂ → ℂ} {f : ℝ → ℂ} {ℓ r u : ℝ} (hℓ : 0 < ℓ)
    (hu : -1 < u)
    (hcontour : ∀ a : ℝ, 0 < a → f r = (2 * π : ℂ)⁻¹ *
      ∫ t : ℝ, saddleMellinInversePower r ((a : ℂ) + (t : ℂ) * I) * M ((a : ℂ) + (t : ℂ) * I)) :
    f r = (ℓ / (2 * π) : ℂ) *
      ∫ T : ℝ, saddleMellinInversePower r (z_contour ℓ u T) * M (z_contour ℓ u T) := by
  have hη : 0 < 1 + u := by linarith
  rw [hcontour (ℓ * (1 + u)) (by positivity), saddleSourceMellinContour_integral_change hℓ u
    fun z ↦ saddleMellinInversePower r z * M z]
  ring

theorem mellinProfile_eq_sourceContourIntegral {ε ℓ r u : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : a₀ε ε ≤ Aε ε) {P : ℂ → ℂ} (hP : IsSaddlePolynomial ε P) (c : ℝ) (hr : 0 < r)
    (hu : -1 < u) :
    mellinProfile ε ℓ P c r = (ℓ / (2 * π) : ℂ) *
      ∫ T : ℝ, saddleMellinInversePower r (z_contour ℓ u T) * mellinData ε ℓ P (z_contour ℓ u T) :=
  saddleProfile_eq_sourceContourIntegral hℓ hu fun _a ha ↦
    mellinProfile_eq_positive_contour hε hℓ horder hP c hr ha

theorem saddleSourceContour_inversePower_exp (ℓ u v T : ℝ) :
    saddleMellinInversePower (exp v) (z_contour ℓ u T) =
      (exp (-(ℓ * (1 + u) * v)) : ℂ) * Complex.exp (I * (ℓ * T * v : ℂ)) := by
  unfold saddleMellinInversePower
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (exp_pos v).ne'),
    ← Complex.ofReal_log (exp_pos v).le, log_exp, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  unfold z_contour
  push_cast
  ring

/-- The positive prefactor of report (46). -/
def saddleSourceCenteredPrefactor (ε ℓ u v : ℝ) : ℝ :=
  ℓ / (2 * π) * exp (-(ℓ * (1 + u) * v)) * saddleSourceContourEnvelopeScale ε ℓ u

theorem saddleSourceCenteredPrefactor_pos {ε ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : -1 < u) (v : ℝ) :
    0 < saddleSourceCenteredPrefactor ε ℓ u v := by
  unfold saddleSourceCenteredPrefactor
  exact mul_pos (mul_pos (div_pos hℓ (by positivity)) (exp_pos _))
    (saddleSourceContourEnvelopeScale_pos (ε := ε) hℓ hu)

theorem saddleSourceContour_envelope_eq_scale_mul_normalized {ε ℓ u : ℝ} (hℓ : 0 < ℓ)
    (hu : -1 < u) (T : ℝ) :
    mellinEnvelope ε ℓ (z_contour ℓ u T) =
      (saddleSourceContourEnvelopeScale ε ℓ u : ℂ) * saddleSourceNormalizedEnvelope ε ℓ u T := by
  unfold saddleSourceNormalizedEnvelope
  field_simp [Complex.ofReal_ne_zero.mpr (saddleSourceContourEnvelopeScale_pos (ε := ε) hℓ hu).ne']

/-- Report (46): the contour integrand factors as a positive constant times the centered
integrand `e^{L_u} P(T + iu)`. -/
theorem saddleSourceCenteredIntegrand_sourcePointwise {ε ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : -1 < u)
    (P : ℂ → ℂ) (v T : ℝ) :
    saddleMellinInversePower (exp v) (z_contour ℓ u T) *
        (mellinEnvelope ε ℓ (z_contour ℓ u T) *
          P (I * (z_contour ℓ u T - (ℓ : ℂ)) / (ℓ : ℂ))) =
      (exp (-(ℓ * (1 + u) * v)) * saddleSourceContourEnvelopeScale ε ℓ u : ℂ) *
        (expL ε ℓ u v T * P ((T : ℂ) + I * (u : ℂ))) := by
  rw [saddleSourceContour_inversePower_exp, saddleSourceMellinContour_shellArgument hℓ,
    saddleSourceContour_envelope_eq_scale_mul_normalized hℓ hu T]
  unfold expL
  push_cast
  ring

theorem centeredIntegrand_sourcePointwise {ε ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : -1 < u) (P : ℂ → ℂ)
    (v T : ℝ) :
    saddleMellinInversePower (exp v) (z_contour ℓ u T) * mellinData ε ℓ P (z_contour ℓ u T) =
      (exp (-(ℓ * (1 + u) * v)) * saddleSourceContourEnvelopeScale ε ℓ u : ℂ) *
        centeredIntegrand ε ℓ P u v T :=
  saddleSourceCenteredIntegrand_sourcePointwise hℓ hu P v T

/-- Report (46): `f(e^v)` is a positive multiple of the integral of the centered integrand. -/
theorem saddleProfile_exp_eq_centeredIntegral {ε ℓ u v : ℝ} {f : ℝ → ℂ} {M : ℂ → ℂ} {g : ℝ → ℂ}
    (hsource : f (exp v) = (ℓ / (2 * π) : ℂ) *
      ∫ T : ℝ, saddleMellinInversePower (exp v) (z_contour ℓ u T) * M (z_contour ℓ u T))
    (hpoint : ∀ T : ℝ, saddleMellinInversePower (exp v) (z_contour ℓ u T) * M (z_contour ℓ u T) =
      (exp (-(ℓ * (1 + u) * v)) * saddleSourceContourEnvelopeScale ε ℓ u : ℂ) * g T) :
    f (exp v) = (saddleSourceCenteredPrefactor ε ℓ u v : ℂ) * ∫ T : ℝ, g T := by
  rw [hsource, integral_congr_ae (Filter.Eventually.of_forall hpoint),
    MeasureTheory.integral_const_mul]
  unfold saddleSourceCenteredPrefactor
  push_cast
  ring

/-- Report (46): `f_P(e^v)` is a positive multiple of the integral of the centered integrand. -/
theorem mellinProfile_exp_eq_centeredIntegral {ε ℓ u : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : a₀ε ε ≤ Aε ε) {P : ℂ → ℂ} (hP : IsSaddlePolynomial ε P) (c v : ℝ) :
    mellinProfile ε ℓ P c (exp v) = (saddleSourceCenteredPrefactor ε ℓ u v : ℂ) *
      ∫ T : ℝ, centeredIntegrand ε ℓ P u v T :=
  saddleProfile_exp_eq_centeredIntegral
    (mellinProfile_eq_sourceContourIntegral hε hℓ horder hP c (exp_pos v) hu)
    fun T ↦ centeredIntegrand_sourcePointwise hℓ hu P v T

/-! ### The Gaussian approximation of report (71) -/

/-- The variance `V(u)` of the Gaussian approximation, report (71). -/
def V_u (ε ℓ u : ℝ) : ℝ := upperSaddleVariance ε ℓ (u - 1)

/-- The Gaussian `e^{-λV(u)T²/2}` of report (71). -/
def saddleSourceGaussianKernel (ε ℓ u T : ℝ) : ℝ := exp (-(ℓ * V_u ε ℓ u / 2) * T ^ 2)

/-- The Gaussian approximation `e^{-λV(u)T²/2} P(iu)` of the centered integrand, report (71). -/
def gaussianIntegrand (ε ℓ : ℝ) (P : ℂ → ℂ) (u T : ℝ) : ℂ :=
  (saddleSourceGaussianKernel ε ℓ u T : ℂ) * P (I * (u : ℂ))

theorem saddleSourceGaussianKernel_integrable {ε ℓ u : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V_u ε ℓ u) :
    Integrable (saddleSourceGaussianKernel ε ℓ u) := by
  unfold saddleSourceGaussianKernel
  exact integrable_exp_neg_mul_sq (by positivity)

theorem saddleSourceGaussianKernel_integral (ε ℓ u : ℝ) :
    (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) = √(π / (ℓ * V_u ε ℓ u / 2)) :=
  integral_gaussian (ℓ * V_u ε ℓ u / 2)

theorem saddleSourceGaussianKernel_integral_pos {ε ℓ u : ℝ} (hℓ : 0 < ℓ)
    (hV : 0 < V_u ε ℓ u) : 0 < ∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T := by
  rw [saddleSourceGaussianKernel_integral]
  positivity

theorem gaussianIntegrand_integrable {ε ℓ u : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V_u ε ℓ u) (P : ℂ → ℂ) :
    Integrable (gaussianIntegrand ε ℓ P u) := by
  unfold gaussianIntegrand
  exact (saddleSourceGaussianKernel_integrable hℓ hV).ofReal.mul_const _

theorem gaussianIntegrand_integral (ε ℓ : ℝ) (P : ℂ → ℂ) (u : ℝ) :
    (∫ T : ℝ, gaussianIntegrand ε ℓ P u T) =
      (√(π / (ℓ * V_u ε ℓ u / 2)) : ℂ) * P (I * (u : ℂ)) := by
  unfold gaussianIntegrand
  rw [MeasureTheory.integral_mul_const, integral_complex_ofReal,
    saddleSourceGaussianKernel_integral]

/-- The Gaussian model integral has real part `Re P(iu)` times the Gaussian mass. -/
theorem gaussianIntegrand_integral_re (ε ℓ : ℝ) (P : ℂ → ℂ) (u : ℝ) :
    (∫ T : ℝ, gaussianIntegrand ε ℓ P u T).re =
      (P (I * (u : ℂ))).re * ∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T := by
  rw [gaussianIntegrand_integral, saddleSourceGaussianKernel_integral]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem eventually_saddleSourceGaussianVariance_secondBranch_pos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    ∀ ℓ : ℝ, 0 < ℓ → ∀ δ : ℝ, ε / 2 ≤ δ → 0 < V_u ε ℓ (1 + δ) := by
  filter_upwards [eventually_upperSaddleVariance_pos] with ε hpositive ℓ hℓ δ hδ
  simpa [V_u] using hpositive ℓ hℓ δ hδ

/-- Report §4.3: a Gaussian approximation with error smaller than the Gaussian mass
`‖P(iu)‖ ∫ e^{-λV T²/2}` forces `f_P(e^v)` to have the sign of `P(iu)`, i.e.
`Re P(iu) · Re f_P(e^v) > 0`. -/
theorem mellinProfile_exp_re_mul_pos_of_gaussian_error {ε ℓ u v : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (hu : -1 < u) (horder : a₀ε ε ≤ Aε ε) {P : ℂ → ℂ} (hP : IsSaddlePolynomial ε P) (c : ℝ)
    (herror : ‖(∫ T : ℝ, centeredIntegrand ε ℓ P u v T) - ∫ T : ℝ, gaussianIntegrand ε ℓ P u T‖ <
      ‖P (I * (u : ℂ))‖ * ∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) :
    0 < (P (I * (u : ℂ))).re * (mellinProfile ε ℓ P c (exp v)).re := by
  set a : ℝ := (P (I * (u : ℂ))).re with ha
  set G : ℝ := ∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T with hG
  set J : ℂ := ∫ T : ℝ, centeredIntegrand ε ℓ P u v T with hJdef
  have hnorm : ‖P (I * (u : ℂ))‖ = |a| := by
    have hz : P (I * (u : ℂ)) = (a : ℂ) := Complex.ext rfl (by simp [hP.im_imaginary u])
    rw [hz, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm] at herror
  have hapos : 0 < |a| := by
    by_contra h
    rw [le_antisymm (not_lt.mp h) (abs_nonneg a), zero_mul] at herror
    exact absurd herror (not_lt.mpr (norm_nonneg _))
  have hJ : 0 < a * J.re := by
    have h1 := Complex.abs_re_le_norm (J - ∫ T : ℝ, gaussianIntegrand ε ℓ P u T)
    rw [Complex.sub_re, gaussianIntegrand_integral_re ε ℓ P u] at h1
    have h2 : |a| * |J.re - a * G| < a ^ 2 * G := by
      calc |a| * |J.re - a * G| ≤ |a| * ‖J - ∫ T : ℝ, gaussianIntegrand ε ℓ P u T‖ := by gcongr
        _ < |a| * (|a| * G) := by gcongr
        _ = a ^ 2 * G := by rw [← mul_assoc, abs_mul_abs_self, sq]
    have h3 : -(|a| * |J.re - a * G|) ≤ a * (J.re - a * G) := by
      rw [← abs_mul]
      exact neg_abs_le _
    nlinarith
  rw [mellinProfile_exp_eq_centeredIntegral hε hℓ hu horder hP c v, ← hJdef]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [mul_left_comm]
  exact mul_pos (saddleSourceCenteredPrefactor_pos hℓ hu v) hJ

/-! ### Positivity of the variance on the first branch -/

theorem saddleSourcePositiveShellVariance_nonneg (ε δ : ℝ) : 0 ≤ V_B ε δ := by
  refine intervalIntegral.integral_nonneg (by linarith) fun a _ ↦ ?_
  unfold w_B
  exact mul_nonneg (mul_nonneg (div_nonneg (shellWeight_pos ε).le (cosh_pos a).le)
    (sq_nonneg a)) (cosh_pos _).le

/-- Report §4.3: on the first branch the short shell carries at most `(1 - 2ε)` of the gamma
variance. -/
theorem upperFirstBranch_shortVariance_le_gamma {ε ℓ u : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (hulower : -1 < u) (huupper : u ≤ 1 + ε / 2) (horder : a₀ε ε ≤ Aε ε)
    (hmargin : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a) :
    V_s ε (u - 1) ≤ (1 - 2 * ε) * V_γ ℓ (1 + u) := by
  have hη : 0 < 1 + u := by linarith
  have ha₀ : 0 < a₀ε ε := by unfold a₀ε; positivity
  have hfactor : 0 ≤ 1 - 2 * ε := by linarith
  have hsubset : Ioc (a₀ε ε) (Aε ε) ⊆ Ioi (0 : ℝ) := fun a ha ↦ ha₀.trans ha.1
  have hgamma : IntegrableOn (fun a : ℝ ↦ a ^ 2 * μ_ℓ ℓ (1 + u) a) (Ioi (0 : ℝ)) :=
    upperGammaVarianceDensity_integrable hℓ hη
  have hshortOn : IntegrableOn (fun a : ℝ ↦ ℓ * (-w_s ε a) * cosh (u * a) * a ^ 2)
      (Ioc (a₀ε ε) (Aε ε)) := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le horder).mp ?_
    exact ((((shortShellDensity_intervalIntegrable hε horder).neg.const_mul ℓ).mul_continuousOn
      (by fun_prop)).mul_continuousOn (by fun_prop))
  have hpoint (a : ℝ) (ha : a ∈ Ioc (a₀ε ε) (Aε ε)) :
      ℓ * (-w_s ε a) * cosh (u * a) * a ^ 2 ≤ (1 - 2 * ε) * (a ^ 2 * μ_ℓ ℓ (1 + u) a) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_right (upperFirstBranch_shortMeasure_pointwise hε hεsmall hℓ
        (ha₀.trans ha.1) hulower.le huupper (hmargin a ⟨ha.1.le, ha.2⟩)) (sq_nonneg a)
  have hmono := setIntegral_mono_on hshortOn
    ((hgamma.mono_set hsubset).const_mul (1 - 2 * ε)) measurableSet_Ioc hpoint
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun a : ℝ ↦ a ^ 2 * μ_ℓ ℓ (1 + u) a := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    exact mul_nonneg (sq_nonneg a) (upperGammaMeasureDensity_pos hℓ ha).le
  have hrestrict := mul_le_mul_of_nonneg_left (setIntegral_mono_set hgamma hnonneg
    (Filter.Eventually.of_forall fun a ha ↦ hsubset ha)) hfactor
  have hshortEq : ℓ * V_s ε (u - 1) =
      ∫ a : ℝ in Ioc (a₀ε ε) (Aε ε), ℓ * (-w_s ε a) * cosh (u * a) * a ^ 2 := by
    unfold V_s
    rw [show 1 + (u - 1) = u from by ring, ← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le horder]
    exact setIntegral_congr_fun measurableSet_Ioc fun a _ ↦ by ring
  have hmain : ℓ * V_s ε (u - 1) ≤
      (1 - 2 * ε) * ∫ a : ℝ in Ioi (0 : ℝ), a ^ 2 * μ_ℓ ℓ (1 + u) a := by
    calc ℓ * V_s ε (u - 1)
        = ∫ a : ℝ in Ioc (a₀ε ε) (Aε ε), ℓ * (-w_s ε a) * cosh (u * a) * a ^ 2 := hshortEq
      _ ≤ ∫ a : ℝ in Ioc (a₀ε ε) (Aε ε), (1 - 2 * ε) * (a ^ 2 * μ_ℓ ℓ (1 + u) a) := hmono
      _ = (1 - 2 * ε) * ∫ a : ℝ in Ioc (a₀ε ε) (Aε ε), a ^ 2 * μ_ℓ ℓ (1 + u) a :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ (1 - 2 * ε) * ∫ a : ℝ in Ioi (0 : ℝ), a ^ 2 * μ_ℓ ℓ (1 + u) a := hrestrict
  calc V_s ε (u - 1) = ℓ⁻¹ * (ℓ * V_s ε (u - 1)) := by field_simp
    _ ≤ ℓ⁻¹ * ((1 - 2 * ε) * ∫ a : ℝ in Ioi (0 : ℝ), a ^ 2 * μ_ℓ ℓ (1 + u) a) :=
        mul_le_mul_of_nonneg_left hmain (inv_pos.mpr hℓ).le
    _ = (1 - 2 * ε) * V_γ ℓ (1 + u) := by
        unfold V_γ
        ring

theorem upperFirstBranch_saddleSourceGaussianVariance_lower_bound {ε ℓ u : ℝ} (hε : 0 < ε)
    (hεsmall : ε ≤ 1 / 4) (hℓ : 0 < ℓ) (hulower : -1 < u) (huupper : u ≤ 1 + ε / 2)
    (horder : a₀ε ε ≤ Aε ε) (hmargin : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a) :
    2 * ε * V_γ ℓ (1 + u) ≤ V_u ε ℓ u := by
  have hshort :=
    upperFirstBranch_shortVariance_le_gamma hε hεsmall hℓ hulower huupper horder hmargin
  have hpositive := saddleSourcePositiveShellVariance_nonneg ε (u - 1)
  unfold V_u upperSaddleVariance upperNetShellVariance
  rw [show 2 + (u - 1) = 1 + u from by ring]
  nlinarith

theorem eventually_saddleSourceGaussianVariance_firstBranch_pos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    ∀ ℓ : ℝ, 0 < ℓ → ∀ u : ℝ, -1 < u → u ≤ 1 + ε / 2 → 0 < V_u ε ℓ u := by
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ≤ 1 / 4 := by
    have htendsto : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    filter_upwards [htendsto.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))] with ε hε
    exact hε.le
  filter_upwards [self_mem_nhdsWithin, hsmall, eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_upper_shortMargin_positive] with ε hε hεsmall horder hmargin ℓ hℓ u hulower huupper
  change 0 < ε at hε
  have hη : 0 < 1 + u := by linarith
  have hgammaPos : 0 < V_γ ℓ (1 + u) :=
    (show (0 : ℝ) < 1 / (2 * (1 + u)) by positivity).trans_le (upperGammaVariance_bounds hℓ hη).1
  exact (mul_pos (by positivity : (0 : ℝ) < 2 * ε) hgammaPos).trans_le
    (upperFirstBranch_saddleSourceGaussianVariance_lower_bound hε hεsmall hℓ hulower huupper horder
      fun a ha ↦ le_trans (by norm_num) (hmargin a ha))

/-! ### Integrability of the centered integrands -/

theorem integrable_of_const_mul_integrable {g : ℝ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (h : Integrable fun T : ℝ ↦ c * g T) : Integrable g := by
  simpa [← mul_assoc, inv_mul_cancel₀ hc] using h.const_mul c⁻¹

theorem saddleSourceCenteredIntegrand_integrable {ε ℓ u v : ℝ} {M : ℂ → ℂ} {g : ℝ → ℂ}
    (hℓ : 0 < ℓ) (hu : -1 < u)
    (hline : Integrable fun t : ℝ ↦ saddleMellinInversePower (exp v)
      (((ℓ * (1 + u) : ℝ) : ℂ) + (t : ℂ) * I) * M (((ℓ * (1 + u) : ℝ) : ℂ) + (t : ℂ) * I))
    (hpoint : ∀ T : ℝ, saddleMellinInversePower (exp v) (z_contour ℓ u T) * M (z_contour ℓ u T) =
      (exp (-(ℓ * (1 + u) * v)) * saddleSourceContourEnvelopeScale ε ℓ u : ℂ) * g T) :
    Integrable g := by
  refine integrable_of_const_mul_integrable
    (c := (exp (-(ℓ * (1 + u) * v)) * saddleSourceContourEnvelopeScale ε ℓ u : ℂ))
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr (exp_pos _).ne')
      (Complex.ofReal_ne_zero.mpr (saddleSourceContourEnvelopeScale_pos (ε := ε) hℓ hu).ne')) ?_
  have hstep (T : ℝ) : saddleMellinInversePower (exp v)
      (((ℓ * (1 + u) : ℝ) : ℂ) + (((-ℓ) * T : ℝ) : ℂ) * I) *
        M (((ℓ * (1 + u) : ℝ) : ℂ) + (((-ℓ) * T : ℝ) : ℂ) * I) =
      (exp (-(ℓ * (1 + u) * v)) * saddleSourceContourEnvelopeScale ε ℓ u : ℂ) * g T := by
    have harg : ((ℓ * (1 + u) : ℝ) : ℂ) + (((-ℓ) * T : ℝ) : ℂ) * I = z_contour ℓ u T := by
      unfold z_contour
      push_cast
      ring
    rw [harg, hpoint T]
  exact (hline.comp_mul_left' (neg_ne_zero.mpr hℓ.ne')).congr
    (Filter.Eventually.of_forall hstep)

theorem centeredIntegrand_integrable {ε ℓ u : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : a₀ε ε ≤ Aε ε) {P : ℂ → ℂ} (hP : IsSaddlePolynomial ε P) (v : ℝ) :
    Integrable (centeredIntegrand ε ℓ P u v) := by
  have hη : 0 < 1 + u := by linarith
  have ha : 0 < ℓ * (1 + u) := by positivity
  exact saddleSourceCenteredIntegrand_integrable hℓ hu
    (mellinData_shiftedLine_weighted_integrable hε hℓ horder hP (saddlePositiveContour_ne_pole ha)
      (exp_pos v))
    fun T ↦ centeredIntegrand_sourcePointwise hℓ hu P v T

end

end CohnElkies
