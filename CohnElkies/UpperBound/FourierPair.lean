import CohnElkies.UpperBound.MellinProfile
import CohnElkies.UpperBound.WallisRadius
import CohnElkies.SchwartzTools
import CohnElkiesForMathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# The Fourier pair `𝓕 f₋ = f₊` and the admissible source (report §4.1, (40), (83)–(84))

The critical log profile of a radial test function and the injectivity of the Mellin frequency
map, radial sources with a prescribed Mellin spectrum, the Fourier data of the profiles `f_P`,
the Fourier pair `𝓕 f₋ = f₊` (report (40)), the admissible function built from `f₊ - f₋` when the
signs are right and its normalized cost, the logarithm of the saddle radius `r(u)` (report (83),
via the Real.digamma function) and the saddle radius `R_{ε,d} = r(1 + ε/4)` with
`R_{ε,d}/√d → α_ε` (report (84)).
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory Real Set
open scoped FourierTransform SchwartzMap Topology

/-! ### The critical log profile of a radial test function (report (8)) -/

/-- The critical log profile `u ↦ e^{-λu} g(e^{-u})`, `λ = d/2`, of the radial profile `g` of a
test function `f`. -/
def radialCriticalLogProfile {d : ℕ} (hd : 0 < d) (f : TestFunction d) (u : ℝ) : ℂ :=
  exp (-((d : ℝ) / 2) * u) • radialProfile hd f (exp (-u))

theorem radialCriticalLogProfile_eq_reflected_tilt {d : ℕ} (hd : 0 < d) (f : TestFunction d)
    (u : ℝ) : radialCriticalLogProfile hd f u =
      schwartzExponentialTilt (radialSchwartzProfile hd f) ((d : ℝ) / 2) 1 (-u) := by
  simp [radialCriticalLogProfile, schwartzExponentialTilt, radialSchwartzProfile_apply, mul_neg]

theorem radialCriticalLogProfile_integrable {d : ℕ} (hd : 0 < d) (f : TestFunction d) :
    Integrable (radialCriticalLogProfile hd f) :=
  ((schwartzExponentialTilt_integrable (radialSchwartzProfile hd f)
    (div_pos (by exact_mod_cast hd) (by norm_num)) one_pos).comp_neg).congr
      (Eventually.of_forall fun u ↦ (radialCriticalLogProfile_eq_reflected_tilt hd f u).symm)

theorem radialCriticalLogProfile_continuous {d : ℕ} (hd : 0 < d) (f : TestFunction d) :
    Continuous (radialCriticalLogProfile hd f) := by
  unfold radialCriticalLogProfile
  exact (by fun_prop : Continuous fun u : ℝ ↦ exp (-((d : ℝ) / 2) * u)).smul
    ((radialProfile_continuous hd f).comp (by fun_prop))

theorem radialCriticalLogProfile_fourier_integrable {d : ℕ} (hd : 0 < d) (f : TestFunction d) :
    Integrable (𝓕 (radialCriticalLogProfile hd f) : ℝ → ℂ) := by
  have hdim : (0 : ℝ) < (d : ℝ) / 2 := div_pos (by exact_mod_cast hd) (by norm_num)
  set G : ℝ → ℂ := schwartzExponentialTilt (radialSchwartzProfile hd f) ((d : ℝ) / 2) 1 with hG
  have hprofile : radialCriticalLogProfile hd f = fun v : ℝ ↦ G (-v) :=
    funext (radialCriticalLogProfile_eq_reflected_tilt hd f)
  refine ((schwartzExponentialTilt_fourier_integrable (radialSchwartzProfile hd f) hdim
    (show (0 : ℝ) < 1 by norm_num)).comp_neg).congr (Eventually.of_forall fun u ↦ ?_)
  rw [hprofile]
  simpa [Function.comp_def, G] using (Real.fourier_comp_linearIsometry
    (LinearIsometryEquiv.neg ℝ) G u).symm

theorem radialMellinFrequency_eq_criticalLogFourier {d : ℕ} (hd : 0 < d) (f : TestFunction d)
    (t : ℝ) : X_fℝ hd f t = (𝓕 (radialCriticalLogProfile hd f) : ℝ → ℂ) (-t / (2 * π)) :=
  radialMellinFrequency_eq_fourier hd f t

/-- Report (8): a radial test function is determined by its Mellin frequency `X_f`. -/
theorem radialMellinFrequency_injective {d : ℕ} (hd : 0 < d) {f g : TestFunction d}
    (hf : IsRadial f) (hg : IsRadial g)
    (hfrequency : ∀ t : ℝ, X_fℝ hd f t = X_fℝ hd g t) :
    f = g := by
  have hinv (h : TestFunction d) : (𝓕⁻ (𝓕 (radialCriticalLogProfile hd h) : ℝ → ℂ) : ℝ → ℂ) =
      radialCriticalLogProfile hd h :=
    funext fun u ↦ (radialCriticalLogProfile_integrable hd h).fourierInv_fourier_eq
      (radialCriticalLogProfile_fourier_integrable hd h)
      (radialCriticalLogProfile_continuous hd h).continuousAt
  have hfourier : (𝓕 (radialCriticalLogProfile hd f) : ℝ → ℂ) =
      (𝓕 (radialCriticalLogProfile hd g) : ℝ → ℂ) := by
    funext ξ
    have h := hfrequency (-(2 * π * ξ))
    rw [radialMellinFrequency_eq_criticalLogFourier,
      radialMellinFrequency_eq_criticalLogFourier] at h
    convert h using 1 <;> field_simp [Real.pi_ne_zero]
  have hlog : radialCriticalLogProfile hd f = radialCriticalLogProfile hd g := by
    rw [← hinv f, hfourier, hinv g]
  have hpositive (r : ℝ) (hr : 0 < r) : radialProfile hd f r = radialProfile hd g r := by
    have h := congrFun hlog (-log r)
    simp only [radialCriticalLogProfile, neg_neg, exp_log hr, Complex.real_smul] at h
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.2 (exp_ne_zero _)) h
  have heventually : radialProfile hd f =ᶠ[𝓝[>] (0 : ℝ)] radialProfile hd g :=
    eventually_nhdsWithin_of_forall hpositive
  have hzero : radialProfile hd f 0 = radialProfile hd g 0 :=
    tendsto_nhds_unique
      ((radialProfile_continuous hd f).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (((radialProfile_continuous hd g).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds).congr' heventually.symm)
  refine SchwartzMap.ext fun x ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simpa using hzero
  · rw [← radialProfile_norm hd f hf x, ← radialProfile_norm hd g hg x]
    exact hpositive _ (norm_pos_iff.2 hx)

/-! ### Radial sources with a prescribed Mellin spectrum (report (40)) -/

theorem exp_neg_rpow_neg_half_dimension {d : ℕ} (u : ℝ) :
    exp (-u) ^ (-((d : ℝ) / 2)) = exp ((d : ℝ) / 2 * u) := by
  rw [rpow_def_of_pos (exp_pos (-u)), log_exp]
  congr 1
  ring

/-- If `f = F ‖·‖` with `F r = r^{-λ} 𝓕G(log r)` for `r > 0`, then the critical log profile of `f`
is the inverse Fourier transform of `G`. -/
theorem criticalLogProfile_eq_fourierInv {d : ℕ} (hd : 0 < d) {F G : ℝ → ℂ}
    (hF : ∀ r : ℝ, 0 < r → F r = (r ^ (-((d : ℝ) / 2)) : ℝ) * 𝓕 G (log r))
    (f : TestFunction d) (hf : ∀ x : Euclidean d, f x = F ‖x‖) :
    radialCriticalLogProfile hd f = (𝓕⁻ G : ℝ → ℂ) := by
  have hprofile (r : ℝ) (hr : 0 ≤ r) : radialProfile hd f r = F r := by
    unfold radialProfile
    rw [hf]
    simp [norm_smul, norm_radialUnitDirection hd, abs_of_nonneg hr]
  funext u
  unfold radialCriticalLogProfile
  rw [hprofile _ (exp_pos (-u)).le, hF _ (exp_pos (-u)), exp_neg_rpow_neg_half_dimension,
    log_exp, Real.fourierInv_eq_fourier_neg]
  simp only [Complex.real_smul]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← exp_add]
  simp

theorem fourier_integrable_of_source {d : ℕ} (hd : 0 < d) {F G : ℝ → ℂ}
    (hF : ∀ r : ℝ, 0 < r → F r = (r ^ (-((d : ℝ) / 2)) : ℝ) * 𝓕 G (log r))
    (f : TestFunction d) (hf : ∀ x : Euclidean d, f x = F ‖x‖) :
    Integrable (𝓕 G : ℝ → ℂ) := by
  refine ((radialCriticalLogProfile_integrable hd f).comp_neg).congr
    (Eventually.of_forall fun u ↦ ?_)
  simpa [Real.fourierInv_eq_fourier_neg] using
    congrFun (criticalLogProfile_eq_fourierInv hd hF f hf) (-u)

/-- Report (40): the Mellin frequency of such a source is `t ↦ G(-t/2π)`. -/
theorem radialMellinFrequency_of_source {d : ℕ} (hd : 0 < d) {F G : ℝ → ℂ}
    (hF : ∀ r : ℝ, 0 < r → F r = (r ^ (-((d : ℝ) / 2)) : ℝ) * 𝓕 G (log r))
    (hGint : Integrable G) (hGcont : Continuous G) (f : TestFunction d)
    (hf : ∀ x : Euclidean d, f x = F ‖x‖) (t : ℝ) :
    X_fℝ hd f t = G (-t / (2 * π)) := by
  rw [radialMellinFrequency_eq_criticalLogFourier hd f t,
    criticalLogProfile_eq_fourierInv hd hF f hf]
  exact hGint.fourier_fourierInv_eq (fourier_integrable_of_source hd hF f hf) hGcont.continuousAt

/-- A test function of the form `x ↦ F ‖x‖` is radial. -/
theorem isRadial_of_source {d : ℕ} {F : ℝ → ℂ} {f : TestFunction d}
    (hf : ∀ x : Euclidean d, f x = F ‖x‖) : IsRadial f := fun x y hxy ↦ by
  rw [hf x, hf y, hxy]

/-! ### The Fourier data of the profiles `f_P` -/

theorem fourierData_continuous {ε ℓ : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ) (horder : a₀ε ε ≤ Aε ε)
    {P : ℂ → ℂ} (hP : IsSaddlePolynomial ε P) : Continuous (fourierData ε ℓ P) := by
  unfold fourierData
  exact (spectrum_continuous hε hℓ horder hP.continuous).comp (by fun_prop)

theorem fourierData_integrable {ε ℓ : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ) (horder : a₀ε ε ≤ Aε ε)
    {P : ℂ → ℂ} (hP : IsSaddlePolynomial ε P) : Integrable (fourierData ε ℓ P) :=
  (integrable_norm_iff (fourierData_continuous hε hℓ horder hP).aestronglyMeasurable).mp
    (by simpa using fourierData_norm_moment_integrable hε hℓ horder hP 0)

/-- Report (40): the Mellin frequency of a test function `x ↦ f_P(‖x‖)` is the spectrum `X_P`. -/
theorem radialMellinFrequency_of_mellinProfile {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : a₀ε ε ≤ Aε ε) {P : ℂ → ℂ} (hP : IsSaddlePolynomial ε P) {c : ℝ}
    (f : TestFunction d) (hf : ∀ x : Euclidean d, f x = mellinProfileFun ε d P c x) (t : ℝ) :
    X_fℝ hd f t = spectrum ε ((d : ℝ) / 2) P t := by
  have hdim : (0 : ℝ) < (d : ℝ) / 2 := div_pos (by exact_mod_cast hd) (by norm_num)
  rw [radialMellinFrequency_of_source hd
    (fun r hr ↦ mellinProfile_eq_fourier ε ((d : ℝ) / 2) P c hr)
    (fourierData_integrable hε hdim horder hP) (fourierData_continuous hε hdim horder hP) f hf t]
  unfold fourierData
  congr 1
  field_simp [Real.pi_ne_zero]

/-! ### The Fourier pair `f̂₋ = f₊` (report (40)) and the admissible source -/

theorem isRealValued_of_mellinProfile {ε : ℝ} {P : ℂ → ℂ} (hP : IsSaddlePolynomial ε P) {d : ℕ}
    {c : ℝ} {f : TestFunction d} (hf : ∀ x : Euclidean d, f x = mellinProfileFun ε d P c x) :
    IsRealValued f :=
  fun x ↦ by rw [hf x]; exact mellinProfileFun_im hP d c x

theorem isRadial_of_mellinProfile {ε : ℝ} {P : ℂ → ℂ} {d : ℕ} {c : ℝ} {f : TestFunction d}
    (hf : ∀ x : Euclidean d, f x = mellinProfileFun ε d P c x) : IsRadial f :=
  isRadial_of_source (F := mellinProfile ε ((d : ℝ) / 2) P c) hf

theorem plusSaddle_real_of_source {ε : ℝ} {d : ℕ} {f : TestFunction d}
    (hf : ∀ x : Euclidean d, f x = fPlusFun ε d x) : IsRealValued f :=
  isRealValued_of_mellinProfile (c := originValue ε ((d : ℝ) / 2)) (isSaddlePolynomial_PPlus ε) hf

theorem minusSaddle_real_of_source {ε : ℝ} {d : ℕ} {f : TestFunction d}
    (hf : ∀ x : Euclidean d, f x = fMinusFun ε d x) : IsRealValued f :=
  isRealValued_of_mellinProfile (c := originValue ε ((d : ℝ) / 2)) (isSaddlePolynomial_PMinus ε)
    hf

/-- Report (40): `𝓕 f_P = f_Q` for test functions `f_P`, `f_Q` realizing the profiles of two
saddle polynomials with `P(-ζ) = Q(ζ)`. -/
theorem fourier_eq_of_mellinProfile {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : a₀ε ε ≤ Aε ε) {P Q : ℂ → ℂ} (hP : IsSaddlePolynomial ε P)
    (hQ : IsSaddlePolynomial ε Q) (hPQ : ∀ z : ℂ, P (-z) = Q z) {c c' : ℝ}
    (f g : TestFunction d) (hf : ∀ x : Euclidean d, f x = mellinProfileFun ε d P c x)
    (hg : ∀ x : Euclidean d, g x = mellinProfileFun ε d Q c' x) :
    (𝓕 f : TestFunction d) = g := by
  have hrf : IsRadial f := isRadial_of_mellinProfile hf
  refine radialMellinFrequency_injective hd (gaussianMellin_fourier_radial hrf)
    (isRadial_of_mellinProfile hg) fun t ↦ ?_
  calc
    X_fℝ hd (𝓕 f : TestFunction d) t = m_ℓ ((d : ℝ) / 2) t * X_fℝ hd f (-t) :=
      radialMellinMultiplier hd f hrf t
    _ = m_ℓ ((d : ℝ) / 2) t * spectrum ε ((d : ℝ) / 2) P (-t) := by
      rw [radialMellinFrequency_of_mellinProfile hε hd horder hP f hf]
    _ = spectrum ε ((d : ℝ) / 2) Q t :=
      mellinMultiplier_mul_spectrum_neg (div_pos (by exact_mod_cast hd) (by norm_num)) hPQ t
    _ = X_fℝ hd g t := (radialMellinFrequency_of_mellinProfile hε hd horder hQ g hg t).symm

/-- Report (40): `f̂₋ = f₊`. -/
theorem saddleSource_fourier_minus_eq_plus {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : a₀ε ε ≤ Aε ε) (fminus fplus : TestFunction d)
    (hminus : ∀ x : Euclidean d, fminus x = fMinusFun ε d x)
    (hplus : ∀ x : Euclidean d, fplus x = fPlusFun ε d x) : (𝓕 fminus : TestFunction d) = fplus :=
  fourier_eq_of_mellinProfile hε hd horder (isSaddlePolynomial_PMinus ε)
    (isSaddlePolynomial_PPlus ε) (minusPolynomial_neg ε) (c := originValue ε ((d : ℝ) / 2))
    (c' := originValue ε ((d : ℝ) / 2)) fminus fplus hminus hplus

/-- Report (42): the common value `f₊(0) = f₋(0) > 0` at the origin. -/
theorem saddleSource_zero_pos {ε : ℝ} (hε : 0 < ε) {d : ℕ} (fminus fplus : TestFunction d)
    (hminus : ∀ x : Euclidean d, fminus x = fMinusFun ε d x)
    (hplus : ∀ x : Euclidean d, fplus x = fPlusFun ε d x) :
    0 < (fminus (0 : Euclidean d)).re ∧ 0 < (fplus (0 : Euclidean d)).re := by
  rw [hminus, hplus]
  exact (saddleFunction_zero_pos hε d).symm

theorem saddleSource_zero_eq {ε : ℝ} {d : ℕ} (fminus fplus : TestFunction d)
    (hminus : ∀ x : Euclidean d, fminus x = fMinusFun ε d x)
    (hplus : ∀ x : Euclidean d, fplus x = fPlusFun ε d x) :
    fminus (0 : Euclidean d) = fplus (0 : Euclidean d) := by
  rw [hminus, hplus, minusSaddleFunction_zero, plusSaddleFunction_zero]

/-- The radial admissible function `x ↦ f₋(Rx)` built from the saddle pair `(f₋, f₊)`. -/
def saddleSourceAdmissible {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d) (horder : a₀ε ε ≤ Aε ε)
    {R : ℝ} (hR : 0 < R) (fminus fplus : TestFunction d)
    (hminus : ∀ x : Euclidean d, fminus x = fMinusFun ε d x)
    (hplus : ∀ x : Euclidean d, fplus x = fPlusFun ε d x)
    (hplusnonneg : ∀ x : Euclidean d, 0 ≤ (fPlusFun ε d x).re)
    (hminusoutside : ∀ x : Euclidean d, R ≤ ‖x‖ → (fMinusFun ε d x).re ≤ 0) :
    RadialAdmissible d := by
  have hfourier : (𝓕 fminus : TestFunction d) = fplus := saddleSource_fourier_minus_eq_plus
      hε hd horder fminus fplus hminus hplus
  have hnonneg : ∀ ξ : Euclidean d, 0 ≤ (fplus ξ).re := fun ξ ↦ by
    rw [hplus ξ]; exact hplusnonneg ξ
  refine
    { function := dilate fminus R hR
      real := (minusSaddle_real_of_source hminus).dilate R hR
      radial := (isRadial_of_source (F := fMinus ε ((d : ℝ) / 2)) hminus).dilate R hR
      fourier_real := ?_
      fourier_nonneg := ?_
      fourier_zero_pos := ?_
      outside_nonpos := ?_ }
  · intro ξ
    rw [fourier_dilate_apply, hfourier, Complex.smul_im, plusSaddle_real_of_source hplus (R⁻¹ • ξ)]
    simp
  · intro ξ
    rw [fourier_dilate_apply, hfourier, Complex.smul_re]
    simpa [smul_eq_mul] using mul_nonneg (inv_nonneg.2 (pow_nonneg hR.le d)) (hnonneg (R⁻¹ • ξ))
  · rw [fourier_dilate_zero, hfourier, Complex.smul_re]
    simpa [smul_eq_mul] using mul_pos (inv_pos.2 (pow_pos hR d))
      (saddleSource_zero_pos hε fminus fplus hminus hplus).2
  · intro x hx
    change (fminus (R • x)).re ≤ 0
    rw [hminus]
    refine hminusoutside _ ?_
    simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hR] using mul_le_mul_of_nonneg_left hx hR.le

/-- Report (31): the normalized cost of the saddle source is `R/√d`. -/
theorem saddleSourceAdmissible_normalizedCost {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : a₀ε ε ≤ Aε ε) {R : ℝ} (hR : 0 < R) (fminus fplus : TestFunction d)
    (hminus : ∀ x : Euclidean d, fminus x = fMinusFun ε d x)
    (hplus : ∀ x : Euclidean d, fplus x = fPlusFun ε d x)
    (hplusnonneg : ∀ x : Euclidean d, 0 ≤ (fPlusFun ε d x).re)
    (hminusoutside : ∀ x : Euclidean d, R ≤ ‖x‖ → (fMinusFun ε d x).re ≤ 0) :
    normalizedCost (saddleSourceAdmissible hε hd horder hR fminus fplus hminus hplus hplusnonneg
      hminusoutside).toAdmissible = R / √(d : ℝ) := by
  have hquotient : quotient (saddleSourceAdmissible hε hd horder hR fminus fplus hminus hplus
      hplusnonneg hminusoutside).toAdmissible = R ^ d := by
    have hzero : 0 < (fplus (0 : Euclidean d)).re :=
      (saddleSource_zero_pos hε fminus fplus hminus hplus).2
    change (dilate fminus R hR (0 : Euclidean d)).re /
        ((𝓕 (dilate fminus R hR) : TestFunction d) (0 : Euclidean d)).re = R ^ d
    rw [dilate_zero, fourier_dilate_zero,
      saddleSource_fourier_minus_eq_plus hε hd horder fminus fplus hminus hplus,
      saddleSource_zero_eq fminus fplus hminus hplus, Complex.smul_re]
    simp only [smul_eq_mul]
    field_simp [pow_ne_zero d hR.ne', hzero.ne']
  unfold normalizedCost
  rw [hquotient]
  congr 1
  rw [← Real.rpow_natCast_mul hR.le, mul_inv_cancel₀ (by exact_mod_cast hd.ne'), Real.rpow_one]

/-! ### The Real.digamma asymptotics and the saddle radius `R_{ε,d}` (report (84)) -/

/-- Report (83): the logarithm of the saddle radius `r(u)` in dimension `d`. -/
def logRadius (ε : ℝ) (d : ℕ) (u : ℝ) : ℝ := -(log π) / 2 +
    Real.digamma (((d : ℝ) / 2) * (1 + u) / 2) / 2 +
    (∫ a in a₀ε ε..Aε ε, w_s ε a * a * sinh (u * a)) +
    (∫ a in Bε ε..Bε ε + 1, w_B ε a * a * sinh (u * a))

/-- The saddle radius `R_{ε,d} = r(1 + ε/4)` of report (84). -/
def R_ε (ε : ℝ) (d : ℕ) : ℝ := exp (logRadius ε d (1 + ε / 4))

theorem saddleSourceRadius_pos (ε : ℝ) (d : ℕ) : 0 < R_ε ε d := exp_pos _

theorem saddle_exp_half_log_eq_sqrt {x : ℝ} (hx : 0 < x) : exp (log x / 2) = √x := by
  rw [← log_sqrt hx.le, exp_log (sqrt_pos.2 hx)]

/-- The Gamma argument `λ(2 + ε/4)/2` on the critical contour `u = 1 + ε/4`. -/
def saddleCriticalGammaArgument (ε : ℝ) (d : ℕ) : ℝ := ((d : ℝ) / 2) * (2 + ε / 4) / 2

/-- Report (84): `R_{ε,d}/√d → α_ε` as `d → ∞`. -/
theorem tendsto_saddleSourceRadius_normalized {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun d : ℕ ↦ R_ε ε d / √(d : ℝ)) atTop (𝓝 (α_ε ε)) := by
  have ha : (0 : ℝ) < 2 + ε / 4 := by positivity
  have hformula : ∀ d : ℕ, 0 < d → R_ε ε d / √(d : ℝ) =
      exp ((Real.digamma (saddleCriticalGammaArgument ε d) -
        log (saddleCriticalGammaArgument ε d)) / 2) * α_ε ε := by
    intro d hd
    have hdreal : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hm : 0 < saddleCriticalGammaArgument ε d := by
      unfold saddleCriticalGammaArgument; positivity
    have hlogm : log (saddleCriticalGammaArgument ε d) =
        log (d : ℝ) + log (2 + ε / 4) - log 4 := by
      rw [show saddleCriticalGammaArgument ε d = (d : ℝ) * (2 + ε / 4) / 4 by
          unfold saddleCriticalGammaArgument; ring,
        log_div (mul_ne_zero hdreal.ne' ha.ne') (by norm_num), log_mul hdreal.ne' ha.ne']
    have hlogq : log ((2 + ε / 4) / (4 * π)) = log (2 + ε / 4) - log 4 - log π := by
      rw [log_div ha.ne' (mul_ne_zero (by norm_num) pi_ne_zero),
        log_mul (by norm_num) pi_ne_zero]
      ring
    have hcrit : logRadius ε d (1 + ε / 4) = -(log π) / 2 +
        Real.digamma (saddleCriticalGammaArgument ε d) / 2 + shortShellRadiusContribution ε +
        positiveShellRadiusContribution ε := by
      unfold logRadius saddleCriticalGammaArgument shortShellRadiusContribution
        shortShellRadiusIntegrand positiveShellRadiusContribution
      congr 2
      ring_nf
    calc
      R_ε ε d / √(d : ℝ) = exp (-(log π) / 2 + Real.digamma (saddleCriticalGammaArgument ε d) / 2 +
          shortShellRadiusContribution ε + positiveShellRadiusContribution ε -
          log (d : ℝ) / 2) := by
        unfold R_ε
        rw [hcrit, ← saddle_exp_half_log_eq_sqrt hdreal, ← exp_sub]
      _ = exp ((Real.digamma (saddleCriticalGammaArgument ε d) -
            log (saddleCriticalGammaArgument ε d)) / 2 + log ((2 + ε / 4) / (4 * π)) / 2 +
            (shortShellRadiusContribution ε + positiveShellRadiusContribution ε)) := by
        congr 1
        rw [hlogm, hlogq]
        ring
      _ = exp ((Real.digamma (saddleCriticalGammaArgument ε d) -
            log (saddleCriticalGammaArgument ε d)) / 2) * α_ε ε := by
        rw [exp_add, exp_add,
          saddle_exp_half_log_eq_sqrt (show (0 : ℝ) < (2 + ε / 4) / (4 * π) by positivity)]
        unfold α_ε
        ring
  have hatTop : Tendsto (saddleCriticalGammaArgument ε) atTop atTop := by
    refine ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const
      (show (0 : ℝ) < (2 + ε / 4) / 4 by positivity)).congr' (Eventually.of_forall fun d ↦ ?_)
    unfold saddleCriticalGammaArgument
    ring
  have hcorrection : Tendsto (fun d : ℕ ↦ exp ((Real.digamma (saddleCriticalGammaArgument ε d) -
      log (saddleCriticalGammaArgument ε d)) / 2)) atTop (𝓝 (1 : ℝ)) := by
    have h : Tendsto (fun d : ℕ ↦ (Real.digamma (saddleCriticalGammaArgument ε d) -
        log (saddleCriticalGammaArgument ε d)) / 2) atTop (𝓝 (0 : ℝ)) := by
      simpa using (Real.tendsto_digamma_sub_log_atTop.comp hatTop).div_const (2 : ℝ)
    simpa using h.rexp
  have htarget : Tendsto (fun d : ℕ ↦ exp ((Real.digamma (saddleCriticalGammaArgument ε d) -
      log (saddleCriticalGammaArgument ε d)) / 2) * α_ε ε) atTop (𝓝 (α_ε ε)) := by
    simpa using hcorrection.mul_const (α_ε ε)
  refine htarget.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
  exact (hformula d hd).symm

end

end CohnElkies
