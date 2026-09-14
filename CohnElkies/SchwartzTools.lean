import CohnElkies.Basic
import CohnElkiesForMathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Tools for test functions: dilations, Fourier symmetries, exponential tilts

Shared infrastructure of both bounds:
* the dilation `x ↦ f(a x)` of a test function and `𝓕 (f (a ·)) (ξ) = a^{-d} 𝓕 f (ξ / a)`
  (report (29));
* the Fourier transform of a radial test function is radial, of a real radial one is real, and
  `conj (𝓕 f ξ) = 𝓕 f (-ξ)` for real `f`;
* the change of variables `r = R e^v` on `(0, ∞)`;
* the exponentially tilted profile `v ↦ e^{κ v} g(R e^v)` of a Schwartz function on `ℝ`, which
  is integrable together with its Fourier transform (used for the Mellin transforms on the lines
  `Re z = κ`).
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology RealInnerProductSpace ENNReal NNReal

/-! ### Dilations of test functions -/

/-- The dilation `x ↦ f (a x)` of a test function, `a > 0`. -/
def dilate {d : ℕ} (f : TestFunction d) (a : ℝ) (ha : 0 < a) : TestFunction d :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero ℝ (Euclidean d) a ha.ne').toContinuousLinearEquiv f

@[simp] theorem dilate_apply {d : ℕ} (f : TestFunction d) (a : ℝ) (ha : 0 < a) (x : Euclidean d) :
    dilate f a ha x = f (a • x) :=
  rfl

@[simp] theorem dilate_zero {d : ℕ} (f : TestFunction d) (a : ℝ) (ha : 0 < a) :
    dilate f a ha 0 = f 0 := by
  simp

theorem IsRealValued.dilate {d : ℕ} {f : TestFunction d} (hf : IsRealValued f) (a : ℝ)
    (ha : 0 < a) : IsRealValued (dilate f a ha) :=
  fun x ↦ hf (a • x)

theorem IsRadial.dilate {d : ℕ} {f : TestFunction d} (hf : IsRadial f) (a : ℝ) (ha : 0 < a) :
    IsRadial (dilate f a ha) :=
  fun x y hxy ↦ hf _ _ (by simp [norm_smul, hxy])

/-- `𝓕 (f (a ·)) (ξ) = a^{-d} 𝓕 f (ξ / a)` (report (29)). -/
theorem fourier_dilate_apply {d : ℕ} (f : TestFunction d) (a : ℝ) (ha : 0 < a) (ξ : Euclidean d) :
    (𝓕 (dilate f a ha) : TestFunction d) ξ = (a ^ d)⁻¹ • (𝓕 f : TestFunction d) (a⁻¹ • ξ) := by
  have h := Measure.integral_comp_smul_of_nonneg (volume : Measure (Euclidean d))
    (fun y ↦ Complex.exp (↑(-2 * π * ⟪y, a⁻¹ • ξ⟫) * I) • f y) a (hR := ha.le)
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, Real.fourier_eq', Real.fourier_eq']
  simp only [finrank_euclideanSpace_fin, real_inner_smul_left, real_inner_smul_right,
    inv_mul_cancel_left₀ ha.ne', dilate_apply] at h ⊢
  exact h

theorem fourier_dilate_zero {d : ℕ} (f : TestFunction d) (a : ℝ) (ha : 0 < a) :
    (𝓕 (dilate f a ha) : TestFunction d) 0 = (a ^ d)⁻¹ • (𝓕 f : TestFunction d) 0 := by
  simpa using fourier_dilate_apply f a ha 0

/-! ### Fourier transforms of radial and real test functions -/

/-- The Fourier transform of a radial test function is radial. -/
theorem IsRadial.fourier {d : ℕ} {f : TestFunction d} (hf : IsRadial f) :
    IsRadial (𝓕 f : TestFunction d) := by
  intro x y hxy
  set A : Euclidean d ≃ₗᵢ[ℝ] Euclidean d := Submodule.reflection (ℝ ∙ (x - y))ᗮ with hAdef
  have hcomp : (f : Euclidean d → ℂ) ∘ A = f := funext fun z ↦ hf (A z) z (A.norm_map z)
  change (𝓕 (f : Euclidean d → ℂ)) x = (𝓕 (f : Euclidean d → ℂ)) y
  calc (𝓕 (f : Euclidean d → ℂ)) x = (𝓕 ((f : Euclidean d → ℂ) ∘ A)) x := by rw [hcomp]
    _ = (𝓕 (f : Euclidean d → ℂ)) (A x) := Real.fourier_comp_linearIsometry A _ x
    _ = (𝓕 (f : Euclidean d → ℂ)) y := by rw [hAdef, Submodule.reflection_sub hxy]

/-- The Fourier transform of a real radial test function is real. -/
theorem IsRealValued.fourier_of_radial {d : ℕ} {f : TestFunction d}
    (hf : IsRealValued f) (hrad : IsRadial f) : IsRealValued (𝓕 f : TestFunction d) := by
  intro ξ
  refine Complex.conj_eq_iff_im.mp ?_
  have hconj : starRingEnd ℂ ((𝓕 f : TestFunction d) ξ) = ((𝓕 f : TestFunction d) (-ξ)) := by
    change starRingEnd ℂ ((𝓕 (f : Euclidean d → ℂ)) ξ) = (𝓕 (f : Euclidean d → ℂ)) (-ξ)
    rw [Real.fourier_eq', Real.fourier_eq', ← integral_conj]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    simp [smul_eq_mul, map_mul, ← Complex.exp_conj, Complex.conj_eq_iff_im.mpr (hf x),
      Complex.conj_ofNat]
  rw [hconj]
  exact hrad.fourier (-ξ) ξ (by simp)

theorem IsRadial.neg_apply {d : ℕ} {f : TestFunction d} (hf : IsRadial f) (x : Euclidean d) :
    f (-x) = f x := hf (-x) x (norm_neg x)

theorem IsRealValued.fourier_conj {d : ℕ} {f : TestFunction d} (hf : IsRealValued f)
    (x : Euclidean d) :
    (starRingEnd ℂ) ((𝓕 f : TestFunction d) x) = (𝓕 f : TestFunction d) (-x) := by
  change (starRingEnd ℂ) (𝓕 (f : Euclidean d → ℂ) x) = 𝓕 (f : Euclidean d → ℂ) (-x)
  rw [Real.fourier_eq', Real.fourier_eq', ← integral_conj]
  refine integral_congr_ae (.of_forall fun y ↦ ?_)
  have hy : (starRingEnd ℂ) (f y) = f y := Complex.conj_eq_iff_im.mpr (hf y)
  simp [smul_eq_mul, ← Complex.exp_conj, hy, real_inner_comm, map_ofNat]

end

noncomputable section

open Filter Function MeasureTheory Metric Real Set
open scoped FourierTransform SchwartzMap Topology ENNReal

/-! ### The change of variables `r = R e^v` -/

/-- The change of variables `r = R e^v` maps `ℝ` bijectively onto `(0, ∞)`, with derivative
`R e^v`. -/
theorem mul_exp_changeOfVariables {R : ℝ} (hR : 0 < R) :
    (fun v : ℝ ↦ R * exp v) '' univ = Ioi 0 ∧
      (∀ x ∈ (univ : Set ℝ), HasDerivWithinAt (fun v : ℝ ↦ R * exp v) (R * exp x) univ x) ∧
      InjOn (fun v : ℝ ↦ R * exp v) univ := by
  refine ⟨?_, fun x _ ↦ ((hasDerivAt_exp x).const_mul R).hasDerivWithinAt,
    fun x _ y _ h ↦ exp_injective (mul_left_cancel₀ hR.ne' h)⟩
  ext r
  constructor
  · rintro ⟨v, -, rfl⟩
    exact mul_pos hR (exp_pos v)
  · refine fun hr ↦ ⟨log (r / R), mem_univ _, ?_⟩
    change R * exp (log (r / R)) = r
    rw [exp_log (div_pos hr hR)]
    field_simp

/-- Change of variables `r = R e^v` in an integral over `(0, ∞)`. -/
theorem integral_scaled_exp_change_Ioi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 < R) (f : ℝ → E) :
    (∫ r : ℝ in Ioi 0, f r) = ∫ v : ℝ, (R * exp v) • f (R * exp v) := by
  obtain ⟨himage, hderiv, hinj⟩ := mul_exp_changeOfVariables hR
  simpa [himage, abs_of_pos (mul_pos hR (exp_pos _))] using
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hderiv hinj f

/-- Integrability under the change of variables `r = R e^v`. -/
theorem integrable_scaled_exp_change_Ioi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 < R) (f : ℝ → E) :
    IntegrableOn f (Ioi 0) ↔ Integrable (fun v : ℝ ↦ (R * Real.exp v) • f (R * Real.exp v)) := by
  obtain ⟨himage, hderiv, hinj⟩ := mul_exp_changeOfVariables hR
  simpa [himage, abs_of_pos (mul_pos hR (exp_pos _))] using
    integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hderiv hinj f

/-- The change of variables `r = R e^v` maps `(-∞, 0)` onto `(0, R)`. -/
theorem image_mul_exp_Iio {R : ℝ} (hR : 0 < R) : (fun v : ℝ ↦ R * exp v) '' Iio 0 = Ioo 0 R := by
  ext r
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨mul_pos hR (exp_pos v), mul_lt_of_lt_one_right hR (exp_lt_one_iff.2 hv)⟩
  · rintro ⟨hr, hrR⟩
    refine ⟨log (r / R), log_neg (div_pos hr hR) ((div_lt_one hR).2 hrR), ?_⟩
    change R * exp (log (r / R)) = r
    rw [exp_log (div_pos hr hR)]
    field_simp

/-- Change of variables `r = R e^v` in an integral over `(0, R)`. -/
theorem setIntegral_Ioo_scaled_exp_change {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 < R) (f : ℝ → E) :
    (∫ r : ℝ in Ioo 0 R, f r) = ∫ v : ℝ in Iio 0, (R * exp v) • f (R * exp v) := by
  obtain ⟨-, hderiv, hinj⟩ := mul_exp_changeOfVariables hR
  rw [← image_mul_exp_Iio hR, integral_image_eq_integral_abs_deriv_smul measurableSet_Iio
    (fun x _ ↦ (hderiv x (mem_univ x)).mono (subset_univ _)) (hinj.mono (subset_univ _)) f]
  exact setIntegral_congr_fun measurableSet_Iio fun v _ ↦ by
    rw [abs_of_pos (mul_pos hR (exp_pos v))]

end

noncomputable section

open Asymptotics Filter Function MeasureTheory Metric Real Set
open scoped FourierTransform SchwartzMap Topology

/-! ### The exponential tilt of a Schwartz function on the line -/

/-- The exponential change of variables turns Mellin convergence at `κ` into integrability of
the tilted function `v ↦ e^{κ v} h(R e^v)`. -/
theorem integrable_exp_tilt_of_mellinConvergent {h : ℝ → ℂ} {κ R : ℝ} (hR : 0 < R)
    (hconv : MellinConvergent h (κ : ℂ)) :
    Integrable fun v : ℝ ↦ (exp (κ * v) : ℂ) * h (R * exp v) := by
  have hchange :=
    (integrable_scaled_exp_change_Ioi (R := (1 : ℝ)) one_pos fun r : ℝ ↦
      (r : ℂ) ^ ((κ : ℂ) - 1) • h (R * r)).mp ((MellinConvergent.comp_mul_left hR).mpr hconv)
  have hpower (v : ℝ) : (exp v : ℂ) * (exp v : ℂ) ^ ((κ : ℂ) - 1) = (exp (κ * v) : ℂ) := by
    have hreal : exp v * exp v ^ (κ - 1) = exp (κ * v) := by
      rw [← Real.exp_mul, ← Real.exp_add, show v + v * (κ - 1) = κ * v by ring]
    rw [← hreal, Complex.ofReal_mul, Complex.ofReal_cpow (exp_pos v).le]
    push_cast
    ring
  refine hchange.congr (.of_forall fun v ↦ ?_)
  simp only [one_mul, smul_eq_mul, Complex.real_smul]
  rw [← mul_assoc, hpower]

theorem schwartzRealLine_mellinConvergent_of_re_pos (g : 𝓢(ℝ, ℂ)) (s : ℂ) (hs : 0 < s.re) :
    MellinConvergent (g : ℝ → ℂ) s := by
  obtain ⟨C, -, hdecay⟩ := g.decay 0 0
  refine mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := (0 : ℝ))
    (g.continuous.locallyIntegrable.locallyIntegrableOn _) ?_ (by linarith)
    (IsBigO.of_bound C (.of_forall fun r ↦ by simpa using hdecay r)) hs
  refine ((g.isBigO_cocompact_rpow (-(s.re + 1))).mono atTop_le_cocompact).congr'
    (.of_forall fun _ ↦ rfl) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  simp [Real.norm_eq_abs, abs_of_pos hr]

/-- The exponentially tilted profile `v ↦ e^{κ v} g(R e^v)` of a Schwartz function on `ℝ`. -/
def schwartzExponentialTilt (g : 𝓢(ℝ, ℂ)) (κ R v : ℝ) : ℂ :=
  (Real.exp (κ * v) : ℂ) * g (R * Real.exp v)

theorem schwartzExponentialTilt_integrable (g : 𝓢(ℝ, ℂ)) {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R) :
    Integrable (schwartzExponentialTilt g κ R) :=
  integrable_exp_tilt_of_mellinConvergent hR
    (schwartzRealLine_mellinConvergent_of_re_pos g (κ : ℂ) (by simpa using hκ))

theorem schwartzExponentialTilt_differentiable (g : 𝓢(ℝ, ℂ)) (κ R : ℝ) :
    Differentiable ℝ (schwartzExponentialTilt g κ R) :=
  (Complex.ofRealCLM.differentiable.comp
    (by fun_prop : Differentiable ℝ fun v : ℝ ↦ exp (κ * v))).mul
      (((g.smooth 1).differentiable (by norm_num)).comp
        (by fun_prop : Differentiable ℝ fun v : ℝ ↦ R * exp v))

theorem schwartzExponentialTilt_deriv (g : 𝓢(ℝ, ℂ)) (κ R : ℝ) :
    deriv (schwartzExponentialTilt g κ R) = fun v ↦ (κ : ℂ) * schwartzExponentialTilt g κ R v +
      (R : ℂ) * schwartzExponentialTilt ((SchwartzMap.derivCLM ℂ ℂ) g) (κ + 1) R v := by
  funext v
  have hlinear : HasDerivAt (fun u : ℝ ↦ κ * u) κ v := by
    simpa using (hasDerivAt_id v).const_mul κ
  have hexpreal : HasDerivAt (fun u : ℝ ↦ exp (κ * u)) (κ * exp (κ * v)) v := by
    convert! (Real.hasDerivAt_exp (κ * v)).comp v hlinear using 1
    simp [mul_comm]
  have hprofile : HasDerivAt (fun u : ℝ ↦ g (R * Real.exp u))
      ((R * exp v) • deriv (g : ℝ → ℂ) (R * exp v)) v := by
    simpa [Function.comp_def] using
      (g.hasDerivAt (R * exp v)).scomp v ((Real.hasDerivAt_exp v).const_mul R)
  change deriv ((fun u : ℝ ↦ (Real.exp (κ * u) : ℂ)) * fun u : ℝ ↦ g (R * Real.exp u)) v = _
  rw [(hexpreal.ofReal_comp.mul hprofile).deriv]
  simp [schwartzExponentialTilt, SchwartzMap.derivCLM_apply, Complex.real_smul,
    show exp ((κ + 1) * v) = exp (κ * v) * exp v by rw [← Real.exp_add]; congr 1; ring]
  ring

theorem schwartzExponentialTilt_deriv_integrable (g : 𝓢(ℝ, ℂ)) {κ R : ℝ} (hκ : 0 < κ)
    (hR : 0 < R) : Integrable (deriv (schwartzExponentialTilt g κ R)) := by
  rw [schwartzExponentialTilt_deriv]
  exact ((schwartzExponentialTilt_integrable g hκ hR).const_mul _).add
    ((schwartzExponentialTilt_integrable _ (by linarith : (0 : ℝ) < κ + 1) hR).const_mul _)

theorem schwartzExponentialTilt_deriv_differentiable (g : 𝓢(ℝ, ℂ)) (κ R : ℝ) :
    Differentiable ℝ (deriv (schwartzExponentialTilt g κ R)) := by
  rw [schwartzExponentialTilt_deriv]
  exact ((schwartzExponentialTilt_differentiable g κ R).const_mul _).add
    ((schwartzExponentialTilt_differentiable _ (κ + 1) R).const_mul _)

theorem schwartzExponentialTilt_deriv_deriv (g : 𝓢(ℝ, ℂ)) (κ R : ℝ) :
    deriv (deriv (schwartzExponentialTilt g κ R)) = fun v ↦
      (κ : ℂ) * deriv (schwartzExponentialTilt g κ R) v +
        (R : ℂ) * deriv (schwartzExponentialTilt ((SchwartzMap.derivCLM ℂ ℂ) g) (κ + 1) R) v := by
  conv_lhs => rw [schwartzExponentialTilt_deriv]
  funext v
  change deriv ((fun u : ℝ ↦ (κ : ℂ) * schwartzExponentialTilt g κ R u) +
    fun u : ℝ ↦ (R : ℂ) * schwartzExponentialTilt ((SchwartzMap.derivCLM ℂ ℂ) g) (κ + 1) R u) v = _
  rw [deriv_add ((schwartzExponentialTilt_differentiable g κ R).const_mul (κ : ℂ) v)
      ((schwartzExponentialTilt_differentiable _ (κ + 1) R).const_mul (R : ℂ) v),
    deriv_const_mul_field (κ : ℂ), deriv_const_mul_field (R : ℂ)]

theorem schwartzExponentialTilt_deriv_deriv_integrable (g : 𝓢(ℝ, ℂ)) {κ R : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) :
    Integrable (deriv (deriv (schwartzExponentialTilt g κ R))) := by
  rw [schwartzExponentialTilt_deriv_deriv]
  exact ((schwartzExponentialTilt_deriv_integrable g hκ hR).const_mul _).add
    ((schwartzExponentialTilt_deriv_integrable _ (by linarith : (0 : ℝ) < κ + 1) hR).const_mul _)

theorem schwartzExponentialTilt_fourier_integrable (g : 𝓢(ℝ, ℂ)) {κ R : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) :
    Integrable (𝓕 (schwartzExponentialTilt g κ R) : ℝ → ℂ) :=
  Real.integrable_fourierIntegral_of_deriv_deriv (schwartzExponentialTilt g κ R)
    (schwartzExponentialTilt_integrable g hκ hR)
    (schwartzExponentialTilt_differentiable g κ R)
    (schwartzExponentialTilt_deriv_integrable g hκ hR)
    (schwartzExponentialTilt_deriv_differentiable g κ R)
    (schwartzExponentialTilt_deriv_deriv_integrable g hκ hR)

/-- The Fourier transform commutes with multiplication by a constant. -/
theorem fourier_const_mul (c : ℂ) (F : ℝ → ℂ) :
    (𝓕 (fun v : ℝ ↦ c * F v) : ℝ → ℂ) = fun t ↦ c * (𝓕 F : ℝ → ℂ) t :=
  VectorFourier.fourierIntegral_const_smul _ _ _ _ _

end

end CohnElkies
