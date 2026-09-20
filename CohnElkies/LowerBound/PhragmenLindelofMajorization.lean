import CohnElkies.LowerBound.CappedMajorization
import CohnElkies.LowerBound.LimitingDensity
import CohnElkiesForMathlib.Analysis.Complex.PhragmenLindelof

/-!
# The Poisson principle in the strip by Phragmén–Lindelöf (an alternative proof of Lemma 3.2)

A second proof of the Poisson principle for the strip, `norm_le_exp_integral_P_σ_of_strip` of
`CohnElkies.LowerBound.CappedMajorization`, which stays inside the strip instead of passing to the
upper half-plane as the report does. It is proved here in the more general form
`norm_le_exp_integral_P_σ_of_strip_of_isBigO`: for `Z` holomorphic on the strip `|Im z| < ℓ`,
continuous on its closure and of Phragmén–Lindelöf growth `O(exp(B e^{c |Re z|}))` with
`c < π/(2ℓ)`, with `‖Z‖ ≤ e^{b}` on the bottom edge for a continuous, linearly bounded profile `b`
and `‖Z‖ ≤ 1` on the top edge, `‖Z(s + iσℓ)‖ ≤ exp (∫ P_σ(T) b(s − ℓT) dT)` at every interior
point. The proof applies the Phragmén–Lindelöf principle to `Z e^{-W[b]}`, where `W[b]` is the
holomorphic Poisson integral of `b` built from the strip kernel `K'_ℓ`: it controls `Re W[b]` far
away (linear growth in `Re z`, from the uniform first-moment bound on the kernels `P_σ`),
identifies its traces `b` and `0` on the two edges, and uses the continuous extension of
`|Z e^{-W[b]}|` to the closed strip.

The bounded case `norm_le_exp_integral_P_σ_of_strip_phragmenLindelof` is the statement of
`norm_le_exp_integral_P_σ_of_strip`, and `norm_Z_g_le_exp_integral_of_cap_phragmenLindelof`,
`exists_capped_poisson_majorization_phragmenLindelof` re-derive Lemma 3.2 of the report from it.
Nothing in this module is used by the rest of the development.
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology

/-! ### The uniform first-moment bound on the kernels `P_σ` -/


/-- For `0 ≤ σ < 1` the kernel `P_σ` is below the `σ`-uniform exponential majorant. -/
theorem P_σ_le_exponentialMajorant {σ : ℝ} (hσ : 0 ≤ σ) (habove : σ < 1) (T : ℝ) :
    P_σ σ T ≤ stripPoissonExponentialMajorant T := by
  obtain ⟨hnonneg, hle⟩ := stripNormalizedPoissonExtension_le_majorant hσ habove.le T
  have hmass := stripBottomMass_pos habove
  have hP : P_σ σ T = M_σ σ * stripNormalizedPoissonExtension σ T := by
    rw [← stripNormalizedPoissonKernel_eq_extension (by linarith) habove T,
      stripNormalizedPoissonKernel]
    field_simp
  nlinarith [mul_nonneg (sub_nonneg.mpr (stripBottomMass_lt_one (by linarith : -1 < σ)).le) hnonneg]

theorem integrable_exponentialMajorant_mul_abs :
    Integrable fun T : ℝ ↦ stripPoissonExponentialMajorant T * |T| := by
  convert! (integrable_abs_pow_mul_exp_neg_mul_abs 1 (half_pos Real.pi_pos)).const_mul (π / 2)
    using 1
  ext T
  simp only [stripPoissonExponentialMajorant, pow_one]
  ring

theorem integrable_P_σ_mul_abs_of_nonneg {σ : ℝ} (hσ : 0 ≤ σ) (habove : σ < 1) :
    Integrable fun T : ℝ ↦ P_σ σ T * |T| := by
  have hmeas : Measurable fun T : ℝ ↦ P_σ σ T * |T| := by unfold P_σ θ; fun_prop
  refine integrable_exponentialMajorant_mul_abs.mono' hmeas.aestronglyMeasurable
    (.of_forall fun T ↦ ?_)
  have hpos := stripPoissonKernel_pos (by linarith) habove T
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hpos.le (abs_nonneg T))]
  exact mul_le_mul_of_nonneg_right (P_σ_le_exponentialMajorant hσ habove T) (abs_nonneg T)

/-- The first absolute moment of `P_σ` is finite throughout the strip. -/
theorem integrable_P_σ_mul_abs {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) :
    Integrable fun T : ℝ ↦ P_σ σ T * |T| :=
  (le_or_gt σ 0).elim
    (fun hσ ↦ stripPoissonKernel_lower_product_integrable hbelow hσ continuous_abs
      (integrable_P_σ_mul_abs_of_nonneg le_rfl one_pos))
    (fun hσ ↦ integrable_P_σ_mul_abs_of_nonneg hσ.le habove)

/-- Report Lemma 3.2: the first absolute moments `∫ P_σ(T) |T| dT` are bounded uniformly in
`-1 < σ < 1`; for `σ ≤ 0` one compares with `P_0` away from the origin, for `σ ≥ 0` with the
exponential majorant. -/
theorem exists_integral_P_σ_mul_abs_le :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ σ : ℝ, -1 < σ → σ < 1 → (∫ T : ℝ, P_σ σ T * |T|) ≤ M := by
  obtain ⟨C, hC, hCle⟩ : ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, -1 < σ → σ ≤ 0 → 1 ≤ |T| →
      P_σ σ T ≤ C * P_σ 0 T := by
    have hinv := (inv_lt_one₀ (Real.cosh_pos (π / 2))).mpr
      (Real.one_lt_cosh.mpr (half_pos Real.pi_pos).ne')
    exact ⟨1 / (1 - (Real.cosh (π / 2))⁻¹), one_div_pos.mpr (by linarith),
      fun σ T hbelow hσ hT ↦ by
        simpa using stripPoissonKernel_le_center_of_lower_of_abs_ge hbelow hσ one_pos hT⟩
  have hcenter : Integrable fun T : ℝ ↦ P_σ 0 T * |T| :=
    integrable_P_σ_mul_abs_of_nonneg le_rfl one_pos
  have hJ : 0 ≤ ∫ T : ℝ, P_σ 0 T * |T| := integral_nonneg fun T ↦
    mul_nonneg (stripPoissonKernel_pos (by norm_num) one_pos T).le (abs_nonneg T)
  have hE : 0 ≤ ∫ T : ℝ, stripPoissonExponentialMajorant T * |T| := integral_nonneg fun T ↦ by
    unfold stripPoissonExponentialMajorant; positivity
  refine ⟨1 + C * (∫ T : ℝ, P_σ 0 T * |T|) + ∫ T : ℝ, stripPoissonExponentialMajorant T * |T|,
    by positivity, fun σ hbelow habove ↦ ?_⟩
  have hmoment : Integrable fun T : ℝ ↦ P_σ σ T * |T| := integrable_P_σ_mul_abs hbelow habove
  rcases le_or_gt σ 0 with hσ | hσ
  · have hk : Integrable (P_σ σ) := stripPoissonKernel_integrable hbelow habove
    have hscaled : Integrable fun T : ℝ ↦ C * (P_σ 0 T * |T|) := hcenter.const_mul C
    have hS : MeasurableSet {T : ℝ | 1 ≤ |T|} :=
      (isClosed_le continuous_const continuous_abs).measurableSet
    have hfar : (∫ T in {T : ℝ | 1 ≤ |T|}, P_σ σ T * |T|) ≤ C * ∫ T : ℝ, P_σ 0 T * |T| := by
      calc (∫ T in {T : ℝ | 1 ≤ |T|}, P_σ σ T * |T|)
          ≤ ∫ T in {T : ℝ | 1 ≤ |T|}, C * (P_σ 0 T * |T|) :=
            setIntegral_mono_on hmoment.integrableOn hscaled.integrableOn hS fun T hT ↦ by
              simpa [mul_assoc] using mul_le_mul_of_nonneg_right (hCle σ T hbelow hσ hT)
                (abs_nonneg T)
        _ ≤ ∫ T : ℝ, C * (P_σ 0 T * |T|) := setIntegral_le_integral hscaled
            (.of_forall fun T ↦ mul_nonneg hC.le (mul_nonneg
              (stripPoissonKernel_pos (by norm_num) one_pos T).le (abs_nonneg T)))
        _ = C * ∫ T : ℝ, P_σ 0 T * |T| := integral_const_mul _ _
    have hnear : (∫ T in {T : ℝ | 1 ≤ |T|}ᶜ, P_σ σ T * |T|) ≤ 1 := by
      calc (∫ T in {T : ℝ | 1 ≤ |T|}ᶜ, P_σ σ T * |T|) ≤ ∫ T in {T : ℝ | 1 ≤ |T|}ᶜ, P_σ σ T :=
            setIntegral_mono_on hmoment.integrableOn hk.integrableOn hS.compl fun T hT ↦ by
              have hT' : |T| ≤ 1 := le_of_lt (not_le.mp hT)
              nlinarith [(stripPoissonKernel_pos hbelow habove T).le]
        _ ≤ ∫ T : ℝ, P_σ σ T := setIntegral_le_integral hk
            (.of_forall fun T ↦ (stripPoissonKernel_pos hbelow habove T).le)
        _ = M_σ σ := integral_stripPoissonKernel hbelow habove
        _ ≤ 1 := (stripBottomMass_lt_one hbelow).le
    linarith [integral_add_compl hS hmoment]
  · linarith [integral_mono hmoment integrable_exponentialMajorant_mul_abs fun T ↦
      mul_le_mul_of_nonneg_right (P_σ_le_exponentialMajorant hσ.le habove T) (abs_nonneg T),
      mul_nonneg hC.le hJ]

/-! ### The holomorphic Poisson integral `W[b]` and the Phragmén–Lindelöf argument -/

/-- A continuous profile with `|b y| ≤ A (1 + |y|)` has integrable exponential weights
`e^{-a|y|} b(y)` for `a > 0`; this is the integrability of the boundary datum required by `W[b]`. -/
theorem integrable_exp_neg_mul_abs_mul_of_abs_le {a : ℝ} (ha : 0 < a) {b : ℝ → ℝ}
    (hb : Continuous b) {A : ℝ} (hbound : ∀ y : ℝ, |b y| ≤ A * (1 + |y|)) :
    Integrable fun y : ℝ ↦ Real.exp (-a * |y|) * b y := by
  have hmajor : Integrable fun y : ℝ ↦
      A * Real.exp (-a * |y|) + A * (|y| ^ 1 * Real.exp (-a * |y|)) :=
    ((integrable_exp_neg_mul_abs ha).const_mul A).add
      ((integrable_abs_pow_mul_exp_neg_mul_abs 1 ha).const_mul A)
  refine hmajor.mono' ((by fun_prop : Continuous fun y : ℝ ↦ Real.exp (-a * |y|)).mul
    hb).aestronglyMeasurable (.of_forall fun y ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), pow_one]
  calc Real.exp (-a * |y|) * |b y| ≤ Real.exp (-a * |y|) * (A * (1 + |y|)) := by
        gcongr; exact hbound y
    _ = A * Real.exp (-a * |y|) + A * (|y| * Real.exp (-a * |y|)) := by ring

/-- `W[b]` is holomorphic on the open strip `|Im z| < ℓ` for every continuous profile `b` with
`|b y| ≤ A (1 + |y|)`. -/
theorem differentiableOn_W_b {ℓ : ℝ} (hℓ : 0 < ℓ) {b : ℝ → ℝ} (hb : Continuous b) {A : ℝ}
    (hbound : ∀ y : ℝ, |b y| ≤ A * (1 + |y|)) :
    DifferentiableOn ℂ (W_b ℓ b) (Complex.im ⁻¹' Ioo (-ℓ) ℓ) := fun z hz ↦
  (differentiableAt_W_b hℓ hz b hb
    (integrable_exp_neg_mul_abs_mul_of_abs_le (by positivity) hb hbound)).differentiableWithinAt

/-- A point of the open strip `|Im z| < ℓ` has normalized height `Im z / ℓ ∈ (-1, 1)`. -/
theorem im_div_mem_Ioo_of_mem_strip {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) : -1 < z.im / ℓ ∧ z.im / ℓ < 1 :=
  ⟨(lt_div_iff₀ hℓ).2 (by simpa using hz.1), (div_lt_iff₀ hℓ).2 (by simpa using hz.2)⟩

/-- On the open strip `Re W[b](z) = ∫ P_σ(T) b(Re z − ℓT) dT` with `σ = Im z / ℓ`; report (16). -/
theorem W_b_re_of_mem_strip {ℓ : ℝ} (hℓ : 0 < ℓ) {b : ℝ → ℝ} (hb : Continuous b) {A : ℝ}
    (hbound : ∀ y : ℝ, |b y| ≤ A * (1 + |y|)) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) :
    (W_b ℓ b z).re = ∫ T : ℝ, P_σ (z.im / ℓ) T * b (z.re - ℓ * T) := by
  obtain ⟨hbelow, habove⟩ := im_div_mem_Ioo_of_mem_strip hℓ hz
  have hzeq : (z.re : ℂ) + I * ((z.im / ℓ : ℝ) * ℓ : ℂ) = z :=
    Complex.ext (by simp) (by simp [hℓ.ne'])
  have h := W_b_re hℓ hbelow habove z.re b (integrable_K'_ℓ_mul hℓ (by rw [hzeq]; exact hz) b hb
    (integrable_exp_neg_mul_abs_mul_of_abs_le (by positivity) hb hbound))
  rwa [hzeq] at h

/-- The Poisson integrand of a linearly bounded profile is dominated by the kernel and its first
moment: `|P_σ(T) b(x − ℓT)| ≤ A (1 + |x|) P_σ(T) + A ℓ P_σ(T) |T|`. -/
theorem norm_P_σ_mul_le_of_abs_le {ℓ σ : ℝ} (hℓ : 0 < ℓ) (hbelow : -1 < σ) (habove : σ < 1)
    {b : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A) (hbound : ∀ y : ℝ, |b y| ≤ A * (1 + |y|)) (x T : ℝ) :
    ‖P_σ σ T * b (x - ℓ * T)‖ ≤ A * (1 + |x|) * P_σ σ T + A * ℓ * (P_σ σ T * |T|) := by
  have hkpos := stripPoissonKernel_pos hbelow habove T
  have hb : |b (x - ℓ * T)| ≤ A * (1 + |x| + ℓ * |T|) := by
    refine (hbound _).trans (mul_le_mul_of_nonneg_left ?_ hA)
    have habs := abs_sub x (ℓ * T)
    rw [abs_mul, abs_of_pos hℓ] at habs
    linarith
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos hkpos, Real.norm_eq_abs]
  nlinarith [mul_nonneg hkpos.le (sub_nonneg.mpr hb)]

/-- The Poisson integrand of a continuous, linearly bounded profile is integrable on every
horizontal line `-1 < σ < 1` of the strip. -/
theorem integrable_P_σ_mul_of_abs_le {ℓ σ : ℝ} (hℓ : 0 < ℓ) (hbelow : -1 < σ) (habove : σ < 1)
    {b : ℝ → ℝ} (hb : Continuous b) {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ y : ℝ, |b y| ≤ A * (1 + |y|)) (x : ℝ) :
    Integrable fun T : ℝ ↦ P_σ σ T * b (x - ℓ * T) := by
  have hmeas : Measurable fun T : ℝ ↦ P_σ σ T * b (x - ℓ * T) :=
    (by unfold P_σ θ; fun_prop : Measurable fun T : ℝ ↦ P_σ σ T).mul
      (hb.measurable.comp (by fun_prop))
  exact (((stripPoissonKernel_integrable hbelow habove).const_mul _).add
    ((integrable_P_σ_mul_abs hbelow habove).const_mul _)).mono' hmeas.aestronglyMeasurable
    (.of_forall fun T ↦ norm_P_σ_mul_le_of_abs_le hℓ hbelow habove hA hbound x T)

/-- Report Lemma 3.2: `Re W[b](z) = ∫ P_σ(T) b(Re z − ℓT) dT` grows at most linearly in `Re z`,
uniformly on the open strip `|Im z| < ℓ`, when `|b y| ≤ A (1 + |y|)`: the mass `M_σ ≤ 1` and the
first absolute moments of the kernels are bounded uniformly in `σ`. -/
theorem exists_abs_W_b_re_le {ℓ : ℝ} (hℓ : 0 < ℓ) {b : ℝ → ℝ} (hb : Continuous b) {A : ℝ}
    (hA : 0 ≤ A) (hbound : ∀ y : ℝ, |b y| ≤ A * (1 + |y|)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ →
      |(W_b ℓ b z).re| ≤ B * (1 + |z.re|) := by
  obtain ⟨M, hM, hmoment⟩ := exists_integral_P_σ_mul_abs_le
  refine ⟨A * (1 + ℓ * M), by positivity, fun z hz ↦ ?_⟩
  obtain ⟨hbelow, habove⟩ := im_div_mem_Ioo_of_mem_strip hℓ hz
  have hconstant : Integrable fun T : ℝ ↦ A * (1 + |z.re|) * P_σ (z.im / ℓ) T :=
    (stripPoissonKernel_integrable hbelow habove).const_mul _
  have hlinear : Integrable fun T : ℝ ↦ A * ℓ * (P_σ (z.im / ℓ) T * |T|) :=
    (integrable_P_σ_mul_abs hbelow habove).const_mul _
  rw [W_b_re_of_mem_strip hℓ hb hbound hz]
  calc |∫ T : ℝ, P_σ (z.im / ℓ) T * b (z.re - ℓ * T)|
      ≤ ∫ T : ℝ, (A * (1 + |z.re|) * P_σ (z.im / ℓ) T + A * ℓ * (P_σ (z.im / ℓ) T * |T|)) := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_of_norm_le (hconstant.add hlinear)
          (.of_forall fun T ↦ norm_P_σ_mul_le_of_abs_le hℓ hbelow habove hA hbound z.re T)
    _ = A * (1 + |z.re|) * M_σ (z.im / ℓ) + A * ℓ * ∫ T : ℝ, P_σ (z.im / ℓ) T * |T| := by
        rw [integral_add hconstant hlinear, integral_const_mul, integral_const_mul,
          integral_stripPoissonKernel hbelow habove]
    _ ≤ A * (1 + ℓ * M) * (1 + |z.re|) := by
        have h₁ := mul_le_mul_of_nonneg_left (stripBottomMass_lt_one hbelow).le
          (by positivity : (0 : ℝ) ≤ A * (1 + |z.re|))
        have h₂ := mul_le_mul_of_nonneg_left (hmoment _ hbelow habove)
          (by positivity : (0 : ℝ) ≤ A * ℓ)
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hA hℓ.le) hM) (abs_nonneg z.re)]

/-- Report Lemma 3.2: if `Z` has the Phragmén–Lindelöf growth `Z = O(exp (B e^{c |Re z|}))` on
the strip `|Im z| < ℓ` for some `c < π/(2ℓ)`, so does `e^{-W[b]} Z`: the linear bound
`|Re W[b](z)| ≤ G (1 + |Re z|)` costs a factor `exp (G (1 + 1/c') e^{c' |Re z|})` for any
`c' > 0`, and one may take `c' = max c (π/(4ℓ))`. -/
theorem isBigO_exp_neg_W_b_mul {ℓ : ℝ} (hℓ : 0 < ℓ) {b : ℝ → ℝ} (hb : Continuous b) {A : ℝ}
    (hA : 0 ≤ A) (hbound : ∀ y : ℝ, |b y| ≤ A * (1 + |y|)) {Z : ℂ → ℂ}
    (hgrowth : ∃ c < π / (2 * ℓ), ∃ B : ℝ, Z =O[comap (fun z : ℂ ↦ |z.re|) atTop ⊓
      𝓟 (Complex.im ⁻¹' Ioo (-ℓ) ℓ)] fun z : ℂ ↦ Real.exp (B * Real.exp (c * |z.re|))) :
    ∃ c < π / (2 * ℓ), ∃ B : ℝ,
      (fun z : ℂ ↦ Complex.exp (-(W_b ℓ b z)) * Z z) =O[comap (fun z : ℂ ↦ |z.re|) atTop ⊓
        𝓟 (Complex.im ⁻¹' Ioo (-ℓ) ℓ)] fun z : ℂ ↦ Real.exp (B * Real.exp (c * |z.re|)) := by
  obtain ⟨c, hc, B, hO⟩ := hgrowth
  obtain ⟨G, hG, houter⟩ := exists_abs_W_b_re_le hℓ hb hA hbound
  obtain ⟨c', hcc', hc'pos, hc'lt⟩ : ∃ c' : ℝ, c ≤ c' ∧ 0 < c' ∧ c' < π / (2 * ℓ) :=
    ⟨max c (π / (4 * ℓ)), le_max_left _ _, lt_max_of_lt_right (by positivity),
      max_lt hc ((div_lt_div_iff_of_pos_left Real.pi_pos (by positivity) (by positivity)).2
        (by linarith))⟩
  refine ⟨c', hc'lt, G * (1 + 1 / c') + max B 0, ?_⟩
  have hexp : ∀ z : ℂ, G * (1 + |z.re|) ≤ G * (1 + 1 / c') * Real.exp (c' * |z.re|) := fun z ↦ by
    have hlin : 1 + |z.re| ≤ (1 + 1 / c') * (1 + c' * |z.re|) := by
      have hrecip : 1 / c' * (c' * |z.re|) = |z.re| := by
        rw [← mul_assoc, one_div_mul_cancel hc'pos.ne', one_mul]
      linarith [mul_nonneg hc'pos.le (abs_nonneg z.re), one_div_pos.mpr hc'pos]
    calc G * (1 + |z.re|) ≤ G * ((1 + 1 / c') * Real.exp (c' * |z.re|)) :=
          mul_le_mul_of_nonneg_left (hlin.trans (mul_le_mul_of_nonneg_left
            (by simpa [add_comm] using Real.add_one_le_exp (c' * |z.re|)) (by positivity))) hG
      _ = G * (1 + 1 / c') * Real.exp (c' * |z.re|) := by ring
  have houterO : (fun z : ℂ ↦ Complex.exp (-(W_b ℓ b z))) =O[comap (fun z : ℂ ↦ |z.re|) atTop ⊓
      𝓟 (Complex.im ⁻¹' Ioo (-ℓ) ℓ)]
        fun z : ℂ ↦ Real.exp (G * (1 + 1 / c') * Real.exp (c' * |z.re|)) := by
    refine IsBigO.of_bound' (eventually_inf_principal.mpr (.of_forall fun z hz ↦ ?_))
    rw [Complex.norm_exp, Complex.neg_re, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((neg_le_abs _).trans ((houter z hz).trans (hexp z)))
  refine (houterO.mul hO).trans (IsBigO.of_bound' (.of_forall fun z ↦ ?_))
  have hB : B * Real.exp (c * |z.re|) ≤ max B 0 * Real.exp (c' * |z.re|) :=
    (mul_le_mul_of_nonneg_right (le_max_left B 0) (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hcc' (abs_nonneg _))) (le_max_right B 0))
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _),
    ← Real.exp_add, add_mul]
  exact Real.exp_le_exp.mpr (by linarith)

/-- Boundary traces at the bottom edge `Im z = -ℓ`: the abscissa converges to `s`, the normalized
height `Im z / ℓ` to `-1`, and the latter eventually lies in `(-1, 0]`. -/
theorem tendsto_bottom_edge {ℓ : ℝ} (hℓ : 0 < ℓ) (s : ℝ) :
    Tendsto Complex.re (𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ] ((s : ℂ) - I * (ℓ : ℂ))) (𝓝 s) ∧
      Tendsto (fun z : ℂ ↦ z.im / ℓ)
          (𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ] ((s : ℂ) - I * (ℓ : ℂ))) (𝓝 (-1 : ℝ)) ∧
      ∀ᶠ z : ℂ in 𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ] ((s : ℂ) - I * (ℓ : ℂ)),
        -1 < z.im / ℓ ∧ z.im / ℓ ≤ 0 := by
  have hre : Tendsto Complex.re
      (𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ] ((s : ℂ) - I * (ℓ : ℂ))) (𝓝 s) := by
    simpa using (Complex.continuous_re.tendsto ((s : ℂ) - I * (ℓ : ℂ))).mono_left
      nhdsWithin_le_nhds
  have hσ : Tendsto (fun z : ℂ ↦ z.im / ℓ)
      (𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ] ((s : ℂ) - I * (ℓ : ℂ))) (𝓝 (-1 : ℝ)) := by
    simpa [hℓ.ne'] using ((Complex.continuous_im.div_const ℓ).tendsto
      ((s : ℂ) - I * (ℓ : ℂ))).mono_left nhdsWithin_le_nhds
  refine ⟨hre, hσ, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    hσ.eventually (eventually_lt_nhds (by norm_num : (-1 : ℝ) < 0))] with z hz hz'
  exact ⟨(lt_div_iff₀ hℓ).2 (by simpa using hz.1), hz'.le⟩

/-- Dominated convergence at an edge of the strip: if the kernels `P_{σ(z)}` stay below an
integrable `Q` with finite first moment on `S` and tend to `0` pointwise there, then the Poisson
averages over `S` of a linearly bounded profile `b` tend to `0`. -/
theorem tendsto_setIntegral_P_σ_mul {ℓ : ℝ} (hℓ : 0 < ℓ) {b : ℝ → ℝ} (hb : Continuous b)
    {A : ℝ} (hA : 0 ≤ A) (hbound : ∀ y : ℝ, |b y| ≤ A * (1 + |y|))
    {S : Set ℝ} (hS : MeasurableSet S) {Q : ℝ → ℝ} (hQ : Integrable Q)
    (hQmoment : Integrable fun T : ℝ ↦ Q T * |T|) (hQnonneg : ∀ T : ℝ, 0 ≤ Q T)
    {F : Filter ℂ} [F.IsCountablyGenerated] {s : ℝ} (hre : Tendsto Complex.re F (𝓝 s))
    (hker : ∀ᶠ z : ℂ in F, ∀ T : ℝ, 0 ≤ P_σ (z.im / ℓ) T)
    (hdom : ∀ᶠ z : ℂ in F, ∀ T ∈ S, P_σ (z.im / ℓ) T ≤ Q T)
    (hzero : ∀ T ∈ S, Tendsto (fun z : ℂ ↦ P_σ (z.im / ℓ) T) F (𝓝 (0 : ℝ))) :
    Tendsto (fun z : ℂ ↦ ∫ T in S, P_σ (z.im / ℓ) T * b (z.re - ℓ * T)) F (𝓝 (0 : ℝ)) := by
  have hG : Integrable fun T : ℝ ↦ A * (2 + |s|) * Q T + A * ℓ * (Q T * |T|) :=
    (hQ.const_mul _).add (hQmoment.const_mul _)
  have hGnonneg : ∀ T : ℝ, 0 ≤ A * (2 + |s|) * Q T + A * ℓ * (Q T * |T|) := fun T ↦
    add_nonneg (mul_nonneg (mul_nonneg hA (by positivity)) (hQnonneg T))
      (mul_nonneg (mul_nonneg hA hℓ.le) (mul_nonneg (hQnonneg T) (abs_nonneg T)))
  have hmeas : ∀ᶠ z : ℂ in F, AEStronglyMeasurable
      (S.indicator fun T : ℝ ↦ P_σ (z.im / ℓ) T * b (z.re - ℓ * T)) := by
    refine .of_forall fun z ↦ ?_
    have hk : Measurable fun T : ℝ ↦ P_σ (z.im / ℓ) T := by unfold P_σ θ; fun_prop
    exact ((hk.mul (hb.measurable.comp (by fun_prop))).aestronglyMeasurable).indicator hS
  have hdom' : ∀ᶠ z : ℂ in F, ∀ᵐ T : ℝ,
      ‖S.indicator (fun T : ℝ ↦ P_σ (z.im / ℓ) T * b (z.re - ℓ * T)) T‖ ≤
        A * (2 + |s|) * Q T + A * ℓ * (Q T * |T|) := by
    filter_upwards [hker, hdom, hre.eventually (Metric.ball_mem_nhds s one_pos)]
      with z hzker hzdom hzre
    have hzabs : |z.re| ≤ |s| + 1 := by
      have hball : |z.re - s| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using hzre
      have htri := abs_add_le (z.re - s) s
      rw [show z.re - s + s = z.re by ring] at htri
      linarith
    refine .of_forall fun T ↦ ?_
    by_cases hT : T ∈ S
    · rw [Set.indicator_of_mem hT, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (hzker T)]
      have hbT : |b (z.re - ℓ * T)| ≤ A * (2 + |s| + ℓ * |T|) := by
        refine (hbound _).trans (mul_le_mul_of_nonneg_left ?_ hA)
        have habs := abs_sub z.re (ℓ * T)
        rw [abs_mul, abs_of_pos hℓ] at habs
        linarith
      calc P_σ (z.im / ℓ) T * |b (z.re - ℓ * T)| ≤ Q T * (A * (2 + |s| + ℓ * |T|)) :=
            mul_le_mul (hzdom T hT) hbT (abs_nonneg _) (hQnonneg T)
        _ = A * (2 + |s|) * Q T + A * ℓ * (Q T * |T|) := by ring
    · rw [Set.indicator_of_notMem hT, norm_zero]
      exact hGnonneg T
  have hpoint : ∀ᵐ T : ℝ, Tendsto
      (fun z : ℂ ↦ S.indicator (fun T : ℝ ↦ P_σ (z.im / ℓ) T * b (z.re - ℓ * T)) T) F
      (𝓝 (0 : ℝ)) := by
    refine .of_forall fun T ↦ ?_
    by_cases hT : T ∈ S
    · simp_rw [Set.indicator_of_mem hT]
      simpa using (hzero T hT).mul
        ((hb.tendsto (s - ℓ * T)).comp (hre.sub_const (ℓ * T)))
    · simpa [Set.indicator_of_notMem hT] using
        (tendsto_const_nhds : Tendsto (fun _ : ℂ ↦ (0 : ℝ)) F (𝓝 0))
  simpa [integral_indicator hS] using MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (f := fun _ : ℝ ↦ (0 : ℝ))
    (fun T : ℝ ↦ A * (2 + |s|) * Q T + A * ℓ * (Q T * |T|)) hmeas hdom' hG hpoint

/-- Report Lemma 3.4: away from `T = 0` the Poisson averages vanish at the bottom edge `σ → -1`,
where the kernels are dominated by a multiple of the central kernel `P_0`. -/
theorem tendsto_integral_far_bottom {ℓ : ℝ} (hℓ : 0 < ℓ) {b : ℝ → ℝ} (hb : Continuous b)
    {A : ℝ} (hA : 0 ≤ A) (hbound : ∀ y : ℝ, |b y| ≤ A * (1 + |y|)) (s : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun z : ℂ ↦ ∫ T in {T : ℝ | δ ≤ |T|}, P_σ (z.im / ℓ) T * b (z.re - ℓ * T))
      (𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ] ((s : ℂ) - I * (ℓ : ℂ))) (𝓝 (0 : ℝ)) := by
  have hCpos : 0 < 1 - (Real.cosh (π * δ / 2))⁻¹ := by
    have hinv := (inv_lt_one₀ (Real.cosh_pos (π * δ / 2))).mpr
      (Real.one_lt_cosh.mpr (div_pos (mul_pos Real.pi_pos hδ) two_pos).ne')
    linarith
  obtain ⟨C, hC, hCle⟩ : ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, -1 < σ → σ ≤ 0 → δ ≤ |T| →
      P_σ σ T ≤ C * P_σ 0 T :=
    ⟨1 / (1 - (Real.cosh (π * δ / 2))⁻¹), one_div_pos.mpr hCpos,
      fun σ T hbelow hσ hT ↦ stripPoissonKernel_le_center_of_lower_of_abs_ge hbelow hσ hδ hT⟩
  obtain ⟨hre, hσ, hrange⟩ := tendsto_bottom_edge hℓ s
  refine tendsto_setIntegral_P_σ_mul hℓ hb hA hbound
    (isClosed_le continuous_const continuous_abs).measurableSet
    ((stripPoissonKernel_integrable (by norm_num) one_pos).const_mul C)
    (by simpa [mul_assoc] using (integrable_P_σ_mul_abs_of_nonneg le_rfl one_pos).const_mul C)
    (fun T ↦ mul_nonneg hC.le (stripPoissonKernel_pos (by norm_num) one_pos T).le) hre
    (hrange.mono fun z hz T ↦ (stripPoissonKernel_pos hz.1 (by linarith [hz.2]) T).le)
    (hrange.mono fun z hz T hT ↦ hCle _ T hz.1 hz.2 hT) fun T hT ↦ ?_
  refine (stripPoissonKernel_tendsto_zero_bottom_of_ne ?_).comp hσ
  rintro rfl
  simp only [Set.mem_ofPred_eq, abs_zero] at hT
  linarith

/-- Report Lemma 3.4: at a point where the profile vanishes the Poisson averages vanish at the
bottom edge: the far part is handled by `tendsto_integral_far_bottom`, the near part by the
continuity of `b` at `s` together with `M_σ ≤ 1`. -/
theorem tendsto_integral_bottom_of_eq_zero {ℓ : ℝ} (hℓ : 0 < ℓ) {b : ℝ → ℝ} (hb : Continuous b)
    {A : ℝ} (hA : 0 ≤ A) (hbound : ∀ y : ℝ, |b y| ≤ A * (1 + |y|))
    (hcentral : ∀ t : ℝ, Integrable fun T : ℝ ↦ P_σ 0 T * b (t - ℓ * T))
    (s : ℝ) (hszero : b s = 0) :
    Tendsto (fun z : ℂ ↦ ∫ T : ℝ, P_σ (z.im / ℓ) T * b (z.re - ℓ * T))
      (𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ] ((s : ℂ) - I * (ℓ : ℂ))) (𝓝 (0 : ℝ)) := by
  obtain ⟨hre, -, hrange⟩ := tendsto_bottom_edge hℓ s
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨η, hη, hcontrol⟩ := (Metric.continuousAt_iff.mp hb.continuousAt) (ε / 2) hhalf
  have hδ : 0 < η / (2 * ℓ) := by positivity
  have hS : MeasurableSet {T : ℝ | η / (2 * ℓ) ≤ |T|} :=
    (isClosed_le continuous_const continuous_abs).measurableSet
  filter_upwards [hrange,
    Metric.tendsto_nhds.mp (tendsto_integral_far_bottom hℓ hb hA hbound s hδ) (ε / 2) hhalf,
    hre.eventually (Metric.ball_mem_nhds s (half_pos hη))] with z hz hzfar hzre
  have hzabove : z.im / ℓ < 1 := by linarith [hz.2]
  have hzre' : |z.re - s| < η / 2 := by simpa [Metric.mem_ball, Real.dist_eq] using hzre
  have hk : Integrable (P_σ (z.im / ℓ)) := stripPoissonKernel_integrable hz.1 hzabove
  have hprod : Integrable fun T : ℝ ↦ P_σ (z.im / ℓ) T * b (z.re - ℓ * T) :=
    stripPoissonKernel_lower_product_integrable hz.1 hz.2
      (hb.comp (by fun_prop : Continuous fun T : ℝ ↦ z.re - ℓ * T)) (hcentral z.re)
  have hnear : ‖∫ T in {T : ℝ | η / (2 * ℓ) ≤ |T|}ᶜ, P_σ (z.im / ℓ) T * b (z.re - ℓ * T)‖ ≤
      ε / 2 := by
    calc ‖∫ T in {T : ℝ | η / (2 * ℓ) ≤ |T|}ᶜ, P_σ (z.im / ℓ) T * b (z.re - ℓ * T)‖
        ≤ ∫ T in {T : ℝ | η / (2 * ℓ) ≤ |T|}ᶜ, ε / 2 * P_σ (z.im / ℓ) T := by
          refine norm_integral_le_of_norm_le (hk.const_mul (ε / 2)).integrableOn ?_
          filter_upwards [ae_restrict_mem hS.compl] with T hT
          have hTsmall : ℓ * |T| < η / 2 := by
            calc ℓ * |T| < ℓ * (η / (2 * ℓ)) := mul_lt_mul_of_pos_left (not_le.mp hT) hℓ
              _ = η / 2 := by field_simp [hℓ.ne']
          have harg : dist (z.re - ℓ * T) s < η := by
            rw [Real.dist_eq, show z.re - ℓ * T - s = z.re - s - ℓ * T by ring]
            have habs := abs_sub (z.re - s) (ℓ * T)
            rw [abs_mul, abs_of_pos hℓ] at habs
            linarith
          have hbsmall : |b (z.re - ℓ * T)| < ε / 2 := by
            simpa [Real.dist_eq, hszero] using hcontrol harg
          have hkpos := stripPoissonKernel_pos hz.1 hzabove T
          rw [norm_mul, Real.norm_eq_abs, abs_of_pos hkpos, Real.norm_eq_abs]
          nlinarith [mul_nonneg hkpos.le (sub_nonneg.mpr hbsmall.le)]
      _ ≤ ∫ T : ℝ, ε / 2 * P_σ (z.im / ℓ) T := setIntegral_le_integral (hk.const_mul (ε / 2))
          (.of_forall fun T ↦ mul_nonneg hhalf.le (stripPoissonKernel_pos hz.1 hzabove T).le)
      _ = ε / 2 * M_σ (z.im / ℓ) := by
          rw [integral_const_mul, integral_stripPoissonKernel hz.1 hzabove]
      _ ≤ ε / 2 := by nlinarith [(stripBottomMass_lt_one hz.1).le]
  rw [dist_zero_right] at hzfar ⊢
  rw [← integral_add_compl hS hprod]
  exact lt_of_le_of_lt (norm_add_le _ _) (by linarith)

/-- Report Lemma 3.4: the Poisson averages of a linearly bounded continuous profile converge to
its boundary value `b s` at the bottom edge. -/
theorem tendsto_integral_bottom {ℓ : ℝ} (hℓ : 0 < ℓ) {b : ℝ → ℝ} (hb : Continuous b)
    {A : ℝ} (hA : 0 ≤ A) (hbound : ∀ y : ℝ, |b y| ≤ A * (1 + |y|))
    (hcentral : ∀ t : ℝ, Integrable fun T : ℝ ↦ P_σ 0 T * b (t - ℓ * T)) (s : ℝ) :
    Tendsto (fun z : ℂ ↦ ∫ T : ℝ, P_σ (z.im / ℓ) T * b (z.re - ℓ * T))
      (𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ] ((s : ℂ) - I * (ℓ : ℂ))) (𝓝 (b s)) := by
  obtain ⟨-, hσ, hrange⟩ := tendsto_bottom_edge hℓ s
  have hb₀ : Continuous fun y : ℝ ↦ b y - b s := hb.sub continuous_const
  have hbound₀ : ∀ y : ℝ, |b y - b s| ≤ (A + |b s|) * (1 + |y|) := fun y ↦ by
    nlinarith [abs_sub (b y) (b s), hbound y, abs_nonneg y, abs_nonneg (b s)]
  have hcentral₀ : ∀ t : ℝ, Integrable fun T : ℝ ↦ P_σ 0 T * (b (t - ℓ * T) - b s) := fun t ↦ by
    have h : Integrable fun T : ℝ ↦ P_σ 0 T * b (t - ℓ * T) - P_σ 0 T * b s :=
      (hcentral t).sub ((stripPoissonKernel_integrable (by norm_num) one_pos).mul_const (b s))
    simpa [mul_sub] using h
  have hzero := tendsto_integral_bottom_of_eq_zero hℓ hb₀ (by positivity) hbound₀ hcentral₀ s
    (by simp)
  have hmass : Tendsto (fun z : ℂ ↦ M_σ (z.im / ℓ))
      (𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ] ((s : ℂ) - I * (ℓ : ℂ))) (𝓝 (1 : ℝ)) := by
    have hM : Continuous M_σ := by unfold M_σ; fun_prop
    have hcomp : Tendsto (fun z : ℂ ↦ M_σ (z.im / ℓ))
        (𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ] ((s : ℂ) - I * (ℓ : ℂ))) (𝓝 (M_σ (-1 : ℝ))) :=
      (hM.tendsto (-1 : ℝ)).comp hσ
    simpa [M_σ] using hcomp
  have heq : (fun z : ℂ ↦ ∫ T : ℝ, P_σ (z.im / ℓ) T * b (z.re - ℓ * T)) =ᶠ[
      𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ] ((s : ℂ) - I * (ℓ : ℂ))]
      fun z : ℂ ↦ (∫ T : ℝ, P_σ (z.im / ℓ) T * (b (z.re - ℓ * T) - b s)) +
        M_σ (z.im / ℓ) * b s := by
    filter_upwards [hrange] with z hz
    have hzabove : z.im / ℓ < 1 := by linarith [hz.2]
    have hprod₀ := stripPoissonKernel_lower_product_integrable hz.1 hz.2
      (hb₀.comp (by fun_prop : Continuous fun T : ℝ ↦ z.re - ℓ * T)) (hcentral₀ z.re)
    have hk : Integrable (P_σ (z.im / ℓ)) := stripPoissonKernel_integrable hz.1 hzabove
    calc (∫ T : ℝ, P_σ (z.im / ℓ) T * b (z.re - ℓ * T))
        = ∫ T : ℝ, (P_σ (z.im / ℓ) T * (b (z.re - ℓ * T) - b s) + P_σ (z.im / ℓ) T * b s) := by
          simp [mul_sub]
      _ = (∫ T : ℝ, P_σ (z.im / ℓ) T * (b (z.re - ℓ * T) - b s)) +
            ∫ T : ℝ, P_σ (z.im / ℓ) T * b s := integral_add hprod₀ (hk.mul_const (b s))
      _ = _ := by rw [integral_mul_const, integral_stripPoissonKernel hz.1 hzabove]
  simpa using (hzero.add (hmass.mul_const (b s))).congr' heq.symm

/-- At the top edge the kernel vanishes: `P_σ(T) → 0` as `σ → 1`, since `θ σ → π`. -/
theorem tendsto_P_σ_one (T : ℝ) : Tendsto (fun σ : ℝ ↦ P_σ σ T) (𝓝 (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hangle : θ (1 : ℝ) = π := by unfold θ; ring
  have hden : 4 * (Real.cosh (π * T / 2) - Real.cos (θ (1 : ℝ))) ≠ 0 := by
    rw [hangle, Real.cos_pi]
    nlinarith [Real.one_le_cosh (π * T / 2)]
  have hnum : ContinuousAt (fun σ : ℝ ↦ Real.sin (θ σ)) 1 := by unfold θ; fun_prop
  have hdencont : ContinuousAt (fun σ : ℝ ↦ 4 * (Real.cosh (π * T / 2) - Real.cos (θ σ))) 1 := by
    unfold θ; fun_prop
  have h : Tendsto (fun σ : ℝ ↦ Real.sin (θ σ) / (4 * (Real.cosh (π * T / 2) - Real.cos (θ σ))))
      (𝓝 1) (𝓝 (Real.sin (θ (1 : ℝ)) / (4 * (Real.cosh (π * T / 2) - Real.cos (θ (1 : ℝ)))))) :=
    hnum.tendsto.div hdencont.tendsto hden
  simpa [P_σ, hangle, Real.sin_pi] using h

/-- Report Lemma 3.4: the Poisson averages of a linearly bounded profile vanish at the top edge,
where `P_σ → 0` pointwise under the exponential majorant. -/
theorem tendsto_integral_top {ℓ : ℝ} (hℓ : 0 < ℓ) {b : ℝ → ℝ} (hb : Continuous b)
    {A : ℝ} (hA : 0 ≤ A) (hbound : ∀ y : ℝ, |b y| ≤ A * (1 + |y|)) (s : ℝ) :
    Tendsto (fun z : ℂ ↦ ∫ T : ℝ, P_σ (z.im / ℓ) T * b (z.re - ℓ * T))
      (𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ] ((s : ℂ) + I * (ℓ : ℂ))) (𝓝 (0 : ℝ)) := by
  have hσ : Tendsto (fun z : ℂ ↦ z.im / ℓ)
      (𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ] ((s : ℂ) + I * (ℓ : ℂ))) (𝓝 (1 : ℝ)) := by
    simpa [hℓ.ne'] using ((Complex.continuous_im.div_const ℓ).tendsto
      ((s : ℂ) + I * (ℓ : ℂ))).mono_left nhdsWithin_le_nhds
  have hrange : ∀ᶠ z : ℂ in 𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ] ((s : ℂ) + I * (ℓ : ℂ)),
      0 ≤ z.im / ℓ ∧ z.im / ℓ < 1 := by
    filter_upwards [self_mem_nhdsWithin,
      hσ.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))] with z hz hz'
    exact ⟨hz'.le, (div_lt_iff₀ hℓ).2 (by simpa using hz.2)⟩
  have hre : Tendsto Complex.re
      (𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ] ((s : ℂ) + I * (ℓ : ℂ))) (𝓝 s) := by
    simpa using (Complex.continuous_re.tendsto ((s : ℂ) + I * (ℓ : ℂ))).mono_left
      nhdsWithin_le_nhds
  simpa using tendsto_setIntegral_P_σ_mul (S := univ) hℓ hb hA hbound MeasurableSet.univ
    stripPoissonExponentialMajorant_integrable integrable_exponentialMajorant_mul_abs
    (fun T ↦ by unfold stripPoissonExponentialMajorant; positivity) hre
    (hrange.mono fun z hz T ↦ (stripPoissonKernel_pos (by linarith [hz.1]) hz.2 T).le)
    (hrange.mono fun z hz T _ ↦ P_σ_le_exponentialMajorant hz.1 hz.2 T)
    fun T _ ↦ (tendsto_P_σ_one T).comp hσ


/-- Extend a function on the open horizontal strip `a < Im z < b` to the closed strip by
prescribing its traces on the two edges. -/
def stripTraceExtension (a b : ℝ) (H : ℂ → ℝ) (bottom top : ℝ → ℝ) (z : ℂ) : ℝ :=
  if z.im = a then bottom z.re else if z.im = b then top z.re else H z

private theorem preimage_im_Icc_eq_union {a b : ℝ} (hab : a < b) :
    Complex.im ⁻¹' Icc a b =
      (Complex.im ⁻¹' Ioo a b ∪ Complex.im ⁻¹' {a}) ∪ Complex.im ⁻¹' {b} := by
  ext w
  simp only [mem_preimage, mem_Icc, mem_Ioo, mem_union, mem_singleton_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact h₁.lt_or_eq.elim (fun h ↦ h₂.lt_or_eq.imp (fun h' ↦ Or.inl ⟨h, h'⟩) id)
      fun h ↦ Or.inl (Or.inr h.symm)
  · rintro ((⟨h, h'⟩ | h) | h) <;> subst_vars <;> constructor <;> linarith

/-- If `H` converges to the prescribed traces at both edges, the extension is continuous on the
closed strip: the closed strip is covered by the open strip and its two edges. -/
theorem stripTraceExtension_continuousOn {a b : ℝ} (hab : a < b) (H : ℂ → ℝ) (bottom top : ℝ → ℝ)
    (hH : ContinuousOn H (Complex.im ⁻¹' Ioo a b)) (hbottom : Continuous bottom)
    (htop : Continuous top)
    (hbottomtrace : ∀ s : ℝ, Tendsto H (𝓝[Complex.im ⁻¹' Ioo a b] ((s : ℂ) + I * (a : ℂ)))
      (𝓝 (bottom s)))
    (htoptrace : ∀ s : ℝ, Tendsto H (𝓝[Complex.im ⁻¹' Ioo a b] ((s : ℂ) + I * (b : ℂ)))
      (𝓝 (top s))) :
    ContinuousOn (stripTraceExtension a b H bottom top) (Complex.im ⁻¹' Icc a b) := by
  set E : ℂ → ℝ := stripTraceExtension a b H bottom top with hE
  have hba : b ≠ a := ne_of_gt hab
  have hinterior : ∀ w ∈ Complex.im ⁻¹' Ioo a b, E w = H w := fun w hw ↦ by
    simp [hE, stripTraceExtension, (ne_of_gt hw.1 : w.im ≠ a), (ne_of_lt hw.2 : w.im ≠ b)]
  intro z hz
  have hedge : ∀ c : ℝ, ∀ g : ℝ → ℝ, Continuous g → (∀ w : ℂ, w.im = c → E w = g w.re) →
      ContinuousWithinAt E (Complex.im ⁻¹' {c}) z := fun c g hg hval ↦ by
    by_cases hzc : z ∈ Complex.im ⁻¹' {c}
    · exact ((hg.comp Complex.continuous_re).continuousAt.continuousWithinAt).congr
        (fun w hw ↦ hval w hw) (hval z hzc)
    · exact continuousWithinAt_of_notMem_closure
        (by rwa [(isClosed_singleton.preimage Complex.continuous_im).closure_eq])
  have hUedge : ∀ c : ℝ, ∀ g : ℝ → ℝ,
      (∀ s : ℝ, Tendsto H (𝓝[Complex.im ⁻¹' Ioo a b] ((s : ℂ) + I * (c : ℂ))) (𝓝 (g s))) →
      z.im = c → E z = g z.re → ContinuousWithinAt E (Complex.im ⁻¹' Ioo a b) z :=
    fun c g htrace hzc hval ↦ by
      have h := htrace z.re
      rw [show (z.re : ℂ) + I * (c : ℂ) = z from Complex.ext (by simp) (by simp [hzc])] at h
      have hevent : E =ᶠ[𝓝[Complex.im ⁻¹' Ioo a b] z] H :=
        mem_of_superset self_mem_nhdsWithin hinterior
      change Tendsto E (𝓝[Complex.im ⁻¹' Ioo a b] z) (𝓝 (E z))
      rw [hval]
      exact h.congr' hevent.symm
  have hU : ContinuousWithinAt E (Complex.im ⁻¹' Ioo a b) z := by
    by_cases hza : z.im = a
    · exact hUedge a bottom hbottomtrace hza (by simp [hE, stripTraceExtension, hza])
    by_cases hzb : z.im = b
    · exact hUedge b top htoptrace hzb (by simp [hE, stripTraceExtension, hzb, hba])
    · have hzO : z ∈ Complex.im ⁻¹' Ioo a b :=
        ⟨lt_of_le_of_ne hz.1 (Ne.symm hza), lt_of_le_of_ne hz.2 hzb⟩
      exact (hH z hzO).congr hinterior (hinterior z hzO)
  rw [preimage_im_Icc_eq_union hab]
  exact (hU.union (hedge a bottom hbottom fun w hw ↦ by
      simp [hE, stripTraceExtension, hw])).union
    (hedge b top htop fun w hw ↦ by simp [hE, stripTraceExtension, hw, hba])

/-- Report Lemma 3.2: `Re W[b]` extends continuously to the bottom edge `Im z = -ℓ`, with trace
`b`. -/
theorem tendsto_W_b_re_bottom {ℓ : ℝ} (hℓ : 0 < ℓ) {b : ℝ → ℝ} (hb : Continuous b) {A : ℝ}
    (hA : 0 ≤ A) (hbound : ∀ y : ℝ, |b y| ≤ A * (1 + |y|)) (s : ℝ) :
    Tendsto (fun z : ℂ ↦ (W_b ℓ b z).re)
      (𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ] ((s : ℂ) - I * (ℓ : ℂ))) (𝓝 (b s)) :=
  (tendsto_integral_bottom hℓ hb hA hbound
    (fun t ↦ integrable_P_σ_mul_of_abs_le hℓ (by norm_num) one_pos hb hA hbound t) s).congr'
    (eventually_nhdsWithin_of_forall fun _ hz ↦ (W_b_re_of_mem_strip hℓ hb hbound hz).symm)

/-- Report Lemma 3.2: `Re W[b]` extends continuously to the top edge `Im z = ℓ`, with trace `0`. -/
theorem tendsto_W_b_re_top {ℓ : ℝ} (hℓ : 0 < ℓ) {b : ℝ → ℝ} (hb : Continuous b) {A : ℝ}
    (hA : 0 ≤ A) (hbound : ∀ y : ℝ, |b y| ≤ A * (1 + |y|)) (s : ℝ) :
    Tendsto (fun z : ℂ ↦ (W_b ℓ b z).re)
      (𝓝[Complex.im ⁻¹' Ioo (-ℓ) ℓ] ((s : ℂ) + I * (ℓ : ℂ))) (𝓝 (0 : ℝ)) :=
  (tendsto_integral_top hℓ hb hA hbound s).congr'
    (eventually_nhdsWithin_of_forall fun _ hz ↦ (W_b_re_of_mem_strip hℓ hb hbound hz).symm)

/-- The continuous extension of `Re W[b]` to the closed strip `|Im z| ≤ ℓ`, with bottom trace `b`
and top trace `0`; report Lemma 3.2. -/
def W_b_reExtension (ℓ : ℝ) (b : ℝ → ℝ) : ℂ → ℝ :=
  stripTraceExtension (-ℓ) ℓ (fun w : ℂ ↦ (W_b ℓ b w).re) b fun _ : ℝ ↦ 0

/-- On the open strip the extension `W_b_reExtension` is `Re W[b]`. -/
theorem W_b_reExtension_of_mem_strip (ℓ : ℝ) (b : ℝ → ℝ) {v : ℂ} (hv : v.im ∈ Ioo (-ℓ) ℓ) :
    W_b_reExtension ℓ b v = (W_b ℓ b v).re := by
  simp [W_b_reExtension, stripTraceExtension, (ne_of_gt hv.1 : v.im ≠ -ℓ),
    (ne_of_lt hv.2 : v.im ≠ ℓ)]

/-- The extension `W_b_reExtension` is continuous on the closed strip; report Lemma 3.2. -/
theorem W_b_reExtension_continuousOn {ℓ : ℝ} (hℓ : 0 < ℓ) {b : ℝ → ℝ} (hb : Continuous b) {A : ℝ}
    (hA : 0 ≤ A) (hbound : ∀ y : ℝ, |b y| ≤ A * (1 + |y|)) :
    ContinuousOn (W_b_reExtension ℓ b) (Complex.im ⁻¹' Icc (-ℓ) ℓ) := by
  refine stripTraceExtension_continuousOn (by linarith) _ _ _
    (Complex.continuous_re.comp_continuousOn (differentiableOn_W_b hℓ hb hbound).continuousOn)
    hb continuous_const (fun s ↦ ?_) fun s ↦ ?_
  · simpa [sub_eq_add_neg] using tendsto_W_b_re_bottom hℓ hb hA hbound s
  · exact tendsto_W_b_re_top hℓ hb hA hbound s

/-- On the bottom edge `e^{-W[b]} Z` has modulus at most `1` once `‖Z‖ ≤ e^{b}` there. -/
private theorem exp_neg_W_b_reExtension_mul_norm_bottom_le_one {ℓ : ℝ} {b : ℝ → ℝ} {Z : ℂ → ℂ}
    (hbottom : ∀ y : ℝ, ‖Z ((y : ℂ) - I * (ℓ : ℂ))‖ ≤ Real.exp (b y)) (v : ℂ) (hv : v.im = -ℓ) :
    Real.exp (-(W_b_reExtension ℓ b v)) * ‖Z v‖ ≤ 1 := by
  have hnorm : ‖Z v‖ ≤ Real.exp (b v.re) := by
    have h := hbottom v.re
    rwa [show (v.re : ℂ) - I * (ℓ : ℂ) = v from Complex.ext (by simp) (by simp [hv])] at h
  rw [show W_b_reExtension ℓ b v = b v.re by simp [W_b_reExtension, stripTraceExtension, hv]]
  calc Real.exp (-(b v.re)) * ‖Z v‖ ≤ Real.exp (-(b v.re)) * Real.exp (b v.re) :=
        mul_le_mul_of_nonneg_left hnorm (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- On the top edge `e^{-W[b]} Z` has modulus at most `1` once `‖Z‖ ≤ 1` there. -/
private theorem exp_neg_W_b_reExtension_mul_norm_top_le_one {ℓ : ℝ} (hℓ : 0 < ℓ) {b : ℝ → ℝ}
    {Z : ℂ → ℂ} (htop : ∀ y : ℝ, ‖Z ((y : ℂ) + I * (ℓ : ℂ))‖ ≤ 1) (v : ℂ) (hv : v.im = ℓ) :
    Real.exp (-(W_b_reExtension ℓ b v)) * ‖Z v‖ ≤ 1 := by
  have hnorm : ‖Z v‖ ≤ 1 := by
    have h := htop v.re
    rwa [show (v.re : ℂ) + I * (ℓ : ℂ) = v from Complex.ext (by simp) (by simp [hv])] at h
  rw [show W_b_reExtension ℓ b v = 0 by
    simp [W_b_reExtension, stripTraceExtension, hv, (by linarith : ℓ ≠ -ℓ)]]
  simpa using hnorm

/-- **Poisson principle for the strip** (report, proof of Lemma 3.2). Let `Z` be holomorphic on
the open strip `|Im z| < ℓ` and continuous on its closure, with the Phragmén–Lindelöf growth
`Z = O(exp (B e^{c |Re z|}))` as `|Re z| → ∞` in the strip for some `c < π/(2ℓ)`. Let `b` be a
continuous profile with `|b y| ≤ A (1 + |y|)` such that `‖Z(y − iℓ)‖ ≤ e^{b(y)}` on the bottom
edge and `‖Z(y + iℓ)‖ ≤ 1` on the top edge. Then at every interior point `s + iσℓ`, `-1 < σ < 1`,
`‖Z(s + iσℓ)‖ ≤ exp (∫ P_σ(T) b(s − ℓT) dT)`, the exponential of the Poisson integral of `b`.

Proof: Phragmén–Lindelöf (`PhragmenLindelof.horizontal_strip_norm_extension`) applied to
`e^{-W[b]} Z`, where `W[b]` is the holomorphic Poisson integral of `b`: `Re W[b]` is the Poisson
average of `b`, its extension to the closed strip is continuous with traces `b` (bottom) and `0`
(top), so `e^{-W[b]} Z` has modulus at most `1` on both edges, and it keeps the growth of `Z`
since `|Re W[b](z)| ≤ B (1 + |Re z|)`. -/
theorem norm_le_exp_integral_P_σ_of_strip_of_isBigO {ℓ : ℝ} (hℓ : 0 < ℓ) {Z : ℂ → ℂ}
    (hZ : DiffContOnCl ℂ Z (Complex.im ⁻¹' Ioo (-ℓ) ℓ))
    (hgrowth : ∃ c < π / (2 * ℓ), ∃ B : ℝ, Z =O[comap (fun z : ℂ ↦ |z.re|) atTop ⊓
      𝓟 (Complex.im ⁻¹' Ioo (-ℓ) ℓ)] fun z : ℂ ↦ Real.exp (B * Real.exp (c * |z.re|)))
    {b : ℝ → ℝ} (hb : Continuous b) {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ y : ℝ, |b y| ≤ A * (1 + |y|))
    (hbottom : ∀ y : ℝ, ‖Z ((y : ℂ) - I * (ℓ : ℂ))‖ ≤ Real.exp (b y))
    (htop : ∀ y : ℝ, ‖Z ((y : ℂ) + I * (ℓ : ℂ))‖ ≤ 1)
    {σ : ℝ} (hσbelow : -1 < σ) (hσabove : σ < 1) (s : ℝ) :
    ‖Z ((s : ℂ) + I * (σ * ℓ : ℂ))‖ ≤ Real.exp (∫ T : ℝ, P_σ σ T * b (s - ℓ * T)) := by
  have hwidth : -ℓ < ℓ := by linarith
  have hZcont : ContinuousOn Z (Complex.im ⁻¹' Icc (-ℓ) ℓ) := by
    have hcl : closure (Complex.im ⁻¹' Ioo (-ℓ) ℓ) = Complex.im ⁻¹' Icc (-ℓ) ℓ := by
      rw [Complex.closure_preimage_im, closure_Ioo hwidth.ne]
    simpa [hcl] using hZ.continuousOn
  have hzmem : ((s : ℂ) + I * (σ * ℓ : ℂ)).im ∈ Ioo (-ℓ) ℓ := by
    simp only [mem_Ioo, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.mul_re,
      Complex.I_re, Complex.ofReal_re, zero_mul, Complex.I_im, one_mul, zero_add, mul_zero,
      sub_zero, add_zero]
    constructor
    · nlinarith [mul_pos (show 0 < 1 + σ by linarith) hℓ]
    · nlinarith [mul_pos (show 0 < 1 - σ by linarith) hℓ]
  have hmax := PhragmenLindelof.horizontal_strip_norm_extension hwidth one_pos
    (fun v ↦ Complex.exp (-(W_b ℓ b v)) * Z v)
    (fun v ↦ Real.exp (-(W_b_reExtension ℓ b v)) * ‖Z v‖)
    ((differentiableOn_W_b hℓ hb hbound).neg.cexp.mul hZ.differentiableOn)
    ((W_b_reExtension_continuousOn hℓ hb hA hbound).neg.rexp.mul hZcont.norm)
    (fun _ _ ↦ mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
    (fun v hv ↦ by
      rw [W_b_reExtension_of_mem_strip ℓ b hv, norm_mul, Complex.norm_exp, Complex.neg_re])
    (exp_neg_W_b_reExtension_mul_norm_bottom_le_one hbottom)
    (exp_neg_W_b_reExtension_mul_norm_top_le_one hℓ htop)
    (by
      rw [show ℓ - -ℓ = 2 * ℓ by ring]
      exact isBigO_exp_neg_W_b_mul hℓ hb hA hbound hgrowth) hzmem.1.le hzmem.2.le
  rw [W_b_reExtension_of_mem_strip ℓ b hzmem, W_b_re hℓ hσbelow hσabove s b
    (integrable_K'_ℓ_mul hℓ hzmem b hb
      (integrable_exp_neg_mul_abs_mul_of_abs_le (by positivity) hb hbound))] at hmax
  calc ‖Z ((s : ℂ) + I * (σ * ℓ : ℂ))‖
      = Real.exp (∫ T : ℝ, P_σ σ T * b (s - ℓ * T)) *
          (Real.exp (-(∫ T : ℝ, P_σ σ T * b (s - ℓ * T))) * ‖Z ((s : ℂ) + I * (σ * ℓ : ℂ))‖) := by
        rw [← mul_assoc (Real.exp _), ← Real.exp_add]; simp
    _ ≤ Real.exp (∫ T : ℝ, P_σ σ T * b (s - ℓ * T)) * 1 :=
        mul_le_mul_of_nonneg_left hmax (Real.exp_pos _).le
    _ = _ := mul_one _

/-- A function bounded on the open strip `|Im z| < ℓ` has the Phragmén–Lindelöf growth required
by `norm_le_exp_integral_P_σ_of_strip_of_isBigO` (with `c = 0` and `B = 0`). -/
theorem isBigO_exp_mul_exp_abs_re_of_norm_le {ℓ : ℝ} (hℓ : 0 < ℓ) {Z : ℂ → ℂ} {K : ℝ}
    (hK : ∀ z : ℂ, z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ → ‖Z z‖ ≤ K) :
    ∃ c < π / (2 * ℓ), ∃ B : ℝ, Z =O[comap (fun z : ℂ ↦ |z.re|) atTop ⊓
      𝓟 (Complex.im ⁻¹' Ioo (-ℓ) ℓ)] fun z : ℂ ↦ Real.exp (B * Real.exp (c * |z.re|)) :=
  ⟨0, by positivity, 0, IsBigO.of_bound K (eventually_inf_principal.mpr (.of_forall fun z hz ↦ by
    simpa using hK z hz))⟩

/-- The Poisson principle for the strip, `norm_le_exp_integral_P_σ_of_strip`, proved by
Phragmén–Lindelöf: the bounded case of `norm_le_exp_integral_P_σ_of_strip_of_isBigO`. -/
theorem norm_le_exp_integral_P_σ_of_strip_phragmenLindelof {ℓ : ℝ} (hℓ : 0 < ℓ) {Z : ℂ → ℂ}
    (hZ : DiffContOnCl ℂ Z (Complex.im ⁻¹' Ioo (-ℓ) ℓ)) {K : ℝ}
    (hK : ∀ z : ℂ, z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ → ‖Z z‖ ≤ K)
    {b : ℝ → ℝ} (hb : Continuous b) {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ y : ℝ, |b y| ≤ A * (1 + |y|))
    (hbottom : ∀ y : ℝ, ‖Z ((y : ℂ) - I * (ℓ : ℂ))‖ ≤ Real.exp (b y))
    (htop : ∀ y : ℝ, ‖Z ((y : ℂ) + I * (ℓ : ℂ))‖ ≤ 1)
    {σ : ℝ} (hσbelow : -1 < σ) (hσabove : σ < 1) (s : ℝ) :
    ‖Z ((s : ℂ) + I * (σ * ℓ : ℂ))‖ ≤ Real.exp (∫ T : ℝ, P_σ σ T * b (s - ℓ * T)) :=
  norm_le_exp_integral_P_σ_of_strip_of_isBigO hℓ hZ (isBigO_exp_mul_exp_abs_re_of_norm_le hℓ hK)
    hb hA hbound hbottom htop hσbelow hσabove s

/-! ### Lemma 3.2 by Phragmén–Lindelöf -/

/-- Report Lemma 3.2 by Phragmén–Lindelöf: the capped bound `norm_Z_g_le_exp_integral_of_cap`,
derived from `norm_le_exp_integral_P_σ_of_strip_phragmenLindelof` instead of the half-plane
Poisson principle. -/
theorem norm_Z_g_le_exp_integral_of_cap_phragmenLindelof {d : ℕ} {ς : ℤˣ} (hd : 0 < d)
    (g : RadialEigenfunction d ς) (R D : ℝ)
    (hcap : ∀ y : ℝ, ‖Z_g hd g.toFun R ((y : ℂ) - I * ((d : ℂ) / 2))‖ ≤
      Real.exp (h_ℓD ((d : ℝ) / 2) R D y))
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    ‖Z_g hd g.toFun R ((s : ℂ) + I * (σ * ((d : ℂ) / 2)))‖ ≤
      Real.exp (∫ T : ℝ, P_σ σ T * h_ℓD ((d : ℝ) / 2) R D (s - (d : ℝ) / 2 * T)) := by
  have hℓ : 0 < (d : ℝ) / 2 := half_pos (Nat.cast_pos.mpr hd)
  have hcast : ((d : ℂ) / 2) = (((d : ℝ) / 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat]
  obtain ⟨A, hA, hbound⟩ := exists_abs_h_ℓD_le hd R D
  obtain ⟨K, -, hK⟩ := g.exists_norm_Z_g_le hd R
  rw [hcast] at hcap ⊢
  exact norm_le_exp_integral_P_σ_of_strip_phragmenLindelof hℓ (g.diffContOnCl_Z_g hd R)
    (fun z hz ↦ hK z hz.1.le hz.2.le) (lowerGammaBoundaryCapped_continuous hℓ R D) hA hbound hcap
    (fun y ↦ by rw [← hcast]; exact g.norm_Z_g_top_le_one hd R y) hbelow habove s

/-- Report Lemma 3.2 by Phragmén–Lindelöf: `exists_capped_poisson_majorization` derived from
`norm_Z_g_le_exp_integral_of_cap_phragmenLindelof`. -/
theorem exists_capped_poisson_majorization_phragmenLindelof {d : ℕ} {ς : ℤˣ} (hd : 0 < d)
    (g : RadialEigenfunction d ς) {R : ℝ} (hR : 0 < R) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∀ {σ : ℝ}, -1 < σ → σ < 1 → ∀ s : ℝ,
      ‖Z_g hd g.toFun R ((s : ℂ) + I * (σ * ((d : ℂ) / 2)))‖ ≤
        Real.exp (∫ T : ℝ, P_σ σ T * h_ℓD ((d : ℝ) / 2) R D (s - (d : ℝ) / 2 * T)) := by
  obtain ⟨D₀, hbottom⟩ := exists_norm_Z_g_bottom_le_exp_h_ℓD hd g hR
  exact ⟨D₀, fun D hD σ hbelow habove s ↦
    norm_Z_g_le_exp_integral_of_cap_phragmenLindelof hd g R D (hbottom D hD) hbelow habove s⟩

end

end CohnElkies
