import CohnElkies.LowerBound.LimitingDensity
import CohnElkies.LowerBound.CappedMajorant
import CohnElkiesForMathlib.Analysis.Complex.PhragmenLindelof

/-!
# The Poisson majorization of `Z` in the strip (report §3.2, Lemma 3.2)

Phragmén–Lindelöf in the strip applied to `Z(z) e^{-W_D(z)}`: the modulus of `Z` at a point
`x - iσ d/2` of the strip is bounded by `exp (∫ P_σ(x - y) h_{λ,D}(y) dy)`, the Poisson integral of
the capped boundary function (`exists_capped_poisson_majorization`). The proof controls the
horizontal integrals far away, the bottom and top edges, and uses the continuous extension of
`|Z e^{-W_D}|` to the closed strip.
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology

theorem abs_log_half_le_half {x : ℝ} (hx : 2 ≤ x) : |Real.log (x / 2)| ≤ x / 2 := by
  rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
  linarith [Real.log_le_sub_one_of_pos (show 0 < x / 2 by linarith)]

theorem abs_log_sqrtFactor_le_add {c x : ℝ} (hc : 0 ≤ c) (hx : 2 ≤ x) :
    |Real.log (√(c ^ 2 + (x / 2) ^ 2))| ≤ c + x := by
  linarith [lower_abs_log_sqrtFactor_le hc (show 0 < x by linarith), abs_log_half_le_half hx]

/-- The Riemann sum of the factors `log √(cⱼ² + (x/2)²)` of `h_λ` is linearly bounded. -/
theorem abs_sum_log_sqrtFactor_le {k : ℕ} {c : ℕ → ℝ} (hc : ∀ j, 0 ≤ c j) {x : ℝ} (hx : 2 ≤ x) :
    |∑ j ∈ Finset.range k, Real.log (√(c j ^ 2 + (x / 2) ^ 2))| ≤
      (∑ j ∈ Finset.range k, c j) + k * x := by
  calc |∑ j ∈ Finset.range k, Real.log (√(c j ^ 2 + (x / 2) ^ 2))|
      ≤ ∑ j ∈ Finset.range k, |Real.log (√(c j ^ 2 + (x / 2) ^ 2))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range k, (c j + x) :=
        Finset.sum_le_sum fun j _ ↦ abs_log_sqrtFactor_le_add (hc j) hx
    _ = (∑ j ∈ Finset.range k, c j) + k * x := by simp [Finset.sum_add_distrib]

/-- Even dimensions: `h_k` grows at most linearly away from the pole at `0`. -/
theorem exists_abs_h_ℓ_le_natCast (k : ℕ) (R : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x : ℝ, 2 ≤ x → |h_ℓ (k : ℝ) R x| ≤ A * (1 + x) := by
  have hL : (0 : ℝ) ≤ |(k : ℝ) * Real.log (π * R ^ 2)| := abs_nonneg _
  have hS : (0 : ℝ) ≤ ∑ j ∈ Finset.range k, (j : ℝ) := by positivity
  refine ⟨|(k : ℝ) * Real.log (π * R ^ 2)| + (∑ j ∈ Finset.range k, (j : ℝ)) + k,
    by positivity, fun x hx ↦ ?_⟩
  have hx0 : (0 : ℝ) ≤ x := by linarith
  rw [lowerGammaBoundaryLog_integer k R (show (0 : ℝ) < x by linarith).ne']
  have hsum := abs_sum_log_sqrtFactor_le (k := k) (c := fun j : ℕ ↦ (j : ℝ))
    (fun j ↦ Nat.cast_nonneg j) hx
  have habs := abs_sub ((k : ℝ) * Real.log (π * R ^ 2))
    (∑ j ∈ Finset.range k, Real.log (√((j : ℝ) ^ 2 + (x / 2) ^ 2)))
  nlinarith [mul_nonneg hL hx0, mul_nonneg hS hx0, mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hx0]

/-- Odd dimensions: `h_{k+1/2}` grows at most linearly away from the pole at `0`; the extra
`coth` correction contributes the terms `π x + |log π|`. -/
theorem exists_abs_h_ℓ_le_natCast_add_half (k : ℕ) (R : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x : ℝ, 2 ≤ x → |h_ℓ ((k : ℝ) + 1 / 2) R x| ≤ A * (1 + x) := by
  have hL : (0 : ℝ) ≤ |((k : ℝ) + 1 / 2) * Real.log (π * R ^ 2)| := abs_nonneg _
  have hQ : (0 : ℝ) ≤ |Real.log π| := abs_nonneg _
  have hS : (0 : ℝ) ≤ ∑ j ∈ Finset.range k, ((j : ℝ) + 1 / 2) := by positivity
  refine ⟨|((k : ℝ) + 1 / 2) * Real.log (π * R ^ 2)| +
    (∑ j ∈ Finset.range k, ((j : ℝ) + 1 / 2)) + k + π + |Real.log π| + 1, by positivity,
    fun x hx ↦ ?_⟩
  have hx0 : (0 : ℝ) < x := by linarith
  have hsum := abs_sum_log_sqrtFactor_le (k := k) (c := fun j : ℕ ↦ (j : ℝ) + 1 / 2)
    (fun j ↦ by positivity) hx
  have hcorr : |1 / 2 * Real.log (lowerCoth (π * (x / 2)) / (x / 2))| ≤
      (π * x + |Real.log π| + x) / 2 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    linarith [lower_abs_log_coth_div_le (show 0 < x / 2 by linarith), abs_log_half_le_half hx]
  rw [lowerGammaBoundaryLog_halfInteger k R hx0.ne', abs_of_pos hx0,
    show π * x / 2 = π * (x / 2) by ring]
  have hmain := abs_sub (((k : ℝ) + 1 / 2) * Real.log (π * R ^ 2))
    (∑ j ∈ Finset.range k, Real.log (√(((j : ℝ) + 1 / 2) ^ 2 + (x / 2) ^ 2)))
  have htotal := abs_add_le (((k : ℝ) + 1 / 2) * Real.log (π * R ^ 2) -
      ∑ j ∈ Finset.range k, Real.log (√(((j : ℝ) + 1 / 2) ^ 2 + (x / 2) ^ 2)))
    (1 / 2 * Real.log (lowerCoth (π * (x / 2)) / (x / 2)))
  nlinarith [mul_nonneg hL hx0.le, mul_nonneg hS hx0.le, mul_nonneg hQ hx0.le,
    mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hx0.le, mul_nonneg Real.pi_pos.le hx0.le]

/-- `h_λ` is even for `λ = d/2`. -/
theorem h_ℓ_eq_abs {d : ℕ} (R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    h_ℓ ((d : ℝ) / 2) R y = h_ℓ ((d : ℝ) / 2) R |y| := by
  rcases abs_choice y with h | h <;> rw [h]
  exact (lowerGammaBoundaryLog_dimension_neg R hy).symm

/-- Report Lemma 3.2: away from the pole the boundary profile `h_{d/2}` is linearly bounded. -/
theorem exists_abs_h_ℓ_le (d : ℕ) (R : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ y : ℝ, 2 ≤ |y| → |h_ℓ ((d : ℝ) / 2) R y| ≤ A * (1 + |y|) := by
  obtain ⟨A, hA, htail⟩ : ∃ A : ℝ, 0 ≤ A ∧
      ∀ x : ℝ, 2 ≤ x → |h_ℓ ((d : ℝ) / 2) R x| ≤ A * (1 + x) := by
    rcases d.even_or_odd with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [show ((k + k : ℕ) : ℝ) / 2 = (k : ℝ) by push_cast; ring]
      exact exists_abs_h_ℓ_le_natCast k R
    · rw [show ((2 * k + 1 : ℕ) : ℝ) / 2 = (k : ℝ) + 1 / 2 by push_cast; ring]
      exact exists_abs_h_ℓ_le_natCast_add_half k R
  refine ⟨A, hA, fun y hy ↦ ?_⟩
  rw [h_ℓ_eq_abs R (by rintro rfl; norm_num at hy)]
  exact htail _ hy

/-- Report Lemma 3.2: the capped profile `h_{d/2,D}` is linearly bounded on all of `ℝ`; near the
pole the cap `D` takes over and continuity bounds the compact part `|y| ≤ 2`. -/
theorem exists_abs_h_ℓD_le {d : ℕ} (hd : 0 < d) (R D : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ y : ℝ, |h_ℓD ((d : ℝ) / 2) R D y| ≤ A * (1 + |y|) := by
  have hℓ : 0 < (d : ℝ) / 2 := half_pos (Nat.cast_pos.mpr hd)
  obtain ⟨A₀, hA₀, htail⟩ := exists_abs_h_ℓ_le d R
  obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact (Icc (-2 : ℝ) 2)).exists_bound_of_continuousOn
    (lowerGammaBoundaryCapped_continuous hℓ R D).continuousOn
  obtain ⟨A, hA, hKA, hDA, hA₀A⟩ : ∃ A : ℝ, 0 ≤ A ∧ K ≤ A ∧ |D| ≤ A ∧ A₀ ≤ A :=
    ⟨max 0 (max K (max |D| A₀)), le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)),
      (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))⟩
  refine ⟨A, hA, fun y ↦ ?_⟩
  have hfactor : A ≤ A * (1 + |y|) := by nlinarith [abs_nonneg y]
  rcases lt_or_ge |y| 2 with hy | hy
  · calc |h_ℓD ((d : ℝ) / 2) R D y| ≤ K := by simpa using hK y (abs_le.mp hy.le)
      _ ≤ A := hKA
      _ ≤ A * (1 + |y|) := hfactor
  · rw [h_ℓD, if_neg (show y ≠ 0 by rintro rfl; norm_num at hy)]
    rcases le_total (h_ℓ ((d : ℝ) / 2) R y) D with hmin | hmin
    · rw [min_eq_left hmin]
      exact (htail y hy).trans (mul_le_mul_of_nonneg_right hA₀A (by positivity))
    · rw [min_eq_right hmin]
      exact hDA.trans hfactor

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

private theorem ofReal_div_mul_half {d : ℕ} (hd : 0 < d) (x : ℝ) :
    (x / ((d : ℝ) / 2) : ℝ) * ((d : ℂ) / 2) = (x : ℂ) := by
  rw [Complex.ofReal_div, Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat]
  exact div_mul_cancel₀ _
    (div_ne_zero (Nat.cast_ne_zero.mpr hd.ne') (by norm_num : (2 : ℂ) ≠ 0))

/-- Report Lemma 3.2: `Re W_D(z) = ∫ P_σ(T) h_{λ,D}(Re z - λT) dT` grows at most linearly in
`Re z`, uniformly on the open strip `|Im z| < λ = d/2`. -/
theorem exists_abs_W_D_re_le {d : ℕ} (hd : 0 < d) (R D : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, z ∈ Complex.im ⁻¹' Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2) →
      |(W_D ((d : ℝ) / 2) R D z).re| ≤ B * (1 + |z.re|) := by
  have hℓ : 0 < (d : ℝ) / 2 := half_pos (Nat.cast_pos.mpr hd)
  obtain ⟨A, hA, hdatum⟩ := exists_abs_h_ℓD_le hd R D
  obtain ⟨M, hM, hmoment⟩ := exists_integral_P_σ_mul_abs_le
  refine ⟨A * (1 + (d : ℝ) / 2 * M), by positivity, fun z hz ↦ ?_⟩
  obtain ⟨σ, hbelow, habove, hre⟩ : ∃ σ : ℝ, -1 < σ ∧ σ < 1 ∧ (W_D ((d : ℝ) / 2) R D z).re =
      ∫ T : ℝ, P_σ σ T * h_ℓD ((d : ℝ) / 2) R D (z.re - (d : ℝ) / 2 * T) := by
    have hbelow : -1 < z.im / ((d : ℝ) / 2) := (lt_div_iff₀ hℓ).2 (by simpa using hz.1)
    have habove : z.im / ((d : ℝ) / 2) < 1 := (div_lt_iff₀ hℓ).2 (by simpa using hz.2)
    have hre := lowerStripCappedGammaOuter_re_dimension (R := R) (D := D) hd hbelow habove z.re
    rw [ofReal_div_mul_half hd z.im, mul_comm I (z.im : ℂ), Complex.re_add_im] at hre
    exact ⟨_, hbelow, habove, hre⟩
  have hconstant : Integrable fun T : ℝ ↦ A * (1 + |z.re|) * P_σ σ T :=
    (stripPoissonKernel_integrable hbelow habove).const_mul _
  have hlinear : Integrable fun T : ℝ ↦ A * ((d : ℝ) / 2) * (P_σ σ T * |T|) :=
    (integrable_P_σ_mul_abs hbelow habove).const_mul _
  have hpoint : ∀ᵐ T : ℝ, ‖P_σ σ T * h_ℓD ((d : ℝ) / 2) R D (z.re - (d : ℝ) / 2 * T)‖ ≤
      A * (1 + |z.re|) * P_σ σ T + A * ((d : ℝ) / 2) * (P_σ σ T * |T|) := by
    refine .of_forall fun T ↦ ?_
    have hkpos := stripPoissonKernel_pos hbelow habove T
    have hb : |h_ℓD ((d : ℝ) / 2) R D (z.re - (d : ℝ) / 2 * T)| ≤
        A * (1 + |z.re| + (d : ℝ) / 2 * |T|) := by
      refine (hdatum _).trans (mul_le_mul_of_nonneg_left ?_ hA)
      have habs := abs_sub z.re ((d : ℝ) / 2 * T)
      rw [abs_mul, abs_of_pos hℓ] at habs
      linarith
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos hkpos, Real.norm_eq_abs]
    nlinarith [mul_nonneg hkpos.le (sub_nonneg.mpr hb)]
  rw [hre]
  calc |∫ T : ℝ, P_σ σ T * h_ℓD ((d : ℝ) / 2) R D (z.re - (d : ℝ) / 2 * T)|
      ≤ ∫ T : ℝ, (A * (1 + |z.re|) * P_σ σ T + A * ((d : ℝ) / 2) * (P_σ σ T * |T|)) := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_of_norm_le (hconstant.add hlinear) hpoint
    _ = A * (1 + |z.re|) * M_σ σ + A * ((d : ℝ) / 2) * ∫ T : ℝ, P_σ σ T * |T| := by
        rw [integral_add hconstant hlinear, integral_const_mul, integral_const_mul,
          integral_stripPoissonKernel hbelow habove]
    _ ≤ A * (1 + (d : ℝ) / 2 * M) * (1 + |z.re|) := by
        have h₁ := mul_le_mul_of_nonneg_left (stripBottomMass_lt_one hbelow).le
          (by positivity : (0 : ℝ) ≤ A * (1 + |z.re|))
        have h₂ := mul_le_mul_of_nonneg_left (hmoment σ hbelow habove)
          (by positivity : (0 : ℝ) ≤ A * ((d : ℝ) / 2))
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hA hℓ.le) hM) (abs_nonneg z.re)]

/-- Report Lemma 3.2: the weighted Mellin integrand `e^{-W_D} Z_g` grows like
`exp (B exp (c |Re z|))` with `c = π/(4λ)`, below the Phragmén–Lindelöf threshold `π/(2λ)`. -/
theorem isBigO_exp_neg_W_D_mul_Z_g {d : ℕ} {ς : ℤˣ} (hd : 0 < d) (g : RadialEigenfunction d ς)
    (R D : ℝ) :
    ∃ c < π / ((d : ℝ) / 2 - -((d : ℝ) / 2)), ∃ B : ℝ,
      (fun z : ℂ ↦ Complex.exp (-(W_D ((d : ℝ) / 2) R D z)) * Z_g hd g.toFun R z) =O[
          comap (fun z : ℂ ↦ |z.re|) atTop ⊓
            principal (Complex.im ⁻¹' Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2))]
        fun z : ℂ ↦ Real.exp (B * Real.exp (c * |z.re|)) := by
  have hℓ : 0 < (d : ℝ) / 2 := half_pos (Nat.cast_pos.mpr hd)
  obtain ⟨G, hG, houter⟩ := exists_abs_W_D_re_le hd R D
  obtain ⟨K, hK, hwitness⟩ := g.exists_norm_Z_g_le hd R
  obtain ⟨c, hc, hclt⟩ : ∃ c : ℝ, 0 < c ∧ c < π / ((d : ℝ) / 2 - -((d : ℝ) / 2)) :=
    ⟨π / (4 * ((d : ℝ) / 2)), by positivity,
      (div_lt_div_iff₀ (by positivity) (by linarith)).2 (by nlinarith [Real.pi_pos])⟩
  refine ⟨c, hclt, G * (1 + 1 / c), IsBigO.of_bound (K + 1)
    (eventually_inf_principal.mpr (.of_forall fun z hz ↦ ?_))⟩
  have hexp : G * (1 + |z.re|) ≤ G * (1 + 1 / c) * Real.exp (c * |z.re|) := by
    have hlin : 1 + |z.re| ≤ (1 + 1 / c) * (1 + c * |z.re|) := by
      have hrecip : 1 / c * (c * |z.re|) = |z.re| := by
        rw [← mul_assoc, one_div_mul_cancel hc.ne', one_mul]
      linarith [mul_nonneg hc.le (abs_nonneg z.re), one_div_pos.mpr hc]
    calc G * (1 + |z.re|) ≤ G * ((1 + 1 / c) * Real.exp (c * |z.re|)) :=
          mul_le_mul_of_nonneg_left (hlin.trans (mul_le_mul_of_nonneg_left
            (by simpa [add_comm] using Real.add_one_le_exp (c * |z.re|)) (by positivity))) hG
      _ = G * (1 + 1 / c) * Real.exp (c * |z.re|) := by ring
  rw [norm_mul, Complex.norm_exp, Complex.neg_re, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-(W_D ((d : ℝ) / 2) R D z).re) * ‖Z_g hd g.toFun R z‖
      ≤ Real.exp (G * (1 + |z.re|)) * K :=
        mul_le_mul (Real.exp_le_exp.mpr ((neg_le_abs _).trans (houter z hz)))
          (hwitness z hz.1.le hz.2.le) (norm_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp (G * (1 + 1 / c) * Real.exp (c * |z.re|)) * K :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp) hK
    _ ≤ (K + 1) * Real.exp (G * (1 + 1 / c) * Real.exp (c * |z.re|)) := by
        nlinarith [Real.exp_pos (G * (1 + 1 / c) * Real.exp (c * |z.re|))]

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

/-- Report Lemma 3.2: for `D` large enough the capped profile majorizes the bottom-edge values of
`Z_g`; away from the pole this is the Gamma bound, near it the global bound `C` and the cap. -/
theorem exists_norm_Z_g_bottom_le_exp_h_ℓD {d : ℕ} {ς : ℤˣ} (hd : 0 < d)
    (g : RadialEigenfunction d ς) {R : ℝ} (hR : 0 < R) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∀ y : ℝ,
      ‖Z_g hd g.toFun R ((y : ℂ) - I * ((d : ℂ) / 2))‖ ≤
        Real.exp (h_ℓD ((d : ℝ) / 2) R D y) := by
  obtain ⟨C, hC, hglobal⟩ := g.exists_norm_Z_g_le hd R
  refine ⟨Real.log (C + 1), fun D hD y ↦ ?_⟩
  have hbounded := hglobal ((y : ℂ) - I * ((d : ℂ) / 2)) (by simp)
    (by simp; linarith [Nat.cast_nonneg (α := ℝ) d])
  have hexp : ‖Z_g hd g.toFun R ((y : ℂ) - I * ((d : ℂ) / 2))‖ ≤ Real.exp D :=
    calc ‖Z_g hd g.toFun R ((y : ℂ) - I * ((d : ℂ) / 2))‖ ≤ C + 1 := by linarith
      _ = Real.exp (Real.log (C + 1)) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp D := Real.exp_le_exp.mpr hD
  rcases eq_or_ne y 0 with rfl | hy
  · simpa [h_ℓD] using hexp
  · rw [h_ℓD, if_neg hy]
    rcases le_total (h_ℓ ((d : ℝ) / 2) R y) D with hmin | hmin
    · rw [min_eq_left hmin]
      exact g.norm_Z_g_bottom_le_exp_h_ℓ hd hR y hy
    · rw [min_eq_right hmin]
      exact hexp

/-- On the open strip `Re W_D` is the Poisson average of the capped boundary profile;
report (16). -/
theorem W_D_re_eventuallyEq {d : ℕ} (hd : 0 < d) (R D : ℝ) (z₀ : ℂ) :
    (fun z : ℂ ↦ (W_D ((d : ℝ) / 2) R D z).re) =ᶠ[
      𝓝[Complex.im ⁻¹' Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2)] z₀]
      fun z : ℂ ↦ ∫ T : ℝ, P_σ (z.im / ((d : ℝ) / 2)) T *
        h_ℓD ((d : ℝ) / 2) R D (z.re - (d : ℝ) / 2 * T) := by
  have hℓ : 0 < (d : ℝ) / 2 := half_pos (Nat.cast_pos.mpr hd)
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hbelow : -1 < z.im / ((d : ℝ) / 2) := (lt_div_iff₀ hℓ).2 (by simpa using hz.1)
  have habove : z.im / ((d : ℝ) / 2) < 1 := (div_lt_iff₀ hℓ).2 (by simpa using hz.2)
  have hre := lowerStripCappedGammaOuter_re_dimension (R := R) (D := D) hd hbelow habove z.re
  rwa [ofReal_div_mul_half hd z.im, mul_comm I (z.im : ℂ), Complex.re_add_im] at hre

/-- Report Lemma 3.2: `Re W_D` extends continuously to the bottom edge, with trace `h_{λ,D}`. -/
theorem tendsto_W_D_re_bottom {d : ℕ} (hd : 0 < d) (R D s : ℝ) :
    Tendsto (fun z : ℂ ↦ (W_D ((d : ℝ) / 2) R D z).re)
      (𝓝[Complex.im ⁻¹' Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2)]
        ((s : ℂ) - I * ((d : ℂ) / 2))) (𝓝 (h_ℓD ((d : ℝ) / 2) R D s)) := by
  have hℓ : 0 < (d : ℝ) / 2 := half_pos (Nat.cast_pos.mpr hd)
  obtain ⟨A, hA, hbound⟩ := exists_abs_h_ℓD_le hd R D
  rw [show ((d : ℂ) / 2) = ((d : ℝ) / 2 : ℝ) by
    rw [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat]]
  exact (tendsto_integral_bottom hℓ (lowerGammaBoundaryCapped_continuous hℓ R D) hA hbound
    (lowerGammaBoundaryCapped_central_poisson_shift_integrable hd R D) s).congr'
      (W_D_re_eventuallyEq hd R D _).symm

/-- Report Lemma 3.2: `Re W_D` extends continuously to the top edge, with trace `0`. -/
theorem tendsto_W_D_re_top {d : ℕ} (hd : 0 < d) (R D s : ℝ) :
    Tendsto (fun z : ℂ ↦ (W_D ((d : ℝ) / 2) R D z).re)
      (𝓝[Complex.im ⁻¹' Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2)]
        ((s : ℂ) + I * ((d : ℂ) / 2))) (𝓝 (0 : ℝ)) := by
  have hℓ : 0 < (d : ℝ) / 2 := half_pos (Nat.cast_pos.mpr hd)
  obtain ⟨A, hA, hbound⟩ := exists_abs_h_ℓD_le hd R D
  rw [show ((d : ℂ) / 2) = ((d : ℝ) / 2 : ℝ) by
    rw [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat]]
  exact (tendsto_integral_top hℓ (lowerGammaBoundaryCapped_continuous hℓ R D) hA hbound s).congr'
    (W_D_re_eventuallyEq hd R D _).symm

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

/-- The continuous extension of `Re W_D` to the closed strip `|Im z| ≤ λ`, with bottom trace
`h_{λ,D}` and top trace `0`; report Lemma 3.2. -/
def W_D_reExtension (d : ℕ) (R D : ℝ) : ℂ → ℝ :=
  stripTraceExtension (-((d : ℝ) / 2)) ((d : ℝ) / 2) (fun w : ℂ ↦ (W_D ((d : ℝ) / 2) R D w).re)
    (h_ℓD ((d : ℝ) / 2) R D) fun _ : ℝ ↦ 0

/-- The extension `W_D_reExtension` is continuous on the closed strip; report Lemma 3.2. -/
theorem W_D_reExtension_continuousOn {d : ℕ} (hd : 0 < d) (R D : ℝ) :
    ContinuousOn (W_D_reExtension d R D) (Complex.im ⁻¹' Icc (-((d : ℝ) / 2)) ((d : ℝ) / 2)) := by
  have hℓ : 0 < (d : ℝ) / 2 := half_pos (Nat.cast_pos.mpr hd)
  refine stripTraceExtension_continuousOn (by linarith) _ _ _
    (Complex.continuous_re.comp_continuousOn
      (lowerStripCappedGammaOuter_differentiableOn_dimension hd R D).continuousOn)
    (lowerGammaBoundaryCapped_continuous hℓ R D) continuous_const (fun s ↦ ?_) fun s ↦ ?_
  · simpa [sub_eq_add_neg] using tendsto_W_D_re_bottom hd R D s
  · simpa using tendsto_W_D_re_top hd R D s

/-- On the bottom edge `e^{-W_D} Z_g` has modulus at most `1` once `‖Z_g‖ ≤ exp h_{λ,D}` there. -/
private theorem exp_neg_W_D_reExtension_mul_norm_Z_g_bottom_le_one {d : ℕ} {ς : ℤˣ} (hd : 0 < d)
    (g : RadialEigenfunction d ς) (R D : ℝ)
    (hcap : ∀ y : ℝ, ‖Z_g hd g.toFun R ((y : ℂ) - I * ((d : ℂ) / 2))‖ ≤
      Real.exp (h_ℓD ((d : ℝ) / 2) R D y))
    (v : ℂ) (hv : v.im = -((d : ℝ) / 2)) :
    Real.exp (-(W_D_reExtension d R D v)) * ‖Z_g hd g.toFun R v‖ ≤ 1 := by
  have hnorm : ‖Z_g hd g.toFun R v‖ ≤ Real.exp (h_ℓD ((d : ℝ) / 2) R D v.re) := by
    have h := hcap v.re
    rwa [show (v.re : ℂ) - I * ((d : ℂ) / 2) = v from
      Complex.ext (by simp) (by simp [hv])] at h
  rw [show W_D_reExtension d R D v = h_ℓD ((d : ℝ) / 2) R D v.re by
    simp [W_D_reExtension, stripTraceExtension, hv]]
  calc Real.exp (-(h_ℓD ((d : ℝ) / 2) R D v.re)) * ‖Z_g hd g.toFun R v‖
      ≤ Real.exp (-(h_ℓD ((d : ℝ) / 2) R D v.re)) * Real.exp (h_ℓD ((d : ℝ) / 2) R D v.re) :=
        mul_le_mul_of_nonneg_left hnorm (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

/-- On the top edge `e^{-W_D} Z_g` has modulus at most `1`. -/
private theorem exp_neg_W_D_reExtension_mul_norm_Z_g_top_le_one {d : ℕ} {ς : ℤˣ} (hd : 0 < d)
    (g : RadialEigenfunction d ς) (R D : ℝ) (v : ℂ) (hv : v.im = (d : ℝ) / 2) :
    Real.exp (-(W_D_reExtension d R D v)) * ‖Z_g hd g.toFun R v‖ ≤ 1 := by
  have hℓ : 0 < (d : ℝ) / 2 := half_pos (Nat.cast_pos.mpr hd)
  have hnorm : ‖Z_g hd g.toFun R v‖ ≤ 1 := by
    have h := g.norm_Z_g_top_le_one hd R v.re
    rwa [show (v.re : ℂ) + I * ((d : ℂ) / 2) = v from
      Complex.ext (by simp) (by simp [hv])] at h
  rw [show W_D_reExtension d R D v = 0 by
    simp [W_D_reExtension, stripTraceExtension, hv, (by linarith : (d : ℝ) / 2 ≠ -((d : ℝ) / 2))]]
  simpa using hnorm

/-- Report Lemma 3.2: `|Z(s + iσλ)| ≤ exp(∫ P_σ(T) h_{λ,D}(s − λT) dT)`, by Phragmén–Lindelöf
applied to `e^{-W_D} Z_g`, whose modulus extends continuously to the closed strip with boundary
values at most `1`. -/
theorem norm_Z_g_le_exp_integral_of_cap {d : ℕ} {ς : ℤˣ} (hd : 0 < d)
    (g : RadialEigenfunction d ς) (R D : ℝ)
    (hcap : ∀ y : ℝ, ‖Z_g hd g.toFun R ((y : ℂ) - I * ((d : ℂ) / 2))‖ ≤
      Real.exp (h_ℓD ((d : ℝ) / 2) R D y))
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    ‖Z_g hd g.toFun R ((s : ℂ) + I * (σ * ((d : ℂ) / 2)))‖ ≤
      Real.exp (∫ T : ℝ, P_σ σ T * h_ℓD ((d : ℝ) / 2) R D (s - (d : ℝ) / 2 * T)) := by
  have hℓ : 0 < (d : ℝ) / 2 := half_pos (Nat.cast_pos.mpr hd)
  have hwidth : -((d : ℝ) / 2) < (d : ℝ) / 2 := by linarith
  have hZcont : ContinuousOn (Z_g hd g.toFun R)
      (Complex.im ⁻¹' Icc (-((d : ℝ) / 2)) ((d : ℝ) / 2)) := by
    have hcl : closure (Complex.im ⁻¹' Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2)) =
        Complex.im ⁻¹' Icc (-((d : ℝ) / 2)) ((d : ℝ) / 2) := by
      rw [Complex.closure_preimage_im, closure_Ioo hwidth.ne]
    simpa [hcl] using (g.diffContOnCl_Z_g hd R).continuousOn
  have hEint : ∀ v : ℂ, v.im ∈ Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2) →
      W_D_reExtension d R D v = (W_D ((d : ℝ) / 2) R D v).re := fun v hv ↦ by
    simp [W_D_reExtension, stripTraceExtension, (ne_of_gt hv.1 : v.im ≠ -((d : ℝ) / 2)),
      (ne_of_lt hv.2 : v.im ≠ (d : ℝ) / 2)]
  have hzim : ((s : ℂ) + I * (σ * ((d : ℂ) / 2))).im = σ * ((d : ℝ) / 2) := by simp
  have hzmem : ((s : ℂ) + I * (σ * ((d : ℂ) / 2))).im ∈
      Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2) := by
    rw [hzim]
    exact ⟨by nlinarith [mul_pos (show 0 < 1 + σ by linarith) hℓ],
      by nlinarith [mul_pos (show 0 < 1 - σ by linarith) hℓ]⟩
  have hmax := PhragmenLindelof.horizontal_strip_norm_extension hwidth one_pos
    (fun v ↦ Complex.exp (-(W_D ((d : ℝ) / 2) R D v)) * Z_g hd g.toFun R v)
    (fun v ↦ Real.exp (-(W_D_reExtension d R D v)) * ‖Z_g hd g.toFun R v‖)
    ((lowerStripCappedGammaOuter_differentiableOn_dimension hd R D).neg.cexp.mul
      (g.diffContOnCl_Z_g hd R).differentiableOn)
    ((W_D_reExtension_continuousOn hd R D).neg.rexp.mul hZcont.norm)
    (fun _ _ ↦ mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
    (fun v hv ↦ by rw [hEint v hv, norm_mul, Complex.norm_exp, Complex.neg_re])
    (exp_neg_W_D_reExtension_mul_norm_Z_g_bottom_le_one hd g R D hcap)
    (exp_neg_W_D_reExtension_mul_norm_Z_g_top_le_one hd g R D)
    (isBigO_exp_neg_W_D_mul_Z_g hd g R D) hzmem.1.le hzmem.2.le
  rw [(hEint _ hzmem).trans
    (lowerStripCappedGammaOuter_re_dimension (R := R) (D := D) hd hbelow habove s)] at hmax
  calc ‖Z_g hd g.toFun R ((s : ℂ) + I * (σ * ((d : ℂ) / 2)))‖
      = Real.exp (∫ T : ℝ, P_σ σ T * h_ℓD ((d : ℝ) / 2) R D (s - (d : ℝ) / 2 * T)) *
          (Real.exp (-(∫ T : ℝ, P_σ σ T * h_ℓD ((d : ℝ) / 2) R D (s - (d : ℝ) / 2 * T))) *
            ‖Z_g hd g.toFun R ((s : ℂ) + I * (σ * ((d : ℂ) / 2)))‖) := by
        rw [← mul_assoc (Real.exp _), ← Real.exp_add]; simp
    _ ≤ Real.exp (∫ T : ℝ, P_σ σ T * h_ℓD ((d : ℝ) / 2) R D (s - (d : ℝ) / 2 * T)) * 1 :=
        mul_le_mul_of_nonneg_left hmax (Real.exp_pos _).le
    _ = _ := mul_one _

/-- Report Lemma 3.2: for every large enough cap `D`, the normalized Mellin transform of a
radial eigenfunction is majorized on the strip by the Poisson extension of `h_{λ,D}`. -/
theorem exists_capped_poisson_majorization {d : ℕ} {ς : ℤˣ} (hd : 0 < d)
    (g : RadialEigenfunction d ς) {R : ℝ} (hR : 0 < R) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∀ {σ : ℝ}, -1 < σ → σ < 1 → ∀ s : ℝ,
      ‖Z_g hd g.toFun R ((s : ℂ) + I * (σ * ((d : ℂ) / 2)))‖ ≤
        Real.exp (∫ T : ℝ, P_σ σ T * h_ℓD ((d : ℝ) / 2) R D (s - (d : ℝ) / 2 * T)) := by
  obtain ⟨D₀, hbottom⟩ := exists_norm_Z_g_bottom_le_exp_h_ℓD hd g hR
  refine ⟨D₀, fun D hD ↦ ?_⟩
  intro σ hbelow habove s
  exact norm_Z_g_le_exp_integral_of_cap hd g R D (hbottom D hD) hbelow habove s

end

end CohnElkies
