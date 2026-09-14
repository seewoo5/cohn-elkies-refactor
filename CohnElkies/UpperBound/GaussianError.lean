import CohnElkies.UpperBound.SaddleTails

/-!
# The full-line Gaussian error (report §4.3, Lemma 4.8, (74)–(75))

Rescaling the cubic weight, the second-branch tail and its uniformity in `δ`, the splitting of
the full-line error into a central window and two tails, the `L¹` tails of the centred and of the
Gaussian integrands, and the conclusion: on both branches the source integral is a Gaussian
integral up to a relative error `< 1` for all large `d`
(`eventually_firstBranch_fullGaussianError`, `eventually_secondBranch_fullGaussianError`).
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section
open Filter MeasureTheory Real Set intervalIntegral
open scoped Topology

/-! ### Rescaling the cubic weight `1 + |T|³` -/

theorem sqrt_le_one_add {x : ℝ} (hx : 0 ≤ x) : √x ≤ 1 + x := by
  nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x, sq_nonneg (√x - 1)]

theorem tailWeight_le_scaled {s : ℝ} (hs : 0 < s) (T : ℝ) :
    saddleGaussianTailWeight T ≤ max 1 (s ^ 3)⁻¹ * saddleGaussianTailWeight (s * T) := by
  have hcube : (1 : ℝ) ≤ max 1 (s ^ 3)⁻¹ * s ^ 3 := by
    rw [← inv_mul_cancel₀ (by positivity : (s : ℝ) ^ 3 ≠ 0)]
    gcongr
    exact le_max_right _ _
  unfold saddleGaussianTailWeight
  rw [abs_mul, abs_of_pos hs]
  nlinarith [le_max_left (1 : ℝ) (s ^ 3)⁻¹, pow_nonneg (abs_nonneg T) 3,
    mul_le_mul_of_nonneg_right hcube (pow_nonneg (abs_nonneg T) 3)]

/-- Generic rescaling estimate: if `w (sT) ≤ 2e^{3g(sT)}` and `3g(sT) - k g(T) = -(k/2) g(T)`,
the `w`-weighted integral of `e^{-k g}` is at most `2 max(1, s⁻³)` times that of `e^{-(k/2)g}`. -/
theorem integral_tailWeight_le_scaled {g : ℝ → ℝ} {k s : ℝ} (hs : 0 < s)
    (hg : ∀ T : ℝ, saddleGaussianTailWeight (s * T) ≤ 2 * exp (3 * g (s * T)))
    (hscale : ∀ T : ℝ, 3 * g (s * T) + -k * g T = -(k / 2) * g T)
    (hw : Integrable fun T : ℝ ↦ saddleGaussianTailWeight T * exp (-k * g T))
    (hmaj : Integrable fun T : ℝ ↦ exp (-(k / 2) * g T)) :
    (∫ T : ℝ, saddleGaussianTailWeight T * exp (-k * g T)) ≤
      2 * max 1 (s ^ 3)⁻¹ * ∫ T : ℝ, exp (-(k / 2) * g T) := by
  have hpoint (T : ℝ) : saddleGaussianTailWeight T * exp (-k * g T) ≤
      2 * max 1 (s ^ 3)⁻¹ * exp (-(k / 2) * g T) := by
    calc saddleGaussianTailWeight T * exp (-k * g T)
        ≤ max 1 (s ^ 3)⁻¹ * (2 * exp (3 * g (s * T))) * exp (-k * g T) := by
          gcongr ?_ * _
          exact (tailWeight_le_scaled hs T).trans (by gcongr; exact hg T)
      _ = 2 * max 1 (s ^ 3)⁻¹ * exp (-(k / 2) * g T) := by
          rw [mul_assoc, mul_assoc, ← Real.exp_add, hscale]; ring
  calc (∫ T : ℝ, saddleGaussianTailWeight T * exp (-k * g T))
      ≤ ∫ T : ℝ, 2 * max 1 (s ^ 3)⁻¹ * exp (-(k / 2) * g T) :=
        integral_mono hw (hmaj.const_mul _) hpoint
    _ = 2 * max 1 (s ^ 3)⁻¹ * ∫ T : ℝ, exp (-(k / 2) * g T) := integral_const_mul _ _

theorem integral_tailWeight_gaussian_le {k : ℝ} (hk : 0 < k) :
    (∫ T : ℝ, saddleGaussianTailWeight T * exp (-k * T ^ 2)) ≤
      2 * max 1 ((√(k / 6) ^ 3)⁻¹) * √(π / (k / 2)) := by
  have hsq : √(k / 6) ^ 2 = k / 6 := Real.sq_sqrt (by positivity)
  rw [← integral_gaussian (k / 2)]
  exact integral_tailWeight_le_scaled (g := fun T ↦ T ^ 2) (Real.sqrt_pos.2 (by positivity))
    (fun T ↦ saddleGaussianTailWeight_le_two_exp_three_sq _) (fun T ↦ by rw [mul_pow, hsq]; ring)
    (saddleGaussianTailWeight_mul_gaussian_integrable hk)
    (integrable_exp_neg_mul_sq (by positivity))

theorem integral_tailWeight_expAbs_le {k : ℝ} (hk : 0 < k) :
    (∫ T : ℝ, saddleGaussianTailWeight T * exp (-k * |T|)) ≤
      2 * max 1 (((k / 6) ^ 3)⁻¹) * (2 / (k / 2)) := by
  rw [← saddle_integral_exp_neg_mul_abs (show (0 : ℝ) < k / 2 by positivity)]
  exact integral_tailWeight_le_scaled (g := abs) (by positivity : (0 : ℝ) < k / 6)
    (fun T ↦ saddleGaussianTailWeight_le_two_exp_three_abs _)
    (fun T ↦ by rw [abs_mul, abs_of_pos (show (0 : ℝ) < k / 6 by positivity)]; ring)
    (saddleGaussianTailWeight_mul_exp_abs_integrable hk)
    (integrable_exp_neg_mul_abs (by positivity))

/-! ### The second-branch tail, report Lemma 4.8 (74)–(75) -/

/-- Half-width `t₀ = 1/(2(B_ε+1))` of the window where `D_u` is quadratically coercive. -/
def secondBranchFreq (ε : ℝ) : ℝ := 1 / (2 * (Bε ε + 1))

/-- Gaussian rate `λV(1+δ)/(100e)` of the local lower bound for `D_u`. -/
def secondBranchRate (ε ℓ δ : ℝ) : ℝ := ℓ / (100 * exp 1) * V_u ε ℓ (1 + δ)

/-- Gaussian rate of the `Γ`-damping `D_γ` on the second branch. -/
def secondBranchGammaRate (ℓ δ : ℝ) : ℝ := ℓ / (8 * exp 1) / (2 + δ)

/-- Linear rate of the `Γ`-damping `D_γ` on the second branch. -/
def secondBranchLinearRate (ℓ : ℝ) : ℝ := ℓ / (8 * exp 1)

/-- Height of the shell barrier `D_B` outside the local window. -/
def secondBranchBarrier (ε ℓ δ : ℝ) : ℝ :=
  99 / 5000 * ℓ * Qε ε * exp (δ * Bε ε) * secondBranchFreq ε ^ 2

/-- Splitting `e^{-D_u}` into the local Gaussian and the barrier-suppressed outer part. -/
theorem eventually_secondBranch_damping_pointwise : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ ℓ : ℝ, 0 < ℓ →
    ∀ δ : ℝ, ε / 2 ≤ δ → ∀ T : ℝ,
      saddleGaussianTailWeight T * exp (-saddleSourceContourDamping ε ℓ (1 + δ) T) ≤
        saddleGaussianTailWeight T * exp (-secondBranchRate ε ℓ δ * T ^ 2) +
          exp (-secondBranchBarrier ε ℓ δ) *
            (saddleGaussianTailWeight T * exp (-secondBranchGammaRate ℓ δ * T ^ 2) +
              saddleGaussianTailWeight T * exp (-secondBranchLinearRate ℓ * |T|)) := by
  filter_upwards [self_mem_nhdsWithin,
      eventually_saddleSourceContourDamping_secondBranch_local_coercivity,
      eventually_upperSaddleDamping_gamma_add_shell] with ε hε hlocal hdom
  change 0 < ε at hε
  intro ℓ hℓ δ hδ T
  have hδ0 : (0 : ℝ) ≤ δ := by nlinarith
  have hB : (0 : ℝ) ≤ Bε ε := by unfold Bε; positivity
  have hw : 0 ≤ saddleGaussianTailWeight T := saddleGaussianTailWeight_nonneg T
  have hfirst : 0 ≤ saddleGaussianTailWeight T * exp (-secondBranchRate ε ℓ δ * T ^ 2) := by
    positivity
  have houter : 0 ≤ exp (-secondBranchBarrier ε ℓ δ) *
      (saddleGaussianTailWeight T * exp (-secondBranchGammaRate ℓ δ * T ^ 2) +
        saddleGaussianTailWeight T * exp (-secondBranchLinearRate ℓ * |T|)) := by positivity
  by_cases hinside : |T| ≤ secondBranchFreq ε
  · have hexp : exp (-saddleSourceContourDamping ε ℓ (1 + δ) T) ≤
        exp (-secondBranchRate ε ℓ δ * T ^ 2) := by
      refine Real.exp_le_exp.2 ?_
      have := hlocal ℓ hℓ δ hδ T (by simpa [secondBranchFreq] using hinside)
      unfold secondBranchRate
      linarith
    linarith [mul_le_mul_of_nonneg_left hexp hw]
  · have ht₀ : 0 < secondBranchFreq ε := by unfold secondBranchFreq Bε; positivity
    have hmin : secondBranchFreq ε ^ 2 ≤ min (T ^ 2) 1 := by
      refine le_min ?_ ?_
      · simpa [sq_abs] using pow_le_pow_left₀ ht₀.le (le_of_not_ge hinside) 2
      · have : secondBranchFreq ε ≤ 1 := by
          unfold secondBranchFreq
          rw [div_le_one (by positivity)]
          linarith
        nlinarith
    have hbarrier : secondBranchBarrier ε ℓ δ ≤ 99 / 100 * D_B ε ℓ δ T := by
      have hshell := positiveShellDamping_lower_bound (ε := ε) (ℓ := ℓ) (δ := δ) (T := T)
        hε hℓ.le hδ0
      have hstep := mul_le_mul_of_nonneg_left hmin
        (by positivity [shellWeight_pos ε] : (0 : ℝ) ≤ ℓ / 50 * Qε ε * exp (δ * Bε ε))
      unfold secondBranchBarrier
      nlinarith
    have hcombined : secondBranchBarrier ε ℓ δ +
        secondBranchLinearRate ℓ * min (T ^ 2 / (2 + δ)) |T| ≤
          saddleSourceContourDamping ε ℓ (1 + δ) T := by
      rw [saddleSourceContourDamping_eq_secondBranch]
      unfold secondBranchLinearRate
      linarith [hdom ℓ hℓ δ hδ T,
        upperGammaDamping_lower_bound hℓ (show (0 : ℝ) < 2 + δ by linarith) T]
    have hexp : exp (-saddleSourceContourDamping ε ℓ (1 + δ) T) ≤
        exp (-secondBranchBarrier ε ℓ δ) * (exp (-secondBranchGammaRate ℓ δ * T ^ 2) +
          exp (-secondBranchLinearRate ℓ * |T|)) := by
      calc exp (-saddleSourceContourDamping ε ℓ (1 + δ) T)
          ≤ exp (-(secondBranchBarrier ε ℓ δ +
              secondBranchLinearRate ℓ * min (T ^ 2 / (2 + δ)) |T|)) :=
            Real.exp_le_exp.2 (by linarith)
        _ = exp (-secondBranchBarrier ε ℓ δ) *
              exp (-secondBranchLinearRate ℓ * min (T ^ 2 / (2 + δ)) |T|) := by
            rw [← Real.exp_add]; congr 1; ring
        _ ≤ exp (-secondBranchBarrier ε ℓ δ) *
              (exp (-secondBranchLinearRate ℓ * (T ^ 2 / (2 + δ))) +
                exp (-secondBranchLinearRate ℓ * |T|)) := by
            gcongr
            exact saddle_exp_neg_mul_min_le_add (by unfold secondBranchLinearRate; positivity)
        _ = _ := by
            rw [show -secondBranchGammaRate ℓ δ * T ^ 2 =
              -secondBranchLinearRate ℓ * (T ^ 2 / (2 + δ)) by
                unfold secondBranchGammaRate secondBranchLinearRate; ring]
    linarith [mul_le_mul_of_nonneg_left hexp hw]

/-- Report (74): the weighted tail integral of `e^{-D_u}` past radius `R`. -/
theorem eventually_secondBranch_weighted_tail_le : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ ℓ : ℝ, 0 < ℓ →
    ∀ δ : ℝ, ε / 2 ≤ δ → ∀ R : ℝ, 0 ≤ R → 6 ≤ secondBranchRate ε ℓ δ →
      (∫ T : ℝ in saddleGaussianTailSet R,
          saddleGaussianTailWeight T * exp (-saddleSourceContourDamping ε ℓ (1 + δ) T)) ≤
        2 * exp (-(secondBranchRate ε ℓ δ / 4) * R ^ 2) * √(π / (secondBranchRate ε ℓ δ / 4)) +
          exp (-secondBranchBarrier ε ℓ δ) *
            (2 * max 1 ((√(secondBranchGammaRate ℓ δ / 6) ^ 3)⁻¹) *
                √(π / (secondBranchGammaRate ℓ δ / 2)) +
              2 * max 1 (((secondBranchLinearRate ℓ / 6) ^ 3)⁻¹) *
                (2 / (secondBranchLinearRate ℓ / 2))) := by
  filter_upwards [self_mem_nhdsWithin, eventually_saddleSource_secondBranch_weighted_integrable,
      eventually_secondBranch_damping_pointwise] with ε hε hsource hpoint
  change 0 < ε at hε
  intro ℓ hℓ δ hδ R hR hk
  have hη : (0 : ℝ) < 2 + δ := by nlinarith
  have hq : 0 < secondBranchGammaRate ℓ δ := by unfold secondBranchGammaRate; positivity
  have ha : 0 < secondBranchLinearRate ℓ := by unfold secondBranchLinearRate; positivity
  have hlocal := saddleGaussianTailWeight_mul_gaussian_integrable
    (show (0 : ℝ) < secondBranchRate ε ℓ δ by linarith)
  have hgamma := saddleGaussianTailWeight_mul_gaussian_integrable hq
  have hlinear := saddleGaussianTailWeight_mul_exp_abs_integrable ha
  have houter : Integrable fun T : ℝ ↦ exp (-secondBranchBarrier ε ℓ δ) *
      (saddleGaussianTailWeight T * exp (-secondBranchGammaRate ℓ δ * T ^ 2) +
        saddleGaussianTailWeight T * exp (-secondBranchLinearRate ℓ * |T|)) :=
    (hgamma.add hlinear).const_mul _
  have hgaussianTail := saddleGaussian_cubic_tail_integral_le hk hR
  have hgammaTail := setIntegral_le_integral (s := saddleGaussianTailSet R) hgamma
    (Filter.Eventually.of_forall fun T ↦
      mul_nonneg (saddleGaussianTailWeight_nonneg T) (Real.exp_pos _).le)
  have hlinearTail := setIntegral_le_integral (s := saddleGaussianTailSet R) hlinear
    (Filter.Eventually.of_forall fun T ↦
      mul_nonneg (saddleGaussianTailWeight_nonneg T) (Real.exp_pos _).le)
  have hgammaFull := integral_tailWeight_gaussian_le hq
  have hlinearFull := integral_tailWeight_expAbs_le ha
  calc (∫ T : ℝ in saddleGaussianTailSet R,
        saddleGaussianTailWeight T * exp (-saddleSourceContourDamping ε ℓ (1 + δ) T))
      ≤ ∫ T : ℝ in saddleGaussianTailSet R, (saddleGaussianTailWeight T *
          exp (-secondBranchRate ε ℓ δ * T ^ 2) + exp (-secondBranchBarrier ε ℓ δ) *
            (saddleGaussianTailWeight T * exp (-secondBranchGammaRate ℓ δ * T ^ 2) +
              saddleGaussianTailWeight T * exp (-secondBranchLinearRate ℓ * |T|))) :=
        MeasureTheory.setIntegral_mono_on (hsource ℓ hℓ δ hδ).integrableOn
          (hlocal.add houter).integrableOn (saddleGaussianTailSet_measurable R)
          fun T _ ↦ hpoint ℓ hℓ δ hδ T
    _ = (∫ T : ℝ in saddleGaussianTailSet R,
          saddleGaussianTailWeight T * exp (-secondBranchRate ε ℓ δ * T ^ 2)) +
        exp (-secondBranchBarrier ε ℓ δ) * ((∫ T : ℝ in saddleGaussianTailSet R,
            saddleGaussianTailWeight T * exp (-secondBranchGammaRate ℓ δ * T ^ 2)) +
          ∫ T : ℝ in saddleGaussianTailSet R,
            saddleGaussianTailWeight T * exp (-secondBranchLinearRate ℓ * |T|)) := by
        rw [MeasureTheory.integral_add hlocal.integrableOn houter.integrableOn,
          MeasureTheory.integral_const_mul,
          MeasureTheory.integral_add hgamma.integrableOn hlinear.integrableOn]
    _ ≤ 2 * exp (-(secondBranchRate ε ℓ δ / 4) * R ^ 2) * √(π / (secondBranchRate ε ℓ δ / 4)) +
        exp (-secondBranchBarrier ε ℓ δ) *
          ((∫ T : ℝ, saddleGaussianTailWeight T * exp (-secondBranchGammaRate ℓ δ * T ^ 2)) +
            ∫ T : ℝ, saddleGaussianTailWeight T * exp (-secondBranchLinearRate ℓ * |T|)) := by
        gcongr
    _ ≤ _ := by gcongr

/-- Report (75): the same tail after the Gaussian rescaling `T ↦ T √(λV)`. -/
theorem eventually_secondBranch_normalized_tail_le : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ ℓ : ℝ, 0 < ℓ →
    ∀ δ : ℝ, ε / 2 ≤ δ → ∀ z : ℝ, 0 ≤ z → 6 ≤ secondBranchRate ε ℓ δ →
      √(ℓ * V_u ε ℓ (1 + δ)) * (∫ T : ℝ in saddleGaussianTailSet
            (z / √(ℓ * V_u ε ℓ (1 + δ))),
          saddleGaussianTailWeight T * exp (-saddleSourceContourDamping ε ℓ (1 + δ) T)) ≤
        2 * √(400 * exp 1 * π) * exp (-(z ^ 2 / (400 * exp 1))) +
          √(ℓ * V_u ε ℓ (1 + δ)) * exp (-secondBranchBarrier ε ℓ δ) *
            (2 * max 1 ((√(secondBranchGammaRate ℓ δ / 6) ^ 3)⁻¹) *
                √(π / (secondBranchGammaRate ℓ δ / 2)) +
              2 * max 1 (((secondBranchLinearRate ℓ / 6) ^ 3)⁻¹) *
                (2 / (secondBranchLinearRate ℓ / 2))) := by
  filter_upwards [eventually_secondBranch_weighted_tail_le,
      eventually_saddleSourceGaussianVariance_secondBranch_pos] with ε htail hvariance
  intro ℓ hℓ δ hδ z hz hk
  have hV : 0 < V_u ε ℓ (1 + δ) := hvariance ℓ hℓ δ hδ
  have hLV : 0 < ℓ * V_u ε ℓ (1 + δ) := mul_pos hℓ hV
  have hpref : √(ℓ * V_u ε ℓ (1 + δ)) * √(π / (secondBranchRate ε ℓ δ / 4)) =
      √(400 * exp 1 * π) := by
    rw [← Real.sqrt_mul hLV.le]
    congr 1
    unfold secondBranchRate
    field_simp [hℓ.ne', hV.ne', (Real.exp_pos 1).ne']
    ring
  have hexponent : -(secondBranchRate ε ℓ δ / 4) * (z / √(ℓ * V_u ε ℓ (1 + δ))) ^ 2 =
      -(z ^ 2 / (400 * exp 1)) := by
    rw [div_pow, Real.sq_sqrt hLV.le]
    unfold secondBranchRate
    field_simp [hℓ.ne', hV.ne', (Real.exp_pos 1).ne']
    ring
  calc √(ℓ * V_u ε ℓ (1 + δ)) * (∫ T : ℝ in saddleGaussianTailSet
          (z / √(ℓ * V_u ε ℓ (1 + δ))),
        saddleGaussianTailWeight T * exp (-saddleSourceContourDamping ε ℓ (1 + δ) T))
      ≤ √(ℓ * V_u ε ℓ (1 + δ)) * (2 * exp (-(secondBranchRate ε ℓ δ / 4) *
            (z / √(ℓ * V_u ε ℓ (1 + δ))) ^ 2) * √(π / (secondBranchRate ε ℓ δ / 4)) +
          exp (-secondBranchBarrier ε ℓ δ) *
            (2 * max 1 ((√(secondBranchGammaRate ℓ δ / 6) ^ 3)⁻¹) *
                √(π / (secondBranchGammaRate ℓ δ / 2)) +
              2 * max 1 (((secondBranchLinearRate ℓ / 6) ^ 3)⁻¹) *
                (2 / (secondBranchLinearRate ℓ / 2)))) :=
        mul_le_mul_of_nonneg_left (htail ℓ hℓ δ hδ _ (by positivity) hk) (Real.sqrt_nonneg _)
    _ = _ := by
        rw [hexponent]
        linear_combination (2 * exp (-(z ^ 2 / (400 * exp 1)))) * hpref

/-! ### Bounding the outer moments by a power of `2 + δ` -/

theorem inv_sqrt_cube_le {q : ℝ} (hq : 0 < q) : (√(q / 6) ^ 3)⁻¹ ≤ 1 + (6 / q) ^ 3 := by
  have hs : 0 < √(q / 6) := Real.sqrt_pos.2 (by positivity)
  have hsquare : √(q / 6) ^ 2 = q / 6 := Real.sq_sqrt (by positivity)
  have hid : ((√(q / 6) ^ 3)⁻¹) ^ 2 = (6 / q) ^ 3 := by
    field_simp [hq.ne', hs.ne']
    nlinarith [congrArg (fun x : ℝ ↦ x ^ 3) hsquare]
  rw [← hid]
  nlinarith [sq_nonneg ((√(q / 6) ^ 3)⁻¹ - 1 / 2)]

theorem gammaCoefficient_le {q η C : ℝ} (hq : 0 < q) (hη : 1 ≤ η) (hC : 0 < C)
    (hrate : 1 / q ≤ C * η) :
    2 * max 1 ((√(q / 6) ^ 3)⁻¹) * √(π / (q / 2)) ≤
      2 * (1 + (6 * C) ^ 3) * (1 + 2 * π * C) * η ^ 4 := by
  have hcube : (1 : ℝ) ≤ η ^ 3 := by simpa using pow_le_pow_left₀ zero_le_one hη 3
  have hqscaled : 6 / q ≤ 6 * C * η := by
    rw [show (6 : ℝ) / q = 6 * (1 / q) by ring]; linarith
  have hmax : max 1 ((√(q / 6) ^ 3)⁻¹) ≤ (1 + (6 * C) ^ 3) * η ^ 3 :=
    calc max 1 ((√(q / 6) ^ 3)⁻¹) ≤ 1 + (6 / q) ^ 3 :=
          max_le (le_add_of_nonneg_right (by positivity)) (inv_sqrt_cube_le hq)
      _ ≤ 1 + (6 * C * η) ^ 3 := by gcongr
      _ ≤ (1 + (6 * C) ^ 3) * η ^ 3 := by
          nlinarith [mul_nonneg (show (0 : ℝ) ≤ (6 * C) ^ 3 by positivity)
            (show (0 : ℝ) ≤ η ^ 3 - 1 by linarith)]
  have hsqrt : √(π / (q / 2)) ≤ (1 + 2 * π * C) * η :=
    calc √(π / (q / 2)) ≤ 1 + π / (q / 2) := sqrt_le_one_add (by positivity)
      _ ≤ 1 + 2 * π * C * η := by
          have : π / (q / 2) = 2 * π * (1 / q) := by field_simp [hq.ne']
          nlinarith [mul_le_mul_of_nonneg_left hrate (by positivity : (0 : ℝ) ≤ 2 * π)]
      _ ≤ (1 + 2 * π * C) * η := by nlinarith [Real.pi_pos]
  calc 2 * max 1 ((√(q / 6) ^ 3)⁻¹) * √(π / (q / 2))
      ≤ 2 * ((1 + (6 * C) ^ 3) * η ^ 3) * ((1 + 2 * π * C) * η) := by gcongr
    _ = 2 * (1 + (6 * C) ^ 3) * (1 + 2 * π * C) * η ^ 4 := by ring

theorem linearCoefficient_le {a η C : ℝ} (ha : 0 < a) (hη : 1 ≤ η) (hC : 0 < C)
    (hrate : 1 / a ≤ C) :
    2 * max 1 (((a / 6) ^ 3)⁻¹) * (2 / (a / 2)) ≤ 8 * C * (1 + (6 * C) ^ 3) * η ^ 4 := by
  have hfour : (1 : ℝ) ≤ η ^ 4 := by simpa using pow_le_pow_left₀ zero_le_one hη 4
  have hbase : 6 / a ≤ 6 * C := by
    rw [show (6 : ℝ) / a = 6 * (1 / a) by ring]; linarith
  have hcubes : (6 / a) ^ 3 ≤ (6 * C) ^ 3 := by gcongr
  have hmax : max 1 (((a / 6) ^ 3)⁻¹) ≤ 1 + (6 * C) ^ 3 := by
    rw [show ((a / 6) ^ 3)⁻¹ = (6 / a) ^ 3 by field_simp [ha.ne']]
    exact max_le (le_add_of_nonneg_right (by positivity)) (by linarith)
  have hlinear : 2 / (a / 2) ≤ 4 * C := by
    rw [show 2 / (a / 2) = 4 * (1 / a) by field_simp [ha.ne']; ring]
    linarith
  calc 2 * max 1 (((a / 6) ^ 3)⁻¹) * (2 / (a / 2)) ≤ 2 * (1 + (6 * C) ^ 3) * (4 * C) := by gcongr
    _ ≤ 8 * C * (1 + (6 * C) ^ 3) * η ^ 4 := by
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ 8 * C * (1 + (6 * C) ^ 3) by positivity)
          (show (0 : ℝ) ≤ η ^ 4 - 1 by linarith)]

/-- The constant multiplying `(2 + δ)⁴` in the outer-moment bound of report Lemma 4.8. -/
def secondBranchMomentCoeff : ℝ :=
  2 * (1 + (48 * exp 1) ^ 3) * (1 + 16 * π * exp 1) + 64 * exp 1 * (1 + (48 * exp 1) ^ 3)

theorem secondBranchMomentCoeff_pos : 0 < secondBranchMomentCoeff := by
  unfold secondBranchMomentCoeff; positivity

theorem secondBranch_outerMoment_le {ℓ δ : ℝ} (hℓ : 1 ≤ ℓ) (hδ : 0 ≤ δ) :
    2 * max 1 ((√(secondBranchGammaRate ℓ δ / 6) ^ 3)⁻¹) *
          √(π / (secondBranchGammaRate ℓ δ / 2)) +
        2 * max 1 (((secondBranchLinearRate ℓ / 6) ^ 3)⁻¹) *
          (2 / (secondBranchLinearRate ℓ / 2)) ≤ secondBranchMomentCoeff * (2 + δ) ^ 4 := by
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hη : (1 : ℝ) ≤ 2 + δ := by linarith
  have hC : (0 : ℝ) < 8 * exp 1 := by positivity
  have hq : 0 < secondBranchGammaRate ℓ δ := by unfold secondBranchGammaRate; positivity
  have ha : 0 < secondBranchLinearRate ℓ := by unfold secondBranchLinearRate; positivity
  have hqrate : 1 / secondBranchGammaRate ℓ δ ≤ 8 * exp 1 * (2 + δ) := by
    rw [show 1 / secondBranchGammaRate ℓ δ = 8 * exp 1 * (2 + δ) / ℓ by
      unfold secondBranchGammaRate; field_simp, div_le_iff₀ hℓ0]
    nlinarith [mul_nonneg (mul_nonneg hC.le (by linarith : (0 : ℝ) ≤ 2 + δ))
      (by linarith : (0 : ℝ) ≤ ℓ - 1)]
  have harate : 1 / secondBranchLinearRate ℓ ≤ 8 * exp 1 := by
    rw [show 1 / secondBranchLinearRate ℓ = 8 * exp 1 / ℓ by
      unfold secondBranchLinearRate; field_simp, div_le_iff₀ hℓ0]
    nlinarith [mul_nonneg hC.le (by linarith : (0 : ℝ) ≤ ℓ - 1)]
  have hgamma := gammaCoefficient_le hq hη hC hqrate
  have hlinear := linearCoefficient_le ha hη hC harate
  unfold secondBranchMomentCoeff
  nlinarith

/-! ### Uniformity in `δ` of the second-branch tail -/

/-- The constant in the second-branch upper bound `V(1+δ) ≤ C_ε e^{(B_ε+1)δ}`. -/
def secondBranchVarCoeff (ε : ℝ) : ℝ := 2 + (Bε ε + 1) ^ 2 * Qε ε

theorem secondBranchVarCoeff_pos (ε : ℝ) : 0 < secondBranchVarCoeff ε := by
  unfold secondBranchVarCoeff
  positivity [shellWeight_pos ε]

theorem eventually_secondBranch_sqrtVariance_le : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ ℓ : ℝ, 1 ≤ ℓ →
    ∀ δ : ℝ, ε / 2 ≤ δ → √(ℓ * V_u ε ℓ (1 + δ)) ≤
      √(secondBranchVarCoeff ε) * √ℓ * exp ((Bε ε + 1) / 2 * δ) := by
  filter_upwards [self_mem_nhdsWithin, eventually_upperSaddleVariance_bounds] with ε hε hvariance
  change 0 < ε at hε
  intro ℓ hℓ δ hδ
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hδ0 : (0 : ℝ) ≤ δ := by nlinarith
  have hB : (0 : ℝ) ≤ Bε ε := by unfold Bε; positivity
  have hC : 0 < secondBranchVarCoeff ε := secondBranchVarCoeff_pos ε
  have hupper : V_u ε ℓ (1 + δ) ≤ secondBranchVarCoeff ε * exp ((Bε ε + 1) * δ) := by
    have hexp : (1 : ℝ) ≤ exp ((Bε ε + 1) * δ) := Real.one_le_exp (by positivity)
    have hfirst : 1 / (2 * (2 + δ)) ≤ (1 : ℝ) := by
      rw [div_le_one (by positivity)]; linarith
    have hsecond : 1 / (ℓ * (2 + δ) ^ 2) ≤ (1 : ℝ) := by
      rw [div_le_one (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hℓ (sq_nonneg (2 + δ)), sq_nonneg (1 + δ)]
    have hfull : V_u ε ℓ (1 + δ) ≤ 1 / (2 * (2 + δ)) + 1 / (ℓ * (2 + δ) ^ 2) + V_B ε δ := by
      simpa [V_u] using (hvariance ℓ hℓ0 δ hδ).2
    have hshell : V_B ε δ ≤ (Bε ε + 1) ^ 2 * Qε ε * exp ((Bε ε + 1) * δ) := by
      have h := (upperPositiveShellVariance_bounds hε hδ0).2
      rwa [show δ * (Bε ε + 1) = (Bε ε + 1) * δ from mul_comm _ _] at h
    unfold secondBranchVarCoeff
    nlinarith
  calc √(ℓ * V_u ε ℓ (1 + δ)) ≤ √(ℓ * (secondBranchVarCoeff ε * exp ((Bε ε + 1) * δ))) := by
        gcongr
    _ = √(secondBranchVarCoeff ε) * √ℓ * exp ((Bε ε + 1) / 2 * δ) := by
        rw [Real.sqrt_mul hℓ0.le, Real.sqrt_mul hC.le, ← Real.exp_half,
          show (Bε ε + 1) * δ / 2 = (Bε ε + 1) / 2 * δ by ring]
        ring

theorem tendsto_secondBranchTailMajorant :
    Tendsto (fun ℓ : ℝ ↦ 2 * √(400 * exp 1 * π) * exp (-(ℓ ^ (1 / 6 : ℝ) / (400 * exp 1))))
      atTop (𝓝 (0 : ℝ)) := by
  have hneg : Tendsto (fun ℓ : ℝ ↦ -(ℓ ^ (1 / 6 : ℝ) / (400 * exp 1))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).atTop_div_const (by positivity))
  simpa using (Real.tendsto_exp_atBot.comp hneg).const_mul (2 * √(400 * exp 1 * π))

/-- Report Lemma 4.8: the rescaled second-branch tail past `λ^{1/12}` is uniformly small. -/
theorem eventually_saddleSource_secondBranch_uniform_tail : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ κ : ℝ,
    0 < κ → ∀ᶠ ℓ : ℝ in atTop, ∀ δ : ℝ, ε / 2 ≤ δ →
      √(ℓ * V_u ε ℓ (1 + δ)) * (∫ T : ℝ in saddleGaussianTailSet
          (ℓ ^ (1 / 12 : ℝ) / √(ℓ * V_u ε ℓ (1 + δ))),
        saddleGaussianTailWeight T * exp (-saddleSourceContourDamping ε ℓ (1 + δ) T)) < κ := by
  filter_upwards [self_mem_nhdsWithin, eventually_secondBranch_normalized_tail_le,
      eventually_secondBranch_sqrtVariance_le,
      eventually_saddleSourceGaussianVariance_secondBranch_floor]
    with ε hε htail hsqrt hfloor
  change 0 < ε at hε
  intro κ hκ
  have hB : 0 < Bε ε := by unfold Bε; positivity
  have hQ : 0 < Qε ε := shellWeight_pos ε
  have ht₀ : 0 < secondBranchFreq ε := by unfold secondBranchFreq Bε; positivity
  have hc : (0 : ℝ) < 99 / 5000 * secondBranchFreq ε ^ 2 := by positivity
  have hV₀ : 0 < saddleSourceSecondBranchVarianceFloor ε :=
    saddleSourceSecondBranchVarianceFloor_pos hε
  have hK : (0 : ℝ) < √(secondBranchVarCoeff ε) * secondBranchMomentCoeff :=
    mul_pos (Real.sqrt_pos.2 (secondBranchVarCoeff_pos ε)) secondBranchMomentCoeff_pos
  have hhalf : 0 < κ / 2 := by positivity
  have houter := eventually_saddleGaussianOuterPhi_uniform_polynomial hB hQ hc
    (by positivity : (0 : ℝ) ≤ ε / 2) hK.le (κ / 2) hhalf
  have hlocal := tendsto_secondBranchTailMajorant.eventually (Iio_mem_nhds hhalf)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
      eventually_ge_atTop (600 * exp 1 / saddleSourceSecondBranchVarianceFloor ε), hlocal, houter]
    with ℓ hℓ hone hlocalℓ houterℓ
  intro δ hδ
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hδ0 : (0 : ℝ) ≤ δ := by nlinarith
  have hVfloor : saddleSourceSecondBranchVarianceFloor ε ≤ V_u ε ℓ (1 + δ) := hfloor ℓ hℓ0 δ hδ
  have hV : 0 < V_u ε ℓ (1 + δ) := hV₀.trans_le hVfloor
  have hq : 0 < secondBranchGammaRate ℓ δ := by unfold secondBranchGammaRate; positivity
  have ha : 0 < secondBranchLinearRate ℓ := by unfold secondBranchLinearRate; positivity
  have hscale : 600 * exp 1 ≤ ℓ * V_u ε ℓ (1 + δ) := by
    have h := (div_le_iff₀ hV₀).mp hone
    linarith [mul_le_mul_of_nonneg_left hVfloor hℓ0.le]
  have hk : 6 ≤ secondBranchRate ε ℓ δ := by
    unfold secondBranchRate
    rw [show ℓ / (100 * exp 1) * V_u ε ℓ (1 + δ) = ℓ * V_u ε ℓ (1 + δ) / (100 * exp 1) by ring,
      le_div_iff₀ (by positivity)]
    linarith
  have hsource := htail ℓ hℓ0 δ hδ (ℓ ^ (1 / 12 : ℝ)) (Real.rpow_nonneg hℓ0.le _) hk
  have hlocalterm : 2 * √(400 * exp 1 * π) *
      exp (-((ℓ ^ (1 / 12 : ℝ)) ^ 2 / (400 * exp 1))) < κ / 2 := by
    rw [show ((ℓ : ℝ) ^ (1 / 12 : ℝ)) ^ 2 = ℓ ^ (1 / 6 : ℝ) by
      rw [← Real.rpow_natCast (ℓ ^ (1 / 12 : ℝ)) 2, ← Real.rpow_mul hℓ0.le]; norm_num]
    exact hlocalℓ
  have houterterm : √(ℓ * V_u ε ℓ (1 + δ)) * exp (-secondBranchBarrier ε ℓ δ) *
      (2 * max 1 ((√(secondBranchGammaRate ℓ δ / 6) ^ 3)⁻¹) *
          √(π / (secondBranchGammaRate ℓ δ / 2)) +
        2 * max 1 (((secondBranchLinearRate ℓ / 6) ^ 3)⁻¹) *
          (2 / (secondBranchLinearRate ℓ / 2))) < κ / 2 := by
    have hmoment := secondBranch_outerMoment_le hℓ hδ0
    have hsqrtsource := hsqrt ℓ hℓ δ hδ
    calc √(ℓ * V_u ε ℓ (1 + δ)) * exp (-secondBranchBarrier ε ℓ δ) *
          (2 * max 1 ((√(secondBranchGammaRate ℓ δ / 6) ^ 3)⁻¹) *
              √(π / (secondBranchGammaRate ℓ δ / 2)) +
            2 * max 1 (((secondBranchLinearRate ℓ / 6) ^ 3)⁻¹) *
              (2 / (secondBranchLinearRate ℓ / 2)))
        ≤ √(secondBranchVarCoeff ε) * √ℓ * exp ((Bε ε + 1) / 2 * δ) *
            exp (-secondBranchBarrier ε ℓ δ) * (secondBranchMomentCoeff * (2 + δ) ^ 4) := by
          gcongr
      _ = √(secondBranchVarCoeff ε) * secondBranchMomentCoeff * √ℓ *
            exp ((Bε ε + 1) / 2 * δ) * (2 + δ) ^ 4 *
            exp (-(99 / 5000 * secondBranchFreq ε ^ 2) * ℓ * Qε ε * exp (Bε ε * δ)) := by
          unfold secondBranchBarrier
          ring_nf
      _ < κ / 2 := houterℓ δ hδ
  linarith

end

noncomputable section

open Filter MeasureTheory Real Set
open scoped Topology

theorem eventually_eps_le_quarter : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ≤ 1 / 4 := by
  have h : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  filter_upwards [h.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))] with ε hε
  exact hε.le

/-! ### Splitting the full-line error into a central window and two tails -/

theorem fullLine_error_le_central_add_tails {F G : ℝ → ℂ} (hF : Integrable F) (hG : Integrable G)
    (R : ℝ) :
    ‖(∫ T : ℝ, F T) - ∫ T : ℝ, G T‖ ≤ ‖∫ T : ℝ in Icc (-R) R, (F T - G T)‖ +
      (∫ T : ℝ in saddleGaussianTailSet R, ‖F T‖) +
      ∫ T : ℝ in saddleGaussianTailSet R, ‖G T‖ := by
  have hdiff : Integrable fun T : ℝ ↦ F T - G T := hF.sub hG
  have hsub : (Icc (-R) R)ᶜ ⊆ saddleGaussianTailSet R := fun T hT ↦ by
    change R ≤ |T|
    by_contra hnot
    exact hT ⟨(abs_lt.mp (lt_of_not_ge hnot)).1.le, (abs_lt.mp (lt_of_not_ge hnot)).2.le⟩
  have hsubae : (Icc (-R) R)ᶜ ≤ᵐ[volume] saddleGaussianTailSet R :=
    Filter.Eventually.of_forall hsub
  have hmonoF : (∫ T : ℝ in (Icc (-R) R)ᶜ, ‖F T‖) ≤ ∫ T : ℝ in saddleGaussianTailSet R, ‖F T‖ :=
    setIntegral_mono_set hF.norm.integrableOn
      (Filter.Eventually.of_forall fun T ↦ norm_nonneg (F T)) hsubae
  have hmonoG : (∫ T : ℝ in (Icc (-R) R)ᶜ, ‖G T‖) ≤ ∫ T : ℝ in saddleGaussianTailSet R, ‖G T‖ :=
    setIntegral_mono_set hG.norm.integrableOn
      (Filter.Eventually.of_forall fun T ↦ norm_nonneg (G T)) hsubae
  calc ‖(∫ T : ℝ, F T) - ∫ T : ℝ, G T‖ = ‖∫ T : ℝ, (F T - G T)‖ := by
        rw [MeasureTheory.integral_sub hF hG]
    _ = ‖(∫ T : ℝ in Icc (-R) R, (F T - G T)) + ∫ T : ℝ in (Icc (-R) R)ᶜ, (F T - G T)‖ := by
        rw [integral_add_compl measurableSet_Icc hdiff]
    _ ≤ ‖∫ T : ℝ in Icc (-R) R, (F T - G T)‖ + ‖∫ T : ℝ in (Icc (-R) R)ᶜ, (F T - G T)‖ :=
        norm_add_le _ _
    _ ≤ ‖∫ T : ℝ in Icc (-R) R, (F T - G T)‖ +
          ((∫ T : ℝ in saddleGaussianTailSet R, ‖F T‖) +
            ∫ T : ℝ in saddleGaussianTailSet R, ‖G T‖) := by
        gcongr
        calc ‖∫ T : ℝ in (Icc (-R) R)ᶜ, (F T - G T)‖ ≤ ∫ T : ℝ in (Icc (-R) R)ᶜ, ‖F T - G T‖ :=
              norm_integral_le_integral_norm _
          _ ≤ ∫ T : ℝ in (Icc (-R) R)ᶜ, (‖F T‖ + ‖G T‖) :=
              MeasureTheory.setIntegral_mono_on hdiff.norm.integrableOn
                (hF.norm.add hG.norm).integrableOn measurableSet_Icc.compl
                fun T _ ↦ norm_sub_le _ _
          _ = (∫ T : ℝ in (Icc (-R) R)ᶜ, ‖F T‖) + ∫ T : ℝ in (Icc (-R) R)ᶜ, ‖G T‖ :=
              MeasureTheory.integral_add hF.norm.integrableOn hG.norm.integrableOn
          _ ≤ _ := add_le_add hmonoF hmonoG
    _ = _ := by ring

/-- If the central error is `< A/4` and both rescaled tails are `< √(2π)A/8`, the full-line
error is smaller than the Gaussian mass, report §4.3. -/
theorem fullLine_error_lt_gaussian {ε ℓ u R A : ℝ} {F G : ℝ → ℂ} (hF : Integrable F)
    (hG : Integrable G) (hℓ : 0 < ℓ) (hV : 0 < V_u ε ℓ u) (hA : 0 < A)
    (hcentral : ‖∫ T : ℝ in Icc (-R) R, (F T - G T)‖ <
      1 / 4 * A * ∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T)
    (hsource : √(ℓ * V_u ε ℓ u) * (∫ T : ℝ in saddleGaussianTailSet R, ‖F T‖) <
      √(2 * π) / 8 * A)
    (hgaussian : √(ℓ * V_u ε ℓ u) * (∫ T : ℝ in saddleGaussianTailSet R, ‖G T‖) <
      √(2 * π) / 8 * A) :
    ‖(∫ T : ℝ, F T) - ∫ T : ℝ, G T‖ < A * ∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T := by
  have hLV : 0 < ℓ * V_u ε ℓ u := mul_pos hℓ hV
  have hS : 0 < √(ℓ * V_u ε ℓ u) := Real.sqrt_pos.2 hLV
  have hmass : √(ℓ * V_u ε ℓ u) * (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) = √(2 * π) := by
    rw [saddleSourceGaussianKernel_integral, ← Real.sqrt_mul hLV.le]
    congr 1
    field_simp
  have hmass' : √(ℓ * V_u ε ℓ u) * (1 / 8 * A * ∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) =
      √(2 * π) / 8 * A := by
    rw [show √(ℓ * V_u ε ℓ u) * (1 / 8 * A * ∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) =
        1 / 8 * A * (√(ℓ * V_u ε ℓ u) * ∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) by ring,
      hmass]
    ring
  have hkey : ∀ X : ℝ, √(ℓ * V_u ε ℓ u) * X < √(2 * π) / 8 * A →
      X < 1 / 8 * A * ∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T := fun X hX ↦
    lt_of_mul_lt_mul_left (by rw [hmass']; exact hX) hS.le
  linarith [fullLine_error_le_central_add_tails hF hG R, hkey _ hsource, hkey _ hgaussian,
    mul_pos hA (saddleSourceGaussianKernel_integral_pos hℓ hV)]

/-! ### `L¹` tails of the centred integrands -/

/-- Tail bound for a centred integrand deduced from a uniform polynomial bound for `P`. -/
theorem centered_tail_integral_le {F : ℝ → ℂ} {P : ℂ → ℂ} {D : ℝ → ℝ} {C u R : ℝ}
    (hF : Integrable F) (hW : Integrable fun T : ℝ ↦ saddleGaussianTailWeight T * exp (-D T))
    (hnorm : ∀ T : ℝ, ‖F T‖ = exp (-D T) * ‖P ((T : ℂ) + I * (u : ℂ))‖)
    (hpoly : ∀ T : ℝ, ‖P ((T : ℂ) + I * (u : ℂ))‖ ≤ C * (1 + |T| ^ 3) * ‖P (I * (u : ℂ))‖) :
    (∫ T : ℝ in saddleGaussianTailSet R, ‖F T‖) ≤ C * ‖P (I * (u : ℂ))‖ *
      ∫ T : ℝ in saddleGaussianTailSet R, saddleGaussianTailWeight T * exp (-D T) := by
  have hpoint : ∀ T ∈ saddleGaussianTailSet R,
      ‖F T‖ ≤ C * ‖P (I * (u : ℂ))‖ * (saddleGaussianTailWeight T * exp (-D T)) := fun T _ ↦ by
    have hp := hpoly T
    rw [hnorm T]
    unfold saddleGaussianTailWeight
    calc exp (-D T) * ‖P ((T : ℂ) + I * (u : ℂ))‖
        ≤ exp (-D T) * (C * (1 + |T| ^ 3) * ‖P (I * (u : ℂ))‖) := by gcongr
      _ = C * ‖P (I * (u : ℂ))‖ * ((1 + |T| ^ 3) * exp (-D T)) := by ring
  calc (∫ T : ℝ in saddleGaussianTailSet R, ‖F T‖)
      ≤ ∫ T : ℝ in saddleGaussianTailSet R,
          C * ‖P (I * (u : ℂ))‖ * (saddleGaussianTailWeight T * exp (-D T)) :=
        MeasureTheory.setIntegral_mono_on hF.norm.integrableOn (hW.const_mul _).integrableOn
          (saddleGaussianTailSet_measurable R) hpoint
    _ = _ := MeasureTheory.integral_const_mul _ _

/-- Tail bound for the centred integrand of a saddle polynomial with range bounds. -/
theorem SaddleRangeBounds.exists_centered_tail_bound {ε : ℝ} (hε : 0 < ε)
    (horder : a₀ε ε ≤ Aε ε) {P : ℂ → ℂ} (hP : IsSaddlePolynomial ε P) {u₀ : ℝ}
    (hrange : SaddleRangeBounds P u₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ ℓ : ℝ, 0 < ℓ → ∀ u : ℝ, -1 < u → u₀ ≤ u → ∀ v R : ℝ,
      Integrable (fun T : ℝ ↦ saddleGaussianTailWeight T *
          exp (-saddleSourceContourDamping ε ℓ u T)) →
        (∫ T : ℝ in saddleGaussianTailSet R, ‖centeredIntegrand ε ℓ P u v T‖) ≤
          C * ‖P (I * (u : ℂ))‖ * ∫ T : ℝ in saddleGaussianTailSet R,
            saddleGaussianTailWeight T * exp (-saddleSourceContourDamping ε ℓ u T) := by
  obtain ⟨C, hC, hpoly⟩ := hrange.weighted
  exact ⟨C, hC, fun ℓ hℓ u hu hu₀ v R hW ↦ centered_tail_integral_le
    (centeredIntegrand_integrable hε hℓ hu horder hP v) hW
    (centeredIntegrand_norm hε hℓ hu horder P v) (hpoly u hu₀)⟩

/-- From `S · Y < κ/C` and `X ≤ C·A·Y` one gets `S · X < κ · A`. -/
theorem scaled_tail_lt_of_bound {S A C κ X Y : ℝ} (hS : 0 ≤ S) (hA : 0 < A) (hC : 0 < C)
    (hbound : X ≤ C * A * Y) (hlt : S * Y < κ / C) : S * X < κ * A := by
  rw [lt_div_iff₀ hC] at hlt
  nlinarith [mul_le_mul_of_nonneg_left hbound hS, mul_lt_mul_of_pos_right hlt hA]

/-! ### `L¹` tails of the Gaussian integrands -/

theorem gaussianIntegrand_tail_norm_eq (ε ℓ : ℝ) (P : ℂ → ℂ) (u R : ℝ) :
    (∫ T : ℝ in saddleGaussianTailSet R, ‖gaussianIntegrand ε ℓ P u T‖) =
      ‖P (I * (u : ℂ))‖ * ∫ T : ℝ in saddleGaussianTailSet R,
        saddleSourceGaussianKernel ε ℓ u T := by
  have h : ∀ T : ℝ, ‖gaussianIntegrand ε ℓ P u T‖ =
      saddleSourceGaussianKernel ε ℓ u T * ‖P (I * (u : ℂ))‖ := fun T ↦ by
    rw [gaussianIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (show 0 < saddleSourceGaussianKernel ε ℓ u T by
        unfold saddleSourceGaussianKernel; positivity)]
  simp_rw [h]
  rw [MeasureTheory.integral_mul_const, mul_comm]

/-- The Gaussian tail past `z/√(λV)` is `O(e^{-z²/8})` once `λV ≥ 12`. -/
theorem gaussianKernel_normalized_tail_le {ε ℓ u z : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V_u ε ℓ u)
    (hz : 0 ≤ z) (hlarge : 12 ≤ ℓ * V_u ε ℓ u) :
    √(ℓ * V_u ε ℓ u) * (∫ T : ℝ in saddleGaussianTailSet (z / √(ℓ * V_u ε ℓ u)),
        saddleSourceGaussianKernel ε ℓ u T) ≤ 4 * √(2 * π) * exp (-(z ^ 2 / 8)) := by
  have hLV : 0 < ℓ * V_u ε ℓ u := mul_pos hℓ hV
  have hsq : √(ℓ * V_u ε ℓ u) ^ 2 = ℓ * V_u ε ℓ u := Real.sq_sqrt hLV.le
  have hk : (6 : ℝ) ≤ ℓ * V_u ε ℓ u / 2 := by linarith
  have hR : 0 ≤ z / √(ℓ * V_u ε ℓ u) := by positivity
  have hpoint : ∀ T ∈ saddleGaussianTailSet (z / √(ℓ * V_u ε ℓ u)),
      saddleSourceGaussianKernel ε ℓ u T ≤
        saddleGaussianTailWeight T * exp (-(ℓ * V_u ε ℓ u / 2) * T ^ 2) := fun T _ ↦ by
    have hw : 1 ≤ saddleGaussianTailWeight T := by
      unfold saddleGaussianTailWeight
      nlinarith [pow_nonneg (abs_nonneg T) 3]
    unfold saddleSourceGaussianKernel
    nlinarith [Real.exp_pos (-(ℓ * V_u ε ℓ u / 2) * T ^ 2)]
  have hcompare := MeasureTheory.setIntegral_mono_on
    (saddleSourceGaussianKernel_integrable hℓ hV).integrableOn
    (saddleGaussianTailWeight_mul_gaussian_integrable (show (0 : ℝ) < ℓ * V_u ε ℓ u / 2 by
      linarith)).integrableOn (saddleGaussianTailSet_measurable _) hpoint
  have hexp : -(ℓ * V_u ε ℓ u / 2 / 4) * (z / √(ℓ * V_u ε ℓ u)) ^ 2 = -(z ^ 2 / 8) := by
    rw [div_pow, hsq]
    field_simp
    ring
  have hroot : √(ℓ * V_u ε ℓ u) * √(π / (ℓ * V_u ε ℓ u / 2 / 4)) = 2 * √(2 * π) := by
    rw [← Real.sqrt_mul hLV.le, show ℓ * V_u ε ℓ u * (π / (ℓ * V_u ε ℓ u / 2 / 4)) =
        2 ^ 2 * (2 * π) by field_simp [hℓ.ne', hV.ne']; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  calc √(ℓ * V_u ε ℓ u) * (∫ T : ℝ in saddleGaussianTailSet (z / √(ℓ * V_u ε ℓ u)),
        saddleSourceGaussianKernel ε ℓ u T)
      ≤ √(ℓ * V_u ε ℓ u) * (∫ T : ℝ in saddleGaussianTailSet (z / √(ℓ * V_u ε ℓ u)),
          saddleGaussianTailWeight T * exp (-(ℓ * V_u ε ℓ u / 2) * T ^ 2)) :=
        mul_le_mul_of_nonneg_left hcompare (Real.sqrt_nonneg _)
    _ ≤ √(ℓ * V_u ε ℓ u) * (2 * exp (-(ℓ * V_u ε ℓ u / 2 / 4) * (z / √(ℓ * V_u ε ℓ u)) ^ 2) *
          √(π / (ℓ * V_u ε ℓ u / 2 / 4))) :=
        mul_le_mul_of_nonneg_left (saddleGaussian_cubic_tail_integral_le hk hR)
          (Real.sqrt_nonneg _)
    _ = 4 * √(2 * π) * exp (-(z ^ 2 / 8)) := by
        rw [hexp]
        linear_combination (2 * exp (-(z ^ 2 / 8))) * hroot

/-- Majorant `4√(2π) e^{-x^{1/6}/8}` of the normalized Gaussian tails. -/
def gaussianNormalizedTailMajorant (x : ℝ) : ℝ := 4 * √(2 * π) * exp (-(x ^ (1 / 6 : ℝ) / 8))

theorem tendsto_gaussianNormalizedTailMajorant :
    Tendsto gaussianNormalizedTailMajorant atTop (𝓝 (0 : ℝ)) := by
  have hneg : Tendsto (fun x : ℝ ↦ -(x ^ (1 / 6 : ℝ) / 8)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).atTop_div_const (by norm_num))
  unfold gaussianNormalizedTailMajorant
  simpa using (Real.tendsto_exp_atBot.comp hneg).const_mul (4 * √(2 * π))

theorem eventually_firstBranch_uniform_gaussian_tail : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ κ : ℝ, 0 < κ →
    ∀ᶠ ℓ : ℝ in atTop, ∀ u : ℝ, -1 < u → u ≤ 1 + ε / 2 → log ℓ / 4 ≤ ℓ * (1 + u) →
      √(ℓ * V_u ε ℓ u) * (∫ T : ℝ in saddleGaussianTailSet
          (saddleSourceFirstBranchCentralRadius ε ℓ u),
        saddleSourceGaussianKernel ε ℓ u T) < κ := by
  filter_upwards [self_mem_nhdsWithin, eventually_eps_le_quarter,
      eventually_upper_shortCutoff_le_shortEndpoint, eventually_upper_shortMargin_positive,
      eventually_saddleSourceGaussianVariance_firstBranch_pos]
    with ε hε hεsmall horder hmargin hvariance
  change 0 < ε at hε
  intro κ hκ
  have hU : (0 : ℝ) < 2 + ε / 2 := by positivity
  have hmargin' : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a := fun a ha ↦ by linarith [hmargin a ha]
  have hlog : Tendsto (fun ℓ : ℝ ↦ log ℓ / 4) atTop atTop :=
    Real.tendsto_log_atTop.atTop_div_const (by norm_num)
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (12 * (2 + ε / 2) / ε),
      hlog.eventually (eventually_ge_atTop (0 : ℝ)),
      (tendsto_gaussianNormalizedTailMajorant.comp hlog).eventually (Iio_mem_nhds hκ)]
    with ℓ hℓ hthreshold hlognonneg hdecayℓ
  intro u hulower huupper hlogscale
  have hη : (0 : ℝ) < 1 + u := by linarith
  have hV : 0 < V_u ε ℓ u := hvariance ℓ hℓ u hulower huupper
  have hlarge : 12 ≤ ℓ * V_u ε ℓ u := by
    have h1 : ε ≤ (2 + ε / 2) * V_u ε ℓ u :=
      (upperFirstBranch_saddleSourceGaussianVariance_scaled_lower_bound hε hεsmall hℓ hulower
        huupper horder hmargin').trans (mul_le_mul_of_nonneg_right (by linarith) hV.le)
    have h2 : 12 * (2 + ε / 2) ≤ ℓ * ε := (div_le_iff₀ hε).mp hthreshold
    nlinarith [mul_le_mul_of_nonneg_left h1 hℓ.le, hU]
  have hsquare : ((ℓ * (1 + u)) ^ (1 / 12 : ℝ)) ^ 2 = (ℓ * (1 + u)) ^ (1 / 6 : ℝ) := by
    rw [← Real.rpow_natCast ((ℓ * (1 + u)) ^ (1 / 12 : ℝ)) 2,
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ ℓ * (1 + u))]
    norm_num
  have hpower : (log ℓ / 4) ^ (1 / 6 : ℝ) ≤ ((ℓ * (1 + u)) ^ (1 / 12 : ℝ)) ^ 2 := by
    rw [hsquare]
    exact Real.rpow_le_rpow hlognonneg hlogscale (by norm_num)
  calc √(ℓ * V_u ε ℓ u) * (∫ T : ℝ in saddleGaussianTailSet
        (saddleSourceFirstBranchCentralRadius ε ℓ u), saddleSourceGaussianKernel ε ℓ u T)
      ≤ 4 * √(2 * π) * exp (-(((ℓ * (1 + u)) ^ (1 / 12 : ℝ)) ^ 2 / 8)) :=
        gaussianKernel_normalized_tail_le hℓ hV (Real.rpow_nonneg (by positivity) _) hlarge
    _ ≤ gaussianNormalizedTailMajorant (log ℓ / 4) := by
        unfold gaussianNormalizedTailMajorant
        gcongr
    _ < κ := hdecayℓ

theorem eventually_secondBranch_uniform_gaussian_tail : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ κ : ℝ, 0 < κ →
    ∀ᶠ ℓ : ℝ in atTop, ∀ δ : ℝ, ε / 2 ≤ δ → √(ℓ * V_u ε ℓ (1 + δ)) *
      (∫ T : ℝ in saddleGaussianTailSet (saddleSourceSecondBranchCentralRadius ε ℓ (1 + δ)),
        saddleSourceGaussianKernel ε ℓ (1 + δ) T) < κ := by
  filter_upwards [self_mem_nhdsWithin, eventually_saddleSourceGaussianVariance_secondBranch_floor]
    with ε hε hfloor
  change 0 < ε at hε
  intro κ hκ
  have hV₀ : 0 < saddleSourceSecondBranchVarianceFloor ε :=
    saddleSourceSecondBranchVarianceFloor_pos hε
  filter_upwards [eventually_gt_atTop (0 : ℝ),
      eventually_ge_atTop (12 / saddleSourceSecondBranchVarianceFloor ε),
      tendsto_gaussianNormalizedTailMajorant.eventually (Iio_mem_nhds hκ)]
    with ℓ hℓ hthreshold hdecayℓ
  intro δ hδ
  have hVlower := hfloor ℓ hℓ δ hδ
  have hV : 0 < V_u ε ℓ (1 + δ) := hV₀.trans_le hVlower
  have hlarge : 12 ≤ ℓ * V_u ε ℓ (1 + δ) := by
    have h := (div_le_iff₀ hV₀).mp hthreshold
    nlinarith [mul_le_mul_of_nonneg_left hVlower hℓ.le]
  have hsquare : (ℓ ^ (1 / 12 : ℝ)) ^ 2 = ℓ ^ (1 / 6 : ℝ) := by
    rw [← Real.rpow_natCast (ℓ ^ (1 / 12 : ℝ)) 2, ← Real.rpow_mul hℓ.le]
    norm_num
  calc √(ℓ * V_u ε ℓ (1 + δ)) * (∫ T : ℝ in saddleGaussianTailSet
        (saddleSourceSecondBranchCentralRadius ε ℓ (1 + δ)),
        saddleSourceGaussianKernel ε ℓ (1 + δ) T)
      ≤ 4 * √(2 * π) * exp (-((ℓ ^ (1 / 12 : ℝ)) ^ 2 / 8)) :=
        gaussianKernel_normalized_tail_le hℓ hV (Real.rpow_nonneg hℓ.le _) hlarge
    _ = gaussianNormalizedTailMajorant ℓ := by
        unfold gaussianNormalizedTailMajorant
        rw [hsquare]
    _ < κ := hdecayℓ

end

noncomputable section

open Filter MeasureTheory Real Set intervalIntegral
open scoped Topology

theorem eventually_firstBranch_sourceL1Tail : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ κ : ℝ, 0 < κ →
    ∀ (P : ℂ → ℂ) (u₀ : ℝ), IsSaddlePolynomial ε P → SaddleRangeBounds P u₀ →
      ∀ᶠ ℓ : ℝ in atTop, ∀ u : ℝ, -1 < u → u ≤ 1 + ε / 2 → log ℓ / 4 ≤ ℓ * (1 + u) → u₀ ≤ u →
        √(ℓ * V_u ε ℓ u) * (∫ T : ℝ in saddleGaussianTailSet
            (saddleSourceFirstBranchCentralRadius ε ℓ u),
          ‖centeredIntegrand ε ℓ P u (vℓ ε ℓ u) T‖) < κ * ‖P (I * (u : ℂ))‖ := by
  filter_upwards [self_mem_nhdsWithin, eventually_eps_le_quarter,
      eventually_upper_shortCutoff_le_shortEndpoint, eventually_upper_shortMargin_positive,
      eventually_saddleSource_firstBranch_uniform_tail]
    with ε hε hεsmall horder hmargin htail
  change 0 < ε at hε
  have hmargin' : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a := fun a ha ↦ by linarith [hmargin a ha]
  intro κ hκ P u₀ hP hrange
  obtain ⟨C, hC, hbound⟩ := hrange.exists_centered_tail_bound hε horder hP
  filter_upwards [eventually_gt_atTop (0 : ℝ), htail (κ / C) (div_pos hκ hC)] with ℓ hℓ ht
  intro u hu huupper hstar hu₀
  exact scaled_tail_lt_of_bound (Real.sqrt_nonneg _) (hrange.norm_pos u hu₀) hC
    (hbound ℓ hℓ u hu hu₀ _ _ (saddleSource_firstBranch_weighted_integrable hε hεsmall hℓ hu
      huupper horder hmargin')) (ht u hu huupper hstar)

theorem eventually_firstBranch_gaussianL1Tail : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ κ : ℝ, 0 < κ →
    ∀ (P : ℂ → ℂ) (u₀ : ℝ), SaddleRangeBounds P u₀ →
      ∀ᶠ ℓ : ℝ in atTop, ∀ u : ℝ, -1 < u → u ≤ 1 + ε / 2 → log ℓ / 4 ≤ ℓ * (1 + u) → u₀ ≤ u →
        √(ℓ * V_u ε ℓ u) * (∫ T : ℝ in saddleGaussianTailSet
            (saddleSourceFirstBranchCentralRadius ε ℓ u),
          ‖gaussianIntegrand ε ℓ P u T‖) < κ * ‖P (I * (u : ℂ))‖ := by
  filter_upwards [eventually_firstBranch_uniform_gaussian_tail] with ε htail
  intro κ hκ P u₀ hrange
  filter_upwards [htail κ hκ] with ℓ hℓ u hu huupper hstar hu₀
  rw [gaussianIntegrand_tail_norm_eq]
  nlinarith [mul_lt_mul_of_pos_left (hℓ u hu huupper hstar) (hrange.norm_pos u hu₀)]

/-- Report §4.3, first branch: the centred integral of a saddle polynomial `P` is approximated by
its Gaussian with an error smaller than the Gaussian mass `‖P(iu)‖ ∫ e^{-λV T²/2}`. -/
theorem eventually_firstBranch_fullGaussianError : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    ∀ (P : ℂ → ℂ) (u₀ : ℝ), IsSaddlePolynomial ε P → SaddleRangeBounds P u₀ →
      ∀ᶠ ℓ : ℝ in atTop, ∀ u : ℝ, -1 < u → u ≤ 1 + ε / 2 → log ℓ / 4 ≤ ℓ * (1 + u) → u₀ ≤ u →
        ‖(∫ T : ℝ, centeredIntegrand ε ℓ P u (vℓ ε ℓ u) T) -
            (∫ T : ℝ, gaussianIntegrand ε ℓ P u T)‖ <
          ‖P (I * (u : ℂ))‖ * (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) := by
  filter_upwards [self_mem_nhdsWithin, eventually_upper_shortCutoff_le_shortEndpoint,
      eventually_saddleSourceGaussianVariance_firstBranch_pos,
      eventually_firstBranch_centralGaussianError, eventually_firstBranch_sourceL1Tail,
      eventually_firstBranch_gaussianL1Tail]
    with ε hε horder hvariance hcentral hsource hgaussian
  change 0 < ε at hε
  intro P u₀ hP hrange
  have ha : (0 : ℝ) < √(2 * π) / 8 := by positivity
  filter_upwards [eventually_gt_atTop (0 : ℝ), hcentral (1 / 4 : ℝ) (by norm_num) P u₀ hP hrange,
      hsource (√(2 * π) / 8) ha P u₀ hP hrange, hgaussian (√(2 * π) / 8) ha P u₀ hrange]
    with ℓ hℓ hc hs hg
  intro u hu huupper hstar hu₀
  have hV : 0 < V_u ε ℓ u := hvariance ℓ hℓ u hu huupper
  exact fullLine_error_lt_gaussian (centeredIntegrand_integrable hε hℓ hu horder hP _)
    (gaussianIntegrand_integrable hℓ hV P) hℓ hV (hrange.norm_pos u hu₀)
    (hc u hu huupper hstar hu₀) (hs u hu huupper hstar hu₀) (hg u hu huupper hstar hu₀)

theorem eventually_secondBranch_sourceL1Tail : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ κ : ℝ, 0 < κ →
    ∀ (P : ℂ → ℂ) (u₀ : ℝ), IsSaddlePolynomial ε P → SaddleRangeBounds P u₀ →
      ∀ᶠ ℓ : ℝ in atTop, ∀ δ : ℝ, ε / 2 ≤ δ → u₀ ≤ 1 + δ →
        √(ℓ * V_u ε ℓ (1 + δ)) * (∫ T : ℝ in saddleGaussianTailSet
            (saddleSourceSecondBranchCentralRadius ε ℓ (1 + δ)),
          ‖centeredIntegrand ε ℓ P (1 + δ) (vℓ ε ℓ (1 + δ)) T‖) <
        κ * ‖P (I * ((1 + δ : ℝ) : ℂ))‖ := by
  filter_upwards [self_mem_nhdsWithin, eventually_upper_shortCutoff_le_shortEndpoint,
      eventually_saddleSource_secondBranch_weighted_integrable,
      eventually_saddleSource_secondBranch_uniform_tail]
    with ε hε horder hweight htail
  change 0 < ε at hε
  intro κ hκ P u₀ hP hrange
  obtain ⟨C, hC, hbound⟩ := hrange.exists_centered_tail_bound hε horder hP
  filter_upwards [eventually_gt_atTop (0 : ℝ), htail (κ / C) (div_pos hκ hC)] with ℓ hℓ ht
  intro δ hδ hu₀
  have hu : (-1 : ℝ) < 1 + δ := by linarith
  exact scaled_tail_lt_of_bound (Real.sqrt_nonneg _) (hrange.norm_pos _ hu₀) hC
    (hbound ℓ hℓ _ hu hu₀ _ _ (hweight ℓ hℓ δ hδ)) (ht δ hδ)

theorem eventually_secondBranch_gaussianL1Tail : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ κ : ℝ, 0 < κ →
    ∀ (P : ℂ → ℂ) (u₀ : ℝ), SaddleRangeBounds P u₀ →
      ∀ᶠ ℓ : ℝ in atTop, ∀ δ : ℝ, ε / 2 ≤ δ → u₀ ≤ 1 + δ →
        √(ℓ * V_u ε ℓ (1 + δ)) * (∫ T : ℝ in saddleGaussianTailSet
            (saddleSourceSecondBranchCentralRadius ε ℓ (1 + δ)),
          ‖gaussianIntegrand ε ℓ P (1 + δ) T‖) < κ * ‖P (I * ((1 + δ : ℝ) : ℂ))‖ := by
  filter_upwards [eventually_secondBranch_uniform_gaussian_tail] with ε htail
  intro κ hκ P u₀ hrange
  filter_upwards [htail κ hκ] with ℓ hℓ δ hδ hu₀
  rw [gaussianIntegrand_tail_norm_eq]
  nlinarith [mul_lt_mul_of_pos_left (hℓ δ hδ) (hrange.norm_pos _ hu₀)]

/-- Report §4.3, second branch: the centred integral of a saddle polynomial `P` is approximated
by its Gaussian with an error smaller than the Gaussian mass. -/
theorem eventually_secondBranch_fullGaussianError : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    ∀ (P : ℂ → ℂ) (u₀ : ℝ), IsSaddlePolynomial ε P → SaddleRangeBounds P u₀ →
      ∀ᶠ ℓ : ℝ in atTop, ∀ δ : ℝ, ε / 2 ≤ δ → u₀ ≤ 1 + δ →
        ‖(∫ T : ℝ, centeredIntegrand ε ℓ P (1 + δ) (vℓ ε ℓ (1 + δ)) T) -
            (∫ T : ℝ, gaussianIntegrand ε ℓ P (1 + δ) T)‖ <
          ‖P (I * ((1 + δ : ℝ) : ℂ))‖ * (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ (1 + δ) T) := by
  filter_upwards [self_mem_nhdsWithin, eventually_upper_shortCutoff_le_shortEndpoint,
      eventually_saddleSourceGaussianVariance_secondBranch_pos,
      eventually_secondBranch_centralGaussianError, eventually_secondBranch_sourceL1Tail,
      eventually_secondBranch_gaussianL1Tail]
    with ε hε horder hvariance hcentral hsource hgaussian
  change 0 < ε at hε
  intro P u₀ hP hrange
  have ha : (0 : ℝ) < √(2 * π) / 8 := by positivity
  filter_upwards [eventually_gt_atTop (0 : ℝ), hcentral (1 / 4 : ℝ) (by norm_num) P u₀ hP hrange,
      hsource (√(2 * π) / 8) ha P u₀ hP hrange, hgaussian (√(2 * π) / 8) ha P u₀ hrange]
    with ℓ hℓ hc hs hg
  intro δ hδ hu₀
  have hu : (-1 : ℝ) < 1 + δ := by linarith
  have hV : 0 < V_u ε ℓ (1 + δ) := hvariance ℓ hℓ δ hδ
  exact fullLine_error_lt_gaussian (centeredIntegrand_integrable hε hℓ hu horder hP _)
    (gaussianIntegrand_integrable hℓ hV P) hℓ hV (hrange.norm_pos _ hu₀) (hc δ hδ hu₀)
    (hs δ hδ hu₀) (hg δ hδ hu₀)

end

end CohnElkies
