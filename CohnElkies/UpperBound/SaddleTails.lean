import CohnElkies.UpperBound.GammaPhase
import CohnElkiesForMathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Tail estimates on the saddle contour (report §4.3, Lemma 4.8)

The Gaussian tail weight and its integrals, the first-branch tail of the source integrand and its
uniformity in the polynomial, the central window of the Gaussian approximation (central radii
and central Gaussian error on both branches), the second-branch damping coercivity, and the
`SaddleRangeBounds` structure recording the bounds on `P` used on a branch.
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory Real Set
open scoped Topology

/-- The cubic weight `1 + |T|³` majorising the polynomial factors along the saddle contour. -/
def saddleGaussianTailWeight (T : ℝ) : ℝ := 1 + |T| ^ 3

theorem saddleGaussianTailWeight_nonneg (T : ℝ) : 0 ≤ saddleGaussianTailWeight T := by
  unfold saddleGaussianTailWeight; positivity

/-- If `|T| ≤ e ^ x` for some `x ≥ 0`, the cubic weight is at most `2 e ^ (3x)`. -/
theorem saddleGaussianTailWeight_le_two_exp_three {T x : ℝ} (hx : 0 ≤ x) (hT : |T| ≤ exp x) :
    saddleGaussianTailWeight T ≤ 2 * exp (3 * x) := by
  have hexp : exp (3 * x) = exp x ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have hone : 1 ≤ exp (3 * x) := Real.one_le_exp (by positivity)
  have hcube : |T| ^ 3 ≤ exp (3 * x) := by
    rw [hexp]; exact pow_le_pow_left₀ (abs_nonneg T) hT 3
  unfold saddleGaussianTailWeight
  linarith

theorem saddleGaussianTailWeight_le_two_exp_three_sq (T : ℝ) :
    saddleGaussianTailWeight T ≤ 2 * exp (3 * T ^ 2) :=
  saddleGaussianTailWeight_le_two_exp_three (sq_nonneg T)
    ((by nlinarith [sq_nonneg (|T| - 1), sq_abs T, abs_nonneg T] : |T| ≤ T ^ 2 + 1).trans
      (Real.add_one_le_exp _))

theorem saddleGaussianTailWeight_le_two_exp_three_abs (T : ℝ) :
    saddleGaussianTailWeight T ≤ 2 * exp (3 * |T|) :=
  saddleGaussianTailWeight_le_two_exp_three (abs_nonneg T)
    ((by linarith : |T| ≤ |T| + 1).trans (Real.add_one_le_exp _))

theorem saddle_integral_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    (∫ T : ℝ, exp (-a * |T|)) = 2 / a := by
  rw [integral_comp_abs (f := fun T : ℝ ↦ exp (-a * T)),
    integral_exp_mul_Ioi (neg_lt_zero.mpr ha) (0 : ℝ)]
  simp [div_eq_mul_inv]

theorem saddleGaussianTailWeight_mul_gaussian_integrable {k : ℝ} (hk : 0 < k) :
    Integrable fun T : ℝ ↦ saddleGaussianTailWeight T * exp (-k * T ^ 2) := by
  have hcube : Integrable fun T : ℝ ↦ T ^ 3 * exp (-k * T ^ 2) := by
    simpa [Real.rpow_natCast] using
      integrable_rpow_mul_exp_neg_mul_sq hk (s := (3 : ℝ)) (by norm_num)
  refine ((integrable_exp_neg_mul_sq hk).add hcube.norm).congr ?_
  filter_upwards [] with T
  simp [saddleGaussianTailWeight, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), add_mul]

theorem saddleGaussianTailWeight_mul_exp_abs_integrable {k : ℝ} (hk : 0 < k) :
    Integrable fun T : ℝ ↦ saddleGaussianTailWeight T * exp (-k * |T|) := by
  refine ((integrable_exp_neg_mul_abs hk).add
    (integrable_abs_pow_mul_exp_neg_mul_abs 3 hk)).congr ?_
  filter_upwards [] with T
  simp [saddleGaussianTailWeight, add_mul]

/-- The tail region `R ≤ |T|` of the saddle contour. -/
def saddleGaussianTailSet (R : ℝ) : Set ℝ := {T : ℝ | R ≤ |T|}

theorem saddleGaussianTailSet_measurable (R : ℝ) : MeasurableSet (saddleGaussianTailSet R) :=
  measurableSet_le measurable_const measurable_abs

/-- Generic tail estimate: if the damping profile `p` is at least `P ≥ 0` on the tail region and
`k ≥ 6`, then a quarter of the damping already absorbs the cubic weight. -/
theorem saddleGaussianTailWeight_tail_integral_le {k R P J : ℝ} {p : ℝ → ℝ} (hk : 6 ≤ k)
    (hP : 0 ≤ P) (hweight : ∀ T, saddleGaussianTailWeight T ≤ 2 * exp (3 * p T))
    (hmono : ∀ T ∈ saddleGaussianTailSet R, P ≤ p T)
    (hsrc : Integrable fun T : ℝ ↦ saddleGaussianTailWeight T * exp (-k * p T))
    (hmaj : Integrable fun T : ℝ ↦ exp (-(k / 4) * p T))
    (hJ : (∫ T : ℝ, exp (-(k / 4) * p T)) = J) :
    (∫ T : ℝ in saddleGaussianTailSet R, saddleGaussianTailWeight T * exp (-k * p T)) ≤
      2 * exp (-(k / 4) * P) * J := by
  have hmajc : Integrable fun T : ℝ ↦ 2 * exp (-(k / 4) * P) * exp (-(k / 4) * p T) :=
    hmaj.const_mul _
  have hpoint : ∀ T ∈ saddleGaussianTailSet R, saddleGaussianTailWeight T * exp (-k * p T) ≤
      2 * exp (-(k / 4) * P) * exp (-(k / 4) * p T) := fun T hT ↦ by
    have hp := hmono T hT
    calc saddleGaussianTailWeight T * exp (-k * p T)
        ≤ 2 * exp (3 * p T) * exp (-k * p T) := by gcongr; exact hweight T
      _ = 2 * exp (3 * p T + -k * p T) := by rw [Real.exp_add]; ring
      _ ≤ 2 * exp (-(k / 4) * P + -(k / 4) * p T) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
            nlinarith [mul_nonneg (show (0 : ℝ) ≤ 3 * k / 4 - 3 by linarith) (sub_nonneg.mpr hp),
              mul_nonneg (show (0 : ℝ) ≤ k / 2 - 3 by linarith) hP])) (by norm_num)
      _ = 2 * exp (-(k / 4) * P) * exp (-(k / 4) * p T) := by rw [Real.exp_add]; ring
  calc (∫ T : ℝ in saddleGaussianTailSet R, saddleGaussianTailWeight T * exp (-k * p T))
      ≤ ∫ T : ℝ in saddleGaussianTailSet R, 2 * exp (-(k / 4) * P) * exp (-(k / 4) * p T) :=
        setIntegral_mono_on hsrc.integrableOn hmajc.integrableOn
          (saddleGaussianTailSet_measurable R) hpoint
    _ ≤ ∫ T : ℝ, 2 * exp (-(k / 4) * P) * exp (-(k / 4) * p T) :=
        setIntegral_le_integral hmajc (.of_forall fun T ↦ by positivity)
    _ = 2 * exp (-(k / 4) * P) * J := by rw [integral_const_mul, hJ]

theorem saddleGaussian_cubic_tail_integral_le {k R : ℝ} (hk : 6 ≤ k) (hR : 0 ≤ R) :
    (∫ T : ℝ in saddleGaussianTailSet R, saddleGaussianTailWeight T * exp (-k * T ^ 2)) ≤
      2 * exp (-(k / 4) * R ^ 2) * √(π / (k / 4)) :=
  saddleGaussianTailWeight_tail_integral_le hk (sq_nonneg R)
    saddleGaussianTailWeight_le_two_exp_three_sq
    (fun T hT ↦ by simpa [sq_abs] using pow_le_pow_left₀ hR hT 2)
    (saddleGaussianTailWeight_mul_gaussian_integrable (by linarith))
    (integrable_exp_neg_mul_sq (by linarith)) (integral_gaussian _)

theorem saddleExponential_cubic_tail_integral_le {k R : ℝ} (hk : 6 ≤ k) (hR : 0 ≤ R) :
    (∫ T : ℝ in saddleGaussianTailSet R, saddleGaussianTailWeight T * exp (-k * |T|)) ≤
      2 * exp (-(k / 4) * R) * (2 / (k / 4)) :=
  saddleGaussianTailWeight_tail_integral_le hk hR saddleGaussianTailWeight_le_two_exp_three_abs
    (fun _ hT ↦ hT) (saddleGaussianTailWeight_mul_exp_abs_integrable (by linarith))
    (integrable_exp_neg_mul_abs (by linarith)) (saddle_integral_exp_neg_mul_abs (by linarith))

/-- The outer exponent `Φ δ = (B+1)δ/2 + 4 log (2+δ) - c ℓ Q e ^ (Bδ)` of Lemma 4.8. -/
def saddleGaussianOuterPhi (B Q c ℓ δ : ℝ) : ℝ :=
  (B + 1) / 2 * δ + 4 * log (2 + δ) - c * ℓ * Q * exp (B * δ)

theorem saddleGaussianOuterPhi_le_endpointBarrier {B Q c ℓ δ₀ δ : ℝ} (hQ : 0 < Q) (hc : 0 < c)
    (hℓ : 0 ≤ ℓ) (hδ₀ : 0 ≤ δ₀) (hδ : δ₀ ≤ δ)
    (hscale : (B + 1) / 2 + 4 ≤ c * ℓ * Q * B * exp (B * δ₀)) :
    saddleGaussianOuterPhi B Q c ℓ δ ≤
      ((B + 1) / 2 + 4) * δ₀ + 4 - c * ℓ * Q * exp (B * δ₀) := by
  have hδnonneg : 0 ≤ δ := hδ₀.trans hδ
  have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 + δ by linarith)
  have hstep : exp (B * δ₀) * (1 + B * (δ - δ₀)) ≤ exp (B * δ) := by
    rw [show B * δ = B * δ₀ + B * (δ - δ₀) by ring, Real.exp_add]
    exact mul_le_mul_of_nonneg_left
      (by simpa [add_comm] using Real.add_one_le_exp (B * (δ - δ₀))) (Real.exp_pos _).le
  have hdiff : exp (B * δ₀) * (B * (δ - δ₀)) ≤ exp (B * δ) - exp (B * δ₀) := by nlinarith
  unfold saddleGaussianOuterPhi
  nlinarith [mul_le_mul_of_nonneg_left hdiff (mul_nonneg (mul_nonneg hc.le hℓ) hQ.le),
    mul_le_mul_of_nonneg_right hscale (show (0 : ℝ) ≤ δ - δ₀ by linarith)]

theorem eventually_saddleGaussianOuterPhi_uniform {B Q c δ₀ : ℝ} (hB : 0 < B) (hQ : 0 < Q)
    (hc : 0 < c) (hδ₀ : 0 ≤ δ₀) :
    ∀ κ : ℝ, 0 < κ → ∀ᶠ ℓ : ℝ in atTop,
      ∀ δ : ℝ, δ₀ ≤ δ → √ℓ * exp (saddleGaussianOuterPhi B Q c ℓ δ) < κ := by
  intro κ hκ
  have hs : (0 : ℝ) < c * Q * exp (B * δ₀) := by positivity
  have htendsto : Tendsto (fun ℓ : ℝ ↦
      √ℓ * exp (((B + 1) / 2 + 4) * δ₀ + 4 - c * Q * exp (B * δ₀) * ℓ)) atTop (𝓝 (0 : ℝ)) := by
    have hscaled := (tendsto_const_nhds (x := exp (((B + 1) / 2 + 4) * δ₀ + 4))).mul
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2 : ℝ) (c * Q * exp (B * δ₀)) hs)
    rw [mul_zero] at hscaled
    refine hscaled.congr fun ℓ ↦ ?_
    rw [Real.sqrt_eq_rpow, show ((B + 1) / 2 + 4) * δ₀ + 4 - c * Q * exp (B * δ₀) * ℓ =
      (((B + 1) / 2 + 4) * δ₀ + 4) + -(c * Q * exp (B * δ₀)) * ℓ by ring,
      Real.exp_add (((B + 1) / 2 + 4) * δ₀ + 4) (-(c * Q * exp (B * δ₀)) * ℓ)]
    ring
  have hthreshold : ∀ᶠ ℓ : ℝ in atTop, (B + 1) / 2 + 4 ≤ c * ℓ * Q * B * exp (B * δ₀) := by
    have hfactor : (0 : ℝ) < c * Q * B * exp (B * δ₀) := by positivity
    filter_upwards [eventually_ge_atTop (((B + 1) / 2 + 4) / (c * Q * B * exp (B * δ₀)))]
      with ℓ hℓ
    nlinarith [(div_le_iff₀ hfactor).mp hℓ]
  filter_upwards [eventually_ge_atTop (0 : ℝ), hthreshold,
    htendsto.eventually (Iio_mem_nhds hκ)] with ℓ hℓ hscale hbound δ hδ
  refine lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.sqrt_nonneg ℓ)) hbound
  linarith [saddleGaussianOuterPhi_le_endpointBarrier hQ hc hℓ hδ₀ hδ hscale]

theorem eventually_saddleGaussianOuterPhi_uniform_polynomial {B Q c δ₀ K : ℝ} (hB : 0 < B)
    (hQ : 0 < Q) (hc : 0 < c) (hδ₀ : 0 ≤ δ₀) (hK : 0 ≤ K) :
    ∀ κ : ℝ, 0 < κ → ∀ᶠ ℓ : ℝ in atTop, ∀ δ : ℝ, δ₀ ≤ δ →
      K * √ℓ * exp ((B + 1) / 2 * δ) * (2 + δ) ^ 4 * exp (-c * ℓ * Q * exp (B * δ)) < κ := by
  intro κ hκ
  rcases hK.eq_or_lt with rfl | hKpos
  · filter_upwards [] with ℓ δ _
    simpa using hκ
  · filter_upwards [eventually_saddleGaussianOuterPhi_uniform hB hQ hc hδ₀ (κ / K)
      (div_pos hκ hKpos)] with ℓ hℓ δ hδ
    have hη : (0 : ℝ) < 2 + δ := by linarith [hδ₀.trans hδ]
    have hpower : (2 + δ) ^ 4 = exp (4 * log (2 + δ)) := by
      rw [← Real.exp_log hη, ← Real.exp_nat_mul, Real.exp_log hη]
      norm_num
    have hproduct : exp ((B + 1) / 2 * δ) * exp (4 * log (2 + δ)) *
        exp (-c * ℓ * Q * exp (B * δ)) = exp (saddleGaussianOuterPhi B Q c ℓ δ) := by
      rw [← Real.exp_add, ← Real.exp_add]
      unfold saddleGaussianOuterPhi
      ring_nf
    calc K * √ℓ * exp ((B + 1) / 2 * δ) * (2 + δ) ^ 4 * exp (-c * ℓ * Q * exp (B * δ))
        = K * (√ℓ * exp (saddleGaussianOuterPhi B Q c ℓ δ)) := by
          rw [hpower, ← hproduct]; ring
      _ < K * (κ / K) := mul_lt_mul_of_pos_left (hℓ δ hδ) hKpos
      _ = κ := by field_simp

theorem positiveShellDensity_nonneg (ε a : ℝ) : 0 ≤ w_B ε a :=
  div_nonneg (shellWeight_pos ε).le (Real.cosh_pos a).le

/-- The positive-shell moments `∫ w_B a aⁿ cosh (u a)` grow with the contour height, so on the
first branch they are dominated by their value at `u = 1 + ε/2`. -/
theorem positiveShellMoment_firstBranch_le {ε u : ℝ} (hε : 0 < ε) (n : ℕ) (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2) :
    (∫ a in Bε ε..Bε ε + 1, w_B ε a * a ^ n * cosh (u * a)) ≤
      ∫ a in Bε ε..Bε ε + 1, w_B ε a * a ^ n * cosh ((1 + ε / 2) * a) := by
  have hB : (0 : ℝ) ≤ Bε ε := by unfold Bε; positivity
  have hcont (v : ℝ) : Continuous fun a : ℝ ↦ w_B ε a * a ^ n * cosh (v * a) := by
    have := positiveShellDensity_continuous ε
    fun_prop
  refine intervalIntegral.integral_mono_on (μ := volume) (by linarith)
    ((hcont u).intervalIntegrable _ _) ((hcont (1 + ε / 2)).intervalIntegrable _ _) fun a ha ↦ ?_
  have ha0 : 0 ≤ a := hB.trans ha.1
  refine mul_le_mul_of_nonneg_left (Real.cosh_le_cosh.mpr ?_)
    (mul_nonneg (positiveShellDensity_nonneg ε a) (pow_nonneg ha0 n))
  rw [abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_pos (by positivity : (0 : ℝ) < 1 + ε / 2)]
  exact mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith, by linarith⟩) ha0

/-- The constant `3/2 + (2 + ε/2) V_B (ε/2)` bounding `(1+u) V_u` on the first branch. -/
def saddleSourceFirstBranchVarianceCoefficient (ε : ℝ) : ℝ :=
  3 / 2 + (2 + ε / 2) * V_B ε (ε / 2)

theorem saddleSourceFirstBranchVarianceCoefficient_pos {ε : ℝ} (hε : 0 < ε) :
    0 < saddleSourceFirstBranchVarianceCoefficient ε := by
  unfold saddleSourceFirstBranchVarianceCoefficient
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ 2 + ε / 2 by positivity)
    (saddleSourcePositiveShellVariance_nonneg ε (ε / 2))]

theorem upperFirstBranch_saddleSourceGaussianVariance_upper_bound {ε ℓ u : ℝ} (hε : 0 < ε)
    (hℓ : 0 < ℓ) (hulower : -1 < u) (huupper : u ≤ 1 + ε / 2) (horder : a₀ε ε ≤ Aε ε)
    (hmargin : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a) (hscale : 1 ≤ ℓ * (1 + u)) :
    V_u ε ℓ u ≤ saddleSourceFirstBranchVarianceCoefficient ε / (1 + u) := by
  have hη : (0 : ℝ) < 1 + u := by linarith
  have hgamma : (1 + u) * V_γ ℓ (1 + u) ≤ 3 / 2 := by
    have hone : 1 / (ℓ * (1 + u)) ≤ (1 : ℝ) := by rw [div_le_one (by positivity)]; linarith
    calc (1 + u) * V_γ ℓ (1 + u) ≤ (1 + u) * (1 / (2 * (1 + u)) + 1 / (ℓ * (1 + u) ^ 2)) :=
          mul_le_mul_of_nonneg_left (upperGammaVariance_bounds hℓ hη).2 hη.le
      _ = 1 / 2 + 1 / (ℓ * (1 + u)) := by field_simp [hℓ.ne', hη.ne']
      _ ≤ 3 / 2 := by linarith
  have hshort := upperShortShellVariance_nonneg (δ := u - 1) hε horder hmargin
  have hremote : V_B ε (u - 1) ≤ V_B ε (ε / 2) := by
    unfold V_B
    rw [show 1 + (u - 1) = u by ring]
    exact positiveShellMoment_firstBranch_le hε 2 hulower huupper
  have hpositive := saddleSourcePositiveShellVariance_nonneg ε (ε / 2)
  unfold V_u upperSaddleVariance upperNetShellVariance saddleSourceFirstBranchVarianceCoefficient
  rw [show 2 + (u - 1) = 1 + u by ring, le_div_iff₀ hη]
  nlinarith [hgamma, mul_nonneg hshort hη.le, mul_le_mul_of_nonneg_right hremote hη.le,
    mul_nonneg hpositive (show (0 : ℝ) ≤ 2 + ε / 2 - (1 + u) by linarith)]

theorem saddle_exp_neg_mul_min_le_add {a x y : ℝ} (ha : 0 ≤ a) :
    exp (-a * min x y) ≤ exp (-a * x) + exp (-a * y) := by
  have hmax : exp (-a * min x y) = max (exp (-a * x)) (exp (-a * y)) := by
    rcases le_total x y with hxy | hyx
    · rw [min_eq_left hxy,
        max_eq_left (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg ha (sub_nonneg.mpr hxy)]))]
    · rw [min_eq_right hyx,
        max_eq_right (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg ha (sub_nonneg.mpr hyx)]))]
  rw [hmax]
  exact max_le_add_of_nonneg (Real.exp_pos _).le (Real.exp_pos _).le

theorem saddleSourceTailIntegrand_continuous {ε ℓ u : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : a₀ε ε ≤ Aε ε) :
    Continuous fun T : ℝ ↦
      saddleGaussianTailWeight T * exp (-saddleSourceContourDamping ε ℓ u T) := by
  have harg : Continuous fun T : ℝ ↦ z_contour ℓ u T := by unfold z_contour; fun_prop
  have hgamma : Continuous fun T : ℝ ↦ Complex.Gamma (z_contour ℓ u T / 2) := by
    refine continuous_iff_continuousAt.mpr fun T ↦ ?_
    have hre : 0 < (z_contour ℓ u T).re := by
      unfold z_contour
      simp
      nlinarith [mul_pos hℓ (show (0 : ℝ) < 1 + u by linarith)]
    exact (saddleMellinGamma_differentiableAt_of_re_pos hre).continuousAt.comp_of_eq
      harg.continuousAt rfl
  have henvelope : Continuous fun T : ℝ ↦ mellinEnvelope ε ℓ (z_contour ℓ u T) := by
    refine (hgamma.mul ((saddleRegularMellinFactor_continuous hε horder ℓ).comp harg)).congr
      fun T ↦ ?_
    change Complex.Gamma (z_contour ℓ u T / 2) * saddleRegularMellinFactor ε ℓ (z_contour ℓ u T) =
      mellinEnvelope ε ℓ (z_contour ℓ u T)
    unfold mellinEnvelope saddleRegularMellinFactor
    ring
  have hweight : Continuous saddleGaussianTailWeight := by
    unfold saddleGaussianTailWeight; fun_prop
  refine hweight.mul (Continuous.congr (Continuous.norm ?_) fun T ↦
    saddleSourceNormalizedEnvelope_norm hε hℓ hu horder T)
  unfold saddleSourceNormalizedEnvelope
  exact henvelope.div_const _

theorem saddleSourceContourDamping_firstBranch_min_lower_bound {ε ℓ u : ℝ} (hε : 0 < ε)
    (hεsmall : ε ≤ 1 / 4) (hℓ : 0 < ℓ) (hulower : -1 < u) (huupper : u ≤ 1 + ε / 2)
    (horder : a₀ε ε ≤ Aε ε) (hmargin : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a) (T : ℝ) :
    ε * ℓ / (4 * exp 1) * min (T ^ 2 / (1 + u)) |T| ≤ saddleSourceContourDamping ε ℓ u T := by
  have hη : (0 : ℝ) < 1 + u := by linarith
  rw [saddleSourceContourDamping_eq_firstBranch]
  calc ε * ℓ / (4 * exp 1) * min (T ^ 2 / (1 + u)) |T|
      = 2 * ε * (ℓ / (8 * exp 1) * min (T ^ 2 / (1 + u)) |T|) := by ring
    _ ≤ 2 * ε * D_γ ℓ (1 + u) T :=
        mul_le_mul_of_nonneg_left (upperGammaDamping_lower_bound hℓ hη T) (by positivity)
    _ ≤ saddleSourceContourDamping ε ℓ u T :=
        upperFirstBranchSaddleDamping_lower_bound hε hεsmall hℓ hulower huupper horder hmargin T

/-- Pointwise majorant for a damping bounded below by `a · min (T²/η) |T|`. -/
theorem saddleGaussianTailWeight_exp_neg_le {D : ℝ → ℝ} {a η : ℝ} (ha : 0 < a)
    (hmin : ∀ T : ℝ, a * min (T ^ 2 / η) |T| ≤ D T) (T : ℝ) :
    saddleGaussianTailWeight T * exp (-D T) ≤
      saddleGaussianTailWeight T * exp (-(a / η) * T ^ 2) +
        saddleGaussianTailWeight T * exp (-a * |T|) := by
  have hexp : exp (-D T) ≤ exp (-(a / η) * T ^ 2) + exp (-a * |T|) := by
    have h := (Real.exp_le_exp.mpr
        (by linarith [hmin T] : -D T ≤ -a * min (T ^ 2 / η) |T|)).trans
      (saddle_exp_neg_mul_min_le_add (a := a) (x := T ^ 2 / η) (y := |T|) ha.le)
    rwa [show -a * (T ^ 2 / η) = -(a / η) * T ^ 2 by ring] at h
  linarith [mul_le_mul_of_nonneg_left hexp (saddleGaussianTailWeight_nonneg T)]

/-- Integrability of the weighted tail integrand from a `min (T²/η) |T|` lower bound. -/
theorem integrable_saddleGaussianTailWeight_exp_neg {D : ℝ → ℝ} {a η : ℝ} (ha : 0 < a)
    (hη : 0 < η) (hcont : Continuous fun T : ℝ ↦ saddleGaussianTailWeight T * exp (-D T))
    (hmin : ∀ T : ℝ, a * min (T ^ 2 / η) |T| ≤ D T) :
    Integrable fun T : ℝ ↦ saddleGaussianTailWeight T * exp (-D T) := by
  refine ((saddleGaussianTailWeight_mul_gaussian_integrable (div_pos ha hη)).add
    (saddleGaussianTailWeight_mul_exp_abs_integrable ha)).mono'
    hcont.aestronglyMeasurable (.of_forall fun T ↦ ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (saddleGaussianTailWeight_nonneg T) (Real.exp_pos _).le)]
  exact saddleGaussianTailWeight_exp_neg_le ha hmin T

theorem saddleSource_firstBranch_weighted_integrable {ε ℓ u : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (hulower : -1 < u) (huupper : u ≤ 1 + ε / 2) (horder : a₀ε ε ≤ Aε ε)
    (hmargin : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a) :
    Integrable fun T : ℝ ↦
      saddleGaussianTailWeight T * exp (-saddleSourceContourDamping ε ℓ u T) :=
  integrable_saddleGaussianTailWeight_exp_neg (by positivity) (by linarith)
    (saddleSourceTailIntegrand_continuous hε hℓ hulower horder)
    (saddleSourceContourDamping_firstBranch_min_lower_bound hε hεsmall hℓ hulower huupper horder
      hmargin)

theorem saddleSource_firstBranch_weighted_tail_le {ε ℓ u R : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (hulower : -1 < u) (huupper : u ≤ 1 + ε / 2) (horder : a₀ε ε ≤ Aε ε)
    (hmargin : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a) (hR : 0 ≤ R)
    (hquadratic : 6 ≤ ε * ℓ / (4 * exp 1) / (1 + u)) (hlinear : 6 ≤ ε * ℓ / (4 * exp 1)) :
    (∫ T : ℝ in saddleGaussianTailSet R,
        saddleGaussianTailWeight T * exp (-saddleSourceContourDamping ε ℓ u T)) ≤
      2 * exp (-(ε * ℓ / (4 * exp 1) / (1 + u) / 4) * R ^ 2) *
          √(π / (ε * ℓ / (4 * exp 1) / (1 + u) / 4)) +
        2 * exp (-(ε * ℓ / (4 * exp 1) / 4) * R) * (2 / (ε * ℓ / (4 * exp 1) / 4)) := by
  have ha : (0 : ℝ) < ε * ℓ / (4 * exp 1) := by positivity
  have hη : (0 : ℝ) < 1 + u := by linarith
  have hgauss := saddleGaussianTailWeight_mul_gaussian_integrable (div_pos ha hη)
  have hlin := saddleGaussianTailWeight_mul_exp_abs_integrable ha
  calc (∫ T : ℝ in saddleGaussianTailSet R,
        saddleGaussianTailWeight T * exp (-saddleSourceContourDamping ε ℓ u T))
      ≤ ∫ T : ℝ in saddleGaussianTailSet R,
          (saddleGaussianTailWeight T * exp (-(ε * ℓ / (4 * exp 1) / (1 + u)) * T ^ 2) +
            saddleGaussianTailWeight T * exp (-(ε * ℓ / (4 * exp 1)) * |T|)) :=
        setIntegral_mono_on
          (saddleSource_firstBranch_weighted_integrable hε hεsmall hℓ hulower huupper horder
            hmargin).integrableOn (hgauss.add hlin).integrableOn
          (saddleGaussianTailSet_measurable R) fun T _ ↦
            saddleGaussianTailWeight_exp_neg_le ha
              (saddleSourceContourDamping_firstBranch_min_lower_bound hε hεsmall hℓ hulower
                huupper horder hmargin) T
    _ = (∫ T : ℝ in saddleGaussianTailSet R,
            saddleGaussianTailWeight T * exp (-(ε * ℓ / (4 * exp 1) / (1 + u)) * T ^ 2)) +
          ∫ T : ℝ in saddleGaussianTailSet R,
            saddleGaussianTailWeight T * exp (-(ε * ℓ / (4 * exp 1)) * |T|) :=
        integral_add hgauss.integrableOn hlin.integrableOn
    _ ≤ _ := by
        gcongr
        · exact saddleGaussian_cubic_tail_integral_le hquadratic hR
        · exact saddleExponential_cubic_tail_integral_le hlinear hR

theorem saddleFirstBranch_normalizedGaussian_prefactor_le {ℓ V η c C : ℝ} (hℓ : 0 < ℓ)
    (hV : 0 < V) (hη : 0 < η) (hc : 0 < c) (hupper : η * V ≤ C) :
    √(ℓ * V) * √(π / (c * ℓ / η / 4)) ≤ 2 * √(π * C / c) := by
  rw [← Real.sqrt_mul (mul_nonneg hℓ.le hV.le)]
  calc √(ℓ * V * (π / (c * ℓ / η / 4))) ≤ √(4 * (π * C / c)) := by
        refine Real.sqrt_le_sqrt ?_
        calc ℓ * V * (π / (c * ℓ / η / 4)) = 4 * π * (η * V) / c := by
              field_simp [hc.ne', hℓ.ne', hη.ne']
          _ ≤ 4 * π * C / c := by gcongr
          _ = 4 * (π * C / c) := by ring
    _ = 2 * √(π * C / c) := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num

theorem saddleFirstBranch_normalizedGaussian_exponent_le {ℓ V η c C z : ℝ} (hℓ : 0 < ℓ)
    (hV : 0 < V) (hη : 0 < η) (hc : 0 < c) (hupper : η * V ≤ C) :
    c / (4 * C) * z ^ 2 ≤ c * ℓ / η / 4 * (z / √(ℓ * V)) ^ 2 := by
  rw [div_pow, Real.sq_sqrt (mul_pos hℓ hV).le]
  calc c / (4 * C) * z ^ 2 = c * z ^ 2 / 4 * (1 / C) := by ring
    _ ≤ c * z ^ 2 / 4 * (1 / (η * V)) :=
        mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (mul_pos hη hV) hupper)
          (by positivity)
    _ = c * ℓ / η / 4 * (z ^ 2 / (ℓ * V)) := by field_simp [hℓ.ne', hV.ne', hη.ne']

theorem saddleFirstBranch_normalizedLinear_prefactor_le {ℓ V η C : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    (hη : 0 < η) (hupper : η * V ≤ C) : √(ℓ * V) / ℓ ≤ √(C / (ℓ * η)) := by
  have hidentity : √(ℓ * V) / ℓ = √(V / ℓ) := by
    rw [show V / ℓ = ℓ * V / ℓ ^ 2 by field_simp [hℓ.ne'],
      Real.sqrt_div (mul_nonneg hℓ.le hV.le), Real.sqrt_sq_eq_abs, abs_of_pos hℓ]
  rw [hidentity]
  refine Real.sqrt_le_sqrt ?_
  rw [div_le_div_iff₀ hℓ (mul_pos hℓ hη)]
  nlinarith [mul_le_mul_of_nonneg_left hupper hℓ.le]

/-- Rescaling `T = z / √(ℓ V)`: the tail contribution is bounded by a Gaussian in `z` plus a
term of size `ℓ^{-1/2}`. -/
theorem saddleSource_normalized_tail_bound {D : ℝ → ℝ} {ℓ V η c C z : ℝ} (hℓ : 0 < ℓ)
    (hV : 0 < V) (hη : 0 < η) (hc : 0 < c) (hC : 0 < C) (hupper : η * V ≤ C) (hz : 0 ≤ z)
    (htail : (∫ T : ℝ in saddleGaussianTailSet (z / √(ℓ * V)),
          saddleGaussianTailWeight T * exp (-D T)) ≤
        2 * exp (-(c * ℓ / η / 4) * (z / √(ℓ * V)) ^ 2) * √(π / (c * ℓ / η / 4)) +
          2 * exp (-(c * ℓ / 4) * (z / √(ℓ * V))) * (2 / (c * ℓ / 4))) :
    √(ℓ * V) * (∫ T : ℝ in saddleGaussianTailSet (z / √(ℓ * V)),
        saddleGaussianTailWeight T * exp (-D T)) ≤
      4 * √(π * C / c) * exp (-(c / (4 * C)) * z ^ 2) + 16 / c * √(C / (ℓ * η)) := by
  have hgaussian : √(ℓ * V) * (2 * exp (-(c * ℓ / η / 4) * (z / √(ℓ * V)) ^ 2) *
      √(π / (c * ℓ / η / 4))) ≤ 4 * √(π * C / c) * exp (-(c / (4 * C)) * z ^ 2) := by
    have hexp : exp (-(c * ℓ / η / 4) * (z / √(ℓ * V)) ^ 2) ≤ exp (-(c / (4 * C)) * z ^ 2) :=
      Real.exp_le_exp.mpr (by
        linarith [saddleFirstBranch_normalizedGaussian_exponent_le (z := z) hℓ hV hη hc hupper])
    calc √(ℓ * V) * (2 * exp (-(c * ℓ / η / 4) * (z / √(ℓ * V)) ^ 2) * √(π / (c * ℓ / η / 4)))
        = 2 * (√(ℓ * V) * √(π / (c * ℓ / η / 4))) *
            exp (-(c * ℓ / η / 4) * (z / √(ℓ * V)) ^ 2) := by ring
      _ ≤ 2 * (2 * √(π * C / c)) * exp (-(c / (4 * C)) * z ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left
            (saddleFirstBranch_normalizedGaussian_prefactor_le hℓ hV hη hc hupper) (by norm_num))
            hexp (Real.exp_pos _).le (by positivity)
      _ = 4 * √(π * C / c) * exp (-(c / (4 * C)) * z ^ 2) := by ring
  have hlinear : √(ℓ * V) * (2 * exp (-(c * ℓ / 4) * (z / √(ℓ * V))) * (2 / (c * ℓ / 4))) ≤
      16 / c * √(C / (ℓ * η)) := by
    have hexp : exp (-(c * ℓ / 4) * (z / √(ℓ * V))) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by
        nlinarith [mul_pos hc hℓ, div_nonneg hz (Real.sqrt_nonneg (ℓ * V))])
    calc √(ℓ * V) * (2 * exp (-(c * ℓ / 4) * (z / √(ℓ * V))) * (2 / (c * ℓ / 4)))
        = 16 / c * (√(ℓ * V) / ℓ) * exp (-(c * ℓ / 4) * (z / √(ℓ * V))) := by
          field_simp [hc.ne', hℓ.ne']; ring
      _ ≤ 16 / c * √(C / (ℓ * η)) * 1 := by
          gcongr
          exact saddleFirstBranch_normalizedLinear_prefactor_le hℓ hV hη hupper
      _ = 16 / c * √(C / (ℓ * η)) := by ring
  calc √(ℓ * V) * (∫ T : ℝ in saddleGaussianTailSet (z / √(ℓ * V)),
        saddleGaussianTailWeight T * exp (-D T))
      ≤ √(ℓ * V) * (2 * exp (-(c * ℓ / η / 4) * (z / √(ℓ * V)) ^ 2) * √(π / (c * ℓ / η / 4)) +
          2 * exp (-(c * ℓ / 4) * (z / √(ℓ * V))) * (2 / (c * ℓ / 4))) :=
        mul_le_mul_of_nonneg_left htail (Real.sqrt_nonneg _)
    _ ≤ 4 * √(π * C / c) * exp (-(c / (4 * C)) * z ^ 2) + 16 / c * √(C / (ℓ * η)) := by
        rw [mul_add]; exact add_le_add hgaussian hlinear

/-- The `ℓ`-majorant `4√(πC/c) e^{-(c/4C)(log ℓ/4)^{1/6}} + (16/c)√(C/(log ℓ/4))` of the tails. -/
def saddleFirstBranchTailLogMajorant (c C ℓ : ℝ) : ℝ :=
  4 * √(π * C / c) * exp (-(c / (4 * C)) * (log ℓ / 4) ^ (1 / 6 : ℝ)) +
    16 / c * √(C / (log ℓ / 4))

theorem tendsto_saddleFirstBranchTailLogMajorant {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    Tendsto (saddleFirstBranchTailLogMajorant c C) atTop (𝓝 (0 : ℝ)) := by
  have hx : Tendsto (fun ℓ : ℝ ↦ log ℓ / 4) atTop atTop :=
    Real.tendsto_log_atTop.atTop_div_const (by norm_num)
  have hexp : Tendsto (fun ℓ : ℝ ↦ exp (-(c / (4 * C)) * (log ℓ / 4) ^ (1 / 6 : ℝ)))
      atTop (𝓝 (0 : ℝ)) :=
    Real.tendsto_exp_atBot.comp
      (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp hx).const_mul_atTop_of_neg
        (neg_lt_zero.mpr (by positivity)))
  have hsqrt : Tendsto (fun ℓ : ℝ ↦ √(C / (log ℓ / 4))) atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_const_nhds.div_atTop hx).sqrt
  have h := (hexp.const_mul (4 * √(π * C / c))).add (hsqrt.const_mul (16 / c))
  rw [mul_zero, mul_zero, add_zero] at h
  exact h

theorem eventually_nhdsGT_le_quarter : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ≤ 1 / 4 := by
  filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))] with ε hε
  exact le_of_lt hε

theorem eventually_saddleSource_firstBranch_uniform_tail : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    ∀ κ : ℝ, 0 < κ → ∀ᶠ ℓ : ℝ in atTop, ∀ u : ℝ, -1 < u → u ≤ 1 + ε / 2 →
      log ℓ / 4 ≤ ℓ * (1 + u) → √(ℓ * V_u ε ℓ u) *
        (∫ T : ℝ in saddleGaussianTailSet ((ℓ * (1 + u)) ^ (1 / 12 : ℝ) / √(ℓ * V_u ε ℓ u)),
          saddleGaussianTailWeight T * exp (-saddleSourceContourDamping ε ℓ u T)) < κ := by
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsGT_le_quarter,
    eventually_upper_shortCutoff_le_shortEndpoint, eventually_upper_shortMargin_positive,
    eventually_saddleSourceGaussianVariance_firstBranch_pos]
    with ε hε hεsmall horder hmargin hVpos
  change 0 < ε at hε
  have hmargin' : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a := fun a ha ↦ by linarith [hmargin a ha]
  intro κ hκ
  have hc : (0 : ℝ) < ε / (4 * exp 1) := by positivity
  have hC := saddleSourceFirstBranchVarianceCoefficient_pos hε
  have hlogtop : Tendsto (fun ℓ : ℝ ↦ log ℓ / 4) atTop atTop :=
    Real.tendsto_log_atTop.atTop_div_const (by norm_num)
  filter_upwards [eventually_gt_atTop (0 : ℝ), hlogtop.eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (6 / (ε / (4 * exp 1))),
    eventually_ge_atTop (6 * (2 + ε / 2) / (ε / (4 * exp 1))),
    (tendsto_saddleFirstBranchTailLogMajorant hc hC).eventually (Iio_mem_nhds hκ)]
    with ℓ hℓ hlogone hlinbase hquadbase htailℓ
  intro u hulower huupper hlogscale
  have hη : (0 : ℝ) < 1 + u := by linarith
  have hV : 0 < V_u ε ℓ u := hVpos ℓ hℓ u hulower huupper
  have hupper : (1 + u) * V_u ε ℓ u ≤ saddleSourceFirstBranchVarianceCoefficient ε := by
    have h := upperFirstBranch_saddleSourceGaussianVariance_upper_bound hε hℓ hulower huupper
      horder hmargin' (hlogone.trans hlogscale)
    rw [le_div_iff₀ hη] at h
    linarith
  have hlinear : 6 ≤ ε * ℓ / (4 * exp 1) := by
    rw [show ε * ℓ / (4 * exp 1) = ℓ * (ε / (4 * exp 1)) by ring]
    exact (div_le_iff₀ hc).mp hlinbase
  have hquadratic : 6 ≤ ε * ℓ / (4 * exp 1) / (1 + u) := by
    rw [le_div_iff₀ hη, show ε * ℓ / (4 * exp 1) = ℓ * (ε / (4 * exp 1)) by ring]
    calc 6 * (1 + u) ≤ 6 * (2 + ε / 2) := by linarith
      _ ≤ ℓ * (ε / (4 * exp 1)) := (div_le_iff₀ hc).mp hquadbase
  have hz : (0 : ℝ) ≤ (ℓ * (1 + u)) ^ (1 / 12 : ℝ) := Real.rpow_nonneg (by positivity) _
  have htail := saddleSource_firstBranch_weighted_tail_le
    (R := (ℓ * (1 + u)) ^ (1 / 12 : ℝ) / √(ℓ * V_u ε ℓ u)) hε hεsmall hℓ hulower huupper horder
    hmargin' (by positivity) hquadratic hlinear
  rw [show ε * ℓ / (4 * exp 1) = ε / (4 * exp 1) * ℓ by ring] at htail
  refine (saddleSource_normalized_tail_bound (D := saddleSourceContourDamping ε ℓ u) hℓ hV hη hc
    hC hupper hz htail).trans_lt (lt_of_le_of_lt ?_ htailℓ)
  have hpower : (log ℓ / 4) ^ (1 / 6 : ℝ) ≤ ((ℓ * (1 + u)) ^ (1 / 12 : ℝ)) ^ 2 := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ ℓ * (1 + u)),
      show (1 / 12 : ℝ) * (2 : ℕ) = 1 / 6 by norm_num]
    exact Real.rpow_le_rpow (by linarith) hlogscale (by norm_num)
  unfold saddleFirstBranchTailLogMajorant
  refine add_le_add (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity))
  · nlinarith [mul_nonneg
      (show (0 : ℝ) ≤ ε / (4 * exp 1) / (4 * saddleSourceFirstBranchVarianceCoefficient ε) by
        positivity) (sub_nonneg.mpr hpower)]
  · exact div_le_div_of_nonneg_left hC.le (by linarith) hlogscale

end

noncomputable section

open Filter MeasureTheory Real Set intervalIntegral
open scoped Topology

theorem saddleSourcePositiveShellThirdMoment_nonneg {ε : ℝ} (hε : 0 < ε) (δ : ℝ) :
    0 ≤ upperPositiveShellThirdMoment ε δ := by
  have hB : (0 : ℝ) ≤ Bε ε := by unfold Bε; positivity
  unfold upperPositiveShellThirdMoment
  refine intervalIntegral.integral_nonneg (by linarith) fun a ha ↦ ?_
  exact mul_nonneg (mul_nonneg (positiveShellDensity_nonneg ε a) (pow_nonneg (hB.trans ha.1) 3))
    (Real.cosh_pos _).le

/-- The constant `5/2 + (3/2) A (2 + ε/2) + (2 + ε/2)² M₃_B(ε/2)` bounding `(1+u)² M₃` on the
first branch. -/
def saddleSourceFirstBranchThirdMomentCoefficient (ε : ℝ) : ℝ :=
  5 / 2 + 3 / 2 * Aε ε * (2 + ε / 2) + (2 + ε / 2) ^ 2 * upperPositiveShellThirdMoment ε (ε / 2)

theorem upperFirstBranch_saddleSourceThirdMoment_scaled_le {ε ℓ u : ℝ} (hε : 0 < ε)
    (hεsmall : ε ≤ 1 / 4) (hℓ : 0 < ℓ) (hulower : -1 < u) (huupper : u ≤ 1 + ε / 2)
    (horder : a₀ε ε ≤ Aε ε) (hmargin : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a)
    (hscale : 1 ≤ ℓ * (1 + u)) :
    (1 + u) ^ 2 * M₃ ε ℓ (u - 1) ≤ saddleSourceFirstBranchThirdMomentCoefficient ε := by
  have hη : (0 : ℝ) < 1 + u := by linarith
  have hA : (0 : ℝ) ≤ Aε ε := le_trans (by unfold a₀ε; positivity) horder
  have hone : 1 / (ℓ * (1 + u)) ≤ (1 : ℝ) := by rw [div_le_one (by positivity)]; linarith
  have htwo : 2 / (ℓ * (1 + u)) ≤ (2 : ℝ) := by rw [div_le_iff₀ (by positivity)]; linarith
  have hgammaV : (1 + u) * V_γ ℓ (1 + u) ≤ 3 / 2 := by
    calc (1 + u) * V_γ ℓ (1 + u) ≤ (1 + u) * (1 / (2 * (1 + u)) + 1 / (ℓ * (1 + u) ^ 2)) :=
          mul_le_mul_of_nonneg_left (upperGammaVariance_bounds hℓ hη).2 hη.le
      _ = 1 / 2 + 1 / (ℓ * (1 + u)) := by field_simp [hℓ.ne', hη.ne']
      _ ≤ 3 / 2 := by linarith
  have hgammaM : (1 + u) ^ 2 * M₃_γ ℓ (1 + u) ≤ 5 / 2 := by
    calc (1 + u) ^ 2 * M₃_γ ℓ (1 + u)
        ≤ (1 + u) ^ 2 * (1 / (2 * (1 + u) ^ 2) + 2 / (ℓ * (1 + u) ^ 3)) :=
          mul_le_mul_of_nonneg_left (upperGammaThirdMoment_bounds hℓ hη).2 (sq_nonneg _)
      _ = 1 / 2 + 2 / (ℓ * (1 + u)) := by field_simp [hℓ.ne', hη.ne']
      _ ≤ 5 / 2 := by linarith
  have hgammanonneg : 0 ≤ V_γ ℓ (1 + u) :=
    le_trans (by positivity) (upperGammaVariance_bounds hℓ hη).1
  have hshortvariance : V_s ε (u - 1) ≤ V_γ ℓ (1 + u) := by
    have h := upperFirstBranch_shortVariance_le_gamma hε hεsmall hℓ hulower huupper horder hmargin
    nlinarith [mul_nonneg hε.le hgammanonneg]
  have hshort : (1 + u) ^ 2 * upperShortShellThirdMoment ε (u - 1) ≤
      3 / 2 * Aε ε * (2 + ε / 2) := by
    calc (1 + u) ^ 2 * upperShortShellThirdMoment ε (u - 1)
        ≤ (1 + u) ^ 2 * (Aε ε * V_s ε (u - 1)) :=
          mul_le_mul_of_nonneg_left (upperShortShellThirdMoment_le (δ := u - 1) hε horder hmargin)
            (sq_nonneg _)
      _ ≤ (1 + u) ^ 2 * (Aε ε * V_γ ℓ (1 + u)) := by gcongr
      _ = Aε ε * (1 + u) * ((1 + u) * V_γ ℓ (1 + u)) := by ring
      _ ≤ Aε ε * (1 + u) * (3 / 2) := by gcongr
      _ ≤ Aε ε * (2 + ε / 2) * (3 / 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hA) (by norm_num)
      _ = 3 / 2 * Aε ε * (2 + ε / 2) := by ring
  have hremote : upperPositiveShellThirdMoment ε (u - 1) ≤
      upperPositiveShellThirdMoment ε (ε / 2) := by
    unfold upperPositiveShellThirdMoment
    rw [show 1 + (u - 1) = u by ring]
    exact positiveShellMoment_firstBranch_le hε 3 hulower huupper
  have hremote0 := saddleSourcePositiveShellThirdMoment_nonneg hε (ε / 2)
  have hremoteScaled : (1 + u) ^ 2 * upperPositiveShellThirdMoment ε (u - 1) ≤
      (2 + ε / 2) ^ 2 * upperPositiveShellThirdMoment ε (ε / 2) := by
    calc (1 + u) ^ 2 * upperPositiveShellThirdMoment ε (u - 1)
        ≤ (1 + u) ^ 2 * upperPositiveShellThirdMoment ε (ε / 2) :=
          mul_le_mul_of_nonneg_left hremote (sq_nonneg _)
      _ ≤ (2 + ε / 2) ^ 2 * upperPositiveShellThirdMoment ε (ε / 2) :=
          mul_le_mul_of_nonneg_right (by nlinarith) hremote0
  unfold saddleSourceFirstBranchThirdMomentCoefficient M₃ upperNetShellThirdMoment
  rw [show 2 + (u - 1) = 1 + u by ring]
  nlinarith

/-- The variance floor `(99/200) B² Q e^{εB/2}` on the second branch. -/
def saddleSourceSecondBranchVarianceFloor (ε : ℝ) : ℝ :=
  99 / 200 * Bε ε ^ 2 * Qε ε * exp (ε / 2 * Bε ε)

theorem saddleSourceSecondBranchVarianceFloor_pos {ε : ℝ} (hε : 0 < ε) :
    0 < saddleSourceSecondBranchVarianceFloor ε := by
  unfold saddleSourceSecondBranchVarianceFloor Bε
  have := shellWeight_pos ε
  positivity

theorem eventually_saddleSourceGaussianVariance_secondBranch_floor :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ ℓ : ℝ, 0 < ℓ → ∀ δ : ℝ, ε / 2 ≤ δ →
      saddleSourceSecondBranchVarianceFloor ε ≤ V_u ε ℓ (1 + δ) := by
  filter_upwards [self_mem_nhdsWithin, eventually_upperSaddleVariance_bounds] with ε hε hvariance
  change 0 < ε at hε
  intro ℓ hℓ δ hδ
  have hδ0 : 0 ≤ δ := by linarith
  have hB : (0 : ℝ) ≤ Bε ε := by unfold Bε; positivity
  have hfloor : saddleSourceSecondBranchVarianceFloor ε ≤ 99 / 100 * V_B ε δ := by
    calc saddleSourceSecondBranchVarianceFloor ε
        = 99 / 100 * (1 / 2 * Bε ε ^ 2 * Qε ε * exp (ε / 2 * Bε ε)) := by
          unfold saddleSourceSecondBranchVarianceFloor; ring
      _ ≤ 99 / 100 * (1 / 2 * Bε ε ^ 2 * Qε ε * exp (δ * Bε ε)) := by
          have hweight := shellWeight_pos ε
          gcongr
      _ ≤ 99 / 100 * V_B ε δ := by gcongr; exact (upperPositiveShellVariance_bounds hε hδ0).1
  unfold V_u
  rw [show 1 + δ - 1 = δ by ring]
  have hgamma : (0 : ℝ) ≤ 1 / (2 * (2 + δ)) := by positivity
  linarith [(hvariance ℓ hℓ δ hδ).1]

/-- Cubic window bound under a variance floor `V₀ ≤ V`. -/
theorem saddleSource_cubic_window_le_of_variance_floor {ℓ V M C V₀ z T : ℝ} (hℓ : 0 < ℓ)
    (hV₀ : 0 < V₀) (hfloor : V₀ ≤ V) (hC : 0 ≤ C) (hz : 0 ≤ z) (hM : M ≤ C * V)
    (hT : |T| ≤ z / √(ℓ * V)) :
    ℓ * M / 6 * |T| ^ 3 ≤ C / 6 * z ^ 3 / (√ℓ * √V₀) := by
  have hV : 0 < V := hV₀.trans_le hfloor
  have hs : 0 < √(ℓ * V) := Real.sqrt_pos.2 (mul_pos hℓ hV)
  calc ℓ * M / 6 * |T| ^ 3 ≤ ℓ * (C * V) / 6 * |T| ^ 3 := by gcongr
    _ ≤ ℓ * (C * V) / 6 * (z / √(ℓ * V)) ^ 3 := by gcongr
    _ = C / 6 * z ^ 3 / √(ℓ * V) := by
        field_simp [hs.ne']
        rw [Real.sq_sqrt (mul_nonneg hℓ.le hV.le)]
        ring
    _ ≤ C / 6 * z ^ 3 / √(ℓ * V₀) := by gcongr
    _ = C / 6 * z ^ 3 / (√ℓ * √V₀) := by rw [Real.sqrt_mul hℓ.le]

end

noncomputable section

open Filter Set
open scoped Topology

/-- The uniform estimates of Lemmas 4.2, 4.4 and 4.5 for a polynomial factor `P` on the
horizontal lines `Im ζ = u`, `u ≥ u₀`: `P(iu) ≠ 0` and
`‖P(T + iu) - P(iu)‖ ≤ C (|T| + |T|³) ‖P(iu)‖`.  Satisfied by `P₊` on `u ≥ -1` and by `P₋`, `P₀`
on `u ≥ 1 + ε/4`. -/
structure SaddleRangeBounds (P : ℂ → ℂ) (u₀ : ℝ) : Prop where
  norm_pos : ∀ u : ℝ, u₀ ≤ u → 0 < ‖P (I * u)‖
  difference : ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, u₀ ≤ u → ∀ T : ℝ,
    ‖P ((T : ℂ) + I * u) - P (I * u)‖ ≤ C * (|T| + |T| ^ 3) * ‖P (I * u)‖

/-- Lemma 4.4: the uniform cubic bound `‖P(T + iu)‖ ≤ C (1 + |T|³) ‖P(iu)‖`. -/
theorem SaddleRangeBounds.weighted {P : ℂ → ℂ} {u₀ : ℝ} (h : SaddleRangeBounds P u₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, u₀ ≤ u → ∀ T : ℝ,
      ‖P ((T : ℂ) + I * u)‖ ≤ C * (1 + |T| ^ 3) * ‖P (I * u)‖ := by
  obtain ⟨C, hC, hbound⟩ := h.difference
  refine ⟨1 + 2 * C, by positivity, fun u hu T ↦ ?_⟩
  have hT : |T| ≤ 1 + |T| ^ 3 := by
    nlinarith [abs_nonneg T, sq_nonneg (|T| - 1), mul_nonneg (abs_nonneg T) (sq_nonneg (|T| - 1))]
  have hdiff := hbound u hu T
  have htri : ‖P ((T : ℂ) + I * u)‖ ≤ ‖P (I * u)‖ + ‖P ((T : ℂ) + I * u) - P (I * u)‖ := by
    simpa using norm_add_le (P (I * u)) (P ((T : ℂ) + I * u) - P (I * u))
  have hCN : 0 ≤ C * ‖P (I * u)‖ := mul_nonneg hC.le (norm_nonneg _)
  have hcube : 0 ≤ |T| ^ 3 * ‖P (I * u)‖ := mul_nonneg (pow_nonneg (abs_nonneg T) 3) (norm_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left hT hCN]

/-- Generic central window: a uniform difference bound `C (|T| + |T|³) ‖P (iu)‖` shrinks below
`κ ‖P (iu)‖` on a window `|T| ≤ R` independent of `u`. -/
theorem exists_uniform_central_window {P : ℂ → ℂ} {p : ℝ → Prop} {κ : ℝ} (hκ : 0 < κ)
    (h : ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, p u → ∀ T : ℝ,
      ‖P ((T : ℂ) + I * u) - P (I * u)‖ ≤ C * (|T| + |T| ^ 3) * ‖P (I * u)‖) :
    ∃ R : ℝ, 0 < R ∧ ∀ u : ℝ, p u → ∀ T : ℝ, |T| ≤ R →
      ‖P ((T : ℂ) + I * u) - P (I * u)‖ ≤ κ * ‖P (I * u)‖ := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨min 1 (κ / (2 * C)), by positivity, fun u hu T hT ↦ ?_⟩
  have hTunit : |T| ≤ 1 := hT.trans (min_le_left _ _)
  have hcube : |T| ^ 3 ≤ |T| := by
    nlinarith [mul_nonneg (mul_nonneg (abs_nonneg T) (sub_nonneg.mpr hTunit))
      (by positivity : (0 : ℝ) ≤ 1 + |T|)]
  have hscale : C * (|T| + |T| ^ 3) ≤ κ := by
    have hT' := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * C)).mp
      (hT.trans (min_le_right 1 (κ / (2 * C))))
    nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hcube)]
  exact (hbound u hu T).trans (mul_le_mul_of_nonneg_right hscale (norm_nonneg _))

/-- Lemma 4.5: the central window of a saddle range. -/
theorem SaddleRangeBounds.exists_central_window {P : ℂ → ℂ} {u₀ : ℝ} (h : SaddleRangeBounds P u₀)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ R : ℝ, 0 < R ∧ ∀ u : ℝ, u₀ ≤ u → ∀ T : ℝ, |T| ≤ R →
      ‖P ((T : ℂ) + I * u) - P (I * u)‖ ≤ κ * ‖P (I * u)‖ :=
  exists_uniform_central_window (p := fun u ↦ u₀ ≤ u) hκ h.difference

/-- Lemmas 4.2, 4.4, 4.5 for `P₊` on `u ≥ -1`. -/
theorem saddleRangeBounds_PPlus {ε : ℝ} (hε : 0 < ε) : SaddleRangeBounds (PPlus ε) (-1) where
  norm_pos u hu := (beta_pos hε).trans_le (plusPolynomial_imaginary_norm_ge_beta hε hu)
  difference := by
    obtain ⟨C, hC, hbound⟩ := exists_plusPolynomial_uniform_difference_ratio hε
    exact ⟨C, hC, fun u hu T ↦ (div_le_iff₀ ((beta_pos hε).trans_le
      (plusPolynomial_imaginary_norm_ge_beta hε hu))).mp (hbound u hu T)⟩

/-- Lemmas 4.2, 4.4, 4.5 for `P₋` on `u ≥ 1 + ε/4`. -/
theorem saddleRangeBounds_PMinus {ε : ℝ} (hε : 0 < ε) :
    SaddleRangeBounds (PMinus ε) (1 + ε / 4) where
  norm_pos u hu := by nlinarith [beta_pos hε, minusPolynomial_imaginary_norm_ge_three_beta hε hu]
  difference := by
    obtain ⟨C, hC, hbound⟩ := exists_minusPolynomial_uniform_difference_ratio hε
    refine ⟨C, hC, fun u hu T ↦ (div_le_iff₀ ?_).mp (hbound u hu T)⟩
    nlinarith [beta_pos hε, minusPolynomial_imaginary_norm_ge_three_beta hε hu]

end

noncomputable section

open Filter MeasureTheory Real Set intervalIntegral
open scoped Topology

/-- Radius `(ℓ(1+u))^{1/12}/√(ℓ V_u)` of the central window on the first branch. -/
def saddleSourceFirstBranchCentralRadius (ε ℓ u : ℝ) : ℝ :=
  (ℓ * (1 + u)) ^ (1 / 12 : ℝ) / √(ℓ * V_u ε ℓ u)

/-- Radius `ℓ^{1/12}/√(ℓ V_u)` of the central window on the second branch. -/
def saddleSourceSecondBranchCentralRadius (ε ℓ u : ℝ) : ℝ :=
  ℓ ^ (1 / 12 : ℝ) / √(ℓ * V_u ε ℓ u)

theorem saddleSource_central_rpow_cube_div_sqrt {x : ℝ} (hx : 0 < x) :
    (x ^ (1 / 12 : ℝ)) ^ 3 / √x = x ^ (-(1 / 4 : ℝ)) := by
  rw [show (x ^ (1 / 12 : ℝ)) ^ 3 = x ^ (1 / 4 : ℝ) by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num,
    Real.sqrt_eq_rpow, ← Real.rpow_sub hx]
  norm_num

theorem saddleSource_central_rpow_div_sqrt {x : ℝ} (hx : 0 < x) :
    x ^ (1 / 12 : ℝ) / √x = x ^ (-(5 / 12 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hx]
  norm_num

theorem tendsto_const_mul_rpow_neg_atTop (A : ℝ) {α : ℝ} (hα : 0 < α) :
    Tendsto (fun x : ℝ ↦ A * x ^ (-α)) atTop (𝓝 (0 : ℝ)) := by
  simpa using (tendsto_rpow_neg_atTop hα).const_mul A

theorem sqrt_mul_mul_sqrt_mul {ℓ η V : ℝ} (hℓ : 0 ≤ ℓ) (hη : 0 ≤ η) (hV : 0 ≤ V) :
    √(ℓ * η) * √(η * V) = √(ℓ * V) * η := by
  rw [← Real.sqrt_mul (by positivity), show ℓ * η * (η * V) = ℓ * V * η ^ 2 by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq hη]

/-- Cubic window bound in terms of the scaled moment `η² M ≤ K` and variance floor `c ≤ η V`. -/
theorem saddleSource_scaled_cubic_window_le {ℓ η V M K c z T : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (hc : 0 < c) (hK : 0 ≤ K) (hz : 0 ≤ z) (hmoment : η ^ 2 * M ≤ K) (hvariance : c ≤ η * V)
    (hT : |T| ≤ z / √(ℓ * V)) :
    ℓ * M / 6 * |T| ^ 3 ≤ K / (6 * c * √c) * (z ^ 3 / √(ℓ * η)) := by
  have hV : 0 < V := by nlinarith [mul_pos hη hc]
  have hs : 0 < √(ℓ * V) := Real.sqrt_pos.2 (mul_pos hℓ hV)
  have ht : 0 < √(ℓ * η) := Real.sqrt_pos.2 (mul_pos hℓ hη)
  have hw : 0 < √(η * V) := Real.sqrt_pos.2 (mul_pos hη hV)
  have hcroot : 0 < √c := Real.sqrt_pos.2 hc
  have hwlower : √c ≤ √(η * V) := Real.sqrt_le_sqrt hvariance
  have hm : M ≤ K / η ^ 2 := (le_div_iff₀ (by positivity)).2 (by nlinarith)
  have hratio : ℓ * √(ℓ * η) * √(η * V) ^ 3 = η ^ 2 * √(ℓ * V) ^ 3 := by
    calc ℓ * √(ℓ * η) * √(η * V) ^ 3 = √(ℓ * η) ^ 2 / η * √(ℓ * η) * √(η * V) ^ 3 := by
          rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ℓ * η)]; field_simp [hη.ne']
      _ = (√(ℓ * η) * √(η * V)) ^ 3 / η := by ring
      _ = (√(ℓ * V) * η) ^ 3 / η := by rw [sqrt_mul_mul_sqrt_mul hℓ.le hη.le hV.le]
      _ = η ^ 2 * √(ℓ * V) ^ 3 := by field_simp [hη.ne']
  calc ℓ * M / 6 * |T| ^ 3 ≤ ℓ * (K / η ^ 2) / 6 * (z / √(ℓ * V)) ^ 3 := by gcongr
    _ = K / 6 * z ^ 3 / (√(ℓ * η) * √(η * V) ^ 3) := by
        field_simp [hη.ne', hs.ne', ht.ne', hw.ne']
        calc ℓ * K * z ^ 3 * √(ℓ * η) * √(η * V) ^ 3
            = K * z ^ 3 * (ℓ * √(ℓ * η) * √(η * V) ^ 3) := by ring
          _ = K * z ^ 3 * (η ^ 2 * √(ℓ * V) ^ 3) := by rw [hratio]
          _ = K * η ^ 2 * z ^ 3 * √(ℓ * V) ^ 3 := by ring
    _ ≤ K / 6 * z ^ 3 / (√(ℓ * η) * √c ^ 3) := by gcongr
    _ = K / (6 * c * √c) * (z ^ 3 / √(ℓ * η)) := by
        field_simp [ht.ne', hc.ne', hcroot.ne']
        rw [Real.sq_sqrt hc.le]

theorem upperFirstBranch_saddleSourceGaussianVariance_scaled_lower_bound {ε ℓ u : ℝ} (hε : 0 < ε)
    (hεsmall : ε ≤ 1 / 4) (hℓ : 0 < ℓ) (hulower : -1 < u) (huupper : u ≤ 1 + ε / 2)
    (horder : a₀ε ε ≤ Aε ε) (hmargin : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a) :
    ε ≤ (1 + u) * V_u ε ℓ u := by
  have hη : (0 : ℝ) < 1 + u := by linarith
  have hgamma := (upperGammaVariance_bounds hℓ hη).1
  have hsource := upperFirstBranch_saddleSourceGaussianVariance_lower_bound hε hεsmall hℓ hulower
    huupper horder hmargin
  calc ε = (1 + u) * (2 * ε * (1 / (2 * (1 + u)))) := by field_simp [hη.ne']
    _ ≤ (1 + u) * (2 * ε * V_γ ℓ (1 + u)) := by gcongr
    _ ≤ (1 + u) * V_u ε ℓ u := by gcongr

/-- Radius bound in terms of the scaled variance floor `c ≤ η V` and `η ≤ U`. -/
theorem saddleSource_scaled_central_radius_le {ℓ η V c U z : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (hc : 0 < c) (hηU : η ≤ U) (hz : 0 ≤ z) (hvariance : c ≤ η * V) :
    z / √(ℓ * V) ≤ U / √c * (z / √(ℓ * η)) := by
  have hV : 0 < V := by nlinarith [mul_pos hη hc]
  have hs : 0 < √(ℓ * V) := Real.sqrt_pos.2 (mul_pos hℓ hV)
  have ht : 0 < √(ℓ * η) := Real.sqrt_pos.2 (mul_pos hℓ hη)
  have hw : 0 < √(η * V) := Real.sqrt_pos.2 (mul_pos hη hV)
  have hcroot : 0 < √c := Real.sqrt_pos.2 hc
  have hwlower : √c ≤ √(η * V) := Real.sqrt_le_sqrt hvariance
  have hU : 0 ≤ U := hη.le.trans hηU
  calc z / √(ℓ * V) = η * z / (√(ℓ * η) * √(η * V)) := by
        rw [sqrt_mul_mul_sqrt_mul hℓ.le hη.le hV.le]
        field_simp [hs.ne', hη.ne']
    _ ≤ U * z / (√(ℓ * η) * √c) := by gcongr
    _ = U / √c * (z / √(ℓ * η)) := by ring

theorem eventually_saddleSourceFirstBranch_cubic_window : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    ∀ κ : ℝ, 0 < κ → ∀ᶠ ℓ : ℝ in atTop, ∀ u : ℝ, -1 < u → u ≤ 1 + ε / 2 →
      log ℓ / 4 ≤ ℓ * (1 + u) → ∀ T : ℝ, |T| ≤ saddleSourceFirstBranchCentralRadius ε ℓ u →
        ℓ * M₃ ε ℓ (u - 1) / 6 * |T| ^ 3 < κ := by
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsGT_le_quarter,
    eventually_upper_shortCutoff_le_shortEndpoint, eventually_upper_shortMargin_positive]
    with ε hε hεsmall horder hmargin
  change 0 < ε at hε
  have hmargin' : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a := fun a ha ↦ by linarith [hmargin a ha]
  have hA : (0 : ℝ) ≤ Aε ε := le_trans (by unfold a₀ε; positivity) horder
  have hK : 0 < saddleSourceFirstBranchThirdMomentCoefficient ε := by
    have := saddleSourcePositiveShellThirdMoment_nonneg hε (ε / 2)
    unfold saddleSourceFirstBranchThirdMomentCoefficient
    positivity
  intro κ hκ
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_const_mul_rpow_neg_atTop
    (saddleSourceFirstBranchThirdMomentCoefficient ε / (6 * ε * √ε))
    (by norm_num : (0 : ℝ) < 1 / 4)).eventually (Iio_mem_nhds hκ))
  filter_upwards [eventually_gt_atTop (0 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop (4 * N),
    Real.tendsto_log_atTop.eventually_ge_atTop (4 : ℝ)]
    with ℓ hℓ hlog hlogone u hulower huupper hstar T hT
  have hη : (0 : ℝ) < 1 + u := by linarith
  have hx : (0 : ℝ) < ℓ * (1 + u) := mul_pos hℓ hη
  refine lt_of_le_of_lt ?_ (hN (ℓ * (1 + u)) (by nlinarith))
  calc ℓ * M₃ ε ℓ (u - 1) / 6 * |T| ^ 3
      ≤ saddleSourceFirstBranchThirdMomentCoefficient ε / (6 * ε * √ε) *
          (((ℓ * (1 + u)) ^ (1 / 12 : ℝ)) ^ 3 / √(ℓ * (1 + u))) :=
        saddleSource_scaled_cubic_window_le (V := V_u ε ℓ u) (M := M₃ ε ℓ (u - 1))
          (K := saddleSourceFirstBranchThirdMomentCoefficient ε) (c := ε)
          (z := (ℓ * (1 + u)) ^ (1 / 12 : ℝ)) hℓ hη (by positivity) hK.le
          (Real.rpow_nonneg hx.le _)
          (upperFirstBranch_saddleSourceThirdMoment_scaled_le hε hεsmall hℓ hulower huupper horder
            hmargin' (by nlinarith))
          (upperFirstBranch_saddleSourceGaussianVariance_scaled_lower_bound hε hεsmall hℓ hulower
            huupper horder hmargin') hT
    _ = saddleSourceFirstBranchThirdMomentCoefficient ε / (6 * ε * √ε) *
          (ℓ * (1 + u)) ^ (-(1 / 4 : ℝ)) := by
        rw [saddleSource_central_rpow_cube_div_sqrt hx]

theorem eventually_saddleSourceSecondBranch_cubic_window : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    ∀ κ : ℝ, 0 < κ → ∀ᶠ ℓ : ℝ in atTop, ∀ δ : ℝ, ε / 2 ≤ δ → ∀ T : ℝ,
      |T| ≤ saddleSourceSecondBranchCentralRadius ε ℓ (1 + δ) →
        ℓ * M₃ ε ℓ δ / 6 * |T| ^ 3 < κ := by
  filter_upwards [self_mem_nhdsWithin, eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_saddleSourceGaussianVariance_secondBranch_floor,
    eventually_upperSaddleThirdMoment_le_variance] with ε hε horder hfloor hmoment
  change 0 < ε at hε
  have hfloorpos := saddleSourceSecondBranchVarianceFloor_pos hε
  have hA : (0 : ℝ) ≤ Aε ε := le_trans (by unfold a₀ε; positivity) horder
  have hB : (0 : ℝ) ≤ Bε ε := by unfold Bε; positivity
  have hC : (0 : ℝ) ≤ 2 + 100 / 99 * upperSaddleShellThirdCoefficient ε := by
    unfold upperSaddleShellThirdCoefficient; positivity
  intro κ hκ
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_const_mul_rpow_neg_atTop
    ((2 + 100 / 99 * upperSaddleShellThirdCoefficient ε) /
      (6 * √(saddleSourceSecondBranchVarianceFloor ε)))
    (by norm_num : (0 : ℝ) < 1 / 4)).eventually (Iio_mem_nhds hκ))
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop N] with ℓ hℓ hℓN δ hδ T hT
  have hℓpos : (0 : ℝ) < ℓ := by linarith
  have hthird : M₃ ε ℓ δ ≤
      (2 + 100 / 99 * upperSaddleShellThirdCoefficient ε) * V_u ε ℓ (1 + δ) := by
    simpa [V_u] using hmoment ℓ hℓ δ hδ
  refine lt_of_le_of_lt ?_ (hN ℓ hℓN)
  calc ℓ * M₃ ε ℓ δ / 6 * |T| ^ 3
      ≤ (2 + 100 / 99 * upperSaddleShellThirdCoefficient ε) / 6 * (ℓ ^ (1 / 12 : ℝ)) ^ 3 /
          (√ℓ * √(saddleSourceSecondBranchVarianceFloor ε)) :=
        saddleSource_cubic_window_le_of_variance_floor (V := V_u ε ℓ (1 + δ)) (M := M₃ ε ℓ δ)
          (C := 2 + 100 / 99 * upperSaddleShellThirdCoefficient ε)
          (V₀ := saddleSourceSecondBranchVarianceFloor ε) (z := ℓ ^ (1 / 12 : ℝ)) hℓpos hfloorpos
          (hfloor ℓ hℓpos δ hδ) hC (Real.rpow_nonneg hℓpos.le _) hthird hT
    _ = (2 + 100 / 99 * upperSaddleShellThirdCoefficient ε) /
          (6 * √(saddleSourceSecondBranchVarianceFloor ε)) *
          ((ℓ ^ (1 / 12 : ℝ)) ^ 3 / √ℓ) := by ring
    _ = (2 + 100 / 99 * upperSaddleShellThirdCoefficient ε) /
          (6 * √(saddleSourceSecondBranchVarianceFloor ε)) * ℓ ^ (-(1 / 4 : ℝ)) := by
        rw [saddleSource_central_rpow_cube_div_sqrt hℓpos]

theorem eventually_saddleSourceFirstBranch_central_radius_lt : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    ∀ κ : ℝ, 0 < κ → ∀ᶠ ℓ : ℝ in atTop, ∀ u : ℝ, -1 < u → u ≤ 1 + ε / 2 →
      log ℓ / 4 ≤ ℓ * (1 + u) → saddleSourceFirstBranchCentralRadius ε ℓ u < κ := by
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsGT_le_quarter,
    eventually_upper_shortCutoff_le_shortEndpoint, eventually_upper_shortMargin_positive]
    with ε hε hεsmall horder hmargin
  change 0 < ε at hε
  have hmargin' : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a := fun a ha ↦ by linarith [hmargin a ha]
  intro κ hκ
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_const_mul_rpow_neg_atTop
    ((2 + ε / 2) / √ε) (by norm_num : (0 : ℝ) < 5 / 12)).eventually (Iio_mem_nhds hκ))
  filter_upwards [eventually_gt_atTop (0 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop (4 * N)]
    with ℓ hℓ hlog u hulower huupper hstar
  have hη : (0 : ℝ) < 1 + u := by linarith
  have hx : (0 : ℝ) < ℓ * (1 + u) := mul_pos hℓ hη
  refine lt_of_le_of_lt ?_ (hN (ℓ * (1 + u)) (by nlinarith))
  calc saddleSourceFirstBranchCentralRadius ε ℓ u
      ≤ (2 + ε / 2) / √ε * ((ℓ * (1 + u)) ^ (1 / 12 : ℝ) / √(ℓ * (1 + u))) :=
        saddleSource_scaled_central_radius_le (V := V_u ε ℓ u) (c := ε) (U := 2 + ε / 2)
          (z := (ℓ * (1 + u)) ^ (1 / 12 : ℝ)) hℓ hη (by positivity) (by linarith)
          (Real.rpow_nonneg hx.le _)
          (upperFirstBranch_saddleSourceGaussianVariance_scaled_lower_bound hε hεsmall hℓ hulower
            huupper horder hmargin')
    _ = (2 + ε / 2) / √ε * (ℓ * (1 + u)) ^ (-(5 / 12 : ℝ)) := by
        rw [saddleSource_central_rpow_div_sqrt hx]

theorem eventually_saddleSourceSecondBranch_central_radius_lt : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    ∀ κ : ℝ, 0 < κ → ∀ᶠ ℓ : ℝ in atTop, ∀ δ : ℝ, ε / 2 ≤ δ →
      saddleSourceSecondBranchCentralRadius ε ℓ (1 + δ) < κ := by
  filter_upwards [self_mem_nhdsWithin, eventually_saddleSourceGaussianVariance_secondBranch_floor]
    with ε hε hfloor
  change 0 < ε at hε
  have hfloorpos := saddleSourceSecondBranchVarianceFloor_pos hε
  intro κ hκ
  filter_upwards [eventually_gt_atTop (0 : ℝ), (tendsto_const_mul_rpow_neg_atTop
    (1 / √(saddleSourceSecondBranchVarianceFloor ε))
    (by norm_num : (0 : ℝ) < 5 / 12)).eventually (Iio_mem_nhds hκ)] with ℓ hℓ hsmall δ hδ
  have hfl := hfloor ℓ hℓ δ hδ
  have hV : 0 < V_u ε ℓ (1 + δ) := hfloorpos.trans_le hfl
  have hz : (0 : ℝ) ≤ ℓ ^ (1 / 12 : ℝ) := Real.rpow_nonneg hℓ.le _
  refine lt_of_le_of_lt ?_ hsmall
  calc saddleSourceSecondBranchCentralRadius ε ℓ (1 + δ)
      = ℓ ^ (1 / 12 : ℝ) / √(ℓ * V_u ε ℓ (1 + δ)) := rfl
    _ ≤ ℓ ^ (1 / 12 : ℝ) / √(ℓ * saddleSourceSecondBranchVarianceFloor ε) := by gcongr
    _ = 1 / √(saddleSourceSecondBranchVarianceFloor ε) * (ℓ ^ (1 / 12 : ℝ) / √ℓ) := by
        rw [Real.sqrt_mul hℓ.le]; ring
    _ = 1 / √(saddleSourceSecondBranchVarianceFloor ε) * ℓ ^ (-(5 / 12 : ℝ)) := by
        rw [saddleSource_central_rpow_div_sqrt hℓ]

theorem exists_saddleSource_central_error_tolerance {κ : ℝ} (hκ : 0 < κ) :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧ 2 * q + (1 + 2 * q) * q < κ := by
  have hq : (0 : ℝ) < min (1 / 4) (κ / 8) := by positivity
  have h4 : min (1 / 4 : ℝ) (κ / 8) ≤ 1 / 4 := min_le_left _ _
  have hk : min (1 / 4 : ℝ) (κ / 8) ≤ κ / 8 := min_le_right _ _
  exact ⟨min (1 / 4) (κ / 8), hq, by linarith,
    by nlinarith [mul_nonneg hq.le (sub_nonneg.mpr h4)]⟩

/-- Upgrading a central Gaussian error bound with tolerance `2q + (1+2q)q` to a strict `κ`. -/
theorem centralGaussianError_lt {A B G κ q : ℝ} (hB : 0 < B) (hG : 0 < G)
    (hfactor : 2 * q + (1 + 2 * q) * q < κ) (h : A ≤ (2 * q + (1 + 2 * q) * q) * B * G) :
    A < κ * B * G := h.trans_lt (by gcongr)

/-- Report (71), first branch: for a saddle polynomial `P` with range bounds on `u ≥ u₀`, the
central Gaussian error of the centred integral is `< κ ‖P(iu)‖ ∫ e^{-λV T²/2}` for large `λ`. -/
theorem eventually_firstBranch_centralGaussianError : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    ∀ κ : ℝ, 0 < κ → ∀ (P : ℂ → ℂ) (u₀ : ℝ), IsSaddlePolynomial ε P → SaddleRangeBounds P u₀ →
      ∀ᶠ ℓ : ℝ in atTop, ∀ u : ℝ, -1 < u → u ≤ 1 + ε / 2 → log ℓ / 4 ≤ ℓ * (1 + u) → u₀ ≤ u →
        ‖∫ T : ℝ in Icc (-(saddleSourceFirstBranchCentralRadius ε ℓ u))
            (saddleSourceFirstBranchCentralRadius ε ℓ u),
            (centeredIntegrand ε ℓ P u (vℓ ε ℓ u) T - gaussianIntegrand ε ℓ P u T)‖ <
          κ * ‖P (I * u)‖ * ∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T := by
  filter_upwards [self_mem_nhdsWithin, eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_upper_shortMargin_positive, eventually_saddleSourceGaussianVariance_firstBranch_pos,
    eventually_saddleSourceFirstBranch_cubic_window,
    eventually_saddleSourceFirstBranch_central_radius_lt]
    with ε hε horder hmargin hvariance hcubic hradius
  change 0 < ε at hε
  have hmargin' : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a := fun a ha ↦ by linarith [hmargin a ha]
  intro κ hκ P u₀ hP hrange
  obtain ⟨q, hq, hqone, hfactor⟩ := exists_saddleSource_central_error_tolerance hκ
  obtain ⟨R, hR, hwindow⟩ := hrange.exists_central_window hq
  filter_upwards [eventually_gt_atTop (0 : ℝ), hcubic q hq, hradius R hR]
    with ℓ hℓ hqc hsmall u hu huupper hstar hu₀
  have hV := hvariance ℓ hℓ u hu huupper
  have hphase : ∀ T : ℝ, |T| ≤ saddleSourceFirstBranchCentralRadius ε ℓ u →
      ℓ * M₃ ε ℓ (u - 1) / 6 * |T| ^ 3 ≤ q := fun T hT ↦ (hqc u hu huupper hstar T hT).le
  exact centralGaussianError_lt (hrange.norm_pos u hu₀)
    (saddleSourceGaussianKernel_integral_pos hℓ hV) hfactor
    (centeredIntegrand_centralGaussianError_le hε hℓ hu horder hmargin' hV hq.le hqone hq.le hP
      hphase fun T hT ↦ hwindow u hu₀ T (hT.trans (hsmall u hu huupper hstar).le))

/-- Report (71), second branch `u = 1 + δ`, `δ ≥ ε/2`: the central Gaussian error of the centred
integral of a saddle polynomial with range bounds. -/
theorem eventually_secondBranch_centralGaussianError : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    ∀ κ : ℝ, 0 < κ → ∀ (P : ℂ → ℂ) (u₀ : ℝ), IsSaddlePolynomial ε P → SaddleRangeBounds P u₀ →
      ∀ᶠ ℓ : ℝ in atTop, ∀ δ : ℝ, ε / 2 ≤ δ → u₀ ≤ 1 + δ →
        ‖∫ T : ℝ in Icc (-(saddleSourceSecondBranchCentralRadius ε ℓ (1 + δ)))
            (saddleSourceSecondBranchCentralRadius ε ℓ (1 + δ)),
            (centeredIntegrand ε ℓ P (1 + δ) (vℓ ε ℓ (1 + δ)) T -
              gaussianIntegrand ε ℓ P (1 + δ) T)‖ <
          κ * ‖P (I * ((1 + δ : ℝ) : ℂ))‖ *
            ∫ T : ℝ, saddleSourceGaussianKernel ε ℓ (1 + δ) T := by
  filter_upwards [self_mem_nhdsWithin, eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_upper_shortMargin_positive, eventually_saddleSourceGaussianVariance_secondBranch_pos,
    eventually_saddleSourceSecondBranch_cubic_window,
    eventually_saddleSourceSecondBranch_central_radius_lt]
    with ε hε horder hmargin hvariance hcubic hradius
  change 0 < ε at hε
  have hmargin' : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a := fun a ha ↦ by linarith [hmargin a ha]
  intro κ hκ P u₀ hP hrange
  obtain ⟨q, hq, hqone, hfactor⟩ := exists_saddleSource_central_error_tolerance hκ
  obtain ⟨R, hR, hwindow⟩ := hrange.exists_central_window hq
  filter_upwards [eventually_gt_atTop (0 : ℝ), hcubic q hq, hradius R hR]
    with ℓ hℓ hqc hsmall δ hδ hu₀
  have hu : (-1 : ℝ) < 1 + δ := by linarith
  have hV : 0 < V_u ε ℓ (1 + δ) := hvariance ℓ hℓ δ hδ
  have hphase : ∀ T : ℝ, |T| ≤ saddleSourceSecondBranchCentralRadius ε ℓ (1 + δ) →
      ℓ * M₃ ε ℓ (1 + δ - 1) / 6 * |T| ^ 3 ≤ q := by
    intro T hT
    rw [show 1 + δ - 1 = δ by ring]
    exact (hqc δ hδ T hT).le
  exact centralGaussianError_lt (hrange.norm_pos _ hu₀)
    (saddleSourceGaussianKernel_integral_pos hℓ hV) hfactor
    (centeredIntegrand_centralGaussianError_le hε hℓ hu horder hmargin' hV hq.le hqone hq.le hP
      hphase fun T hT ↦ hwindow (1 + δ) hu₀ T (hT.trans (hsmall δ hδ).le))

theorem upperPositiveShellDamping_local_variance_lower {ε ℓ δ T : ℝ} (hε : 0 < ε) (hℓ : 0 ≤ ℓ)
    (hT : |T| ≤ 1 / (2 * (Bε ε + 1))) : ℓ / 4 * V_B ε δ * T ^ 2 ≤ D_B ε ℓ δ T := by
  have hB : (0 : ℝ) ≤ Bε ε := by unfold Bε; positivity
  have hB1 : (0 : ℝ) < Bε ε + 1 := by linarith
  have hwindow : (Bε ε + 1) * |T| ≤ 1 / 2 := by
    calc (Bε ε + 1) * |T| ≤ (Bε ε + 1) * (1 / (2 * (Bε ε + 1))) :=
          mul_le_mul_of_nonneg_left hT hB1.le
      _ = 1 / 2 := by field_simp [hB1.ne']
  have hdensity := positiveShellDensity_continuous ε
  have hleft : Continuous fun a : ℝ ↦
      w_B ε a * a ^ 2 * cosh ((1 + δ) * a) * (T ^ 2 / 4) := by fun_prop
  have hright : Continuous fun a : ℝ ↦
      w_B ε a * cosh ((1 + δ) * a) * (1 - cos (a * T)) := by fun_prop
  have hpoint : ∀ a ∈ Icc (Bε ε) (Bε ε + 1),
      w_B ε a * a ^ 2 * cosh ((1 + δ) * a) * (T ^ 2 / 4) ≤
        w_B ε a * cosh ((1 + δ) * a) * (1 - cos (a * T)) := by
    intro a ha
    have ha0 : 0 ≤ a := hB.trans ha.1
    have haT : |a * T| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg ha0]
      calc a * |T| ≤ (Bε ε + 1) * |T| := mul_le_mul_of_nonneg_right ha.2 (abs_nonneg T)
        _ ≤ 1 / 2 := hwindow
        _ ≤ 1 := by norm_num
    calc w_B ε a * a ^ 2 * cosh ((1 + δ) * a) * (T ^ 2 / 4)
        = w_B ε a * cosh ((1 + δ) * a) * ((a * T) ^ 2 / 4) := by ring
      _ ≤ w_B ε a * cosh ((1 + δ) * a) * (1 - cos (a * T)) :=
          mul_le_mul_of_nonneg_left (upper_one_sub_cos_quadratic_lower haT)
            (mul_nonneg (positiveShellDensity_nonneg ε a) (Real.cosh_pos _).le)
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (by linarith)
    (hleft.intervalIntegrable _ _) (hright.intervalIntegrable _ _) hpoint
  rw [intervalIntegral.integral_mul_const] at hmono
  unfold D_B
  calc ℓ / 4 * V_B ε δ * T ^ 2 = ℓ * (V_B ε δ * (T ^ 2 / 4)) := by ring
    _ ≤ ℓ * ∫ a in Bε ε..Bε ε + 1, w_B ε a * cosh ((1 + δ) * a) * (1 - cos (a * T)) :=
        mul_le_mul_of_nonneg_left hmono hℓ

theorem upperGammaVarianceDensity_laplace_linear_lower {ℓ η a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) :
    a * exp (-η * a) ≤ a ^ 2 * μ_ℓ ℓ η a := by
  have hden : 0 < 1 - exp (-(2 * a / ℓ)) := by
    have h := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (by positivity : (0 : ℝ) < 2 * a / ℓ))
    linarith
  have hdenone : 1 - exp (-(2 * a / ℓ)) ≤ 1 := by linarith [Real.exp_pos (-(2 * a / ℓ))]
  have hinv : 1 ≤ (1 - exp (-(2 * a / ℓ)))⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hden).2 (by simpa using hdenone)
  calc a * exp (-η * a) = a * exp (-η * a) * 1 := by ring
    _ ≤ a * exp (-η * a) * (1 - exp (-(2 * a / ℓ)))⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = a ^ 2 * μ_ℓ ℓ η a := by unfold μ_ℓ; field_simp [ha.ne', hden.ne']

theorem upperGammaDamping_local_variance_lower {ℓ η T : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (hT : |T| ≤ η) : ℓ / (32 * exp 1) * V_γ ℓ η * T ^ 2 ≤ D_γ ℓ η T := by
  let p : ℝ := 1 / (2 * η)
  let q : ℝ := 1 / η
  let C : ℝ := (ℓ / 4 + 1 / (4 * η)) * (exp 1)⁻¹ * (T ^ 2 / 4)
  have hp : 0 < p := by positivity
  have hq : 0 < q := by positivity
  have hpq : p ≤ q := by
    change (1 : ℝ) / (2 * η) ≤ 1 / η
    exact one_div_le_one_div_of_le hη (by linarith)
  have hsubset : Ioc p q ⊆ Ioi (0 : ℝ) := fun a ha ↦ hp.trans ha.1
  have hfull := upperGammaDampingIntegrand_integrable hℓ hη T
  have hconstant : IntegrableOn (fun _ : ℝ ↦ C) (Ioc p q) :=
    integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hpoint : ∀ a ∈ Ioc p q, C ≤ upperGammaDampingIntegrand ℓ η T a := by
    intro a ha
    have ha0 : 0 < a := hp.trans ha.1
    have halower : 1 / (2 * η) ≤ a := ha.1.le
    have haupper : a ≤ 1 / η := ha.2
    have heta : η * a ≤ 1 := by
      calc η * a ≤ η * (1 / η) := mul_le_mul_of_nonneg_left haupper hη.le
        _ = 1 := by field_simp
    have hquarter : 1 / (4 * η) ≤ a / 2 := by
      calc 1 / (4 * η) = 1 / (2 * η) / 2 := by ring
        _ ≤ a / 2 := by gcongr
    have hgammadensity := (upperGammaVarianceDensity_pointwise_bounds (η := η) hℓ ha0).1
    have hlaplace := upperGammaVarianceDensity_laplace_linear_lower (η := η) hℓ ha0
    have hmoment : (ℓ / 4 + 1 / (4 * η)) * (exp 1)⁻¹ ≤ a ^ 2 * μ_ℓ ℓ η a := by
      have hexp : (exp 1)⁻¹ ≤ exp (-η * a) := by
        rw [← Real.exp_neg]; exact Real.exp_le_exp.mpr (by linarith)
      calc (ℓ / 4 + 1 / (4 * η)) * (exp 1)⁻¹ ≤ (ℓ / 4 + 1 / (4 * η)) * exp (-η * a) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ ≤ (ℓ / 4 + a / 2) * exp (-η * a) := by gcongr
        _ ≤ a ^ 2 * μ_ℓ ℓ η a := by nlinarith
    have haT : |a * T| ≤ 1 := by
      rw [abs_mul, abs_of_pos ha0]
      calc a * |T| ≤ a * η := mul_le_mul_of_nonneg_left hT ha0.le
        _ = η * a := by ring
        _ ≤ 1 := heta
    calc C = T ^ 2 / 4 * ((ℓ / 4 + 1 / (4 * η)) * (exp 1)⁻¹) := by
          change (ℓ / 4 + 1 / (4 * η)) * (exp 1)⁻¹ * (T ^ 2 / 4) = _
          ring
      _ ≤ T ^ 2 / 4 * (a ^ 2 * μ_ℓ ℓ η a) := mul_le_mul_of_nonneg_left hmoment (by positivity)
      _ = (a * T) ^ 2 / 4 * μ_ℓ ℓ η a := by ring
      _ ≤ (1 - cos (a * T)) * μ_ℓ ℓ η a :=
          mul_le_mul_of_nonneg_right (upper_one_sub_cos_quadratic_lower haT)
            (upperGammaMeasureDensity_pos (η := η) hℓ ha0).le
      _ = upperGammaDampingIntegrand ℓ η T a := rfl
  have hmono := MeasureTheory.setIntegral_mono_on hconstant (hfull.mono_set hsubset)
    measurableSet_Ioc hpoint
  have hnonnegative :
      0 ≤ᶠ[ae (volume.restrict (Ioi (0 : ℝ)))] upperGammaDampingIntegrand ℓ η T := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    exact mul_nonneg (sub_nonneg.mpr (Real.cos_le_one _))
      (upperGammaMeasureDensity_pos (η := η) hℓ ha).le
  have hrestrict := MeasureTheory.setIntegral_mono_set hfull hnonnegative
    (Filter.Eventually.of_forall fun a ha ↦ hsubset ha)
  have hconstintegral : (∫ _a : ℝ in Ioc p q, C) = (q - p) * C := by
    rw [setIntegral_const]
    have : (volume : Measure ℝ).real (Ioc p q) = q - p := by
      change ((volume : Measure ℝ) (Ioc p q)).toReal = q - p
      rw [Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hpq)]
    rw [this]
    rfl
  have hscaled : ℓ * V_γ ℓ η ≤ ℓ / η + 1 / η ^ 2 := by
    calc ℓ * V_γ ℓ η ≤ ℓ * (1 / (2 * η) + 1 / (ℓ * η ^ 2)) :=
          mul_le_mul_of_nonneg_left (upperGammaVariance_bounds hℓ hη).2 hℓ.le
      _ = ℓ / (2 * η) + 1 / η ^ 2 := by field_simp [hℓ.ne', hη.ne']
      _ ≤ ℓ / η + 1 / η ^ 2 := by gcongr; linarith
  have hidentity : (q - p) * C = (ℓ / η + 1 / η ^ 2) / (32 * exp 1) * T ^ 2 := by
    change (1 / η - 1 / (2 * η)) * ((ℓ / 4 + 1 / (4 * η)) * (exp 1)⁻¹ * (T ^ 2 / 4)) = _
    field_simp [hη.ne', (Real.exp_pos 1).ne']
    ring
  calc ℓ / (32 * exp 1) * V_γ ℓ η * T ^ 2 = ℓ * V_γ ℓ η / (32 * exp 1) * T ^ 2 := by ring
    _ ≤ (ℓ / η + 1 / η ^ 2) / (32 * exp 1) * T ^ 2 := by gcongr
    _ = (q - p) * C := hidentity.symm
    _ = ∫ _a : ℝ in Ioc p q, C := hconstintegral.symm
    _ ≤ ∫ a : ℝ in Ioc p q, upperGammaDampingIntegrand ℓ η T a := hmono
    _ ≤ ∫ a : ℝ in Ioi 0, upperGammaDampingIntegrand ℓ η T a := hrestrict
    _ = D_γ ℓ η T := rfl

theorem eventually_saddleSourceContourDamping_secondBranch_local_coercivity :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ ℓ : ℝ, 0 < ℓ → ∀ δ : ℝ, ε / 2 ≤ δ → ∀ T : ℝ,
      |T| ≤ 1 / (2 * (Bε ε + 1)) →
        ℓ / (100 * exp 1) * V_u ε ℓ (1 + δ) * T ^ 2 ≤ saddleSourceContourDamping ε ℓ (1 + δ) T := by
  filter_upwards [self_mem_nhdsWithin, eventually_upperSaddleDamping_gamma_add_shell,
    eventually_upper_netShellVariance_bounds] with ε hε hdom hnet ℓ hℓ δ hδ T hT
  change 0 < ε at hε
  have hδ0 : 0 ≤ δ := by linarith
  have hη : (0 : ℝ) < 2 + δ := by linarith
  have hB : (0 : ℝ) ≤ Bε ε := by unfold Bε; positivity
  have hhalf : 1 / (2 * (Bε ε + 1)) ≤ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (Bε ε + 1))]
    nlinarith
  have hTgamma : |T| ≤ 2 + δ := by linarith [hT.trans hhalf]
  have hS : 0 ≤ V_B ε δ := (upperPositiveShellVariance_pos hε hδ0).le
  have hG : 0 ≤ V_γ ℓ (2 + δ) := le_trans (by positivity) (upperGammaVariance_bounds hℓ hη).1
  have heone : 1 ≤ exp 1 := Real.one_le_exp (by norm_num)
  have hγcoefficient : (1 : ℝ) / (100 * exp 1) ≤ 1 / (32 * exp 1) := by gcongr; norm_num
  have hγbase : 0 ≤ ℓ * V_γ ℓ (2 + δ) * T ^ 2 := by positivity
  have hγscaled : ℓ / (100 * exp 1) * V_γ ℓ (2 + δ) * T ^ 2 ≤ D_γ ℓ (2 + δ) T := by
    refine le_trans ?_ (upperGammaDamping_local_variance_lower hℓ hη hTgamma)
    convert mul_le_mul_of_nonneg_right hγcoefficient hγbase using 1 <;> ring
  have hscoefficient : (1 : ℝ) / (100 * exp 1) ≤ 99 / 100 * (1 / 4) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 100 * exp 1)]
    nlinarith
  have hsbase : 0 ≤ ℓ * V_B ε δ * T ^ 2 := by positivity
  have hsscaled : ℓ / (100 * exp 1) * V_B ε δ * T ^ 2 ≤ 99 / 100 * D_B ε ℓ δ T := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left
      (upperPositiveShellDamping_local_variance_lower hε hℓ.le hT)
      (by norm_num : (0 : ℝ) ≤ 99 / 100))
    convert mul_le_mul_of_nonneg_right hscoefficient hsbase using 1 <;> ring
  have hvariance : upperSaddleVariance ε ℓ δ ≤ V_γ ℓ (2 + δ) + V_B ε δ := by
    unfold upperSaddleVariance
    linarith [(hnet δ hδ).2]
  have hfactor : (0 : ℝ) ≤ ℓ / (100 * exp 1) * T ^ 2 := by positivity
  calc ℓ / (100 * exp 1) * V_u ε ℓ (1 + δ) * T ^ 2
      = ℓ / (100 * exp 1) * upperSaddleVariance ε ℓ δ * T ^ 2 := by simp [V_u]
    _ ≤ ℓ / (100 * exp 1) * V_γ ℓ (2 + δ) * T ^ 2 +
          ℓ / (100 * exp 1) * V_B ε δ * T ^ 2 := by
        linarith [mul_le_mul_of_nonneg_left hvariance hfactor]
    _ ≤ D_γ ℓ (2 + δ) T + 99 / 100 * D_B ε ℓ δ T := add_le_add hγscaled hsscaled
    _ ≤ D_u ε ℓ δ T := hdom ℓ hℓ δ hδ T
    _ = saddleSourceContourDamping ε ℓ (1 + δ) T := (saddleSourceContourDamping_eq_secondBranch
        ε ℓ δ T).symm

theorem eventually_saddleSourceContourDamping_secondBranch_min_lower_bound :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ ℓ : ℝ, 0 < ℓ → ∀ δ : ℝ, ε / 2 ≤ δ → ∀ T : ℝ,
      ℓ / (8 * exp 1) * min (T ^ 2 / (2 + δ)) |T| ≤ saddleSourceContourDamping ε ℓ (1 + δ) T := by
  filter_upwards [self_mem_nhdsWithin, eventually_upperSaddleDamping_gamma_add_shell]
    with ε hε hdom ℓ hℓ δ hδ T
  change 0 < ε at hε
  have hη : (0 : ℝ) < 2 + δ := by linarith
  have hshell : (0 : ℝ) ≤ 99 / 100 * D_B ε ℓ δ T :=
    mul_nonneg (by norm_num) (positiveShellDamping_nonneg hℓ.le)
  rw [saddleSourceContourDamping_eq_secondBranch]
  linarith [hdom ℓ hℓ δ hδ T, upperGammaDamping_lower_bound hℓ hη T]

theorem eventually_saddleSource_secondBranch_weighted_integrable : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    ∀ ℓ : ℝ, 0 < ℓ → ∀ δ : ℝ, ε / 2 ≤ δ → Integrable fun T : ℝ ↦
      saddleGaussianTailWeight T * exp (-saddleSourceContourDamping ε ℓ (1 + δ) T) := by
  filter_upwards [self_mem_nhdsWithin, eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_saddleSourceContourDamping_secondBranch_min_lower_bound]
    with ε hε horder hcoercive ℓ hℓ δ hδ
  change 0 < ε at hε
  exact integrable_saddleGaussianTailWeight_exp_neg (a := ℓ / (8 * exp 1)) (η := 2 + δ)
    (by positivity) (by linarith)
    (saddleSourceTailIntegrand_continuous hε hℓ (by linarith) horder) (hcoercive ℓ hℓ δ hδ)

end

end CohnElkies
