import CohnElkies.UpperBound.MellinProfile

/-!
# The residue expansion of the profiles (report §4.2, (78))

Principal values across a pole, the Gaussian-weighted correction terms, and the expansion of
`f_P(r)` as the sum of the residues `r^{2n} poleResidue n` at the poles `z = -2n`, `n ≤ N`, plus the
remainder integral along the Taylor contour `Re z = -(2N + 1)`
(`mellinProfile_eq_residue_sum_add_remainder`, `plusSaddleProfile_eq_residue_sum_add_remainder`).
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter Set MeasureTheory intervalIntegral
open scoped Interval Topology

/-! ### Principal values across a pole

Report (78).  The symmetric principal value of `(a + it + 2n)⁻¹` over a vertical line equals `π`
to the right of the pole `z = -2n` and `-π` to its left; the jump `2π` is what produces the
residue terms of the Taylor expansion of `f₊`, `f₋`. -/

/-- Principal value of `(a + it + 2n)⁻¹` on a line to the right of the pole `-2n`. -/
theorem tendsto_polePV_pos (n : ℕ) {a : ℝ} (ha : -(2 * n : ℝ) < a) :
    Tendsto (fun T : ℝ ↦ ∫ t in -T..T, ((a : ℂ) + t * I + (2 * n : ℂ))⁻¹)
      atTop (𝓝 (π : ℂ)) := by
  have hb : 0 < a + (2 * n : ℝ) := by linarith
  have harctan : Tendsto (fun T : ℝ ↦ 2 * Real.arctan (T / (a + (2 * n : ℝ))))
      atTop (𝓝 π) := by
    simpa [show (2 : ℝ) * (π / 2) = π by ring] using
      ((tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp
        ((tendsto_div_const_atTop_of_pos hb).2 tendsto_id)).const_mul (2 : ℝ)
  have hcomplex : Tendsto (fun T : ℝ ↦ ((2 * Real.arctan (T / (a + (2 * n : ℝ))) : ℝ) : ℂ))
      atTop (𝓝 (π : ℂ)) := Complex.continuous_ofReal.continuousAt.tendsto.comp harctan
  refine hcomplex.congr fun T ↦ ?_
  rw [← saddleCauchyPole_symmetric_intervalIntegral hb.ne' T]
  exact intervalIntegral.integral_congr fun t _ ↦ by push_cast; ring

/-- Principal value of `(a + it + 2n)⁻¹` on a line to the left of the pole `-2n`. -/
theorem tendsto_polePV_neg (n : ℕ) {a : ℝ} (ha : a < -(2 * n : ℝ)) :
    Tendsto (fun T : ℝ ↦ ∫ t in -T..T, ((a : ℂ) + t * I + (2 * n : ℂ))⁻¹)
      atTop (𝓝 (-(π : ℂ))) := by
  have hb : a + (2 * n : ℝ) < 0 := by linarith
  have harctan : Tendsto (fun T : ℝ ↦ 2 * Real.arctan (T / (a + (2 * n : ℝ))))
      atTop (𝓝 (-π)) := by
    simpa [show (2 : ℝ) * -(π / 2) = -π by ring] using
      ((tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atBot).comp
        ((tendsto_div_const_atBot_of_neg hb).2 tendsto_id)).const_mul (2 : ℝ)
  have hcomplex : Tendsto (fun T : ℝ ↦ ((2 * Real.arctan (T / (a + (2 * n : ℝ))) : ℝ) : ℂ))
      atTop (𝓝 (-(π : ℂ))) := by
    simpa only [Function.comp_def, Complex.ofReal_neg] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp harctan
  refine hcomplex.congr fun T ↦ ?_
  rw [← saddleCauchyPole_symmetric_intervalIntegral hb.ne T]
  exact intervalIntegral.integral_congr fun t _ ↦ by push_cast; ring

/-! ### The rectangular contour -/

/-- The boundary integral of an entire function over the rectangle `[A, B] × [-T, T]` vanishes. -/
theorem boundary_rect_eq_zero {F : ℂ → ℂ} (hF : Differentiable ℂ F) (A B T : ℝ) :
    (∫ a in A..B, F ((a : ℂ) + (-T : ℂ) * I)) - (∫ a in A..B, F ((a : ℂ) + (T : ℂ) * I)) +
      I * (∫ t in -T..T, F ((B : ℂ) + t * I)) - I * (∫ t in -T..T, F ((A : ℂ) + t * I)) = 0 := by
  simpa [Complex.mul_re, Complex.mul_im, smul_eq_mul] using
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn F ((A : ℂ) + (-T : ℂ) * I)
      ((B : ℂ) + (T : ℂ) * I) hF.differentiableOn

/-- If the horizontal sides of the rectangle vanish in the limit and its boundary integral is
zero, the two limiting vertical principal values agree. -/
theorem vertical_limit_eq {F : ℂ → ℂ} {A B : ℝ} {u v : ℂ}
    (hleft : Tendsto (fun T : ℝ ↦ ∫ t in -T..T, F ((A : ℂ) + t * I)) atTop (𝓝 u))
    (hright : Tendsto (fun T : ℝ ↦ ∫ t in -T..T, F ((B : ℂ) + t * I)) atTop (𝓝 v))
    (hlower : Tendsto (fun T : ℝ ↦ ∫ a in A..B, F ((a : ℂ) + (-T : ℂ) * I)) atTop (𝓝 0))
    (hupper : Tendsto (fun T : ℝ ↦ ∫ a in A..B, F ((a : ℂ) + (T : ℂ) * I)) atTop (𝓝 0))
    (hrect : ∀ T : ℝ, (∫ a in A..B, F ((a : ℂ) + (-T : ℂ) * I)) -
      (∫ a in A..B, F ((a : ℂ) + (T : ℂ) * I)) + I * (∫ t in -T..T, F ((B : ℂ) + t * I)) -
      I * (∫ t in -T..T, F ((A : ℂ) + t * I)) = 0) :
    v = u := by
  have hzero : Tendsto (fun T : ℝ ↦ (∫ a in A..B, F ((a : ℂ) + (-T : ℂ) * I)) -
      (∫ a in A..B, F ((a : ℂ) + (T : ℂ) * I)) + I * (∫ t in -T..T, F ((B : ℂ) + t * I)) -
      I * (∫ t in -T..T, F ((A : ℂ) + t * I))) atTop (𝓝 0) :=
    tendsto_const_nhds.congr fun T ↦ (hrect T).symm
  have hid : I * (v - u) = 0 := by
    simpa [mul_sub] using tendsto_nhds_unique
      (((hlower.sub hupper).add (hright.const_mul I)).sub (hleft.const_mul I)) hzero
  exact sub_eq_zero.mp ((mul_eq_zero.mp hid).resolve_left Complex.I_ne_zero)

/-! ### The Gaussian pole representative and its slope -/

/-- On a vertical line missing the pole `-2n`, the shifted coordinate never vanishes. -/
theorem shiftedLine_add_ne_zero (n : ℕ) {a : ℝ} (ha : a ≠ -(2 * n : ℝ)) (t : ℝ) :
    (a : ℂ) + t * I + (2 * n : ℂ) ≠ 0 := by
  intro hzero
  apply ha
  have hre := congrArg Complex.re hzero
  norm_num [Complex.mul_re] at hre
  linarith

/-- `G_n z = (z + 2n)⁻¹ + (slope of `exp` at the pole)`: the Gaussian representative has the same
simple pole as `(z + 2n)⁻¹`, the difference being entire. -/
theorem gaussianPole_eq_inv_add_slope (n : ℕ) {z : ℂ} (hz : z + (2 * n : ℂ) ≠ 0) :
    saddleGaussianPoleRepresentative n z =
      (z + (2 * n : ℂ))⁻¹ + saddleGaussianPoleSlope (z + (2 * n : ℂ)) := by
  rw [saddleGaussianPoleSlope_eq_of_ne hz]
  unfold saddleGaussianPoleRepresentative
  field_simp [hz]
  all_goals ring

/-- The entire part of the Gaussian representative decays like `1 / |t|` on horizontal lines, so
the horizontal sides of the rectangle do not contribute. -/
theorem tendsto_slope_horizontalIntegral {A B : ℝ} (hAB : A ≤ B) (n : ℕ) (s : ℝ) (hs : |s| = 1) :
    Tendsto (fun T : ℝ ↦ ∫ a in A..B,
        saddleGaussianPoleSlope ((a : ℂ) + (s * T : ℂ) * I + (2 * n : ℂ)))
      atTop (𝓝 0) := by
  obtain ⟨C, -, hgauss⟩ := saddleGaussianPoleRepresentative_weighted_horizontalStrip_bound
    (r := 1) one_pos hAB n
  refine saddleHorizontalIntegral_tendsto_zero
    (F := fun z : ℂ ↦ saddleGaussianPoleSlope (z + (2 * n : ℂ))) hAB (C := C + 1) ?_ s hs
  intro a ha t ht
  have hden : |t| ≤ ‖(a : ℂ) + t * I + (2 * n : ℂ)‖ := by
    simpa [Complex.mul_im] using Complex.abs_im_le_norm ((a : ℂ) + t * I + (2 * n : ℂ))
  have hpos : 0 < ‖(a : ℂ) + t * I + (2 * n : ℂ)‖ := (zero_lt_one.trans_le ht).trans_le hden
  have hslope : saddleGaussianPoleSlope ((a : ℂ) + t * I + (2 * n : ℂ)) =
      saddleGaussianPoleRepresentative n ((a : ℂ) + t * I) -
        ((a : ℂ) + t * I + (2 * n : ℂ))⁻¹ := by
    rw [gaussianPole_eq_inv_add_slope n (norm_pos_iff.mp hpos)]
    ring
  have hgauss' : |t| * ‖saddleGaussianPoleRepresentative n ((a : ℂ) + t * I)‖ ≤ C := by
    simpa [saddleMellinInversePower] using hgauss a ha t ht
  have hinv : |t| * ‖((a : ℂ) + t * I + (2 * n : ℂ))⁻¹‖ ≤ 1 := by
    rw [norm_inv, ← div_eq_mul_inv]
    exact (div_le_one hpos).2 hden
  rw [hslope]
  refine le_trans (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (abs_nonneg t)) ?_
  rw [mul_add]
  exact add_le_add hgauss' hinv

/-- Splitting the pole off the vertical integral over a line missing `-2n`. -/
theorem integral_slope_eq_sub (n : ℕ) {a : ℝ} (ha : a ≠ -(2 * n : ℝ)) (T : ℝ) :
    (∫ t in -T..T, saddleGaussianPoleSlope ((a : ℂ) + t * I + (2 * n : ℂ))) =
      (∫ t in -T..T, saddleGaussianPoleRepresentative n ((a : ℂ) + t * I)) -
        ∫ t in -T..T, ((a : ℂ) + t * I + (2 * n : ℂ))⁻¹ := by
  have hpole : IntervalIntegrable (fun t : ℝ ↦ ((a : ℂ) + t * I + (2 * n : ℂ))⁻¹)
      volume (-T) T :=
    ((by fun_prop : Continuous fun t : ℝ ↦ (a : ℂ) + t * I + (2 * n : ℂ)).inv₀
      (shiftedLine_add_ne_zero n ha)).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub
    ((saddleGaussianPoleRepresentative_shiftedLine_continuous n ha).intervalIntegrable _ _) hpole]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  rw [gaussianPole_eq_inv_add_slope n (shiftedLine_add_ne_zero n ha t)]
  ring

/-- The limiting principal value of the entire part, given that of the pole. -/
theorem tendsto_integral_slope {n : ℕ} {a : ℝ} (ha : a ≠ -(2 * n : ℝ)) {c : ℂ}
    (hpole : Tendsto (fun T : ℝ ↦ ∫ t in -T..T, ((a : ℂ) + t * I + (2 * n : ℂ))⁻¹)
      atTop (𝓝 c)) :
    Tendsto (fun T : ℝ ↦ ∫ t in -T..T,
        saddleGaussianPoleSlope ((a : ℂ) + t * I + (2 * n : ℂ))) atTop
      (𝓝 ((∫ t : ℝ, saddleGaussianPoleRepresentative n ((a : ℂ) + t * I)) - c)) :=
  ((intervalIntegral_tendsto_integral (saddleGaussianPoleRepresentative_shiftedLine_integrable n ha)
    tendsto_neg_atTop_atBot tendsto_id).sub hpole).congr fun T ↦ (integral_slope_eq_sub n ha T).symm

/-- Report (78): crossing the pole `z = -2n` changes the vertical integral of the Gaussian
representative `G_n` by `2π`. -/
theorem integral_gaussianPole_jump (n : ℕ) {A B : ℝ} (hA : A < -(2 * n : ℝ))
    (hB : -(2 * n : ℝ) < B) :
    (∫ t : ℝ, saddleGaussianPoleRepresentative n ((B : ℂ) + t * I)) -
      (∫ t : ℝ, saddleGaussianPoleRepresentative n ((A : ℂ) + t * I)) = (2 * π : ℂ) := by
  have hAB : A ≤ B := (hA.trans hB).le
  have hdiff : Differentiable ℂ fun z : ℂ ↦ saddleGaussianPoleSlope (z + (2 * n : ℂ)) :=
    saddleGaussianPoleSlope_differentiable.comp (by fun_prop)
  have hidentity := vertical_limit_eq
    (F := fun z : ℂ ↦ saddleGaussianPoleSlope (z + (2 * n : ℂ)))
    (tendsto_integral_slope hA.ne (tendsto_polePV_neg n hA))
    (tendsto_integral_slope hB.ne' (tendsto_polePV_pos n hB))
    (by simpa using tendsto_slope_horizontalIntegral hAB n (-1) (by norm_num))
    (by simpa using tendsto_slope_horizontalIntegral hAB n 1 (by norm_num))
    fun T ↦ boundary_rect_eq_zero hdiff A B T
  linear_combination hidentity

/-! ### The Gaussian-weighted correction

Report (41): `r ^ (-z) · G_n z` differs from `r ^ (2n) · G_n z` by an entire function, so only the
latter contributes a residue. -/

/-- `r ^ (-z)` at the pole `z = -2n` is `r ^ (2n)`. -/
theorem inversePower_neg_even (r : ℝ) (n : ℕ) :
    saddleMellinInversePower r (-(2 * n : ℂ)) = (r ^ (2 * n) : ℂ) := by
  unfold saddleMellinInversePower
  rw [neg_neg]
  norm_cast

/-- The slope of `z ↦ r ^ (-z)` at the pole `z = -2n`. -/
def poleSlope (r : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  dslope (saddleMellinInversePower r) (-(2 * n : ℂ)) z

/-- The entire correction `exp ((z + 2n) ^ 2) · poleSlope r n z` measuring the difference between
`r ^ (-z) · G_n z` and `r ^ (2n) · G_n z`. -/
def poleCorrection (r : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  Complex.exp ((z + (2 * n : ℂ)) ^ 2) * poleSlope r n z

theorem differentiable_poleCorrection {r : ℝ} (hr : 0 < r) (n : ℕ) :
    Differentiable ℂ (poleCorrection r n) := by
  have hslope : Differentiable ℂ (poleSlope r n) :=
    differentiableOn_univ.mp ((Complex.differentiableOn_dslope (s := univ)
      (c := -(2 * n : ℂ)) univ_mem).mpr
      (saddleMellinInversePower_differentiable hr).differentiableOn)
  unfold poleCorrection
  exact (by fun_prop : Differentiable ℂ fun z : ℂ ↦
    Complex.exp ((z + (2 * n : ℂ)) ^ 2)).mul hslope

/-- The weighted pole representative `r ^ (-z) · G_n z` appearing in the contour shift. -/
def weightedPole (r : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  saddleMellinInversePower r z * saddleGaussianPoleRepresentative n z

/-- Report (41): `r ^ (-z) · G_n z = r ^ (2n) · G_n z + (entire correction)`. -/
theorem weighted_eq_pole_add_correction {r : ℝ} (n : ℕ) {z : ℂ}
    (hz : z + (2 * n : ℂ) ≠ 0) :
    weightedPole r n z =
      (r ^ (2 * n) : ℂ) * saddleGaussianPoleRepresentative n z + poleCorrection r n z := by
  have hslope := sub_smul_dslope (saddleMellinInversePower r) (-(2 * n : ℂ)) z
  rw [show z - -(2 * n : ℂ) = z + (2 * n : ℂ) from by ring, smul_eq_mul] at hslope
  have hdiv : poleSlope r n z = (saddleMellinInversePower r z -
      saddleMellinInversePower r (-(2 * n : ℂ))) / (z + (2 * n : ℂ)) :=
    (eq_div_iff hz).2 (by rw [mul_comm]; exact hslope)
  rw [← inversePower_neg_even r n]
  unfold weightedPole saddleGaussianPoleRepresentative poleCorrection
  rw [hdiv]
  field_simp [hz]
  all_goals ring

theorem poleCorrection_eq_sub {r : ℝ} (n : ℕ) {z : ℂ} (hz : z + (2 * n : ℂ) ≠ 0) :
    poleCorrection r n z =
      weightedPole r n z - (r ^ (2 * n) : ℂ) * saddleGaussianPoleRepresentative n z :=
  eq_sub_of_add_eq' (weighted_eq_pole_add_correction n hz).symm

theorem poleCorrection_integrable {r a : ℝ} (hr : 0 < r) (n : ℕ) (ha : a ≠ -(2 * n : ℝ)) :
    Integrable fun t : ℝ ↦ poleCorrection r n ((a : ℂ) + t * I) :=
  ((saddleGaussianPoleRepresentative_shiftedLine_weighted_integrable n ha hr).sub
    ((saddleGaussianPoleRepresentative_shiftedLine_integrable n ha).const_mul
      (r ^ (2 * n) : ℂ))).congr (Filter.Eventually.of_forall fun t ↦
      (poleCorrection_eq_sub n (shiftedLine_add_ne_zero n ha t)).symm)

theorem poleCorrection_horizontalStrip_bound {r A B : ℝ} (hr : 0 < r) (hAB : A ≤ B) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ Set.Icc A B, ∀ t : ℝ, 1 ≤ |t| →
      |t| * ‖poleCorrection r n ((a : ℂ) + t * I)‖ ≤ C := by
  obtain ⟨Cw, hCw, hw⟩ := saddleGaussianPoleRepresentative_weighted_horizontalStrip_bound hr hAB n
  obtain ⟨Cu, hCu, hu⟩ :=
    saddleGaussianPoleRepresentative_weighted_horizontalStrip_bound (r := 1) one_pos hAB n
  refine ⟨Cw + ‖(r ^ (2 * n) : ℂ)‖ * Cu, by positivity, ?_⟩
  intro a ha t ht
  have hden : |t| ≤ ‖(a : ℂ) + t * I + (2 * n : ℂ)‖ := by
    simpa [Complex.mul_im] using Complex.abs_im_le_norm ((a : ℂ) + t * I + (2 * n : ℂ))
  have hu' : |t| * ‖saddleGaussianPoleRepresentative n ((a : ℂ) + t * I)‖ ≤ Cu := by
    simpa [saddleMellinInversePower] using hu a ha t ht
  rw [poleCorrection_eq_sub n (norm_pos_iff.mp ((zero_lt_one.trans_le ht).trans_le hden))]
  refine le_trans (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (abs_nonneg t)) ?_
  rw [mul_add]
  refine add_le_add (hw a ha t ht) ?_
  rw [norm_mul, ← mul_assoc, mul_comm |t|, mul_assoc]
  exact mul_le_mul_of_nonneg_left hu' (norm_nonneg _)

theorem tendsto_poleCorrection_horizontalIntegral {r A B : ℝ} (hr : 0 < r) (hAB : A ≤ B) (n : ℕ)
    (s : ℝ) (hs : |s| = 1) :
    Tendsto (fun T : ℝ ↦ ∫ a in A..B, poleCorrection r n ((a : ℂ) + (s * T : ℂ) * I))
      atTop (𝓝 0) := by
  obtain ⟨C, -, hbound⟩ := poleCorrection_horizontalStrip_bound hr hAB n
  exact saddleHorizontalIntegral_tendsto_zero hAB hbound s hs

/-- Being entire, the correction contributes the same vertical integral on every line. -/
theorem integral_poleCorrection_eq {r A B : ℝ} (hr : 0 < r) (n : ℕ) (hAB : A ≤ B)
    (hA : A ≠ -(2 * n : ℝ)) (hB : B ≠ -(2 * n : ℝ)) :
    (∫ t : ℝ, poleCorrection r n ((B : ℂ) + t * I)) =
      ∫ t : ℝ, poleCorrection r n ((A : ℂ) + t * I) :=
  saddleInfiniteRectangle_vertical_integral_eq (poleCorrection_integrable hr n hA)
    (poleCorrection_integrable hr n hB)
    (by simpa using tendsto_poleCorrection_horizontalIntegral hr hAB n (-1) (by norm_num))
    (by simpa using tendsto_poleCorrection_horizontalIntegral hr hAB n 1 (by norm_num))
    fun T ↦ boundary_rect_eq_zero (differentiable_poleCorrection hr n) A B T

theorem integral_weighted_eq {r a : ℝ} (hr : 0 < r) (n : ℕ) (ha : a ≠ -(2 * n : ℝ)) :
    (∫ t : ℝ, weightedPole r n ((a : ℂ) + t * I)) =
      (r ^ (2 * n) : ℂ) * (∫ t : ℝ, saddleGaussianPoleRepresentative n ((a : ℂ) + t * I)) +
        ∫ t : ℝ, poleCorrection r n ((a : ℂ) + t * I) := by
  have hrep := saddleGaussianPoleRepresentative_shiftedLine_integrable n ha
  have hsplit : (∫ t : ℝ, weightedPole r n ((a : ℂ) + t * I)) =
      ∫ t : ℝ, (r ^ (2 * n) : ℂ) * saddleGaussianPoleRepresentative n ((a : ℂ) + t * I) +
        poleCorrection r n ((a : ℂ) + t * I) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t ↦
      weighted_eq_pole_add_correction n (shiftedLine_add_ne_zero n ha t))
  rw [hsplit, MeasureTheory.integral_add (hrep.const_mul _) (poleCorrection_integrable hr n ha),
    integral_const_mul_of_integrable hrep]

/-- Report (78): crossing the pole `-2n` adds `2π · r ^ (2n)` to the weighted vertical integral. -/
theorem integral_weighted_jump {r A B : ℝ} (hr : 0 < r) (n : ℕ) (hA : A < -(2 * n : ℝ))
    (hB : -(2 * n : ℝ) < B) :
    (∫ t : ℝ, weightedPole r n ((B : ℂ) + t * I)) -
      (∫ t : ℝ, weightedPole r n ((A : ℂ) + t * I)) =
      (2 * π : ℂ) * (r ^ (2 * n) : ℂ) := by
  rw [integral_weighted_eq hr n hB.ne', integral_weighted_eq hr n hA.ne,
    integral_poleCorrection_eq hr n (hA.trans hB).le hA.ne hB.ne']
  linear_combination (r ^ (2 * n) : ℂ) * integral_gaussianPole_jump n hA hB

/-! ### Finite sums of pole representatives -/

theorem integrable_weightedSum {r a : ℝ} (hr : 0 < r) (c : ℕ → ℂ) (N : ℕ)
    (ha : ∀ n : ℕ, a ≠ -(2 * n : ℝ)) :
    Integrable fun t : ℝ ↦ ∑ n ∈ Finset.range (N + 1), c n * weightedPole r n ((a : ℂ) + t * I) :=
  integrable_finsetSum _ fun n _ ↦
    (saddleGaussianPoleRepresentative_shiftedLine_weighted_integrable n (ha n) hr).const_mul (c n)

theorem integral_weightedSum {r a : ℝ} (hr : 0 < r) (c : ℕ → ℂ) (N : ℕ)
    (ha : ∀ n : ℕ, a ≠ -(2 * n : ℝ)) :
    (∫ t : ℝ, ∑ n ∈ Finset.range (N + 1), c n * weightedPole r n ((a : ℂ) + t * I)) =
      ∑ n ∈ Finset.range (N + 1), c n * ∫ t : ℝ, weightedPole r n ((a : ℂ) + t * I) := by
  have hterm : ∀ n : ℕ, Integrable fun t : ℝ ↦ c n * weightedPole r n ((a : ℂ) + t * I) := fun n ↦
    (saddleGaussianPoleRepresentative_shiftedLine_weighted_integrable n (ha n) hr).const_mul (c n)
  rw [MeasureTheory.integral_finsetSum (Finset.range (N + 1)) fun n _ ↦ hterm n]
  exact Finset.sum_congr rfl fun n _ ↦ integral_const_mul_of_integrable
    (saddleGaussianPoleRepresentative_shiftedLine_weighted_integrable n (ha n) hr)

/-- Report (78): the total residue picked up when the contour crosses the poles `-2n`, `n ≤ N`. -/
theorem integral_weightedSum_jump {r A B : ℝ} (hr : 0 < r) (c : ℕ → ℂ) (N : ℕ)
    (hcross : ∀ n ∈ Finset.range (N + 1), A < -(2 * n : ℝ) ∧ -(2 * n : ℝ) < B) :
    (∑ n ∈ Finset.range (N + 1), c n * ∫ t : ℝ, weightedPole r n ((B : ℂ) + t * I)) -
      (∑ n ∈ Finset.range (N + 1), c n * ∫ t : ℝ, weightedPole r n ((A : ℂ) + t * I)) =
      (2 * π : ℂ) * ∑ n ∈ Finset.range (N + 1), c n * (r ^ (2 * n) : ℂ) := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  rw [← mul_sub, integral_weighted_jump hr n (hcross n hn).1 (hcross n hn).2]
  ring

/-! ### The residue expansion, for an abstract Mellin datum

Everything above is assembled once for an abstract datum `M` with residues `ρ` and regular part
`G` (Lemma 4.3 of the report), then specialised to `M₊` and `M₋`. -/

theorem shiftedLine_mem_halfPlane {a : ℝ} {N : ℕ} (ha : -(2 * ((N : ℝ) + 1)) < a) (t : ℝ) :
    (a : ℂ) + t * I ∈ saddleFinitePoleHalfPlane N := by
  change -(2 * ((N : ℝ) + 1)) < ((a : ℂ) + (t : ℂ) * I).re
  simpa [Complex.mul_re] using ha

/-- On a line missing every pole, the integral of `r ^ (-z) · G` is the integral of `r ^ (-z) · M`
minus the Gaussian pole contributions. -/
theorem integral_regularPart_eq {r a : ℝ} (hr : 0 < r) {M G : ℂ → ℂ} (ρ : ℕ → ℂ) (N : ℕ)
    (ha : ∀ n : ℕ, a ≠ -(2 * n : ℝ))
    (hM : Integrable fun t : ℝ ↦
      saddleMellinInversePower r ((a : ℂ) + t * I) * M ((a : ℂ) + t * I))
    (hG : ∀ t : ℝ, G ((a : ℂ) + t * I) = M ((a : ℂ) + t * I) -
      ∑ n ∈ Finset.range (N + 1), ρ n * saddleGaussianPoleRepresentative n ((a : ℂ) + t * I)) :
    (∫ t : ℝ, saddleMellinInversePower r ((a : ℂ) + t * I) * G ((a : ℂ) + t * I)) =
      (∫ t : ℝ, saddleMellinInversePower r ((a : ℂ) + t * I) * M ((a : ℂ) + t * I)) -
        ∑ n ∈ Finset.range (N + 1), ρ n * ∫ t : ℝ, weightedPole r n ((a : ℂ) + t * I) := by
  have hsplit : (∫ t : ℝ, saddleMellinInversePower r ((a : ℂ) + t * I) * G ((a : ℂ) + t * I)) =
      ∫ t : ℝ, saddleMellinInversePower r ((a : ℂ) + t * I) * M ((a : ℂ) + t * I) -
        ∑ n ∈ Finset.range (N + 1), ρ n * weightedPole r n ((a : ℂ) + t * I) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t ↦ by
      simp only [hG t, mul_sub, Finset.mul_sum, weightedPole]
      exact sub_right_inj.mpr (Finset.sum_congr rfl fun n _ ↦ by ring))
  rw [hsplit, MeasureTheory.integral_sub hM (integrable_weightedSum hr ρ N ha),
    integral_weightedSum hr ρ N ha]

/-! ### The Taylor contour `Re z = -(2N + 1)` -/

/-- The contour `Re z = -(2N + 1)` of report (78), just left of the pole `-2N`. -/
def saddleTaylorContour (N : ℕ) : ℝ := -(2 * N + 1 : ℝ)

theorem saddleTaylorContour_mem_halfPlane (N : ℕ) :
    -(2 * ((N : ℝ) + 1)) < saddleTaylorContour N := by
  simp only [saddleTaylorContour]
  linarith

theorem saddleTaylorContour_ne_pole (N n : ℕ) : saddleTaylorContour N ≠ -(2 * n : ℝ) := by
  intro heq
  simp only [saddleTaylorContour, neg_inj] at heq
  have hnat : 2 * N + 1 = 2 * n := by exact_mod_cast heq
  lia

theorem saddlePositiveContour_ne_pole {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) : ℓ ≠ -(2 * n : ℝ) :=
  ((neg_nonpos.mpr (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ))).trans_lt hℓ).ne'

theorem saddleTaylorContour_le {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) : saddleTaylorContour N ≤ ℓ :=
  ((neg_nonpos.mpr (by positivity : (0 : ℝ) ≤ 2 * (N : ℝ) + 1)).trans hℓ.le :
    -(2 * N + 1 : ℝ) ≤ ℓ)

theorem saddleTaylorContour_crosses_poles {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) :
    ∀ n ∈ Finset.range (N + 1),
      saddleTaylorContour N < -(2 * n : ℝ) ∧ -(2 * n : ℝ) < ℓ := fun n hn ↦ by
  have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  refine ⟨?_, (neg_nonpos.mpr (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ))).trans_lt hℓ⟩
  simp only [saddleTaylorContour, neg_lt_neg_iff]
  linarith

/-- Report (78): the normalized vertical integral of `M` on `Re z = ℓ` is the sum of the first
`N + 1` residue terms plus the same integral on the Taylor contour. -/
theorem normalized_eq_residue_sum_add_remainder {ℓ r : ℝ} (hℓ : 0 < ℓ) (hr : 0 < r)
    {M G : ℂ → ℂ} (ρ : ℕ → ℂ) (N : ℕ)
    (hMA : Integrable fun t : ℝ ↦ saddleMellinInversePower r
      ((saddleTaylorContour N : ℂ) + t * I) * M ((saddleTaylorContour N : ℂ) + t * I))
    (hMB : Integrable fun t : ℝ ↦
      saddleMellinInversePower r ((ℓ : ℂ) + t * I) * M ((ℓ : ℂ) + t * I))
    (hG : ∀ z ∈ saddleFinitePoleHalfPlane N, (∀ n : ℕ, z ≠ -(2 * n : ℂ)) →
      G z = M z - ∑ n ∈ Finset.range (N + 1), ρ n * saddleGaussianPoleRepresentative n z)
    (hshift : (∫ t : ℝ, saddleMellinInversePower r ((ℓ : ℂ) + t * I) * G ((ℓ : ℂ) + t * I)) =
      ∫ t : ℝ, saddleMellinInversePower r ((saddleTaylorContour N : ℂ) + t * I) *
        G ((saddleTaylorContour N : ℂ) + t * I)) :
    (2 * π : ℂ)⁻¹ *
        (∫ t : ℝ, saddleMellinInversePower r ((ℓ : ℂ) + t * I) * M ((ℓ : ℂ) + t * I)) =
      (∑ n ∈ Finset.range (N + 1), ρ n * (r ^ (2 * n) : ℂ)) + (2 * π : ℂ)⁻¹ *
        ∫ t : ℝ, saddleMellinInversePower r ((saddleTaylorContour N : ℂ) + t * I) *
          M ((saddleTaylorContour N : ℂ) + t * I) := by
  have hτ := saddleTaylorContour_mem_halfPlane N
  rw [integral_regularPart_eq hr ρ N (saddlePositiveContour_ne_pole hℓ) hMB fun t ↦ hG _
      (shiftedLine_mem_halfPlane (hτ.trans_le (saddleTaylorContour_le hℓ N)) t)
      (saddleShiftedLine_ne_pole (saddlePositiveContour_ne_pole hℓ) t),
    integral_regularPart_eq hr ρ N (saddleTaylorContour_ne_pole N) hMA fun t ↦ hG _
      (shiftedLine_mem_halfPlane hτ t)
      (saddleShiftedLine_ne_pole (saddleTaylorContour_ne_pole N) t)] at hshift
  have hnormal : (2 * π : ℂ)⁻¹ * (2 * π : ℂ) = 1 :=
    inv_mul_cancel₀ (by simp [Real.pi_ne_zero])
  have hexpand : (∫ t : ℝ, saddleMellinInversePower r ((ℓ : ℂ) + t * I) * M ((ℓ : ℂ) + t * I)) =
      (∫ t : ℝ, saddleMellinInversePower r ((saddleTaylorContour N : ℂ) + t * I) *
          M ((saddleTaylorContour N : ℂ) + t * I)) +
        (2 * π : ℂ) * ∑ n ∈ Finset.range (N + 1), ρ n * (r ^ (2 * n) : ℂ) := by
    linear_combination hshift +
      integral_weightedSum_jump hr ρ N (saddleTaylorContour_crosses_poles hℓ N)
  rw [hexpand, mul_add, ← mul_assoc, hnormal, one_mul]
  ring

/-! ### The Taylor expansion of the radial profiles `f₊`, `f₋` -/

theorem mellinInv_eq_normalized (M : ℂ → ℂ) (σ r : ℝ) :
    mellinInv σ M r = (2 * π : ℂ)⁻¹ *
      ∫ t : ℝ, saddleMellinInversePower r ((σ : ℂ) + t * I) * M ((σ : ℂ) + t * I) := by
  unfold mellinInv saddleMellinInversePower
  simp only [smul_eq_mul, Complex.real_smul, one_div]
  push_cast
  ring

/-- `f_P(r)`, `r > 0`, as the normalized vertical integral of `r^{-z} M_P(z)` over `Re z = λ`. -/
theorem mellinProfile_eq_normalized_vertical_integral {ε ℓ r : ℝ} (P : ℂ → ℂ) (c : ℝ)
    (hr : 0 < r) :
    mellinProfile ε ℓ P c r = (2 * π : ℂ)⁻¹ * (∫ t : ℝ, saddleMellinInversePower r
        ((ℓ : ℂ) + t * I) * mellinData ε ℓ P ((ℓ : ℂ) + t * I)) := by
  rw [mellinProfile_of_ne_zero ε ℓ P c hr.ne', mellinInv_eq_normalized]

/-- The remainder of report (78): the inverse Mellin integral of `M_P` over the Taylor contour. -/
def taylorRemainder (ε ℓ : ℝ) (P : ℂ → ℂ) (N : ℕ) (r : ℝ) : ℂ := (2 * π : ℂ)⁻¹ *
    (∫ t : ℝ, saddleMellinInversePower r ((saddleTaylorContour N : ℂ) + (t : ℂ) * I) *
        mellinData ε ℓ P ((saddleTaylorContour N : ℂ) + (t : ℂ) * I))

/-- The remainder of report (78) for `f₊`; definitionally `taylorRemainder ε ℓ (PPlus ε) N r`. -/
def plusSaddleTaylorRemainder (ε ℓ : ℝ) (N : ℕ) (r : ℝ) : ℂ := (2 * π : ℂ)⁻¹ *
    (∫ t : ℝ, saddleMellinInversePower r ((saddleTaylorContour N : ℂ) + (t : ℂ) * I) *
        MPlus ε ℓ ((saddleTaylorContour N : ℂ) + (t : ℂ) * I))

/-- Report (78): `f_P(r) = ∑_{n ≤ N} Res_n r ^ (2n) + remainder`. -/
theorem mellinProfile_eq_residue_sum_add_remainder {ε ℓ r : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : a₀ε ε ≤ Aε ε) {P : ℂ → ℂ} (hP : IsSaddlePolynomial ε P) (c : ℝ) (hr : 0 < r)
    (N : ℕ) :
    mellinProfile ε ℓ P c r = (∑ n ∈ Finset.range (N + 1), poleResidue ε ℓ P n *
        (r ^ (2 * n) : ℂ)) + taylorRemainder ε ℓ P N r := by
  rw [mellinProfile_eq_normalized_vertical_integral P c hr, taylorRemainder]
  exact normalized_eq_residue_sum_add_remainder hℓ hr (M := mellinData ε ℓ P)
    (G := rapidPoleRegularPart (mellinData ε ℓ P) (poleResidue ε ℓ P) N) (poleResidue ε ℓ P) N
    (mellinData_shiftedLine_weighted_integrable hε hℓ horder hP (saddleTaylorContour_ne_pole N)
      hr)
    (mellinData_shiftedLine_weighted_integrable hε hℓ horder hP (saddlePositiveContour_ne_pole hℓ)
      hr)
    (fun _ hz hpole ↦ rapidPoleRegularPart_eq_of_not_pole
      (isPoleDatum_mellinData hε horder ℓ hP.differentiable) hz hpole)
    (mellinData_rapidContourIntegrand_vertical_integral_eq hε hℓ horder hP hr N
      (saddleTaylorContour_mem_halfPlane N) (saddleTaylorContour_le hℓ N)
      (saddleTaylorContour_ne_pole N) (saddlePositiveContour_ne_pole hℓ))

/-- Report (78): `f₊(r) = ∑_{n ≤ N} Res_n r ^ (2n) + remainder`. -/
theorem plusSaddleProfile_eq_residue_sum_add_remainder {ε ℓ r : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : a₀ε ε ≤ Aε ε) (hr : 0 < r) (N : ℕ) :
    fPlus ε ℓ r = (∑ n ∈ Finset.range (N + 1), plusSaddlePoleResidue ε ℓ n *
        (r ^ (2 * n) : ℂ)) + plusSaddleTaylorRemainder ε ℓ N r :=
  mellinProfile_eq_residue_sum_add_remainder hε hℓ horder (isSaddlePolynomial_PPlus ε)
    (originValue ε ℓ) hr N

/-- On the line `Re z = a` the weight `r ^ (-z)` has constant modulus `r ^ (-a)`. -/
theorem saddleMellinInversePower_shiftedLine_integral_norm {r a : ℝ} (hr : 0 < r) (F : ℂ → ℂ)
    (hF : Integrable fun t : ℝ ↦ F ((a : ℂ) + t * I)) :
    (∫ t : ℝ, ‖saddleMellinInversePower r ((a : ℂ) + t * I) * F ((a : ℂ) + t * I)‖) =
      r ^ (-a) * ∫ t : ℝ, ‖F ((a : ℂ) + t * I)‖ := by
  rw [← integral_const_mul_of_integrable hF.norm]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t ↦ by
    simp only [norm_mul, saddleMellinInversePower_shiftedLine_norm hr a t])

theorem saddleTaylorContour_rpow (r : ℝ) (N : ℕ) :
    r ^ (-(saddleTaylorContour N)) = r ^ (2 * N + 1) := by
  unfold saddleTaylorContour
  rw [neg_neg]
  exact_mod_cast Real.rpow_natCast r (2 * N + 1)

end

end CohnElkies
