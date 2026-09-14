import CohnElkies.UpperBound.Residues

/-!
# The profiles `f₊`, `f₋` are Schwartz functions (report §4.1, Lemma 4.3)

Contour moments of the inverse Mellin kernel `(max u 0)^z` and their derivatives, smoothness of
the profiles at the origin (the residue expansion shows `f_P(r)` is a smooth function of `r²`),
the vertical contour moved into the right half-plane, derivatives of the contour moment far from
the origin, and the Schwartz decay, giving the test functions `plusSaddleSchwartz`,
`minusSaddleSchwartz` (and `mellinProfileSchwartz` for a general saddle polynomial).
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace Topology

/-! ### The positive power `u ↦ (max u 0)^z` -/

/-- `u ↦ (max u 0)^z`: the power `u ↦ u^z`, extended by `0` to the negative half-line. -/
def saddlePositiveCpow (z : ℂ) (u : ℝ) : ℂ := ((max u 0 : ℝ) : ℂ) ^ z

theorem saddlePositiveCpow_hasDerivAt_of_pos {z : ℂ} (hz : z ≠ 0) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (saddlePositiveCpow z) (z * saddlePositiveCpow (z - 1) u) u := by
  have hevent : saddlePositiveCpow z =ᶠ[𝓝 u] fun v : ℝ ↦ (v : ℂ) ^ z := by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    simp [saddlePositiveCpow, max_eq_left (mem_Ioi.mp hv).le]
  have hvalue : saddlePositiveCpow (z - 1) u = (u : ℂ) ^ (z - 1) := by
    simp [saddlePositiveCpow, max_eq_left hu.le]
  rw [hvalue]
  exact (hasDerivAt_ofReal_cpow_const hu.ne' hz).congr_of_eventuallyEq hevent

theorem saddlePositiveCpow_hasDerivAt {z : ℂ} (hz : 1 < z.re) (x : ℝ) :
    HasDerivAt (saddlePositiveCpow z) (z * saddlePositiveCpow (z - 1) x) x := by
  have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz
  have hsub : 0 < (z - 1).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hsub0 : z - 1 ≠ 0 := fun h ↦ by rw [h] at hsub; simp at hsub
  rcases lt_trichotomy x 0 with hneg | rfl | hpos
  · have hevent : saddlePositiveCpow z =ᶠ[𝓝 x] fun _ : ℝ ↦ (0 : ℂ) := by
      filter_upwards [Iio_mem_nhds hneg] with y hy
      simp [saddlePositiveCpow, max_eq_right (mem_Iio.mp hy).le, Complex.zero_cpow hz0]
    have hvalue : saddlePositiveCpow (z - 1) x = 0 := by
      simp [saddlePositiveCpow, max_eq_right hneg.le, Complex.zero_cpow hsub0]
    simpa [hvalue] using (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq hevent
  · have hvalue : saddlePositiveCpow (z - 1) 0 = 0 := by
      simp [saddlePositiveCpow, Complex.zero_cpow hsub0]
    have hcont : Continuous (saddlePositiveCpow (z - 1)) := by
      unfold saddlePositiveCpow
      exact (Complex.continuous_ofReal_cpow_const hsub).comp (continuous_id.max continuous_const)
    have htend : Tendsto (saddlePositiveCpow (z - 1)) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
      simpa [hvalue] using
        (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    rw [hvalue, mul_zero, hasDerivAt_iff_tendsto_slope_zero]
    refine htend.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    rcases lt_or_gt_of_ne ht0 with hneg | hpos
    · simp [saddlePositiveCpow, max_eq_right hneg.le, Complex.zero_cpow hz0,
        Complex.zero_cpow hsub0]
    · simp [saddlePositiveCpow, max_eq_left hpos.le, hz0, Complex.real_smul,
        Complex.cpow_sub z 1 (Complex.ofReal_ne_zero.mpr ht0), div_eq_mul_inv, mul_comm]
  · exact saddlePositiveCpow_hasDerivAt_of_pos hz0 hpos

theorem saddlePositiveCpow_norm_le_one {z : ℂ} (hz : 0 < z.re) {u : ℝ}
    (hu : u ∈ Ioo (-1 : ℝ) 1) : ‖saddlePositiveCpow z u‖ ≤ 1 := by
  unfold saddlePositiveCpow
  rw [Complex.norm_cpow_eq_rpow_re_of_nonneg (le_max_right u 0) hz.ne']
  exact Real.rpow_le_one (le_max_right u 0) (max_le hu.2.le zero_le_one) hz.le

/-! ### Contour moments of the inverse Mellin kernel -/

/-- The exponent `-(a + it)/2` of the inverse Mellin kernel `r ↦ r^{-z}` on the line `Re z = a`. -/
def saddleContourExponent (a t : ℝ) : ℂ := -(((a : ℂ) + (t : ℂ) * I) / 2)

@[simp] theorem saddleContourExponent_re (a t : ℝ) : (saddleContourExponent a t).re = -a / 2 := by
  simp [saddleContourExponent, Complex.mul_re]
  ring

@[simp] theorem saddleContourExponent_sub_nat_re (a t : ℝ) (j : ℕ) :
    (saddleContourExponent a t - (j : ℂ)).re = -a / 2 - (j : ℝ) := by
  simp [saddleContourExponent_re]

/-- `∏_{i<j} (-(a + iX)/2 - i)`: the falling factorial of the contour exponent, produced by
differentiating `u ↦ (max u 0)^{-(a+it)/2}` `j` times. -/
def saddleContourFallingPolynomial (a : ℝ) (j : ℕ) : Polynomial ℂ :=
  ∏ i ∈ Finset.range j,
    (Polynomial.C (-(a : ℂ) / 2) - Polynomial.C (I / 2) * Polynomial.X - Polynomial.C (i : ℂ))

theorem saddleContourFallingPolynomial_eval_succ (a t : ℝ) (j : ℕ) :
    (saddleContourFallingPolynomial a (j + 1)).eval (t : ℂ) =
      (saddleContourFallingPolynomial a j).eval (t : ℂ) *
        (saddleContourExponent a t - (j : ℂ)) := by
  simp only [saddleContourFallingPolynomial, Finset.prod_range_succ, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X, saddleContourExponent]
  ring

theorem saddlePolynomialWeightedData_integrable {D : ℝ → ℂ}
    (hD : ∀ j : ℕ, Integrable fun t : ℝ ↦ (t : ℂ) ^ j * D t) (P : Polynomial ℂ) :
    Integrable fun t : ℝ ↦ P.eval (t : ℂ) * D t := by
  have hpoint (t : ℝ) : ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * ((t : ℂ) ^ j * D t) =
      P.eval (t : ℂ) * D t := by
    rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  exact (integrable_finsetSum (Finset.range (P.natDegree + 1))
    fun j _ ↦ (hD j).const_mul (P.coeff j)).congr (Filter.Eventually.of_forall hpoint)

/-- `∫ (max u 0)^{-(a+it)/2-j} · (falling factorial)(t) · D(t) dt`, the `j`-th derivative in
`u = r²` of the inverse Mellin transform of `D` along the vertical line `Re z = a`. -/
def saddlePositiveContourMoment (a : ℝ) (j : ℕ) (D : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ t : ℝ, saddlePositiveCpow (saddleContourExponent a t - (j : ℂ)) u *
    ((saddleContourFallingPolynomial a j).eval (t : ℂ) * D t)

theorem saddlePositiveCpow_comp_continuous {a u : ℝ} {j : ℕ} (h : 0 < u ∨ (j : ℝ) < -a / 2) :
    Continuous fun t : ℝ ↦ saddlePositiveCpow (saddleContourExponent a t - (j : ℂ)) u := by
  have hfreq : Continuous fun t : ℝ ↦ saddleContourExponent a t - (j : ℂ) := by
    unfold saddleContourExponent; fun_prop
  unfold saddlePositiveCpow
  refine hfreq.const_cpow (h.imp (fun hu ↦ ?_) fun ha t ↦ ?_)
  · rw [max_eq_left hu.le]
    exact Complex.ofReal_ne_zero.mpr hu.ne'
  · have hpos : 0 < (saddleContourExponent a t - (j : ℂ)).re := by
      rw [saddleContourExponent_sub_nat_re]; linarith
    exact ne_of_apply_ne Complex.re (by simpa using hpos.ne')

/-- Differentiation of `saddlePositiveContourMoment` under the integral sign on an open set `s`,
from continuity, a uniform bound and the pointwise derivative of the power. -/
theorem saddlePositiveContourMoment_hasDerivAt_of_bounds {D : ℝ → ℂ}
    (hD : ∀ k : ℕ, Integrable fun t : ℝ ↦ (t : ℂ) ^ k * D t) {a : ℝ} {s : Set ℝ}
    (hs : IsOpen s) (j : ℕ)
    (hcont : ∀ k ≤ j + 1, ∀ v ∈ s,
      Continuous fun t : ℝ ↦ saddlePositiveCpow (saddleContourExponent a t - (k : ℂ)) v)
    (hnorm : ∀ k ≤ j + 1, ∀ v ∈ s, ∀ t : ℝ,
      ‖saddlePositiveCpow (saddleContourExponent a t - (k : ℂ)) v‖ ≤ 1)
    (hpow : ∀ t : ℝ, ∀ v ∈ s,
      HasDerivAt (saddlePositiveCpow (saddleContourExponent a t - (j : ℂ)))
        ((saddleContourExponent a t - (j : ℂ)) *
          saddlePositiveCpow (saddleContourExponent a t - (j : ℂ) - 1) v) v)
    {u : ℝ} (hu : u ∈ s) :
    HasDerivAt (saddlePositiveContourMoment a j D)
      (saddlePositiveContourMoment a (j + 1) D u) u := by
  have hW (k : ℕ) :
      Integrable fun t : ℝ ↦ (saddleContourFallingPolynomial a k).eval (t : ℂ) * D t :=
    saddlePolynomialWeightedData_integrable hD _
  have hmeas (k : ℕ) (hk : k ≤ j + 1) {v : ℝ} (hv : v ∈ s) :
      AEStronglyMeasurable (fun t : ℝ ↦
        saddlePositiveCpow (saddleContourExponent a t - (k : ℂ)) v *
          ((saddleContourFallingPolynomial a k).eval (t : ℂ) * D t)) volume :=
    (hcont k hk v hv).aestronglyMeasurable.mul (hW k).aestronglyMeasurable
  have hdom (k : ℕ) (hk : k ≤ j + 1) {v : ℝ} (hv : v ∈ s) (t : ℝ) :
      ‖saddlePositiveCpow (saddleContourExponent a t - (k : ℂ)) v *
        ((saddleContourFallingPolynomial a k).eval (t : ℂ) * D t)‖ ≤
        ‖(saddleContourFallingPolynomial a k).eval (t : ℂ) * D t‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hnorm k hk v hv t)
  have hstep (t : ℝ) {v : ℝ} (hv : v ∈ s) : HasDerivAt
      (fun x : ℝ ↦ saddlePositiveCpow (saddleContourExponent a t - (j : ℂ)) x *
        ((saddleContourFallingPolynomial a j).eval (t : ℂ) * D t))
      (saddlePositiveCpow (saddleContourExponent a t - ((j + 1 : ℕ) : ℂ)) v *
        ((saddleContourFallingPolynomial a (j + 1)).eval (t : ℂ) * D t)) v := by
    have harg : saddleContourExponent a t - ((j + 1 : ℕ) : ℂ) =
        saddleContourExponent a t - (j : ℂ) - 1 := by push_cast; ring
    have hval : saddlePositiveCpow (saddleContourExponent a t - ((j + 1 : ℕ) : ℂ)) v *
        ((saddleContourFallingPolynomial a (j + 1)).eval (t : ℂ) * D t) =
        (saddleContourExponent a t - (j : ℂ)) *
          saddlePositiveCpow (saddleContourExponent a t - (j : ℂ) - 1) v *
          ((saddleContourFallingPolynomial a j).eval (t : ℂ) * D t) := by
      rw [harg, saddleContourFallingPolynomial_eval_succ]
      ring
    rw [hval]
    exact (hpow t v hv).mul_const ((saddleContourFallingPolynomial a j).eval (t : ℂ) * D t)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (v t : ℝ) ↦ saddlePositiveCpow (saddleContourExponent a t - (j : ℂ)) v *
      ((saddleContourFallingPolynomial a j).eval (t : ℂ) * D t))
    (F' := fun (v t : ℝ) ↦ saddlePositiveCpow (saddleContourExponent a t - ((j + 1 : ℕ) : ℂ)) v *
      ((saddleContourFallingPolynomial a (j + 1)).eval (t : ℂ) * D t))
    (bound := fun t : ℝ ↦ ‖(saddleContourFallingPolynomial a (j + 1)).eval (t : ℂ) * D t‖)
    (hs.mem_nhds hu)
    (Filter.eventually_of_mem (hs.mem_nhds hu) fun v hv ↦ hmeas j (Nat.le_succ j) hv)
    ((hW j).norm.mono' (hmeas j (Nat.le_succ j) hu)
      (Filter.Eventually.of_forall (hdom j (Nat.le_succ j) hu)))
    (hmeas (j + 1) le_rfl hu)
    (Filter.Eventually.of_forall fun t v hv ↦ hdom (j + 1) le_rfl hv t) (hW (j + 1)).norm
    (Filter.Eventually.of_forall fun t v hv ↦ hstep t hv)).2

theorem saddlePositiveContourMoment_hasDerivAt {D : ℝ → ℂ}
    (hD : ∀ k : ℕ, Integrable fun t : ℝ ↦ (t : ℂ) ^ k * D t) {a : ℝ} (j : ℕ)
    (ha : (j : ℝ) + 1 < -a / 2) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (saddlePositiveContourMoment a j D)
      (saddlePositiveContourMoment a (j + 1) D u) u := by
  have hlt {k : ℕ} (hk : k ≤ j + 1) : (k : ℝ) < -a / 2 := by
    have : (k : ℝ) ≤ (j : ℝ) + 1 := by exact_mod_cast hk
    linarith
  refine saddlePositiveContourMoment_hasDerivAt_of_bounds hD isOpen_Ioo j
    (fun k hk v _ ↦ saddlePositiveCpow_comp_continuous (Or.inr (hlt hk)))
    (fun k hk v hv t ↦ saddlePositiveCpow_norm_le_one (by
      rw [saddleContourExponent_sub_nat_re]; linarith [hlt hk]) hv)
    (fun t v _ ↦ saddlePositiveCpow_hasDerivAt (by
      rw [saddleContourExponent_sub_nat_re]; linarith) v) hu

/-- If `F (j+1)` is the derivative of `F j` on the open set `s` for `n` consecutive indices,
then `F j` is `Cⁿ` on `s`. -/
theorem contDiffOn_of_hasDerivAt_range {s : Set ℝ} (hs : IsOpen s) {F : ℕ → ℝ → ℂ} :
    ∀ n j : ℕ, (∀ k ≤ n, ∀ u ∈ s, HasDerivAt (F (j + k)) (F (j + k + 1) u) u) →
      ContDiffOn ℝ n (F j) s := by
  intro n
  induction n with
  | zero =>
      intro j h
      change ContDiffOn ℝ 0 (F j) s
      exact contDiffOn_zero.2 fun u hu ↦ (h 0 le_rfl u hu).continuousAt.continuousWithinAt
  | succ n ih =>
      intro j h
      have h0 : ∀ u ∈ s, HasDerivAt (F j) (F (j + 1) u) u := fun u hu ↦ h 0 (Nat.zero_le _) u hu
      rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by simp,
        contDiffOn_succ_iff_deriv_of_isOpen hs]
      refine ⟨fun u hu ↦ (h0 u hu).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      refine (ih (j + 1) fun k hk u hu ↦ ?_).congr fun u hu ↦ (h0 u hu).deriv
      rw [show j + 1 + k = j + (k + 1) by lia]
      exact h (k + 1) (by lia) u hu

theorem saddlePositiveContourMoment_contDiffOn {D : ℝ → ℂ}
    (hD : ∀ k : ℕ, Integrable fun t : ℝ ↦ (t : ℂ) ^ k * D t) {a : ℝ} (n j : ℕ)
    (ha : (n : ℝ) + (j : ℝ) + 1 < -a / 2) :
    ContDiffOn ℝ n (saddlePositiveContourMoment a j D) (Ioo (-1 : ℝ) 1) :=
  contDiffOn_of_hasDerivAt_range (F := fun k ↦ saddlePositiveContourMoment a k D) isOpen_Ioo n j
    fun k hk u hu ↦ saddlePositiveContourMoment_hasDerivAt hD (j + k) (by
      have hkn : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
      push_cast
      linarith) hu

theorem saddleMellinInversePower_eq_squaredPositiveCpow {r : ℝ} (hr : 0 < r) (z : ℂ) :
    saddleMellinInversePower r z = saddlePositiveCpow (-z / 2) (r ^ 2) := by
  unfold saddleMellinInversePower
  calc (r : ℂ) ^ (-z) = (r : ℂ) ^ (((2 : ℝ) : ℂ) * (-z / 2)) := by
        congr 1
        push_cast
        ring
    _ = ((r ^ (2 : ℝ) : ℝ) : ℂ) ^ (-z / 2) := Complex.cpow_mul_ofReal_nonneg hr.le 2 (-z / 2)
    _ = saddlePositiveCpow (-z / 2) (r ^ 2) := by
        simp [saddlePositiveCpow, max_eq_left (sq_nonneg r)]

@[simp] theorem saddlePositiveContourMoment_zero {a : ℝ} (j : ℕ) (ha : (j : ℝ) < -a / 2)
    (D : ℝ → ℂ) : saddlePositiveContourMoment a j D 0 = 0 := by
  have hzero (t : ℝ) : saddlePositiveCpow (saddleContourExponent a t - (j : ℂ)) 0 = 0 := by
    have hne : saddleContourExponent a t - (j : ℂ) ≠ 0 := by
      have hpos : 0 < (saddleContourExponent a t - (j : ℂ)).re := by
        rw [saddleContourExponent_sub_nat_re]; linarith
      exact ne_of_apply_ne Complex.re (by simpa using hpos.ne')
    simp [saddlePositiveCpow, Complex.zero_cpow hne]
  simp [saddlePositiveContourMoment, hzero]

/-! ### Smoothness at the origin (Lemma 4.3 of the report) -/

/-- The inverse Mellin integral along the vertical line `Re z = a`, as a function of `u = r²`. -/
def saddleSquaredContour (M : ℂ → ℂ) (a u : ℝ) : ℂ := (2 * π : ℂ)⁻¹ *
    saddlePositiveContourMoment a 0 (fun t : ℝ ↦ M ((a : ℂ) + (t : ℂ) * I)) u

theorem saddleSquaredContour_eq (M : ℂ → ℂ) (a : ℝ) {r : ℝ} (hr : 0 < r) :
    (2 * π : ℂ)⁻¹ * (∫ t : ℝ, saddleMellinInversePower r ((a : ℂ) + (t : ℂ) * I) *
        M ((a : ℂ) + (t : ℂ) * I)) = saddleSquaredContour M a (r ^ 2) := by
  have hpoint (t : ℝ) : saddleMellinInversePower r ((a : ℂ) + (t : ℂ) * I) *
      M ((a : ℂ) + (t : ℂ) * I) =
      saddlePositiveCpow (saddleContourExponent a t - ((0 : ℕ) : ℂ)) (r ^ 2) *
        ((saddleContourFallingPolynomial a 0).eval (t : ℂ) * M ((a : ℂ) + (t : ℂ) * I)) := by
    have hq : -((a : ℂ) + (t : ℂ) * I) / 2 = saddleContourExponent a t := by
      unfold saddleContourExponent; ring
    rw [saddleMellinInversePower_eq_squaredPositiveCpow hr ((a : ℂ) + (t : ℂ) * I), hq]
    simp [saddleContourFallingPolynomial]
  unfold saddleSquaredContour saddlePositiveContourMoment
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall hpoint)

theorem saddleSquaredContour_contDiffOn {M : ℂ → ℂ} {a : ℝ}
    (hM : ∀ k : ℕ, Integrable fun t : ℝ ↦ (t : ℂ) ^ k * M ((a : ℂ) + (t : ℂ) * I)) (n : ℕ)
    (hshift : (n : ℝ) + 1 < -a / 2) :
    ContDiffOn ℝ n (saddleSquaredContour M a) (Ioo (-1 : ℝ) 1) :=
  contDiff_const.contDiffOn.mul
    (saddlePositiveContourMoment_contDiffOn hM n 0 (by simpa using hshift))

/-- The Taylor polynomial `∑_{n ≤ N} Res_n u^n` of report (78), in the variable `u = r²`. -/
def saddleSquaredResiduePolynomial (c : ℕ → ℂ) (N : ℕ) (u : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (N + 1), c j * ((u : ℂ) ^ j)

theorem saddleTaylorContour_negativeHalf_pos (N : ℕ) : 0 < -(saddleTaylorContour N) / 2 := by
  simp only [saddleTaylorContour, neg_neg]
  positivity

@[simp] theorem saddleSquaredResiduePolynomial_zero (c : ℕ → ℂ) (N : ℕ) :
    saddleSquaredResiduePolynomial c N 0 = c 0 := by
  unfold saddleSquaredResiduePolynomial
  rw [Finset.sum_eq_single 0]
  · simp
  · exact fun j _ hj ↦ by simp [zero_pow hj]
  · simp

theorem saddleSquaredResiduePolynomial_contDiff (c : ℕ → ℂ) (N n : ℕ) :
    ContDiff ℝ n (saddleSquaredResiduePolynomial c N) := by
  unfold saddleSquaredResiduePolynomial
  exact ContDiff.sum fun j _ ↦ contDiff_const.mul (Complex.ofRealCLM.contDiff.pow j)

@[simp] theorem saddleSquaredContour_taylorContour_zero (M : ℂ → ℂ) (N : ℕ) :
    saddleSquaredContour M (saddleTaylorContour N) 0 = 0 := by
  have h : ((0 : ℕ) : ℝ) < -(saddleTaylorContour N) / 2 := by
    simpa using saddleTaylorContour_negativeHalf_pos N
  simp [saddleSquaredContour, saddlePositiveContourMoment_zero 0 h]

theorem saddleProfile_eq_squaredTaylor {f : ℝ → ℂ} {M : ℂ → ℂ} {c : ℕ → ℂ} {N : ℕ}
    (hzero : f 0 = c 0)
    (htaylor : ∀ r : ℝ, 0 < r → f r =
      (∑ n ∈ Finset.range (N + 1), c n * (r ^ (2 * n) : ℂ)) +
        saddleSquaredContour M (saddleTaylorContour N) (r ^ 2))
    {r : ℝ} (hr : 0 ≤ r) :
    f r = saddleSquaredResiduePolynomial c N (r ^ 2) +
      saddleSquaredContour M (saddleTaylorContour N) (r ^ 2) := by
  rcases hr.eq_or_lt with rfl | hpos
  · simp [hzero]
  · rw [htaylor r hpos]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    congr 1
    push_cast
    rw [← pow_mul]

theorem taylorRemainder_eq_squaredContour (ε ℓ : ℝ) (P : ℂ → ℂ) (N : ℕ) {r : ℝ} (hr : 0 < r) :
    taylorRemainder ε ℓ P N r =
      saddleSquaredContour (mellinData ε ℓ P) (saddleTaylorContour N) (r ^ 2) :=
  saddleSquaredContour_eq (mellinData ε ℓ P) _ hr

/-- Report (78) in the variable `u = r²`: `f_P(r) = ∑_{n ≤ N} Res_n (r²)^n + remainder`, for a
profile whose origin value is the residue at `z = 0`. -/
theorem mellinProfile_eq_squaredTaylor {ε ℓ : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : a₀ε ε ≤ Aε ε) {P : ℂ → ℂ} (hP : IsSaddlePolynomial ε P) {c : ℝ}
    (hc : (c : ℂ) = poleResidue ε ℓ P 0) (N : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    mellinProfile ε ℓ P c r = saddleSquaredResiduePolynomial (poleResidue ε ℓ P) N (r ^ 2) +
      saddleSquaredContour (mellinData ε ℓ P) (saddleTaylorContour N) (r ^ 2) :=
  saddleProfile_eq_squaredTaylor (by rw [mellinProfile_zero]; exact hc)
    (fun r hr ↦ by
      rw [mellinProfile_eq_residue_sum_add_remainder hε hℓ horder hP c hr N,
        taylorRemainder_eq_squaredContour ε ℓ P N hr]) hr

theorem saddleTaylorContour_smoothShift (n : ℕ) :
    (n : ℝ) + 1 < -(saddleTaylorContour (n + 2)) / 2 := by
  simp only [saddleTaylorContour, neg_neg]
  push_cast
  linarith

theorem dimension_half_pos {d : ℕ} (hd : 0 < d) : 0 < (d : ℝ) / 2 :=
  div_pos (by exact_mod_cast hd) two_pos

/-- Lemma 4.3 of the report: a radial function that agrees, for every `N`, with a polynomial in
`r²` plus a `C^N` inverse Mellin remainder is smooth (including at the origin). -/
theorem saddleFunction_contDiff {d : ℕ} {F : Euclidean d → ℂ} {M : ℂ → ℂ} {c : ℕ → ℂ}
    (hout : ContDiffOn ℝ ∞ F ({0}ᶜ : Set (Euclidean d)))
    (hmom : ∀ N k : ℕ, Integrable fun t : ℝ ↦
      (t : ℂ) ^ k * M ((saddleTaylorContour N : ℂ) + (t : ℂ) * I))
    (htaylor : ∀ (N : ℕ) (y : Euclidean d), F y =
      saddleSquaredResiduePolynomial c N (‖y‖ ^ 2) +
        saddleSquaredContour M (saddleTaylorContour N) (‖y‖ ^ 2)) :
    ContDiff ℝ ∞ F := by
  have hmem : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
  refine contDiff_infty.2 fun n ↦ contDiff_iff_contDiffAt.2 fun x ↦ ?_
  by_cases hx : x = 0
  · subst x
    have hsq : ContDiffAt ℝ n (fun y : Euclidean d ↦ ‖y‖ ^ 2) 0 := (contDiff_norm_sq ℝ).contDiffAt
    have hrem : ContDiffAt ℝ n (saddleSquaredContour M (saddleTaylorContour (n + 2)))
        (‖(0 : Euclidean d)‖ ^ 2) := by
      simpa using (saddleSquaredContour_contDiffOn (hmom (n + 2)) n
        (saddleTaylorContour_smoothShift n)).contDiffAt (isOpen_Ioo.mem_nhds hmem)
    exact (((saddleSquaredResiduePolynomial_contDiff c (n + 2) n).contDiffAt.fun_comp
      (0 : Euclidean d) hsq).add (hrem.fun_comp (0 : Euclidean d) hsq)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (htaylor (n + 2)))
  · exact ((hout.contDiffAt ((isOpen_compl_singleton (x := (0 : Euclidean d))).mem_nhds
      (by simpa using hx))).of_le (mod_cast le_top))

/-- Lemma 4.3: `x ↦ f_P(‖x‖)` is smooth on `ℝᵈ` when `f_P(0)` is the residue at `z = 0`. -/
theorem mellinProfileFun_contDiff {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : a₀ε ε ≤ Aε ε) {P : ℂ → ℂ} (hP : IsSaddlePolynomial ε P) {c : ℝ}
    (hc : (c : ℂ) = poleResidue ε (d / 2 : ℝ) P 0) : ContDiff ℝ ∞ (mellinProfileFun ε d P c) :=
  saddleFunction_contDiff (mellinProfileFun_contDiffOn hε hd horder hP c)
    (fun N k ↦ mellinData_shiftedLine_moment_integrable hε (dimension_half_pos hd) horder hP
      (saddleTaylorContour_ne_pole N) k)
    fun N y ↦ mellinProfile_eq_squaredTaylor hε (dimension_half_pos hd) horder hP hc N
      (norm_nonneg y)

end

noncomputable section

open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace SchwartzMap Topology

/-! ### Moving the vertical contour into the right half-plane -/

theorem saddleRightHalfPlane_boundary_rectangle {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.re}) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (T : ℝ) :
    (∫ a in A..B, F ((a : ℂ) + (-T : ℂ) * I)) -
      (∫ a in A..B, F ((a : ℂ) + (T : ℂ) * I)) +
      I * (∫ t in -T..T, F ((B : ℂ) + (t : ℂ) * I)) -
      I * (∫ t in -T..T, F ((A : ℂ) + (t : ℂ) * I)) = 0 := by
  let z : ℂ := (A : ℂ) + (-T : ℂ) * I
  let w : ℂ := (B : ℂ) + (T : ℂ) * I
  have hzre : z.re = A := by simp [z, Complex.mul_re]
  have hwre : w.re = B := by simp [w, Complex.mul_re]
  have hrect : DifferentiableOn ℂ F (Complex.reProdIm [[z.re, w.re]] [[z.im, w.im]]) := by
    refine hF.mono fun u hu ↦ ?_
    rcases mem_uIcc.mp (Complex.mem_reProdIm.mp hu).1 with h | h
    · rw [hzre] at h
      exact hA.trans_le h.1
    · rw [hwre] at h
      exact hB.trans_le h.1
  simpa [z, w, Complex.mul_re, Complex.mul_im, smul_eq_mul] using
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn F z w hrect

/-- Cauchy's theorem on the infinite rectangle: the weighted Mellin integral of `M` is the same
on every vertical line in the open right half-plane. -/
theorem saddleMellinData_vertical_integral_eq {M : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hhol : DifferentiableOn ℂ M {z : ℂ | 0 < z.re})
    (hint : ∀ a : ℝ, 0 < a → Integrable fun t : ℝ ↦
      saddleMellinInversePower r ((a : ℂ) + (t : ℂ) * I) * M ((a : ℂ) + (t : ℂ) * I))
    (htend : ∀ A B : ℝ, A ≤ B → ∀ s : ℝ, |s| = 1 → Tendsto (fun T : ℝ ↦ ∫ a in A..B,
      saddleMellinInversePower r ((a : ℂ) + (s * T : ℂ) * I) *
        M ((a : ℂ) + (s * T : ℂ) * I)) atTop (𝓝 0))
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (∫ t : ℝ, saddleMellinInversePower r ((B : ℂ) + (t : ℂ) * I) * M ((B : ℂ) + (t : ℂ) * I)) =
      ∫ t : ℝ, saddleMellinInversePower r ((A : ℂ) + (t : ℂ) * I) * M ((A : ℂ) + (t : ℂ) * I) := by
  have key : ∀ A B : ℝ, 0 < A → 0 < B → A ≤ B →
      (∫ t : ℝ, saddleMellinInversePower r ((B : ℂ) + (t : ℂ) * I) * M ((B : ℂ) + (t : ℂ) * I)) =
        ∫ t : ℝ, saddleMellinInversePower r ((A : ℂ) + (t : ℂ) * I) *
          M ((A : ℂ) + (t : ℂ) * I) := fun A B hA hB hAB ↦ by
    refine saddleInfiniteRectangle_vertical_integral_eq
      (F := fun z ↦ saddleMellinInversePower r z * M z) (hint A hA) (hint B hB) ?_ ?_
      fun T ↦ saddleRightHalfPlane_boundary_rectangle
        ((saddleMellinInversePower_differentiable hr).differentiableOn.mul hhol) hA hB T
    · simpa using htend A B hAB (-1) (by norm_num)
    · simpa using htend A B hAB 1 (by norm_num)
  rcases le_total A B with h | h
  · exact key A B hA hB h
  · exact (key B A hB hA h).symm

/-- Report §4.2: `f_P(r)` is the inverse Mellin integral of `M_P` over **any** vertical line in the
open right half-plane. -/
theorem mellinProfile_eq_positive_contour {ε ℓ r a : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : a₀ε ε ≤ Aε ε) {P : ℂ → ℂ} (hP : IsSaddlePolynomial ε P) (c : ℝ) (hr : 0 < r)
    (ha : 0 < a) :
    mellinProfile ε ℓ P c r = (2 * π : ℂ)⁻¹ * (∫ t : ℝ, saddleMellinInversePower r
        ((a : ℂ) + (t : ℂ) * I) * mellinData ε ℓ P ((a : ℂ) + (t : ℂ) * I)) := by
  rw [mellinProfile_eq_normalized_vertical_integral P c hr]
  congr 1
  exact saddleMellinData_vertical_integral_eq hr
    (mellinData_differentiableOn_rightHalfPlane hε horder ℓ hP.differentiable)
    (fun b hb ↦ mellinData_shiftedLine_weighted_integrable hε hℓ horder hP
      (saddlePositiveContour_ne_pole hb) hr)
    (fun A B hAB s hs ↦ mellinData_weighted_horizontalIntegral_tendsto_zero hε hℓ horder hP hr
      hAB s hs) ha hℓ

theorem mellinProfile_eq_positive_squaredContour {ε ℓ : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : a₀ε ε ≤ Aε ε) {P : ℂ → ℂ} (hP : IsSaddlePolynomial ε P) (c : ℝ) (r a : ℝ)
    (hr : 0 < r) (ha : 0 < a) :
    mellinProfile ε ℓ P c r = saddleSquaredContour (mellinData ε ℓ P) a (r ^ 2) := by
  rw [mellinProfile_eq_positive_contour hε hℓ horder hP c hr ha,
    saddleSquaredContour_eq (mellinData ε ℓ P) a hr]

/-! ### Derivatives of the contour moment far from the origin -/

theorem saddlePositiveCpow_norm_le_one_of_nonpos {z : ℂ} (hz : z.re ≤ 0) {u : ℝ}
    (hu : u ∈ Ioi (1 : ℝ)) : ‖saddlePositiveCpow z u‖ ≤ 1 := by
  have hu1 : (1 : ℝ) ≤ u := (mem_Ioi.mp hu).le
  have hupos : (0 : ℝ) < u := zero_lt_one.trans_le hu1
  unfold saddlePositiveCpow
  rw [max_eq_left hupos.le, Complex.norm_cpow_eq_rpow_re_of_pos hupos]
  exact Real.rpow_le_one_of_one_le_of_nonpos hu1 hz

theorem saddlePositiveContourMoment_hasDerivAt_of_positiveContour {D : ℝ → ℂ}
    (hD : ∀ k : ℕ, Integrable fun t : ℝ ↦ (t : ℂ) ^ k * D t) {a : ℝ} (ha : 0 < a) (j : ℕ)
    {u : ℝ} (hu : u ∈ Ioi (1 : ℝ)) :
    HasDerivAt (saddlePositiveContourMoment a j D)
      (saddlePositiveContourMoment a (j + 1) D u) u := by
  have hnonpos (k : ℕ) (t : ℝ) : (saddleContourExponent a t - (k : ℂ)).re ≤ 0 := by
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [saddleContourExponent_sub_nat_re]
    linarith
  have hne (t : ℝ) : saddleContourExponent a t - (j : ℂ) ≠ 0 := by
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hneg : (saddleContourExponent a t - (j : ℂ)).re < 0 := by
      rw [saddleContourExponent_sub_nat_re]; linarith
    exact ne_of_apply_ne Complex.re (by simpa using hneg.ne)
  exact saddlePositiveContourMoment_hasDerivAt_of_bounds hD isOpen_Ioi j
    (fun k _ v hv ↦ saddlePositiveCpow_comp_continuous
      (Or.inl (zero_lt_one.trans (mem_Ioi.mp hv))))
    (fun k _ v hv t ↦ saddlePositiveCpow_norm_le_one_of_nonpos (hnonpos k t) hv)
    (fun t v hv ↦ saddlePositiveCpow_hasDerivAt_of_pos (hne t)
      (zero_lt_one.trans (mem_Ioi.mp hv))) hu

theorem saddlePositiveContourMoment_contDiffOn_infty_of_positiveContour {D : ℝ → ℂ}
    (hD : ∀ k : ℕ, Integrable fun t : ℝ ↦ (t : ℂ) ^ k * D t) {a : ℝ} (ha : 0 < a) (j : ℕ) :
    ContDiffOn ℝ ∞ (saddlePositiveContourMoment a j D) (Ioi (1 : ℝ)) :=
  contDiffOn_infty.2 fun n ↦ contDiffOn_of_hasDerivAt_range
    (F := fun k ↦ saddlePositiveContourMoment a k D) isOpen_Ioi n j
    fun k _ _v hv ↦ saddlePositiveContourMoment_hasDerivAt_of_positiveContour hD ha (j + k) hv

theorem saddlePositiveContourMoment_iteratedDeriv_of_positiveContour {D : ℝ → ℂ}
    (hD : ∀ k : ℕ, Integrable fun t : ℝ ↦ (t : ℂ) ^ k * D t) {a : ℝ} (ha : 0 < a) (n j : ℕ)
    {u : ℝ} (hu : u ∈ Ioi (1 : ℝ)) :
    iteratedDeriv n (saddlePositiveContourMoment a j D) u =
      saddlePositiveContourMoment a (j + n) D u := by
  induction n generalizing j u with
  | zero => simp
  | succ n ih =>
      have hevent : deriv (saddlePositiveContourMoment a j D) =ᶠ[𝓝 u]
          saddlePositiveContourMoment a (j + 1) D := by
        filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
        exact (saddlePositiveContourMoment_hasDerivAt_of_positiveContour hD ha j hv).deriv
      rw [iteratedDeriv_succ', hevent.iteratedDeriv_eq n]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (j + 1) hu

/-- The `L¹` norm of the weighted contour data, controlling the size of the moments. -/
def saddleContourMomentL1 (a : ℝ) (j : ℕ) (D : ℝ → ℂ) : ℝ :=
  ∫ t : ℝ, ‖(saddleContourFallingPolynomial a j).eval (t : ℂ) * D t‖

theorem saddlePositiveContourMoment_norm_le {D : ℝ → ℂ}
    (hD : ∀ k : ℕ, Integrable fun t : ℝ ↦ (t : ℂ) ^ k * D t) (a : ℝ) (j : ℕ) {u : ℝ}
    (hu : 0 < u) :
    ‖saddlePositiveContourMoment a j D u‖ ≤
      u ^ (-a / 2 - (j : ℝ)) * saddleContourMomentL1 a j D := by
  have hW : Integrable fun t : ℝ ↦ (saddleContourFallingPolynomial a j).eval (t : ℂ) * D t :=
    saddlePolynomialWeightedData_integrable hD _
  have hpoint (t : ℝ) : ‖saddlePositiveCpow (saddleContourExponent a t - (j : ℂ)) u *
      ((saddleContourFallingPolynomial a j).eval (t : ℂ) * D t)‖ =
      u ^ (-a / 2 - (j : ℝ)) * ‖(saddleContourFallingPolynomial a j).eval (t : ℂ) * D t‖ := by
    rw [norm_mul]
    congr 1
    unfold saddlePositiveCpow
    rw [max_eq_left hu.le, Complex.norm_cpow_eq_rpow_re_of_pos hu,
      saddleContourExponent_sub_nat_re]
  unfold saddlePositiveContourMoment saddleContourMomentL1
  calc ‖∫ t : ℝ, saddlePositiveCpow (saddleContourExponent a t - (j : ℂ)) u *
        ((saddleContourFallingPolynomial a j).eval (t : ℂ) * D t)‖
      ≤ ∫ t : ℝ, ‖saddlePositiveCpow (saddleContourExponent a t - (j : ℂ)) u *
          ((saddleContourFallingPolynomial a j).eval (t : ℂ) * D t)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ t : ℝ, u ^ (-a / 2 - (j : ℝ)) *
          ‖(saddleContourFallingPolynomial a j).eval (t : ℂ) * D t‖ :=
        integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = _ := integral_const_mul_of_integrable hW.norm

theorem saddleSquaredContour_contDiffOn_of_pos {M : ℂ → ℂ} {a : ℝ} (ha : 0 < a)
    (hM : ∀ k : ℕ, Integrable fun t : ℝ ↦ (t : ℂ) ^ k * M ((a : ℂ) + (t : ℂ) * I)) :
    ContDiffOn ℝ ∞ (saddleSquaredContour M a) (Ioi (1 : ℝ)) :=
  contDiff_const.contDiffOn.mul
    (saddlePositiveContourMoment_contDiffOn_infty_of_positiveContour hM ha 0)

theorem saddleSquaredContour_eq_of_pos {M : ℂ → ℂ} {f : ℝ → ℂ}
    (hprof : ∀ r a : ℝ, 0 < r → 0 < a → f r = saddleSquaredContour M a (r ^ 2))
    {a b u : ℝ} (ha : 0 < a) (hb : 0 < b) (hu : 0 < u) :
    saddleSquaredContour M a u = saddleSquaredContour M b u := by
  have hroot : 0 < √u := Real.sqrt_pos.2 hu
  have hsq : √u ^ 2 = u := Real.sq_sqrt hu.le
  calc saddleSquaredContour M a u = saddleSquaredContour M a (√u ^ 2) := by rw [hsq]
    _ = f (√u) := (hprof _ a hroot ha).symm
    _ = saddleSquaredContour M b (√u ^ 2) := hprof _ b hroot hb
    _ = saddleSquaredContour M b u := by rw [hsq]

/-! ### The Schwartz tail -/

/-- A smooth cutoff vanishing for `u ≤ 2` and equal to `1` for `u ≥ 3`. -/
def saddleOuterCutoff (u : ℝ) : ℂ := (Real.smoothTransition (u - 2) : ℂ)

theorem saddleOuterCutoff_contDiff : ContDiff ℝ ∞ saddleOuterCutoff :=
  Complex.ofRealCLM.contDiff.comp
    (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))

/-- The profile on the line `Re z = 2`, cut off near the origin: a Schwartz function of `u = r²`
which agrees with the profile for `u > 3`. -/
def saddleOuterSquaredProfile (M : ℂ → ℂ) (u : ℝ) : ℂ :=
  saddleOuterCutoff u * saddleSquaredContour M 2 u

theorem saddleOuterSquaredProfile_eq_zero (M : ℂ → ℂ) {u : ℝ} (hu : u < 2) :
    saddleOuterSquaredProfile M u = 0 := by
  have hcut : Real.smoothTransition (u - 2) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  simp [saddleOuterSquaredProfile, saddleOuterCutoff, hcut]

theorem saddleOuterSquaredProfile_eq_squaredContour {M : ℂ → ℂ} {f : ℝ → ℂ}
    (hprof : ∀ r a : ℝ, 0 < r → 0 < a → f r = saddleSquaredContour M a (r ^ 2))
    {a u : ℝ} (ha : 0 < a) (hu : 3 < u) :
    saddleOuterSquaredProfile M u = saddleSquaredContour M a u := by
  have hcut : Real.smoothTransition (u - 2) = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  unfold saddleOuterSquaredProfile saddleOuterCutoff
  rw [hcut, Complex.ofReal_one, one_mul]
  exact saddleSquaredContour_eq_of_pos hprof two_pos ha (by linarith)

theorem saddleOuterSquaredProfile_contDiff {M : ℂ → ℂ}
    (hM : ∀ k : ℕ, Integrable fun t : ℝ ↦ (t : ℂ) ^ k * M (((2 : ℝ) : ℂ) + (t : ℂ) * I)) :
    ContDiff ℝ ∞ (saddleOuterSquaredProfile M) := by
  refine contDiff_iff_contDiffAt.2 fun u ↦ ?_
  by_cases hu : u < 2
  · have hevent : saddleOuterSquaredProfile M =ᶠ[𝓝 u] fun _ : ℝ ↦ (0 : ℂ) := by
      filter_upwards [Iio_mem_nhds hu] with v hv
      exact saddleOuterSquaredProfile_eq_zero M (mem_Iio.mp hv)
    exact contDiffAt_const.congr_of_eventuallyEq hevent
  · exact saddleOuterCutoff_contDiff.contDiffAt.mul
      ((saddleSquaredContour_contDiffOn_of_pos (a := (2 : ℝ)) two_pos hM).contDiffAt
        (isOpen_Ioi.mem_nhds (show (1 : ℝ) < u by linarith [not_lt.mp hu])))

theorem saddleOuterSquaredProfile_schwartz_decay {G : ℝ → ℂ} {a : ℝ} {D : ℝ → ℂ} {k n : ℕ}
    (hG : ContDiff ℝ ∞ G) (hzero : ∀ u : ℝ, u < 2 → G u = 0) (ha : 0 < a)
    (hD : ∀ j : ℕ, Integrable fun t : ℝ ↦ (t : ℂ) ^ j * D t)
    (htail : ∀ u : ℝ, 3 < u → G u = (2 * π : ℂ)⁻¹ *
      saddlePositiveContourMoment a 0 D u) (hak : (k : ℝ) ≤ a / 2) :
    ∃ C : ℝ, ∀ u : ℝ, ‖u‖ ^ k * ‖iteratedFDeriv ℝ n G u‖ ≤ C := by
  set c : ℂ := (2 * π : ℂ)⁻¹
  set L : ℝ := saddleContourMomentL1 a n D with hLdef
  have hLnn : 0 ≤ L := by
    rw [hLdef, saddleContourMomentL1]
    exact integral_nonneg fun _ ↦ norm_nonneg _
  have hcont : Continuous fun u : ℝ ↦ ‖u‖ ^ k * ‖iteratedFDeriv ℝ n G u‖ := by
    refine Continuous.mul (by fun_prop) ?_
    exact (hG.of_le (mod_cast le_top)).continuous_iteratedFDeriv'.norm
  obtain ⟨B, hB⟩ : BddAbove ((fun u : ℝ ↦ ‖u‖ ^ k * ‖iteratedFDeriv ℝ n G u‖) '' Icc (2 : ℝ) 4) :=
    isCompact_Icc.bddAbove_image hcont.continuousOn
  refine ⟨max 0 (max B (‖c‖ * L)), fun u ↦ ?_⟩
  by_cases hlow : u < 2
  · have hevent : G =ᶠ[𝓝 u] fun _ : ℝ ↦ (0 : ℂ) := by
      filter_upwards [Iio_mem_nhds hlow] with v hv
      exact hzero v (mem_Iio.mp hv)
    rw [(hevent.iteratedFDeriv ℝ n).eq_of_nhds]
    simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero] using
      le_max_left (0 : ℝ) (max B (‖c‖ * L))
  · by_cases hupper : u ≤ 4
    · exact (hB ⟨u, ⟨not_lt.mp hlow, hupper⟩, rfl⟩).trans
        ((le_max_left B (‖c‖ * L)).trans (le_max_right 0 _))
    · have hu4 : (4 : ℝ) < u := not_le.mp hupper
      have hu0 : (0 : ℝ) < u := by linarith
      have hu1 : (1 : ℝ) < u := by linarith
      have hevent : G =ᶠ[𝓝 u] fun v : ℝ ↦ c * saddlePositiveContourMoment a 0 D v := by
        filter_upwards [Ioi_mem_nhds (show (3 : ℝ) < u by linarith)] with v hv
        exact htail v (mem_Ioi.mp hv)
      have hiter : iteratedDeriv n G u = c * saddlePositiveContourMoment a n D u := by
        rw [hevent.iteratedDeriv_eq n, iteratedDeriv_const_mul_field,
          saddlePositiveContourMoment_iteratedDeriv_of_positiveContour hD ha n 0
            (mem_Ioi.mpr hu1)]
        simp
      have hcancel : u ^ k * u ^ (-(k : ℝ)) = 1 := by
        rw [Real.rpow_neg hu0.le, Real.rpow_natCast]
        exact mul_inv_cancel₀ (pow_ne_zero _ hu0.ne')
      refine le_trans ?_ ((le_max_right B (‖c‖ * L)).trans (le_max_right 0 _))
      calc ‖u‖ ^ k * ‖iteratedFDeriv ℝ n G u‖
          = u ^ k * (‖c‖ * ‖saddlePositiveContourMoment a n D u‖) := by
            rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hiter, norm_mul,
              Real.norm_of_nonneg hu0.le]
        _ ≤ u ^ k * (‖c‖ * (u ^ (-a / 2 - (n : ℝ)) * L)) := by
            gcongr
            exact saddlePositiveContourMoment_norm_le hD a n hu0
        _ ≤ u ^ k * (‖c‖ * (u ^ (-(k : ℝ)) * L)) := by
            gcongr
            · exact hu1.le
            · have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
              linarith
        _ = u ^ k * u ^ (-(k : ℝ)) * (‖c‖ * L) := by ring
        _ = ‖c‖ * L := by rw [hcancel, one_mul]

theorem saddleOuterSquaredProfile_decay {M : ℂ → ℂ} {f : ℝ → ℂ}
    (hmom : ∀ a : ℝ, 0 < a → ∀ j : ℕ,
      Integrable fun t : ℝ ↦ (t : ℂ) ^ j * M ((a : ℂ) + (t : ℂ) * I))
    (hprof : ∀ r a : ℝ, 0 < r → 0 < a → f r = saddleSquaredContour M a (r ^ 2)) (k n : ℕ) :
    ∃ C : ℝ, ∀ u : ℝ, ‖u‖ ^ k * ‖iteratedFDeriv ℝ n (saddleOuterSquaredProfile M) u‖ ≤ C := by
  have ha : (0 : ℝ) < 2 * ((k : ℝ) + 1) := by positivity
  exact saddleOuterSquaredProfile_schwartz_decay
    (saddleOuterSquaredProfile_contDiff (hmom 2 two_pos))
    (fun u hu ↦ saddleOuterSquaredProfile_eq_zero M hu) ha (hmom _ ha)
    (fun u hu ↦ saddleOuterSquaredProfile_eq_squaredContour hprof ha hu) (by linarith)

/-- Pullback of a scalar Schwartz function along `x ↦ ‖x‖²`. -/
def saddleSquaredSchwartzPullback (d : ℕ) : 𝓢(ℝ, ℂ) →L[ℂ] TestFunction d := by
  apply SchwartzMap.compCLM ℂ (Function.hasTemperateGrowth_norm_sq (Euclidean d))
  refine ⟨1, 1, fun x ↦ ?_⟩
  change ‖x‖ ≤ 1 * (1 + ‖‖x‖ ^ 2‖) ^ 1
  rw [one_mul, pow_one, Real.norm_of_nonneg (sq_nonneg _)]
  nlinarith [sq_nonneg (‖x‖ - 1 / 2)]

/-- The Schwartz tail of the radial profile: `χ(‖x‖²)` times the profile on the line
`Re z = 2`. -/
def saddleOuterSchwartz {M : ℂ → ℂ} {f : ℝ → ℂ}
    (hmom : ∀ a : ℝ, 0 < a → ∀ j : ℕ,
      Integrable fun t : ℝ ↦ (t : ℂ) ^ j * M ((a : ℂ) + (t : ℂ) * I))
    (hprof : ∀ r a : ℝ, 0 < r → 0 < a → f r = saddleSquaredContour M a (r ^ 2)) (d : ℕ) :
    TestFunction d :=
  saddleSquaredSchwartzPullback d
    { toFun := saddleOuterSquaredProfile M
      smooth' := saddleOuterSquaredProfile_contDiff (hmom 2 two_pos)
      decay' := saddleOuterSquaredProfile_decay hmom hprof }

theorem saddleOuterDifference_hasCompactSupport {M : ℂ → ℂ} {f : ℝ → ℂ}
    (hmom : ∀ a : ℝ, 0 < a → ∀ j : ℕ,
      Integrable fun t : ℝ ↦ (t : ℂ) ^ j * M ((a : ℂ) + (t : ℂ) * I))
    (hprof : ∀ r a : ℝ, 0 < r → 0 < a → f r = saddleSquaredContour M a (r ^ 2)) (d : ℕ) :
    HasCompactSupport fun x : Euclidean d ↦ f ‖x‖ - saddleOuterSchwartz hmom hprof d x := by
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Euclidean d) 2) fun x hx ↦ ?_
  by_contra houtside
  have hr2 : (2 : ℝ) < ‖x‖ := lt_of_not_ge fun h ↦ houtside (mem_closedBall_zero_iff.mpr h)
  have hsq : (3 : ℝ) < ‖x‖ ^ 2 := by nlinarith
  have houter : saddleOuterSchwartz hmom hprof d x = saddleSquaredContour M 2 (‖x‖ ^ 2) :=
    saddleOuterSquaredProfile_eq_squaredContour hprof two_pos hsq
  change f ‖x‖ - saddleOuterSchwartz hmom hprof d x ≠ 0 at hx
  exact hx (by rw [houter, hprof ‖x‖ 2 (by linarith) two_pos, sub_self])

/-- A smooth function agreeing with a Schwartz function outside a compact set is Schwartz. -/
theorem schwartz_decay_of_hasCompactSupport {d : ℕ} {F : Euclidean d → ℂ} (tail : TestFunction d)
    (hsmooth : ContDiff ℝ ∞ F)
    (hcompact : HasCompactSupport fun x : Euclidean d ↦ F x - tail x) (k n : ℕ) :
    ∃ C : ℝ, ∀ x : Euclidean d, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n F x‖ ≤ C := by
  have hdiff : ContDiff ℝ ∞ fun x : Euclidean d ↦ F x - tail x := hsmooth.sub (tail.smooth ⊤)
  have hfun : F = fun x : Euclidean d ↦ (tail + hcompact.toSchwartzMap hdiff) x := by
    funext x
    change F x = tail x + (F x - tail x)
    ring
  rw [hfun]
  exact (tail + hcompact.toSchwartzMap hdiff).decay' k n

/-- Report Lemma 4.3: `x ↦ f_P(‖x‖)` is a Schwartz function on `ℝᵈ` for every saddle polynomial
`P`, when `f_P(0)` is the residue at `z = 0`. -/
def mellinProfileSchwartz {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d) (horder : a₀ε ε ≤ Aε ε)
    {P : ℂ → ℂ} (hP : IsSaddlePolynomial ε P) {c : ℝ}
    (hc : (c : ℂ) = poleResidue ε (d / 2 : ℝ) P 0) : TestFunction d where
  toFun := mellinProfileFun ε d P c
  smooth' := mellinProfileFun_contDiff hε hd horder hP hc
  decay' := by
    have hℓ : (0 : ℝ) < (d : ℝ) / 2 := dimension_half_pos hd
    have hmom : ∀ a : ℝ, 0 < a → ∀ j : ℕ, Integrable fun t : ℝ ↦
        (t : ℂ) ^ j * mellinData ε ((d : ℝ) / 2) P ((a : ℂ) + (t : ℂ) * I) :=
      fun a ha j ↦ mellinData_shiftedLine_moment_integrable hε hℓ horder hP
        (saddlePositiveContour_ne_pole ha) j
    have hprof := mellinProfile_eq_positive_squaredContour hε hℓ horder hP c
    intro k n
    exact schwartz_decay_of_hasCompactSupport (saddleOuterSchwartz hmom hprof d)
      (mellinProfileFun_contDiff hε hd horder hP hc)
      (saddleOuterDifference_hasCompactSupport hmom hprof d) k n

@[simp] theorem mellinProfileSchwartz_apply {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : a₀ε ε ≤ Aε ε) {P : ℂ → ℂ} (hP : IsSaddlePolynomial ε P) {c : ℝ}
    (hc : (c : ℂ) = poleResidue ε (d / 2 : ℝ) P 0) (x : Euclidean d) :
    mellinProfileSchwartz hε hd horder hP hc x = mellinProfileFun ε d P c x := rfl

/-- Report Lemma 4.3: `f₊` is a Schwartz function on `ℝᵈ`. -/
def plusSaddleSchwartz {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d) (horder : a₀ε ε ≤ Aε ε) :
    TestFunction d :=
  mellinProfileSchwartz hε hd horder (isSaddlePolynomial_PPlus ε)
    (poleResidue_PPlus_zero (dimension_half_pos hd)).symm

/-- Report Lemma 4.3: `f₋` is a Schwartz function on `ℝᵈ`. -/
def minusSaddleSchwartz {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d) (horder : a₀ε ε ≤ Aε ε) :
    TestFunction d :=
  mellinProfileSchwartz hε hd horder (isSaddlePolynomial_PMinus ε)
    (poleResidue_PMinus_zero (dimension_half_pos hd)).symm

theorem plusSaddleSchwartz_apply {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : a₀ε ε ≤ Aε ε) (x : Euclidean d) :
    plusSaddleSchwartz hε hd horder x = fPlusFun ε d x :=
  rfl

theorem minusSaddleSchwartz_apply {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : a₀ε ε ≤ Aε ε) (x : Euclidean d) :
    minusSaddleSchwartz hε hd horder x = fMinusFun ε d x :=
  rfl

end

end CohnElkies
