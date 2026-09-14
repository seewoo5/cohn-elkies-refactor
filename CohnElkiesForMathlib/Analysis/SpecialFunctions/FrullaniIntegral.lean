import Mathlib

/-!
# Exponential Frullani integrals and the Wallis product as a Laplace integral

* The Laplace integrals `∫₀^∞ e^{-ax} dx = a⁻¹` (`a > 0`) and `∫₀^∞ e^{-zx} dx = z⁻¹` (`Re z > 0`).
* The Frullani formula for exponentials, `∫₀^∞ (e^{-ax} - e^{-bx}) / x dx = log (b / a)`
  (`Frullani.integral_expKernel`), and its complex version
  `∫₀^∞ (e^{-zx} - e^{-wx}) / x dx = log w - log z` for `Re z, Re w > 0`
  (`Frullani.integral_cexpKernel`), obtained by writing the kernel as an integral of Laplace
  kernels over the segment from `z` to `w`.
* Integrating the complex Frullani kernel with parameters `z + s`, `1` over `s ∈ [0, 1]` gives
  `∫₀^∞ ((1 - e^{-x}) e^{-zx} - x e^{-x}) / x² dx = 1 + z log z - (z + 1) log (z + 1)`
  (`Frullani.integral_shiftedCexpKernel`).
* The Wallis product as a Laplace-type integral:
  `∫₀^∞ e^{-x} (1 - e^{-x}) / (x (1 + e^{-x})) dx = log (π / 2)`
  (`Real.Wallis.integral_laplaceKernel`), by telescoping the Wallis partial products through
  Frullani integrals.
-/

open Filter MeasureTheory Real Set
open scoped Topology

noncomputable section

/-- The Laplace kernel `x ↦ e^{-ax}` is integrable on `(0, ∞)` for `a > 0`. -/
theorem integrableOn_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ exp (-a * x)) (Ioi 0) :=
  integrableOn_exp_mul_Ioi (by linarith : -a < 0) 0

/-- `∫₀^∞ e^{-ax} dx = a⁻¹` for `a > 0`. -/
theorem integral_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) : (∫ x : ℝ in Ioi 0, exp (-a * x)) = a⁻¹ := by
  simpa using integral_exp_mul_Ioi (by linarith : -a < 0) 0

/-- The Laplace kernel `x ↦ e ^ (-zx)` is integrable on `(0, ∞)` for `Re z > 0`. -/
theorem integrableOn_cexp_neg_mul_Ioi {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun x : ℝ ↦ Complex.exp (-z * (x : ℂ))) (Ioi 0) := by
  simpa only [neg_mul] using integrableOn_exp_mul_complex_Ioi (a := -z) (by simpa using hz) 0

/-- `∫₀^∞ e ^ (-zx) dx = z⁻¹` for `Re z > 0`. -/
theorem integral_cexp_neg_mul_Ioi {z : ℂ} (hz : 0 < z.re) :
    (∫ x : ℝ in Ioi 0, Complex.exp (-z * (x : ℂ))) = z⁻¹ := by
  simpa [div_eq_mul_inv] using integral_exp_mul_complex_Ioi (a := -z) (by simpa using hz) 0

theorem Complex.norm_exp_neg_mul_ofReal (z : ℂ) (x : ℝ) :
    ‖Complex.exp (-z * (x : ℂ))‖ = Real.exp (-z.re * x) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- The open right half-plane is stable under translation by a nonnegative real. -/
theorem Complex.add_ofReal_re_pos {z : ℂ} (hz : 0 < z.re) {s : ℝ} (hs : 0 ≤ s) :
    0 < (z + (s : ℂ)).re := by
  simp only [Complex.add_re, Complex.ofReal_re]
  linarith

namespace Frullani

/-! ### The exponential Frullani kernel -/

/-- The Frullani kernel `(e^{-ax} - e^{-bx}) / x`. -/
def expKernel (a b x : ℝ) : ℝ := (exp (-a * x) - exp (-b * x)) / x

/-- The Frullani kernel is the `s`-integral of the Laplace kernel over `[a, b]`. -/
theorem intervalIntegral_exp_neg_mul_eq_expKernel {x : ℝ} (hx : x ≠ 0) (a b : ℝ) :
    (∫ s in a..b, exp (-s * x)) = expKernel a b x := by
  have hderiv (s : ℝ) : HasDerivAt (fun u : ℝ ↦ -exp (-u * x) / x) (exp (-s * x)) s := by
    convert! (((Real.hasDerivAt_exp (-s * x)).comp s
      ((hasDerivAt_id s).neg.mul_const x)).neg.div_const x) using 1
    field_simp [hx]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hderiv s)
    ((continuous_exp.comp (continuous_id.neg.mul continuous_const)).intervalIntegrable a b)]
  unfold expKernel
  ring

theorem integrable_exp_neg_mul_prod {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Integrable (Function.uncurry fun s x : ℝ ↦ exp (-s * x))
      ((volume.restrict (uIoc a b)).prod (volume.restrict (Ioi 0))) := by
  have hpos : ∀ s ∈ uIoc a b, 0 < s := fun s hs ↦ by
    rw [uIoc_of_le hab] at hs
    linarith [hs.1]
  refine (integrable_prod_iff (by fun_prop)).2 ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    exact integrableOn_exp_neg_mul_Ioi (hpos s hs)
  · have hinv : Integrable (fun s : ℝ ↦ s⁻¹) (volume.restrict (uIoc a b)) :=
      intervalIntegrable_iff.mp (continuousOn_id.inv₀ fun s hs ↦ by
        rw [uIcc_of_le hab] at hs
        exact (ha.trans_le hs.1).ne').intervalIntegrable
    refine hinv.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    symm
    change (∫ y : ℝ in Ioi 0, ‖exp (-s * y)‖) = s⁻¹
    simpa only [Real.norm_eq_abs, abs_of_pos (exp_pos _)] using integral_exp_neg_mul_Ioi (hpos s hs)

/-- The Frullani formula `∫₀^∞ (e^{-ax} - e^{-bx}) / x dx = log (b / a)`. -/
theorem integral_expKernel {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x : ℝ in Ioi 0, expKernel a b x) = log (b / a) := by
  calc (∫ x : ℝ in Ioi 0, expKernel a b x)
      = ∫ x : ℝ in Ioi 0, ∫ s in a..b, exp (-s * x) :=
        setIntegral_congr_fun measurableSet_Ioi fun x hx ↦
          (intervalIntegral_exp_neg_mul_eq_expKernel hx.ne' a b).symm
    _ = ∫ s in a..b, ∫ x : ℝ in Ioi 0, exp (-s * x) :=
        (intervalIntegral_integral_swap (integrable_exp_neg_mul_prod ha hab)).symm
    _ = ∫ s in a..b, s⁻¹ := intervalIntegral.integral_congr fun s hs ↦ by
        rw [uIcc_of_le hab] at hs
        exact integral_exp_neg_mul_Ioi (ha.trans_le hs.1)
    _ = log (b / a) := integral_inv_of_pos ha (ha.trans_le hab)

theorem integrableOn_expKernel {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (expKernel a b) (Ioi 0) := by
  refine (integrable_exp_neg_mul_prod ha hab).integral_prod_right.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change (∫ s in uIoc a b, exp (-s * x)) = expKernel a b x
  rw [uIoc_of_le hab, ← intervalIntegral.integral_of_le hab]
  exact intervalIntegral_exp_neg_mul_eq_expKernel hx.ne' a b

/-! ### The complex exponential Frullani kernel -/

/-- The segment `s ↦ z + s(w - z)` joining `z` to `w`. -/
def segment (z w : ℂ) (s : ℝ) : ℂ := z + (s : ℂ) * (w - z)

theorem min_re_le_segment_re (z w : ℂ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    min z.re w.re ≤ (segment z w s).re := by
  simp only [segment, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.sub_re, zero_mul, sub_zero]
  have hfirst : 0 ≤ (1 - s) * (z.re - min z.re w.re) :=
    mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr (min_le_left z.re w.re))
  have hsecond : 0 ≤ s * (w.re - min z.re w.re) :=
    mul_nonneg hs.1 (sub_nonneg.mpr (min_le_right z.re w.re))
  nlinarith

theorem segment_re_pos {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : 0 < (segment z w s).re :=
  (lt_min hz hw).trans_le (min_re_le_segment_re z w hs)

/-- The Frullani kernel `x ↦ (e ^ (-zx) - e ^ (-wx)) / x`. -/
def cexpKernel (z w : ℂ) (x : ℝ) : ℂ := (Complex.exp (-z * (x : ℂ)) -
    Complex.exp (-w * (x : ℂ))) / (x : ℂ)

theorem hasDerivAt_segment (z w : ℂ) (s : ℝ) :
    HasDerivAt (segment z w) (w - z) s := by
  have hcomplex : HasDerivAt (fun q : ℂ ↦ z + q * (w - z)) (w - z) (s : ℂ) := by
    convert! (hasDerivAt_const (s : ℂ) z).add ((hasDerivAt_id (s : ℂ)).mul_const (w - z)) using 1
    all_goals simp
  exact hcomplex.comp_ofReal

theorem intervalIntegral_cexp_segment (z w : ℂ) {x : ℝ} (hx : x ≠ 0) :
    (∫ s in (0 : ℝ)..1, (w - z) * Complex.exp (-segment z w s * (x : ℂ))) =
      cexpKernel z w x := by
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  have hderiv (s : ℝ) : HasDerivAt (fun r : ℝ ↦
      -Complex.exp (-segment z w r * (x : ℂ)) / (x : ℂ))
      ((w - z) * Complex.exp (-segment z w s * (x : ℂ))) s := by
    convert! (((hasDerivAt_segment z w s).neg.mul_const
      (x : ℂ)).cexp.neg.div_const (x : ℂ)) using 1
    simp only [Pi.neg_apply]
    field_simp
  have hcont : Continuous fun s : ℝ ↦
      (w - z) * Complex.exp (-segment z w s * (x : ℂ)) := by
    unfold segment
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hderiv s)
    (hcont.intervalIntegrable 0 1)]
  unfold segment cexpKernel
  push_cast
  simp only [zero_mul, one_mul, add_zero]
  ring_nf

theorem norm_cexpKernel_le (z w : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖cexpKernel z w x‖ ≤ ‖w - z‖ * exp (-min z.re w.re * x) := by
  rw [← intervalIntegral_cexp_segment z w hx.ne']
  have hbound : ‖∫ s in (0 : ℝ)..1,
        (w - z) * Complex.exp (-segment z w s * (x : ℂ))‖ ≤
      ‖w - z‖ * exp (-min z.re w.re * x) * |(1 : ℝ) - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs ↦ ?_
    rw [Set.uIoc_of_le zero_le_one] at hs
    rw [norm_mul, Complex.norm_exp_neg_mul_ofReal]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    nlinarith [min_re_le_segment_re z w ⟨hs.1.le, hs.2⟩]
  simpa using hbound

theorem integral_norm_cexp_segment {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ x : ℝ in Ioi 0, ‖(w - z) * Complex.exp (-segment z w s * (x : ℂ))‖) =
      ‖w - z‖ * (segment z w s).re⁻¹ := by
  rw [setIntegral_congr_fun measurableSet_Ioi
      (g := fun x : ℝ ↦ ‖w - z‖ * exp (-(segment z w s).re * x))
      fun x _ ↦ by simp only [norm_mul, Complex.norm_exp_neg_mul_ofReal],
    integral_const_mul, integral_exp_neg_mul_Ioi (segment_re_pos hz hw hs)]

theorem integrable_cexp_segment_prod {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    Integrable (Function.uncurry fun s x : ℝ ↦
        (w - z) * Complex.exp (-segment z w s * (x : ℂ)))
      ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod (volume.restrict (Ioi 0))) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry fun s x : ℝ ↦
      (w - z) * Complex.exp (-segment z w s * (x : ℂ)))
      ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod (volume.restrict (Ioi 0))) := by
    unfold segment
    fun_prop
  have hseg : Continuous fun s : ℝ ↦ (segment z w s).re := by
    unfold segment
    fun_prop
  refine (integrable_prod_iff hmeas).2 ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [Set.uIoc_of_le zero_le_one] at hs
    exact (integrableOn_cexp_neg_mul_Ioi
      (segment_re_pos hz hw ⟨hs.1.le, hs.2⟩)).const_mul (w - z)
  · have hcont : ContinuousOn (fun s : ℝ ↦ ‖w - z‖ * (segment z w s).re⁻¹)
        (Set.uIcc (0 : ℝ) 1) :=
      continuousOn_const.mul (hseg.continuousOn.inv₀ fun s hs ↦
        (segment_re_pos hz hw (by rwa [Set.uIcc_of_le zero_le_one] at hs)).ne')
    refine (intervalIntegrable_iff.mp hcont.intervalIntegrable).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [Set.uIoc_of_le zero_le_one] at hs
    exact (integral_norm_cexp_segment hz hw ⟨hs.1.le, hs.2⟩).symm

theorem integrableOn_cexpKernel {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    IntegrableOn (cexpKernel z w) (Ioi 0) := by
  refine (integrable_cexp_segment_prod hz hw).integral_prod_right.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Set.uIoc_of_le zero_le_one, ← intervalIntegral.integral_of_le zero_le_one]
  exact intervalIntegral_cexp_segment z w (ne_of_gt hx)

theorem intervalIntegral_segment_inv {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    (∫ s in (0 : ℝ)..1, (w - z) * (segment z w s)⁻¹) =
      Complex.log w - Complex.log z := by
  have hseg : Continuous (segment z w) := by
    unfold segment
    fun_prop
  have hslit : ∀ s ∈ Set.uIcc (0 : ℝ) 1, segment z w s ∈ Complex.slitPlane :=
    fun s hs ↦ Complex.mem_slitPlane_iff.mpr (Or.inl (segment_re_pos hz hw
      (by rwa [Set.uIcc_of_le zero_le_one] at hs)))
  have hcont : ContinuousOn (fun s : ℝ ↦ (w - z) * (segment z w s)⁻¹)
      (Set.uIcc (0 : ℝ) 1) :=
    continuousOn_const.mul (hseg.continuousOn.inv₀ fun s hs ↦
      Complex.slitPlane_ne_zero (hslit s hs))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun r : ℝ ↦ Complex.log (segment z w r)) (fun s hs ↦ by
      simpa [div_eq_mul_inv] using
        (hasDerivAt_segment z w s).clog_real (hslit s hs))
    hcont.intervalIntegrable]
  simp [segment]

/-- The complex Frullani formula `∫₀^∞ (e^{-zx} - e^{-wx}) / x dx = log w - log z`. -/
theorem integral_cexpKernel {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    (∫ x : ℝ in Ioi 0, cexpKernel z w x) = Complex.log w - Complex.log z := by
  calc (∫ x : ℝ in Ioi 0, cexpKernel z w x)
      = ∫ x : ℝ in Ioi 0, ∫ s in (0 : ℝ)..1,
          (w - z) * Complex.exp (-segment z w s * (x : ℂ)) :=
        setIntegral_congr_fun measurableSet_Ioi fun x hx ↦
          (intervalIntegral_cexp_segment z w (ne_of_gt hx)).symm
    _ = ∫ s in (0 : ℝ)..1, ∫ x : ℝ in Ioi 0,
          (w - z) * Complex.exp (-segment z w s * (x : ℂ)) :=
        (intervalIntegral_integral_swap (integrable_cexp_segment_prod hz hw)).symm
    _ = ∫ s in (0 : ℝ)..1, (w - z) * (segment z w s)⁻¹ :=
        intervalIntegral.integral_congr fun s hs ↦ by
          rw [Set.uIcc_of_le zero_le_one] at hs
          simp only [integral_const_mul,
            integral_cexp_neg_mul_Ioi (segment_re_pos hz hw hs)]
    _ = Complex.log w - Complex.log z := intervalIntegral_segment_inv hz hw

/-! ### The shifted kernel `((1 - e^{-x}) e^{-zx} - x e^{-x}) / x²` -/

theorem norm_cexpKernel_add_ofReal_le (z : ℂ) {s x : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hx : 0 < x) :
    ‖cexpKernel (z + (s : ℂ)) 1 x‖ ≤ (‖(1 : ℂ) - z‖ + 1) * exp (-min z.re 1 * x) := by
  have hnorm : ‖(1 : ℂ) - (z + (s : ℂ))‖ ≤ ‖(1 : ℂ) - z‖ + 1 := by
    calc ‖(1 : ℂ) - (z + (s : ℂ))‖ = ‖((1 : ℂ) - z) - (s : ℂ)‖ := by congr 1; ring
      _ ≤ ‖(1 : ℂ) - z‖ + ‖(s : ℂ)‖ := norm_sub_le _ _
      _ ≤ ‖(1 : ℂ) - z‖ + 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
          linarith [hs.2]
  have hmin : min z.re 1 ≤ min (z + (s : ℂ)).re (1 : ℂ).re := by
    refine le_min ?_ (min_le_right z.re 1)
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith [min_le_left z.re (1 : ℝ), hs.1]
  calc ‖cexpKernel (z + (s : ℂ)) 1 x‖
      ≤ ‖(1 : ℂ) - (z + (s : ℂ))‖ * exp (-min (z + (s : ℂ)).re (1 : ℂ).re * x) :=
        norm_cexpKernel_le (z + (s : ℂ)) 1 hx
    _ ≤ (‖(1 : ℂ) - z‖ + 1) * exp (-min (z + (s : ℂ)).re (1 : ℂ).re * x) :=
        mul_le_mul_of_nonneg_right hnorm (Real.exp_pos _).le
    _ ≤ (‖(1 : ℂ) - z‖ + 1) * exp (-min z.re 1 * x) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) (by positivity)

theorem integrable_cexpKernel_add_ofReal_prod {z : ℂ} (hz : 0 < z.re) :
    Integrable (Function.uncurry fun s x : ℝ ↦ cexpKernel (z + (s : ℂ)) 1 x)
      ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod (volume.restrict (Ioi 0))) := by
  have hm : 0 < min z.re 1 := lt_min hz one_pos
  have hmeas : AEStronglyMeasurable (Function.uncurry fun s x : ℝ ↦
      cexpKernel (z + (s : ℂ)) 1 x)
      ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod (volume.restrict (Ioi 0))) := by
    change AEStronglyMeasurable (fun p : ℝ × ℝ ↦
        (Complex.exp (-(z + (p.1 : ℂ)) * (p.2 : ℂ)) - Complex.exp (-(1 : ℂ) * (p.2 : ℂ))) /
          (p.2 : ℂ)) _
    apply Measurable.aestronglyMeasurable
    fun_prop
  refine (integrable_prod_iff hmeas).2 ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [Set.uIoc_of_le zero_le_one] at hs
    change IntegrableOn (cexpKernel (z + (s : ℂ)) 1) (Ioi 0)
    exact integrableOn_cexpKernel (Complex.add_ofReal_re_pos hz hs.1.le)
      (by norm_num : 0 < (1 : ℂ).re)
  · have hconst : Integrable (fun _ : ℝ ↦ (‖(1 : ℂ) - z‖ + 1) * (min z.re 1)⁻¹)
        (volume.restrict (Set.uIoc (0 : ℝ) 1)) :=
      intervalIntegrable_iff.mp (continuous_const.intervalIntegrable (a := (0 : ℝ)) (b := 1))
    refine hconst.mono' (by simpa only [Function.uncurry_apply_pair] using
      hmeas.norm.integral_prod_right') ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [Set.uIoc_of_le zero_le_one] at hs
    change ‖∫ x : ℝ in Ioi 0, ‖cexpKernel (z + (s : ℂ)) 1 x‖‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x ↦ norm_nonneg
      (cexpKernel (z + (s : ℂ)) 1 x))]
    calc (∫ x : ℝ in Ioi 0, ‖cexpKernel (z + (s : ℂ)) 1 x‖)
        ≤ ∫ x : ℝ in Ioi 0, (‖(1 : ℂ) - z‖ + 1) * exp (-min z.re 1 * x) := by
          refine integral_mono_ae (integrableOn_cexpKernel (Complex.add_ofReal_re_pos hz hs.1.le)
            (by norm_num : 0 < (1 : ℂ).re)).norm ((integrableOn_exp_neg_mul_Ioi hm).const_mul _) ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          exact norm_cexpKernel_add_ofReal_le z ⟨hs.1.le, hs.2⟩ hx
      _ = (‖(1 : ℂ) - z‖ + 1) * (min z.re 1)⁻¹ := by
          rw [integral_const_mul, integral_exp_neg_mul_Ioi hm]

/-- The Wallis phase kernel `x ↦ ((1 - e ^ (-x)) e ^ (-zx) - x e ^ (-x)) / x²`. -/
def shiftedCexpKernel (z : ℂ) (x : ℝ) : ℂ := ((1 - Complex.exp (-(x : ℂ))) *
      Complex.exp (-z * (x : ℂ)) -
    (x : ℂ) * Complex.exp (-(x : ℂ))) / (x : ℂ) ^ 2

theorem intervalIntegral_cexpKernel_add_ofReal (z : ℂ) {x : ℝ} (hx : x ≠ 0) :
    (∫ s in (0 : ℝ)..1, cexpKernel (z + (s : ℂ)) 1 x) =
      shiftedCexpKernel z x := by
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  have hfirst : (∫ s in (0 : ℝ)..1, Complex.exp (-(z + (s : ℂ)) * (x : ℂ))) =
      cexpKernel z (z + 1) x := by
    convert! intervalIntegral_cexp_segment z (z + 1) hx using 1
    refine intervalIntegral.integral_congr fun s _ ↦ ?_
    unfold segment
    ring_nf
  have hexponential : Complex.exp (-(z + 1) * (x : ℂ)) =
      Complex.exp (-z * (x : ℂ)) * Complex.exp (-(x : ℂ)) := by
    rw [show -(z + 1) * (x : ℂ) = -z * (x : ℂ) + -(x : ℂ) by ring, Complex.exp_add]
  unfold cexpKernel
  simp only [neg_one_mul]
  have hexpCont : Continuous fun s : ℝ ↦ Complex.exp (-(z + (s : ℂ)) * (x : ℂ)) := by fun_prop
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
      (hexpCont.intervalIntegrable 0 1) (continuous_const.intervalIntegrable 0 1),
    hfirst, intervalIntegral.integral_const]
  unfold cexpKernel shiftedCexpKernel
  simp only [sub_zero, one_smul]
  rw [hexponential]
  field_simp

theorem integrableOn_shiftedCexpKernel {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (shiftedCexpKernel z) (Ioi 0) := by
  refine (integrable_cexpKernel_add_ofReal_prod hz).integral_prod_right.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Set.uIoc_of_le zero_le_one, ← intervalIntegral.integral_of_le zero_le_one]
  exact intervalIntegral_cexpKernel_add_ofReal z hx.ne'

theorem hasDerivAt_mul_log_sub {z : ℂ} (hz : 0 < z.re) (s : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun r : ℝ ↦ (z + (r : ℂ)) * Complex.log (z + (r : ℂ)) - (z + (r : ℂ)))
      (Complex.log (z + (s : ℂ))) s := by
  have hline : HasDerivAt (fun r : ℝ ↦ z + (r : ℂ)) (1 : ℂ) s := by
    have hreal : HasDerivAt (fun r : ℝ ↦ (r : ℂ)) (1 : ℂ) s := by
      simpa using! Complex.ofRealCLM.hasDerivAt
    simpa using! hreal.const_add z
  have hslit : z + (s : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (Complex.add_ofReal_re_pos hz hs.1))
  convert! (hline.mul (hline.clog_real hslit)).sub hline using 1
  simp [div_eq_mul_inv, Complex.slitPlane_ne_zero hslit]

theorem intervalIntegral_log_add_ofReal {z : ℂ} (hz : 0 < z.re) :
    (∫ s in (0 : ℝ)..1, Complex.log (z + (s : ℂ))) =
      (z + 1) * Complex.log (z + 1) - z * Complex.log z - 1 := by
  have hcont : ContinuousOn (fun s : ℝ ↦ Complex.log (z + (s : ℂ))) (Set.uIcc (0 : ℝ) 1) :=
    (by fun_prop : Continuous fun s : ℝ ↦ z + (s : ℂ)).continuousOn.clog fun s hs ↦
      Complex.mem_slitPlane_iff.mpr (Or.inl (Complex.add_ofReal_re_pos hz
        (by rw [Set.uIcc_of_le zero_le_one] at hs; exact hs.1)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs ↦
    hasDerivAt_mul_log_sub hz s (by rwa [Set.uIcc_of_le zero_le_one] at hs))
    hcont.intervalIntegrable]
  push_cast
  simp only [add_zero]
  ring

/-- `∫₀^∞ ((1 - e^{-x}) e^{-zx} - x e^{-x}) / x² dx = 1 + z log z - (z + 1) log (z + 1)`. -/
theorem integral_shiftedCexpKernel {z : ℂ} (hz : 0 < z.re) :
    (∫ x : ℝ in Ioi 0, shiftedCexpKernel z x) = 1 + z * Complex.log z -
        (z + 1) * Complex.log (z + 1) := by
  calc (∫ x : ℝ in Ioi 0, shiftedCexpKernel z x)
      = ∫ x : ℝ in Ioi 0, ∫ s in (0 : ℝ)..1, cexpKernel (z + (s : ℂ)) 1 x :=
        setIntegral_congr_fun measurableSet_Ioi fun x hx ↦
          (intervalIntegral_cexpKernel_add_ofReal z hx.ne').symm
    _ = ∫ s in (0 : ℝ)..1, ∫ x : ℝ in Ioi 0, cexpKernel (z + (s : ℂ)) 1 x :=
        (intervalIntegral_integral_swap (integrable_cexpKernel_add_ofReal_prod hz)).symm
    _ = ∫ s in (0 : ℝ)..1, -Complex.log (z + (s : ℂ)) :=
        intervalIntegral.integral_congr fun s hs ↦ by
          rw [Set.uIcc_of_le zero_le_one] at hs
          simp [integral_cexpKernel (Complex.add_ofReal_re_pos hz hs.1)
            (by norm_num : 0 < (1 : ℂ).re)]
    _ = 1 + z * Complex.log z - (z + 1) * Complex.log (z + 1) := by
        rw [intervalIntegral.integral_neg, intervalIntegral_log_add_ofReal hz]
        ring

end Frullani

namespace Real.Wallis

/-! ### The Wallis product as a Laplace integral -/

/-- Mathlib's Wallis partial product `W n` satisfies `log (W n) → log (π / 2)`. -/
theorem tendsto_log_W_nhds_log_pi_div_two :
    Tendsto (fun n : ℕ ↦ log (W n)) atTop (𝓝 (log (π / 2))) :=
  (Real.continuousAt_log (by positivity)).tendsto.comp tendsto_W_nhds_pi_div_two

/-- The `n`-th telescoping block of the Wallis product, as a Frullani difference. -/
def pairKernel (n : ℕ) (x : ℝ) : ℝ := Frullani.expKernel (2 * (n : ℝ) + 1) (2 * (n : ℝ) + 2) x -
    Frullani.expKernel (2 * (n : ℝ) + 2) (2 * (n : ℝ) + 3) x

theorem pairKernel_eq (n : ℕ) (x : ℝ) :
    pairKernel n x = exp (-(2 * (n : ℝ) + 1) * x) * (1 - exp (-x)) ^ 2 / x := by
  have htwo : exp (-(2 * (n : ℝ) + 2) * x) = exp (-(2 * (n : ℝ) + 1) * x) * exp (-x) := by
    rw [show -(2 * (n : ℝ) + 2) * x = -(2 * (n : ℝ) + 1) * x + -x by ring, Real.exp_add]
  have hthree : exp (-(2 * (n : ℝ) + 3) * x) = exp (-(2 * (n : ℝ) + 1) * x) * exp (-x) ^ 2 := by
    rw [show -(2 * (n : ℝ) + 3) * x = -(2 * (n : ℝ) + 1) * x + -x + -x by ring,
      Real.exp_add, Real.exp_add]
    ring
  unfold pairKernel Frullani.expKernel
  rw [htwo, hthree]
  ring

theorem integrableOn_pairKernel (n : ℕ) : IntegrableOn (pairKernel n) (Ioi 0) :=
  (Frullani.integrableOn_expKernel (by positivity) (by linarith)).sub
    (Frullani.integrableOn_expKernel (by positivity) (by linarith))

/-- The ratio `W (n + 1) / W n` of consecutive Wallis partial products. -/
def pairFactor (n : ℕ) : ℝ := ((2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 1)) *
    ((2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 3))

theorem pairFactor_pos (n : ℕ) : 0 < pairFactor n := by
  unfold pairFactor
  positivity

theorem integral_pairKernel (n : ℕ) :
    (∫ x : ℝ in Ioi 0, pairKernel n x) = log (pairFactor n) := by
  unfold pairKernel pairFactor
  rw [integral_sub (Frullani.integrableOn_expKernel (by positivity) (by linarith))
      (Frullani.integrableOn_expKernel (by positivity) (by linarith)),
    Frullani.integral_expKernel (by positivity) (by linarith),
    Frullani.integral_expKernel (by positivity) (by linarith),
    Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by positivity)]
  ring

theorem W_succ_eq_mul_pairFactor (n : ℕ) : W (n + 1) = W n * pairFactor n := by
  simpa [pairFactor] using W_succ n

/-- The first `n` telescoping blocks of the Wallis product. -/
def partialKernel (n : ℕ) (x : ℝ) : ℝ := ∑ k ∈ Finset.range n, pairKernel k x

theorem integrableOn_partialKernel (n : ℕ) : IntegrableOn (partialKernel n) (Ioi 0) :=
  integrable_finsetSum _ fun k _ ↦ integrableOn_pairKernel k

theorem partialKernel_succ (n : ℕ) (x : ℝ) :
    partialKernel (n + 1) x = partialKernel n x + pairKernel n x := by
  simp [partialKernel, Finset.sum_range_succ]

theorem integral_partialKernel (n : ℕ) :
    (∫ x : ℝ in Ioi 0, partialKernel n x) = log (W n) := by
  induction n with
  | zero => simp [partialKernel, W]
  | succ n ih =>
    rw [funext (partialKernel_succ n),
      integral_add (integrableOn_partialKernel n) (integrableOn_pairKernel n), ih,
      integral_pairKernel, W_succ_eq_mul_pairFactor,
      Real.log_mul (W_pos n).ne' (pairFactor_pos n).ne']

/-- The Laplace kernel `e^{-x} (1 - e^{-x}) / (x (1 + e^{-x}))` of report (33). -/
def laplaceKernel (x : ℝ) : ℝ := exp (-x) * (1 - exp (-x)) / (x * (1 + exp (-x)))

theorem partialKernel_eq (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    partialKernel n x = laplaceKernel x * (1 - exp (-(2 * (n : ℝ)) * x)) := by
  induction n with
  | zero => simp [partialKernel]
  | succ n ih =>
    have htwo : exp (-(2 * (n + 1 : ℝ)) * x) = exp (-(2 * (n : ℝ)) * x) * exp (-x) ^ 2 := by
      rw [show -(2 * ((n : ℝ) + 1)) * x = -(2 * (n : ℝ)) * x + -x + -x by ring,
        Real.exp_add, Real.exp_add]
      ring
    have hone : exp (-(2 * (n : ℝ) + 1) * x) = exp (-(2 * (n : ℝ)) * x) * exp (-x) := by
      rw [show -(2 * (n : ℝ) + 1) * x = -(2 * (n : ℝ)) * x + -x by ring, Real.exp_add]
    rw [partialKernel_succ, ih, pairKernel_eq, Nat.cast_succ, htwo, hone]
    unfold laplaceKernel
    field_simp [hx, (by positivity : (1 : ℝ) + exp (-x) ≠ 0)]
    ring

theorem laplaceKernel_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ laplaceKernel x :=
  div_nonneg (mul_nonneg (exp_pos _).le
      (sub_nonneg.mpr (Real.exp_le_one_iff.2 (neg_nonpos.mpr hx.le))))
    (mul_nonneg hx.le (by positivity))

theorem integrableOn_laplaceKernel : IntegrableOn laplaceKernel (Ioi 0) := by
  have hbound : IntegrableOn (fun x : ℝ ↦ exp (-x)) (Ioi 0) := by
    simpa using integrableOn_exp_neg_mul_Ioi (a := (1 : ℝ)) zero_lt_one
  refine hbound.mono' ?_ ?_
  · unfold laplaceKernel
    exact (by fun_prop : Measurable fun x : ℝ ↦
      exp (-x) * (1 - exp (-x)) / (x * (1 + exp (-x)))).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx' : 0 < x := hx
  rw [Real.norm_eq_abs, abs_of_nonneg (laplaceKernel_nonneg hx)]
  unfold laplaceKernel
  refine (div_le_iff₀ (by positivity)).2 ?_
  nlinarith [Real.add_one_le_exp (-x), exp_pos (-x), mul_nonneg hx.le (exp_pos (-x)).le]

theorem abs_partialKernel_le (n : ℕ) {x : ℝ} (hx : 0 < x) :
    |partialKernel n x| ≤ laplaceKernel x := by
  have hexp : exp (-(2 * (n : ℝ)) * x) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  rw [partialKernel_eq n hx.ne',
    abs_of_nonneg (mul_nonneg (laplaceKernel_nonneg hx) (sub_nonneg.mpr hexp))]
  exact mul_le_of_le_one_right (laplaceKernel_nonneg hx)
    (by linarith [exp_pos (-(2 * (n : ℝ)) * x)])

theorem tendsto_partialKernel {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ ↦ partialKernel n x) atTop (𝓝 (laplaceKernel x)) := by
  have hexp : Tendsto (fun n : ℕ ↦ exp (-(2 * (n : ℝ)) * x)) atTop (𝓝 0) := by
    convert! Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity : (0 : ℝ) < 2 * x)) using 1
    funext n
    congr 1
    ring
  simpa only [partialKernel_eq _ hx.ne', sub_zero, mul_one] using
    (tendsto_const_nhds (x := laplaceKernel x)).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hexp)

theorem tendsto_integral_partialKernel :
    Tendsto (fun n : ℕ ↦ ∫ x : ℝ in Ioi 0, partialKernel n x) atTop
      (𝓝 (∫ x : ℝ in Ioi 0, laplaceKernel x)) := by
  refine tendsto_integral_of_dominated_convergence laplaceKernel
    (fun n ↦ (integrableOn_partialKernel n).aestronglyMeasurable)
    integrableOn_laplaceKernel (fun n ↦ ?_) ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simpa only [Real.norm_eq_abs] using abs_partialKernel_le n hx
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact tendsto_partialKernel hx

/-- Report (33): the Laplace kernel integrates to `log (π / 2)`, by the Wallis product. -/
theorem integral_laplaceKernel :
    (∫ x : ℝ in Ioi 0, laplaceKernel x) = log (π / 2) :=
  tendsto_nhds_unique tendsto_integral_partialKernel
    (by simpa only [integral_partialKernel] using tendsto_log_W_nhds_log_pi_div_two)

end Real.Wallis

end
