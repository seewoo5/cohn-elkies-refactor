import CohnElkies.SignUncertainty.Basic
import CohnElkies.UpperBound.SelfFourier

/-! # The upper bound of Theorem 1.2 (report, proof of Theorem 1.2)

For every sufficiently small `ε > 0` and all large `d`, the functions `g_{ε,d,-} = f₊ - f₋` and
`g_{ε,d,+} = f₀` of the report (Theorem 4.1 and (83)) are real radial test functions with
`𝓕 g = ς g`, `g(0) = 0`, which are strictly positive outside the ball of radius `R_{ε,d}`; in
particular they are nonzero, so their real parts are sign eigenfunctions of report (6) and
`A_ς(d) ≤ R_{ε,d}` for both signs `ς`. Since `R_{ε,d}/√d → α_ε` (report (84)) and `α_ε → 1/π`
(report (85)), `limsup_{d → ∞} A_ς(d)/√d ≤ 1/π`. -/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap Topology

/-! ### From real radial Schwartz eigenfunctions to `L¹` sign eigenfunctions -/

namespace RadialEigenfunction

variable {d : ℕ} {ς : ℤˣ}

theorem ofReal_re_apply (g : RadialEigenfunction d ς) (x : Euclidean d) :
    (((g.toFun x).re : ℝ) : ℂ) = g.toFun x :=
  Complex.ext (by simp) (by simp [g.real x])

/-- The real part of a real radial Schwartz eigenfunction (`𝓕 g = ς g`, `g(0) = 0`, `g ≠ 0`) is
a sign eigenfunction of report (6): it is integrable, and `𝓕 (Re g) = Re (𝓕 g) = ς Re g` since
`g` is real valued. -/
def toSignEigenfunction (g : RadialEigenfunction d ς) : SignEigenfunction d ς where
  toFun := fun x ↦ (g.toFun x).re
  integrable := g.toFun.integrable.re
  fourier_eq := by
    intro ξ
    have hfun : (fun x ↦ (((g.toFun x).re : ℝ) : ℂ)) = ⇑g.toFun := funext g.ofReal_re_apply
    rw [hfun, ← SchwartzMap.fourier_coe, g.fourier_eq, smul_apply, smul_eq_mul,
      g.ofReal_re_apply]
  ne_zero h := g.ne_zero <| SchwartzMap.ext fun x ↦ by
    have hx : (g.toFun x).re = 0 := congrFun h x
    rw [← g.ofReal_re_apply x, hx]
    simp
  zero := by simp [g.zero]

@[simp] theorem toSignEigenfunction_apply (g : RadialEigenfunction d ς) (x : Euclidean d) :
    g.toSignEigenfunction x = (g.toFun x).re :=
  rfl

/-- `r(Re g) ≤ R` when `Re g ≥ 0` outside the ball of radius `R` (report (5)). -/
theorem signRadius_toSignEigenfunction_le (g : RadialEigenfunction d ς) {R : ℝ}
    (hR : ∀ x : Euclidean d, R ≤ ‖x‖ → 0 ≤ (g.toFun x).re) :
    signRadius g.toSignEigenfunction ≤ ENNReal.ofReal R :=
  signRadius_le fun x hx ↦ hR x ((Real.le_coe_toNNReal R).trans hx)

/-- `A_ς(d) ≤ R` as soon as some real radial Schwartz eigenfunction with eigenvalue `ς` is
nonnegative outside the ball of radius `R` (report (6)). -/
theorem signUncertaintyConstant_le_of_nonneg_outside (g : RadialEigenfunction d ς) {R : ℝ}
    (hR : ∀ x : Euclidean d, R ≤ ‖x‖ → 0 ≤ (g.toFun x).re) :
    signUncertaintyConstant ς d ≤ ENNReal.ofReal R :=
  (signUncertaintyConstant_le g.toSignEigenfunction).trans
    (g.signRadius_toSignEigenfunction_le hR)

end RadialEigenfunction

/-! ### The Schwartz realizations `f₊`, `f₋` as real radial test functions (report (40), (83)) -/

section SaddlePair

variable {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d) (horder : a₀ε ε ≤ Aε ε)

theorem isRealValued_plusSaddleSchwartz : IsRealValued (plusSaddleSchwartz hε hd horder) :=
  plusSaddle_real_of_source fun _ ↦ rfl

theorem isRealValued_minusSaddleSchwartz : IsRealValued (minusSaddleSchwartz hε hd horder) :=
  minusSaddle_real_of_source fun _ ↦ rfl

theorem isRadial_plusSaddleSchwartz : IsRadial (plusSaddleSchwartz hε hd horder) :=
  isRadial_of_source (F := fPlus ε ((d : ℝ) / 2)) fun _ ↦ rfl

theorem isRadial_minusSaddleSchwartz : IsRadial (minusSaddleSchwartz hε hd horder) :=
  isRadial_of_source (F := fMinus ε ((d : ℝ) / 2)) fun _ ↦ rfl

/-- Report (40): `𝓕 f₋ = f₊`. -/
theorem fourier_minusSaddleSchwartz :
    (𝓕 (minusSaddleSchwartz hε hd horder) : TestFunction d) = plusSaddleSchwartz hε hd horder :=
  saddleSource_fourier_minus_eq_plus hε hd horder _ _ (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- Report (83): `f₋(0) = f₊(0)`. -/
theorem minusSaddleSchwartz_zero_eq :
    minusSaddleSchwartz hε hd horder 0 = plusSaddleSchwartz hε hd horder 0 :=
  saddleSource_zero_eq (ε := ε) _ _ (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- `f₊ - f₋ = 𝓕 f₋ - f₋` is the anti-self-Fourier part of `f₋` (report (40)). -/
theorem antiFourierPart_minusSaddleSchwartz :
    antiFourierPart (minusSaddleSchwartz hε hd horder) =
      plusSaddleSchwartz hε hd horder - minusSaddleSchwartz hε hd horder := by
  rw [antiFourierPart, fourier_minusSaddleSchwartz]

/-- Report, proof of Theorem 1.2: `g_{ε,d,-} = f₊ - f₋` is a real radial test function with
`𝓕 g = -g` (by (40) and Fourier inversion) and `g(0) = f₊(0) - f₋(0) = 0` (by (83)); it is a
radial eigenfunction with eigenvalue `-1` once it is known to be nonzero. -/
def minusSaddleEigenfunction
    (hne : plusSaddleSchwartz hε hd horder - minusSaddleSchwartz hε hd horder ≠ 0) :
    RadialEigenfunction d (-1) where
  toFun := plusSaddleSchwartz hε hd horder - minusSaddleSchwartz hε hd horder
  real := by
    intro x
    rw [sub_apply, Complex.sub_im, isRealValued_plusSaddleSchwartz hε hd horder x,
      isRealValued_minusSaddleSchwartz hε hd horder x, sub_zero]
  radial := by
    intro x y hxy
    rw [sub_apply, sub_apply, isRadial_plusSaddleSchwartz hε hd horder x y hxy,
      isRadial_minusSaddleSchwartz hε hd horder x y hxy]
  ne_zero := hne
  fourier_eq := by
    rw [← antiFourierPart_minusSaddleSchwartz hε hd horder,
      fourier_antiFourierPart _ (isRadial_minusSaddleSchwartz hε hd horder)]
    simp
  zero := by rw [sub_apply, minusSaddleSchwartz_zero_eq hε hd horder, sub_self]

end SaddlePair

/-! ### The anti-self-Fourier function `g_{ε,d,-} = f₊ - f₋` (report, proof of Theorem 1.2) -/

/-- Report, proof of Theorem 1.2 (with (83)): for small `ε` and large `d`, `g_{ε,d,-} = f₊ - f₋`
is a real radial anti-self-Fourier eigenfunction vanishing at the origin and strictly positive
outside the ball of radius `R_{ε,d}` (there `f₊ ≥ 0 > f₋`). -/
theorem eventually_exists_radialEigenfunction_neg_one : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    ∀ᶠ d : ℕ in atTop, ∃ g : RadialEigenfunction d (-1),
      ∀ x : Euclidean d, R_ε ε d ≤ ‖x‖ → 0 < (g.toFun x).re := by
  filter_upwards [self_mem_nhdsWithin, eventually_upper_shortCutoff_le_shortEndpoint,
    saddleSourceEventualSigns, eventually_fMinus_re_neg_of_radius] with ε hε₀ horder hsigns hneg
  have hε : 0 < ε := hε₀
  filter_upwards [hsigns, hneg, eventually_gt_atTop 0] with d hsign hneg_d hd0
  have hpos : ∀ x : Euclidean d, R_ε ε d ≤ ‖x‖ →
      0 < ((plusSaddleSchwartz hε hd0 horder - minusSaddleSchwartz hε hd0 horder) x).re := by
    intro x hx
    have h1 : 0 ≤ (fPlusFun ε d x).re := hsign.1 x
    have h2 : (fMinusFun ε d x).re < 0 := hneg_d ‖x‖ hx
    rw [sub_apply, Complex.sub_re, plusSaddleSchwartz_apply, minusSaddleSchwartz_apply]
    linarith
  have hne : plusSaddleSchwartz hε hd0 horder - minusSaddleSchwartz hε hd0 horder ≠ 0 := by
    intro hzero
    have hx : ‖R_ε ε d • radialUnitDirection hd0‖ = R_ε ε d := by
      rw [norm_smul, norm_radialUnitDirection hd0, mul_one, Real.norm_eq_abs,
        abs_of_pos (saddleSourceRadius_pos ε d)]
    have h := hpos (R_ε ε d • radialUnitDirection hd0) hx.symm.le
    rw [hzero] at h
    simp at h
  exact ⟨minusSaddleEigenfunction hε hd0 horder hne, hpos⟩

/-! ### `A_ς(d) ≤ R_{ε,d}` and the `limsup` bound -/

/-- Report, proof of Theorem 1.2: for both signs `ς`, for small `ε` and large `d`, the function
`g_{ε,d,ς}` (`f₊ - f₋` for `ς = -1`, `f₀` for `ς = 1`) is a real radial eigenfunction with
eigenvalue `ς` vanishing at the origin and strictly positive outside the ball of radius
`R_{ε,d}`. -/
theorem eventually_exists_radialEigenfunction_pos_outside (ς : ℤˣ) :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ᶠ d : ℕ in atTop, ∃ g : RadialEigenfunction d ς,
      ∀ x : Euclidean d, R_ε ε d ≤ ‖x‖ → 0 < (g.toFun x).re := by
  rcases Int.units_eq_one_or ς with rfl | rfl
  · filter_upwards [eventually_exists_radialEigenfunction_fZero] with ε hε
    filter_upwards [hε] with d hd
    obtain ⟨g, -, hg⟩ := hd
    exact ⟨g, hg⟩
  · exact eventually_exists_radialEigenfunction_neg_one

/-- Report, proof of Theorem 1.2: `A_ς(d) ≤ R_{ε,d}` for both signs, for small `ε` and large
`d`. -/
theorem eventually_signUncertaintyConstant_le (ς : ℤˣ) : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    ∀ᶠ d : ℕ in atTop, signUncertaintyConstant ς d ≤ ENNReal.ofReal (R_ε ε d) := by
  filter_upwards [eventually_exists_radialEigenfunction_pos_outside ς] with ε hε
  filter_upwards [hε] with d hd
  obtain ⟨g, hg⟩ := hd
  exact g.signUncertaintyConstant_le_of_nonneg_outside fun x hx ↦ (hg x hx).le

/-- `limsup_{d → ∞} A_ς(d)/√d ≤ α_ε` for every small `ε > 0` (in `ℝ≥0∞`), from
`A_ς(d) ≤ R_{ε,d}` and `R_{ε,d}/√d → α_ε` (report (84)). -/
theorem eventually_limsup_signUncertaintyConstant_div_sqrt_le (ς : ℤˣ) :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      limsup (fun d : ℕ ↦ signUncertaintyConstant ς d / ENNReal.ofReal (Real.sqrt d)) atTop ≤
        ENNReal.ofReal (α_ε ε) := by
  filter_upwards [self_mem_nhdsWithin, eventually_signUncertaintyConstant_le ς] with ε hε hle
  have hlim : Tendsto (fun d : ℕ ↦ ENNReal.ofReal (R_ε ε d / √(d : ℝ))) atTop
      (𝓝 (ENNReal.ofReal (α_ε ε))) :=
    ENNReal.tendsto_ofReal (tendsto_saddleSourceRadius_normalized hε)
  refine (limsup_le_limsup ?_).trans hlim.limsup_eq.le
  filter_upwards [hle, eventually_gt_atTop 0] with d hd hd0
  have hsq : 0 < √(d : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hd0)
  rw [ENNReal.ofReal_div_of_pos hsq]
  exact ENNReal.div_le_div_right hd _

/-- The upper bound of Theorem 1.2 in `limsup` form: `limsup_{d → ∞} A_ς(d)/√d ≤ 1/π`
(in `ℝ≥0∞`), letting `ε → 0⁺` in the previous bound, by `α_ε → 1/π` (report (85)). -/
theorem limsup_signUncertaintyConstant_div_sqrt_le (ς : ℤˣ) :
    limsup (fun d : ℕ ↦ signUncertaintyConstant ς d / ENNReal.ofReal (Real.sqrt d)) atTop ≤
      ENNReal.ofReal (Real.pi⁻¹) :=
  ge_of_tendsto (ENNReal.tendsto_ofReal tendsto_limitingSaddleRadius)
    (eventually_limsup_signUncertaintyConstant_div_sqrt_le ς)

end

end CohnElkies
