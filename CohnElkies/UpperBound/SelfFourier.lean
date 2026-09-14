import CohnElkies.UpperBound.Signs

/-!
# The self-Fourier function `f₀` (report §4.3, Lemma 4.3, Corollary 4.9)

The spectrum `X₀`, the Mellin data `M₀` and the profile `f₀` of the polynomial
`P₀(ζ) = -(1 + ζ²)`, obtained from the generic results on `mellinProfile`: `f₀` is a real radial
Schwartz function with `𝓕 f₀ = f₀` and `f₀(0) = 0`, and `f₀ > 0` outside the ball of radius
`R_{ε,d}` for all large `d`, so that it is a radial eigenfunction of eigenvalue `+1`
(`eventually_exists_radialEigenfunction_fZero`).
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory Real Set
open scoped ContDiff FourierTransform SchwartzMap Topology

/-! ### The polynomial `P₀(ζ) = -(1 + ζ²)` of the self-Fourier function (report, Lemma 4.3)

The self-Fourier function `f₀` of the report is the profile of the Mellin data
`M₀(z) = E_λ(i(z - λ)) P₀(i(z - λ)/λ)`, `P₀(ζ) = -(1 + ζ²)`, exactly as `f₊`, `f₋` are the
profiles for `P₊`, `P₋`. Everything below is obtained from the generic results on the profiles
`mellinProfile ε ℓ P c` of a saddle polynomial `P` (`IsSaddlePolynomial`), the only
`P₀`-specific inputs being `P₀(-ζ) = P₀(ζ)` (self-Fourier, report (40)), `P₀(-i) = 0`
(so `f₀(0) = 0`, report (42)) and `P₀(iu) = u² - 1 ≥ (ε/4)(2 + ε/4) > 0` for `u ≥ 1 + ε/4`
(the sign, report §4.3 and Corollary 4.9). -/

/-- `P₀` is a saddle polynomial: entire, of cubic growth and conjugation symmetric. -/
theorem isSaddlePolynomial_PZero (ε : ℝ) : IsSaddlePolynomial ε PZero where
  differentiable := differentiable_PZero
  norm_le := norm_PZero_le ε
  conj_eq := PZero_conj

/-- Lemmas 4.2, 4.4, 4.5 for `P₀` on `u ≥ 1 + ε/4`: `P₀(iu) ≥ (ε/4)(2 + ε/4) > 0` and
`‖P₀(T + iu) - P₀(iu)‖ ≤ C (|T| + |T|³) ‖P₀(iu)‖`. -/
theorem saddleRangeBounds_PZero {ε : ℝ} (hε : 0 < ε) : SaddleRangeBounds PZero (1 + ε / 4) where
  norm_pos u hu := by
    rw [norm_PZero_imaginary hε hu]
    have := PZero_imaginary_re_pos hε hu
    rw [PZero_imaginary] at this
    exact_mod_cast this
  difference := by
    have hbpos : 0 < ε / 4 * (2 + ε / 4) := by positivity
    set b : ℝ := ε / 4 * (2 + ε / 4)
    refine ⟨2 + 3 / b, by positivity, fun u hu T ↦ ?_⟩
    rw [norm_PZero_imaginary hε hu]
    have hD : b ≤ u ^ 2 - 1 := by
      have := PZero_imaginary_re_ge hε hu
      rw [PZero_imaginary] at this
      exact_mod_cast this
    have hu1 : 1 ≤ u := by linarith
    have hS : 0 ≤ |T| + |T| ^ 3 := by positivity
    have hT : T ^ 2 ≤ |T| + |T| ^ 3 := by
      nlinarith [abs_nonneg T, sq_abs T, mul_nonneg (abs_nonneg T) (sq_nonneg (|T| - 1))]
    have h1 : T ^ 2 ≤ 1 / b * (|T| + |T| ^ 3) * (u ^ 2 - 1) := by
      calc T ^ 2 ≤ |T| + |T| ^ 3 := hT
        _ = 1 / b * (|T| + |T| ^ 3) * b := by field_simp [hbpos.ne']
        _ ≤ 1 / b * (|T| + |T| ^ 3) * (u ^ 2 - 1) :=
            mul_le_mul_of_nonneg_left hD (by positivity)
    have hu' : |u| ≤ (1 + 1 / b) * (u ^ 2 - 1) := by
      rw [abs_of_nonneg (by linarith : 0 ≤ u)]
      have hbinv : 1 ≤ 1 / b * (u ^ 2 - 1) := by
        rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hbpos]
        linarith
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ u) (by linarith : (0 : ℝ) ≤ u - 1)]
    have h2 : 2 * |u| * |T| ≤ 2 * (1 + 1 / b) * (|T| + |T| ^ 3) * (u ^ 2 - 1) := by
      have hTle : |T| ≤ |T| + |T| ^ 3 := by nlinarith [pow_nonneg (abs_nonneg T) 3]
      have hfactor : 0 ≤ 2 * ((1 + 1 / b) * (u ^ 2 - 1)) :=
        mul_nonneg (by norm_num) (mul_nonneg (by positivity) (by linarith))
      calc 2 * |u| * |T| ≤ 2 * ((1 + 1 / b) * (u ^ 2 - 1)) * (|T| + |T| ^ 3) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hu' (by norm_num)) hTle (abs_nonneg T) hfactor
        _ = 2 * (1 + 1 / b) * (|T| + |T| ^ 3) * (u ^ 2 - 1) := by ring
    calc ‖PZero ((T : ℂ) + I * u) - PZero (I * u)‖ ≤ T ^ 2 + 2 * |u| * |T| :=
        norm_PZero_sub_imaginary_le T u
      _ ≤ 1 / b * (|T| + |T| ^ 3) * (u ^ 2 - 1) +
          2 * (1 + 1 / b) * (|T| + |T| ^ 3) * (u ^ 2 - 1) := add_le_add h1 h2
      _ = (2 + 3 / b) * (|T| + |T| ^ 3) * (u ^ 2 - 1) := by ring

/-! ### The spectrum `X₀`, the Mellin data `M₀` and the profile `f₀` -/

/-- `X₀(t) = E_λ(t) P₀(t/λ)`, report (38). -/
def XZero (ε ℓ t : ℝ) : ℂ := E ε ℓ t * PZero ((t : ℂ) / (ℓ : ℂ))

/-- `M₀(z) = E_λ(i(z - λ)) P₀(i(z - λ)/λ)`. -/
def MZero (ε ℓ : ℝ) (z : ℂ) : ℂ := mellinEnvelope ε ℓ z * PZero (I * (z - (ℓ : ℂ)) / (ℓ : ℂ))

/-- The radial profile `f₀` of the report: the inverse Mellin transform of `M₀` for `r ≠ 0`, with
`f₀(0) = 0` (report (42)); definitionally `mellinProfile ε ℓ PZero 0`. -/
def fZero (ε ℓ r : ℝ) : ℂ := if r = 0 then 0 else mellinInv ℓ (MZero ε ℓ) r

/-- The radial function `x ↦ f₀(‖x‖)` on `ℝ ^ d`. -/
def fZeroFun (ε : ℝ) (d : ℕ) (x : Euclidean d) : ℂ := fZero ε (d / 2 : ℝ) ‖x‖

theorem XZero_eq_spectrum (ε ℓ : ℝ) : XZero ε ℓ = spectrum ε ℓ PZero := rfl

theorem MZero_eq_mellinData (ε ℓ : ℝ) : MZero ε ℓ = mellinData ε ℓ PZero := rfl

theorem fZero_eq_mellinProfile (ε ℓ : ℝ) : fZero ε ℓ = mellinProfile ε ℓ PZero 0 := rfl

theorem fZeroFun_eq_mellinProfileFun (ε : ℝ) (d : ℕ) :
    fZeroFun ε d = mellinProfileFun ε d PZero 0 := rfl

@[simp] theorem fZero_zero (ε ℓ : ℝ) : fZero ε ℓ 0 = 0 := by simp [fZero]

@[simp] theorem fZeroFun_zero (ε : ℝ) (d : ℕ) : fZeroFun ε d (0 : Euclidean d) = 0 := by
  simp [fZeroFun]

theorem fZeroFun_radial (ε : ℝ) (d : ℕ) : IsRadial (fZeroFun ε d) :=
  fun _ _ hxy ↦ by simp only [fZeroFun, hxy]

/-- Report (42) for `P₀`: the residue of `M₀` at `z = 0` vanishes, since `P₀(-i) = 0`; it is the
value `f₀(0) = 0` of the residue expansion (78). -/
theorem poleResidue_PZero_zero {ε ℓ : ℝ} (hℓ : 0 < ℓ) : poleResidue ε ℓ PZero 0 = 0 := by
  rw [poleResidue_zero hℓ, PZero_neg_I, mul_zero]

/-- The multiplier identity `m_λ(t) X₀(-t) = X₀(t)` of report (40) for `P₀`. -/
theorem mellinMultiplier_mul_XZero_neg {ε ℓ : ℝ} (hℓ : 0 < ℓ) (t : ℝ) :
    m_ℓ ℓ t * XZero ε ℓ (-t) = XZero ε ℓ t :=
  mellinMultiplier_mul_spectrum_neg hℓ PZero_neg t

/-- `f₀` is real valued. -/
theorem fZeroFun_im (ε : ℝ) (d : ℕ) : IsRealValued (fZeroFun ε d) :=
  mellinProfileFun_im (isSaddlePolynomial_PZero ε) d 0

/-- Lemma 4.3 for `f₀`: `x ↦ f₀(‖x‖)` is smooth on `ℝᵈ`. -/
theorem fZeroFun_contDiff {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d) (horder : a₀ε ε ≤ Aε ε) :
    ContDiff ℝ ∞ (fZeroFun ε d) :=
  mellinProfileFun_contDiff hε hd horder (isSaddlePolynomial_PZero ε) (c := 0)
    (by rw [poleResidue_PZero_zero (dimension_half_pos hd), Complex.ofReal_zero])

/-- Report Lemma 4.3: `f₀` is a Schwartz function on `ℝᵈ`. -/
def zeroSaddleSchwartz {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d) (horder : a₀ε ε ≤ Aε ε) :
    TestFunction d :=
  mellinProfileSchwartz hε hd horder (isSaddlePolynomial_PZero ε) (c := 0)
    (by rw [poleResidue_PZero_zero (dimension_half_pos hd), Complex.ofReal_zero])

@[simp] theorem zeroSaddleSchwartz_apply {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : a₀ε ε ≤ Aε ε) (x : Euclidean d) :
    zeroSaddleSchwartz hε hd horder x = fZeroFun ε d x :=
  rfl

theorem isRealValued_zeroSaddleSchwartz {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : a₀ε ε ≤ Aε ε) : IsRealValued (zeroSaddleSchwartz hε hd horder) :=
  isRealValued_of_mellinProfile (c := 0) (isSaddlePolynomial_PZero ε) fun _ ↦ rfl

theorem isRadial_zeroSaddleSchwartz {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : a₀ε ε ≤ Aε ε) : IsRadial (zeroSaddleSchwartz hε hd horder) :=
  isRadial_of_mellinProfile (ε := ε) (P := PZero) (c := 0) fun _ ↦ rfl

/-- Report Lemma 4.3 and (40) for `P₀`: `𝓕 f₀ = f₀`, the self-Fourier property of `f₀`. -/
theorem fourier_zeroSaddleSchwartz {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : a₀ε ε ≤ Aε ε) :
    (𝓕 (zeroSaddleSchwartz hε hd horder) : TestFunction d) = zeroSaddleSchwartz hε hd horder :=
  fourier_eq_of_mellinProfile hε hd horder (isSaddlePolynomial_PZero ε)
    (isSaddlePolynomial_PZero ε) PZero_neg (c := 0) (c' := 0) _ _ (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- `f₀` as a real radial self-Fourier eigenfunction (`𝓕 g = g`, `g(0) = 0`), once it is known to
be nonzero. -/
def zeroSaddleEigenfunction {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d) (horder : a₀ε ε ≤ Aε ε)
    (hne : zeroSaddleSchwartz hε hd horder ≠ 0) : RadialEigenfunction d 1 where
  toFun := zeroSaddleSchwartz hε hd horder
  real := isRealValued_zeroSaddleSchwartz hε hd horder
  radial := isRadial_zeroSaddleSchwartz hε hd horder
  ne_zero := hne
  fourier_eq := by rw [fourier_zeroSaddleSchwartz]; simp
  zero := fZeroFun_zero ε d

/-! ### The sign of `f₀` outside the ball of radius `R_{ε,d}` (report §4.3, Corollary 4.9) -/

/-- Report §4.3 and Corollary 4.9 for `P₀`: for every sufficiently small `ε > 0` and all large
`d`, `Re f₀(r) > 0` for all `r ≥ R_{ε,d}`. -/
theorem eventually_fZero_re_pos_of_radius : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ᶠ d : ℕ in atTop,
    ∀ r : ℝ, R_ε ε d ≤ r → 0 < (fZero ε ((d : ℝ) / 2) r).re := by
  filter_upwards [self_mem_nhdsWithin, eventually_mellinProfile_re_mul_pos_of_radius]
    with ε hε hradius
  change 0 < ε at hε
  have hsign : ∀ u : ℝ, 1 + ε / 4 ≤ u → 0 < (1 : ℝ) * (PZero (I * (u : ℂ))).re :=
    fun u hu ↦ by rw [one_mul]; exact PZero_imaginary_re_pos hε hu
  filter_upwards [hradius PZero (1 + ε / 4) 1 (isSaddlePolynomial_PZero ε)
    (saddleRangeBounds_PZero hε) (by linarith) hsign] with d hd r hr
  rw [fZero_eq_mellinProfile]
  simpa using hd 0 r hr

/-- Report §4.3 and Corollary 4.9 for `P₀`: `f₀(x) > 0` for `‖x‖ ≥ R_{ε,d}`, for small `ε` and
large `d`. -/
theorem eventually_fZeroFun_re_pos_of_radius : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ᶠ d : ℕ in atTop,
    ∀ x : Euclidean d, R_ε ε d ≤ ‖x‖ → 0 < (fZeroFun ε d x).re := by
  filter_upwards [eventually_fZero_re_pos_of_radius] with ε h
  filter_upwards [h] with d hd x hx
  exact hd ‖x‖ hx

/-- Report §4 for `P₀`, packaged: for small `ε` and large `d` the function `f₀` is realized by a
real radial self-Fourier eigenfunction `g` (`𝓕 g = g`, `g(0) = 0`, `g ≠ 0`) which is positive
outside the ball of radius `R_{ε,d}`. -/
theorem eventually_exists_radialEigenfunction_fZero : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    ∀ᶠ d : ℕ in atTop, ∃ g : RadialEigenfunction d 1,
      (∀ x : Euclidean d, g.toFun x = fZeroFun ε d x) ∧
        ∀ x : Euclidean d, R_ε ε d ≤ ‖x‖ → 0 < (g.toFun x).re := by
  filter_upwards [self_mem_nhdsWithin, eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_fZeroFun_re_pos_of_radius] with ε hε horder hpos
  filter_upwards [hpos, eventually_gt_atTop 0] with d hd hd0
  have hne : zeroSaddleSchwartz hε hd0 horder ≠ 0 := by
    intro hzero
    have hx : ‖R_ε ε d • radialUnitDirection hd0‖ = R_ε ε d := by
      rw [norm_smul, norm_radialUnitDirection hd0, mul_one, Real.norm_eq_abs,
        abs_of_pos (saddleSourceRadius_pos ε d)]
    have h := hd (R_ε ε d • radialUnitDirection hd0) hx.symm.le
    rw [← zeroSaddleSchwartz_apply hε hd0 horder, hzero] at h
    simp at h
  exact ⟨zeroSaddleEigenfunction hε hd0 horder hne, fun _ ↦ rfl, hd⟩

end

end CohnElkies
