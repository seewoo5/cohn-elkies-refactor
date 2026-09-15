import CohnElkies.SignUncertainty.OriginCorrection
import CohnElkies.SignUncertainty.AppendixA

/-! # Positivity and finiteness of the sign-uncertainty constants

For every dimension `d ≥ 1` and both signs `ς = ±1`, the constants `A_ς(d) = inf r(g)` of report (6)
satisfy `0 < A_ς(d) < ∞`, the two facts needed before extremizers of `A_ς(d)` can be discussed
(Cohn–Gonçalves, *An optimal uncertainty principle in twelve dimensions via modular forms*, Invent.
Math. 2019, §3.1 and Theorem 1.4).

* `A_ς(d) > 0` (`signUncertaintyConstant_pos`): if `g ∈ 𝓔_ς(d)` is nonnegative outside the ball
  `B_ρ`, then, normalizing `‖g‖₁ = 1` and using `∫ g = 0`, the negative part `g₋ = (|g| - g)/2`
  has `∫ g₋ = ½`, vanishes outside `B_ρ` and is bounded by `|g| ≤ ‖g‖₁ = 1`; hence `½ ≤ vol(B_ρ)`
  (`SignEigenfunction.half_le_volume_ball`). Since `vol(B_ρ) = ρ^d vol(B_1)` is small for small
  `ρ`, no `g ∈ 𝓔_ς(d)` is nonnegative outside a small ball, and `A_ς(d) ≥ ρ > 0`.
* `A₋(d) < ∞` (`signUncertaintyConstant_neg_one_lt_top`): the explicit function
  `G = ψ_{1/4} - ψ_{1/2}` (`explicitEigenfunction`), with `ψ_t = φ_t - 𝓕φ_t` the perturbation of
  `CohnElkies.SignUncertainty.OriginCorrection`, satisfies `𝓕 G = -G`, `G(0) = -1 - (-1) = 0`,
  and `G > 0` outside an explicit ball (`explicitEigenfunction_pos`), so `G ∈ 𝓔₋(d)` and
  `r(G) < ∞`. Writing `E_b(x) = e^{-π b |x|²}`, `D = 2^d - 2^{d/2}` and `D' = 2^{d/2} - 1`,
  ```
    ψ_{1/4} = (E_{1/4} - E_{1/2} - 2^d E_4 + 2^{d/2} E_2) / D,
    ψ_{1/2} = (E_{1/2} - 2^{d/2} E_2) / D',
  ```
  and dropping the positive `E_2`-terms, `E_{1/2} = E_{1/4} e^{-π|x|²/4}` and
  `E_4 ≤ E_{1/4} e^{-π|x|²/4}` give `G ≥ E_{1/4} (1 - e^{-π|x|²/4} (1 + D/D' + 2^d)) / D`, which
  is positive as soon as `|x|² > (4/π) log (1 + D/D' + 2^d)`.
* `A₊(d) < ∞` (`signUncertaintyConstant_lt_top`) follows from `A₊(d) ≤ A₋(d)`
  (`signUncertaintyConstant_one_le_neg_one`, Appendix A of the report). -/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal FourierTransform Topology

variable {d : ℕ}

/-! ### `A_ς(d) > 0`: no sign eigenfunction is nonnegative outside a ball of volume `< ½` -/

/-- Cohn–Gonçalves §3.1, first display: if `g ∈ 𝓔_ς(d)` is nonnegative outside the ball `B_ρ`,
then `½ ≤ vol(B_ρ)`. Indeed, for `h = g/‖g‖₁`, `∫ h = 0` gives `∫ (|h| - h) = ‖h‖₁ = 1`, while
`|h| - h` vanishes outside `B_ρ` and is at most `2 |h| ≤ 2 ‖h‖₁ = 2` on `B_ρ`. -/
theorem SignEigenfunction.half_le_volume_ball {ς : ℤˣ} (g : SignEigenfunction d ς) {ρ : ℝ}
    (hρ : ∀ x : Euclidean d, ρ ≤ ‖x‖ → 0 ≤ g x) :
    2⁻¹ ≤ (volume (Metric.ball (0 : Euclidean d) ρ)).toReal := by
  set h := g.normalize
  have h1 : ∫ x, ‖h x‖ = 1 := g.integral_norm_normalize
  have hnn : ∀ x : Euclidean d, ρ ≤ ‖x‖ → 0 ≤ h x := fun x hx ↦
    mul_nonneg (inv_pos.2 g.integral_norm_pos).le (hρ x hx)
  have hbd : ∀ x, ‖h x‖ ≤ 1 := fun x ↦ (h.norm_apply_le x).trans_eq h1
  have hint : ∫ x, (‖h x‖ - h x) = 1 := by
    rw [integral_sub h.integrable.norm h.integrable, h.integral_eq_zero, sub_zero, h1]
  have hle : ∀ x, ‖h x‖ - h x ≤ (Metric.ball (0 : Euclidean d) ρ).indicator (fun _ ↦ 2) x := by
    intro x
    by_cases hx : x ∈ Metric.ball (0 : Euclidean d) ρ
    · rw [indicator_of_mem hx]
      have := hbd x
      rw [Real.norm_eq_abs] at this ⊢
      linarith [neg_abs_le (h x)]
    · rw [indicator_of_notMem hx, Real.norm_of_nonneg (hnn x (not_lt.1 fun h' ↦
        hx (mem_ball_zero_iff.2 h'))), sub_self]
  have hi : Integrable ((Metric.ball (0 : Euclidean d) ρ).indicator fun _ ↦ (2 : ℝ)) :=
    (integrable_indicator_iff measurableSet_ball).2 (integrableOn_const measure_ball_lt_top.ne)
  have this : ∫ x, (‖h x‖ - h x) ≤ ∫ x, (Metric.ball (0 : Euclidean d) ρ).indicator (fun _ ↦ 2) x :=
    integral_mono (h.integrable.norm.sub h.integrable) hi hle
  rw [hint, integral_indicator_const _ measurableSet_ball, smul_eq_mul, measureReal_def] at this
  linarith

/-- A ball of small radius has volume `< ½`: `vol(B_ρ) = ρ^d vol(B_1) ≤ ρ vol(B_1)` for `ρ ≤ 1`,
`d ≥ 1`, and `ρ = 1 / (2 (vol(B_1) + 1))` works. -/
theorem exists_volume_ball_lt_half (hd : 0 < d) :
    ∃ ρ : ℝ, 0 < ρ ∧ (volume (Metric.ball (0 : Euclidean d) ρ)).toReal < 2⁻¹ := by
  set V : ℝ := (volume (Metric.ball (0 : Euclidean d) 1)).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hρ : (0 : ℝ) < (2 * (V + 1))⁻¹ := by positivity
  refine ⟨(2 * (V + 1))⁻¹, hρ, ?_⟩
  rw [Measure.addHaar_ball_of_pos _ _ hρ, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    finrank_euclideanSpace_fin, ← hV]
  have hρ1 : (2 * (V + 1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  calc (2 * (V + 1))⁻¹ ^ d * V ≤ (2 * (V + 1))⁻¹ * V :=
        mul_le_mul_of_nonneg_right (pow_le_of_le_one hρ.le hρ1 hd.ne') hV0
    _ < 2⁻¹ := by
        rw [inv_mul_eq_div, div_lt_iff₀ (by positivity)]
        linarith

/-- `A_ς(d) > 0` for `d ≥ 1` and both signs (Cohn–Gonçalves §3.1): no sign eigenfunction is
nonnegative outside a ball of volume `< ½`. -/
theorem signUncertaintyConstant_pos (hd : 0 < d) (ς : ℤˣ) : 0 < signUncertaintyConstant ς d := by
  obtain ⟨ρ, hρ, hvol⟩ := exists_volume_ball_lt_half hd
  refine (ENNReal.ofReal_pos.2 hρ).trans_le (le_signUncertaintyConstant fun g hg ↦ ?_)
  exact absurd (g.half_le_volume_ball hg) (not_le.2 hvol)

/-! ### `A₋(d) < ∞`: the explicit eigenfunction `G = ψ_{1/4} - ψ_{1/2}` -/

/-- `G = ψ_{1/4} - ψ_{1/2}`, with `ψ_t = φ_t - 𝓕φ_t`: `𝓕 G = -G`, `G(0) = -1 - (-1) = 0`, and
`G > 0` outside an explicit ball (`explicitEigenfunction_pos`), so `G ∈ 𝓔₋(d)`
(`explicitSignEigenfunction`). -/
def explicitEigenfunction (d : ℕ) (x : Euclidean d) : ℝ :=
  gaussianPerturbation d (1 / 4) x - gaussianPerturbation d (1 / 2) x

/-- `ψ_{1/4} = (E_{1/4} - E_{1/2} - 2^d E_4 + 2^{d/2} E_2) / D` with `E_b(x) = e^{-π b |x|²}`,
`D = 2^d - 2^{d/2}`, where `2^d = ((1/4)^{d/2})⁻¹` and `2^{d/2} = ((1/2)^{d/2})⁻¹`. -/
theorem gaussianPerturbation_quarter_eq (x : Euclidean d) :
    gaussianPerturbation d (1 / 4) x =
      (gaussianReal (1 / 4) x - gaussianReal (1 / 2) x -
        ((1 / 4 : ℝ) ^ (d / 2 : ℝ))⁻¹ * gaussianReal 4 x +
        ((1 / 2 : ℝ) ^ (d / 2 : ℝ))⁻¹ * gaussianReal 2 x) / gaussianDifferenceDenom d (1 / 4) := by
  have h1 : (2 : ℝ) * (1 / 4) = 1 / 2 := by norm_num
  have h2 : ((1 : ℝ) / 4)⁻¹ = 4 := by norm_num
  have h3 : ((1 : ℝ) / 2)⁻¹ = 2 := by norm_num
  simp only [gaussianPerturbation, gaussianDifference, fourierGaussianDifference, h1, h2, h3]
  ring

/-- `ψ_{1/2} = (E_{1/2} - 2^{d/2} E_2) / D'` with `D' = 2^{d/2} - 1` (the two `E_1`-terms of
`φ_{1/2}` and `𝓕φ_{1/2}` cancel), where `2^{d/2} = ((1/2)^{d/2})⁻¹`. -/
theorem gaussianPerturbation_half_eq (x : Euclidean d) :
    gaussianPerturbation d (1 / 2) x =
      (gaussianReal (1 / 2) x - ((1 / 2 : ℝ) ^ (d / 2 : ℝ))⁻¹ * gaussianReal 2 x) /
        gaussianDifferenceDenom d (1 / 2) := by
  have h1 : (2 : ℝ) * (1 / 2) = 1 := by norm_num
  have h3 : ((1 : ℝ) / 2)⁻¹ = 2 := by norm_num
  simp only [gaussianPerturbation, gaussianDifference, fourierGaussianDifference, h1, h3,
    Real.one_rpow, inv_one, one_mul]
  ring

/-- `E_{1/2} = E_{1/4} · e^{-π|x|²/4}`. -/
theorem gaussianReal_half_eq (x : Euclidean d) :
    gaussianReal (1 / 2) x = gaussianReal (1 / 4) x * Real.exp (-(π * ‖x‖ ^ 2 / 4)) := by
  rw [gaussianReal, gaussianReal, ← Real.exp_add]
  congr 1
  ring

/-- `E_4 = E_{1/4} · e^{-15π|x|²/4} ≤ E_{1/4} · e^{-π|x|²/4}`. -/
theorem gaussianReal_four_le (x : Euclidean d) :
    gaussianReal 4 x ≤ gaussianReal (1 / 4) x * Real.exp (-(π * ‖x‖ ^ 2 / 4)) := by
  rw [gaussianReal, gaussianReal, ← Real.exp_add, Real.exp_le_exp]
  have : 0 ≤ π * ‖x‖ ^ 2 := by positivity
  linarith

/-- The lower bound `G ≥ E_{1/4} · (1 - e^{-π|x|²/4} (1 + D/D' + 2^d)) / D`: drop the positive
`E_2`-terms of `ψ_{1/4}` and `-ψ_{1/2}`, and use `E_{1/2} = E_{1/4} e^{-π|x|²/4}`,
`E_4 ≤ E_{1/4} e^{-π|x|²/4}`. -/
theorem le_explicitEigenfunction (hd : 0 < d) (x : Euclidean d) :
    gaussianReal (1 / 4) x * (1 - Real.exp (-(π * ‖x‖ ^ 2 / 4)) *
      (1 + gaussianDifferenceDenom d (1 / 4) / gaussianDifferenceDenom d (1 / 2) +
        ((1 / 4 : ℝ) ^ (d / 2 : ℝ))⁻¹)) / gaussianDifferenceDenom d (1 / 4) ≤
      explicitEigenfunction d x := by
  have hD := gaussianDifferenceDenom_pos hd (by norm_num : (0 : ℝ) < 1 / 4)
  have hD' := gaussianDifferenceDenom_pos hd (by norm_num : (0 : ℝ) < 1 / 2)
  have hc₄ : 0 < ((1 / 4 : ℝ) ^ (d / 2 : ℝ))⁻¹ := inv_pos.2 (Real.rpow_pos_of_pos (by norm_num) _)
  have hc₂ : 0 < ((1 / 2 : ℝ) ^ (d / 2 : ℝ))⁻¹ := inv_pos.2 (Real.rpow_pos_of_pos (by norm_num) _)
  have hE₂ := gaussianReal_pos 2 x
  have h4 := gaussianReal_four_le x
  rw [explicitEigenfunction, gaussianPerturbation_quarter_eq, gaussianPerturbation_half_eq,
    gaussianReal_half_eq, ← sub_nonneg]
  set D := gaussianDifferenceDenom d (1 / 4)
  set D' := gaussianDifferenceDenom d (1 / 2)
  set c₄ := ((1 / 4 : ℝ) ^ (d / 2 : ℝ))⁻¹
  set c₂ := ((1 / 2 : ℝ) ^ (d / 2 : ℝ))⁻¹
  set E₁ := gaussianReal (1 / 4) x
  set E₂ := gaussianReal 2 x
  set E₄ := gaussianReal 4 x
  set q := Real.exp (-(π * ‖x‖ ^ 2 / 4))
  have hD0 : D ≠ 0 := hD.ne'
  have hD'0 : D' ≠ 0 := hD'.ne'
  have key : (E₁ - E₁ * q - c₄ * E₄ + c₂ * E₂) / D - (E₁ * q - c₂ * E₂) / D' -
      E₁ * (1 - q * (1 + D / D' + c₄)) / D =
      c₄ * (E₁ * q - E₄) / D + c₂ * E₂ / D + c₂ * E₂ / D' := by
    field_simp
    ring
  rw [key]
  exact add_nonneg (add_nonneg (div_nonneg (mul_nonneg hc₄.le (sub_nonneg.2 h4)) hD.le)
    (by positivity)) (by positivity)

/-- `G(x) > 0` when `|x|² > (4/π) log (1 + D/D' + 2^d)`, with `D = 2^d - 2^{d/2}`,
`D' = 2^{d/2} - 1` and `2^d = ((1/4)^{d/2})⁻¹`: then `e^{-π|x|²/4} (1 + D/D' + 2^d) < 1` in the
lower bound `le_explicitEigenfunction`. -/
theorem explicitEigenfunction_pos (hd : 0 < d) {x : Euclidean d}
    (hx : 4 * Real.log (1 + gaussianDifferenceDenom d (1 / 4) / gaussianDifferenceDenom d (1 / 2) +
      ((1 / 4 : ℝ) ^ (d / 2 : ℝ))⁻¹) / π < ‖x‖ ^ 2) : 0 < explicitEigenfunction d x := by
  have hD := gaussianDifferenceDenom_pos hd (by norm_num : (0 : ℝ) < 1 / 4)
  have hD' := gaussianDifferenceDenom_pos hd (by norm_num : (0 : ℝ) < 1 / 2)
  have hc₄ : 0 < ((1 / 4 : ℝ) ^ (d / 2 : ℝ))⁻¹ := inv_pos.2 (Real.rpow_pos_of_pos (by norm_num) _)
  have hS : 0 < 1 + gaussianDifferenceDenom d (1 / 4) / gaussianDifferenceDenom d (1 / 2) +
      ((1 / 4 : ℝ) ^ (d / 2 : ℝ))⁻¹ := by
    have := div_pos hD hD'
    linarith
  refine lt_of_lt_of_le (div_pos (mul_pos (gaussianReal_pos _ _) (sub_pos.2 ?_)) hD)
    (le_explicitEigenfunction hd x)
  rw [div_lt_iff₀ Real.pi_pos] at hx
  have hlog := (Real.log_lt_iff_lt_exp hS).1 (by linarith : Real.log _ < π * ‖x‖ ^ 2 / 4)
  calc Real.exp (-(π * ‖x‖ ^ 2 / 4)) * _ <
      Real.exp (-(π * ‖x‖ ^ 2 / 4)) * Real.exp (π * ‖x‖ ^ 2 / 4) :=
        mul_lt_mul_of_pos_left hlog (Real.exp_pos _)
    _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

/-- A radius beyond which `G > 0`: `R(d) = √((4/π) log (1 + D/D' + 2^d)) + 1`. -/
def explicitEigenfunctionRadius (d : ℕ) : ℝ :=
  √(4 * Real.log (1 + gaussianDifferenceDenom d (1 / 4) / gaussianDifferenceDenom d (1 / 2) +
    ((1 / 4 : ℝ) ^ (d / 2 : ℝ))⁻¹) / π) + 1

theorem explicitEigenfunctionRadius_nonneg (d : ℕ) : 0 ≤ explicitEigenfunctionRadius d :=
  add_nonneg (Real.sqrt_nonneg _) zero_le_one

/-- `G(x) > 0` for `|x| ≥ R(d)`: then `|x|² ≥ (√L + 1)² > L = (4/π) log (1 + D/D' + 2^d)`. -/
theorem explicitEigenfunction_pos_of_le (hd : 0 < d) {x : Euclidean d}
    (hx : explicitEigenfunctionRadius d ≤ ‖x‖) : 0 < explicitEigenfunction d x := by
  have hD := gaussianDifferenceDenom_pos hd (by norm_num : (0 : ℝ) < 1 / 4)
  have hD' := gaussianDifferenceDenom_pos hd (by norm_num : (0 : ℝ) < 1 / 2)
  have hc₄ : 0 < ((1 / 4 : ℝ) ^ (d / 2 : ℝ))⁻¹ := inv_pos.2 (Real.rpow_pos_of_pos (by norm_num) _)
  refine explicitEigenfunction_pos hd ?_
  set L := 4 * Real.log (1 + gaussianDifferenceDenom d (1 / 4) / gaussianDifferenceDenom d (1 / 2) +
    ((1 / 4 : ℝ) ^ (d / 2 : ℝ))⁻¹) / π with hL
  have hL0 : 0 < L := by
    have := div_pos hD hD'
    exact div_pos (mul_pos four_pos (Real.log_pos (by linarith))) Real.pi_pos
  have hs := Real.sqrt_nonneg L
  have hsq := Real.sq_sqrt hL0.le
  have := pow_le_pow_left₀ (explicitEigenfunctionRadius_nonneg d) hx 2
  unfold explicitEigenfunctionRadius at this
  rw [← hL] at this
  nlinarith

/-- Cohn–Gonçalves, §3.3: `G = ψ_{1/4} - ψ_{1/2} ∈ 𝓔₋(d)`: `𝓕 G = -G` (as `𝓕ψ_t = -ψ_t`),
`G(0) = -1 - (-1) = 0`, `G` is integrable, and `G ≠ 0` since `G > 0` outside the ball of radius
`R(d)`. -/
def explicitSignEigenfunction (hd : 0 < d) : SignEigenfunction d (-1) where
  toFun := explicitEigenfunction d
  integrable := (integrable_gaussianPerturbation (by norm_num)).sub
    (integrable_gaussianPerturbation (by norm_num))
  fourier_eq ξ := by
    have h4 : (0 : ℝ) < 1 / 4 := by norm_num
    have h2 : (0 : ℝ) < 1 / 2 := by norm_num
    have h : (fun x ↦ (explicitEigenfunction d x : ℂ)) = fun x ↦
        (gaussianPerturbation d (1 / 4) x : ℂ) - (gaussianPerturbation d (1 / 2) x : ℂ) := by
      funext x
      simp [explicitEigenfunction]
    rw [h, fourier_sub_apply (integrable_ofReal_gaussianPerturbation h4)
      (integrable_ofReal_gaussianPerturbation h2), fourier_gaussianPerturbation h4,
      fourier_gaussianPerturbation h2, explicitEigenfunction]
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
    push_cast
    ring
  ne_zero h := by
    set x : Euclidean d := explicitEigenfunctionRadius d • radialUnitDirection hd with hx
    have hxn : explicitEigenfunctionRadius d ≤ ‖x‖ := by
      rw [hx, norm_smul, norm_radialUnitDirection hd, mul_one,
        Real.norm_of_nonneg (explicitEigenfunctionRadius_nonneg d)]
    have := explicitEigenfunction_pos_of_le hd hxn
    rw [congrFun h x, Pi.zero_apply] at this
    exact lt_irrefl _ this
  zero := by
    rw [explicitEigenfunction, gaussianPerturbation_apply_zero hd (by norm_num),
      gaussianPerturbation_apply_zero hd (by norm_num), sub_self]

theorem explicitSignEigenfunction_apply (hd : 0 < d) (x : Euclidean d) :
    explicitSignEigenfunction hd x = explicitEigenfunction d x :=
  rfl

/-- `r(G) ≤ R(d) = √((4/π) log (1 + D/D' + 2^d)) + 1`. -/
theorem signRadius_explicitSignEigenfunction_le (hd : 0 < d) :
    signRadius (explicitSignEigenfunction hd) ≤ ENNReal.ofReal (explicitEigenfunctionRadius d) :=
  signRadius_le (R := Real.toNNReal (explicitEigenfunctionRadius d)) fun _ hx ↦
    (explicitEigenfunction_pos_of_le hd ((Real.le_coe_toNNReal _).trans hx)).le

/-- `r(G) < ∞`. -/
theorem signRadius_explicitSignEigenfunction_lt_top (hd : 0 < d) :
    signRadius (explicitSignEigenfunction hd) < ⊤ :=
  (signRadius_explicitSignEigenfunction_le hd).trans_lt ENNReal.ofReal_lt_top

/-- `A₋(d) < ∞` for `d ≥ 1`: `A₋(d) ≤ r(G) < ∞` for the explicit `G ∈ 𝓔₋(d)`. -/
theorem signUncertaintyConstant_neg_one_lt_top (hd : 0 < d) :
    signUncertaintyConstant (-1) d < ⊤ :=
  (signUncertaintyConstant_le (explicitSignEigenfunction hd)).trans_lt
    (signRadius_explicitSignEigenfunction_lt_top hd)

/-- `A_ς(d) < ∞` for `d ≥ 1` and both signs: `A₊(d) ≤ A₋(d) < ∞` (Appendix A of the report). -/
theorem signUncertaintyConstant_lt_top (hd : 0 < d) (ς : ℤˣ) :
    signUncertaintyConstant ς d < ⊤ := by
  rcases Int.units_eq_one_or ς with rfl | rfl
  · exact (signUncertaintyConstant_one_le_neg_one hd).trans_lt
      (signUncertaintyConstant_neg_one_lt_top hd)
  · exact signUncertaintyConstant_neg_one_lt_top hd

/-- `0 < A_ς(d) < ∞` for `d ≥ 1` and both signs. -/
theorem signUncertaintyConstant_pos_lt_top (hd : 0 < d) (ς : ℤˣ) :
    0 < signUncertaintyConstant ς d ∧ signUncertaintyConstant ς d < ⊤ :=
  ⟨signUncertaintyConstant_pos hd ς, signUncertaintyConstant_lt_top hd ς⟩

end

end CohnElkies
