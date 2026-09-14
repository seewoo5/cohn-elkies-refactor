import CohnElkies.UpperBound.Residues
import CohnElkies.UpperBound.WallisRadius

/-!
# Shell estimates for the saddle-point construction (report §4.2, Lemmas 4.2, 4.4–4.6, (45)–(48))

Uniform ratios for `P₊`, `P₋` on horizontal lines, the Gamma factors at the negative
half-integers, the domination of the short shell by the positive shell (Lemma 4.6), the short-shell
damping `D_s` (report (59)), the shell variances `V_B`, `V_s` (report (45)), the net shell variance
and third moment (report (46)), the gamma density `μ_{ℓ,η}` and its moments (report (37), (48)), the
small-radius expansion of `f₊` (Lemma 4.4), the shell phase on the imaginary axis, and the
truncated residue sum `S_N(y)` of report (78)–(79) with its tail bound.
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

/-! ### Uniform ratios for `P₊`, `P₋` on horizontal lines (Lemmas 4.2, 4.4, 4.5) -/

/-- Cubic growth of `(1 + |u|)³` against `‖P (iu)‖`, from a lower bound `b` for `‖P (iu)‖` and a
bound valid for `u > 2`.  Used for `P₊` with `(b, c) = (β, 9)` and `P₋` with `(b, c) = (3β, 6)`. -/
theorem norm_imaginary_cubic_growth {P : ℂ → ℂ} {u b c : ℝ} (hb : 0 < b) (hc : 0 ≤ c)
    (hu : -1 ≤ u) (hlow : b ≤ ‖P (I * u)‖)
    (hbig : 2 < u → (1 + u) ^ 3 ≤ c * ‖P (I * u)‖) :
    (1 + |u|) ^ 3 ≤ (27 / b + c) * ‖P (I * u)‖ := by
  have h27 : 27 / b * b = 27 := by field_simp
  have hmain : (27 : ℝ) ≤ 27 / b * ‖P (I * u)‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hlow (by positivity : (0 : ℝ) ≤ 27 / b)]
  have hc' : 0 ≤ c * ‖P (I * u)‖ := mul_nonneg hc (norm_nonneg _)
  rcases le_or_gt u 2 with h | h
  · have h0 : (0 : ℝ) ≤ |u| := abs_nonneg u
    have h2 : (0 : ℝ) ≤ 2 - |u| := by linarith [abs_le.2 (⟨by linarith, h⟩ : -2 ≤ u ∧ u ≤ 2)]
    have hcube : (1 + |u|) ^ 3 ≤ 27 := by
      nlinarith [mul_nonneg (mul_nonneg h0 h0) h2, mul_nonneg h0 h2]
    nlinarith
  · rw [abs_of_pos (by linarith : (0 : ℝ) < u)]
    nlinarith [hbig h]

/-- Lemma 4.2: `β ≤ ‖P₊(iu)‖` for `u ≥ -1`. -/
theorem plusPolynomial_imaginary_norm_ge_beta {ε u : ℝ} (hε : 0 < ε) (hu : -1 ≤ u) :
    β ε ≤ ‖PPlus ε (I * u)‖ := by
  have hb := beta_pos hε
  have hterm : 0 ≤ (1 - u) ^ 2 * (1 + u) := mul_nonneg (sq_nonneg _) (by linarith)
  have hnorm : ‖PPlus ε (I * u)‖ = |β ε + (1 - u) ^ 2 * (1 + u)| := by
    rw [plusPolynomial_imaginary]; norm_cast
  rw [hnorm, abs_of_pos (by linarith : 0 < β ε + (1 - u) ^ 2 * (1 + u))]
  linarith

/-- Lemma 4.2: `3β ≤ ‖P₋(iu)‖` for `u ≥ 1 + ε/4`. -/
theorem minusPolynomial_imaginary_norm_ge_three_beta {ε u : ℝ} (hε : 0 < ε)
    (hu : 1 + ε / 4 ≤ u) : 3 * β ε ≤ ‖PMinus ε (I * u)‖ := by
  have hb := beta_pos hε
  have hbeta : β ε ≤ u - 1 := by unfold β; linarith
  have hsq : 0 ≤ (u - 1) * ((1 + u) ^ 2 - 4) :=
    mul_nonneg (by linarith) (by nlinarith [sq_nonneg (u - 1)])
  have hnorm : ‖PMinus ε (I * u)‖ = |β ε + (1 - u) * (1 + u) ^ 2| := by
    rw [minusPolynomial_imaginary]; norm_cast
  rw [hnorm, abs_of_neg (by nlinarith : β ε + (1 - u) * (1 + u) ^ 2 < 0)]
  nlinarith

theorem plusPolynomial_imaginary_cubic_growth_le {ε u : ℝ} (hε : 0 < ε) (hu : -1 ≤ u) :
    (1 + |u|) ^ 3 ≤ (27 / β ε + 9) * ‖PPlus ε (I * u)‖ := by
  have hb := beta_pos hε
  refine norm_imaginary_cubic_growth (P := PPlus ε) hb (by norm_num) hu
    (plusPolynomial_imaginary_norm_ge_beta hε hu) fun h ↦ ?_
  have hterm : 0 ≤ (1 - u) ^ 2 * (1 + u) := mul_nonneg (sq_nonneg _) (by linarith)
  have hnorm : ‖PPlus ε (I * u)‖ = |β ε + (1 - u) ^ 2 * (1 + u)| := by
    rw [plusPolynomial_imaginary]; norm_cast
  rw [hnorm, abs_of_pos (by linarith : 0 < β ε + (1 - u) ^ 2 * (1 + u))]
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + u)
    (by linarith : (0 : ℝ) ≤ 4 * u - 2)) (by linarith : (0 : ℝ) ≤ 2 * u - 4)]

theorem minusPolynomial_imaginary_cubic_growth_le {ε u : ℝ} (hε : 0 < ε) (hu : 1 + ε / 4 ≤ u) :
    (1 + |u|) ^ 3 ≤ (9 / β ε + 6) * ‖PMinus ε (I * u)‖ := by
  have hb := beta_pos hε
  have hbeta : β ε ≤ u - 1 := by unfold β; linarith
  have hbig : 2 < u → (1 + u) ^ 3 ≤ 6 * ‖PMinus ε (I * u)‖ := fun h ↦ by
    have hsq : 0 ≤ (u - 1) * ((1 + u) ^ 2 - 4) := mul_nonneg (by linarith) (by nlinarith)
    have hnorm : ‖PMinus ε (I * u)‖ = |β ε + (1 - u) * (1 + u) ^ 2| := by
      rw [minusPolynomial_imaginary]; norm_cast
    rw [hnorm, abs_of_neg (by nlinarith : β ε + (1 - u) * (1 + u) ^ 2 < 0)]
    nlinarith [mul_nonneg (by nlinarith : (0 : ℝ) ≤ (1 + u) ^ 2 - 9)
      (by linarith : (0 : ℝ) ≤ 5 * u - 7)]
  have key := norm_imaginary_cubic_growth (P := PMinus ε) (b := 3 * β ε) (by linarith)
    (by norm_num : (0 : ℝ) ≤ 6) (by linarith)
    (minusPolynomial_imaginary_norm_ge_three_beta hε hu) hbig
  rwa [show (27 : ℝ) / (3 * β ε) = 9 / β ε from
    (div_eq_div_iff (mul_ne_zero three_ne_zero hb.ne') hb.ne').2 (by ring)] at key

/-- Lemma 4.4 in generic form: a cubic envelope for `P` plus cubic growth of `‖P (iu)‖` give a
uniform cubic bound for `‖P (T + iu)‖ / ‖P (iu)‖`. -/
theorem norm_div_norm_imaginary_le {P : ℂ → ℂ} {M c u : ℝ} (hM : 0 ≤ M)
    (hP : ∀ z : ℂ, ‖P z‖ ≤ M * (1 + ‖z‖) ^ 3)
    (hcubic : (1 + |u|) ^ 3 ≤ c * ‖P (I * u)‖) (T : ℝ) :
    ‖P ((T : ℂ) + I * u)‖ / ‖P (I * u)‖ ≤ 4 * M * c * (1 + |T| ^ 3) := by
  have hone : (1 : ℝ) ≤ (1 + |u|) ^ 3 := one_le_pow₀ (by linarith [abs_nonneg u])
  have hD : 0 < ‖P (I * u)‖ := by
    rcases (norm_nonneg (P (I * u))).eq_or_lt with h | h
    · rw [← h, mul_zero] at hcubic; linarith
    · exact h
  have htri : 1 + ‖(T : ℂ) + I * u‖ ≤ (1 + |T|) * (1 + |u|) := by
    have h : ‖(T : ℂ) + I * u‖ ≤ |T| + |u| := (norm_add_le _ _).trans_eq (by simp)
    nlinarith [mul_nonneg (abs_nonneg T) (abs_nonneg u)]
  rw [div_le_iff₀ hD]
  calc ‖P ((T : ℂ) + I * u)‖ ≤ M * (1 + ‖(T : ℂ) + I * u‖) ^ 3 := hP _
    _ ≤ M * ((1 + |T|) * (1 + |u|)) ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) htri 3) hM
    _ = M * ((1 + |T|) ^ 3 * (1 + |u|) ^ 3) := by ring
    _ ≤ M * (4 * (1 + |T| ^ 3) * (c * ‖P (I * u)‖)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ hcubic (by positivity) (by positivity)) hM
        nlinarith [mul_nonneg (sq_nonneg (|T| - 1)) (by positivity : (0 : ℝ) ≤ |T| + 1)]
    _ = 4 * M * c * (1 + |T| ^ 3) * ‖P (I * u)‖ := by ring

/-- Lemma 4.4 for `P₊`: `‖P₊(T + iu)‖ / ‖P₊(iu)‖ ≪ 1 + |T|³`, uniformly in `u ≥ -1`. -/
theorem exists_plusPolynomial_uniform_norm_ratio {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, -1 ≤ u → ∀ T : ℝ,
      ‖PPlus ε ((T : ℂ) + I * u)‖ / ‖PPlus ε (I * u)‖ ≤ C * (1 + |T| ^ 3) := by
  have hb := beta_pos hε
  exact ⟨4 * (1 + β ε) * (27 / β ε + 9), by positivity, fun u hu T ↦
    norm_div_norm_imaginary_le (P := PPlus ε) (M := 1 + β ε) (c := 27 / β ε + 9) (by positivity)
      (fun z ↦ by simpa [abs_of_pos hb] using norm_plusPolynomial_le ε z)
      (plusPolynomial_imaginary_cubic_growth_le hε hu) T⟩

/-- Lemma 4.4 for `P₋`: `‖P₋(T + iu)‖ / ‖P₋(iu)‖ ≪ 1 + |T|³`, uniformly in `u ≥ 1 + ε/4`. -/
theorem exists_minusPolynomial_uniform_norm_ratio {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 1 + ε / 4 ≤ u → ∀ T : ℝ,
      ‖PMinus ε ((T : ℂ) + I * u)‖ / ‖PMinus ε (I * u)‖ ≤ C * (1 + |T| ^ 3) := by
  have hb := beta_pos hε
  exact ⟨4 * (1 + β ε) * (9 / β ε + 6), by positivity, fun u hu T ↦
    norm_div_norm_imaginary_le (P := PMinus ε) (M := 1 + β ε) (c := 9 / β ε + 6) (by positivity)
      (fun z ↦ by simpa [abs_of_pos hb] using norm_minusPolynomial_le ε z)
      (minusPolynomial_imaginary_cubic_growth_le hε hu) T⟩

/-- Bounds for the linear and quadratic Taylor coefficients of `P₊` (`σ = I`) and `P₋`
(`σ = -I`) at a point `z`. -/
theorem norm_translation_coeffs {σ z : ℂ} (hσ : ‖σ‖ = 1) :
    ‖2 * z + σ * (1 + 3 * z ^ 2)‖ ≤ 3 * (1 + ‖z‖) ^ 2 ∧
      ‖1 + 3 * σ * z‖ ≤ 3 * (1 + ‖z‖) ^ 2 := by
  have hz := norm_nonneg z
  have hinner : ‖(1 : ℂ) + 3 * z ^ 2‖ ≤ 1 + 3 * ‖z‖ ^ 2 := by
    refine (norm_add_le _ _).trans_eq ?_
    rw [norm_mul, norm_pow]
    simp
  have h1 : ‖2 * z + σ * (1 + 3 * z ^ 2)‖ ≤ 2 * ‖z‖ + (1 + 3 * ‖z‖ ^ 2) :=
    (norm_add_le _ _).trans (add_le_add (by simp) (by rw [norm_mul, hσ, one_mul]; exact hinner))
  have h2 : ‖1 + 3 * σ * z‖ ≤ 1 + 3 * ‖z‖ :=
    (norm_add_le _ _).trans (add_le_add (by simp) (by simp [hσ]))
  exact ⟨by nlinarith, by nlinarith⟩

/-- Norm of a cubic increment `T A + T² B + C T³` with controlled coefficients. -/
theorem norm_cubic_translation_le (u T : ℝ) {A B C : ℂ} (hA : ‖A‖ ≤ 3 * (1 + |u|) ^ 2)
    (hB : ‖B‖ ≤ 3 * (1 + |u|) ^ 2) (hC : ‖C‖ ≤ 1) :
    ‖(T : ℂ) * A + (T : ℂ) ^ 2 * B + C * (T : ℂ) ^ 3‖ ≤ 9 * (1 + |u|) ^ 2 * (|T| + |T| ^ 3) := by
  have hT : (0 : ℝ) ≤ |T| := abs_nonneg T
  have hH : (1 : ℝ) ≤ (1 + |u|) ^ 2 := one_le_pow₀ (by linarith [abs_nonneg u])
  have hTsq : |T| ^ 2 ≤ |T| + |T| ^ 3 := by nlinarith [mul_nonneg hT (sq_nonneg (|T| - 1 / 2))]
  have h1 : ‖(T : ℂ) * A‖ ≤ |T| * (3 * (1 + |u|) ^ 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; gcongr
  have h2 : ‖(T : ℂ) ^ 2 * B‖ ≤ |T| ^ 2 * (3 * (1 + |u|) ^ 2) := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]; gcongr
  have h3 : ‖C * (T : ℂ) ^ 3‖ ≤ |T| ^ 3 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    simpa using mul_le_mul_of_nonneg_right hC (pow_nonneg hT 3)
  refine ((norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add h1 h2)) h3)).trans ?_
  nlinarith [mul_le_mul_of_nonneg_left hTsq (by positivity : (0 : ℝ) ≤ 3 * (1 + |u|) ^ 2),
    mul_nonneg (sub_nonneg.2 hH) (pow_nonneg hT 3),
    mul_nonneg (by linarith : (0 : ℝ) ≤ (1 + |u|) ^ 2) hT]

/-- Lemma 4.5 in generic form: the increment of `P` along the horizontal line through `iu` is
`O(|T| + |T|³)` relative to `‖P (iu)‖`. -/
theorem norm_sub_div_norm_imaginary_le {P : ℂ → ℂ} {A B C : ℂ} {c u : ℝ}
    (hA : ‖A‖ ≤ 3 * (1 + |u|) ^ 2) (hB : ‖B‖ ≤ 3 * (1 + |u|) ^ 2) (hC : ‖C‖ ≤ 1)
    (hexp : ∀ T : ℝ, P ((T : ℂ) + I * u) - P (I * u) =
      (T : ℂ) * A + (T : ℂ) ^ 2 * B + C * (T : ℂ) ^ 3)
    (hcubic : (1 + |u|) ^ 3 ≤ c * ‖P (I * u)‖) (T : ℝ) :
    ‖P ((T : ℂ) + I * u) - P (I * u)‖ / ‖P (I * u)‖ ≤ 9 * c * (|T| + |T| ^ 3) := by
  have hu0 : (0 : ℝ) ≤ |u| := abs_nonneg u
  have hone : (1 : ℝ) ≤ (1 + |u|) ^ 3 := one_le_pow₀ (by linarith)
  have hD : 0 < ‖P (I * u)‖ := by
    rcases (norm_nonneg (P (I * u))).eq_or_lt with h | h
    · rw [← h, mul_zero] at hcubic; linarith
    · exact h
  have hquad : (1 + |u|) ^ 2 ≤ c * ‖P (I * u)‖ :=
    (pow_le_pow_right₀ (by linarith) (by norm_num)).trans hcubic
  rw [div_le_iff₀ hD, hexp T]
  calc ‖(T : ℂ) * A + (T : ℂ) ^ 2 * B + C * (T : ℂ) ^ 3‖
      ≤ 9 * (1 + |u|) ^ 2 * (|T| + |T| ^ 3) := norm_cubic_translation_le u T hA hB hC
    _ ≤ 9 * (c * ‖P (I * u)‖) * (|T| + |T| ^ 3) := by gcongr
    _ = 9 * c * (|T| + |T| ^ 3) * ‖P (I * u)‖ := by ring

/-- Lemma 4.5 for `P₊`: `‖P₊(T + iu) - P₊(iu)‖ / ‖P₊(iu)‖ ≪ |T| + |T|³`. -/
theorem exists_plusPolynomial_uniform_difference_ratio {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, -1 ≤ u → ∀ T : ℝ,
      ‖PPlus ε ((T : ℂ) + I * u) - PPlus ε (I * u)‖ / ‖PPlus ε (I * u)‖ ≤
        C * (|T| + |T| ^ 3) := by
  have hb := beta_pos hε
  refine ⟨9 * (27 / β ε + 9), by positivity, fun u hu T ↦ ?_⟩
  obtain ⟨hA, hB⟩ := norm_translation_coeffs (σ := I) (z := I * (u : ℂ)) (by simp)
  rw [show ‖I * (u : ℂ)‖ = |u| by simp] at hA hB
  exact norm_sub_div_norm_imaginary_le (P := PPlus ε) (C := I) hA hB (by simp)
    (fun T ↦ by unfold PPlus; ring) (plusPolynomial_imaginary_cubic_growth_le hε hu) T

/-- Lemma 4.5 for `P₋`: `‖P₋(T + iu) - P₋(iu)‖ / ‖P₋(iu)‖ ≪ |T| + |T|³`. -/
theorem exists_minusPolynomial_uniform_difference_ratio {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 1 + ε / 4 ≤ u → ∀ T : ℝ,
      ‖PMinus ε ((T : ℂ) + I * u) - PMinus ε (I * u)‖ / ‖PMinus ε (I * u)‖ ≤
        C * (|T| + |T| ^ 3) := by
  have hb := beta_pos hε
  refine ⟨9 * (9 / β ε + 6), by positivity, fun u hu T ↦ ?_⟩
  obtain ⟨hA, hB⟩ := norm_translation_coeffs (σ := -I) (z := I * (u : ℂ)) (by simp)
  rw [show ‖I * (u : ℂ)‖ = |u| by simp] at hA hB
  exact norm_sub_div_norm_imaginary_le (P := PMinus ε) (C := -I) hA hB (by simp)
    (fun T ↦ by unfold PMinus; ring) (minusPolynomial_imaginary_cubic_growth_le hε hu) T

/-! ### The Gamma factors at the negative half-integers -/

/-- The Gamma argument `-(N + 1/2) - i s/2` at the `N`-th negative half-integer pole. -/
def upperNegativeHalfGammaArgument (N : ℕ) (s : ℝ) : ℂ :=
  -((N : ℂ) + 1 / 2) - I * (s / 2 : ℂ)

theorem upperNegativeHalfGammaArgument_ne_zero (N : ℕ) (s : ℝ) :
    upperNegativeHalfGammaArgument N s ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  simp [upperNegativeHalfGammaArgument] at hre
  linarith

theorem upperNegativeHalfGammaArgument_succ_add_one (N : ℕ) (s : ℝ) :
    upperNegativeHalfGammaArgument (N + 1) s + 1 = upperNegativeHalfGammaArgument N s := by
  unfold upperNegativeHalfGammaArgument
  push_cast
  ring

/-! ### Domination of the short shell by the positive shell (Lemma 4.6) -/

/-- `ε (1 + A_ε) → 0` as `ε ↓ 0`, where `A_ε = log (1/ε)`. -/
theorem tendsto_mul_one_add_shortEndpoint :
    Tendsto (fun ε : ℝ ↦ ε * (1 + Aε ε)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hlog := tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 1)
  simp only [Real.rpow_one] at hlog
  have hshort : Tendsto (fun ε : ℝ ↦ ε * Aε ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert! hlog.const_mul (-1 : ℝ) using 1
    · ext ε
      unfold Aε
      rw [one_div, Real.log_inv]
      ring
    · norm_num
  have hid : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  convert! hid.add hshort using 1
  · ext ε
    ring
  · norm_num

/-- Lemma 4.6: the short-shell margin `b_ε(a)` stays above `1/2` on `[a₀, A]` for small `ε`. -/
theorem eventually_upper_shortMargin_positive : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    ∀ a ∈ Set.Icc (a₀ε ε) (Aε ε), (1 / 2 : ℝ) ≤ bε ε a := by
  filter_upwards [self_mem_nhdsWithin,
    (tendsto_mul_one_add_shortEndpoint.const_mul (2 : ℝ)).eventually
      (Iio_mem_nhds (by norm_num : (2 : ℝ) * 0 < 1 / 2))] with ε hε hbound a ha
  change 0 < ε at hε
  change 2 * (ε * (1 + Aε ε)) < 1 / 2 at hbound
  unfold bε
  nlinarith [mul_le_mul_of_nonneg_left (show 1 + a ≤ 1 + Aε ε by linarith [ha.2]) hε.le]

/-- For small `ε` the positive shell `[B, B + 1]` lies beyond the short-shell endpoint `A`. -/
theorem eventually_upper_shellLocation_gt_shortEndpoint : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    Aε ε + 1 < Bε ε := by
  have hid : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hpow : Tendsto (fun ε : ℝ ↦ ε ^ 2 * (ε * (1 + Aε ε))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (hid.pow 2).mul tendsto_mul_one_add_shortEndpoint
  filter_upwards [self_mem_nhdsWithin,
    hpow.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with ε hε hbound
  change 0 < ε at hε
  change ε ^ 2 * (ε * (1 + Aε ε)) < 1 at hbound
  have hinv : ε ^ 3 * Bε ε = 1 := by unfold Bε; field_simp
  nlinarith [pow_pos hε 3]

/-- The size `A_ε + a₀_ε⁻¹` of the short shell. -/
def upperShellShortCoefficient (ε : ℝ) : ℝ := Aε ε + (a₀ε ε)⁻¹

/-- The ratio of report (61) comparing the short shell with the positive shell. -/
def upperShellMarginRatio (ε : ℝ) : ℝ :=
  5000 * upperShellShortCoefficient ε * Real.exp (ε / 2 * Aε ε) /
    (Qε ε * Real.exp (ε / 2 * Bε ε))

theorem tendsto_upperShellMarginRatio : Tendsto upperShellMarginRatio (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hcubic : Tendsto (fun x : ℝ ↦ (Real.log x + x ^ 2) * Real.exp (-(x ^ 2) / 8))
      atTop (𝓝 0) := by
    have hupper : Tendsto (fun x : ℝ ↦ 11 * ((x ^ 3 + 1) * Real.exp (-(x ^ 2) / 8)))
        atTop (𝓝 0) := by simpa using tendsto_cubic_gaussian_atTop.const_mul (11 : ℝ)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds (x := (0 : ℝ))) hupper ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hx0 : (0 : ℝ) < x := by linarith
      have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
      positivity
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hx0 : (0 : ℝ) < x := by linarith
      have hlog := Real.log_le_sub_one_of_pos hx0
      have hsquare : (0 : ℝ) ≤ x ^ 2 - 1 := by nlinarith [sq_nonneg (x - 1)]
      have hfactor : Real.log x + x ^ 2 ≤ 11 * (x ^ 3 + 1) := by
        nlinarith [mul_nonneg hx0.le hsquare, mul_nonneg (sq_nonneg x) (sub_nonneg.2 hx)]
      calc (Real.log x + x ^ 2) * Real.exp (-(x ^ 2) / 8)
          ≤ 11 * (x ^ 3 + 1) * Real.exp (-(x ^ 2) / 8) :=
            mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le
        _ = 11 * ((x ^ 3 + 1) * Real.exp (-(x ^ 2) / 8)) := by ring
  have hcorr : Tendsto (fun x : ℝ ↦ Real.exp (Real.log x / (2 * x))) atTop (𝓝 1) := by
    have hlog : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num : (1 : ℝ) ≠ 0)
    have hscaled : Tendsto (fun x : ℝ ↦ Real.log x / (2 * x)) atTop (𝓝 0) := by
      convert! hlog.const_mul (1 / 2 : ℝ) using 1
      · ext x
        ring
      · norm_num
    simpa using hscaled.rexp
  have hproduct : Tendsto (fun x : ℝ ↦ 5000 * ((Real.log x + x ^ 2) *
      Real.exp (-(x ^ 2) / 8)) * Real.exp (Real.log x / (2 * x))) atTop (𝓝 0) := by
    simpa using (hcubic.const_mul (5000 : ℝ)).mul hcorr
  refine tendsto_nhdsGT_zero_of_comp_inv_tendsto_atTop (hproduct.congr' ?_)
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
  have hA : Aε x⁻¹ = Real.log x := by simp [Aε]
  have hB : Bε x⁻¹ = x ^ 3 := by simp [Bε]
  have hQ : Qε x⁻¹ = Real.exp (-(3 : ℝ) * x ^ 2 / 8) := by
    unfold Qε
    rw [hB]
    congr 1
    field_simp [hx]
  have hsplit : Real.exp (x⁻¹ / 2 * Real.log x) =
      Real.exp (-(x ^ 2) / 8) * Real.exp (Real.log x / (2 * x)) *
        (Real.exp (-(3 : ℝ) * x ^ 2 / 8) * Real.exp (x⁻¹ / 2 * x ^ 3)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  unfold upperShellMarginRatio upperShellShortCoefficient
  rw [hA, hB, hQ, show (a₀ε x⁻¹)⁻¹ = x ^ 2 by simp [a₀ε], eq_div_iff (by positivity), hsplit]
  ring

/-- Lemma 4.6: for small `ε` the short shell carries at most `1/5000` of the positive shell. -/
theorem eventually_upper_shell_parameter_margin : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    upperShellShortCoefficient ε * Real.exp ((ε / 2) * Aε ε) ≤
      (1 / 5000 : ℝ) * Qε ε * Real.exp ((ε / 2) * Bε ε) := by
  filter_upwards [tendsto_upperShellMarginRatio.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with ε hε
  unfold upperShellMarginRatio at hε
  have hden : 0 < Qε ε * Real.exp (ε / 2 * Bε ε) :=
    mul_pos (shellWeight_pos ε) (Real.exp_pos _)
  nlinarith [(div_lt_one hden).mp hε]

/-! ### The short-shell damping `D_s` (report (59)) -/

/-- The short-shell cutoff `a₀ = ε²` is positive. -/
theorem shortCutoff_pos {ε : ℝ} (hε : 0 < ε) : 0 < a₀ε ε := by unfold a₀ε; positivity

/-- The short-shell density `w_s ε` is continuous on the short shell `[a₀, A]`. -/
theorem continuousOn_shortShellDensity {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (w_s ε) (Set.Icc (a₀ε ε) (Aε ε)) := by
  have hn : Continuous fun a : ℝ ↦ bε ε a * Real.exp (-2 * a) := by unfold bε; fun_prop
  have hd : Continuous fun a : ℝ ↦ 2 * a ^ 2 * Real.cosh a := by fun_prop
  unfold w_s
  exact (hn.continuousOn.div hd.continuousOn fun a ha ↦ by
    have : 0 < a := (shortCutoff_pos hε).trans_le ha.1
    positivity).neg

/-- `w_s ε a ≤ 0` wherever the short-shell margin `b_ε(a)` is nonnegative. -/
theorem neg_shortShellDensity_nonneg {ε a : ℝ} (ha : 0 < a) (hb : 0 ≤ bε ε a) :
    0 ≤ -w_s ε a := by
  unfold w_s
  simpa using div_nonneg (mul_nonneg hb (Real.exp_pos _).le)
    (by positivity : (0 : ℝ) ≤ 2 * a ^ 2 * Real.cosh a)

theorem upper_min_frequency_inverse_sq_le {a : ℝ} (ha : 0 < a) (T : ℝ) :
    min (T ^ 2) ((a ^ 2)⁻¹) ≤ min (T ^ 2) 1 * (1 + (a ^ 2)⁻¹) := by
  have hinv : (0 : ℝ) ≤ (a ^ 2)⁻¹ := by positivity
  rcases le_or_gt (T ^ 2) 1 with hsmall | hsmall
  · rw [min_eq_left hsmall]
    nlinarith [min_le_left (T ^ 2) ((a ^ 2)⁻¹), mul_nonneg (sq_nonneg T) hinv]
  · rw [min_eq_right hsmall.le]
    nlinarith [min_le_right (T ^ 2) ((a ^ 2)⁻¹)]

/-- Damping `D_s(T)` produced by the short shell on the contour of height `1 + δ`. -/
def D_s (ε ℓ δ T : ℝ) : ℝ :=
  ℓ * ∫ a in a₀ε ε..Aε ε, (-w_s ε a) * Real.cosh ((1 + δ) * a) * (1 - Real.cos (a * T))

theorem upper_shortShell_oscillation_div_sq_le {a : ℝ} (ha : 0 < a) (T : ℝ) :
    (1 - Real.cos (a * T)) / (2 * a ^ 2) ≤ min (T ^ 2) ((a ^ 2)⁻¹) := by
  have hden : (0 : ℝ) < 2 * a ^ 2 := by positivity
  have hquad : 1 - Real.cos (a * T) ≤ (a * T) ^ 2 / 2 := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := a * T)]
  have htwo : 1 - Real.cos (a * T) ≤ 2 := by linarith [Real.neg_one_le_cos (a * T)]
  refine le_min ?_ ?_
  · calc (1 - Real.cos (a * T)) / (2 * a ^ 2) ≤ (a * T) ^ 2 / 2 / (2 * a ^ 2) := by gcongr
      _ = T ^ 2 / 4 := by field_simp; ring
      _ ≤ T ^ 2 := by nlinarith [sq_nonneg T]
  · calc (1 - Real.cos (a * T)) / (2 * a ^ 2) ≤ 2 / (2 * a ^ 2) := by gcongr
      _ = (a ^ 2)⁻¹ := by field_simp

theorem upper_shortShellDensity_damping_le {ε δ a A : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ)
    (ha : 0 < a) (haA : a ≤ A) (hmargin : 0 ≤ bε ε a) (T : ℝ) :
    (-w_s ε a) * Real.cosh ((1 + δ) * a) * (1 - Real.cos (a * T)) ≤
      Real.exp (δ * A) * min (T ^ 2) 1 * (1 + (a ^ 2)⁻¹) := by
  have hmarginone : bε ε a ≤ 1 := by
    unfold bε
    nlinarith [mul_nonneg hε.le (show (0 : ℝ) ≤ 1 + a by linarith)]
  have hnegativeexp : Real.exp (-2 * a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hratio : Real.cosh ((1 + δ) * a) / Real.cosh a ≤ Real.exp (δ * A) :=
    (cosh_ratio_upper ha.le hδ).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left haA hδ))
  have hosc_nonneg : (0 : ℝ) ≤ (1 - Real.cos (a * T)) / (2 * a ^ 2) :=
    div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (by positivity)
  rw [show (-w_s ε a) * Real.cosh ((1 + δ) * a) * (1 - Real.cos (a * T)) =
      bε ε a * Real.exp (-2 * a) * (Real.cosh ((1 + δ) * a) / Real.cosh a) *
        ((1 - Real.cos (a * T)) / (2 * a ^ 2)) by
    unfold w_s; field_simp [ha.ne', (Real.cosh_pos a).ne']]
  calc bε ε a * Real.exp (-2 * a) * (Real.cosh ((1 + δ) * a) / Real.cosh a) *
        ((1 - Real.cos (a * T)) / (2 * a ^ 2))
      ≤ bε ε a * Real.exp (-2 * a) * Real.exp (δ * A) *
        ((1 - Real.cos (a * T)) / (2 * a ^ 2)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hratio (mul_nonneg hmargin (Real.exp_pos _).le)) hosc_nonneg
    _ ≤ (1 : ℝ) * 1 * Real.exp (δ * A) * min (T ^ 2) ((a ^ 2)⁻¹) := by
        gcongr
        exact upper_shortShell_oscillation_div_sq_le ha T
    _ = Real.exp (δ * A) * min (T ^ 2) ((a ^ 2)⁻¹) := by ring
    _ ≤ Real.exp (δ * A) * (min (T ^ 2) 1 * (1 + (a ^ 2)⁻¹)) :=
        mul_le_mul_of_nonneg_left (upper_min_frequency_inverse_sq_le ha T) (Real.exp_pos _).le
    _ = Real.exp (δ * A) * min (T ^ 2) 1 * (1 + (a ^ 2)⁻¹) := by ring

theorem upper_intervalIntegral_one_add_inv_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, 1 + (x ^ 2)⁻¹) = b - a + a⁻¹ - b⁻¹ := by
  have hcont : ContinuousOn (fun x : ℝ ↦ 1 + (x ^ 2)⁻¹) (Set.Icc a b) :=
    continuousOn_const.add ((continuous_id.pow 2).continuousOn.inv₀ fun x hx ↦
      (pow_pos (ha.trans_le hx.1) 2).ne')
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y : ℝ ↦ y - y⁻¹)
      (fun x hx ↦ by
        have hxpos : 0 < x := ha.trans_le ((Set.uIcc_of_le hab ▸ hx : x ∈ Set.Icc a b)).1
        convert! (hasDerivAt_id x).sub (hasDerivAt_inv hxpos.ne') using 1
        ring)
      (hcont.intervalIntegrable_of_Icc hab)]
  ring

/-- Report (59): the short shell contributes at most `λ (A + a₀⁻¹) e^{δA} min(T², 1)`. -/
theorem upperShortShellDamping_global_bound {ε ℓ δ T : ℝ} (hε : 0 < ε) (hℓ : 0 ≤ ℓ) (hδ : 0 ≤ δ)
    (horder : a₀ε ε ≤ Aε ε) (hmargin : ∀ a ∈ Set.Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a) :
    D_s ε ℓ δ T ≤ ℓ * upperShellShortCoefficient ε * Real.exp (δ * Aε ε) * min (T ^ 2) 1 := by
  have ha₀ := shortCutoff_pos hε
  have hA : 0 < Aε ε := ha₀.trans_le horder
  have hK : (0 : ℝ) ≤ Real.exp (δ * Aε ε) * min (T ^ 2) 1 :=
    mul_nonneg (Real.exp_pos _).le (le_min (sq_nonneg T) (by norm_num))
  have hleft : ContinuousOn (fun a : ℝ ↦ (-w_s ε a) * Real.cosh ((1 + δ) * a) *
      (1 - Real.cos (a * T))) (Set.Icc (a₀ε ε) (Aε ε)) :=
    ((continuousOn_shortShellDensity hε).neg.mul (by fun_prop : Continuous fun a : ℝ ↦
      Real.cosh ((1 + δ) * a)).continuousOn).mul
      (by fun_prop : Continuous fun a : ℝ ↦ 1 - Real.cos (a * T)).continuousOn
  have hright : ContinuousOn (fun a : ℝ ↦ Real.exp (δ * Aε ε) * min (T ^ 2) 1 *
      (1 + (a ^ 2)⁻¹)) (Set.Icc (a₀ε ε) (Aε ε)) :=
    continuousOn_const.mul (continuousOn_const.add
      ((continuous_id.pow 2).continuousOn.inv₀ fun a ha ↦ (pow_pos (ha₀.trans_le ha.1) 2).ne'))
  have hmono := intervalIntegral.integral_mono_on (μ := volume) horder
    (hleft.intervalIntegrable_of_Icc horder) (hright.intervalIntegrable_of_Icc horder)
    fun a ha ↦ upper_shortShellDensity_damping_le hε hδ (ha₀.trans_le ha.1) ha.2 (hmargin a ha) T
  rw [intervalIntegral.integral_const_mul,
    upper_intervalIntegral_one_add_inv_sq ha₀ horder] at hmono
  have hcoefficient : Aε ε - a₀ε ε + (a₀ε ε)⁻¹ - (Aε ε)⁻¹ ≤ Aε ε + (a₀ε ε)⁻¹ := by
    have := (inv_pos.mpr hA).le
    linarith
  unfold D_s upperShellShortCoefficient
  calc ℓ * ∫ a in a₀ε ε..Aε ε, (-w_s ε a) * Real.cosh ((1 + δ) * a) * (1 - Real.cos (a * T))
      ≤ ℓ * (Real.exp (δ * Aε ε) * min (T ^ 2) 1 *
        (Aε ε - a₀ε ε + (a₀ε ε)⁻¹ - (Aε ε)⁻¹)) := mul_le_mul_of_nonneg_left hmono hℓ
    _ ≤ ℓ * (Real.exp (δ * Aε ε) * min (T ^ 2) 1 * (Aε ε + (a₀ε ε)⁻¹)) := by gcongr
    _ = ℓ * (Aε ε + (a₀ε ε)⁻¹) * Real.exp (δ * Aε ε) * min (T ^ 2) 1 := by ring

/-- For small `ε` the short shell `[a₀, A]` is nonempty. -/
theorem eventually_upper_shortCutoff_le_shortEndpoint : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    a₀ε ε ≤ Aε ε := by
  filter_upwards [tendsto_shortCutoff.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    tendsto_shortEndpoint.eventually_ge_atTop (1 : ℝ)] with ε hl hu
  linarith

/-- Propagation of the margin of Lemma 4.6 from `δ = ε/2` to any larger `δ`. -/
theorem upper_shell_parameter_margin_propagate {ε δ : ℝ} (hδ : ε / 2 ≤ δ)
    (hseparation : Aε ε ≤ Bε ε)
    (hmargin : upperShellShortCoefficient ε * Real.exp ((ε / 2) * Aε ε) ≤
        (1 / 5000 : ℝ) * Qε ε * Real.exp ((ε / 2) * Bε ε)) :
    upperShellShortCoefficient ε * Real.exp (δ * Aε ε) ≤ (1 / 5000 : ℝ) * Qε ε *
        Real.exp (δ * Bε ε) := by
  have hexp : Real.exp ((δ - ε / 2) * Aε ε) ≤ Real.exp ((δ - ε / 2) * Bε ε) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hseparation (by linarith))
  have hfactor : (0 : ℝ) ≤ (1 / 5000 : ℝ) * Qε ε * Real.exp ((ε / 2) * Bε ε) :=
    mul_nonneg (mul_nonneg (by norm_num) (shellWeight_pos ε).le) (Real.exp_pos _).le
  calc upperShellShortCoefficient ε * Real.exp (δ * Aε ε)
      = upperShellShortCoefficient ε * Real.exp ((ε / 2) * Aε ε) *
        Real.exp ((δ - ε / 2) * Aε ε) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
    _ ≤ (1 / 5000 : ℝ) * Qε ε * Real.exp ((ε / 2) * Bε ε) * Real.exp ((δ - ε / 2) * Aε ε) :=
        mul_le_mul_of_nonneg_right hmargin (Real.exp_pos _).le
    _ ≤ (1 / 5000 : ℝ) * Qε ε * Real.exp ((ε / 2) * Bε ε) * Real.exp ((δ - ε / 2) * Bε ε) :=
        mul_le_mul_of_nonneg_left hexp hfactor
    _ = (1 / 5000 : ℝ) * Qε ε * Real.exp (δ * Bε ε) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-- Report (61): the short-shell damping is at most `1/100` of the positive-shell damping. -/
theorem eventually_upper_shortShell_domination : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ ℓ : ℝ, 0 ≤ ℓ →
    ∀ δ : ℝ, ε / 2 ≤ δ → ∀ T : ℝ, D_s ε ℓ δ T ≤ (1 / 100 : ℝ) * D_B ε ℓ δ T := by
  filter_upwards [self_mem_nhdsWithin, eventually_upper_shortCutoff_le_shortEndpoint,
      eventually_upper_shortMargin_positive,
      eventually_upper_shellLocation_gt_shortEndpoint,
      eventually_upper_shell_parameter_margin]
    with ε hε horder hshortmargin hseparation hmargin
  change 0 < ε at hε
  intro ℓ hℓ δ hδ T
  have hδnonneg : 0 ≤ δ := by nlinarith
  have hshort := upperShortShellDamping_global_bound (T := T) hε hℓ hδnonneg horder
    fun a ha ↦ by linarith [hshortmargin a ha]
  have hpropagate := upper_shell_parameter_margin_propagate hδ (by linarith) hmargin
  have hpositive := positiveShellDamping_lower_bound (ε := ε) (ℓ := ℓ) (δ := δ) (T := T)
      hε hℓ hδnonneg
  have hfreq : (0 : ℝ) ≤ min (T ^ 2) 1 := le_min (sq_nonneg T) (by norm_num)
  calc D_s ε ℓ δ T ≤ ℓ * upperShellShortCoefficient ε * Real.exp (δ * Aε ε) * min (T ^ 2) 1 :=
        hshort
    _ ≤ ℓ * ((1 / 5000 : ℝ) * Qε ε * Real.exp (δ * Bε ε)) * min (T ^ 2) 1 := by
        convert! mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpropagate hℓ)
          hfreq using 1; ring
    _ = (1 / 100 : ℝ) * (ℓ / 50 * Qε ε * Real.exp (δ * Bε ε) * min (T ^ 2) 1) := by ring
    _ ≤ (1 / 100 : ℝ) * D_B ε ℓ δ T := mul_le_mul_of_nonneg_left hpositive (by norm_num)

/-! ### The shell variances `V_B`, `V_s` (report (45)) -/

/-- Variance `V_B` carried by the positive shell on the contour of height `1 + δ`. -/
def V_B (ε δ : ℝ) : ℝ := ∫ a in Bε ε..Bε ε + 1, w_B ε a * a ^ 2 * Real.cosh ((1 + δ) * a)

/-- Report (45): two-sided bounds for the positive-shell variance `V_B`. -/
theorem upperPositiveShellVariance_bounds {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) :
    (1 / 2 : ℝ) * (Bε ε) ^ 2 * Qε ε * Real.exp (δ * Bε ε) ≤ V_B ε δ ∧
      V_B ε δ ≤ (Bε ε + 1) ^ 2 * Qε ε * Real.exp (δ * (Bε ε + 1)) := by
  have hB : (0 : ℝ) ≤ Bε ε := by unfold Bε; positivity
  have hQ : 0 < Qε ε := shellWeight_pos ε
  have horder : Bε ε ≤ Bε ε + 1 := by linarith
  have hcont : Continuous fun a : ℝ ↦ w_B ε a * a ^ 2 * Real.cosh ((1 + δ) * a) := by
    have hdensity := positiveShellDensity_continuous ε
    fun_prop
  have hlopoint : ∀ a ∈ Set.Icc (Bε ε) (Bε ε + 1),
      (1 / 2 : ℝ) * (Bε ε) ^ 2 * Qε ε * Real.exp (δ * Bε ε) ≤
        w_B ε a * a ^ 2 * Real.cosh ((1 + δ) * a) := by
    intro a ha
    have ha0 : (0 : ℝ) ≤ a := hB.trans ha.1
    have hsquare : (Bε ε) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hB ha.1 2
    have hexp : Real.exp (δ * Bε ε) ≤ Real.exp (δ * a) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ha.1 hδ)
    have hratio : Real.exp (δ * Bε ε) / 2 ≤ Real.cosh ((1 + δ) * a) / Real.cosh a :=
      le_trans (by linarith) (cosh_ratio_lower ha0 hδ)
    calc (1 / 2 : ℝ) * (Bε ε) ^ 2 * Qε ε * Real.exp (δ * Bε ε)
        = Qε ε * (Bε ε) ^ 2 * (Real.exp (δ * Bε ε) / 2) := by ring
      _ ≤ Qε ε * a ^ 2 * (Real.cosh ((1 + δ) * a) / Real.cosh a) := by gcongr
      _ = w_B ε a * a ^ 2 * Real.cosh ((1 + δ) * a) := by unfold w_B; ring
  have hhipoint : ∀ a ∈ Set.Icc (Bε ε) (Bε ε + 1),
      w_B ε a * a ^ 2 * Real.cosh ((1 + δ) * a) ≤
        (Bε ε + 1) ^ 2 * Qε ε * Real.exp (δ * (Bε ε + 1)) := by
    intro a ha
    have ha0 : (0 : ℝ) ≤ a := hB.trans ha.1
    have hsquare : a ^ 2 ≤ (Bε ε + 1) ^ 2 := pow_le_pow_left₀ ha0 ha.2 2
    have hratio : Real.cosh ((1 + δ) * a) / Real.cosh a ≤ Real.exp (δ * (Bε ε + 1)) :=
      (cosh_ratio_upper ha0 hδ).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ha.2 hδ))
    calc w_B ε a * a ^ 2 * Real.cosh ((1 + δ) * a)
        = Qε ε * a ^ 2 * (Real.cosh ((1 + δ) * a) / Real.cosh a) := by unfold w_B; ring
      _ ≤ Qε ε * (Bε ε + 1) ^ 2 * Real.exp (δ * (Bε ε + 1)) := by gcongr
      _ = (Bε ε + 1) ^ 2 * Qε ε * Real.exp (δ * (Bε ε + 1)) := by ring
  unfold V_B
  refine ⟨?_, ?_⟩
  · simpa using intervalIntegral.integral_mono_on (μ := volume) horder intervalIntegrable_const
      (hcont.intervalIntegrable _ _) hlopoint
  · simpa using intervalIntegral.integral_mono_on (μ := volume) horder
      (hcont.intervalIntegrable _ _) intervalIntegrable_const hhipoint

/-- Variance `V_s` carried by the short shell on the contour of height `1 + δ`. -/
def V_s (ε δ : ℝ) : ℝ := ∫ a in a₀ε ε..Aε ε, (-w_s ε a) * a ^ 2 * Real.cosh ((1 + δ) * a)

theorem upper_shortShellDensity_variance_le {ε δ a A : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ)
    (ha : 0 < a) (haA : a ≤ A) :
    (-w_s ε a) * a ^ 2 * Real.cosh ((1 + δ) * a) ≤ (1 / 2 : ℝ) * Real.exp (δ * A) := by
  have hmargin : bε ε a ≤ 1 := by
    unfold bε
    nlinarith [mul_nonneg hε.le (show (0 : ℝ) ≤ 1 + a by linarith)]
  have hexp : Real.exp (-2 * a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hratio : Real.cosh ((1 + δ) * a) / Real.cosh a ≤ Real.exp (δ * A) :=
    (cosh_ratio_upper ha.le hδ).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left haA hδ))
  rw [show (-w_s ε a) * a ^ 2 * Real.cosh ((1 + δ) * a) = (1 / 2 : ℝ) * bε ε a *
      Real.exp (-2 * a) * (Real.cosh ((1 + δ) * a) / Real.cosh a) by
    unfold w_s; field_simp [ha.ne', (Real.cosh_pos a).ne']]
  calc (1 / 2 : ℝ) * bε ε a * Real.exp (-2 * a) * (Real.cosh ((1 + δ) * a) / Real.cosh a)
      ≤ (1 / 2 : ℝ) * 1 * 1 * Real.exp (δ * A) := by gcongr
    _ = (1 / 2 : ℝ) * Real.exp (δ * A) := by ring

/-- Report (45): the short-shell variance is at most `(A + a₀⁻¹) e^{δA} / 2`. -/
theorem upperShortShellVariance_global_bound {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ)
    (horder : a₀ε ε ≤ Aε ε) :
    V_s ε δ ≤ (1 / 2 : ℝ) * upperShellShortCoefficient ε * Real.exp (δ * Aε ε) := by
  have ha₀ := shortCutoff_pos hε
  have hK : (0 : ℝ) ≤ (1 / 2 : ℝ) * Real.exp (δ * Aε ε) := by positivity
  have hleft : ContinuousOn (fun a : ℝ ↦ (-w_s ε a) * a ^ 2 * Real.cosh ((1 + δ) * a))
      (Set.Icc (a₀ε ε) (Aε ε)) :=
    ((continuousOn_shortShellDensity hε).neg.mul (continuous_id.pow 2).continuousOn).mul
      (by fun_prop : Continuous fun a : ℝ ↦ Real.cosh ((1 + δ) * a)).continuousOn
  have hmono := intervalIntegral.integral_mono_on (μ := volume) horder
    (hleft.intervalIntegrable_of_Icc horder) intervalIntegrable_const
    fun a ha ↦ upper_shortShellDensity_variance_le hε hδ (ha₀.trans_le ha.1) ha.2
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  unfold V_s upperShellShortCoefficient
  calc (∫ a in a₀ε ε..Aε ε, (-w_s ε a) * a ^ 2 * Real.cosh ((1 + δ) * a))
      ≤ (Aε ε - a₀ε ε) * ((1 / 2 : ℝ) * Real.exp (δ * Aε ε)) := hmono
    _ ≤ (Aε ε + (a₀ε ε)⁻¹) * ((1 / 2 : ℝ) * Real.exp (δ * Aε ε)) :=
        mul_le_mul_of_nonneg_right (by linarith [(inv_pos.mpr ha₀).le]) hK
    _ = (1 / 2 : ℝ) * (Aε ε + (a₀ε ε)⁻¹) * Real.exp (δ * Aε ε) := by ring

end

noncomputable section
open Filter MeasureTheory Set
open scoped Topology

/-! ### The net shell variance and third moment (report (46)) -/

/-- The short-shell variance is nonnegative when the margin `b_ε` is. -/
theorem upperShortShellVariance_nonneg {ε δ : ℝ} (hε : 0 < ε) (horder : a₀ε ε ≤ Aε ε)
    (hmargin : ∀ a ∈ Set.Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a) : 0 ≤ V_s ε δ := by
  unfold V_s
  exact intervalIntegral.integral_nonneg horder fun a ha ↦ mul_nonneg (mul_nonneg
    (neg_shortShellDensity_nonneg ((shortCutoff_pos hε).trans_le ha.1) (hmargin a ha))
    (sq_nonneg a)) (Real.cosh_pos _).le

/-- The short-shell variance is at most `1/100` of the positive-shell variance. -/
theorem eventually_upper_shortShellVariance_domination : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    ∀ δ : ℝ, ε / 2 ≤ δ → V_s ε δ ≤ (1 / 100 : ℝ) * V_B ε δ := by
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < 1 :=
    (tendsto_id.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin, hsmall, eventually_upper_shortCutoff_le_shortEndpoint,
      eventually_upper_shellLocation_gt_shortEndpoint, eventually_upper_shell_parameter_margin]
    with ε hε hεone horder hseparation hmargin
  change 0 < ε at hε
  change ε < 1 at hεone
  intro δ hδ
  have hδnonneg : 0 ≤ δ := by nlinarith
  have hB : 1 ≤ Bε ε := by
    have hinv : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).mpr hεone.le
    unfold Bε
    calc (1 : ℝ) = 1 ^ 3 := (one_pow 3).symm
      _ ≤ (ε⁻¹) ^ 3 := pow_le_pow_left₀ zero_le_one hinv 3
  have hBsq : 1 ≤ (Bε ε) ^ 2 := by nlinarith
  have hpropagate := upper_shell_parameter_margin_propagate hδ (by linarith) hmargin
  have hqexp : (0 : ℝ) ≤ Qε ε * Real.exp (δ * Bε ε) :=
    mul_nonneg (shellWeight_pos ε).le (Real.exp_pos _).le
  calc V_s ε δ ≤ (1 / 2 : ℝ) * upperShellShortCoefficient ε * Real.exp (δ * Aε ε) :=
        upperShortShellVariance_global_bound hε hδnonneg horder
    _ ≤ (1 / 2 : ℝ) * ((1 / 5000 : ℝ) * Qε ε * Real.exp (δ * Bε ε)) := by
        convert! mul_le_mul_of_nonneg_left hpropagate (by norm_num : (0 : ℝ) ≤ 1 / 2) using 1
        ring
    _ ≤ (1 / 100 : ℝ) * ((1 / 2 : ℝ) * (Bε ε) ^ 2 * Qε ε * Real.exp (δ * Bε ε)) := by
        nlinarith [mul_le_mul_of_nonneg_right hBsq hqexp]
    _ ≤ (1 / 100 : ℝ) * V_B ε δ :=
        mul_le_mul_of_nonneg_left (upperPositiveShellVariance_bounds hε hδnonneg).1 (by norm_num)

/-- The net shell variance `V_B - V_s` of report (46). -/
def upperNetShellVariance (ε δ : ℝ) : ℝ := V_B ε δ - V_s ε δ

/-- Report (46): the net shell variance is between `99/100` and `1` times `V_B`. -/
theorem eventually_upper_netShellVariance_bounds : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ δ : ℝ, ε / 2 ≤ δ →
    (99 / 100 : ℝ) * V_B ε δ ≤ upperNetShellVariance ε δ ∧ upperNetShellVariance ε δ ≤ V_B ε δ := by
  filter_upwards [self_mem_nhdsWithin, eventually_upper_shortCutoff_le_shortEndpoint,
      eventually_upper_shortMargin_positive, eventually_upper_shortShellVariance_domination]
    with ε hε horder hmargin hdom
  change 0 < ε at hε
  intro δ hδ
  have hnonneg := upperShortShellVariance_nonneg (δ := δ) hε horder
    fun a ha ↦ by linarith [hmargin a ha]
  have hupper := hdom δ hδ
  unfold upperNetShellVariance
  constructor <;> nlinarith

/-- Third moment carried by the positive shell on the contour of height `1 + δ`. -/
def upperPositiveShellThirdMoment (ε δ : ℝ) : ℝ :=
  ∫ a in Bε ε..Bε ε + 1, w_B ε a * a ^ 3 * Real.cosh ((1 + δ) * a)

/-- On `[a, b]`, the third moment of a nonnegative shell density is at most `b` times its
second moment. -/
theorem intervalIntegral_thirdMoment_le {w : ℝ → ℝ} {a b δ : ℝ} (hab : a ≤ b)
    (hw : ∀ x ∈ Set.Icc a b, 0 ≤ w x) (hc : ContinuousOn w (Set.Icc a b)) :
    (∫ x in a..b, w x * x ^ 3 * Real.cosh ((1 + δ) * x)) ≤
      b * ∫ x in a..b, w x * x ^ 2 * Real.cosh ((1 + δ) * x) := by
  have hcosh : Continuous fun x : ℝ ↦ Real.cosh ((1 + δ) * x) := by fun_prop
  have hsq : ContinuousOn (fun x : ℝ ↦ w x * x ^ 2 * Real.cosh ((1 + δ) * x)) (Set.Icc a b) :=
    (hc.mul (continuous_id.pow 2).continuousOn).mul hcosh.continuousOn
  have hcu : ContinuousOn (fun x : ℝ ↦ w x * x ^ 3 * Real.cosh ((1 + δ) * x)) (Set.Icc a b) :=
    (hc.mul (continuous_id.pow 3).continuousOn).mul hcosh.continuousOn
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hab
    (hcu.intervalIntegrable_of_Icc hab)
    ((continuousOn_const.mul hsq).intervalIntegrable_of_Icc hab) fun x hx ↦ by
      have hnonneg : (0 : ℝ) ≤ w x * x ^ 2 * Real.cosh ((1 + δ) * x) :=
        mul_nonneg (mul_nonneg (hw x hx) (sq_nonneg x)) (Real.cosh_pos _).le
      calc w x * x ^ 3 * Real.cosh ((1 + δ) * x)
          = x * (w x * x ^ 2 * Real.cosh ((1 + δ) * x)) := by ring
        _ ≤ b * (w x * x ^ 2 * Real.cosh ((1 + δ) * x)) :=
            mul_le_mul_of_nonneg_right hx.2 hnonneg
  simpa [intervalIntegral.integral_const_mul] using hmono

theorem upperPositiveShellThirdMoment_le {ε δ : ℝ} :
    upperPositiveShellThirdMoment ε δ ≤ (Bε ε + 1) * V_B ε δ := by
  unfold upperPositiveShellThirdMoment V_B
  exact intervalIntegral_thirdMoment_le (w := w_B ε) (by linarith)
    (fun a _ ↦ div_nonneg (shellWeight_pos ε).le (Real.cosh_pos a).le)
    (positiveShellDensity_continuous ε).continuousOn

/-- Third moment carried by the short shell on the contour of height `1 + δ`. -/
def upperShortShellThirdMoment (ε δ : ℝ) : ℝ :=
  ∫ a in a₀ε ε..Aε ε, (-w_s ε a) * a ^ 3 * Real.cosh ((1 + δ) * a)

/-- The short-shell third moment is at most `A` times the short-shell variance. -/
theorem upperShortShellThirdMoment_le {ε δ : ℝ} (hε : 0 < ε) (horder : a₀ε ε ≤ Aε ε)
    (hmargin : ∀ a ∈ Set.Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a) :
    upperShortShellThirdMoment ε δ ≤ Aε ε * V_s ε δ := by
  unfold upperShortShellThirdMoment V_s
  exact intervalIntegral_thirdMoment_le (w := fun a ↦ -w_s ε a) horder
    (fun a ha ↦ neg_shortShellDensity_nonneg ((shortCutoff_pos hε).trans_le ha.1) (hmargin a ha))
    (continuousOn_shortShellDensity hε).neg

theorem eventually_upper_shortShellThirdMoment_domination : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    ∀ δ : ℝ, ε / 2 ≤ δ → upperShortShellThirdMoment ε δ ≤ (Aε ε / 100) * V_B ε δ := by
  filter_upwards [self_mem_nhdsWithin, eventually_upper_shortCutoff_le_shortEndpoint,
      eventually_upper_shortMargin_positive, eventually_upper_shortShellVariance_domination]
    with ε hε horder hmargin hdom
  change 0 < ε at hε
  intro δ hδ
  have hA : (0 : ℝ) ≤ Aε ε := ((shortCutoff_pos hε).trans_le horder).le
  calc upperShortShellThirdMoment ε δ ≤ Aε ε * V_s ε δ :=
        upperShortShellThirdMoment_le (δ := δ) hε horder fun a ha ↦ by linarith [hmargin a ha]
    _ ≤ Aε ε * ((1 / 100 : ℝ) * V_B ε δ) := mul_le_mul_of_nonneg_left (hdom δ hδ) hA
    _ = (Aε ε / 100) * V_B ε δ := by ring

/-- The net shell third moment of report (46). -/
def upperNetShellThirdMoment (ε δ : ℝ) : ℝ :=
  upperPositiveShellThirdMoment ε δ + upperShortShellThirdMoment ε δ

/-- Report (46): the net shell third moment is `O((B + A) V_B)`. -/
theorem eventually_upper_netShellThirdMoment_bound : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ δ : ℝ, ε / 2 ≤ δ →
    upperNetShellThirdMoment ε δ ≤ (Bε ε + 1 + Aε ε / 100) * V_B ε δ := by
  filter_upwards [eventually_upper_shortShellThirdMoment_domination] with ε hshort
  intro δ hδ
  have hpositive := upperPositiveShellThirdMoment_le (ε := ε) (δ := δ)
  unfold upperNetShellThirdMoment
  nlinarith [hshort δ hδ]

/-! ### The gamma density `μ_{ℓ,η}` and its moments (report (37), (48)) -/

theorem upper_inv_one_sub_exp_neg_bounds {x : ℝ} (hx : 0 < x) :
    x⁻¹ ≤ (1 - Real.exp (-x))⁻¹ ∧ (1 - Real.exp (-x))⁻¹ ≤ 1 + x⁻¹ := by
  have hden : 0 < 1 - Real.exp (-x) := by
    have := Real.exp_lt_one_iff.mpr (show -x < 0 by linarith)
    linarith
  have hplus : (0 : ℝ) < 1 + x := by linarith
  have hexp : Real.exp (-x) ≤ (1 + x)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos x) hplus).2 (by linarith [Real.add_one_le_exp x])
  refine ⟨(inv_le_inv₀ hx hden).2 (by nlinarith [Real.add_one_le_exp (-x)]), ?_⟩
  rw [inv_eq_one_div]
  refine (div_le_iff₀ hden).2 ?_
  calc (1 : ℝ) = (1 + x⁻¹) * (1 - (1 + x)⁻¹) := by field_simp [hx.ne', hplus.ne']; ring
    _ ≤ (1 + x⁻¹) * (1 - Real.exp (-x)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- The gamma density `μ_{λ,η}(a) = e^{-ηa} / (a (1 - e^{-2a/λ}))` of report (37). -/
def μ_ℓ (ℓ η a : ℝ) : ℝ := Real.exp (-η * a) / (a * (1 - Real.exp (-(2 * a / ℓ))))

theorem upper_laplace_monomial_integrable {η : ℝ} (hη : 0 < η) (k : ℕ) :
    IntegrableOn (fun a : ℝ ↦ a ^ k * Real.exp (-η * a)) (Set.Ioi 0) :=
  (integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (k : ℝ)) (b := η)
    (by exact_mod_cast (show (-(1 : ℤ) < (k : ℤ)) by lia)) (by norm_num) hη).congr_fun
    (fun a _ ↦ by simp [Real.rpow_natCast]) measurableSet_Ioi

theorem upper_laplace_monomial_integral {η : ℝ} (hη : 0 < η) (k : ℕ) :
    (∫ a : ℝ in Set.Ioi 0, a ^ k * Real.exp (-η * a)) = (k.factorial : ℝ) / η ^ (k + 1) := by
  calc (∫ a : ℝ in Set.Ioi 0, a ^ k * Real.exp (-η * a))
      = ∫ a : ℝ in Set.Ioi 0, a ^ ((k : ℝ) + 1 - 1) * Real.exp (-(η * a)) :=
        setIntegral_congr_fun measurableSet_Ioi fun a _ ↦ by
          rw [show (k : ℝ) + 1 - 1 = (k : ℝ) by ring, Real.rpow_natCast, neg_mul]
    _ = (1 / η) ^ ((k : ℝ) + 1) * Real.Gamma ((k : ℝ) + 1) :=
        Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) hη
    _ = (k.factorial : ℝ) / η ^ (k + 1) := by
        rw [Real.Gamma_nat_eq_factorial, ← Nat.cast_add_one, Real.rpow_natCast]
        simp [inv_pow, div_eq_mul_inv, mul_comm]

/-- Report (37): pointwise bounds for `a² μ_{ℓ,η}(a)`. -/
theorem upperGammaVarianceDensity_pointwise_bounds {ℓ η a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) :
    (ℓ / 2) * Real.exp (-η * a) ≤ a ^ 2 * μ_ℓ ℓ η a ∧
    a ^ 2 * μ_ℓ ℓ η a ≤ (a + ℓ / 2) * Real.exp (-η * a) := by
  have hx : (0 : ℝ) < 2 * a / ℓ := by positivity
  obtain ⟨hlo, hhi⟩ := upper_inv_one_sub_exp_neg_bounds hx
  have hden : 0 < 1 - Real.exp (-(2 * a / ℓ)) := by
    have := Real.exp_lt_one_iff.mpr (show -(2 * a / ℓ) < 0 by linarith)
    linarith
  have hfactor : (0 : ℝ) ≤ a * Real.exp (-η * a) := by positivity
  have hidentity : a ^ 2 * μ_ℓ ℓ η a =
      a * Real.exp (-η * a) * (1 - Real.exp (-(2 * a / ℓ)))⁻¹ := by
    unfold μ_ℓ
    field_simp [ha.ne', hℓ.ne', hden.ne']
  constructor
  · calc (ℓ / 2) * Real.exp (-η * a) = a * Real.exp (-η * a) * (2 * a / ℓ)⁻¹ := by
          field_simp [ha.ne', hℓ.ne']
      _ ≤ a * Real.exp (-η * a) * (1 - Real.exp (-(2 * a / ℓ)))⁻¹ :=
          mul_le_mul_of_nonneg_left hlo hfactor
      _ = a ^ 2 * μ_ℓ ℓ η a := hidentity.symm
  · calc a ^ 2 * μ_ℓ ℓ η a = a * Real.exp (-η * a) * (1 - Real.exp (-(2 * a / ℓ)))⁻¹ := hidentity
      _ ≤ a * Real.exp (-η * a) * (1 + (2 * a / ℓ)⁻¹) := mul_le_mul_of_nonneg_left hhi hfactor
      _ = (a + ℓ / 2) * Real.exp (-η * a) := by field_simp [ha.ne', hℓ.ne']

/-- Pointwise bounds for `a^{k+2} μ_{ℓ,η}(a)`, obtained from the case `k = 0`. -/
theorem upperGammaDensity_pointwise_bounds {ℓ η a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) (k : ℕ) :
    (ℓ / 2) * (a ^ k * Real.exp (-η * a)) ≤ a ^ (k + 2) * μ_ℓ ℓ η a ∧
    a ^ (k + 2) * μ_ℓ ℓ η a ≤ (a ^ (k + 1) + (ℓ / 2) * a ^ k) * Real.exp (-η * a) := by
  obtain ⟨hlo, hhi⟩ := upperGammaVarianceDensity_pointwise_bounds (η := η) hℓ ha
  have hk : (0 : ℝ) ≤ a ^ k := by positivity
  rw [show a ^ (k + 2) * μ_ℓ ℓ η a = a ^ k * (a ^ 2 * μ_ℓ ℓ η a) by ring,
    show (ℓ / 2) * (a ^ k * Real.exp (-η * a)) = a ^ k * ((ℓ / 2) * Real.exp (-η * a)) by ring,
    show (a ^ (k + 1) + (ℓ / 2) * a ^ k) * Real.exp (-η * a) =
      a ^ k * ((a + ℓ / 2) * Real.exp (-η * a)) by ring]
  exact ⟨mul_le_mul_of_nonneg_left hlo hk, mul_le_mul_of_nonneg_left hhi hk⟩

theorem upperGammaDensity_integrable {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) (k : ℕ) :
    IntegrableOn (fun a : ℝ ↦ a ^ (k + 2) * μ_ℓ ℓ η a) (Set.Ioi 0) := by
  have hmajor : IntegrableOn
      (fun a : ℝ ↦ (a ^ (k + 1) + (ℓ / 2) * a ^ k) * Real.exp (-η * a)) (Set.Ioi 0) :=
    ((upper_laplace_monomial_integrable hη (k + 1)).add
      ((upper_laplace_monomial_integrable hη k).const_mul (ℓ / 2))).congr_fun
      (fun a _ ↦ by
        change a ^ (k + 1) * Real.exp (-η * a) + (ℓ / 2) * (a ^ k * Real.exp (-η * a)) =
          (a ^ (k + 1) + (ℓ / 2) * a ^ k) * Real.exp (-η * a)
        ring) measurableSet_Ioi
  have hmeas : Measurable fun a : ℝ ↦ a ^ (k + 2) * μ_ℓ ℓ η a := by unfold μ_ℓ; fun_prop
  refine hmajor.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  have hapos : 0 < a := ha
  obtain ⟨hlo, hhi⟩ := upperGammaDensity_pointwise_bounds (η := η) hℓ hapos k
  rw [Real.norm_eq_abs, abs_of_nonneg (le_trans (by positivity) hlo)]
  exact hhi

/-- `a² μ_{ℓ,η}` is integrable on `(0, ∞)`. -/
theorem upperGammaVarianceDensity_integrable {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) :
    IntegrableOn (fun a : ℝ ↦ a ^ 2 * μ_ℓ ℓ η a) (Set.Ioi 0) :=
  upperGammaDensity_integrable hℓ hη 0

/-- `a³ μ_{ℓ,η}` is integrable on `(0, ∞)`. -/
theorem upperGammaThirdMomentDensity_integrable {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) :
    IntegrableOn (fun a : ℝ ↦ a ^ 3 * μ_ℓ ℓ η a) (Set.Ioi 0) :=
  upperGammaDensity_integrable hℓ hη 1

/-- The variance `V_γ` of the gamma density, report (48). -/
def V_γ (ℓ η : ℝ) : ℝ := ℓ⁻¹ * ∫ a : ℝ in Set.Ioi 0, a ^ 2 * μ_ℓ ℓ η a

/-- The third moment `M₃_γ` of the gamma density, report (48). -/
def M₃_γ (ℓ η : ℝ) : ℝ := ℓ⁻¹ * ∫ a : ℝ in Set.Ioi 0, a ^ 3 * μ_ℓ ℓ η a

/-- Report (48): bounds for the `ℓ`-normalized `(k+2)`-nd moment of `μ_{ℓ,η}`. -/
theorem upperGammaMoment_bounds {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) (k : ℕ) :
    (k.factorial : ℝ) / (2 * η ^ (k + 1)) ≤
        ℓ⁻¹ * ∫ a : ℝ in Set.Ioi 0, a ^ (k + 2) * μ_ℓ ℓ η a ∧
      ℓ⁻¹ * (∫ a : ℝ in Set.Ioi 0, a ^ (k + 2) * μ_ℓ ℓ η a) ≤
        (k.factorial : ℝ) / (2 * η ^ (k + 1)) + ((k + 1).factorial : ℝ) / (ℓ * η ^ (k + 2)) := by
  have hint := upper_laplace_monomial_integrable hη
  have hact := upperGammaDensity_integrable hℓ hη k
  have hlow : ℓ / 2 * ((k.factorial : ℝ) / η ^ (k + 1)) ≤
      ∫ a : ℝ in Set.Ioi 0, a ^ (k + 2) * μ_ℓ ℓ η a := by
    rw [← upper_laplace_monomial_integral hη k, ← integral_const_mul]
    refine integral_mono_ae ((hint k).const_mul _) hact ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    exact (upperGammaDensity_pointwise_bounds (η := η) hℓ ha k).1
  have hup : (∫ a : ℝ in Set.Ioi 0, a ^ (k + 2) * μ_ℓ ℓ η a) ≤
      ((k + 1).factorial : ℝ) / η ^ (k + 2) + ℓ / 2 * ((k.factorial : ℝ) / η ^ (k + 1)) := by
    have hval : (∫ a : ℝ in Set.Ioi 0, a ^ (k + 1) * Real.exp (-η * a) +
        (ℓ / 2) * (a ^ k * Real.exp (-η * a))) =
        ((k + 1).factorial : ℝ) / η ^ (k + 2) + ℓ / 2 * ((k.factorial : ℝ) / η ^ (k + 1)) := by
      rw [integral_add (hint (k + 1)) ((hint k).const_mul (ℓ / 2)),
        upper_laplace_monomial_integral hη (k + 1), integral_const_mul,
        upper_laplace_monomial_integral hη k]
    rw [← hval]
    refine integral_mono_ae hact ((hint (k + 1)).add ((hint k).const_mul (ℓ / 2))) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    change a ^ (k + 2) * μ_ℓ ℓ η a ≤
      a ^ (k + 1) * Real.exp (-η * a) + (ℓ / 2) * (a ^ k * Real.exp (-η * a))
    calc a ^ (k + 2) * μ_ℓ ℓ η a ≤ (a ^ (k + 1) + (ℓ / 2) * a ^ k) * Real.exp (-η * a) :=
          (upperGammaDensity_pointwise_bounds (η := η) hℓ ha k).2
      _ = a ^ (k + 1) * Real.exp (-η * a) + (ℓ / 2) * (a ^ k * Real.exp (-η * a)) := by ring
  have hinv : (0 : ℝ) ≤ ℓ⁻¹ := (inv_pos.mpr hℓ).le
  constructor
  · calc (k.factorial : ℝ) / (2 * η ^ (k + 1))
        = ℓ⁻¹ * (ℓ / 2 * ((k.factorial : ℝ) / η ^ (k + 1))) := by
          field_simp [hℓ.ne', hη.ne']
      _ ≤ ℓ⁻¹ * ∫ a : ℝ in Set.Ioi 0, a ^ (k + 2) * μ_ℓ ℓ η a :=
          mul_le_mul_of_nonneg_left hlow hinv
  · calc ℓ⁻¹ * (∫ a : ℝ in Set.Ioi 0, a ^ (k + 2) * μ_ℓ ℓ η a)
        ≤ ℓ⁻¹ * (((k + 1).factorial : ℝ) / η ^ (k + 2) +
            ℓ / 2 * ((k.factorial : ℝ) / η ^ (k + 1))) := mul_le_mul_of_nonneg_left hup hinv
      _ = (k.factorial : ℝ) / (2 * η ^ (k + 1)) +
            ((k + 1).factorial : ℝ) / (ℓ * η ^ (k + 2)) := by
          field_simp [hℓ.ne', hη.ne']
          ring

/-- Report (48): `1/(2η) ≤ V_γ ≤ 1/(2η) + 1/(λη²)`. -/
theorem upperGammaVariance_bounds {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) :
    1 / (2 * η) ≤ V_γ ℓ η ∧ V_γ ℓ η ≤ 1 / (2 * η) + 1 / (ℓ * η ^ 2) := by
  simpa [V_γ, Nat.factorial] using upperGammaMoment_bounds hℓ hη 0

/-- Report (48): `1/(2η²) ≤ M₃_γ ≤ 1/(2η²) + 2/(λη³)`. -/
theorem upperGammaThirdMoment_bounds {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) :
    1 / (2 * η ^ 2) ≤ M₃_γ ℓ η ∧ M₃_γ ℓ η ≤ 1 / (2 * η ^ 2) + 2 / (ℓ * η ^ 3) := by
  simpa [M₃_γ, Nat.factorial] using upperGammaMoment_bounds hℓ hη 1

/-! ### The small-radius expansion of `f₊` (report Lemma 4.4) -/

theorem plusPolynomial_negative_imaginary_residue (ε s : ℝ) :
    PPlus ε (I * ((-(1 + s) : ℝ) : ℂ)) = ((β ε - s * (2 + s) ^ 2 : ℝ) : ℂ) := by
  rw [plusPolynomial_imaginary]
  push_cast
  ring

/-- The derivative `h₁' = h_ε'(1)` of the shell phase at the saddle height. -/
def h₁' (ε : ℝ) : ℝ :=
  (∫ a in a₀ε ε..Aε ε, w_s ε a * a * Real.sinh a) + ∫ a in Bε ε..Bε ε + 1, w_B ε a * a * Real.sinh a

/-- The small-radius variable `y_r = π e^{2h₁'} r²`. -/
def y_r (ε r : ℝ) : ℝ := π * Real.exp (2 * h₁' ε) * r ^ 2

/-- The small-radius coefficients `A_{λ,n}` of the residue expansion of `f₊`. -/
def A_ℓn (ε ℓ : ℝ) (n : ℕ) : ℝ :=
  Real.exp (ℓ * (h_εI ε (1 + 2 * (n : ℝ) / ℓ) - h_εI ε 1) - 2 * (n : ℝ) * h₁' ε) *
    ((β ε - (2 * (n : ℝ) / ℓ) * (2 + 2 * (n : ℝ) / ℓ) ^ 2) / β ε)

theorem plusSaddlePoleResidue_explicit_real {ε ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) :
    plusSaddlePoleResidue ε ℓ n = ((2 * (-1 : ℝ) ^ n / (n.factorial : ℝ) *
        (π ^ (ℓ / 2 + (n : ℝ)) * Real.exp (ℓ * h_εI ε (1 + 2 * (n : ℝ) / ℓ))) *
        (β ε - (2 * (n : ℝ) / ℓ) * (2 + 2 * (n : ℝ) / ℓ) ^ 2) : ℝ) : ℂ) := by
  unfold plusSaddlePoleResidue
  rw [plusSaddleRegularMellinFactor_neg_even hℓ n, plusPolynomial_negative_imaginary_residue]
  push_cast
  ring

/-- The small-radius variable `y_r` is nonnegative. -/
theorem saddleSmallRadiusVariable_nonneg (ε r : ℝ) : 0 ≤ y_r ε r := by
  unfold y_r
  positivity

theorem saddleSmallRadiusVariable_neg_pow (ε r : ℝ) (n : ℕ) : (-y_r ε r) ^ n =
      (-1 : ℝ) ^ n * π ^ n * Real.exp (2 * h₁' ε) ^ n * r ^ (2 * n) := by
  rw [show -y_r ε r = -1 * π * Real.exp (2 * h₁' ε) * r ^ 2 by unfold y_r; ring]
  ring

theorem saddleSmallRadiusPhase_pole_factorization (ε ℓ : ℝ) (n : ℕ) :
    Real.exp (ℓ * h_εI ε (1 + 2 * (n : ℝ) / ℓ)) =
      Real.exp (ℓ * h_εI ε 1) * Real.exp (2 * h₁' ε) ^ n *
        Real.exp (ℓ * (h_εI ε (1 + 2 * (n : ℝ) / ℓ) - h_εI ε 1) - 2 * (n : ℝ) * h₁' ε) := by
  rw [show ℓ * h_εI ε (1 + 2 * (n : ℝ) / ℓ) = ℓ * h_εI ε 1 + (n : ℝ) * (2 * h₁' ε) +
      (ℓ * (h_εI ε (1 + 2 * (n : ℝ) / ℓ) - h_εI ε 1) - 2 * (n : ℝ) * h₁' ε) by ring,
    Real.exp_add, Real.exp_add, Real.exp_nat_mul]

theorem plusSaddlePoleResidue_mul_pow_eq_smallCoefficient {ε ℓ : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (n : ℕ) (r : ℝ) :
    plusSaddlePoleResidue ε ℓ n * (r ^ (2 * n) : ℂ) = ((originValue ε ℓ *
        ((-y_r ε r) ^ n / (n.factorial : ℝ)) * A_ℓn ε ℓ n : ℝ) : ℂ) := by
  have hfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [plusSaddlePoleResidue_explicit_real hℓ n, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  refine congrArg Complex.ofReal ?_
  unfold originValue A_ℓn
  rw [Real.rpow_add_natCast Real.pi_ne_zero (ℓ / 2) n,
    saddleSmallRadiusPhase_pole_factorization ε ℓ n, saddleSmallRadiusVariable_neg_pow ε r n]
  field_simp [(beta_pos hε).ne', hfac]

/-- Report Lemma 4.4: the small-radius residue expansion of `f₊ / f₊(0)`. -/
theorem plusSaddleProfile_div_origin_eq_small_radius_residue_series {ε ℓ r : ℝ} (hε : 0 < ε)
    (hℓ : 0 < ℓ) (horder : a₀ε ε ≤ Aε ε) (hr : 0 < r) (N : ℕ) :
    fPlus ε ℓ r / (originValue ε ℓ : ℂ) = ((∑ n ∈ Finset.range (N + 1),
        (-y_r ε r) ^ n / (n.factorial : ℝ) * A_ℓn ε ℓ n : ℝ) : ℂ) +
      plusSaddleTaylorRemainder ε ℓ N r / (originValue ε ℓ : ℂ) := by
  have hzero : (originValue ε ℓ : ℂ) ≠ 0 := by exact_mod_cast (saddleOriginValue_pos hε ℓ).ne'
  have hseries : fPlus ε ℓ r = (originValue ε ℓ : ℂ) * ((∑ n ∈ Finset.range (N + 1),
        (-y_r ε r) ^ n / (n.factorial : ℝ) * A_ℓn ε ℓ n : ℝ) : ℂ) +
      plusSaddleTaylorRemainder ε ℓ N r := by
    rw [plusSaddleProfile_eq_residue_sum_add_remainder hε hℓ horder hr N]
    congr 1
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    have hterm := plusSaddlePoleResidue_mul_pow_eq_smallCoefficient hε hℓ n r
    push_cast at hterm
    simpa only [mul_assoc] using hterm
  rw [hseries]
  field_simp [hzero]

/-! ### The shell phase on the imaginary axis -/

/-- The shell phase `h_ε` restricted to the imaginary axis is smooth. -/
theorem realHyperbolicShellPhase_contDiff {ε : ℝ} (hε : 0 < ε) (horder : a₀ε ε ≤ Aε ε)
    (n : WithTop ℕ∞) : ContDiff ℝ n (h_εI ε) := by
  have hcomplex : ContDiff ℝ n (h_ε ε) :=
    ((mellinShellPhase_analyticOnNhd hε horder).restrictScalars (𝕜 := ℝ)).contDiff
  have harg : ContDiff ℝ n fun u : ℝ ↦ I * (u : ℂ) :=
    contDiff_const.mul Complex.ofRealCLM.contDiff
  have hphase : ContDiff ℝ n fun u : ℝ ↦ h_ε ε (I * (u : ℂ)) := by
    simpa only [Function.comp_apply] using! hcomplex.comp harg
  have hre : ContDiff ℝ n fun u : ℝ ↦ (h_ε ε (I * (u : ℂ))).re := by
    simpa only [Function.comp_apply] using! Complex.reCLM.contDiff.comp hphase
  simpa only [mellinShellPhase_imaginary, Complex.ofReal_re] using! hre

theorem realHyperbolicShellInterval_hasDerivAt (w : ℝ → ℝ) (hw : Continuous w)
    {a b : ℝ} (hab : a ≤ b) (u : ℝ) :
    HasDerivAt (fun v : ℝ ↦ ∫ x in a..b, w x * (Real.cosh (x * v) - 1)) (∫ x in a..b,
        w x * x * Real.sinh (x * u)) u := by
  let F : ℝ → ℝ → ℝ := fun v x ↦ w x * (Real.cosh (x * v) - 1)
  let F' : ℝ → ℝ → ℝ := fun v x ↦ w x * x * Real.sinh (x * v)
  have hF (v : ℝ) : Continuous (F v) := hw.mul ((Real.continuous_cosh.comp
    (continuous_id.mul continuous_const)).sub continuous_const)
  have hF' (v : ℝ) : Continuous (F' v) := (hw.mul continuous_id).mul
    (Real.continuous_sinh.comp (continuous_id.mul continuous_const))
  have hF'joint : Continuous (Function.uncurry F') :=
    ((hw.comp continuous_snd).mul continuous_snd).mul
      (Real.continuous_sinh.comp (continuous_snd.mul continuous_fst))
  have hderiv (x v : ℝ) : HasDerivAt (fun z : ℝ ↦ F z x) (F' v x) v := by
    have hlinear : HasDerivAt (fun z : ℝ ↦ x * z) x v := by
      simpa using (hasDerivAt_id v).const_mul x
    simpa [F, F', mul_assoc, mul_left_comm, mul_comm] using
      (((Real.hasDerivAt_cosh (x * v)).comp v hlinear).sub_const (1 : ℝ)).const_mul (w x)
  rw [show (fun v : ℝ ↦ ∫ x in a..b, w x * (Real.cosh (x * v) - 1)) =
      fun v : ℝ ↦ ∫ x in Set.Icc a b, F v x from funext fun v ↦ by
        rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc],
    show (∫ x in a..b, w x * x * Real.sinh (x * u)) = ∫ x in Set.Icc a b, F' u x by
      rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]]
  have hcompact : IsCompact (Metric.closedBall u 1 ×ˢ Set.Icc a b) :=
    (isCompact_closedBall u 1).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hcompact.bddAbove_image hF'joint.norm.continuousOn
  have hbound : ∀ᵐ x ∂volume.restrict (Set.Icc a b), ∀ v ∈ Metric.ball u 1, ‖F' v x‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx v hv
    have hpair : (v, x) ∈ Metric.closedBall u 1 ×ˢ Set.Icc a b :=
      ⟨Metric.ball_subset_closedBall hv, hx⟩
    exact hC (Set.mem_image_of_mem (fun p : ℝ × ℝ ↦ ‖F' p.1 p.2‖) hpair)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Set.Icc a b))
    (s := Metric.ball u 1) (bound := fun _ : ℝ ↦ C) (Metric.ball_mem_nhds u zero_lt_one)
    (Eventually.of_forall fun v ↦ (hF v).aestronglyMeasurable) (hF u).integrableOn_Icc
    (hF' u).aestronglyMeasurable hbound (integrableOn_const isCompact_Icc.measure_ne_top)
    (Eventually.of_forall fun x v _ ↦ hderiv x v)).2

/-- Derivative of the shell phase on the imaginary axis, by differentiation under `∫`. -/
theorem realHyperbolicShellPhase_hasDerivAt {ε : ℝ} (hε : 0 < ε) (horder : a₀ε ε ≤ Aε ε)
    (u : ℝ) :
    HasDerivAt (h_εI ε) ((∫ a in a₀ε ε..Aε ε, w_s ε a * a * Real.sinh (a * u)) +
      (∫ a in Bε ε..Bε ε + 1, w_B ε a * a * Real.sinh (a * u))) u := by
  have hmax (a : ℝ) : 0 < max a (a₀ε ε) := (shortCutoff_pos hε).trans_le (le_max_right _ _)
  have hw : Continuous fun a : ℝ ↦ w_s ε (max a (a₀ε ε)) := by
    have hn : Continuous fun a : ℝ ↦ bε ε (max a (a₀ε ε)) * Real.exp (-2 * max a (a₀ε ε)) := by
      unfold bε
      fun_prop
    have hd : Continuous fun a : ℝ ↦ 2 * max a (a₀ε ε) ^ 2 * Real.cosh (max a (a₀ε ε)) := by
      fun_prop
    unfold w_s
    exact (hn.div hd fun a ↦ by positivity [hmax a]).neg
  have hmaxeq : ∀ a ∈ Set.uIcc (a₀ε ε) (Aε ε), max a (a₀ε ε) = a := fun a ha ↦ by
    rw [uIcc_of_le horder] at ha
    exact max_eq_left ha.1
  have hfun : (fun v : ℝ ↦ ∫ a in a₀ε ε..Aε ε, w_s ε a * (Real.cosh (a * v) - 1)) =
      fun v : ℝ ↦ ∫ a in a₀ε ε..Aε ε, w_s ε (max a (a₀ε ε)) * (Real.cosh (a * v) - 1) := by
    funext v
    refine intervalIntegral.integral_congr fun a ha ↦ ?_
    rw [hmaxeq a ha]
  have hderivfun : (∫ a in a₀ε ε..Aε ε, w_s ε a * a * Real.sinh (a * u)) =
      ∫ a in a₀ε ε..Aε ε, w_s ε (max a (a₀ε ε)) * a * Real.sinh (a * u) := by
    refine intervalIntegral.integral_congr fun a ha ↦ ?_
    rw [hmaxeq a ha]
  have hshort : HasDerivAt (fun v : ℝ ↦ ∫ a in a₀ε ε..Aε ε,
      w_s ε a * (Real.cosh (a * v) - 1))
      (∫ a in a₀ε ε..Aε ε, w_s ε a * a * Real.sinh (a * u)) u := by
    rw [hfun, hderivfun]
    exact realHyperbolicShellInterval_hasDerivAt _ hw horder u
  exact hshort.add (realHyperbolicShellInterval_hasDerivAt (w_B ε)
    (positiveShellDensity_continuous ε) (by linarith) u)

/-- Report Lemma 4.4: a quadratic Taylor remainder for the shell phase on `[1, 2]`. -/
theorem exists_realHyperbolicShellPhase_quadratic_remainder {ε : ℝ} (hε : 0 < ε)
    (horder : a₀ε ε ≤ Aε ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Icc (1 : ℝ) 2,
      |h_εI ε x - h_εI ε 1 - (x - 1) * h₁' ε| ≤ C * (x - 1) ^ 2 := by
  obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound (f := h_εI ε) (n := 1)
    (by norm_num : (1 : ℝ) ≤ 2)
    (realHyperbolicShellPhase_contDiff hε horder (2 : WithTop ℕ∞)).contDiffOn
  have hwithin : derivWithin (h_εI ε) (Set.Icc (1 : ℝ) 2) 1 = h₁' ε :=
    ((realHyperbolicShellPhase_hasDerivAt hε horder 1).hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_Icc (by norm_num : (1 : ℝ) < 2)) 1 (by constructor <;> norm_num))).trans
      (by simp [h₁'])
  refine ⟨max C 0, le_max_right _ _, fun x hx ↦ ?_⟩
  have hxbound := hC x hx
  rw [show taylorWithinEval (h_εI ε) 1 (Set.Icc (1 : ℝ) 2) 1 x =
      h_εI ε 1 + (x - 1) * h₁' ε by
    simp [taylorWithinEval_succ, iteratedDerivWithin_one, hwithin, smul_eq_mul],
    Real.norm_eq_abs] at hxbound
  calc |h_εI ε x - h_εI ε 1 - (x - 1) * h₁' ε|
      = |h_εI ε x - (h_εI ε 1 + (x - 1) * h₁' ε)| := by ring_nf
    _ ≤ C * (x - 1) ^ 2 := hxbound
    _ ≤ max C 0 * (x - 1) ^ 2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)

theorem exists_plusSaddleSmallRadiusPhase_error {ε : ℝ} (hε : 0 < ε)
    (horder : a₀ε ε ≤ Aε ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ : ℝ), 0 < ℓ → ∀ n : ℕ, 2 * (n : ℝ) ≤ ℓ →
      |ℓ * (h_εI ε (1 + 2 * (n : ℝ) / ℓ) - h_εI ε 1) - 2 * (n : ℝ) * h₁' ε| ≤
        C * (n : ℝ) ^ 2 / ℓ := by
  obtain ⟨C, hCnonneg, hC⟩ := exists_realHyperbolicShellPhase_quadratic_remainder hε horder
  refine ⟨4 * C, by positivity, fun ℓ hℓ n hn ↦ ?_⟩
  set x : ℝ := 1 + 2 * (n : ℝ) / ℓ with hxdef
  have hratio : (0 : ℝ) ≤ 2 * (n : ℝ) / ℓ := by positivity
  have hratioupper : 2 * (n : ℝ) / ℓ ≤ 1 := (div_le_iff₀ hℓ).mpr (by simpa using hn)
  have hx : x ∈ Set.Icc (1 : ℝ) 2 := ⟨by rw [hxdef]; linarith, by rw [hxdef]; linarith⟩
  have hscale : ℓ * (x - 1) = 2 * (n : ℝ) := by
    rw [hxdef]
    field_simp
    ring
  calc |ℓ * (h_εI ε x - h_εI ε 1) - 2 * (n : ℝ) * h₁' ε|
      = ℓ * |h_εI ε x - h_εI ε 1 - (x - 1) * h₁' ε| := by
        rw [show ℓ * (h_εI ε x - h_εI ε 1) - 2 * (n : ℝ) * h₁' ε =
          ℓ * (h_εI ε x - h_εI ε 1 - (x - 1) * h₁' ε) by rw [← hscale]; ring, abs_mul,
          abs_of_pos hℓ]
    _ ≤ ℓ * (C * (x - 1) ^ 2) := mul_le_mul_of_nonneg_left (hC x hx) hℓ.le
    _ = 4 * C * (n : ℝ) ^ 2 / ℓ := by rw [hxdef]; field_simp; ring

theorem plusSaddleSmallRadiusPolynomial_error {ε ℓ : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (n : ℕ) (hn : 2 * (n : ℝ) ≤ ℓ) :
    |((β ε - (2 * (n : ℝ) / ℓ) * (2 + 2 * (n : ℝ) / ℓ) ^ 2) / β ε) - 1| ≤
      (18 / β ε) * ((n : ℝ) / ℓ) := by
  have hb : 0 < β ε := beta_pos hε
  set s : ℝ := 2 * (n : ℝ) / ℓ with hsdef
  have hs : (0 : ℝ) ≤ s := by rw [hsdef]; positivity
  have hsone : s ≤ 1 := by rw [hsdef]; exact (div_le_iff₀ hℓ).mpr (by simpa using hn)
  have hnumerator : (0 : ℝ) ≤ s * (2 + s) ^ 2 := mul_nonneg hs (sq_nonneg _)
  rw [show (β ε - s * (2 + s) ^ 2) / β ε - 1 = -(s * (2 + s) ^ 2) / β ε by field_simp; ring,
    abs_div, abs_neg, abs_of_nonneg hnumerator, abs_of_pos hb]
  calc s * (2 + s) ^ 2 / β ε ≤ s * 9 / β ε := by
        gcongr
        nlinarith
    _ = 18 / β ε * ((n : ℝ) / ℓ) := by rw [hsdef]; field_simp; ring

/-- `|e^t - 1| ≤ |t| e^{|t|}`. -/
theorem abs_exp_sub_one_le_abs_mul_exp_abs (t : ℝ) :
    |Real.exp t - 1| ≤ |t| * Real.exp |t| := by
  rcases le_total 0 t with ht | ht
  · have hexp : 1 ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
    have hcancel : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
    have hmul := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-t)) (Real.exp_pos t).le
    rw [hcancel] at hmul
    rw [abs_of_nonneg (sub_nonneg.mpr hexp), abs_of_nonneg ht]
    nlinarith
  · have hexp : Real.exp t ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr ht
    have hnegt : (0 : ℝ) ≤ -t := neg_nonneg.mpr ht
    have hexpneg : 1 ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
    rw [abs_of_nonpos (sub_nonpos.mpr hexp), abs_of_nonpos ht]
    nlinarith [mul_nonneg hnegt (sub_nonneg.mpr hexpneg), Real.add_one_le_exp t]

theorem plusSaddleSmallRadiusCoefficient_error_of_phase {ε ℓ : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (n : ℕ) (hn : 2 * (n : ℝ) ≤ ℓ) {C : ℝ} (hC : 0 ≤ C)
    (hphase : |ℓ * (h_εI ε (1 + 2 * (n : ℝ) / ℓ) - h_εI ε 1) - 2 * (n : ℝ) * h₁' ε| ≤
        C * (n : ℝ) ^ 2 / ℓ) :
    |A_ℓn ε ℓ n - 1| ≤
      (C * (n : ℝ) ^ 2 / ℓ + (18 / β ε) * ((n : ℝ) / ℓ)) * Real.exp (C * (n : ℝ) ^ 2 / ℓ) := by
  have hb : 0 < β ε := beta_pos hε
  set E : ℝ := ℓ * (h_εI ε (1 + 2 * (n : ℝ) / ℓ) - h_εI ε 1) - 2 * (n : ℝ) * h₁' ε
  set q : ℝ := C * (n : ℝ) ^ 2 / ℓ with hqdef
  set k : ℝ := 18 / β ε * ((n : ℝ) / ℓ) with hkdef
  set P : ℝ := (β ε - 2 * (n : ℝ) / ℓ * (2 + 2 * (n : ℝ) / ℓ) ^ 2) / β ε with hPdef
  have hq : (0 : ℝ) ≤ q := by rw [hqdef]; positivity
  have hPk : |P - 1| ≤ k := by
    rw [hPdef, hkdef]
    exact plusSaddleSmallRadiusPolynomial_error hε hℓ n hn
  have hexp : Real.exp E ≤ Real.exp q := Real.exp_le_exp.mpr ((le_abs_self E).trans hphase)
  have htermP : |Real.exp E * (P - 1)| ≤ Real.exp q * k := by
    rw [abs_mul, abs_of_pos (Real.exp_pos E)]
    exact mul_le_mul hexp hPk (abs_nonneg _) (Real.exp_pos q).le
  have htermE : |Real.exp E - 1| ≤ q * Real.exp q :=
    (abs_exp_sub_one_le_abs_mul_exp_abs E).trans (mul_le_mul hphase
      (Real.exp_le_exp.mpr hphase) (Real.exp_pos |E|).le hq)
  change |Real.exp E * P - 1| ≤ (q + k) * Real.exp q
  calc |Real.exp E * P - 1| = |Real.exp E * (P - 1) + (Real.exp E - 1)| := by
        congr 1
        ring
    _ ≤ |Real.exp E * (P - 1)| + |Real.exp E - 1| := abs_add_le _ _
    _ ≤ Real.exp q * k + q * Real.exp q := add_le_add htermP htermE
    _ = (q + k) * Real.exp q := by ring

/-- Report Lemma 4.4: `A_{λ,n} = 1 + O((n + n²)/λ)` for `2n ≤ λ`. -/
theorem exists_plusSaddleSmallRadiusCoefficient_error {ε : ℝ} (hε : 0 < ε)
    (horder : a₀ε ε ≤ Aε ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ : ℝ), 0 < ℓ → ∀ n : ℕ, 2 * (n : ℝ) ≤ ℓ →
      |A_ℓn ε ℓ n - 1| ≤ (C * ((n : ℝ) + (n : ℝ) ^ 2) / ℓ) * Real.exp (C * (n : ℝ) ^ 2 / ℓ) := by
  have hb : 0 < β ε := beta_pos hε
  obtain ⟨C, hC, hphase⟩ := exists_plusSaddleSmallRadiusPhase_error hε horder
  have hK : (0 : ℝ) ≤ 18 / β ε := by positivity
  refine ⟨C + 18 / β ε, by positivity, fun ℓ hℓ n hn ↦ ?_⟩
  have hnreal : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hpoly : C * (n : ℝ) ^ 2 / ℓ + 18 / β ε * ((n : ℝ) / ℓ) ≤
      (C + 18 / β ε) * ((n : ℝ) + (n : ℝ) ^ 2) / ℓ := by
    rw [show C * (n : ℝ) ^ 2 / ℓ + 18 / β ε * ((n : ℝ) / ℓ) =
      (C * (n : ℝ) ^ 2 + 18 / β ε * (n : ℝ)) / ℓ by ring]
    exact (div_le_div_iff_of_pos_right hℓ).mpr
      (by nlinarith [mul_nonneg hC hnreal, mul_nonneg hK (sq_nonneg (n : ℝ))])
  have hq : C * (n : ℝ) ^ 2 / ℓ ≤ (C + 18 / β ε) * (n : ℝ) ^ 2 / ℓ := by
    gcongr
    exact le_add_of_nonneg_right hK
  exact (plusSaddleSmallRadiusCoefficient_error_of_phase hε hℓ n hn hC
    (hphase ℓ hℓ n hn)).trans (mul_le_mul hpoly (Real.exp_le_exp.mpr hq) (Real.exp_pos _).le
      (by positivity))

/-- The exponential series `∑ yⁿ/n! = e^y`. -/
theorem saddleExpSeries_hasSum (y : ℝ) : HasSum (fun n : ℕ ↦ y ^ n / (n.factorial : ℝ))
      (Real.exp y) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp y

/-- The first moment `∑ n yⁿ/n! = y e^y` of the exponential series. -/
theorem saddleExpSeries_firstMoment_hasSum (y : ℝ) :
    HasSum (fun n : ℕ ↦ (n : ℝ) * (y ^ n / (n.factorial : ℝ))) (y * Real.exp y) := by
  let f : ℕ → ℝ := fun n ↦ (n : ℝ) * (y ^ n / (n.factorial : ℝ))
  have htail : HasSum (fun n : ℕ ↦ f (n + 1)) (y * Real.exp y) := by
    rw [show (fun n : ℕ ↦ f (n + 1)) = fun n : ℕ ↦ y * (y ^ n / (n.factorial : ℝ)) from
      funext fun n ↦ by
        have hfact : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
        dsimp only [f]
        rw [Nat.factorial_succ, pow_succ]
        push_cast
        field_simp]
    exact (saddleExpSeries_hasSum y).mul_left y
  simpa [f] using htail.zero_add

end

noncomputable section

open Filter MeasureTheory Real Set
open scoped Topology

/-! ### The truncated residue sum `S_N(y) = ∑_{n ≤ N} (-y)ⁿ/n! · A_{λ,n}` of report (78)–(79) -/

/-- The polynomial moment `∑ₙ (n + n²) yⁿ/n! = (2y + y²) eʸ` of the exponential series. -/
theorem hasSum_expSeries_polynomialMoment (y : ℝ) :
    HasSum (fun n : ℕ ↦ ((n : ℝ) + (n : ℝ) ^ 2) * (y ^ n / (n.factorial : ℝ)))
      ((2 * y + y ^ 2) * exp y) := by
  let f : ℕ → ℝ := fun n ↦ (n : ℝ) * ((n : ℝ) - 1) * (y ^ n / (n.factorial : ℝ))
  have hshift : (fun n : ℕ ↦ f (n + 2)) = fun n : ℕ ↦ y ^ 2 * (y ^ n / (n.factorial : ℝ)) := by
    funext n
    have h0 : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
    simp only [f, Nat.factorial_succ, pow_succ]
    push_cast
    field_simp
    ring
  have hfalling : HasSum f (y ^ 2 * exp y) := by
    have h : HasSum (fun n : ℕ ↦ f (n + 2)) (y ^ 2 * exp y) := by
      rw [hshift]; exact (saddleExpSeries_hasSum y).mul_left _
    simpa [f, Finset.sum_range_succ] using h.sum_range_add
  have hfun : (fun n : ℕ ↦ ((n : ℝ) + (n : ℝ) ^ 2) * (y ^ n / (n.factorial : ℝ))) =
      fun n : ℕ ↦ 2 * ((n : ℝ) * (y ^ n / (n.factorial : ℝ))) + f n := by
    funext n; simp only [f]; ring
  rw [hfun, show (2 * y + y ^ 2) * exp y = 2 * (y * exp y) + y ^ 2 * exp y by ring]
  exact ((saddleExpSeries_firstMoment_hasSum y).mul_left 2).add hfalling

/-- Alternating tail bound for `e^{-y}`: as soon as `2y ≤ m + 1`, the remainder of the
exponential series after `m` terms is at most `2 yᵐ/m!`. -/
theorem expSeries_alternating_tail_bound {y : ℝ} (hy : 0 ≤ y) {m : ℕ}
    (hym : 2 * y ≤ (m : ℝ) + 1) :
    |exp (-y) - ∑ n ∈ Finset.range m, (-y) ^ n / (n.factorial : ℝ)| ≤
      2 * (y ^ m / (m.factorial : ℝ)) := by
  have key : ∀ k : ℕ, y ^ (m + k) / ((m + k).factorial : ℝ) ≤
      y ^ m / (m.factorial : ℝ) * (1 / 2) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h0 : ((m + k).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (m + k).factorial_ne_zero
      have hden : (0 : ℝ) < (m : ℝ) + k + 1 := by positivity
      have hratio : y / ((m : ℝ) + k + 1) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ hden (by norm_num)]
        nlinarith [Nat.cast_nonneg (α := ℝ) k]
      have hstep : y ^ (m + (k + 1)) / ((m + (k + 1)).factorial : ℝ) =
          y ^ (m + k) / ((m + k).factorial : ℝ) * (y / ((m : ℝ) + k + 1)) := by
        rw [show m + (k + 1) = (m + k) + 1 from rfl, Nat.factorial_succ, pow_succ]
        push_cast
        field_simp
      rw [hstep, pow_succ, ← mul_assoc]
      exact mul_le_mul ih hratio (by positivity) (by positivity)
  let f : ℕ → ℝ := fun n ↦ (-y) ^ n / (n.factorial : ℝ)
  have hwhole : HasSum f (exp (-y)) := saddleExpSeries_hasSum (-y)
  have htail : Summable (fun n : ℕ ↦ f (n + m)) := (summable_nat_add_iff m).mpr hwhole.summable
  have hnorm : Summable (fun n : ℕ ↦ ‖f (n + m)‖) := htail.norm
  have hgeometric : Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) := by
    apply summable_geometric_of_norm_lt_one
    norm_num
  have hmajor : Summable (fun n : ℕ ↦ (y ^ m / (m.factorial : ℝ)) * ((1 / 2 : ℝ) ^ n)) :=
    hgeometric.mul_left (y ^ m / (m.factorial : ℝ))
  have hdecomp : (∑ n ∈ Finset.range m, f n) + (∑' n : ℕ, f (n + m)) = exp (-y) :=
    HasSum.unique htail.hasSum.sum_range_add hwhole
  have hterms (n : ℕ) : ‖f (n + m)‖ ≤ (y ^ m / (m.factorial : ℝ)) * ((1 / 2 : ℝ) ^ n) := by
    have hfact : 0 < ((n + m).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (n + m)
    have hnf : ‖f (n + m)‖ = y ^ (m + n) / ((m + n).factorial : ℝ) := by
      dsimp only [f]
      rw [Real.norm_eq_abs, abs_div, abs_pow, abs_neg, abs_of_nonneg hy, abs_of_pos hfact,
        Nat.add_comm n m]
    rw [hnf]
    exact key n
  change |exp (-y) - (∑ n ∈ Finset.range m, f n)| ≤ 2 * (y ^ m / (m.factorial : ℝ))
  have hidentity : exp (-y) - (∑ n ∈ Finset.range m, f n) = ∑' n : ℕ, f (n + m) := by linarith
  calc
    |exp (-y) - (∑ n ∈ Finset.range m, f n)| = ‖∑' n : ℕ, f (n + m)‖ := by
      rw [Real.norm_eq_abs, hidentity]
    _ ≤ ∑' n : ℕ, ‖f (n + m)‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, (y ^ m / (m.factorial : ℝ)) * ((1 / 2 : ℝ) ^ n) :=
      Summable.tsum_le_tsum hterms hnorm hmajor
    _ = 2 * (y ^ m / (m.factorial : ℝ)) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num
      ring

/-- Report (79): after multiplication by `eʸ`, the truncated residue sum `S_N(y)` of report (78)
approximates `e^{-y}` with an error controlled by `1/λ` and by the exponential tail. -/
theorem exists_plusSaddleSmallRadius_relativeFiniteResidue_error {ε : ℝ} (hε : 0 < ε)
    (horder : a₀ε ε ≤ Aε ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ : ℝ), 0 < ℓ → ∀ N : ℕ, 2 * (N : ℝ) ≤ ℓ → ∀ y : ℝ, 0 ≤ y →
      2 * y ≤ (N : ℝ) + 2 →
        exp y * |(∑ n ∈ Finset.range (N + 1), ((-y) ^ n / (n.factorial : ℝ)) * A_ℓn ε ℓ n) -
            exp (-y)| ≤
          (C / ℓ) * exp (C * (N : ℝ) ^ 2 / ℓ) * (2 * y + y ^ 2) * exp (2 * y) +
            2 * exp y * (y ^ (N + 1) / ((N + 1).factorial : ℝ)) := by
  obtain ⟨C, hC, hcoeff⟩ := exists_plusSaddleSmallRadiusCoefficient_error hε horder
  refine ⟨C, hC, fun ℓ hℓ N hN y hy hyratio ↦ ?_⟩
  set K : ℝ := C / ℓ * exp (C * (N : ℝ) ^ 2 / ℓ) with hK
  have hKnonneg : 0 ≤ K := by rw [hK]; positivity
  have hweight : (∑ n ∈ Finset.range (N + 1), y ^ n / (n.factorial : ℝ) *
      |A_ℓn ε ℓ n - 1|) ≤ K * ((2 * y + y ^ 2) * exp y) := by
    calc
      (∑ n ∈ Finset.range (N + 1), y ^ n / (n.factorial : ℝ) * |A_ℓn ε ℓ n - 1|) ≤
          ∑ n ∈ Finset.range (N + 1),
            K * (((n : ℝ) + (n : ℝ) ^ 2) * (y ^ n / (n.factorial : ℝ))) := by
        refine Finset.sum_le_sum fun n hn ↦ ?_
        have hnN : (n : ℝ) ≤ (N : ℝ) := Nat.cast_le.2 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn))
        have hterm : (0 : ℝ) ≤ y ^ n / (n.factorial : ℝ) := by positivity
        have hbase : (0 : ℝ) ≤ C * ((n : ℝ) + (n : ℝ) ^ 2) / ℓ := by positivity
        have hq : C * (n : ℝ) ^ 2 / ℓ ≤ C * (N : ℝ) ^ 2 / ℓ := by gcongr
        calc
          y ^ n / (n.factorial : ℝ) * |A_ℓn ε ℓ n - 1| ≤ y ^ n / (n.factorial : ℝ) *
              (C * ((n : ℝ) + (n : ℝ) ^ 2) / ℓ * exp (C * (n : ℝ) ^ 2 / ℓ)) :=
            mul_le_mul_of_nonneg_left (hcoeff ℓ hℓ n (by linarith)) hterm
          _ ≤ y ^ n / (n.factorial : ℝ) *
              (C * ((n : ℝ) + (n : ℝ) ^ 2) / ℓ * exp (C * (N : ℝ) ^ 2 / ℓ)) := by gcongr
          _ = K * (((n : ℝ) + (n : ℝ) ^ 2) * (y ^ n / (n.factorial : ℝ))) := by rw [hK]; ring
      _ = K * ∑ n ∈ Finset.range (N + 1),
            ((n : ℝ) + (n : ℝ) ^ 2) * (y ^ n / (n.factorial : ℝ)) := (Finset.mul_sum _ _ _).symm
      _ ≤ K * ((2 * y + y ^ 2) * exp y) := by
        gcongr
        exact sum_le_hasSum _ (fun n _ ↦ by positivity) (hasSum_expSeries_polynomialMoment y)
  have hsplit : |(∑ n ∈ Finset.range (N + 1), (-y) ^ n / (n.factorial : ℝ) * A_ℓn ε ℓ n) -
      exp (-y)| ≤ (∑ n ∈ Finset.range (N + 1), y ^ n / (n.factorial : ℝ) *
        |A_ℓn ε ℓ n - 1|) + 2 * (y ^ (N + 1) / ((N + 1).factorial : ℝ)) := by
    have hsum : (∑ n ∈ Finset.range (N + 1), (-y) ^ n / (n.factorial : ℝ) * A_ℓn ε ℓ n) =
        (∑ n ∈ Finset.range (N + 1), (-y) ^ n / (n.factorial : ℝ) * (A_ℓn ε ℓ n - 1)) +
          ∑ n ∈ Finset.range (N + 1), (-y) ^ n / (n.factorial : ℝ) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun n _ ↦ by ring
    rw [hsum, show ∀ a b c : ℝ, a + b - c = a - (c - b) by intros; ring]
    refine (abs_sub _ _).trans (add_le_add ?_ (expSeries_alternating_tail_bound hy
      (m := N + 1) (by push_cast; linarith)))
    refine (Finset.abs_sum_le_sum_abs _ _).trans_eq (Finset.sum_congr rfl fun n _ ↦ ?_)
    have hfact : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.2 n.factorial_pos
    rw [abs_mul, abs_div, abs_pow, abs_neg, abs_of_nonneg hy, abs_of_pos hfact]
  calc
    exp y * |(∑ n ∈ Finset.range (N + 1), (-y) ^ n / (n.factorial : ℝ) * A_ℓn ε ℓ n) -
        exp (-y)| ≤ exp y * (K * ((2 * y + y ^ 2) * exp y) +
          2 * (y ^ (N + 1) / ((N + 1).factorial : ℝ))) :=
      mul_le_mul_of_nonneg_left (hsplit.trans (by linarith)) (exp_pos y).le
    _ = K * (2 * y + y ^ 2) * exp (2 * y) +
        2 * exp y * (y ^ (N + 1) / ((N + 1).factorial : ℝ)) := by
      rw [two_mul, exp_add]; ring

end

end CohnElkies
