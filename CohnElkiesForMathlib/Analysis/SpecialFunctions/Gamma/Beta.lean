import Mathlib
import CohnElkiesForMathlib.Analysis.Complex.Trigonometric

/-!
# The Gamma function on the imaginary axis and the line `Re z = 1/2`

From the reflection formula `Γ(z) Γ(1 - z) = π / sin (π z)`:
`‖Γ(1/2 + ix)‖² = π / cosh (π x)`, `‖Γ(ix)‖² = π / (x sinh (π x))` and
`Γ(1 + ix) Γ(1 - ix) = π x / sinh (π x)`; the quotient of the first two reads
`log ‖Γ(ix)‖ - log ‖Γ(1/2 + ix)‖ = ½ log (coth (π|x|) / |x|)`.
-/

open Real
open Complex (I)

/-- `|Γ(1/2 + ib)|² = π / cosh(πb)`; report (7). -/
theorem Complex.norm_Gamma_one_half_add_I_mul_sq (x : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + I * (x : ℂ))‖ ^ 2 = π / Real.cosh (π * x) := by
  set z : ℂ := (1 / 2 : ℂ) + I * (x : ℂ) with hz
  have harg : 1 - z = starRingEnd ℂ z := by
    rw [hz]
    simp only [map_add, map_div₀, Complex.conj_ofReal, Complex.conj_I, Complex.conj_ofNat,
      map_mul, map_one]
    ring
  have hsin : Complex.sin ((π : ℂ) * z) = (Real.cosh (π * x) : ℂ) := by
    rw [show (π : ℂ) * z = π / 2 + (π * x : ℂ) * I by rw [hz]; ring, Complex.sin_add_mul_I,
      Complex.sin_pi_div_two, Complex.cos_pi_div_two]
    simp
  have hnorm : Complex.Gamma z * starRingEnd ℂ (Complex.Gamma z) = (‖Complex.Gamma z‖ ^ 2 : ℂ) := by
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have href := Complex.Gamma_mul_Gamma_one_sub z
  rw [harg, Complex.Gamma_conj, hsin, hnorm] at href
  exact_mod_cast href

/-- `|Γ(ib)|² = π / (b sinh(πb))`; report (7). -/
theorem Complex.norm_Gamma_I_mul_sq {x : ℝ} (hx : x ≠ 0) :
    ‖Complex.Gamma (I * (x : ℂ))‖ ^ 2 = π / (x * Real.sinh (π * x)) := by
  set z : ℂ := I * (x : ℂ) with hz
  have hzne : -z ≠ 0 := by
    rw [hz]
    exact neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hx))
  have hrec : Complex.Gamma (1 - z) = (-z) * Complex.Gamma (-z) := by
    convert! Complex.Gamma_add_one (-z) hzne using 1; ring_nf
  have hconjarg : -z = starRingEnd ℂ z := by
    rw [hz]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hconj : Complex.Gamma (-z) = starRingEnd ℂ (Complex.Gamma z) := by
    rw [hconjarg, Complex.Gamma_conj]
  have hsinarg : (π : ℂ) * z = (π * x : ℂ) * I := by
    rw [hz]; ring
  have hsin : Complex.sin ((π : ℂ) * z) = (Real.sinh (π * x) : ℂ) * I := by
    rw [hsinarg, Complex.sin_mul_I, Complex.ofReal_sinh, Complex.ofReal_mul]
  have hsinh : Real.sinh (π * x) ≠ 0 := Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hx)
  have hprod : Complex.Gamma z * starRingEnd ℂ (Complex.Gamma z) = (‖Complex.Gamma z‖ ^ 2 : ℂ) := by
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have href := Complex.Gamma_mul_Gamma_one_sub z
  rw [hrec, hconj, hsin] at href
  have hidentity : (‖Complex.Gamma z‖ ^ 2 * (x * Real.sinh (π * x)) : ℂ) = π := by
    calc (‖Complex.Gamma z‖ ^ 2 * (x * Real.sinh (π * x)) : ℂ) =
          (Complex.Gamma z * starRingEnd ℂ (Complex.Gamma z)) * (x * Real.sinh (π * x) : ℂ) := by
          rw [hprod]
      _ = (Complex.Gamma z * (-z * starRingEnd ℂ (Complex.Gamma z))) *
            ((Real.sinh (π * x) : ℂ) * I) := by
          rw [hz]
          ring_nf
          simp [Complex.I_sq]
      _ = ((π : ℂ) / ((Real.sinh (π * x) : ℂ) * I)) * ((Real.sinh (π * x) : ℂ) * I) := by rw [href]
      _ = (π : ℂ) :=
          div_mul_cancel₀ _ (mul_ne_zero (Complex.ofReal_ne_zero.mpr hsinh) Complex.I_ne_zero)
  exact (eq_div_iff (mul_ne_zero hx hsinh)).2 (by exact_mod_cast hidentity)

/-- `Γ(1 + ix) Γ(1 - ix) = πx / sinh (πx)`, from the reflection formula; report (7). -/
theorem Complex.Gamma_one_add_I_mul_mul_Gamma_one_sub_I_mul {x : ℝ} (hx : x ≠ 0) :
    Complex.Gamma (1 + I * (x : ℂ)) * Complex.Gamma (1 - I * (x : ℂ)) =
      (π * x / Real.sinh (π * x) : ℂ) := by
  set z : ℂ := I * (x : ℂ) with hzdef
  have hz : z ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hx)
  have hplus : Complex.Gamma (1 + z) = z * Complex.Gamma z := by
    convert! Complex.Gamma_add_one z hz using 1; ring_nf
  have hminus : Complex.Gamma (1 - z) = -z * Complex.Gamma (-z) := by
    convert! Complex.Gamma_add_one (-z) (neg_ne_zero.mpr hz) using 1; ring_nf
  have hprod : Complex.Gamma z * Complex.Gamma (-z) = (‖Complex.Gamma z‖ ^ 2 : ℂ) := by
    rw [show -z = starRingEnd ℂ z by rw [hzdef]; simp, Complex.Gamma_conj, mul_comm,
      ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have hneg : z * -z = (x ^ 2 : ℂ) := by
    rw [show z * -z = -(I ^ 2) * (x : ℂ) ^ 2 by rw [hzdef]; ring, Complex.I_sq]
    ring
  have hnormsq : (‖Complex.Gamma z‖ : ℂ) ^ 2 = ((π / (x * Real.sinh (π * x)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, hzdef, Complex.norm_Gamma_I_mul_sq hx]
  have hsinh : Real.sinh (π * x) ≠ 0 := Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hx)
  rw [hplus, hminus, show z * Complex.Gamma z * (-z * Complex.Gamma (-z)) =
    z * -z * (Complex.Gamma z * Complex.Gamma (-z)) by ring, hneg, hprod, hnormsq]
  norm_cast
  field_simp

/-- The quotient of the two modulus identities on the critical line, as a `coth` quotient:
`log ‖Γ(ix)‖ - log ‖Γ(1/2 + ix)‖ = ½ log (coth (π|x|) / |x|)`; report Lemma 3.2. -/
theorem Complex.log_norm_Gamma_I_mul_sub_log_norm_Gamma_one_half_add_I_mul {x : ℝ} (hx : x ≠ 0) :
    Real.log ‖Complex.Gamma (I * (x : ℂ))‖ -
        Real.log ‖Complex.Gamma ((1 / 2 : ℂ) + I * (x : ℂ))‖ =
      1 / 2 * Real.log (Real.coth (π * |x|) / |x|) := by
  have hsinh : Real.sinh (π * x) ≠ 0 := Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hx)
  have hden : x * Real.sinh (π * x) ≠ 0 := mul_ne_zero hx hsinh
  have hcosh : Real.cosh (π * x) ≠ 0 := (Real.cosh_pos _).ne'
  have key : ∀ (w : ℂ) (v : ℝ), v ≠ 0 → ‖Complex.Gamma w‖ ^ 2 = π / v →
      2 * Real.log ‖Complex.Gamma w‖ = Real.log π - Real.log v := fun w v hv hw ↦ by
    rw [show 2 * Real.log ‖Complex.Gamma w‖ = Real.log (‖Complex.Gamma w‖ ^ 2) by
      rw [Real.log_pow]; norm_num, hw, Real.log_div Real.pi_ne_zero hv]
  have himaginary := key _ _ hden (Complex.norm_Gamma_I_mul_sq hx)
  have hhalf := key _ _ hcosh (Complex.norm_Gamma_one_half_add_I_mul_sq x)
  have hcoth : Real.coth (π * |x|) / |x| = Real.cosh (π * x) / (x * Real.sinh (π * x)) := by
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · rw [abs_of_neg hneg, show π * -x = -(π * x) by ring]
      unfold Real.coth
      rw [Real.cosh_neg, Real.sinh_neg]
      field_simp
    · rw [abs_of_pos hpos]
      unfold Real.coth
      field_simp
  rw [hcoth, Real.log_div hcosh hden]
  linarith
