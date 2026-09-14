import Mathlib

/-!
# The parameters and polynomials of the upper-bound construction (report §4)

The regularisation parameters `a₀ = ε²`, `A = log (1/ε)`, `B = ε⁻³`, `Q = exp (-3εB/8)`,
`b(a) = 1 - 2ε(1 + a)`, `β = ε/4` of report §4, the cubic polynomials
`P₊(ζ) = 1 + ζ² + β + iζ(1 + ζ²)`, `P₋(ζ) = 1 + ζ² + β - iζ(1 + ζ²)` of the saddle-point pair
`f₊`, `f₋` (report (40)) and the polynomial `P₀(ζ) = -(1 + ζ²)` of the self-Fourier function
`f₀` (report, Lemma 4.3), with their values on the imaginary axis.
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Real

/-- The parameter `a₀ = ε²` of the upper bound construction. -/
def a₀ε (ε : ℝ) : ℝ := ε ^ 2

/-- The parameter `A = log (1/ε)` of the upper bound construction. -/
def Aε (ε : ℝ) : ℝ := log (1 / ε)

/-- The parameter `B = ε⁻³` of the upper bound construction. -/
def Bε (ε : ℝ) : ℝ := ε⁻¹ ^ 3

/-- The shell weight `Q = exp (-3 ε B / 8)` of the upper bound construction. -/
def Qε (ε : ℝ) : ℝ := exp (-3 * ε * Bε ε / 8)

/-- The parameter `b(a) = 1 - 2 ε (1 + a)` of the upper bound construction. -/
def bε (ε a : ℝ) : ℝ := 1 - 2 * ε * (1 + a)

/-- The parameter `β = ε / 4` of the polynomials `P₊`, `P₋`. -/
def β (ε : ℝ) : ℝ := ε / 4

/-- The polynomial `P₊(ζ) = 1 + ζ² + β + iζ(1 + ζ²)` of the report. -/
def PPlus (ε : ℝ) (z : ℂ) : ℂ := 1 + z ^ 2 + β ε + I * z * (1 + z ^ 2)

/-- The polynomial `P₋(ζ) = 1 + ζ² + β - iζ(1 + ζ²)` of the report. -/
def PMinus (ε : ℝ) (z : ℂ) : ℂ := 1 + z ^ 2 + β ε - I * z * (1 + z ^ 2)

theorem shellWeight_pos (ε : ℝ) : 0 < Qε ε := exp_pos _

theorem beta_pos {ε : ℝ} (hε : 0 < ε) : 0 < β ε := div_pos hε (by norm_num)

/-- `P₊(iu) = β + (1 - u)² (1 + u)` is real. -/
theorem plusPolynomial_imaginary (ε u : ℝ) :
    PPlus ε (I * u) = β ε + (1 - u) ^ 2 * (1 + u) := by
  apply Complex.ext <;> simp [PPlus, pow_two] <;> ring

/-- `P₋(iu) = β + (1 - u) (1 + u)²` is real. -/
theorem minusPolynomial_imaginary (ε u : ℝ) :
    PMinus ε (I * u) = β ε + (1 - u) * (1 + u) ^ 2 := by
  apply Complex.ext <;> simp [PMinus, pow_two] <;> ring

theorem plusPolynomial_imaginary_re_pos {ε u : ℝ} (hε : 0 < ε) (hu : -1 < u) :
    0 < (PPlus ε (I * u)).re := by
  rw [plusPolynomial_imaginary]
  norm_cast
  exact add_pos_of_pos_of_nonneg (beta_pos hε) (mul_nonneg (sq_nonneg _) (by linarith))

theorem minusPolynomial_imaginary_re_neg {ε u : ℝ} (hε : 0 < ε) (hu : 1 + ε / 4 ≤ u) :
    (PMinus ε (I * u)).re < 0 := by
  rw [minusPolynomial_imaginary]
  norm_cast
  rw [β]
  have hs : 4 ≤ (1 + u) ^ 2 := by nlinarith [sq_nonneg (u - 1)]
  nlinarith [mul_le_mul_of_nonneg_left hs hε.le, mul_nonneg (sub_nonneg.2 hu) (sq_nonneg (1 + u))]

end

noncomputable section

open Real

/-! ### The polynomial `P₀(ζ) = -(1 + ζ²)` of the self-Fourier function `f₀` (report, Lemma 4.3) -/

/-- The polynomial `P₀(ζ) = -(1 + ζ²)` of the self-Fourier function `f₀` of the report. -/
def PZero (z : ℂ) : ℂ := -(1 + z ^ 2)

/-- `P₀` is even: the self-Fourier symmetry of report (40). -/
theorem PZero_neg (z : ℂ) : PZero (-z) = PZero z := by simp [PZero]

/-- `P₀(-i) = 0`, report (42): the residue of `M₀` at `z = 0` vanishes. -/
theorem PZero_neg_I : PZero (-I) = 0 := by simp [PZero]

theorem differentiable_PZero : Differentiable ℂ PZero := by unfold PZero; fun_prop

/-- `P₀(iu) = u² - 1` is real. -/
theorem PZero_imaginary (u : ℝ) : PZero (I * u) = u ^ 2 - 1 := by
  apply Complex.ext <;> simp [PZero, pow_two] <;> ring

/-- `P₀(iu) = u² - 1 ≥ (ε/4)(2 + ε/4)` for `u ≥ 1 + ε/4` (report §4.3). -/
theorem PZero_imaginary_re_ge {ε u : ℝ} (hε : 0 < ε) (hu : 1 + ε / 4 ≤ u) :
    ε / 4 * (2 + ε / 4) ≤ (PZero (I * u)).re := by
  rw [PZero_imaginary]
  norm_cast
  have h1 : ε / 4 ≤ u - 1 := by linarith
  have h2 : 2 + ε / 4 ≤ u + 1 := by linarith
  nlinarith [mul_le_mul h1 h2 (by linarith) (by linarith)]

theorem PZero_imaginary_re_pos {ε u : ℝ} (hε : 0 < ε) (hu : 1 + ε / 4 ≤ u) :
    0 < (PZero (I * u)).re :=
  (by positivity : (0 : ℝ) < ε / 4 * (2 + ε / 4)).trans_le (PZero_imaginary_re_ge hε hu)

theorem norm_PZero_imaginary {ε u : ℝ} (hε : 0 < ε) (hu : 1 + ε / 4 ≤ u) :
    ‖PZero (I * u)‖ = u ^ 2 - 1 := by
  have h : 0 ≤ u ^ 2 - 1 := by nlinarith
  rw [PZero_imaginary]
  norm_cast
  exact Real.norm_of_nonneg h

theorem norm_PZero_le (ε : ℝ) (z : ℂ) : ‖PZero z‖ ≤ (1 + |β ε|) * (1 + ‖z‖) ^ 3 := by
  have h0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hbase : ‖PZero z‖ ≤ 1 + ‖z‖ ^ 2 := by
    unfold PZero
    rw [norm_neg]
    exact (norm_add_le _ _).trans_eq (by simp)
  have hcube : 1 + ‖z‖ ^ 2 ≤ (1 + ‖z‖) ^ 3 := by nlinarith [pow_nonneg h0 3, mul_nonneg h0 h0]
  calc ‖PZero z‖ ≤ (1 + ‖z‖) ^ 3 := hbase.trans hcube
    _ ≤ (1 + |β ε|) * (1 + ‖z‖) ^ 3 :=
        le_mul_of_one_le_left (by positivity) (by linarith [abs_nonneg (β ε)])

theorem PZero_conj (z : ℂ) : starRingEnd ℂ (PZero z) = PZero (-starRingEnd ℂ z) := by
  simp [PZero]

/-- The increment `P₀(T + iu) - P₀(iu) = -(T² + 2uT i)` along the line `Im ζ = u`. -/
theorem PZero_sub_imaginary (T u : ℝ) :
    PZero ((T : ℂ) + I * u) - PZero (I * u) = -((T : ℂ) ^ 2 + 2 * u * T * I) := by
  unfold PZero
  ring

theorem norm_PZero_sub_imaginary_le (T u : ℝ) :
    ‖PZero ((T : ℂ) + I * u) - PZero (I * u)‖ ≤ T ^ 2 + 2 * |u| * |T| := by
  rw [PZero_sub_imaginary, norm_neg]
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_mul, Complex.norm_I, mul_one]
  norm_cast
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg T), abs_mul, abs_mul, abs_two]

end

end CohnElkies
