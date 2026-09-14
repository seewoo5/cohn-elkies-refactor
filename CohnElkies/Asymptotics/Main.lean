import CohnElkies.Asymptotics.Framework
import CohnElkies.Asymptotics.Stirling
import CohnElkies.Admissible.Nonempty
import CohnElkies.Admissible.Radialization
import CohnElkies.LowerBound.Main
import CohnElkies.LowerBound.Balanced
import CohnElkies.UpperBound.Signs

/-!
# Theorem 1.1 of the report: the exponential rate of the Cohn–Elkies bound

The positivity of the exponent `(1/2) log₂ (2π/e)`, the uniform lower bound from Proposition 3.7
for every `f ∈ 𝒜_d` (`uniformAdmissibleLowerBound_of_signRadius`, via the rotational average of
`f`, report §2.1), the passage from the normalized program to
`LP_d^{1/d}`, `log (LP_d)/d` and `log₂ (LP_d)/d` via Stirling's formula, and the assembly of both
bounds: `sharpAsymptotics` gives `inf_{f ∈ 𝒜_d} (f(0)/𝓕f(0))^{1/d}/√d → 1/π`,
`LP_d^{1/d} → √(e/(2π))`, `log (LP_d)/d → (1/2) log (e/(2π))` and
`log₂ (LP_d)/d → -(1/2) log₂ (2π/e)`.
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Real

theorem log_criticalPackingBase : log criticalPackingBase = 1 / 2 * log (exp 1 / (2 * π)) := by
  rw [criticalPackingBase, log_sqrt (by positivity)]
  ring

theorem logb_criticalPackingBase : logb 2 criticalPackingBase = -criticalBinaryExponent := by
  simp only [logb, criticalBinaryExponent, log_criticalPackingBase]
  rw [log_div (by positivity) (by positivity), log_div (by positivity) (by positivity), log_exp]
  ring

/-- The exponent of Theorem 1.1 is positive, since `2π > e`. -/
theorem criticalBinaryExponent_pos : 0 < criticalBinaryExponent := by
  have hbase : criticalPackingBase < 1 := by
    rw [criticalPackingBase]
    refine (sqrt_lt' one_pos).2 ?_
    rw [one_pow, div_lt_one (by positivity)]
    linarith [exp_one_lt_three, pi_gt_three]
  have h : logb 2 criticalPackingBase < 0 := logb_neg (by norm_num) criticalPackingBase_pos hbase
  rw [logb_criticalPackingBase] at h
  linarith

end

noncomputable section

open Filter Real
open scoped Topology

/-- Theorem 3.8 of the report before Stirling's formula: below the critical radius `1/π`, every
admissible `f ∈ 𝒜_d` of every large dimension has normalized cost at least `c`. By the radial
reduction of §2.1, `f` is first replaced by its rotational average, which has the same cost. -/
theorem uniformAdmissibleLowerBound_of_signRadius (hsign : UniformAntiFourierSignRadius) :
    UniformAdmissibleLowerBound := by
  intro c hc
  rcases le_or_gt c 0 with hc0 | hc0
  · exact .of_forall fun d f ↦ hc0.trans (normalizedCost_nonneg f)
  · filter_upwards [hsign c hc0 hc, eventually_gt_atTop 0] with d hno hd f
    rw [← f.normalizedCost_radialize]
    exact normalizedCost_ge_of_no_antiFourierWitness f.radialize hd c hno

theorem normalizedProgram_eq_quotientInf_root_unconditional (d : ℕ) :
    normalizedProgram d = quotientRootMap d (sInf (quotientSet d)) :=
  normalizedProgram_eq_quotientInf_root d (admissible_nonempty d)

theorem quotientInf_nonneg_unconditional (d : ℕ) : 0 ≤ sInf (quotientSet d) :=
  quotientInf_nonneg d (admissible_nonempty d)

theorem linearProgram_nonneg (d : ℕ) : 0 ≤ LP d :=
  mul_nonneg (geometricFactor_pos d).le (quotientInf_nonneg_unconditional d)

/-- The two constants of Theorem 1.1 match: `√(2πe)/2 · (1/π) = √(e/(2π))`. -/
theorem geometricLimit_mul_criticalRadius :
    √(2 * π * exp 1) / 2 * criticalRadius = criticalPackingBase := by
  have hπ : π ≠ 0 := pi_ne_zero
  have h : exp 1 / (2 * π) = 2 * π * exp 1 / (2 * π) ^ 2 := by field_simp
  rw [criticalRadius, criticalPackingBase, h, sqrt_div (by positivity), sqrt_sq (by positivity)]
  ring

theorem sharpPackingRoot_of_sharpQuotient (hquotient : SharpQuotientAsymptotic) :
    SharpPackingRootAsymptotic := by
  have hproduct := tendsto_packingGeometricRoot.mul hquotient
  rw [geometricLimit_mul_criticalRadius] at hproduct
  unfold SharpPackingRootAsymptotic
  refine hproduct.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with d hd
  exact (linearProgram_root_eq_geometric_mul_normalizedProgram hd (admissible_nonempty d)).symm

theorem eventually_linearProgram_pos_of_sharpQuotient (hquotient : SharpQuotientAsymptotic) :
    ∀ᶠ d : ℕ in atTop, 0 < LP d := by
  have hnorm : ∀ᶠ d : ℕ in atTop, 0 < normalizedProgram d :=
    hquotient.eventually (Ioi_mem_nhds criticalRadius_pos)
  filter_upwards [hnorm, eventually_gt_atTop 0] with d hpositive hd
  have hdreal : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have hinf : 0 < sInf (quotientSet d) := by
    refine (quotientInf_nonneg_unconditional d).lt_of_ne' fun hzero ↦ ?_
    rw [normalizedProgram_eq_quotientInf_root_unconditional d, hzero] at hpositive
    simp [quotientRootMap, hdreal] at hpositive
  exact mul_pos (geometricFactor_pos d) hinf

theorem sharpLog_of_sharpQuotient (hquotient : SharpQuotientAsymptotic) : SharpLogAsymptotic := by
  have hlogs := (sharpPackingRoot_of_sharpQuotient hquotient).log criticalPackingBase_pos.ne'
  rw [log_criticalPackingBase] at hlogs
  unfold SharpLogAsymptotic
  refine hlogs.congr' ?_
  filter_upwards [eventually_linearProgram_pos_of_sharpQuotient hquotient] with d hd
  rw [log_rpow hd]
  ring

/-- Base-2 form of Theorem 1.1: `log₂ (LP_d)/d → -(1/2) log₂ (2π/e)`. -/
def SharpBinaryLogAsymptotic : Prop :=
  Tendsto (fun d : ℕ ↦ logb 2 (LP d) / (d : ℝ)) atTop (𝓝 (-criticalBinaryExponent))

theorem sharpBinaryLog_of_sharpQuotient (hquotient : SharpQuotientAsymptotic) :
    SharpBinaryLogAsymptotic := by
  have hscaled := (sharpLog_of_sharpQuotient hquotient).div_const (log 2)
  rw [show 1 / 2 * log (exp 1 / (2 * π)) / log 2 = -criticalBinaryExponent from by
    rw [← log_criticalPackingBase, ← logb, logb_criticalPackingBase]] at hscaled
  exact hscaled.congr fun d ↦ by rw [logb]; ring

theorem saddleSourceSchwartzRealization : SaddleSourceSchwartzRealization :=
  fun _ hε horder _ hd ↦ ⟨minusSaddleSchwartz hε hd horder, plusSaddleSchwartz hε hd horder,
    fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- Theorem 1.1 in its four forms, from the eventual signs of the saddle-point pair `f_ε^±`. -/
theorem sharpAsymptotics_of_saddleSourceEventualSigns (hsigns : SaddleSourceEventualSigns) :
    SharpQuotientAsymptotic ∧ SharpPackingRootAsymptotic ∧
      SharpLogAsymptotic ∧ SharpBinaryLogAsymptotic := by
  have hquotient := sharpQuotient_of_uniform_lower_and_ordered_upper
    (uniformAdmissibleLowerBound_of_signRadius uniformAntiFourierSignRadius)
    (saddleOrderedUpperConstruction saddleSourceSchwartzRealization hsigns)
  exact ⟨hquotient, sharpPackingRoot_of_sharpQuotient hquotient,
    sharpLog_of_sharpQuotient hquotient, sharpBinaryLog_of_sharpQuotient hquotient⟩

/-- Theorem 1.1 of the report, in its four equivalent forms. -/
theorem sharpAsymptotics : SharpQuotientAsymptotic ∧ SharpPackingRootAsymptotic ∧
    SharpLogAsymptotic ∧ SharpBinaryLogAsymptotic :=
  sharpAsymptotics_of_saddleSourceEventualSigns saddleSourceEventualSigns

/-- `inf_{f ∈ 𝒜_d} (f(0)/𝓕f(0))^{1/d} / √d → 1/π`. -/
theorem sharpQuotientAsymptotic : SharpQuotientAsymptotic := sharpAsymptotics.1

/-- `LP_d^{1/d} → √(e/(2π))`. -/
theorem sharpPackingRootAsymptotic : SharpPackingRootAsymptotic := sharpAsymptotics.2.1

/-- `log (LP_d)/d → (1/2) log (e/(2π))`. -/
theorem sharpLogAsymptotic : SharpLogAsymptotic := sharpAsymptotics.2.2.1

/-- `log₂ (LP_d)/d → -(1/2) log₂ (2π/e)`. -/
theorem sharpBinaryLogAsymptotic : SharpBinaryLogAsymptotic := sharpAsymptotics.2.2.2

end

end CohnElkies
