import CohnElkies.Radial
import CohnElkiesForMathlib.Analysis.SpecialFunctions.Stirling
import CohnElkiesForMathlib.Topology.Sequences

/-!
# The geometric factor of the Cohn–Elkies bound and Stirling's formula (report (28), (31))

The normalization `x ↦ x^{1/d}/√d` turning quotients into normalized costs, the splitting
`LP_d^{1/d} = (v_d/2^d)^{1/d} √d · normalizedProgram d`, the odd-dimensional volume formula
`v_{2k+1} = π^k 2^{2k+1} k!/(2k+1)!`, and Stirling's formula for the geometric factor:
`(v_d/2^d)^{1/d} √d → √(2πe)/2` (`tendsto_packingGeometricRoot`).
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Real Set

/-- The normalization `x ↦ x^{1/d}/√d` turning a quotient into a normalized cost (report (31)). -/
def quotientRootMap (d : ℕ) (x : ℝ) : ℝ := x ^ (d : ℝ)⁻¹ / √d

/-- The normalized program is the normalization of `inf_{f ∈ 𝒜_d} f(0)/𝓕f(0)`. -/
theorem normalizedProgram_eq_quotientInf_root (d : ℕ) (hadmissible : Nonempty (Admissible d)) :
    normalizedProgram d = quotientRootMap d (sInf (quotientSet d)) := by
  obtain ⟨f⟩ := hadmissible
  have hmono : MonotoneOn (quotientRootMap d) (quotientSet d) := by
    rintro x ⟨g, rfl⟩ y - hxy
    unfold quotientRootMap
    exact div_le_div_of_nonneg_right
      (rpow_le_rpow (quotient_pos g).le hxy (by positivity)) (sqrt_nonneg _)
  have hrange : Set.range (normalizedCost (d := d)) = quotientRootMap d '' quotientSet d := by
    ext y
    constructor
    · rintro ⟨g, rfl⟩; exact ⟨quotient g, ⟨g, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩; exact ⟨g, rfl⟩
  unfold normalizedProgram
  rw [hrange]
  exact (MonotoneOn.map_csInf_of_continuousWithinAt
    ((continuous_rpow_const (by positivity)).div_const _).continuousWithinAt hmono
    ⟨quotient f, f, rfl⟩ (quotientSet_bddBelow d)).symm

theorem quotientInf_nonneg (d : ℕ) (hadmissible : Nonempty (Admissible d)) :
    0 ≤ sInf (quotientSet d) := by
  obtain ⟨f⟩ := hadmissible
  exact le_csInf ⟨quotient f, f, rfl⟩ (by rintro _ ⟨g, rfl⟩; exact (quotient_pos g).le)

/-- The geometric factor `(v_d/2^d)^{1/d} √d` of the Cohn–Elkies bound. -/
def packingGeometricRoot (d : ℕ) : ℝ := (unitBallVolume d / 2 ^ d) ^ (d : ℝ)⁻¹ * √d

/-- `LP_d^{1/d}` splits as the geometric factor times the normalized program. -/
theorem linearProgram_root_eq_geometric_mul_normalizedProgram
    {d : ℕ} (hd : 0 < d) (hadmissible : Nonempty (Admissible d)) :
    (LP d) ^ ((d : ℝ)⁻¹) = packingGeometricRoot d * normalizedProgram d := by
  have hsqrt : √(d : ℝ) ≠ 0 := (sqrt_pos.2 (by exact_mod_cast hd)).ne'
  rw [normalizedProgram_eq_quotientInf_root d hadmissible]
  change (unitBallVolume d / 2 ^ d * sInf (quotientSet d)) ^ ((d : ℝ)⁻¹) = _
  unfold packingGeometricRoot quotientRootMap
  rw [mul_rpow (geometricFactor_pos d).le (quotientInf_nonneg d hadmissible)]
  field_simp

end

noncomputable section

open Filter Real
open scoped Nat Topology

/-- The volume of the odd-dimensional unit ball: `v_{2k+1} = π^k 2^{2k+1} k! / (2k+1)!`. -/
theorem unitBallVolume_odd (k : ℕ) :
    unitBallVolume (2 * k + 1) = π ^ k * 2 ^ (2 * k + 1) * k ! / (2 * k + 1)! := by
  have hhalf : ((2 * k + 1 : ℕ) : ℝ) / 2 = k + 1 / 2 := by push_cast; ring
  have hfac : ((2 * k + 1)‼ : ℝ) * 2 ^ k * k ! = ((2 * k + 1)! : ℝ) := by
    have h : (2 * k + 1)‼ * 2 ^ k * k ! = (2 * k + 1)! := by
      rw [mul_assoc, ← Nat.doubleFactorial_two_mul, ← Nat.factorial_eq_mul_doubleFactorial]
    exact_mod_cast h
  have hd : ((2 * k + 1)‼ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.doubleFactorial_pos _).ne'
  have hk : (k ! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  have hs : √π ≠ 0 := by positivity
  rw [unitBallVolume, hhalf, rpow_add pi_pos, rpow_natCast, ← sqrt_eq_rpow,
    show (k : ℝ) + 1 / 2 + 1 = k + 1 + 1 / 2 by ring, Gamma_nat_add_one_add_half, ← hfac]
  field_simp
  ring

/-- The normalized log-volume `log (v_d)/d + (log d)/2` (the logarithm of `v_d^{1/d} √d`). -/
def normalizedVolumeLog (d : ℕ) : ℝ := log (unitBallVolume d) / d + log d / 2

theorem tendsto_normalizedVolumeLog_even :
    Tendsto (fun k : ℕ ↦ normalizedVolumeLog (2 * k)) atTop (𝓝 ((log (2 * π) + 1) / 2)) := by
  have key := (tendsto_const_nhds (x := log (2 * π) / 2)).sub
    (Stirling.tendsto_log_factorial_div_sub_log.const_mul (1 / 2 : ℝ))
  rw [show log (2 * π) / 2 - 1 / 2 * (-1 : ℝ) = (log (2 * π) + 1) / 2 by ring] at key
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hk1 : (k ! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  rw [normalizedVolumeLog, unitBallVolume_even]
  push_cast
  rw [log_div (by positivity) hk1, log_pow, log_mul two_ne_zero hk0,
    log_mul two_ne_zero pi_ne_zero]
  field_simp
  ring

theorem tendsto_normalizedVolumeLog_odd :
    Tendsto (fun k : ℕ ↦ normalizedVolumeLog (2 * k + 1)) atTop (𝓝 ((log (2 * π) + 1) / 2)) := by
  have hq := Stirling.tendsto_self_div_two_mul_self_add_one
  have hS := Stirling.tendsto_log_factorial_div_sub_log
  have hodd : Tendsto (fun k : ℕ ↦ log ((2 * k + 1)! : ℝ) / (2 * (k : ℝ) + 1)
      - log (2 * (k : ℝ) + 1)) atTop (𝓝 (-1)) := by
    have hdim : Tendsto (fun k : ℕ ↦ 2 * k + 1) atTop atTop :=
      tendsto_atTop_mono (fun k ↦ by change k ≤ 2 * k + 1; omega) tendsto_id
    simpa [Function.comp_def] using hS.comp hdim
  have hcorr : Tendsto (fun k : ℕ ↦ ((k : ℝ) / (2 * k + 1) - 1 / 2) * log k) atTop (𝓝 0) := by
    have h := (Real.tendsto_log_natCast_div_natCast.mul hq).const_mul (-1 / 2 : ℝ)
    simp only [zero_mul, mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with k hk
    have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
    field_simp
    ring
  have hratio : Tendsto (fun k : ℕ ↦ log k - log (2 * (k : ℝ) + 1)) atTop (𝓝 (log (1 / 2))) := by
    refine (hq.log (by norm_num)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with k hk
    exact log_div (Nat.cast_ne_zero.2 hk.ne') (by positivity)
  have key := (((((hq.mul_const (log π)).add (tendsto_const_nhds (x := log 2))).add
    (hq.mul hS)).sub hodd).add hcorr).add (hratio.const_mul (1 / 2 : ℝ))
  rw [show (1 / 2 * log π + log 2 + 1 / 2 * (-1) - -1 + 0 + 1 / 2 * log (1 / 2) : ℝ)
      = (log (2 * π) + 1) / 2 by
    rw [log_mul two_ne_zero pi_ne_zero, log_div one_ne_zero two_ne_zero, log_one]; ring] at key
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hk1 : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast k.factorial_pos
  have hk2 : (0 : ℝ) < ((2 * k + 1)! : ℝ) := by exact_mod_cast (2 * k + 1).factorial_pos
  have hp : (0 : ℝ) < π ^ k * 2 ^ (2 * k + 1) := by positivity
  have hlog : log (unitBallVolume (2 * k + 1))
      = k * log π + (2 * k + 1) * log 2 + log (k ! : ℝ) - log ((2 * k + 1)! : ℝ) := by
    rw [unitBallVolume_odd, log_div (mul_ne_zero hp.ne' hk1.ne') hk2.ne', log_mul hp.ne' hk1.ne',
      log_mul (by positivity) (by positivity), log_pow, log_pow]
    push_cast
    ring
  rw [normalizedVolumeLog, hlog]
  push_cast
  have hodd0 : 2 * (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem tendsto_normalizedVolumeLog :
    Tendsto normalizedVolumeLog atTop (𝓝 ((log (2 * π) + 1) / 2)) :=
  Filter.tendsto_of_even_odd tendsto_normalizedVolumeLog_even tendsto_normalizedVolumeLog_odd

theorem exp_normalizedVolumeLog_limit :
    exp ((log (2 * π) + 1) / 2) = √(2 * π * exp 1) := by
  rw [exp_half, exp_add, exp_log (by positivity)]

theorem packingGeometricRoot_eq_exp {d : ℕ} (hd : 0 < d) :
    packingGeometricRoot d = exp (normalizedVolumeLog d) / 2 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hv : (0 : ℝ) < unitBallVolume d ^ (d : ℝ)⁻¹ := rpow_pos_of_pos (unitBallVolume_pos d) _
  have hs : (0 : ℝ) < √(d : ℝ) := sqrt_pos.2 hd'
  have h : normalizedVolumeLog d = log (unitBallVolume d ^ (d : ℝ)⁻¹ * √d) := by
    rw [log_mul hv.ne' hs.ne', log_rpow (unitBallVolume_pos d), log_sqrt hd'.le,
      normalizedVolumeLog]
    ring
  rw [h, exp_log (mul_pos hv hs), packingGeometricRoot,
    div_rpow (unitBallVolume_pos d).le (by positivity),
    pow_rpow_inv_natCast (by norm_num) hd.ne']
  ring

/-- Stirling's formula for the geometric factor: `(v_d/2^d)^{1/d} √d → √(2πe)/2` (report (28)). -/
theorem tendsto_packingGeometricRoot :
    Tendsto packingGeometricRoot atTop (𝓝 (√(2 * π * exp 1) / 2)) := by
  rw [← exp_normalizedVolumeLog_limit]
  refine (((continuous_exp.tendsto _).comp tendsto_normalizedVolumeLog).div_const 2).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with d hd
  exact (packingGeometricRoot_eq_exp hd).symm

end

end CohnElkies
