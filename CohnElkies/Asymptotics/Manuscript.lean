import CohnElkies.Asymptotics.Main

/-!
# Theorem 1.1 in the notation of the manuscript

The forms of Theorem 1.1 stated in Chapter 1 of the report: the infimum of the quotient roots
divided by `√d` tends to `1/π`, with vanishing error terms `LP_d = (√(e/(2π)) + o(1))^d`,
`LP_d = 2^{-(½ log₂(2π/e) + o(1)) d}`, and a universal nonnegative `δ_d → 0` with
`(2^d/v_d) (√(e/(2π)) - δ_d)^d ≤ f(0)/𝓕f(0)` for every admissible `f`.
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter Real
open scoped Topology

/-- The manuscript's set of normalized roots `{(f(0)/𝓕f(0))^{1/d} : f ∈ 𝒜_d}`. -/
def manuscriptQuotientRootSet (d : ℕ) : Set ℝ :=
  Set.range fun f : Admissible d ↦ quotient f ^ ((d : ℝ)⁻¹)

theorem manuscriptQuotientRootInf_div_sqrt_eq (d : ℕ) :
    sInf (manuscriptQuotientRootSet d) / √(d : ℝ) = normalizedProgram d := by
  obtain ⟨f⟩ := admissible_nonempty d
  have hmono : MonotoneOn (fun x : ℝ ↦ x ^ (d : ℝ)⁻¹) (quotientSet d) := by
    rintro x ⟨g, rfl⟩ y - hxy
    exact rpow_le_rpow (quotient_pos g).le hxy (by positivity)
  have himage : manuscriptQuotientRootSet d = (fun x : ℝ ↦ x ^ (d : ℝ)⁻¹) '' quotientSet d := by
    ext y
    constructor
    · rintro ⟨g, rfl⟩; exact ⟨quotient g, ⟨g, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩; exact ⟨g, rfl⟩
  have hinf : sInf (manuscriptQuotientRootSet d) = sInf (quotientSet d) ^ (d : ℝ)⁻¹ := by
    rw [himage]
    exact (MonotoneOn.map_csInf_of_continuousWithinAt
      (continuous_rpow_const (by positivity)).continuousWithinAt hmono ⟨quotient f, f, rfl⟩
      (quotientSet_bddBelow d)).symm
  rw [hinf, normalizedProgram_eq_quotientInf_root_unconditional]
  rfl

/-- Manuscript form of Theorem 1.1: `inf {(f(0)/𝓕f(0))^{1/d} : f ∈ 𝒜_d} / √d → 1/π`. -/
theorem manuscriptQuotientRootInf_div_sqrt_tendsto (hquotient : SharpQuotientAsymptotic) :
    Tendsto (fun d : ℕ ↦ sInf (manuscriptQuotientRootSet d) / √(d : ℝ)) atTop (𝓝 π⁻¹) :=
  hquotient.congr fun d ↦ (manuscriptQuotientRootInf_div_sqrt_eq d).symm

/-- The manuscript's deficit `max 0 (√(e/(2π)) - LP_d^{1/d})`, a nonnegative `o(1)` error. -/
def manuscriptPackingDeficit (d : ℕ) : ℝ :=
  max 0 (criticalPackingBase - (LP d) ^ ((d : ℝ)⁻¹))

theorem manuscriptPackingDeficit_isLittleO :
    Asymptotics.IsLittleO atTop manuscriptPackingDeficit (fun _ : ℕ ↦ (1 : ℝ)) := by
  refine (Asymptotics.isLittleO_one_iff ℝ).2 ?_
  have hsub : Tendsto (fun d : ℕ ↦ criticalPackingBase - (LP d) ^ ((d : ℝ)⁻¹)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := criticalPackingBase)).sub sharpPackingRootAsymptotic
  change Tendsto (fun d : ℕ ↦ max 0 (criticalPackingBase - (LP d) ^ ((d : ℝ)⁻¹))) atTop (𝓝 0)
  simpa using (tendsto_const_nhds (x := (0 : ℝ))).max hsub

theorem manuscriptPackingDeficit_le (d : ℕ) :
    manuscriptPackingDeficit d ≤ criticalPackingBase := by
  rw [manuscriptPackingDeficit]
  refine max_le criticalPackingBase_pos.le ?_
  have : 0 ≤ (LP d) ^ ((d : ℝ)⁻¹) := rpow_nonneg (linearProgram_nonneg d) _
  linarith

/-- Manuscript Corollary: a universal lower bound on every quotient, with an `o(1)` deficit. -/
theorem manuscriptUniversalQuotientBound {d : ℕ} (hd : 0 < d) (f : Admissible d) :
    (2 : ℝ) ^ d / unitBallVolume d * (criticalPackingBase - manuscriptPackingDeficit d) ^ d ≤
      quotient f := by
  have hv : unitBallVolume d ≠ 0 := (unitBallVolume_pos d).ne'
  have hbase : 0 ≤ criticalPackingBase - manuscriptPackingDeficit d :=
    sub_nonneg.2 (manuscriptPackingDeficit_le d)
  have hroot : criticalPackingBase - manuscriptPackingDeficit d ≤ (LP d) ^ ((d : ℝ)⁻¹) := by
    have h : criticalPackingBase - (LP d) ^ ((d : ℝ)⁻¹) ≤ manuscriptPackingDeficit d :=
      le_max_right _ _
    linarith
  have hpow : (criticalPackingBase - manuscriptPackingDeficit d) ^ d ≤ LP d := by
    have h := pow_le_pow_left₀ hbase hroot d
    rwa [rpow_inv_natCast_pow (linearProgram_nonneg d) hd.ne'] at h
  have hLP : LP d ≤ unitBallVolume d / 2 ^ d * quotient f :=
    mul_le_mul_of_nonneg_left (csInf_le (quotientSet_bddBelow d) ⟨f, rfl⟩)
      (geometricFactor_pos d).le
  calc (2 : ℝ) ^ d / unitBallVolume d * (criticalPackingBase - manuscriptPackingDeficit d) ^ d
      ≤ (2 : ℝ) ^ d / unitBallVolume d * (unitBallVolume d / 2 ^ d * quotient f) :=
        mul_le_mul_of_nonneg_left (hpow.trans hLP)
          (div_pos (by positivity) (unitBallVolume_pos d)).le
    _ = quotient f := by field_simp

theorem exists_manuscriptUniversalPackingIsLittleO : ∃ δ : ℕ → ℝ,
    Asymptotics.IsLittleO atTop δ (fun _ : ℕ ↦ (1 : ℝ)) ∧ (∀ d : ℕ, 0 ≤ δ d) ∧
      (∀ d : ℕ, 0 < d → ∀ f : Admissible d, (2 : ℝ) ^ d / unitBallVolume d *
        (criticalPackingBase - δ d) ^ d ≤ quotient f) :=
  ⟨manuscriptPackingDeficit, manuscriptPackingDeficit_isLittleO, fun _ ↦ le_max_left _ _,
    fun _ hd f ↦ manuscriptUniversalQuotientBound hd f⟩

/-- The manuscript's error term `LP_d^{1/d} - √(e/(2π))`. -/
def manuscriptPackingRootError (d : ℕ) : ℝ := (LP d) ^ ((d : ℝ)⁻¹) - criticalPackingBase

theorem manuscriptPackingRootError_isLittleO :
    Asymptotics.IsLittleO atTop manuscriptPackingRootError (fun _ : ℕ ↦ (1 : ℝ)) := by
  refine (Asymptotics.isLittleO_one_iff ℝ).2 ?_
  change Tendsto (fun d : ℕ ↦ (LP d) ^ ((d : ℝ)⁻¹) - criticalPackingBase) atTop (𝓝 0)
  simpa using sharpPackingRootAsymptotic.sub (tendsto_const_nhds (x := criticalPackingBase))

/-- Manuscript form of Theorem 1.1: `LP_d = (√(e/(2π)) + o(1))^d`. -/
theorem exists_manuscriptPackingIsLittleO : ∃ e : ℕ → ℝ,
    Asymptotics.IsLittleO atTop e (fun _ : ℕ ↦ (1 : ℝ)) ∧
      ∀ d : ℕ, 0 < d → LP d = (criticalPackingBase + e d) ^ d := by
  refine ⟨manuscriptPackingRootError, manuscriptPackingRootError_isLittleO, fun d hd ↦ ?_⟩
  rw [show criticalPackingBase + manuscriptPackingRootError d = (LP d) ^ ((d : ℝ)⁻¹) from by
      rw [manuscriptPackingRootError]; ring,
    rpow_inv_natCast_pow (linearProgram_nonneg d) hd.ne']

/-- The manuscript's error term `-(log₂ LP_d)/d - (1/2) log₂ (2π/e)`. -/
def manuscriptBinaryExponentError (d : ℕ) : ℝ :=
  -(logb 2 (LP d) / (d : ℝ)) - criticalBinaryExponent

theorem manuscriptBinaryExponentError_isLittleO :
    Asymptotics.IsLittleO atTop manuscriptBinaryExponentError (fun _ : ℕ ↦ (1 : ℝ)) := by
  refine (Asymptotics.isLittleO_one_iff ℝ).2 ?_
  change Tendsto (fun d : ℕ ↦ -(logb 2 (LP d) / (d : ℝ)) - criticalBinaryExponent) atTop (𝓝 0)
  simpa using sharpBinaryLogAsymptotic.neg.sub (tendsto_const_nhds (x := criticalBinaryExponent))

/-- Manuscript form of Theorem 1.1: `LP_d = 2^{-((1/2) log₂ (2π/e) + o(1)) d}`. -/
theorem exists_manuscriptBinaryIsLittleO : ∃ e : ℕ → ℝ,
    Asymptotics.IsLittleO atTop e (fun _ : ℕ ↦ (1 : ℝ)) ∧
      ∀ᶠ d : ℕ in atTop, LP d = (2 : ℝ) ^ (-(criticalBinaryExponent + e d) * (d : ℝ)) := by
  refine ⟨manuscriptBinaryExponentError, manuscriptBinaryExponentError_isLittleO, ?_⟩
  filter_upwards [eventually_gt_atTop 0,
    eventually_linearProgram_pos_of_sharpQuotient sharpQuotientAsymptotic] with d hd hpositive
  have hdreal : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  rw [show -(criticalBinaryExponent + manuscriptBinaryExponentError d) * (d : ℝ)
      = logb 2 (LP d) from by rw [manuscriptBinaryExponentError]; field_simp; ring,
    rpow_logb (by norm_num) (by norm_num) hpositive]

/-- The manuscript's error term `normalizedProgram d - 1/π`. -/
def manuscriptQuotientRootError (d : ℕ) : ℝ := normalizedProgram d - criticalRadius

theorem manuscriptQuotientRootError_isLittleO :
    Asymptotics.IsLittleO atTop manuscriptQuotientRootError (fun _ : ℕ ↦ (1 : ℝ)) := by
  refine (Asymptotics.isLittleO_one_iff ℝ).2 ?_
  change Tendsto (fun d : ℕ ↦ normalizedProgram d - criticalRadius) atTop (𝓝 0)
  simpa using sharpQuotientAsymptotic.sub (tendsto_const_nhds (x := criticalRadius))

/-- Manuscript form of Theorem 1.1: `inf {(f(0)/𝓕f(0))^{1/d}} = (1/π + o(1)) √d`. -/
theorem exists_manuscriptQuotientRootIsLittleO : ∃ e : ℕ → ℝ,
    Asymptotics.IsLittleO atTop e (fun _ : ℕ ↦ (1 : ℝ)) ∧
      ∀ d : ℕ, 0 < d → sInf (manuscriptQuotientRootSet d) = (π⁻¹ + e d) * √(d : ℝ) := by
  refine ⟨manuscriptQuotientRootError, manuscriptQuotientRootError_isLittleO, fun d hd ↦ ?_⟩
  have hsqrt : √(d : ℝ) ≠ 0 := by positivity
  rw [show π⁻¹ + manuscriptQuotientRootError d = normalizedProgram d from by
      rw [manuscriptQuotientRootError, criticalRadius]; ring,
    ← manuscriptQuotientRootInf_div_sqrt_eq d]
  field_simp

end

end CohnElkies
