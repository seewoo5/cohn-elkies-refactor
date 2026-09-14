import CohnElkies.Asymptotics.Manuscript

/-!
# The conclusions of Chapter 1 of the report, in the notation of the manuscript

`PackingBounds.SharpFullCohnElkiesManuscriptConclusions` bundles Theorem 1.1 and its corollaries
for the Cohn–Elkies program `LP_d` of equation (3) (`PackingBounds.fullLinearProgram`, over all
of `𝒜_d`) exactly as stated in the manuscript, including Theorem 3.8 for every `f ∈ 𝒜_d`;
`PackingBounds.sharpFullCohnElkiesManuscriptConclusions` proves them.
-/

open scoped Real
open Complex (I)

noncomputable section

open Filter
open scoped Topology

namespace PackingBounds

theorem manuscriptQuotientRootSet_eq_literal (d : ℕ) : CohnElkies.manuscriptQuotientRootSet d =
    {q : ℝ | ∃ f : FullAdmissible d, fullQuotient f ^ ((d : ℝ)⁻¹) = q} :=
  rfl

/-- The conclusions of Chapter 1 of the report for the Cohn–Elkies program `LP_d`, in the
notation of the manuscript. -/
structure SharpFullCohnElkiesManuscriptConclusions : Prop where
  root_before_infimum : Tendsto (fun d : ℕ ↦
        sInf {q : ℝ | ∃ f : FullAdmissible d, fullQuotient f ^ ((d : ℝ)⁻¹) = q} / √(d : ℝ))
      atTop (𝓝 (1 / π))
  root_before_infimum_vanishing_error : ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧ ∀ d : ℕ, 0 < d →
        sInf {q : ℝ | ∃ f : FullAdmissible d, fullQuotient f ^ ((d : ℝ)⁻¹) = q} =
          (1 / π + err d) * √(d : ℝ)
  linear_program_root : Tendsto (fun d : ℕ ↦ (fullLinearProgram d) ^ ((d : ℝ)⁻¹))
      atTop (𝓝 (√(Real.exp 1 / (2 * π))))
  natural_logarithmic_rate : Tendsto (fun d : ℕ ↦ Real.log (fullLinearProgram d) / (d : ℝ)) atTop
      (𝓝 ((1 / 2 : ℝ) * Real.log (Real.exp 1 / (2 * π))))
  natural_vanishing_exponential_error : ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧ (∀ᶠ d : ℕ in atTop,
        fullLinearProgram d = (√(Real.exp 1 / (2 * π)) + err d) ^ d)
  universal_nonnegative_delta : ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧ (∀ d : ℕ, 0 ≤ δ d) ∧
      (∀ᶠ d : ℕ in atTop, ∀ f : FullAdmissible d, (2 : ℝ) ^ d / CohnElkies.unitBallVolume d *
          (√(Real.exp 1 / (2 * π)) - δ d) ^ d ≤ fullQuotient f)
  base_two_exponent_positive : 0 < (1 / 2 : ℝ) * Real.logb 2 (2 * π / Real.exp 1)
  base_two_logarithmic_rate : Tendsto (fun d : ℕ ↦ Real.logb 2 (fullLinearProgram d) / (d : ℝ))
      atTop
      (𝓝 (-((1 / 2 : ℝ) * Real.logb 2 (2 * π / Real.exp 1))))
  base_two_vanishing_exponential_error : ∃ err : ℕ → ℝ, Tendsto err atTop (𝓝 0) ∧
      (∀ᶠ d : ℕ in atTop, fullLinearProgram d = (2 : ℝ) ^ (-((1 / 2 : ℝ) *
                Real.logb 2 (2 * π / Real.exp 1) + err d) *
              (d : ℝ)))

/-- Chapter 1 of the report holds for the Cohn–Elkies program `LP_d` (Theorem 1.1 in all its
forms, Theorem 3.8 for every `f ∈ 𝒜_d`). -/
theorem sharpFullCohnElkiesManuscriptConclusions : SharpFullCohnElkiesManuscriptConclusions where
  root_before_infimum := by
    simp_rw [← manuscriptQuotientRootSet_eq_literal]
    simpa [one_div] using
      CohnElkies.manuscriptQuotientRootInf_div_sqrt_tendsto CohnElkies.sharpQuotientAsymptotic
  root_before_infimum_vanishing_error := by
    obtain ⟨err, herr, hformula⟩ := CohnElkies.exists_manuscriptQuotientRootIsLittleO
    refine ⟨err, (Asymptotics.isLittleO_one_iff ℝ).mp herr, fun d hd ↦ ?_⟩
    rw [← manuscriptQuotientRootSet_eq_literal]
    simpa [one_div] using hformula d hd
  linear_program_root := by
    simpa [CohnElkies.SharpPackingRootAsymptotic, CohnElkies.criticalPackingBase] using
      CohnElkies.sharpPackingRootAsymptotic
  natural_logarithmic_rate := by
    simpa [CohnElkies.SharpLogAsymptotic] using CohnElkies.sharpLogAsymptotic
  natural_vanishing_exponential_error := by
    obtain ⟨err, herr, hformula⟩ := CohnElkies.exists_manuscriptPackingIsLittleO
    refine ⟨err, (Asymptotics.isLittleO_one_iff ℝ).mp herr, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd
    simpa [CohnElkies.criticalPackingBase] using hformula d hd
  universal_nonnegative_delta := by
    obtain ⟨δ, hδ, hnonneg, hbound⟩ := CohnElkies.exists_manuscriptUniversalPackingIsLittleO
    refine ⟨δ, (Asymptotics.isLittleO_one_iff ℝ).mp hδ, hnonneg, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with d hd f
    simpa [CohnElkies.criticalPackingBase] using hbound d hd f
  base_two_exponent_positive := by
    simpa [CohnElkies.criticalBinaryExponent] using CohnElkies.criticalBinaryExponent_pos
  base_two_logarithmic_rate := by
    simpa [CohnElkies.SharpBinaryLogAsymptotic, CohnElkies.criticalBinaryExponent] using
      CohnElkies.sharpBinaryLogAsymptotic
  base_two_vanishing_exponential_error := by
    obtain ⟨err, herr, hformula⟩ := CohnElkies.exists_manuscriptBinaryIsLittleO
    exact ⟨err, (Asymptotics.isLittleO_one_iff ℝ).mp herr,
      by simpa [CohnElkies.criticalBinaryExponent] using hformula⟩

end PackingBounds

end
