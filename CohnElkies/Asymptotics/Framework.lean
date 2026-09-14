import CohnElkies.Basic

/-!
# The sandwich framework for Theorem 1.1 (report §1, §3–4)

Theorem 1.1 from its two halves: a uniform lower bound on the normalized cost of every admissible
function below the critical radius `1/π` (`UniformAdmissibleLowerBound`) and a primal construction
above it (`ConstructivePrimalUpperBound`, in practice an ordered `ε`-construction
`OrderedEpsilonUpperConstruction`) force `normalizedProgram d → 1/π`.
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter
open scoped Topology

/-- Dual half of Theorem 1.1: below the critical radius `1/π`, *every* admissible function of
every large enough dimension has normalized cost at least `c`. -/
def UniformAdmissibleLowerBound : Prop := ∀ c : ℝ, c < criticalRadius → ∀ᶠ d : ℕ in atTop,
      ∀ f : Admissible d, c ≤ normalizedCost f

/-- Primal half of Theorem 1.1: above the critical radius `1/π`, every large enough dimension
carries an admissible function of normalized cost at most `c`. -/
def ConstructivePrimalUpperBound : Prop := ∀ c : ℝ, criticalRadius < c → ∀ᶠ d : ℕ in atTop,
      ∃ f : Admissible d, normalizedCost f ≤ c

/-- Theorem 1.1 of the report from its two halves: a uniform lower bound on all admissible
functions together with a primal construction forces `normalizedProgram d → 1/π`. -/
theorem sharpQuotient_of_uniform_lower_and_constructive_upper (hlower : UniformAdmissibleLowerBound)
    (hupper : ConstructivePrimalUpperBound) : SharpQuotientAsymptotic := by
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · filter_upwards [hlower _ (show (a + criticalRadius) / 2 < criticalRadius by linarith),
      hupper (criticalRadius + 1) (by linarith)] with d hcost ⟨f, _⟩
    have : (a + criticalRadius) / 2 ≤ normalizedProgram d :=
      le_csInf ⟨normalizedCost f, f, rfl⟩ (by rintro _ ⟨g, rfl⟩; exact hcost g)
    linarith
  · filter_upwards [hupper _ (show criticalRadius < (criticalRadius + b) / 2 by linarith)]
      with d ⟨f, hf⟩
    have : normalizedProgram d ≤ normalizedCost f :=
      csInf_le (normalizedCostSet_bddBelow d) ⟨f, rfl⟩
    linarith

/-- A family of admissible functions indexed by a regularization parameter `ε`, whose normalized
radii converge dimensionwise to a limit that tends to the critical radius as `ε → 0⁺`. -/
structure OrderedEpsilonUpperConstruction where
  epsilonBound : ℝ
  epsilonBound_pos : 0 < epsilonBound
  normalizedRadius : ℝ → ℕ → ℝ
  limitingRadius : ℝ → ℝ
  limitingRadius_tendsto : Tendsto limitingRadius (𝓝[>] (0 : ℝ)) (𝓝 criticalRadius)
  normalizedRadius_tendsto : ∀ ε : ℝ, 0 < ε → ε < epsilonBound →
      Tendsto (normalizedRadius ε) atTop (𝓝 (limitingRadius ε))
  admissibleWitness : ∀ ε : ℝ, 0 < ε → ε < epsilonBound → ∀ᶠ d : ℕ in atTop,
        ∃ f : Admissible d, normalizedCost f ≤ normalizedRadius ε d

/-- Theorem 1.1 of the report: a uniform lower bound plus an ordered `ε`-construction give the
sharp asymptotics of the normalized program. -/
theorem sharpQuotient_of_uniform_lower_and_ordered_upper (hlower : UniformAdmissibleLowerBound)
    (construction : OrderedEpsilonUpperConstruction) : SharpQuotientAsymptotic := by
  refine sharpQuotient_of_uniform_lower_and_constructive_upper hlower fun c hc ↦ ?_
  have hpositive : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, hεclose, hεpositive, hεsmall⟩ :=
    (((tendsto_order.1 construction.limitingRadius_tendsto).2 c hc).and (hpositive.and
      ((tendsto_id.mono_left nhdsWithin_le_nhds).eventually
        (gt_mem_nhds construction.epsilonBound_pos)))).exists
  filter_upwards [construction.admissibleWitness ε hεpositive hεsmall,
    (tendsto_order.1 (construction.normalizedRadius_tendsto ε hεpositive hεsmall)).2 c hεclose]
    with d ⟨f, hf⟩ hr
  exact ⟨f, hf.trans hr.le⟩

end

end CohnElkies
