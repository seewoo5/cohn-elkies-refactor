import Mathlib

/-!
# Haar measures on compact groups are right invariant

Compact groups are unimodular: a Haar measure on a compact group is right invariant
(`MeasureTheory.Measure.IsHaarMeasure.isMulRightInvariant_of_compactSpace`). Right translation by
`g` is left translation by `g` followed by conjugation by `g⁻¹`, a continuous surjective group
homomorphism of the compact group, which preserves every Haar measure by
`MonoidHom.measurePreserving`.
-/

namespace MeasureTheory.Measure

/-- A Haar measure on a compact group is right invariant (compact groups are unimodular). -/
@[to_additive
/-- An additive Haar measure on a compact additive group is right invariant. -/]
instance (priority := 100) IsHaarMeasure.isMulRightInvariant_of_compactSpace
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsHaarMeasure μ] :
    IsMulRightInvariant μ := by
  constructor
  intro g
  have hconj : MeasurePreserving (MulAut.conj g⁻¹ : G →* G) μ μ :=
    MonoidHom.measurePreserving (show Continuous fun x : G ↦ g⁻¹ * x * g⁻¹⁻¹ by fun_prop)
      (MulAut.conj g⁻¹).surjective rfl
  calc map (· * g) μ = map ((MulAut.conj g⁻¹ : G →* G) ∘ (g * ·)) μ := by
        congr 1
        funext x
        simp
    _ = μ := by
        rw [← map_map hconj.measurable (measurable_const_mul g), map_mul_left_eq_self μ g,
          hconj.map_eq]

end MeasureTheory.Measure
