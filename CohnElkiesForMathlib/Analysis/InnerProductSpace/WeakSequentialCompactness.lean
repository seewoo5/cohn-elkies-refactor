import Mathlib

/-!
# Weak sequential compactness of bounded sets in a separable Hilbert space

Let `E` be a separable Hilbert space over `𝕜 = ℝ` or `ℂ`. We show that closed balls of `E` are
sequentially compact for the weak topology `WeakSpace 𝕜 E`, i.e. that every bounded sequence in
`E` has a weakly convergent subsequence. This is the sequential Banach–Alaoglu theorem
`WeakDual.isSeqCompact_closedBall` for the dual of `E`, transported to `E` along the
Fréchet–Riesz isometry `InnerProductSpace.toDual`.

## Main results

* `tendsto_toWeakSpace_iff_forall_tendsto`: in a topological vector space whose continuous linear
  functionals separate points, convergence in the weak topology is convergence against every
  continuous linear functional.
* `InnerProductSpace.tendsto_toWeakSpace_iff_forall_tendsto_inner_right` (and `..._inner_left`):
  in a Hilbert space, `u a` converges weakly to `y` if and only if `⟪z, u a⟫ → ⟪z, y⟫` for every
  `z` (equivalently, `⟪u a, z⟫ → ⟪y, z⟫` for every `z`).
* `InnerProductSpace.isSeqCompact_toWeakSpace_image_closedBall`: closed balls of a separable
  Hilbert space are weakly sequentially compact.
* `InnerProductSpace.tendsto_subseq_toWeakSpace_of_norm_le`,
  `InnerProductSpace.tendsto_subseq_inner_left_of_norm_le`,
  `InnerProductSpace.tendsto_subseq_inner_right_of_norm_le`: every sequence `x` in a separable
  Hilbert space with `‖x n‖ ≤ C` has a subsequence `x ∘ φ` converging weakly to some `y` with
  `‖y‖ ≤ C`.
-/

open Filter Topology TopologicalSpace
open scoped InnerProductSpace

section SeparatingDual

variable {α 𝕜 E : Type*} [CommRing 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [SeparatingDual 𝕜 E]

variable (𝕜 E) in
/-- If the continuous linear functionals on `E` separate points, then the pairing
`x ↦ (f ↦ f x)` of `E` with its dual is injective. -/
theorem topDualPairing_flip_injective : Function.Injective (topDualPairing 𝕜 E).flip :=
  fun _ _ h ↦ (SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜)).mpr (LinearMap.congr_fun h)

/-- If the continuous linear functionals on `E` separate points, then a function converges in the
weak topology `WeakSpace 𝕜 E` if and only if its composition with every continuous linear
functional converges. -/
theorem tendsto_toWeakSpace_iff_forall_tendsto {l : Filter α} {u : α → E} {y : E} :
    Tendsto (fun a ↦ toWeakSpace 𝕜 E (u a)) l (𝓝 (toWeakSpace 𝕜 E y)) ↔
      ∀ f : StrongDual 𝕜 E, Tendsto (fun a ↦ f (u a)) l (𝓝 (f y)) :=
  WeakBilin.tendsto_iff_forall_eval_tendsto _ (topDualPairing_flip_injective 𝕜 E)

end SeparatingDual

variable {α 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- `⟪u a, z⟫` converges to `⟪y, z⟫` if and only if `⟪z, u a⟫` converges to `⟪z, y⟫`. -/
theorem tendsto_inner_left_iff_tendsto_inner_right {l : Filter α} {u : α → E} {y z : E} :
    Tendsto (fun a ↦ ⟪u a, z⟫_𝕜) l (𝓝 ⟪y, z⟫_𝕜) ↔ Tendsto (fun a ↦ ⟪z, u a⟫_𝕜) l (𝓝 ⟪z, y⟫_𝕜) := by
  constructor <;> intro h <;>
    simpa only [Function.comp_def, inner_conj_symm] using (RCLike.continuous_conj.tendsto _).comp h

namespace InnerProductSpace

variable [CompleteSpace E]

/-- In a Hilbert space, `u a` converges weakly to `y` if and only if `⟪z, u a⟫` converges to
`⟪z, y⟫` for every `z`. -/
theorem tendsto_toWeakSpace_iff_forall_tendsto_inner_right {l : Filter α} {u : α → E} {y : E} :
    Tendsto (fun a ↦ toWeakSpace 𝕜 E (u a)) l (𝓝 (toWeakSpace 𝕜 E y)) ↔
      ∀ z : E, Tendsto (fun a ↦ ⟪z, u a⟫_𝕜) l (𝓝 ⟪z, y⟫_𝕜) :=
  tendsto_toWeakSpace_iff_forall_tendsto.trans <|
    Iff.symm <| Equiv.forall_congr (toDual 𝕜 E) fun _ ↦ Iff.rfl

/-- In a Hilbert space, `u a` converges weakly to `y` if and only if `⟪u a, z⟫` converges to
`⟪y, z⟫` for every `z`. -/
theorem tendsto_toWeakSpace_iff_forall_tendsto_inner_left {l : Filter α} {u : α → E} {y : E} :
    Tendsto (fun a ↦ toWeakSpace 𝕜 E (u a)) l (𝓝 (toWeakSpace 𝕜 E y)) ↔
      ∀ z : E, Tendsto (fun a ↦ ⟪u a, z⟫_𝕜) l (𝓝 ⟪y, z⟫_𝕜) :=
  tendsto_toWeakSpace_iff_forall_tendsto_inner_right.trans <|
    forall_congr' fun _ ↦ tendsto_inner_left_iff_tendsto_inner_right.symm

variable (𝕜) [SeparableSpace E]

/-- **Weak sequential compactness of closed balls**: closed balls of a separable Hilbert space are
sequentially compact for the weak topology. -/
theorem isSeqCompact_toWeakSpace_image_closedBall (x₀ : E) (r : ℝ) :
    IsSeqCompact (toWeakSpace 𝕜 E '' Metric.closedBall x₀ r) := by
  intro x hx
  choose x' hx' hxx' using hx
  obtain rfl : x = fun n ↦ toWeakSpace 𝕜 E (x' n) := funext fun n ↦ (hxx' n).symm
  -- By the Fréchet–Riesz theorem, the functionals `⟪x' n, ·⟫` lie in a closed ball of the dual,
  -- which is weak-* sequentially compact by the sequential Banach–Alaoglu theorem.
  have hmem : ∀ n, StrongDual.toWeakDual (toDual 𝕜 E (x' n)) ∈
      WeakDual.toStrongDual ⁻¹' Metric.closedBall (toDual 𝕜 E x₀) r := fun n ↦ by
    simpa using hx' n
  obtain ⟨ℓ, hℓ, φ, hφ, hlim⟩ := WeakDual.isSeqCompact_closedBall 𝕜 E (toDual 𝕜 E x₀) r hmem
  refine ⟨_, ⟨(toDual 𝕜 E).symm (WeakDual.toStrongDual ℓ), ?_, rfl⟩, φ, hφ, ?_⟩
  · rw [Metric.mem_closedBall, ← (toDual 𝕜 E).dist_map, LinearIsometryEquiv.apply_symm_apply]
    exact hℓ
  · refine (tendsto_toWeakSpace_iff_forall_tendsto_inner_left (u := fun n ↦ x' (φ n))).mpr
      fun z ↦ ?_
    rw [toDual_symm_apply]
    exact ((WeakDual.eval_continuous z).tendsto ℓ).comp hlim

/-- Every bounded sequence in a separable Hilbert space has a weakly convergent subsequence: if
`‖x n‖ ≤ C` for all `n`, there are a strictly increasing `φ` and `y` with `‖y‖ ≤ C` such that
`x (φ n)` converges weakly to `y`. -/
theorem tendsto_subseq_toWeakSpace_of_norm_le {x : ℕ → E} {C : ℝ} (hx : ∀ n, ‖x n‖ ≤ C) :
    ∃ (φ : ℕ → ℕ) (y : E), StrictMono φ ∧ ‖y‖ ≤ C ∧
      Tendsto (fun n ↦ toWeakSpace 𝕜 E (x (φ n))) atTop (𝓝 (toWeakSpace 𝕜 E y)) := by
  have hmem : ∀ n, toWeakSpace 𝕜 E (x n) ∈ toWeakSpace 𝕜 E '' Metric.closedBall (0 : E) C :=
    fun n ↦ ⟨x n, by simpa using hx n, rfl⟩
  obtain ⟨_, ⟨y, hy, rfl⟩, φ, hφ, hlim⟩ :=
    isSeqCompact_toWeakSpace_image_closedBall 𝕜 (0 : E) C hmem
  exact ⟨φ, y, hφ, by simpa using hy, hlim⟩

/-- Every bounded sequence in a separable Hilbert space has a weakly convergent subsequence: if
`‖x n‖ ≤ C` for all `n`, there are a strictly increasing `φ` and `y` with `‖y‖ ≤ C` such that
`⟪x (φ n), z⟫` converges to `⟪y, z⟫` for every `z`. -/
theorem tendsto_subseq_inner_left_of_norm_le {x : ℕ → E} {C : ℝ} (hx : ∀ n, ‖x n‖ ≤ C) :
    ∃ (φ : ℕ → ℕ) (y : E), StrictMono φ ∧ ‖y‖ ≤ C ∧
      ∀ z : E, Tendsto (fun n ↦ ⟪x (φ n), z⟫_𝕜) atTop (𝓝 ⟪y, z⟫_𝕜) :=
  let ⟨φ, y, hφ, hy, h⟩ := tendsto_subseq_toWeakSpace_of_norm_le 𝕜 hx
  ⟨φ, y, hφ, hy, tendsto_toWeakSpace_iff_forall_tendsto_inner_left.mp h⟩

/-- Every bounded sequence in a separable Hilbert space has a weakly convergent subsequence: if
`‖x n‖ ≤ C` for all `n`, there are a strictly increasing `φ` and `y` with `‖y‖ ≤ C` such that
`⟪z, x (φ n)⟫` converges to `⟪z, y⟫` for every `z`. -/
theorem tendsto_subseq_inner_right_of_norm_le {x : ℕ → E} {C : ℝ} (hx : ∀ n, ‖x n‖ ≤ C) :
    ∃ (φ : ℕ → ℕ) (y : E), StrictMono φ ∧ ‖y‖ ≤ C ∧
      ∀ z : E, Tendsto (fun n ↦ ⟪z, x (φ n)⟫_𝕜) atTop (𝓝 ⟪z, y⟫_𝕜) :=
  let ⟨φ, y, hφ, hy, h⟩ := tendsto_subseq_toWeakSpace_of_norm_le 𝕜 hx
  ⟨φ, y, hφ, hy, tendsto_toWeakSpace_iff_forall_tendsto_inner_right.mp h⟩

end InnerProductSpace
