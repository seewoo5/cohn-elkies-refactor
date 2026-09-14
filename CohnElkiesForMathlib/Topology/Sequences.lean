import Mathlib

/-!
# Convergence of a sequence from its even and odd subsequences

`Filter.tendsto_of_even_odd`: a sequence in a topological space converges to `x` as soon as its
even and its odd subsequence converge to `x`.
-/

open Filter
open scoped Topology

/-- A sequence converges as soon as its even and its odd subsequence converge to the same limit. -/
theorem Filter.tendsto_of_even_odd {X : Type*} [TopologicalSpace X] {f : ℕ → X} {x : X}
    (heven : Tendsto (fun k : ℕ ↦ f (2 * k)) atTop (𝓝 x))
    (hodd : Tendsto (fun k : ℕ ↦ f (2 * k + 1)) atTop (𝓝 x)) : Tendsto f atTop (𝓝 x) := by
  refine tendsto_iff_forall_eventually_mem.2 fun s hs ↦ ?_
  obtain ⟨a, ha⟩ := eventually_atTop.1 (heven.eventually hs)
  obtain ⟨b, hb⟩ := eventually_atTop.1 (hodd.eventually hs)
  filter_upwards [eventually_ge_atTop (2 * max a b + 1)] with n hn
  rcases Nat.even_or_odd n with h | h
  · obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp h
    exact ha k (by lia)
  · obtain ⟨k, rfl⟩ := odd_iff_exists_bit1.mp h
    exact hb k (by lia)
