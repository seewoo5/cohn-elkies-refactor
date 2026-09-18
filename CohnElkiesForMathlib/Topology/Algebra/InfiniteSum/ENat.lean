import Mathlib

/-!
# Sums of `ℕ∞`-valued functions

Every family `f : α → ℕ∞` is summable, with `∑' a, f a = ⨆ s : Finset α, ∑ a ∈ s, f a`; sums of
constants, reindexing along injective, surjective and bijective maps, sums over sigma types and
over pairwise disjoint unions, and `(⋃ i, s i).encard = ∑' i, (s i).encard` for pairwise disjoint
families of sets.
-/

namespace ENat

open Function Set

variable {α β : Type*} {f : α → ℕ∞}

protected theorem hasSum : HasSum f (⨆ s : Finset α, ∑ a ∈ s, f a) :=
  tendsto_atTop_iSup fun _ _ ↦ Finset.sum_le_sum_of_subset

@[simp] protected theorem summable : Summable f := ENat.hasSum.summable

protected theorem tsum_eq_iSup : ∑' a, f a = ⨆ s : Finset α, ∑ a ∈ s, f a := ENat.hasSum.tsum_eq

theorem tsum_const (c : ℕ∞) : ∑' _ : α, c = ENat.card α * c := by
  rcases finite_or_infinite α with h | h
  · have := Fintype.ofFinite α
    simp [tsum_fintype, ENat.card_eq_coe_fintype_card, nsmul_eq_mul]
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  rw [ENat.card_eq_top_of_infinite, ENat.top_mul hc, ENat.tsum_eq_iSup]
  refine iSup_eq_top.2 fun b hb ↦ ?_
  obtain ⟨s, hs⟩ := Finset.exists_card_eq (α := α) (b.toNat + 1)
  have h₁ : b < (s.card : ℕ∞) := by
    rw [← ENat.natCast_toNat hb.ne, hs]
    exact_mod_cast Nat.lt_succ_self _
  have h₂ : (s.card : ℕ∞) ≤ ∑ _a ∈ s, c := by
    simpa [Finset.sum_const, nsmul_eq_mul] using
      le_mul_of_one_le_right' (a := (s.card : ℕ∞)) (Order.one_le_iff_ne_zero.2 hc)
  exact ⟨s, h₁.trans_le h₂⟩

theorem tsum_subtype_const (s : Set α) (c : ℕ∞) :
    ∑' _ : s, c = s.encard * c := by
  rw [ENat.tsum_const, Set.encard]

theorem tsum_one : ∑' _ : α, 1 = ENat.card α := by
  simp [ENat.tsum_const]

theorem tsum_subtype_one (s : Set α) : ∑' _ : s, 1 = s.encard := by
  rw [ENat.tsum_one, Set.encard]

protected theorem tsum_comp_le_of_injective {φ : α → β} (hφ : Injective φ) (g : β → ℕ∞) :
    ∑' x, g (φ x) ≤ ∑' y, g y :=
  (ENat.summable (f := fun x ↦ g (φ x))).tsum_le_tsum_of_inj φ hφ (fun _ _ ↦ bot_le)
    (fun _ ↦ le_rfl) (ENat.summable (f := g))

protected theorem tsum_le_tsum_comp_of_surjective {φ : α → β} (hφ : Surjective φ) (g : β → ℕ∞) :
    ∑' y, g y ≤ ∑' x, g (φ x) :=
  calc ∑' y, g y = ∑' y, g (φ (surjInv hφ y)) := by simp [surjInv_eq hφ]
    _ ≤ ∑' x, g (φ x) := ENat.tsum_comp_le_of_injective (injective_surjInv hφ) fun x ↦ g (φ x)

protected theorem tsum_comp_of_bijective {φ : α → β} (hφ : φ.Bijective) (g : β → ℕ∞) :
    ∑' x, g (φ x) = ∑' y, g y :=
  (ENat.tsum_comp_le_of_injective hφ.injective g).antisymm
    (ENat.tsum_le_tsum_comp_of_surjective hφ.surjective g)

protected theorem tsum_sigma {β : α → Type*} (f : (Σ a, β a) → ℕ∞) :
    ∑' p : Σ a, β a, f p = ∑' (a) (b), f ⟨a, b⟩ :=
  Summable.tsum_sigma' (fun _ ↦ ENat.summable) ENat.summable

/-- A sum over a pairwise disjoint union is the sum of the sums over the pieces. -/
theorem tsum_iUnion_of_pairwise_disjoint {ι : Type*} (f : α → ℕ∞) (t : ι → Set α)
    (ht : Pairwise (Disjoint on t)) : ∑' x : ⋃ i, t i, f x = ∑' i, ∑' x : t i, f x :=
  calc ∑' x : ⋃ i, t i, f x = ∑' x : Σ i, t i, f x.2 := (ENat.tsum_comp_of_bijective
      (sigmaToiUnion_bijective t fun _ _ hij ↦ ht hij) _).symm
    _ = _ := ENat.tsum_sigma _

end ENat

/-- `(⋃ i, s i).encard = ∑' i, (s i).encard` for pairwise disjoint sets `s i`. -/
theorem Set.encard_disjoint_union_eq_tsum {ι α : Type*} {s : ι → Set α}
    (hs : Set.PairwiseDisjoint Set.univ s) : (⋃ i, s i).encard = ∑' i, (s i).encard := by
  simpa [ENat.tsum_subtype_one] using
    ENat.tsum_iUnion_of_pairwise_disjoint (f := fun _ : α ↦ (1 : ℕ∞)) (t := s)
      (by simpa [Set.PairwiseDisjoint, Set.pairwise_univ] using hs)
