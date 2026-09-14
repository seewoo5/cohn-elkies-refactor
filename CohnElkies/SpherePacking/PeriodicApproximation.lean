import CohnElkies.SpherePacking.Periodic

/-!
# The periodic packing constant equals the packing constant

A sphere packing of separation `1` can be approximated by periodic packings: keep the centers
inside a large axis-aligned cube `[0, L) ^ d` that are at distance at least `1 / 2` from its
boundary, and repeat them periodically along the cubic lattice `L • ℤ ^ d`.  The centers that are
lost near the boundary are negligible as `L → ∞`, which gives
`PeriodicSpherePackingConstant d = SpherePackingConstant d`.
-/

section
open scoped Real
open Complex (I)

section

open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module

section PeriodicConstantAux

open MeasureTheory Metric EuclideanSpace
open scoped Pointwise

variable {d : ℕ}

lemma abs_apply_le_norm (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) : |x i| ≤ ‖x‖ := by
  simpa using PiLp.norm_apply_le x i

/-- A ball of radius `r` around a point all of whose coordinates lie in `[r, L - r]` is contained
in the half-open cube `[0, L) ^ d`. -/
lemma ball_subset_axisAlignedCell {x : EuclideanSpace ℝ (Fin d)} {r L : ℝ}
    (hx : ∀ i : Fin d, x i ∈ Set.Icc r (L - r)) :
    ball x r ⊆ {y : EuclideanSpace ℝ (Fin d) | ∀ i : Fin d, y i ∈ Set.Ico (0 : ℝ) L} := by
  intro y hy i
  have hnorm : ‖y - x‖ < r := by simpa [Metric.mem_ball, dist_eq_norm, dist_comm] using hy
  obtain ⟨h₁, h₂⟩ := abs_lt.mp (lt_of_le_of_lt
    (by simpa using abs_apply_le_norm (y - x) i) hnorm)
  obtain ⟨h₃, h₄⟩ := hx i
  exact ⟨by linarith, by linarith⟩

/-- Two points whose balls of radius `r` lie in disjoint sets are at distance at least `2 * r`. -/
lemma le_dist_of_ball_subset_disjoint {x y : EuclideanSpace ℝ (Fin d)} {r : ℝ}
    {A B : Set (EuclideanSpace ℝ (Fin d))}
    (hx : ball x r ⊆ A) (hy : ball y r ⊆ B) (hAB : Disjoint A B) :
    2 * r ≤ dist x y := by
  by_contra! hlt
  have hhalf : (1 / 2 : ℝ) * dist x y < r := by linarith
  have hmx : midpoint ℝ x y ∈ ball x r := by
    simpa [Metric.mem_ball, dist_comm] using (by simpa using hhalf : dist (midpoint ℝ x y) x < r)
  have hmy : midpoint ℝ x y ∈ ball y r := by
    simpa [Metric.mem_ball, dist_comm] using
      (by simpa [dist_comm] using hhalf : dist (midpoint ℝ x y) y < r)
  exact Set.disjoint_left.1 hAB (hx hmx) (hy hmy)

open scoped Pointwise in
/-- The union of the `Λ`-translates of `F`, i.e. the set `F` repeated periodically. -/
noncomputable def latticeReplicatedCenters (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
    (F : Set (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)) :=
  ⋃ g : Λ, g +ᵥ F

lemma mem_latticeReplicatedCenters_iff {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
    {F : Set (EuclideanSpace ℝ (Fin d))} {x : EuclideanSpace ℝ (Fin d)} :
    x ∈ latticeReplicatedCenters (d := d) Λ F ↔ ∃ g : Λ, ∃ f ∈ F, x = g +ᵥ f := by
  simp [latticeReplicatedCenters, Set.mem_iUnion, Set.mem_vadd_set, eq_comm]

lemma add_mem_latticeReplicatedCenters {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
    {F : Set (EuclideanSpace ℝ (Fin d))} {x y : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ Λ) (hy : y ∈ latticeReplicatedCenters (d := d) Λ F) :
    x + y ∈ latticeReplicatedCenters (d := d) Λ F := by
  obtain ⟨g, f, hf, rfl⟩ := (mem_latticeReplicatedCenters_iff (Λ := Λ) (F := F) (x := y)).1 hy
  refine (mem_latticeReplicatedCenters_iff (Λ := Λ) (F := F)).2 ⟨(⟨x, hx⟩ : Λ) + g, f, hf, ?_⟩
  simp [Submodule.vadd_def, vadd_eq_add, add_assoc]

lemma ball_vadd_subset_vadd {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
    {D : Set (EuclideanSpace ℝ (Fin d))} {r : ℝ} {g : Λ} {x : EuclideanSpace ℝ (Fin d)}
    (hx : ball x r ⊆ D) :
    ball (g +ᵥ x) r ⊆ g +ᵥ D := by
  intro y hy
  refine Set.mem_vadd_set.2 ⟨(-g : Λ) +ᵥ y, ?_, by simp [Submodule.vadd_def, vadd_eq_add]⟩
  apply hx
  have : (- (g : EuclideanSpace ℝ (Fin d))) +ᵥ y ∈
        (- (g : EuclideanSpace ℝ (Fin d))) +ᵥ ball (g +ᵥ x) r :=
    Set.mem_vadd_set.2 ⟨y, by simpa [Submodule.vadd_def, vadd_eq_add] using hy, rfl⟩
  simpa [Metric.vadd_ball, add_vadd, Submodule.vadd_def, vadd_eq_add] using this

/-- The periodic packing obtained from the centers `F` by repeating them along the lattice `Λ`.
Here the `Λ`-translates of `D` tile the space and each ball of radius `separation / 2` around a
point of `F` is contained in `D`, so that the replicated centers are still `separation`-apart. -/
noncomputable def replicateToPeriodicPacking (S : SpherePacking d)
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (D F : Set (EuclideanSpace ℝ (Fin d)))
    (hD_unique_covers : ∀ x, ∃! g : Λ, g +ᵥ x ∈ D)
    (hF_centers : F ⊆ S.centers)
    (hF_ball : ∀ x ∈ F, ball x (S.separation / 2) ⊆ D) :
    PeriodicSpherePacking d where
  centers := latticeReplicatedCenters Λ F
  separation := S.separation
  separation_pos := S.separation_pos
  centers_dist := by
    intro a b hab
    obtain ⟨ga, fa, hfa, ha⟩ := mem_latticeReplicatedCenters_iff.1 a.property
    obtain ⟨gb, fb, hfb, hb⟩ := mem_latticeReplicatedCenters_iff.1 b.property
    change S.separation ≤ dist (a : EuclideanSpace ℝ (Fin d)) b
    rw [ha, hb]
    by_cases hgg : ga = gb
    · subst hgg
      have hne : fa ≠ fb := fun h ↦ hab (Subtype.ext (by rw [ha, hb, h]))
      simpa [Submodule.vadd_def, dist_eq_norm, add_sub_add_left_eq_sub] using
        S.distinct_centers_separation_bound fa fb (hF_centers hfa) (hF_centers hfb) hne
    · have := le_dist_of_ball_subset_disjoint
        (ball_vadd_subset_vadd (hF_ball fa hfa))
        (ball_vadd_subset_vadd (hF_ball fb hfb))
        (translates_disjoint_of_unique_cover hD_unique_covers hgg)
      linarith
  lattice := Λ
  lattice_action := fun _ _ hx hy ↦ add_mem_latticeReplicatedCenters hx hy
  lattice_discrete := inferInstance
  lattice_isZLattice := inferInstance

end PeriodicConstantAux

section PeriodicConstantCube

open scoped Pointwise

variable {d : ℕ}

/-- The half-open axis-aligned cube `[0, L) ^ d`. -/
def axisAlignedCell (L : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i : Fin d, x i ∈ Set.Ico (0 : ℝ) L}

/-- The closed cube `[r, L - r] ^ d`: the points of `[0, L) ^ d` whose coordinates are at
distance at least `r` from the boundary. -/
def insetAxisAlignedCell (L r : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i : Fin d, x i ∈ Set.Icc r (L - r)}

/-- The basis `L • e i` of `ℝ ^ d`, whose fundamental domain is the cube `[0, L) ^ d`. -/
noncomputable def axisCellBasis (L : ℝ) (hL : 0 < L) : Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) :=
  ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis).isUnitSMul
    (fun _ : Fin d ↦ IsUnit.mk0 L (ne_of_gt hL))

/-- The cubic lattice `L • ℤ ^ d`. -/
noncomputable def axisCellLattice (L : ℝ) (hL : 0 < L) : Submodule ℤ (EuclideanSpace ℝ (Fin d)) :=
  Submodule.span ℤ (Set.range (axisCellBasis (d := d) L hL))

/-- The fundamental domain of the basis `L • (e i)` is the half-open cube `[0, L) ^ d`. -/
lemma fundamentalDomain_axisCellBasis (L : ℝ) (hL : 0 < L) :
    fundamentalDomain (axisCellBasis (d := d) L hL) = axisAlignedCell (d := d) L := by
  ext x
  simp [ZSpan.mem_fundamentalDomain, axisAlignedCell, axisCellBasis,
    Module.Basis.repr_isUnitSMul, Units.smul_def, Units.val_inv_eq_inv_val, inv_mul_eq_div,
    le_div_iff₀ hL, div_lt_one hL]

lemma latticeReplicatedCenters_inter {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
    {D F : Set (EuclideanSpace ℝ (Fin d))}
    (hF_sub : F ⊆ D) (hD_unique_covers : ∀ x, ∃! g : Λ, g +ᵥ x ∈ D) :
    latticeReplicatedCenters (d := d) Λ F ∩ D = F := by
  ext x
  constructor
  · rintro ⟨hx, hxD⟩
    rcases (mem_latticeReplicatedCenters_iff (d := d) (Λ := Λ) (F := F)).1 hx with ⟨g, f, hf, hxf⟩
    obtain ⟨g₀, hg₀, hunique⟩ := hD_unique_covers f
    have hg : g = 0 := (hunique g (show g +ᵥ f ∈ D from hxf ▸ hxD)).trans
      (hunique 0 (by simpa using hF_sub hf)).symm
    simpa [hxf, hg] using hf
  · intro hx
    refine ⟨?_, hF_sub hx⟩
    exact (mem_latticeReplicatedCenters_iff (d := d) (Λ := Λ) (F := F)).2 ⟨0, x, hx, by simp⟩

end PeriodicConstantCube

section Periodic_Constant_Eq_Constant

open scoped Pointwise

namespace PeriodicConstant

variable {d : ℕ}

private lemma coordinate_preimage_volume (s : Set (Fin d → ℝ)) (hs : MeasurableSet s) :
    volume ((fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) ⁻¹' s) = volume s := by
  simpa using (PiLp.volume_preserving_ofLp (ι := Fin d)).measure_preimage hs.nullMeasurableSet

lemma exists_unique_vadd_mem_axisAlignedCell (L : ℝ) (hL : 0 < L) :
    ∀ x, ∃! g : axisCellLattice (d := d) L hL, g +ᵥ x ∈ axisAlignedCell (d := d) L := fun x ↦ by
    have h := exist_unique_vadd_mem_fundamentalDomain (axisCellBasis (d := d) L hL) x
    rwa [fundamentalDomain_axisCellBasis (d := d) (L := L) (hL := hL)] at h

lemma isBounded_axisAlignedCell (L : ℝ) (hL : 0 < L) : IsBounded (axisAlignedCell (d := d) L) := by
  simpa [fundamentalDomain_axisCellBasis (d := d) (L := L) (hL := hL)] using
    fundamentalDomain_isBounded (axisCellBasis (d := d) L hL)

lemma measurableSet_axisAlignedCell (L : ℝ) (hL : 0 < L) :
    MeasurableSet (axisAlignedCell (d := d) L) := by
  simpa [fundamentalDomain_axisCellBasis (d := d) (L := L) (hL := hL)] using
    fundamentalDomain_measurableSet (axisCellBasis (d := d) L hL)

/-- The cube `[0, L) ^ d` has volume `L ^ d`. -/
lemma axis_cell_volume_formula (L : ℝ) :
    volume (axisAlignedCell (d := d) L) = (ENNReal.ofReal L) ^ d := by
  have hcell : axisAlignedCell (d := d) L = (fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) ⁻¹'
      (Set.pi Set.univ fun _ : Fin d ↦ Set.Ico (0 : ℝ) L) := by
    ext x; simp [axisAlignedCell, Set.mem_pi]
  rw [hcell, coordinate_preimage_volume _
    (MeasurableSet.pi Set.countable_univ fun _ _ ↦ measurableSet_Ico), volume_pi, Measure.pi_pi]
  simp [Real.volume_Ico, sub_zero]

lemma insetAxisAlignedCell_eq_preimage (L r : ℝ) : insetAxisAlignedCell (d := d) L r =
      (fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) ⁻¹'
        (Set.pi Set.univ fun _ : Fin d ↦ Set.Icc r (L - r)) := by
  ext x
  simp [insetAxisAlignedCell, Pi.le_def, forall_and]

lemma volume_insetAxisAlignedCell (L r : ℝ) :
    volume (insetAxisAlignedCell (d := d) L r) = (ENNReal.ofReal (L - 2 * r)) ^ d := by
  have hmeas : MeasurableSet (Set.pi Set.univ fun _ : Fin d ↦ Set.Icc r (L - r)) :=
    MeasurableSet.pi Set.countable_univ fun _ _ ↦ measurableSet_Icc
  have hpre : volume (insetAxisAlignedCell (d := d) L r) =
        volume (Set.pi Set.univ fun _ : Fin d ↦ Set.Icc r (L - r)) := by
    simpa [insetAxisAlignedCell_eq_preimage (d := d) (L := L) (r := r)] using
      (coordinate_preimage_volume (d := d) (s := Set.pi Set.univ fun _ : Fin d ↦ Set.Icc r (L - r))
        hmeas)
  rw [hpre, volume_pi, Measure.pi_pi]
  simp [Real.volume_Icc, sub_eq_add_neg, add_left_comm, add_comm, two_mul]

lemma insetAxisAlignedCell_subset {L r : ℝ} (hr : 0 < r) :
    insetAxisAlignedCell (d := d) L r ⊆ axisAlignedCell (d := d) L := by
  intro x hx i
  have hxi := hx i
  exact ⟨(le_of_lt hr).trans hxi.1, hxi.2.trans_lt (sub_lt_self L hr)⟩

end PeriodicConstant

section PeriodicConstantApprox

open scoped Pointwise
open MeasureTheory Metric

namespace PeriodicConstantApprox

variable {d : ℕ}

lemma exists_unique_vadd_mem_vadd_axisAlignedCell (L : ℝ) (hL : 0 < L)
    (v : axisCellLattice (d := d) L hL) :
    ∀ x, ∃! g : axisCellLattice (d := d) L hL, g +ᵥ x ∈ v +ᵥ axisAlignedCell (d := d) L := by
  intro x
  have hvadd (a : axisCellLattice (d := d) L hL) :
      a +ᵥ x ∈ v +ᵥ axisAlignedCell (d := d) L ↔ (a - v) +ᵥ x ∈ axisAlignedCell (d := d) L := by
    simp [Set.mem_vadd_set_iff_neg_vadd_mem, Submodule.vadd_def, vadd_eq_add, sub_eq_add_neg,
      add_assoc, add_comm]
  obtain ⟨g, hg, hguniq⟩ := PeriodicConstant.exists_unique_vadd_mem_axisAlignedCell (d := d) L hL x
  refine ⟨g + v, (hvadd (a := g + v)).2 (by simpa using hg), ?_⟩
  intro a ha
  exact sub_eq_iff_eq_add.1 (hguniq _ ((hvadd a).1 ha))

lemma ball_subset_vadd_axisAlignedCell {L r : ℝ} (hL : 0 < L)
    {v : axisCellLattice (d := d) L hL} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ v +ᵥ insetAxisAlignedCell (d := d) L r) :
    ball x r ⊆ v +ᵥ axisAlignedCell (d := d) L := by
  have hx' : (- (v : EuclideanSpace ℝ (Fin d))) +ᵥ x ∈ insetAxisAlignedCell (d := d) L r := by
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem, Submodule.vadd_def] using hx
  have hball : ball ((- (v : EuclideanSpace ℝ (Fin d))) +ᵥ x) r ⊆ axisAlignedCell (d := d) L := by
    simpa [axisAlignedCell, insetAxisAlignedCell] using ball_subset_axisAlignedCell hx'
  simpa [add_vadd, Submodule.vadd_def, vadd_eq_add, add_assoc, add_comm] using
    ball_vadd_subset_vadd (Λ := axisCellLattice (d := d) L hL) (D := axisAlignedCell (d := d) L)
      (g := v) (x := (- (v : EuclideanSpace ℝ (Fin d))) +ᵥ x) (r := r) hball

/-- A ball contains only finitely many points of the cubic lattice `L • ℤ ^ d`. -/
lemma finite_axisCellLattice_inter_ball (L : ℝ) (hL : 0 < L) (R : ℝ) :
    Set.Finite {g : axisCellLattice (d := d) L hL | (g : EuclideanSpace ℝ (Fin d)) ∈ ball 0 R} := by
  refine ((ZSpan.setFinite_inter (axisCellBasis (d := d) L hL)
    (Metric.isBounded_ball (x := (0 : EuclideanSpace ℝ (Fin d))) (r := R))).preimage
    (f := fun g : axisCellLattice (d := d) L hL ↦ (g : EuclideanSpace ℝ (Fin d)))
    Subtype.val_injective.injOn).subset fun g hg ↦ ⟨hg, g.2⟩

end PeriodicConstantApprox

end PeriodicConstantApprox

end Periodic_Constant_Eq_Constant

end

section

open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open scoped Pointwise Topology

variable {d : ℕ}

namespace PeriodicConstantApprox

section CoordCubeCover

open Metric

variable (L : ℝ) (hL : 0 < L)

/-- The unique vector `g` of the cubic lattice `L • ℤ ^ d` with `g + x` in the cube
`[0, L) ^ d`. -/
noncomputable def axisCellCoverIndex (x : EuclideanSpace ℝ (Fin d)) :
    axisCellLattice (d := d) L hL :=
  Classical.choose (PeriodicConstant.exists_unique_vadd_mem_axisAlignedCell (d := d) L hL x)

lemma axisCellCoverIndex_vadd_mem (x : EuclideanSpace ℝ (Fin d)) :
    axisCellCoverIndex (d := d) L hL x +ᵥ x ∈ axisAlignedCell (d := d) L :=
  (Classical.choose_spec
    (PeriodicConstant.exists_unique_vadd_mem_axisAlignedCell (d := d) L hL x)).1

lemma neg_axisCellCoverIndex_mem_ball {C R : ℝ}
    (hC : axisAlignedCell (d := d) L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ ball 0 R) :
    ((-axisCellCoverIndex (d := d) L hL x : axisCellLattice (d := d) L hL) :
        EuclideanSpace ℝ (Fin d)) ∈ ball 0 (R + C) := by
  have hx0 : ‖x‖ < R := by simpa [mem_ball_zero_iff] using hx
  have hxgC : ‖(axisCellCoverIndex (d := d) L hL x : EuclideanSpace ℝ (Fin d)) + x‖ < C := by
    have hmem : (axisCellCoverIndex (d := d) L hL x : EuclideanSpace ℝ (Fin d)) + x ∈
        axisAlignedCell (d := d) L := by
      simpa [Submodule.vadd_def, vadd_eq_add] using axisCellCoverIndex_vadd_mem (d := d) L hL x
    simpa [mem_ball_zero_iff] using (hC hmem)
  have htri : ‖(axisCellCoverIndex (d := d) L hL x : EuclideanSpace ℝ (Fin d))‖ ≤
        ‖(axisCellCoverIndex (d := d) L hL x : EuclideanSpace ℝ (Fin d)) + x‖ + ‖x‖ := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using norm_sub_le
      (a := (axisCellCoverIndex (d := d) L hL x : EuclideanSpace ℝ (Fin d)) + x) (b := x)
  have : ‖(- (axisCellCoverIndex (d := d) L hL x : EuclideanSpace ℝ (Fin d)))‖ < R + C := by
    have : ‖(axisCellCoverIndex (d := d) L hL x : EuclideanSpace ℝ (Fin d))‖ < C + R := by
      refine lt_of_le_of_lt htri ?_
      simpa [add_comm, add_left_comm, add_assoc] using add_lt_add hxgC hx0
    simpa [norm_neg, add_comm, add_left_comm, add_assoc] using this
  simpa [mem_ball_zero_iff] using this

lemma mem_vadd_axisAlignedCell_iff (g : axisCellLattice (d := d) L hL)
    (x : EuclideanSpace ℝ (Fin d)) :
    x ∈ g +ᵥ axisAlignedCell (d := d) L ↔ g = -axisCellCoverIndex (d := d) L hL x := by
  constructor
  · intro hx
    have : (-g : axisCellLattice (d := d) L hL) = axisCellCoverIndex (d := d) L hL x :=
      (Classical.choose_spec
        (PeriodicConstant.exists_unique_vadd_mem_axisAlignedCell (d := d) L hL x)).2 _
        (by simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using hx)
    simpa using congrArg (fun t : axisCellLattice (d := d) L hL ↦ -t) this
  · rintro rfl
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using axisCellCoverIndex_vadd_mem (d := d) L hL x

end CoordCubeCover

section CoverVolumeBound

open scoped BigOperators

lemma vadd_axisAlignedCell_subset_ball {L : ℝ} (hL : 0 < L) {R C : ℝ}
    (hC : axisAlignedCell (d := d) L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C)
    {g : axisCellLattice (d := d) L hL}
    (hg : (g : EuclideanSpace ℝ (Fin d)) ∈ ball 0 (R + C)) :
    g +ᵥ axisAlignedCell (d := d) L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) (R + (2 * C)) := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have hx' : ‖x‖ < C := by simpa [mem_ball_zero_iff] using hC hx
  have hg' : ‖(g : EuclideanSpace ℝ (Fin d))‖ < R + C := by simpa [mem_ball_zero_iff] using hg
  have : ‖(g : EuclideanSpace ℝ (Fin d)) + x‖ < R + (2 * C) := by
    refine (lt_of_le_of_lt (norm_add_le _ _) ?_)
    simpa [two_mul, add_assoc, add_left_comm, add_comm] using add_lt_add hg' hx'
  simpa [Submodule.vadd_def, vadd_eq_add, mem_ball_zero_iff] using this

lemma lattice_count_mul_volume_cell_le_volume_ball {L : ℝ} (hL : 0 < L)
    {R C : ℝ} (hC : axisAlignedCell (d := d) L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C) :
    let htSet := PeriodicConstantApprox.finite_axisCellLattice_inter_ball (d := d) L hL (R + C)
    let t : Finset (axisCellLattice (d := d) L hL) := htSet.toFinset
    (t.card : ℝ≥0∞) * volume (axisAlignedCell (d := d) L) ≤
      volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + (2 * C))) := by
  intro htSet t
  have hdisj : Set.PairwiseDisjoint (↑t : Set (axisCellLattice (d := d) L hL))
        (fun g : axisCellLattice (d := d) L hL ↦ g +ᵥ axisAlignedCell (d := d) L) := by
    intro g _ h _ hgh
    exact translates_disjoint_of_unique_cover (d := d)
      (Λ := axisCellLattice (d := d) L hL) (D := axisAlignedCell (d := d) L)
      (PeriodicConstant.exists_unique_vadd_mem_axisAlignedCell (d := d) L hL) hgh
  have hmeas : ∀ g ∈ t, MeasurableSet (g +ᵥ axisAlignedCell (d := d) L) := by
    intro g _; simpa using
      (MeasurableSet.const_vadd (PeriodicConstant.measurableSet_axisAlignedCell (d := d) L hL) g)
  have hvol_union : volume (⋃ g ∈ t, g +ᵥ axisAlignedCell (d := d) L) =
        ∑ g ∈ t, volume (g +ᵥ axisAlignedCell (d := d) L) :=
    measure_biUnion_finset (μ := volume) hdisj hmeas
  have hsub : (⋃ g ∈ t, g +ᵥ axisAlignedCell (d := d) L) ⊆
      ball (0 : EuclideanSpace ℝ (Fin d)) (R + (2 * C)) := by
    intro y hy
    obtain ⟨g, hgT, hy'⟩ := Set.mem_iUnion₂.1 hy
    exact vadd_axisAlignedCell_subset_ball (hL := hL) (R := R) hC
      (htSet.mem_toFinset.1 (by simpa [t] using hgT)) hy'
  have hle := volume.mono hsub
  simp_all

end CoverVolumeBound

section BoundaryControl

open scoped ENNReal Pointwise BigOperators

/-- The vector of `ℝ ^ d` all of whose coordinates are equal to `c`. -/
def constVector (d : ℕ) (c : ℝ) : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 fun _ : Fin d ↦ c

/-- The shell around the boundary of the cube `[0, L) ^ d`, namely
`[-1/2, L + 1/2] ^ d \ [1, L - 1] ^ d`. -/
def boundaryShell (d : ℕ) (L : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  (constVector d (-(1 / 2 : ℝ)) +ᵥ insetAxisAlignedCell (d := d) (L + 1) 0) \
    insetAxisAlignedCell (d := d) L 1

lemma abs_apply_lt_of_norm_lt {x : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hx : ‖x‖ < r)
    (i : Fin d) : |x i| < r :=
  lt_of_le_of_lt (abs_apply_le_norm x i) hx

/-- Every point within distance `1 / 2` of the non-inner part of the cube `[0, L) ^ d` lies in
the boundary shell. -/
lemma boundary_add_ball_subset_boundaryShell (L : ℝ) :
    ((axisAlignedCell (d := d) L \ insetAxisAlignedCell (d := d) L (1 / 2)) +
      ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) ⊆ boundaryShell d L := by
  rintro _ ⟨a, ⟨ha, ha_boundary⟩, b, hb, rfl⟩
  have hb_norm : ‖b‖ < (1 / 2 : ℝ) := by simpa [mem_ball_zero_iff] using hb
  refine ⟨Set.mem_vadd_set.2 ⟨a + b - constVector d (-(1 / 2 : ℝ)), fun i ↦ ?_, by simp⟩,
    fun h_inset ↦ ha_boundary fun i ↦ ?_⟩
  · obtain ⟨hb₁, hb₂⟩ := abs_lt.mp (abs_apply_lt_of_norm_lt hb_norm i)
    obtain ⟨ha₁, ha₂⟩ := ha i
    change 0 ≤ (a + b - constVector d (-(1 / 2 : ℝ))) i ∧
      (a + b - constVector d (-(1 / 2 : ℝ))) i ≤ L + 1 - 0
    simp only [PiLp.sub_apply, PiLp.add_apply, constVector]
    constructor <;> linarith
  · obtain ⟨hb₁, hb₂⟩ := abs_lt.mp (abs_apply_lt_of_norm_lt hb_norm i)
    have hxi := h_inset i
    change 1 ≤ (a + b) i ∧ (a + b) i ≤ L - 1 at hxi
    simp only [PiLp.add_apply] at hxi
    change (1 / 2 : ℝ) ≤ a i ∧ a i ≤ L - 1 / 2
    exact ⟨by linarith [hxi.1], by linarith [hxi.2]⟩

variable (S : SpherePacking d)

lemma boundary_count_mul_ball_volume_le_shell {L : ℝ} (hL : 0 < L) (hSsep : S.separation = 1)
    {g : axisCellLattice (d := d) L hL} {s : Finset (EuclideanSpace ℝ (Fin d))}
    (hs_centers : ∀ x ∈ s, x ∈ S.centers)
    (hs_boundary : ∀ x ∈ s,
      x ∈ (g +ᵥ axisAlignedCell (d := d) L) \ (g +ᵥ insetAxisAlignedCell (d := d) L (1 / 2))) :
    (s.card : ℝ≥0∞) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (2⁻¹ : ℝ)) ≤
      volume (boundaryShell d L) := by
  classical
  let v : EuclideanSpace ℝ (Fin d) := g
  have hdisj : Set.PairwiseDisjoint (↑s : Set (EuclideanSpace ℝ (Fin d)))
      (fun x : EuclideanSpace ℝ (Fin d) ↦ ball (x - v) (1 / 2 : ℝ)) := by
    intro x hx y hy hxy
    refine ball_disjoint_ball ?_
    have hdist := S.distinct_centers_separation_bound x y (hs_centers x hx) (hs_centers y hy) hxy
    rw [hSsep] at hdist
    convert hdist using 1 <;> norm_num [dist_eq_norm, sub_sub_sub_cancel_right]
  have hsub : (⋃ x ∈ s, ball (x - v) (1 / 2 : ℝ)) ⊆ boundaryShell d L := by
    intro y hy
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.mp hy
    refine boundary_add_ball_subset_boundaryShell L (Set.mem_add.mpr
      ⟨x - v, ⟨?_, fun hinset ↦ (hs_boundary x hx).2 ?_⟩, y - (x - v),
        by simpa [mem_ball, dist_eq_norm] using hy, by abel⟩)
    · simpa [v, Set.mem_vadd_set_iff_neg_vadd_mem, Submodule.vadd_def,
        vadd_eq_add, sub_eq_add_neg, add_comm] using (hs_boundary x hx).1
    · simpa [v, Set.mem_vadd_set_iff_neg_vadd_mem, Submodule.vadd_def,
        vadd_eq_add, sub_eq_add_neg, add_comm] using hinset
  calc (s.card : ℝ≥0∞) * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (2⁻¹ : ℝ))
      = volume (⋃ x ∈ s, ball (x - v) (1 / 2 : ℝ)) := by
        rw [measure_biUnion_finset (μ := volume) hdisj fun _ _ ↦ measurableSet_ball]
        simp [Measure.addHaar_ball_center]
    _ ≤ volume (boundaryShell d L) := volume.mono hsub

end BoundaryControl

end PeriodicConstantApprox

namespace PeriodicConstantApprox

open Filter

variable {d : ℕ}

lemma inset_cell_subset_vadd_inset_cell (L : ℝ) : insetAxisAlignedCell (d := d) L 1 ⊆
      (constVector d (- (1 / 2 : ℝ))) +ᵥ insetAxisAlignedCell (d := d) (L + 1) 0 := by
  intro x hx
  refine (Set.mem_vadd_set_iff_neg_vadd_mem).2 ?_
  have hx' : ∀ i : Fin d, x.ofLp i ∈ Set.Icc (1 : ℝ) (L - 1) := by
    simpa [insetAxisAlignedCell, Set.mem_ofPred_eq] using hx
  simp only [insetAxisAlignedCell, Set.mem_ofPred_eq, constVector, vadd_eq_add, one_div,
    WithLp.ofLp_add, WithLp.ofLp_neg, Pi.add_apply, Pi.neg_apply, neg_neg]
  exact fun i ↦ ⟨by linarith [(hx' i).1], by linarith [(hx' i).2]⟩

/-- The volume of the boundary shell of the cube `[0, L) ^ d`. -/
lemma volume_boundaryShell (L : ℝ) : volume (boundaryShell d L) =
    (ENNReal.ofReal (L + 1)) ^ d - (ENNReal.ofReal (L - 2)) ^ d := by
  have hmeas_inner : MeasurableSet (insetAxisAlignedCell (d := d) L 1) := by
    have hmeasPi : MeasurableSet (Set.pi Set.univ fun _ : Fin d ↦ Set.Icc (1 : ℝ) (L - 1)) :=
      MeasurableSet.pi Set.countable_univ fun _ _ ↦ measurableSet_Icc
    have hmp : MeasurePreserving (fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp) := by
      simpa using (PiLp.volume_preserving_ofLp (ι := Fin d))
    simpa [PeriodicConstant.insetAxisAlignedCell_eq_preimage (L := L) (r := (1 : ℝ))] using
      hmeasPi.preimage hmp.measurable
  have hfin : volume (insetAxisAlignedCell (d := d) L 1) ≠ ∞ := by
    simp [PeriodicConstant.volume_insetAxisAlignedCell]
  rw [boundaryShell, measure_sdiff (μ := volume) (inset_cell_subset_vadd_inset_cell L)
    hmeas_inner.nullMeasurableSet hfin, measure_vadd]
  simp [PeriodicConstant.volume_insetAxisAlignedCell]

section CubeLatticeCovolume

open scoped ENNReal
open ZSpan

lemma covolume_axisCellLattice (L : ℝ) (hL : 0 < L) :
    ZLattice.covolume (axisCellLattice (d := d) L hL) volume =
      (volume (axisAlignedCell (d := d) L)).toReal := by
  have : DiscreteTopology (axisCellLattice (d := d) L hL) :=
    ZSpan.instDiscreteTopologySubtypeMemSubmoduleIntSpanRangeCoeBasisRealOfFinite
      (axisCellBasis (d := d) L hL)
  have : IsZLattice ℝ (axisCellLattice (d := d) L hL) :=
    instIsZLatticeRealSpan (axisCellBasis (d := d) L hL)
  have hfund : IsAddFundamentalDomain (axisCellLattice (d := d) L hL)
        (fundamentalDomain (axisCellBasis (d := d) L hL)) volume :=
    ZSpan.isAddFundamentalDomain (axisCellBasis (d := d) L hL) volume
  simpa [Measure.real, fundamentalDomain_axisCellBasis (d := d) (L := L) (hL := hL)] using
    (ZLattice.covolume_eq_measure_fundamentalDomain (L := axisCellLattice (d := d) L hL)
      (μ := volume) hfund)

lemma covolume_axisCellLattice_toNNReal (L : ℝ) (hL : 0 < L) :
    Real.toNNReal (ZLattice.covolume (axisCellLattice (d := d) L hL) volume) =
      (volume (axisAlignedCell (d := d) L)).toNNReal := by
  simp [covolume_axisCellLattice (d := d) (L := L) hL]

end CubeLatticeCovolume

section PeriodizeCubeDensity

open scoped ENNReal Pointwise
open SpherePacking EuclideanSpace MeasureTheory Metric Bornology

variable {d : ℕ}

lemma exists_replicated_packing_density_eq (hd : 0 < d) (S : SpherePacking d)
    (hSsep : S.separation = 1) {L : ℝ} (hL : 0 < L) {g : axisCellLattice (d := d) L hL}
    (F : Finset (EuclideanSpace ℝ (Fin d)))
    (hF_centers : ∀ x ∈ F, x ∈ S.centers)
    (hF_inner : ∀ x ∈ F, x ∈ g +ᵥ insetAxisAlignedCell (d := d) L (2⁻¹ : ℝ)) :
    ∃ P : PeriodicSpherePacking d, P.separation = 1 ∧ P.upperPackingDensity = (F.card : ℝ≥0∞) *
              volume (ball (0 : EuclideanSpace ℝ (Fin d)) (2⁻¹ : ℝ)) /
            Real.toNNReal (ZLattice.covolume (axisCellLattice (d := d) L hL) volume) := by
  let Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d)) := axisCellLattice (d := d) L hL
  let D : Set (EuclideanSpace ℝ (Fin d)) := g +ᵥ axisAlignedCell (d := d) L
  let Fset : Set (EuclideanSpace ℝ (Fin d)) := (F : Set (EuclideanSpace ℝ (Fin d)))
  have : DiscreteTopology Λ :=
    ZSpan.instDiscreteTopologySubtypeMemSubmoduleIntSpanRangeCoeBasisRealOfFinite
      (axisCellBasis (d := d) L hL)
  have : IsZLattice ℝ Λ := instIsZLatticeRealSpan (axisCellBasis (d := d) L hL)
  let P : PeriodicSpherePacking d := replicateToPeriodicPacking (d := d) S (Λ := Λ) D Fset
      (hD_unique_covers :=
        PeriodicConstantApprox.exists_unique_vadd_mem_vadd_axisAlignedCell (d := d) L hL g)
      (hF_centers := by assumption)
      (hF_ball := by
        intro x hx
        have hx' : x ∈ F := by simpa [Fset] using hx
        have hxInner : x ∈ g +ᵥ insetAxisAlignedCell (d := d) L (S.separation / 2) := by
          simpa [hSsep] using (hF_inner x hx')
        exact ball_subset_vadd_axisAlignedCell hL hxInner)
  have hPsep : P.separation = 1 := by simpa [P, hSsep]
  refine ⟨P, hPsep, ?_⟩
  have hD_bounded : IsBounded D := by
    simpa [D, Submodule.vadd_def, vadd_eq_add] using
      (PeriodicConstant.isBounded_axisAlignedCell (d := d) L hL).vadd (g : EuclideanSpace ℝ (Fin d))
  have hD_unique : ∀ x, ∃! g0 : (axisCellLattice (d := d) L hL), g0 +ᵥ x ∈ D :=
    PeriodicConstantApprox.exists_unique_vadd_mem_vadd_axisAlignedCell (d := d) L hL g
  have hF_sub : Fset ⊆ D := by
    intro x hx
    have hx' : x ∈ F := by simpa [Fset] using hx
    rcases (hF_inner x hx') with ⟨a, ha, rfl⟩
    have ha' : a ∈ axisAlignedCell (d := d) L :=
      PeriodicConstant.insetAxisAlignedCell_subset (d := d) (L := L) (r := (2⁻¹ : ℝ))
        (by norm_num) ha
    exact ⟨a, ha', rfl⟩
  have hcenters_inter : P.centers ∩ D = Fset := by
    simpa [P, replicateToPeriodicPacking, Fset] using
      (latticeReplicatedCenters_inter (d := d) (Λ := axisCellLattice (d := d) L hL) (D := D)
        (F := Fset) hF_sub hD_unique)
  have hnumReps : P.centerOrbitCardinality = F.card := by
    have h' : (P.centerOrbitCardinality : ENat) = (F.card : ENat) := by
      simpa [hcenters_inter, Fset, Set.encard_coe_eq_coe_finsetCard] using
        (P.encard_centers_in_fundamental_region (d := d) (D := D) hD_bounded hD_unique hd).symm
    exact_mod_cast h'
  simpa [hnumReps, hPsep] using! P.density_eq_numReps_mul_volume_ball_div_covolume (d := d) hd

end PeriodizeCubeDensity

lemma tendsto_shell_ratio_zero :
    Tendsto (fun L : ℝ ↦ ((L + 1) ^ d - (L - 2) ^ d) / (L ^ d)) atTop (𝓝 (0 : ℝ)) := by
  have hinv : Tendsto (fun L : ℝ ↦ L⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hplus : Tendsto (fun L : ℝ ↦ 1 + L⁻¹) atTop (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds.add hinv)
  have hminus : Tendsto (fun L : ℝ ↦ 1 - 2 * L⁻¹) atTop (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv))
  have hlimit : Tendsto (fun L : ℝ ↦ (1 + L⁻¹) ^ d - (1 - 2 * L⁻¹) ^ d) atTop (𝓝 (0 : ℝ)) := by
    simpa using (hplus.pow d).sub (hminus.pow d)
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have hplus_eq : 1 + L⁻¹ = (L + 1) / L := by field_simp [hL.ne']
  have hminus_eq : 1 - 2 * L⁻¹ = (L - 2) / L := by field_simp [hL.ne']
  rw [hplus_eq, hminus_eq, div_pow, div_pow, ← sub_div]

/-- The boundary shell of the cube `[0, L) ^ d` is negligible compared to the cube itself. -/
lemma tendsto_volume_boundaryShell_div_cell :
    Tendsto (fun L : ℝ ↦ volume (boundaryShell d L) / volume (axisAlignedCell (d := d) L))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
  have hlimit : Tendsto (fun L : ℝ ↦ ENNReal.ofReal (((L + 1) ^ d - (L - 2) ^ d) / (L ^ d)))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_shell_ratio_zero (d := d))
  refine hlimit.congr' ?_
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with L hL
  have hL0 : 0 < L := by linarith
  have hLplus : 0 ≤ L + 1 := by linarith
  have hLminus : 0 ≤ L - 2 := by linarith
  rw [volume_boundaryShell, PeriodicConstant.axis_cell_volume_formula,
    ← ENNReal.ofReal_pow hLplus d, ← ENNReal.ofReal_pow hLminus d,
    ← ENNReal.ofReal_pow hL0.le d,
    ← ENNReal.ofReal_sub,
    ← ENNReal.ofReal_div_of_pos (pow_pos hL0 d)]
  exact pow_nonneg hLminus d

end PeriodicConstantApprox

namespace SpherePacking

open Filter
open scoped ENNReal BigOperators

variable {d : ℕ}

theorem exists_periodic_unit_packing_above_density_threshold (hd : 0 < d)
    (S : SpherePacking d) (hSsep : S.separation = 1) {b : ℝ≥0∞} (hb : b < S.upperPackingDensity) :
    ∃ P : PeriodicSpherePacking d, P.separation = 1 ∧ b < P.upperPackingDensity := by
  classical
  by_contra! hnone
  obtain ⟨c, hbc, hc⟩ := exists_between hb
  let cell : ℝ → ℝ≥0∞ := fun L ↦ volume (axisAlignedCell (d := d) L)
  let shell : ℝ → ℝ≥0∞ := fun L ↦ volume (PeriodicConstantApprox.boundaryShell d L)
  have hshell : Tendsto (fun L : ℝ ↦ shell L / cell L) atTop (𝓝 0) := by
    simpa [shell, cell] using
      (PeriodicConstantApprox.tendsto_volume_boundaryShell_div_cell (d := d))
  have hsmall : ∀ᶠ L : ℝ in atTop, b + shell L / cell L < c := by
    have hlim : Tendsto (fun L : ℝ ↦ b + shell L / cell L) atTop (𝓝 b) := by
      simpa using tendsto_const_nhds.add hshell
    exact hlim.eventually (Iio_mem_nhds hbc)
  obtain ⟨L, hL, hsmallL⟩ := ((eventually_gt_atTop (0 : ℝ)).and hsmall).exists
  have hcell_top : cell L ≠ ∞ := by simp [cell, PeriodicConstant.axis_cell_volume_formula]
  have hcell_zero : cell L ≠ 0 := by simp [cell, PeriodicConstant.axis_cell_volume_formula, hL]
  have hden : (↑(Real.toNNReal (ZLattice.covolume (axisCellLattice (d := d) L hL) volume)) : ℝ≥0∞) =
        cell L := by
    rw [PeriodicConstantApprox.covolume_axisCellLattice_toNNReal (d := d) L hL]
    exact ENNReal.coe_toNNReal hcell_top
  obtain ⟨C, hC⟩ : ∃ C : ℝ, axisAlignedCell (d := d) L ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) C :=
    by simpa using (PeriodicConstant.isBounded_axisAlignedCell (d := d) L hL).subset_ball 0
  let A : ℝ≥0∞ := b + shell L / cell L
  have hAc : A < c := hsmallL
  have hratio : Tendsto (fun R : ℝ ↦ A *
        (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + (1 / 2 + 2 * C))) /
          volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + 0)))) atTop (𝓝 A) := by
    simpa using (ENNReal.Tendsto.const_mul (volume_ball_add_div_volume_ball_add_tendsto_one
          (d := d) (C := 1 / 2 + 2 * C) (C' := 0) hd)
        (Or.inl one_ne_zero))
  have hratio_small : ∀ᶠ R : ℝ in atTop, A *
      (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + (1 / 2 + 2 * C))) /
        volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + 0))) < c :=
    hratio.eventually (Iio_mem_nhds hAc)
  have hfreq : ∃ᶠ R in (atTop : Filter ℝ), c < S.densityInsideRadius R :=
    frequently_lt_of_lt_limsup (u := S.densityInsideRadius) (b := c)
      (h := by simpa [SpherePacking.upperPackingDensity] using hc)
  obtain ⟨R, hR_density, hR_ratio⟩ := (hfreq.and_eventually hratio_small).exists
  let huSet : (S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + (1 / 2 : ℝ))).Finite :=
    Set.finite_coe_iff.1 (S.finite_centers_inside_ball _)
  let u : Finset (EuclideanSpace ℝ (Fin d)) := huSet.toFinset
  let htSet := PeriodicConstantApprox.finite_axisCellLattice_inter_ball (d := d) L hL
    (R + (1 / 2 : ℝ) + C)
  let t : Finset (axisCellLattice (d := d) L hL) := htSet.toFinset
  let index (x : EuclideanSpace ℝ (Fin d)) : axisCellLattice (d := d) L hL :=
    -PeriodicConstantApprox.axisCellCoverIndex (d := d) L hL x
  have hindex : ∀ x ∈ u, index x ∈ t := by
    intro x hx
    have hxball : x ∈ ball (0 : EuclideanSpace ℝ (Fin d)) (R + (1 / 2 : ℝ)) :=
      (huSet.mem_toFinset.mp (by simpa [u] using hx)).2
    apply htSet.mem_toFinset.mpr
    simpa [index, t] using (PeriodicConstantApprox.neg_axisCellCoverIndex_mem_ball
        (d := d) L hL (C := C) (R := R + (1 / 2 : ℝ)) hC hxball)
  let piece (g : axisCellLattice (d := d) L hL) : Finset (EuclideanSpace ℝ (Fin d)) :=
    u.filter fun x ↦ index x = g
  let inner (g : axisCellLattice (d := d) L hL) : Finset (EuclideanSpace ℝ (Fin d)) :=
    (piece g).filter fun x ↦ x ∈ g +ᵥ insetAxisAlignedCell (d := d) L (2⁻¹ : ℝ)
  let boundary (g : axisCellLattice (d := d) L hL) : Finset (EuclideanSpace ℝ (Fin d)) :=
    (piece g).filter fun x ↦ x ∉ g +ᵥ insetAxisAlignedCell (d := d) L (2⁻¹ : ℝ)
  let V : ℝ≥0∞ := volume (ball (0 : EuclideanSpace ℝ (Fin d)) (2⁻¹ : ℝ))
  have hpiece_center {g : axisCellLattice (d := d) L hL}
      {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ piece g) : x ∈ S.centers := by
    simp only [piece, Finset.mem_filter] at hx
    exact (huSet.mem_toFinset.mp (by simpa [u] using hx.1)).1
  have hpiece_cell {g : axisCellLattice (d := d) L hL}
      {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ piece g) :
      x ∈ g +ᵥ axisAlignedCell (d := d) L := by
    simp only [piece, Finset.mem_filter] at hx
    exact (PeriodicConstantApprox.mem_vadd_axisAlignedCell_iff (d := d) L hL g x).2
      (by simpa [index] using hx.2.symm)
  have hinner_bound (g : axisCellLattice (d := d) L hL) :
      ((inner g).card : ℝ≥0∞) * V ≤ b * cell L := by
    obtain ⟨P, hPsep, hPdensity⟩ := PeriodicConstantApprox.exists_replicated_packing_density_eq
        (d := d) hd S hSsep hL (inner g)
        (fun x hx ↦ hpiece_center (Finset.mem_filter.mp (by simpa [inner] using hx)).1)
        (fun x hx ↦ (Finset.mem_filter.mp (by simpa [inner] using hx)).2)
    have hPbound : P.upperPackingDensity ≤ b := hnone P hPsep
    rw [hPdensity, hden] at hPbound
    exact (ENNReal.div_le_iff hcell_zero hcell_top).mp (by simpa [V] using hPbound)
  have hboundary_bound (g : axisCellLattice (d := d) L hL) :
      ((boundary g).card : ℝ≥0∞) * V ≤ shell L := by
    refine PeriodicConstantApprox.boundary_count_mul_ball_volume_le_shell (d := d) S hL hSsep
      (g := g) (fun x hx ↦ ?_) (fun x hx ↦ ?_) <;> simp only [boundary, Finset.mem_filter] at hx
    · exact hpiece_center hx.1
    · exact ⟨hpiece_cell hx.1, by simpa [one_div] using hx.2⟩
  have hpiece_bound (g : axisCellLattice (d := d) L hL) :
      ((piece g).card : ℝ≥0∞) * V ≤ A * cell L := by
    have hcard : (inner g).card + (boundary g).card = (piece g).card := by
      simpa [inner, boundary] using (Finset.card_filter_add_card_filter_not (s := piece g)
          (fun x : EuclideanSpace ℝ (Fin d) ↦ x ∈ g +ᵥ insetAxisAlignedCell (d := d) L (2⁻¹ : ℝ)))
    have hcard' : ((piece g).card : ℝ≥0∞) = ((inner g).card : ℝ≥0∞) + (boundary g).card := by
      exact_mod_cast hcard.symm
    calc
      ((piece g).card : ℝ≥0∞) * V = ((inner g).card : ℝ≥0∞) * V +
            ((boundary g).card : ℝ≥0∞) * V := by rw [hcard', add_mul]
      _ ≤ b * cell L + shell L := add_le_add (hinner_bound g) (hboundary_bound g)
      _ = A * cell L := by simp [A, add_mul, ENNReal.div_mul_cancel hcell_zero hcell_top]
  have hpartition : ∑ g ∈ t, (piece g).card = u.card := by
    simpa [piece, Finset.filter_eq_self.mpr hindex] using
      (Finset.sum_card_fiberwise_eq_card_filter u t index)
  have hsum_bound : (u.card : ℝ≥0∞) * V ≤ (t.card : ℝ≥0∞) * (A * cell L) := by
    have hcast : (u.card : ℝ≥0∞) = ∑ g ∈ t, ((piece g).card : ℝ≥0∞) := by
      exact_mod_cast hpartition.symm
    calc
      (u.card : ℝ≥0∞) * V = (∑ g ∈ t, ((piece g).card : ℝ≥0∞)) * V := by rw [hcast]
      _ = ∑ g ∈ t, ((piece g).card : ℝ≥0∞) * V := by simp_rw [Finset.sum_mul]
      _ ≤ ∑ _g ∈ t, A * cell L := Finset.sum_le_sum fun g _ ↦ hpiece_bound g
      _ = (t.card : ℝ≥0∞) * (A * cell L) := by simp [nsmul_eq_mul]
  have ht_volume : (t.card : ℝ≥0∞) * cell L ≤ volume (ball (0 : EuclideanSpace ℝ (Fin d))
        ((R + (1 / 2 : ℝ)) + 2 * C)) := by
    simpa [t, htSet, cell] using
      (PeriodicConstantApprox.lattice_count_mul_volume_cell_le_volume_ball
        (d := d) (hL := hL) (R := R + (1 / 2 : ℝ)) (C := C) hC)
  have hcenter_bound : (u.card : ℝ≥0∞) * V ≤ A * volume (ball (0 : EuclideanSpace ℝ (Fin d))
        (R + (1 / 2 + 2 * C))) := by
    calc
      (u.card : ℝ≥0∞) * V ≤ (t.card : ℝ≥0∞) * (A * cell L) := hsum_bound
      _ = A * ((t.card : ℝ≥0∞) * cell L) := by ac_rfl
      _ ≤ A * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + (1 / 2 + 2 * C))) := by
          gcongr
          simpa [add_assoc] using ht_volume
  have hlocal_bound : S.densityInsideRadius R ≤ (u.card : ℝ≥0∞) * V /
      volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
    have h := S.local_density_upper_bound hd R
    simp only [hSsep, one_div] at h
    rw [show (S.centers ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + (2⁻¹ : ℝ))).encard
      = (u.card : ENat) from by simpa [u, huSet, one_div] using
        huSet.encard_eq_coe_toFinset_card] at h
    simpa [V] using h
  refine absurd hR_density (not_lt.2 (le_of_lt (lt_of_le_of_lt ?_ hR_ratio)))
  calc S.densityInsideRadius R
      ≤ (u.card : ℝ≥0∞) * V / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := hlocal_bound
    _ ≤ A * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + (1 / 2 + 2 * C)))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by gcongr
    _ = A * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + (1 / 2 + 2 * C))) /
        volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + 0))) := by simp [div_eq_mul_inv, mul_assoc]

end SpherePacking

theorem periodic_packing_supremum_eq_unrestricted (hd : 0 < d) :
    PeriodicSpherePackingConstant d = SpherePackingConstant d := by
  rw [periodic_packing_supremum_eq_unit_separation (d := d),
    SpherePacking.packing_supremum_eq_unit_separation (d := d)]
  refine le_antisymm (iSup₂_le fun P hPsep ↦ le_iSup_of_le P.toSpherePacking
    (le_iSup_of_le hPsep le_rfl)) (iSup₂_le fun S hSsep ↦ le_of_forall_lt fun a ha ↦ ?_)
  obtain ⟨b, hab, hbS⟩ := exists_between ha
  obtain ⟨P, hPsep, hbP⟩ :=
    SpherePacking.exists_periodic_unit_packing_above_density_threshold hd S hSsep hbS
  exact hab.trans (hbP.trans_le (le_iSup_of_le P (le_iSup_of_le hPsep le_rfl)))

end

end
