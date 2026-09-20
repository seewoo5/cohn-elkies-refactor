import CohnElkies.Basic

/-!
# Sphere packings and packing densities

A `SpherePacking d` (defined in `CohnElkies.Basic`, together with its density inside a ball, its
upper density and the packing constant `SpherePackingConstant d`) is a set of `centers` in `ℝ ^ d`
that are pairwise at distance at least `separation`; a `PeriodicSpherePacking d` is a sphere
packing whose centers are invariant under a full-rank lattice, with packing constant
`PeriodicSpherePackingConstant d`.
-/

section

open scoped Real
open Complex (I)

section

open Metric MeasureTheory

variable {r : ℝ} {ι : Type*} [Fintype ι]

theorem EuclideanSpace.euclidean_ball_volume_positive [Nonempty ι] (x : EuclideanSpace ℝ ι)
    (hr : 0 < r) : 0 < volume (ball x r) :=
  measure_ball_pos volume x hr

end

section

open MeasureTheory Metric Filter
open Module

open scoped BigOperators ENNReal Pointwise

section Definitions

/-- A periodic sphere packing: a sphere packing whose set of centers is invariant under
translation by a full-rank lattice. -/
structure PeriodicSpherePacking (d : ℕ) extends SpherePacking d where
  /-- The lattice of periods. -/
  lattice : Submodule ℤ (EuclideanSpace ℝ (Fin d))
  /-- The set of centers is invariant under translation by the lattice. -/
  lattice_action : ∀ ⦃x y⦄, x ∈ lattice → y ∈ centers → x + y ∈ centers
  /-- The lattice is discrete. -/
  lattice_discrete : DiscreteTopology lattice := by infer_instance
  /-- The lattice has full rank. -/
  lattice_isZLattice : IsZLattice ℝ lattice := by infer_instance

variable {d : ℕ}

attribute [instance] PeriodicSpherePacking.lattice_discrete
attribute [instance] PeriodicSpherePacking.lattice_isZLattice

theorem SpherePacking.distinct_centers_separation_bound (S : SpherePacking d)
    (x y : EuclideanSpace ℝ (Fin d)) (hx : x ∈ S.centers) (hy : y ∈ S.centers) (hxy : x ≠ y) :
    S.separation ≤ dist x y := by
  simpa only [Subtype.dist_eq] using S.centers_dist
    (fun h ↦ hxy (congrArg Subtype.val h) : (⟨x, hx⟩ : S.centers) ≠ ⟨y, hy⟩)

instance PeriodicSpherePacking.instFullRankPackingLattice (S : PeriodicSpherePacking d) :
    IsZLattice ℝ S.lattice :=
  S.lattice_isZLattice

instance SpherePacking.instDiscretePackingCenters (S : SpherePacking d) :
    DiscreteTopology S.centers :=
  DiscreteTopology.of_forall_le_dist S.separation_pos S.centers_dist

/-- The lattice of a periodic packing acts on its centers by translation. -/
noncomputable instance PeriodicSpherePacking.latticeCenterTranslationAction
    (S : PeriodicSpherePacking d) : AddAction S.lattice S.centers where
  vadd x y := ⟨(x : EuclideanSpace ℝ (Fin d)) + y, S.lattice_action x.property y.property⟩
  zero_vadd y := Subtype.ext (zero_add (y : EuclideanSpace ℝ (Fin d)))
  add_vadd x y z := Subtype.ext (add_assoc (x : EuclideanSpace ℝ (Fin d)) y z)

theorem PeriodicSpherePacking.integral_basis_spans_packing_lattice
    (S : PeriodicSpherePacking d) {ι : Type*} (b : Basis ι ℤ S.lattice) :
    Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ _)) = S.lattice :=
  Basis.ofZLatticeBasis_span ℝ S.lattice b

theorem PeriodicSpherePacking.mem_integral_basis_span_iff
    (S : PeriodicSpherePacking d) {ι : Type*} (b : Basis ι ℤ S.lattice) (v) :
    v ∈ Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ _)) ↔ v ∈ S.lattice :=
  SetLike.ext_iff.mp (S.integral_basis_spans_packing_lattice b) v

end Definitions

section Scaling
variable {d : ℕ}
open Real

/-- The packing `c • S`, obtained by scaling all centers of `S` by a factor `c > 0`; its
separation is `c * S.separation`. -/
def SpherePacking.rescaleConfiguration (S : SpherePacking d) {c : ℝ} (hc : 0 < c) :
    SpherePacking d where
  centers := (fun x : EuclideanSpace ℝ (Fin d) ↦ c • x) '' S.centers
  separation := c * S.separation
  separation_pos := mul_pos hc S.separation_pos
  centers_dist := by
    rintro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩ hxy
    have hne : x ≠ y := fun h ↦ hxy (by subst h; rfl)
    change c * S.separation ≤ dist (c • x) (c • y)
    simpa [dist_smul₀, abs_of_pos hc] using
      mul_le_mul_of_nonneg_left (S.distinct_centers_separation_bound x y hx hy hne) hc.le

/-- The periodic packing `c • S`, obtained by scaling both the centers and the lattice of `S` by
a factor `c > 0`. -/
noncomputable def PeriodicSpherePacking.rescaleConfiguration (S : PeriodicSpherePacking d) {c : ℝ}
    (hc : 0 < c) :
    PeriodicSpherePacking d := by
  let scale : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
    LinearMap.lsmul ℝ (EuclideanSpace ℝ (Fin d)) c
  let scaledLattice : Submodule ℤ (EuclideanSpace ℝ (Fin d)) :=
    S.lattice.map (scale.restrictScalars ℤ)
  have hmem (x : EuclideanSpace ℝ (Fin d)) : x ∈ S.lattice ↔ c • x ∈ scaledLattice := by
    refine ⟨fun hx ↦ ⟨x, hx, rfl⟩, ?_⟩
    rintro ⟨y, hy, hxy : c • y = c • x⟩
    rwa [smul_right_injective _ hc.ne' hxy] at hy
  letI : DiscreteTopology scaledLattice :=
    ((Homeomorph.smulOfNeZero c hc.ne').subtype hmem).discreteTopology
  letI : IsZLattice ℝ scaledLattice := ⟨by
    have hcoe : (scaledLattice : Set (EuclideanSpace ℝ (Fin d)))
        = scale '' (S.lattice : Set (EuclideanSpace ℝ (Fin d))) := rfl
    rw [hcoe, Submodule.span_image, IsZLattice.span_top, Submodule.map_top,
      LinearMap.range_eq_top]
    exact fun x ↦ ⟨c⁻¹ • x, by simp [scale, smul_smul, hc.ne']⟩⟩
  refine
    { toSpherePacking := S.toSpherePacking.rescaleConfiguration hc
      lattice := scaledLattice
      lattice_action := ?_
      lattice_discrete := inferInstance
      lattice_isZLattice := inferInstance }
  rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
  exact ⟨x + y, S.lattice_action hx hy, smul_add c x y⟩

lemma SpherePacking.rescale_occupied_region {S : SpherePacking d} {c : ℝ} (hc : 0 < c) :
    (S.rescaleConfiguration hc).occupiedBallRegion = c • S.occupiedBallRegion := by
  ext x
  simp [SpherePacking.occupiedBallRegion, SpherePacking.rescaleConfiguration,
    Set.smul_set_iUnion, Set.mem_smul_set, _root_.smul_ball hc.ne', Real.norm_eq_abs,
    abs_of_pos hc, mul_div_assoc]

end Scaling

noncomputable section Density

variable {d : ℕ} (S : SpherePacking d)

/-- The periodic packing constant of `ℝ ^ d`: the supremum of the densities of all periodic
sphere packings. -/
def PeriodicSpherePackingConstant (d : ℕ) : ℝ≥0∞ :=
  ⨆ S : PeriodicSpherePacking d, S.upperPackingDensity

end Density

section DensityLemmas
namespace SpherePacking

lemma upper_packing_density_le_one {d : ℕ} (S : SpherePacking d) : S.upperPackingDensity ≤ 1 := by
  refine limsup_le_iSup.trans <| iSup_le fun R ↦ ?_
  simpa [densityInsideRadius] using
    ENNReal.div_le_of_le_mul (by simpa using volume.mono Set.inter_subset_right)

@[simp] lemma rescale_densityInsideRadius {d : ℕ} (S : SpherePacking d) {c : ℝ} (hc : 0 < c)
    (R : ℝ) :
    (S.rescaleConfiguration hc).densityInsideRadius R = S.densityInsideRadius (R / c) := by
  have hball : ball (0 : EuclideanSpace ℝ (Fin d)) R = c • ball 0 (R / c) := by
    rw [smul_ball hc.ne' 0 (R / c)]
    simp [abs_of_pos hc, mul_div_cancel₀ _ hc.ne']
  rw [densityInsideRadius, rescale_occupied_region, hball, ← Set.smul_set_inter₀ hc.ne',
    Measure.addHaar_smul_of_nonneg _ hc.le, Measure.addHaar_smul_of_nonneg _ hc.le,
    ENNReal.mul_div_mul_left, densityInsideRadius]
  · rw [ne_eq, ENNReal.ofReal_eq_zero, not_le, finrank_euclideanSpace_fin]
    positivity
  · exact ENNReal.ofReal_ne_top

lemma rescale_upper_packing_density {d : ℕ} (S : SpherePacking d) {c : ℝ} (hc : 0 < c) :
    (S.rescaleConfiguration hc).upperPackingDensity = S.upperPackingDensity := by
  simpa [upperPackingDensity, Function.comp, map_div_atTop_eq c hc] using
    (limsup_congr (Eventually.of_forall fun R ↦ rescale_densityInsideRadius S hc R)).trans
      (Filter.limsup_comp (u := S.densityInsideRadius) (v := fun R ↦ R / c) (f := atTop))

/-- Rescaling reduces the packing constant to packings of separation `1`. -/
theorem packing_supremum_eq_unit_separation {d : ℕ} : SpherePackingConstant d =
    ⨆ (S : SpherePacking d) (_ : S.separation = 1), S.upperPackingDensity := by
  rw [iSup_subtype', SpherePackingConstant]
  refine le_antisymm (iSup_le fun S ↦ ?_) (iSup_le fun S ↦ le_iSup upperPackingDensity S.1)
  simpa [rescale_upper_packing_density] using
    le_iSup (fun S : { S : SpherePacking d // S.separation = 1 } ↦ S.val.upperPackingDensity)
      ⟨S.rescaleConfiguration (inv_pos.mpr S.separation_pos),
        inv_mul_cancel₀ S.separation_pos.ne'⟩

end DensityLemmas.SpherePacking
section BasicResults
open scoped ENNReal
open EuclideanSpace

variable {d : ℕ} (S : SpherePacking d)

lemma biUnion_ball_subset_inter_ball (X : Set (EuclideanSpace ℝ (Fin d))) (r R : ℝ) :
    ⋃ x ∈ X ∩ ball 0 R, ball x r ⊆ (⋃ x ∈ X, ball x r) ∩ ball 0 (R + r) := by
  intro x hx
  simp only [Set.mem_inter_iff, Set.mem_iUnion, mem_ball, exists_prop, dist_zero_right] at hx ⊢
  obtain ⟨y, ⟨hy₁, hy₂⟩⟩ := hx
  exact ⟨⟨y, hy₁.1, hy₂⟩, lt_of_le_of_lt (norm_le_norm_add_norm_sub' x y) (by gcongr <;> tauto)⟩

lemma inter_ball_subset_biUnion_ball (X : Set (EuclideanSpace ℝ (Fin d))) (r R : ℝ) :
    (⋃ x ∈ X, ball x r) ∩ ball 0 (R - r) ⊆ ⋃ x ∈ X ∩ ball 0 R, ball x r := by
  intro x hx
  simp only [Set.mem_inter_iff, Set.mem_iUnion, mem_ball, exists_prop, dist_zero_right] at hx ⊢
  obtain ⟨⟨y, ⟨hy₁, hy₂⟩⟩, hx⟩ := hx
  refine ⟨y, ⟨hy₁, ?_⟩, hy₂⟩
  refine lt_of_le_of_lt (norm_le_norm_add_norm_sub x y) ?_
  rw [← sub_add_cancel R r]
  exact add_lt_add hx (by simpa [dist_eq_norm, norm_sub_rev] using hy₂)

/-- The balls of radius `r' ≤ separation / 2` around the centers inside `ball 0 R` are disjoint,
so the volume of their union is the sum of their volumes. -/
theorem SpherePacking.volume_center_ball_union_eq_tsum
    (R : ℝ) {r' : ℝ} (hr' : r' ≤ S.separation / 2) :
    volume (⋃ x : ↑(S.centers ∩ ball 0 R), ball (x : EuclideanSpace ℝ (Fin d)) r')
      = ∑' x : ↑(S.centers ∩ ball 0 R), volume (ball (x : EuclideanSpace ℝ (Fin d)) r') := by
  have : Countable ↑(S.centers ∩ ball 0 R) :=
    Set.Countable.mono Set.inter_subset_left (countable_of_Lindelof_of_discrete (X := S.centers))
  refine measure_iUnion ?_ fun _ ↦ measurableSet_ball
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  apply ball_disjoint_ball
  simp_rw [ne_eq, Subtype.mk.injEq] at h ⊢
  linarith [S.distinct_centers_separation_bound x y hx.1 hy.1 h]

theorem SpherePacking.center_count_in_ball_upper_bound (hd : 0 < d) (R : ℝ) :
    (S.centers ∩ ball 0 R).encard ≤ volume (S.occupiedBallRegion ∩ ball 0 (R + S.separation / 2))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2)) := by
  have h := volume.mono <| biUnion_ball_subset_inter_ball S.centers (S.separation / 2) R
  change volume _ ≤ volume _ at h
  simp_rw [Set.biUnion_eq_iUnion, S.volume_center_ball_union_eq_tsum R le_rfl,
    Measure.addHaar_ball_center, ENNReal.tsum_set_const] at h
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rwa [← ENNReal.le_div_iff_mul_le] at h <;> left
  · exact (euclidean_ball_volume_positive _ (by linarith [S.separation_pos])).ne'
  · exact measure_ball_lt_top.ne

theorem SpherePacking.center_count_in_ball_lower_bound (R : ℝ) : (S.centers ∩ ball 0 R).encard ≥
      volume (S.occupiedBallRegion ∩ ball 0 (R - S.separation / 2))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2)) := by
  have h := volume.mono <| inter_ball_subset_biUnion_ball S.centers (S.separation / 2) R
  change volume _ ≤ volume _ at h
  simp_rw [Set.biUnion_eq_iUnion, S.volume_center_ball_union_eq_tsum _ le_rfl,
    Measure.addHaar_ball_center, ENNReal.tsum_set_const] at h
  exact ENNReal.div_le_of_le_mul h

theorem SpherePacking.finite_centers_inside_ball (R : ℝ) : Finite ↑(S.centers ∩ ball 0 R) := by
  apply Set.encard_lt_top_iff.mp
  rcases eq_or_ne d 0 with rfl | hd
  · exact Set.encard_lt_top_iff.2 <| Set.Finite.of_subsingleton (S.centers ∩ ball 0 R)
  have hd' : 0 < d := Nat.pos_of_ne_zero hd
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd'
  refine ENat.toENNReal_lt.mp <| lt_of_le_of_lt (S.center_count_in_ball_upper_bound hd' R) ?_
  exact ENNReal.div_lt_top (lt_of_le_of_lt (volume.mono Set.inter_subset_right)
      measure_ball_lt_top).ne
    (euclidean_ball_volume_positive _ (by linarith [S.separation_pos])).ne'

theorem SpherePacking.local_density_lower_bound (hd : 0 < d) (R : ℝ) : S.densityInsideRadius R
      ≥ (S.centers ∩ ball 0 (R - S.separation / 2)).encard
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [densityInsideRadius, occupiedBallRegion]
  refine ENNReal.div_le_div_right ((ENNReal.le_div_iff_mul_le
    (Or.inl (euclidean_ball_volume_positive _ (by linarith [S.separation_pos])).ne')
    (Or.inl measure_ball_lt_top.ne)).1 ?_) _
  simpa [sub_add_cancel] using S.center_count_in_ball_upper_bound hd (R - S.separation / 2)

theorem SpherePacking.local_density_upper_bound (hd : 0 < d) (R : ℝ) : S.densityInsideRadius R
      ≤ (S.centers ∩ ball 0 (R + S.separation / 2)).encard
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [densityInsideRadius, occupiedBallRegion]
  refine ENNReal.div_le_div_right ((ENNReal.div_le_iff_le_mul
    (Or.inl (euclidean_ball_volume_positive _ (by linarith [S.separation_pos])).ne')
    (Or.inl measure_ball_lt_top.ne)).1 ?_) _
  simpa [add_sub_cancel_right] using S.center_count_in_ball_lower_bound (R + S.separation / 2)

end BasicResults

end

end
