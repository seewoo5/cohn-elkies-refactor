import CohnElkies.SpherePacking.Basic
import CohnElkiesForMathlib.Topology.Algebra.InfiniteSum.ENat

/-!
# Periodic sphere packings: counting centers and the density formula

Let `S` be a periodic packing in `ℝ ^ d` with lattice `Λ`.  A bounded region contains only
finitely many centers, the centers inside a fundamental domain of `Λ` are in bijection with the
`Λ`-orbits of centers (there are `S.centerOrbitCardinality` of them), and the density of `S` is
`centerOrbitCardinality * vol (ball (separation / 2)) / covol Λ`.  As a consequence the periodic
packing constant is already attained by packings of separation `1`.
-/

section
open scoped Real
open Complex (I)

section

variable {d : ℕ}

namespace ZLattice

/-- A `ℤ`-basis of a full-rank lattice of `ℝ ^ d` is indexed by a type equivalent to `Fin d`. -/
noncomputable def coordinateIndexEquiv (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] :
    (Module.Free.ChooseBasisIndex ℤ Λ) ≃ (Fin d) :=
  Fintype.equivFinOfCardEq <| by
    rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ Λ, finrank_euclideanSpace_fin]

end ZLattice

end

section

open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module

section aux_lemmas

variable {d : ℕ} (S : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))

/-- A bounded region meets the centers of a sphere packing in a finite set: the balls of radius
`separation / 2` around those centers are disjoint, have equal positive volume, and lie in a
bounded set. -/
lemma finite_centers_in_bounded_region (hD_isBounded : IsBounded D) (hd : 0 < d) :
    Finite ↑(S.centers ∩ D) := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hD_isBounded
  have hbdd : IsBounded
      (⋃ x : ↑(S.centers ∩ D), ball (x : EuclideanSpace ℝ (Fin d)) (S.separation / 2)) := by
    refine isBounded_iff_forall_norm_le.2 ⟨M + S.separation / 2, fun y hy ↦ ?_⟩
    obtain ⟨x, hx⟩ := Set.mem_iUnion.1 hy
    exact (norm_le_norm_add_norm_sub' y x).trans (add_le_add (hM _ x.2.2)
      (by simpa [dist_eq_norm] using (mem_ball.1 hx).le))
  have hdisj : Pairwise (Function.onFun Disjoint fun x : ↑(S.centers ∩ D) ↦
      ball (x : EuclideanSpace ℝ (Fin d)) (S.separation / 2)) := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    refine ball_disjoint_ball ?_
    simpa [add_halves] using S.distinct_centers_separation_bound x y hx.1 hy.1
      (by simpa [Subtype.ext_iff] using hxy)
  simpa [Measure.addHaar_ball_center, Set.finite_univ_iff] using
    Measure.finite_const_le_meas_of_disjoint_iUnion volume
      (As := fun x : ↑(S.centers ∩ D) ↦ ball (x : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
      (euclidean_ball_volume_positive (0 : EuclideanSpace ℝ (Fin d)) (half_pos S.separation_pos))
      (fun _ ↦ measurableSet_ball) hdisj hbdd.measure_lt_top.ne

end aux_lemmas

section Pointwise

open scoped Pointwise

variable {d : ℕ}

/-- If the `Λ`-translates of `D` cover each point of the space exactly once, then two distinct
translates of `D` are disjoint. -/
lemma translates_disjoint_of_unique_cover {Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))}
    {D : Set (EuclideanSpace ℝ (Fin d))}
    (hD_unique_covers : ∀ x, ∃! g : Λ, g +ᵥ x ∈ D) {g h : Λ} (hgh : g ≠ h) :
    Disjoint (g +ᵥ D) (h +ᵥ D) :=
  Set.disjoint_left.2 fun x hxg hxh ↦ hgh <| neg_injective <| (hD_unique_covers x).unique
    (by simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using hxg)
    (by simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using hxh)

end Pointwise

section instances
variable {d : ℕ} (S : PeriodicSpherePacking d)
open scoped Pointwise

/-- The fundamental domain of a `ℤ`-basis of the lattice of `S` is a fundamental domain for the
action of the lattice: every point has a unique lattice translate inside it. -/
theorem PeriodicSpherePacking.exists_unique_vadd_mem_fundamentalDomain {ι : Type*} [Finite ι]
    (b : Basis ι ℤ S.lattice) (x : EuclideanSpace ℝ (Fin d)) :
    ∃! g : S.lattice, g +ᵥ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _) := by
  obtain ⟨g, hg, huniq⟩ := exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x
  refine ⟨⟨g, (S.mem_integral_basis_span_iff b g).mp g.property⟩, hg, ?_⟩
  rintro ⟨h, hh⟩ hmem
  have hv : h = (g : EuclideanSpace ℝ (Fin d)) :=
    congrArg Subtype.val (huniq ⟨h, (S.mem_integral_basis_span_iff b h).mpr hh⟩ hmem)
  exact Subtype.ext hv

/-- Version of `PeriodicSpherePacking.exists_unique_vadd_mem_fundamentalDomain` for a translate
of the fundamental domain. -/
theorem PeriodicSpherePacking.exists_unique_vadd_mem_vadd_fundamentalDomain {ι : Type*} [Finite ι]
    (b : Basis ι ℤ S.lattice) (v x : EuclideanSpace ℝ (Fin d)) :
    ∃! g : S.lattice, g +ᵥ x ∈ v +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _) := by
  have key (g : S.lattice) : g +ᵥ x ∈ v +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _) ↔
      g +ᵥ (-v + x) ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _) := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simp [Submodule.vadd_def, vadd_eq_add, ← add_assoc, add_comm]
  simpa only [key] using S.exists_unique_vadd_mem_fundamentalDomain b (-v + x)

/-- If the lattice translates of `D` cover each point exactly once, the `Λ`-orbits of centers are
in bijection with the centers lying in `D`. -/
noncomputable def PeriodicSpherePacking.centerOrbitEquivFundamentalRegion
    (D : Set (EuclideanSpace ℝ (Fin d))) (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) :
    Quotient S.latticeCenterTranslationAction.orbitRel ≃ ↑(S.centers ∩ D) := by
  classical
  have h_vadd (g : S.lattice) (x : S.centers) :
      ((g +ᵥ x : S.centers) : EuclideanSpace ℝ (Fin d)) = (g : EuclideanSpace ℝ (Fin d)) + x := rfl
  refine (Equiv.ofBijective
    (fun x : ↑(S.centers ∩ D) ↦ Quotient.mk _ (⟨x.1, x.2.1⟩ : S.centers)) ⟨?_, ?_⟩).symm
  · intro x y hxy
    obtain ⟨g, hg⟩ := Quotient.exact hxy
    have hco : (g : EuclideanSpace ℝ (Fin d)) + y.1 = x.1 := by
      simpa only [h_vadd] using congrArg Subtype.val hg
    have hgD : (g : EuclideanSpace ℝ (Fin d)) + y.1 ∈ D := hco.symm ▸ x.2.2
    have hgzero : g = 0 := (hD_unique_covers y.1).unique hgD (by simpa using y.2.2)
    exact Subtype.ext (by simpa [hgzero] using hco.symm)
  · intro q
    refine Quotient.inductionOn q fun x ↦ ?_
    obtain ⟨g, hg, -⟩ := hD_unique_covers (x : EuclideanSpace ℝ (Fin d))
    exact ⟨⟨(g +ᵥ x : S.centers), (g +ᵥ x : S.centers).2, (h_vadd g x).symm ▸ hg⟩,
      Quotient.sound ⟨g, Subtype.ext rfl⟩⟩

noncomputable instance PeriodicSpherePacking.finiteCenterTranslationQuotient :
    Finite (Quotient S.latticeCenterTranslationAction.orbitRel) := by
  by_cases hd : 0 < d
  · let b : Basis _ ℤ S.lattice := (ZLattice.module_free ℝ S.lattice).chooseBasis
    have : Finite ↑(S.centers ∩ fundamentalDomain (b.ofZLatticeBasis ℝ _)) :=
      finite_centers_in_bounded_region S _ (fundamentalDomain_isBounded _) hd
    exact Finite.of_equiv _ (S.centerOrbitEquivFundamentalRegion _
      (S.exists_unique_vadd_mem_fundamentalDomain b)).symm
  · obtain rfl : d = 0 := Nat.eq_zero_of_not_pos hd
    exact Quotient.finite (AddAction.orbitRel ..)

noncomputable instance : Fintype (Quotient S.latticeCenterTranslationAction.orbitRel) :=
  Fintype.ofFinite _

end instances

section centerOrbitCardinality

open scoped Pointwise

open Finset Set

variable {d : ℕ} (S : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))

/-- The number of orbits of the lattice of `S` acting on the centers of `S`. -/
noncomputable def PeriodicSpherePacking.centerOrbitCardinality : ℕ :=
  Fintype.card (Quotient S.latticeCenterTranslationAction.orbitRel)

theorem PeriodicSpherePacking.card_centers_in_fundamental_region (hD_isBounded : IsBounded D)
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D)
    (hd : 0 < d) :
    haveI := @Fintype.ofFinite _ <| finite_centers_in_bounded_region S D hD_isBounded hd
    (S.centers ∩ D).toFinset.card = S.centerOrbitCardinality := by
  rw [centerOrbitCardinality]
  convert Finset.card_eq_of_equiv_fintype ?_
  simpa [Set.mem_toFinset] using! (S.centerOrbitEquivFundamentalRegion D hD_unique_covers).symm

theorem PeriodicSpherePacking.encard_centers_in_fundamental_region (hD_isBounded : IsBounded D)
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D)
    (hd : 0 < d) :
    (S.centers ∩ D).encard = S.centerOrbitCardinality := by
  rw [← S.card_centers_in_fundamental_region D hD_isBounded hD_unique_covers hd]
  convert Set.encard_eq_coe_toFinset_card _

theorem PeriodicSpherePacking.encard_centers_in_translated_region (hd : 0 < d)
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) (v : EuclideanSpace ℝ (Fin d)) :
    (S.centers ∩ (v +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _))).encard =
      S.centerOrbitCardinality :=
  S.encard_centers_in_fundamental_region _ ((fundamentalDomain_isBounded _).vadd v)
    (S.exists_unique_vadd_mem_vadd_fundamentalDomain b v) hd

end centerOrbitCardinality

section numReps_aux

variable {d : ℕ}

/-- The `Fintype` structure on the centers of `S` inside a bounded region. -/
@[reducible] noncomputable def PeriodicSpherePacking.instFintypeBoundedCenterRepresentatives
    (S : PeriodicSpherePacking d) (hd : 0 < d)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D) :
    Fintype ↑(S.centers ∩ D) :=
  @Fintype.ofFinite _ <| finite_centers_in_bounded_region S D hD_isBounded hd

/-- The number of centers of `S` inside a bounded region `D`. -/
noncomputable def PeriodicSpherePacking.boundedCenterRepresentativeCount
    (S : PeriodicSpherePacking d) (hd : 0 < d)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D) : ℕ :=
  letI := S.instFintypeBoundedCenterRepresentatives hd hD_isBounded
  Fintype.card ↑(S.centers ∩ D)

theorem PeriodicSpherePacking.orbit_cardinality_eq_bounded_representatives
    (S : PeriodicSpherePacking d) (hd : 0 < d)
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD_isBounded : IsBounded D)
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) :
    S.centerOrbitCardinality = S.boundedCenterRepresentativeCount hd hD_isBounded := by
  simpa [PeriodicSpherePacking.boundedCenterRepresentativeCount, Set.toFinset_card] using
    (S.card_centers_in_fundamental_region (D := D) hD_isBounded hD_unique_covers hd).symm

end numReps_aux

section theorem_2_3

variable {d : ℕ} (S : PeriodicSpherePacking d) (D : Set (EuclideanSpace ℝ (Fin d)))

open scoped Pointwise

private theorem iUnion_vadd_fundamentalDomain_subset_ball
    {ι : Type*} (b : Basis ι ℝ (EuclideanSpace ℝ (Fin d)))
    {L : ℝ} (hL : ∀ x ∈ fundamentalDomain b, ‖x‖ ≤ L) (R : ℝ) :
    ⋃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R - L),
      x +ᵥ (fundamentalDomain b : Set (EuclideanSpace ℝ (Fin d))) ⊆ ball 0 R := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ : ∃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R - L),
      ∃ y ∈ fundamentalDomain b, x + y = z := by
    simpa [Set.mem_vadd_set, eq_comm] using hz
  have hxnorm : ‖x‖ < R - L := by simpa [mem_ball, dist_zero_right] using hx.2
  simpa [mem_ball, dist_zero_right] using
    lt_of_le_of_lt (norm_add_le x y) (by linarith [hL y hy])

private theorem fundamental_region_translates_disjoint
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice)
    {x y : EuclideanSpace ℝ (Fin d)} (hx : x ∈ S.lattice) (hy : y ∈ S.lattice) (hxy : x ≠ y) :
    Disjoint (x +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _))
      (y +ᵥ fundamentalDomain (b.ofZLatticeBasis ℝ _)) := by
  simpa [Submodule.vadd_def] using translates_disjoint_of_unique_cover (Λ := S.lattice)
    (D := fundamentalDomain (b.ofZLatticeBasis ℝ _))
    (S.exists_unique_vadd_mem_fundamentalDomain b) (g := ⟨x, hx⟩) (h := ⟨y, hy⟩)
    (fun h ↦ hxy (congrArg Subtype.val h))

private theorem centers_inter_translates_pairwiseDisjoint {ι : Type*} [Finite ι]
    (b : Basis ι ℤ S.lattice) (T : Set (EuclideanSpace ℝ (Fin d))) :
    Set.PairwiseDisjoint Set.univ fun x : ↑((S.lattice : Set (EuclideanSpace ℝ (Fin d))) ∩ T) ↦
      S.centers ∩ ((x : EuclideanSpace ℝ (Fin d)) +ᵥ
        fundamentalDomain (b.ofZLatticeBasis ℝ _)) := by
  rintro ⟨x, hx⟩ - ⟨y, hy⟩ - hxy
  exact Set.disjoint_left.2 fun u hux huy ↦ Set.disjoint_left.1
    (fundamental_region_translates_disjoint S b hx.1 hy.1 fun h ↦ hxy (Subtype.ext h))
    hux.2 huy.2

theorem PeriodicSpherePacking.nsmul_encard_lattice_le_encard_centers
    (hd : 0 < d) {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice)
    {L : ℝ} (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (R : ℝ) :
    (↑S.centers ∩ ball 0 R).encard ≥ S.centerOrbitCardinality •
      (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R - L)).encard := by
  have hsub := Set.inter_subset_inter_right S.centers
    (iUnion_vadd_fundamentalDomain_subset_ball
      S (b.ofZLatticeBasis ℝ _) hL R)
  rw [Set.biUnion_eq_iUnion, Set.inter_iUnion] at hsub
  have henc := Set.encard_mono hsub
  rw [Set.encard_disjoint_union_eq_tsum (centers_inter_translates_pairwiseDisjoint S b _)] at henc
  simp_rw [S.encard_centers_in_translated_region hd] at henc
  convert! henc.ge
  rw [nsmul_eq_mul, ENat.tsum_subtype_const, mul_comm]

private theorem ball_subset_iUnion_vadd_fundamentalDomain
    {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice)
    {L : ℝ} (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (R : ℝ) :
    ball 0 R ⊆ ⋃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + L),
        x +ᵥ (fundamentalDomain (b.ofZLatticeBasis ℝ _) : Set (EuclideanSpace ℝ (Fin d))) := by
  have : Fintype ι := Fintype.ofFinite ι
  intro x hx
  refine Set.mem_iUnion₂.2 ⟨floor (b.ofZLatticeBasis ℝ _) x, ⟨?_, ?_⟩, ?_⟩
  · rw [SetLike.mem_coe, ← S.mem_integral_basis_span_iff b]
    exact Submodule.coe_mem _
  · rw [mem_ball_zero_iff] at hx ⊢
    have hfloor : ‖floor (b.ofZLatticeBasis ℝ _) x‖ = ‖x - fract (b.ofZLatticeBasis ℝ _) x‖ := by
      simp [fract]
    refine lt_of_le_of_lt (hfloor.le.trans (norm_sub_le _ _)) ?_
    exact add_lt_add_of_lt_of_le hx (hL _ (fract_mem_fundamentalDomain _ _))
  · rw [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub]
    exact fract_mem_fundamentalDomain (b.ofZLatticeBasis ℝ _) x

theorem PeriodicSpherePacking.encard_centers_le_nsmul_encard_lattice
    (hd : 0 < d) {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice)
    {L : ℝ} (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (R : ℝ) :
    (↑S.centers ∩ ball 0 R).encard ≤ S.centerOrbitCardinality •
      (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + L)).encard := by
  have hsub := Set.inter_subset_inter_right S.centers
    (ball_subset_iUnion_vadd_fundamentalDomain S b hL R)
  rw [Set.biUnion_eq_iUnion, Set.inter_iUnion] at hsub
  have henc := Set.encard_mono hsub
  rw [Set.encard_disjoint_union_eq_tsum (centers_inter_translates_pairwiseDisjoint S b _)] at henc
  simp_rw [S.encard_centers_in_translated_region hd] at henc
  convert! henc
  rw [nsmul_eq_mul, ENat.tsum_subtype_const, mul_comm]

end theorem_2_3

section theorem_2_2

open scoped Pointwise
variable {d : ℕ} (S : PeriodicSpherePacking d)
  {ι : Type*} [Finite ι]
  (D : Set (EuclideanSpace ℝ (Fin d))) {L : ℝ} (R : ℝ)

theorem isAddFundamentalDomain_of_unique_cover
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D) :
    IsAddFundamentalDomain S.lattice D :=
  MeasureTheory.IsAddFundamentalDomain.mk' (μ := volume) hD_measurable.nullMeasurableSet
    hD_unique_covers

private theorem ball_subset_iUnion_vadd
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hL : ∀ x ∈ D, ‖x‖ ≤ L) :
    ball 0 (R - L) ⊆ ⋃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R, (x +ᵥ D) := by
  intro x hx
  have hx' : ‖x‖ < R - L := by simpa [mem_ball_zero_iff] using hx
  obtain ⟨g, hg, -⟩ := hD_unique_covers x
  have hg' : (g : EuclideanSpace ℝ (Fin d)) + x ∈ D := by simpa [Submodule.vadd_def] using hg
  simp_rw [Set.mem_iUnion, exists_prop, Set.mem_inter_iff]
  refine ⟨-g.val, ⟨by simp, ?_⟩,
    (Set.mem_vadd_set_iff_neg_vadd_mem).2 (by simpa [Submodule.vadd_def] using hg)⟩
  have htri : ‖g.val‖ ≤ ‖g.val + x‖ + ‖x‖ := by
    simpa [sub_eq_add_neg, add_assoc] using norm_sub_le (a := g.val + x) (b := x)
  rw [mem_ball_zero_iff, norm_neg]
  linarith [hL _ hg']

instance (E : Type*) [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd E] [Module ℤ E]
    [Module ℝ E] (μ : Measure E) [μ.IsAddLeftInvariant] [IsScalarTower ℤ ℝ E] (s : Submodule ℤ E) :
    VAddInvariantMeasure s E μ where
  measure_preimage_vadd c t ht := by
    simp only [Submodule.vadd_def, vadd_eq_add, measure_preimage_add]

theorem PeriodicSpherePacking.volume_div_le_encard_lattice
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D)
    (hL : ∀ x ∈ D, ‖x‖ ≤ L) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≥ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - L)) / volume D := by
  have hcover := volume.mono (ball_subset_iUnion_vadd (S := S) (D := D) (R := R)
      hD_unique_covers hL)
  rw [Set.biUnion_eq_iUnion] at hcover
  have : Countable ↑((S.lattice : Set (EuclideanSpace ℝ (Fin d))) ∩ ball 0 R) :=
    Set.Countable.mono Set.inter_subset_left (countable_of_Lindelof_of_discrete (X := S.lattice))
  refine ENNReal.div_le_of_le_mul (hcover.trans ?_)
  calc
    volume (⋃ x : ↑((S.lattice : Set (EuclideanSpace ℝ (Fin d))) ∩ ball 0 R),
      (x : EuclideanSpace ℝ (Fin d)) +ᵥ D)
      ≤ ∑' x : ↑((S.lattice : Set (EuclideanSpace ℝ (Fin d))) ∩ ball 0 R),
        volume ((x : EuclideanSpace ℝ (Fin d)) +ᵥ D) := measure_iUnion_le _
    _ = ∑' _ : ↑((S.lattice : Set (EuclideanSpace ℝ (Fin d))) ∩ ball 0 R),
      volume D := by simp_rw [measure_vadd]
    _ = _ := ENNReal.tsum_set_const _ _

private theorem iUnion_vadd_subset_ball (hL : ∀ x ∈ D, ‖x‖ ≤ L) :
    ⋃ x ∈ ↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R, (x +ᵥ D) ⊆ ball 0 (R + L) := by
  intro x hx
  rw [mem_ball_zero_iff]
  obtain ⟨i, ⟨-, hi_ball⟩, hi_mem⟩ :=
    (by simpa [Set.mem_iUnion, exists_prop, Set.mem_inter_iff] using hx)
  have hi_ball' : ‖i‖ < R := by simpa [mem_ball_zero_iff] using hi_ball
  have hi_mem' : ‖-i + x‖ ≤ L := hL _ (Set.mem_vadd_set_iff_neg_vadd_mem.mp hi_mem)
  calc
    _ = ‖i + (-i + x)‖ := by congr; abel
    _ ≤ ‖i‖ + ‖-i + x‖ := norm_add_le _ _
    _ < R + L := add_lt_add_of_lt_of_le hi_ball' hi_mem'

theorem PeriodicSpherePacking.encard_lattice_le_volume_div
    (hD_unique_covers : ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ D) (hD_measurable : MeasurableSet D)
    (hL : ∀ x ∈ D, ‖x‖ ≤ L) (hd : 0 < d) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≤ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + L)) / volume D := by
  classical
  let T : Set (EuclideanSpace ℝ (Fin d)) := ↑S.lattice ∩ ball 0 R
  have : Countable T := Set.Countable.mono Set.inter_subset_left
      (countable_of_Lindelof_of_discrete (X := S.lattice))
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hfinite : volume D ≠ ⊤ := ((Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin d)))
    (r := L)).subset fun x hx ↦ by
      simpa [Metric.mem_closedBall, dist_zero_right] using hL x hx).measure_lt_top.ne
  have hnonzero : volume D ≠ 0 :=
    (isAddFundamentalDomain_of_unique_cover S D hD_unique_covers hD_measurable).measure_ne_zero
      fun hv ↦ by
        have hp := euclidean_ball_volume_positive (0 : EuclideanSpace ℝ (Fin d)) one_pos
        simp [hv] at hp
  refine (ENNReal.le_div_iff_mul_le (Or.inl hnonzero) (Or.inl hfinite)).2 ?_
  calc
    (T.encard : ℝ≥0∞) * volume D = ∑' x : T, volume ((x : EuclideanSpace ℝ (Fin d)) +ᵥ D) := by
      simp_rw [measure_vadd]
      exact (ENNReal.tsum_set_const T (volume D)).symm
    _ = volume (⋃ x : T, (x : EuclideanSpace ℝ (Fin d)) +ᵥ D) := by
      refine (measure_iUnion (fun x y hxy ↦ ?_) fun x ↦ hD_measurable.const_vadd _).symm
      refine translates_disjoint_of_unique_cover (Λ := S.lattice) (D := D) hD_unique_covers
        (g := ⟨x, x.property.1⟩) (h := ⟨y, y.property.1⟩) fun hg ↦ hxy ?_
      exact Subtype.ext (congrArg (fun z : S.lattice ↦ (z : EuclideanSpace ℝ (Fin d))) hg)
    _ ≤ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + L)) := volume.mono (by
      simpa [T, Set.biUnion_eq_iUnion] using
        iUnion_vadd_subset_ball (S := S) (D := D) (R := R) hL)

open ZSpan

variable (b : Basis ι ℤ S.lattice)

theorem PeriodicSpherePacking.volume_div_le_encard_lattice_fundamentalDomain
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≥ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - L))
        / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)) :=
  S.volume_div_le_encard_lattice _ R
    (S.exists_unique_vadd_mem_fundamentalDomain b) hL

theorem PeriodicSpherePacking.encard_lattice_le_volume_div_fundamentalDomain
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) R).encard
      ≤ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + L))
        / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)) :=
  S.encard_lattice_le_volume_div _ R
    (S.exists_unique_vadd_mem_fundamentalDomain b) (fundamentalDomain_measurableSet _) hL hd

section finiteDensity_limit

open MeasureTheory Measure Metric ZSpan

variable
  {d : ℕ} {S : PeriodicSpherePacking d}
  {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) {L : ℝ} (R : ℝ)

theorem densityInsideRadius_le_mul_ratio
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    S.densityInsideRadius R ≤ S.centerOrbitCardinality
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _))
            * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + S.separation / 2 + L * 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)) := calc
  _ ≤ (S.centers ∩ ball 0 (R + S.separation / 2)).encard
      * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) :=
    S.local_density_upper_bound hd R
  _ ≤ S.centerOrbitCardinality
        • (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d)) (R + S.separation / 2 + L)).encard
          * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
            / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
    gcongr
    simpa using ENat.toENNReal_le.mpr
      (S.encard_centers_le_nsmul_encard_lattice hd b hL _)
  _ ≤ S.centerOrbitCardinality
        * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + S.separation / 2 + L + L))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)))
            * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
    rw [nsmul_eq_mul]
    gcongr
    exact S.encard_lattice_le_volume_div_fundamentalDomain _ b hL hd
  _ = S.centerOrbitCardinality * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _))
            * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + S.separation / 2 + L * 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)) := by
    rw [← mul_div_assoc, ← mul_div_assoc, mul_two, ← add_assoc, ← ENNReal.mul_div_right_comm,
      ← ENNReal.mul_div_right_comm, mul_assoc, mul_assoc]
    congr 3
    rw [mul_comm]

theorem densityInsideRadius_ge_mul_ratio
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    S.densityInsideRadius R ≥ S.centerOrbitCardinality
        * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
          / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _))
            * (volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R - S.separation / 2 - L * 2))
              / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)) := calc
  _ ≥ (S.centers ∩ ball 0 (R - S.separation / 2)).encard
      * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
        / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) :=
    S.local_density_lower_bound hd R
  _ ≥ S.centerOrbitCardinality • (↑S.lattice ∩ ball (0 : EuclideanSpace ℝ (Fin d))
        (R - S.separation / 2 - L)).encard
          * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
            / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
    gcongr
    simpa using ENat.toENNReal_le.mpr
      (S.nsmul_encard_lattice_le_encard_centers
        hd b hL (R - S.separation / 2))
  _ ≥ S.centerOrbitCardinality * (volume (ball (0 : EuclideanSpace ℝ (Fin d))
        (R - S.separation / 2 - L - L)) / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)))
          * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
            / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R) := by
    rw [nsmul_eq_mul]
    gcongr
    exact S.volume_div_le_encard_lattice_fundamentalDomain _ b hL
  _ = _ := by
    rw [show R - S.separation / 2 - L - L = R - S.separation / 2 - L * 2 by ring]
    simp only [div_eq_mul_inv]
    ac_rfl

open Filter Topology

section VolumeBallRatio

open scoped Topology NNReal
open Asymptotics Filter ENNReal EuclideanSpace

/-- The volumes of two balls whose radii differ by a constant are asymptotically equal. -/
theorem volume_ball_add_div_volume_ball_add_tendsto_one {d : ℕ} {C C' : ℝ} (hd : 0 < d) :
    Tendsto (fun R ↦ volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C))
      / volume (ball (0 : EuclideanSpace ℝ (Fin d)) (R + C'))) atTop (𝓝 1) := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hratio : Tendsto (fun R : ℝ ↦ (R + C) / (R + C')) atTop (𝓝 1) := by
    have herror : Tendsto (fun R : ℝ ↦ (C - C') / (R + C')) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ C' tendsto_id)).const_mul
          (C - C')
    have hsum : Tendsto (fun R : ℝ ↦ 1 + (C - C') / (R + C')) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add herror
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop (-C')] with R hR
    have hden : R + C' ≠ 0 := ne_of_gt (by linarith)
    field_simp
    ring
  have henn : Tendsto (fun R : ℝ ↦ ENNReal.ofReal (((R + C) / (R + C')) ^ d)) atTop (𝓝 1) := by
    simpa using tendsto_ofReal (hratio.pow d)
  have hV₀ : volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ 0 :=
    (euclidean_ball_volume_positive 0 one_pos).ne'
  have hV : volume (ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ⊤ := measure_ball_lt_top.ne
  refine henn.congr' ?_
  filter_upwards [eventually_gt_atTop (max (-C) (-C'))] with R hR
  have hC : 0 < R + C := by linarith [(le_max_left (-C) (-C')).trans_lt hR]
  have hC' : 0 < R + C' := by linarith [(le_max_right (-C) (-C')).trans_lt hR]
  rw [Measure.addHaar_ball _ _ hC.le, Measure.addHaar_ball _ _ hC'.le, finrank_euclideanSpace_fin,
    ENNReal.mul_div_mul_right _ _ hV₀ hV, ← ENNReal.ofReal_div_of_pos (pow_pos hC' d), div_pow]

end VolumeBallRatio
end finiteDensity_limit
end theorem_2_2

end

section

open scoped ENNReal
open SpherePacking EuclideanSpace MeasureTheory Metric ZSpan Bornology Module
open Filter
open scoped Pointwise
open scoped Topology

variable {d : ℕ}

section DensityEqFdDensity

variable
  {d : ℕ} {S : PeriodicSpherePacking d}
  {ι : Type*} [Finite ι] (b : Basis ι ℤ S.lattice) {L : ℝ} (R : ℝ)

lemma PeriodicSpherePacking.tendsto_densityInsideRadius
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    Tendsto S.densityInsideRadius atTop
      (𝓝 (S.centerOrbitCardinality * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
        / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)))) := by
  have hone (a : ℝ≥0∞) : 𝓝 a = 𝓝 (a * 1) := by rw [mul_one]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ ?_
      (densityInsideRadius_ge_mul_ratio b · hL hd)
      (densityInsideRadius_le_mul_ratio b · hL hd)
  · rw [hone]
    refine ENNReal.Tendsto.const_mul ?_ (Or.inl one_ne_zero)
    simp_rw [sub_sub, sub_eq_add_neg]
    convert volume_ball_add_div_volume_ball_add_tendsto_one hd (C := -(S.separation / 2 + L * 2))
    rw [add_zero]
  · rw [hone]
    refine ENNReal.Tendsto.const_mul ?_ (Or.inl one_ne_zero)
    simp_rw [add_assoc]
    convert volume_ball_add_div_volume_ball_add_tendsto_one hd (C := S.separation / 2 + L * 2)
    rw [add_zero]

/-- The density of a periodic packing equals the number of centers in a fundamental domain times
the volume of a ball of radius `separation / 2`, divided by the covolume of the lattice. -/
theorem PeriodicSpherePacking.upperPackingDensity_eq_div_volume_fundamentalDomain
    (hL : ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L) (hd : 0 < d) :
    S.upperPackingDensity
      = S.centerOrbitCardinality * volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2))
        / volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)) :=
  limsSup_eq_of_le_nhds (S.tendsto_densityInsideRadius b hL hd)

end DensityEqFdDensity

section ConstantEqNormalizedConstant

/-- Rescaling reduces the periodic packing constant to packings of separation `1`. -/
theorem periodic_packing_supremum_eq_unit_separation :
    PeriodicSpherePackingConstant d = ⨆ (S : PeriodicSpherePacking d) (_ : S.separation = 1),
    S.upperPackingDensity := by
  rw [iSup_subtype', PeriodicSpherePackingConstant]
  refine le_antisymm (iSup_le fun S ↦ ?_)
    (iSup_le fun S ↦ le_iSup (fun S : PeriodicSpherePacking d ↦ S.upperPackingDensity) S.1)
  rw [← rescale_upper_packing_density S.toSpherePacking (inv_pos.mpr S.separation_pos)]
  exact le_iSup (fun x : { x : PeriodicSpherePacking d // x.separation = 1 } ↦
      x.val.upperPackingDensity)
    ⟨S.rescaleConfiguration (inv_pos.mpr S.separation_pos),
      inv_mul_cancel₀ S.separation_pos.ne'⟩

end ConstantEqNormalizedConstant

section Fundamental_Domains_in_terms_of_Basis

open Submodule

variable (S : PeriodicSpherePacking d) (b : Basis (Fin d) ℤ S.lattice)

theorem PeriodicSpherePacking.fundamental_region_admits_norm_bound :
    ∃ L : ℝ, ∀ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _), ‖x‖ ≤ L :=
  isBounded_iff_forall_norm_le.1 (fundamentalDomain_isBounded (Basis.ofZLatticeBasis ℝ S.lattice b))

theorem PeriodicSpherePacking.basis_region_translates_cover_uniquely :
    ∀ x, ∃! g : S.lattice, g +ᵥ x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ _) :=
  S.exists_unique_vadd_mem_fundamentalDomain b

end Fundamental_Domains_in_terms_of_Basis

section Periodic_Density_Formula

/-- The index type of the chosen `ℤ`-basis of the lattice of a periodic packing in `ℝ ^ d` is
equivalent to `Fin d`. -/
noncomputable def PeriodicSpherePacking.coordinateIndexEquiv
    (P : PeriodicSpherePacking d) : (Module.Free.ChooseBasisIndex ℤ ↥P.lattice) ≃ (Fin d) :=
  ZLattice.coordinateIndexEquiv P.lattice

/-- A `ℤ`-basis of the lattice of a periodic packing in `ℝ ^ d`, indexed by `Fin d`. -/
noncomputable def PeriodicSpherePacking.canonicalPackingLatticeBasis (S : PeriodicSpherePacking d) :
    Basis (Fin d) ℤ ↥S.lattice :=
  ((ZLattice.module_free ℝ S.lattice).chooseBasis).reindex S.coordinateIndexEquiv

@[simp] theorem PeriodicSpherePacking.density_eq_numReps_mul_volume_ball_div_covolume
    (S : PeriodicSpherePacking d) (hd : 0 < d) : S.upperPackingDensity =
    (ENat.toENNReal (S.centerOrbitCardinality : ENat)) *
    volume (ball (0 : EuclideanSpace ℝ (Fin d)) (S.separation / 2)) /
    Real.toNNReal (ZLattice.covolume S.lattice) := by
  obtain ⟨L, hL⟩ := S.fundamental_region_admits_norm_bound S.canonicalPackingLatticeBasis
  set b := S.canonicalPackingLatticeBasis with hb
  rw [S.upperPackingDensity_eq_div_volume_fundamentalDomain b hL hd]
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hfinite : volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)) ≠ ⊤ :=
    (fundamentalDomain_isBounded (b.ofZLatticeBasis ℝ _)).measure_lt_top.ne
  have hfund : IsAddFundamentalDomain S.lattice (fundamentalDomain (b.ofZLatticeBasis ℝ _)) :=
    isAddFundamentalDomain_of_unique_cover S _
      (S.basis_region_translates_cover_uniquely b) (fundamentalDomain_measurableSet _)
  rw [ZLattice.covolume_eq_measure_fundamentalDomain S.lattice volume hfund,
    show (↑(Real.toNNReal (volume.real (fundamentalDomain (b.ofZLatticeBasis ℝ _)))) : ℝ≥0∞)
      = volume (fundamentalDomain (b.ofZLatticeBasis ℝ _)) from ENNReal.ofReal_toReal hfinite]
  norm_num

end Periodic_Density_Formula

section Empty_Centers

/-- A periodic packing without centers has density zero. -/
theorem PeriodicSpherePacking.packing_density_zero_of_empty_centers (S : PeriodicSpherePacking d)
    (hd : 0 < d) [instEmpty : IsEmpty S.centers] : S.upperPackingDensity = 0 := by
  rw [S.density_eq_numReps_mul_volume_ball_div_covolume hd]
  set b := S.canonicalPackingLatticeBasis with hb
  set D := fundamentalDomain (Basis.ofZLatticeBasis ℝ S.lattice b) with hD
  have hD_isBounded : IsBounded D := fundamentalDomain_isBounded _
  rw [← S.card_centers_in_fundamental_region D hD_isBounded
    (S.basis_region_translates_cover_uniquely b) hd]
  simp only [Set.toFinset_card, ENat.toENNReal_coe, ENNReal.div_eq_zero_iff, mul_eq_zero,
    Nat.cast_eq_zero, ENNReal.coe_ne_top, or_false]
  have := @Fintype.ofFinite _ <| finite_centers_in_bounded_region S D hD_isBounded hd
  have : IsEmpty (↥(S.centers ∩ D)) := ⟨fun x ↦ instEmpty.false ⟨x.1, x.2.1⟩⟩
  simp

end Empty_Centers

end

end
