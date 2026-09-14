import CohnElkies.Radialization

/-!
# Radial reduction of the Cohn–Elkies program (report §2.1)

The rotational average `ℛf(x) = ∫_{O(d)} f(U⁻¹x) dU` of an admissible function `f ∈ 𝒜_d`
(report (2)) is a radial admissible function, `Admissible.radialize : Admissible d →
RadialAdmissible d`: averaging over `O(d)` preserves realness, the sign of `𝓕 f`, the values
`f(0)` and `𝓕f(0)` (`radialize_apply_zero`, `fourier_radialize_apply_zero`), hence the quotient
`f(0)/𝓕f(0)` (`quotient_radialize`), and nonpositivity outside a ball of any radius
(`radialize_nonpos_of_le_norm`). Consequently the infimum defining `LP_d` (report (3)) is
unchanged when `𝒜_d` is replaced by `𝒜_d^rad` (`quotientSet_eq_radial`, `LP_eq_radial`), and so
is the normalized program (`normalizedProgram_eq_radial`).
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open MeasureTheory
open scoped FourierTransform SchwartzMap

/-- The rotational average `ℛf = ∫_{O(d)} f(U⁻¹ ·) dU` of an admissible function, as a radial
admissible function (report §2.1): rotational averaging preserves every sign condition of (2). -/
def Admissible.radialize {d : ℕ} (f : Admissible d) : RadialAdmissible d :=
  have hreal : IsRealValued (rotationalAverageSchwartz f.function) := fun x ↦ by
    rw [rotationalAverageSchwartz_apply]
    exact rotationalAverage_im_eq_zero f.real x
  have hradial : IsRadial (rotationalAverageSchwartz f.function) := fun x y hxy ↦ by
    simp only [rotationalAverageSchwartz_apply]
    exact rotationalAverage_eq_of_norm_eq _ _ _ hxy
  { function := rotationalAverageSchwartz f.function
    real := hreal
    radial := hradial
    fourier_real := hreal.fourier_of_radial hradial
    fourier_nonneg := fun ξ ↦ by
      rw [fourier_rotationalAverageSchwartz, rotationalAverageSchwartz_apply]
      exact rotationalAverage_nonneg_of_nonneg
        (𝓕 f.function : TestFunction d).continuous f.fourier_nonneg ξ
    fourier_zero_pos := by
      rw [fourier_rotationalAverageSchwartz, rotationalAverageSchwartz_apply,
        rotationalAverage_zero]
      exact f.fourier_zero_pos
    outside_nonpos := fun x hx ↦ by
      rw [rotationalAverageSchwartz_apply]
      exact rotationalAverage_nonpos_of_le_norm f.function.continuous f.outside_nonpos hx }

theorem Admissible.radialize_function {d : ℕ} (f : Admissible d) :
    f.radialize.function = rotationalAverageSchwartz f.function :=
  rfl

/-- `ℛf(x) = ∫_{O(d)} f(U⁻¹x) dU`, for the Haar probability measure of `O(d)`. -/
theorem Admissible.radialize_apply {d : ℕ} (f : Admissible d) (x : Euclidean d) :
    f.radialize.function x =
      ∫ U : OrthogonalGroup d, f.function (orthogonalAction U⁻¹ x) ∂radialOrthogonalHaar d :=
  rfl

/-- `ℛf(0) = f(0)`. -/
theorem Admissible.radialize_apply_zero {d : ℕ} (f : Admissible d) :
    f.radialize.function 0 = f.function 0 := by
  rw [Admissible.radialize_function, rotationalAverageSchwartz_apply, rotationalAverage_zero]

/-- `𝓕(ℛf)(0) = 𝓕f(0)`. -/
theorem Admissible.fourier_radialize_apply_zero {d : ℕ} (f : Admissible d) :
    (𝓕 f.radialize.function : TestFunction d) 0 = (𝓕 f.function : TestFunction d) 0 := by
  rw [Admissible.radialize_function, fourier_rotationalAverageSchwartz,
    rotationalAverageSchwartz_apply, rotationalAverage_zero]

/-- Radialization preserves the quotient `f(0)/𝓕f(0)` (report §2.1). -/
theorem Admissible.quotient_radialize {d : ℕ} (f : Admissible d) :
    quotient f.radialize.toAdmissible = quotient f := by
  change (f.radialize.function 0).re / ((𝓕 f.radialize.function : TestFunction d) 0).re = _
  rw [Admissible.radialize_apply_zero, Admissible.fourier_radialize_apply_zero]
  rfl

/-- Radialization preserves the normalized cost `(f(0)/𝓕f(0))^{1/d}/√d` (report (31)). -/
theorem Admissible.normalizedCost_radialize {d : ℕ} (f : Admissible d) :
    normalizedCost f.radialize.toAdmissible = normalizedCost f := by
  unfold normalizedCost
  rw [Admissible.quotient_radialize]

/-- "With smaller radius": nonpositivity outside the ball of any radius `R` is preserved by
radialization, since exterior regions are rotation invariant (report §2.1). -/
theorem Admissible.radialize_nonpos_of_le_norm {d : ℕ} (f : Admissible d) {R : ℝ}
    (h : ∀ x : Euclidean d, R ≤ ‖x‖ → (f.function x).re ≤ 0) :
    ∀ x : Euclidean d, R ≤ ‖x‖ → (f.radialize.function x).re ≤ 0 := fun x hx ↦ by
  rw [Admissible.radialize_function, rotationalAverageSchwartz_apply]
  exact rotationalAverage_nonpos_of_le_norm f.function.continuous h hx

/-- A quantity invariant under radialization has the same range on `𝒜_d^rad` as on `𝒜_d`. -/
theorem range_radialAdmissible_eq {d : ℕ} {α : Type*} (φ : Admissible d → α)
    (hφ : ∀ f : Admissible d, φ f.radialize.toAdmissible = φ f) :
    Set.range (fun f : RadialAdmissible d ↦ φ f.toAdmissible) = Set.range φ :=
  Set.Subset.antisymm (Set.range_comp_subset_range RadialAdmissible.toAdmissible φ)
    (Set.range_subset_iff.2 fun f ↦ ⟨f.radialize, hφ f⟩)

/-- The quotients `f(0)/𝓕f(0)` of `𝒜_d` are those of `𝒜_d^rad` (report §2.1). -/
theorem quotientSet_eq_radial (d : ℕ) :
    quotientSet d = Set.range fun f : RadialAdmissible d ↦ quotient f.toAdmissible :=
  (range_radialAdmissible_eq quotient Admissible.quotient_radialize).symm

/-- Radial reduction of the Cohn–Elkies program (report §2.1): the infimum in (3) is unchanged
when `𝒜_d` is replaced by `𝒜_d^rad`. -/
theorem LP_eq_radial (d : ℕ) : LP d = unitBallVolume d / 2 ^ d *
    sInf (Set.range fun f : RadialAdmissible d ↦ quotient f.toAdmissible) :=
  congrArg (unitBallVolume d / 2 ^ d * sInf ·) (quotientSet_eq_radial d)

/-- Radial reduction of the normalized program `inf_{f ∈ 𝒜_d} (f(0)/𝓕f(0))^{1/d}/√d`. -/
theorem normalizedProgram_eq_radial (d : ℕ) : normalizedProgram d =
    sInf (Set.range fun f : RadialAdmissible d ↦ normalizedCost f.toAdmissible) :=
  congrArg sInf (range_radialAdmissible_eq normalizedCost Admissible.normalizedCost_radialize).symm

end

end CohnElkies
