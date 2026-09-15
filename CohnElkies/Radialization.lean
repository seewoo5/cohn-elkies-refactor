import CohnElkies.Basic
import CohnElkies.SchwartzTools

/-!
# Rotational averaging over the orthogonal group (report §2.1)

The orthogonal group `O(d)` with its Haar probability measure and its tautological action on `ℝ^d`
by linear isometries (transitive on spheres), and the **rotational average**
`ℛg(x) = ∫_{O(d)} g(U⁻¹ x) dU` of a function `g : ℝ^d → E`.

The `U⁻¹` of the report is what makes `ℛ` an action-compatible averaging operator, and only the
*left* invariance of the Haar measure is used below. The function `x ↦ ∫_{O(d)} g(Ux) dU` is the
same, by inversion invariance of the Haar measure of a compact group; Mathlib proves inversion
invariance only for abelian groups (`IsHaarMeasure.isInvInvariant_of_regular`), so the two forms
are not identified here.

`ℛg` is rotation invariant, hence radial (`rotationalAverage_eq_of_norm_eq`); it satisfies
`ℛg(0) = g(0)`, preserves real values and the sign of the real part, in particular outside a ball
of any radius; and for continuous integrable `g` it is continuous
(`continuous_rotationalAverage`) and integrable (`integrable_rotationalAverage`) with
`‖ℛg‖₁ ≤ ‖g‖₁` (`integral_norm_rotationalAverage_le`) and `𝓕(ℛg) = ℛ(𝓕g)`
(`fourier_rotationalAverage`).

The last section packages the rotational average of a *test* function as a test function
(`rotationalAverageSchwartz`), through differentiation under the integral sign for a uniformly
dominated family of Schwartz functions (`schwartzAverage`). The radial reduction of the
Cohn–Elkies program is in `CohnElkies.Admissible.Radialization`, the sign-uncertainty application
in `CohnElkies.SignUncertainty.Radialization`.
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Matrix MeasureTheory Set

/-! ### The orthogonal group `O(d)`, its action on `ℝ^d` and its Haar probability measure -/

/-- The orthogonal group `O(d)`, as a subgroup of `d × d` real matrices. -/
abbrev OrthogonalGroup (d : ℕ) := Matrix.orthogonalGroup (Fin d) ℝ

theorem orthogonal_isCompact (d : ℕ) : IsCompact (Matrix.orthogonalGroup (Fin d) ℝ :
      Set (Matrix (Fin d) (Fin d) ℝ)) := by
  refine ((isCompact_Icc (a := (-1 : ℝ)) (b := (1 : ℝ))).matrix).of_isClosed_subset
    isClosed_unitary fun A hA ↦ ?_
  change ∀ i j, A i j ∈ Set.Icc (-1 : ℝ) 1
  intro i j
  have hsum : (∑ k : Fin d, A i k * A i k) = (1 : ℝ) := by
    simpa [Matrix.mul_apply] using congrArg (fun B : Matrix (Fin d) (Fin d) ℝ ↦ B i i)
      ((Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).mp hA)
  refine abs_le.mp (abs_le_one_iff_mul_self_le_one.2 ?_)
  exact (Finset.single_le_sum (fun k _ ↦ mul_self_nonneg (A i k)) (Finset.mem_univ j)).trans_eq hsum

instance orthogonalGroupCompactSpace (d : ℕ) : CompactSpace (OrthogonalGroup d) :=
  isCompact_iff_compactSpace.mp (orthogonal_isCompact d)

instance orthogonalGroupMeasurableSpace (d : ℕ) : MeasurableSpace (OrthogonalGroup d) :=
  borel (OrthogonalGroup d)

instance orthogonalGroupBorelSpace (d : ℕ) : BorelSpace (OrthogonalGroup d) := ⟨rfl⟩

/-- The tautological action of `O(d)` on `ℝ^d`. -/
def orthogonalAction {d : ℕ} (U : OrthogonalGroup d) (x : Euclidean d) : Euclidean d :=
  Matrix.toLpLin 2 2 (U : Matrix (Fin d) (Fin d) ℝ) x

@[simp] theorem orthogonalAction_one {d : ℕ} (x : Euclidean d) :
    orthogonalAction (1 : OrthogonalGroup d) x = x := by
  change Matrix.toLpLin 2 2 (1 : Matrix (Fin d) (Fin d) ℝ) x = x
  rw [Matrix.toLpLin_one]
  rfl

@[simp] theorem orthogonalAction_mul {d : ℕ} (U V : OrthogonalGroup d) (x : Euclidean d) :
    orthogonalAction (U * V) x = orthogonalAction U (orthogonalAction V x) := by
  change Matrix.toLpLin 2 2 ((U : Matrix (Fin d) (Fin d) ℝ) * (V : Matrix (Fin d) (Fin d) ℝ)) x =
      Matrix.toLpLin 2 2 (U : Matrix (Fin d) (Fin d) ℝ)
        (Matrix.toLpLin 2 2 (V : Matrix (Fin d) (Fin d) ℝ) x)
  rw [Matrix.toLpLin_mul_same]
  rfl

@[simp] theorem orthogonalAction_zero {d : ℕ} (U : OrthogonalGroup d) :
    orthogonalAction U (0 : Euclidean d) = 0 :=
  map_zero (Matrix.toLpLin 2 2 (U : Matrix (Fin d) (Fin d) ℝ))

/-- Each `U ∈ O(d)` acts as a linear isometry of `ℝ^d`. -/
def orthogonalLinearIsometry {d : ℕ} (U : OrthogonalGroup d) : Euclidean d ≃ₗᵢ[ℝ] Euclidean d :=
  (Unitary.mapEquiv (StarMulEquiv.ofClass
    (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)))).toMulEquiv.trans Unitary.linearIsometryEquiv U

@[simp] theorem orthogonalLinearIsometry_apply {d : ℕ} (U : OrthogonalGroup d) (x : Euclidean d) :
    orthogonalLinearIsometry U x = orthogonalAction U x := rfl

@[simp] theorem norm_orthogonalAction {d : ℕ} (U : OrthogonalGroup d) (x : Euclidean d) :
    ‖orthogonalAction U x‖ = ‖x‖ := (orthogonalLinearIsometry U).norm_map x

theorem continuous_orthogonalAction {d : ℕ} (x : Euclidean d) :
    Continuous fun U : OrthogonalGroup d ↦ orthogonalAction U x := by
  change Continuous fun U : OrthogonalGroup d ↦
    WithLp.toLp 2 ((U : Matrix (Fin d) (Fin d) ℝ) *ᵥ WithLp.ofLp x)
  exact (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous.comp
    (continuous_subtype_val.matrix_mulVec continuous_const)

theorem orthogonalAction_joint_continuous (d : ℕ) :
    Continuous fun p : OrthogonalGroup d × Euclidean d ↦ orthogonalAction p.1 p.2 := by
  change Continuous fun p : OrthogonalGroup d × Euclidean d ↦
    WithLp.toLp 2 ((p.1 : Matrix (Fin d) (Fin d) ℝ) *ᵥ WithLp.ofLp p.2)
  exact (PiLp.continuous_toLp 2 fun _ : Fin d ↦ ℝ).comp
    ((continuous_subtype_val.comp continuous_fst).matrix_mulVec
      ((PiLp.continuous_ofLp 2 fun _ : Fin d ↦ ℝ).comp continuous_snd))

/-- The element of `O(d)` represented by a linear isometry of `ℝ^d`. -/
def orthogonalMatrixOfIsometry {d : ℕ} (A : Euclidean d ≃ₗᵢ[ℝ] Euclidean d) : OrthogonalGroup d :=
  ⟨A.toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin d) ℝ).toBasis,
    A.toMatrix_mem_unitaryGroup (EuclideanSpace.basisFun (Fin d) ℝ)
      (EuclideanSpace.basisFun (Fin d) ℝ)⟩

@[simp] theorem orthogonalMatrixOfIsometry_action {d : ℕ}
    (A : Euclidean d ≃ₗᵢ[ℝ] Euclidean d) (x : Euclidean d) :
    orthogonalAction (orthogonalMatrixOfIsometry A) x = A x := by
  change (Matrix.toLpLin 2 2) ((LinearMap.toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)
      A.toLinearEquiv.toLinearMap) x = A x
  rw [Matrix.toLpLin_eq_toLin]
  change (Matrix.toLin (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)
      ((LinearMap.toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)
        A.toLinearEquiv.toLinearMap) x = A x
  rw [Matrix.toLin_toMatrix]
  rfl

/-- `O(d)` acts transitively on each sphere. -/
theorem orthogonal_transitive {d : ℕ} {x y : Euclidean d} (hxy : ‖x‖ = ‖y‖) :
    ∃ U : OrthogonalGroup d, orthogonalAction U x = y :=
  ⟨orthogonalMatrixOfIsometry (Submodule.reflection (ℝ ∙ (x - y))ᗮ), by
    rw [orthogonalMatrixOfIsometry_action]
    exact Submodule.reflection_sub hxy⟩

/-- `O(d)` itself, as a positive compact subset of `O(d)`. -/
def orthogonalPositiveCompacts (d : ℕ) : TopologicalSpace.PositiveCompacts (OrthogonalGroup d) :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

/-- The Haar probability measure of `O(d)`, used to average over rotations. -/
def radialOrthogonalHaar (d : ℕ) : Measure (OrthogonalGroup d) :=
  Measure.haarMeasure (orthogonalPositiveCompacts d)

@[simp] theorem radialOrthogonalHaar_univ (d : ℕ) : radialOrthogonalHaar d Set.univ = 1 := by
  simpa [radialOrthogonalHaar, orthogonalPositiveCompacts] using
    (Measure.haarMeasure_self (K₀ := orthogonalPositiveCompacts d))

instance radialOrthogonalHaar_probability (d : ℕ) : IsProbabilityMeasure (radialOrthogonalHaar d) :=
  ⟨radialOrthogonalHaar_univ d⟩

instance radialOrthogonalHaar_isHaar (d : ℕ) : (radialOrthogonalHaar d).IsHaarMeasure := by
  unfold radialOrthogonalHaar
  infer_instance

end

noncomputable section

open Filter MeasureTheory Set
open scoped FourierTransform RealInnerProductSpace Topology

variable {d : ℕ}

/-! ### Rotations of a function on `ℝ^d` -/

section Rotations

variable {E : Type*} [NormedAddCommGroup E]

theorem continuous_comp_orthogonalAction_inv {g : Euclidean d → E} (hg : Continuous g) :
    Continuous fun p : OrthogonalGroup d × Euclidean d ↦ g (orthogonalAction p.1⁻¹ p.2) := by
  have heq : (fun p : OrthogonalGroup d × Euclidean d ↦ g (orthogonalAction p.1⁻¹ p.2)) =
      g ∘ (fun p : OrthogonalGroup d × Euclidean d ↦ orthogonalAction p.1 p.2) ∘
        fun p : OrthogonalGroup d × Euclidean d ↦ (p.1⁻¹, p.2) := by
    funext p
    simp only [Function.comp_apply]
  rw [heq]
  exact hg.comp ((orthogonalAction_joint_continuous d).comp
    ((continuous_inv.comp continuous_fst).prodMk continuous_snd))

theorem integrable_comp_orthogonalAction {g : Euclidean d → E} (hg : Integrable g)
    (U : OrthogonalGroup d) : Integrable fun x ↦ g (orthogonalAction U x) :=
  ((orthogonalLinearIsometry U).measurePreserving.integrable_comp_emb
    (orthogonalLinearIsometry U).toHomeomorph.measurableEmbedding).2 hg

theorem integral_norm_comp_orthogonalAction (g : Euclidean d → E) (U : OrthogonalGroup d) :
    ∫ x, ‖g (orthogonalAction U x)‖ = ∫ x, ‖g x‖ :=
  (orthogonalLinearIsometry U).measurePreserving.integral_comp
    (orthogonalLinearIsometry U).toHomeomorph.measurableEmbedding fun x ↦ ‖g x‖

/-- On the compact group `O(d)`, the rotations of a continuous function are integrable. -/
theorem integrable_comp_orthogonalAction_inv {g : Euclidean d → E} (hg : Continuous g)
    (x : Euclidean d) :
    Integrable (fun U : OrthogonalGroup d ↦ g (orthogonalAction U⁻¹ x))
      (radialOrthogonalHaar d) := by
  have hcont : Continuous fun U : OrthogonalGroup d ↦ g (orthogonalAction U⁻¹ x) :=
    hg.comp ((continuous_orthogonalAction x).comp continuous_inv)
  simpa using hcont.continuousOn.integrableOn_compact isCompact_univ

end Rotations

/-! ### The rotational average -/

section Average

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The rotational average `ℛg(x) = ∫_{O(d)} g(U⁻¹x) dU` of a function on `ℝ^d` (report §2.1),
with respect to the Haar probability measure of `O(d)`. -/
def rotationalAverage (g : Euclidean d → E) (x : Euclidean d) : E :=
  ∫ U : OrthogonalGroup d, g (orthogonalAction U⁻¹ x) ∂radialOrthogonalHaar d

theorem rotationalAverage_comp_orthogonal (g : Euclidean d → E) (A : OrthogonalGroup d)
    (x : Euclidean d) : rotationalAverage g (orthogonalAction A x) = rotationalAverage g x := by
  unfold rotationalAverage
  calc (∫ U : OrthogonalGroup d, g (orthogonalAction U⁻¹ (orthogonalAction A x))
          ∂radialOrthogonalHaar d)
      = ∫ U : OrthogonalGroup d, g (orthogonalAction (A * U)⁻¹ (orthogonalAction A x))
          ∂radialOrthogonalHaar d :=
        (integral_mul_left_eq_self (μ := radialOrthogonalHaar d) (fun U : OrthogonalGroup d ↦
          g (orthogonalAction U⁻¹ (orthogonalAction A x))) A).symm
    _ = ∫ U : OrthogonalGroup d, g (orthogonalAction U⁻¹ x) ∂radialOrthogonalHaar d := by
        refine integral_congr_ae (.of_forall fun U ↦ ?_)
        simp only [mul_inv_rev, orthogonalAction_mul]
        rw [← orthogonalAction_mul A⁻¹ A x]
        simp

/-- The rotational average is radial. -/
theorem rotationalAverage_eq_of_norm_eq (g : Euclidean d → E) :
    IsRadial (rotationalAverage g) := fun x y hxy ↦ by
  obtain ⟨A, rfl⟩ := orthogonal_transitive hxy
  exact (rotationalAverage_comp_orthogonal g A x).symm

theorem rotationalAverage_ofReal (g : Euclidean d → ℝ) (x : Euclidean d) :
    rotationalAverage (fun y ↦ (g y : ℂ)) x = ((rotationalAverage g x : ℝ) : ℂ) :=
  integral_complex_ofReal

/-- Rotational averaging preserves nonnegativity outside a ball (report §2.1: `r(ℛg) ≤ r(g)`). -/
theorem rotationalAverage_nonneg_of_norm_le {g : Euclidean d → ℝ} {R : ℝ}
    (hg : ∀ x : Euclidean d, R ≤ ‖x‖ → 0 ≤ g x) {x : Euclidean d} (hx : R ≤ ‖x‖) :
    0 ≤ rotationalAverage g x :=
  integral_nonneg fun U ↦ hg _ (by rwa [norm_orthogonalAction])

end Average

section Complete

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]

omit [SecondCountableTopology E] in
@[simp] theorem rotationalAverage_zero [CompleteSpace E] (g : Euclidean d → E) :
    rotationalAverage g 0 = g 0 := by
  simp [rotationalAverage, integral_const]

theorem continuous_rotationalAverage {g : Euclidean d → E} (hg : Continuous g) :
    Continuous (rotationalAverage g) := by
  have hunc : Continuous (Function.uncurry fun (x : Euclidean d) (U : OrthogonalGroup d) ↦
      g (orthogonalAction U⁻¹ x)) := by
    have heq : (Function.uncurry fun (x : Euclidean d) (U : OrthogonalGroup d) ↦
        g (orthogonalAction U⁻¹ x)) =
        (fun p : OrthogonalGroup d × Euclidean d ↦ g (orthogonalAction p.1⁻¹ p.2)) ∘
          Prod.swap := by
      funext p
      rfl
    rw [heq]
    exact (continuous_comp_orthogonalAction_inv hg).comp continuous_swap
  have h : rotationalAverage g = fun x ↦
      ∫ U in univ, g (orthogonalAction U⁻¹ x) ∂radialOrthogonalHaar d := by
    rw [Measure.restrict_univ]
    rfl
  rw [h]
  exact continuous_parametric_integral_of_continuous hunc isCompact_univ

omit [NormedSpace ℝ E] in
theorem integrable_prod_comp_orthogonalAction_inv {g : Euclidean d → E} (hg : Continuous g)
    (hi : Integrable g) :
    Integrable (fun p : OrthogonalGroup d × Euclidean d ↦ g (orthogonalAction p.1⁻¹ p.2))
      ((radialOrthogonalHaar d).prod volume) := by
  refine (integrable_prod_iff (continuous_comp_orthogonalAction_inv hg).aestronglyMeasurable).2
    ⟨.of_forall fun U ↦ integrable_comp_orthogonalAction hi U⁻¹, ?_⟩
  exact (integrable_const (∫ x, ‖g x‖)).congr
    (.of_forall fun U ↦ (integral_norm_comp_orthogonalAction g U⁻¹).symm)

theorem integrable_rotationalAverage {g : Euclidean d → E} (hg : Continuous g)
    (hi : Integrable g) : Integrable (rotationalAverage g) :=
  (integrable_prod_comp_orthogonalAction_inv hg hi).integral_prod_right

/-- `‖ℛg‖₁ ≤ ‖g‖₁`. -/
theorem integral_norm_rotationalAverage_le {g : Euclidean d → E} (hg : Continuous g)
    (hi : Integrable g) : ∫ x, ‖rotationalAverage g x‖ ≤ ∫ x, ‖g x‖ := by
  have hF := (integrable_prod_comp_orthogonalAction_inv hg hi).norm
  calc ∫ x, ‖rotationalAverage g x‖
      ≤ ∫ x, ∫ U : OrthogonalGroup d, ‖g (orthogonalAction U⁻¹ x)‖ ∂radialOrthogonalHaar d :=
        integral_mono_of_nonneg (.of_forall fun x ↦ norm_nonneg _) hF.integral_prod_right
          (.of_forall fun x ↦ norm_integral_le_integral_norm _)
    _ = ∫ U : OrthogonalGroup d, (∫ x, ‖g (orthogonalAction U⁻¹ x)‖) ∂radialOrthogonalHaar d :=
        (integral_integral_swap (f := fun U x ↦ ‖g (orthogonalAction U⁻¹ x)‖) hF).symm
    _ = ∫ U : OrthogonalGroup d, (∫ x, ‖g x‖) ∂radialOrthogonalHaar d :=
        integral_congr_ae (.of_forall fun U ↦ integral_norm_comp_orthogonalAction g U⁻¹)
    _ = ∫ x, ‖g x‖ := by simp

end Complete

/-! ### Real and imaginary parts, and signs -/

/-- The real part of the rotational average is the rotational average of the real part. -/
theorem rotationalAverage_re {g : Euclidean d → ℂ} (hg : Continuous g) (x : Euclidean d) :
    (rotationalAverage g x).re = rotationalAverage (fun y ↦ (g y).re) x :=
  (integral_re (integrable_comp_orthogonalAction_inv hg x)).symm

/-- Rotational averaging preserves real values. -/
theorem rotationalAverage_im_eq_zero {g : Euclidean d → ℂ} (hg : IsRealValued g) :
    IsRealValued (rotationalAverage g) := fun x ↦ by
  have h : (fun y ↦ (((g y).re : ℝ) : ℂ)) = g := funext fun y ↦ Complex.ext rfl (hg y).symm
  calc (rotationalAverage g x).im
      = (rotationalAverage (fun y ↦ (((g y).re : ℝ) : ℂ)) x).im := by rw [h]
    _ = 0 := by rw [rotationalAverage_ofReal]; exact Complex.ofReal_im _

theorem rotationalAverage_nonneg_of_nonneg {g : Euclidean d → ℂ} (hg : Continuous g)
    (h : ∀ y : Euclidean d, 0 ≤ (g y).re) (x : Euclidean d) : 0 ≤ (rotationalAverage g x).re := by
  rw [rotationalAverage_re hg]
  exact integral_nonneg fun U ↦ h _

/-- Nonpositivity outside the ball of any radius `R` is preserved by rotational averaging. -/
theorem rotationalAverage_nonpos_of_le_norm {g : Euclidean d → ℂ} (hg : Continuous g) {R : ℝ}
    (h : ∀ y : Euclidean d, R ≤ ‖y‖ → (g y).re ≤ 0) {x : Euclidean d} (hx : R ≤ ‖x‖) :
    (rotationalAverage g x).re ≤ 0 := by
  rw [rotationalAverage_re hg]
  exact integral_nonpos fun U ↦ h _ (by rwa [norm_orthogonalAction])

/-! ### The Fourier transform commutes with rotational averaging -/

/-- The Fourier character `x ↦ e^{-2πi⟪x, ξ⟫}`. -/
def fourierCharacter (ξ x : Euclidean d) : ℂ := Complex.exp (↑(-2 * π * ⟪x, ξ⟫) * I)

theorem continuous_fourierCharacter (ξ : Euclidean d) : Continuous (fourierCharacter ξ) := by
  unfold fourierCharacter
  fun_prop

@[simp] theorem norm_fourierCharacter (ξ x : Euclidean d) : ‖fourierCharacter ξ x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem integrable_fourierCharacter_mul {g : Euclidean d → ℂ} (hg : Integrable g)
    (ξ : Euclidean d) (U : OrthogonalGroup d) :
    Integrable fun x : Euclidean d ↦ fourierCharacter ξ x * g (orthogonalAction U x) :=
  (integrable_comp_orthogonalAction hg U).bdd_mul (c := (1 : ℝ))
    (continuous_fourierCharacter ξ).aestronglyMeasurable
    (.of_forall fun x ↦ (norm_fourierCharacter ξ x).le)

theorem integral_norm_fourierCharacter_mul (g : Euclidean d → ℂ) (ξ : Euclidean d)
    (U : OrthogonalGroup d) :
    ∫ x : Euclidean d, ‖fourierCharacter ξ x * g (orthogonalAction U x)‖ = ∫ x, ‖g x‖ := by
  simp only [norm_mul, norm_fourierCharacter, one_mul]
  exact integral_norm_comp_orthogonalAction g U

theorem integral_fourierCharacter_mul (g : Euclidean d → ℂ) (ξ : Euclidean d)
    (U : OrthogonalGroup d) :
    ∫ x : Euclidean d, fourierCharacter ξ x * g (orthogonalAction U x) =
      𝓕 g (orthogonalAction U ξ) := by
  change ∫ x : Euclidean d, fourierCharacter ξ x * g (orthogonalLinearIsometry U x) =
    𝓕 g (orthogonalLinearIsometry U ξ)
  rw [← Real.fourier_comp_linearIsometry, Real.fourier_eq']
  rfl

/-- The Fourier transform commutes with rotational averaging: `𝓕(ℛg) = ℛ(𝓕g)` (report §2.1). -/
theorem fourier_rotationalAverage {g : Euclidean d → ℂ} (hg : Continuous g) (hi : Integrable g)
    (ξ : Euclidean d) : 𝓕 (rotationalAverage g) ξ = rotationalAverage (𝓕 g) ξ := by
  have hkernel : Integrable (Function.uncurry fun (U : OrthogonalGroup d) (x : Euclidean d) ↦
        fourierCharacter ξ x * g (orthogonalAction U⁻¹ x))
      ((radialOrthogonalHaar d).prod volume) := by
    have hmeas : AEStronglyMeasurable (fun p : OrthogonalGroup d × Euclidean d ↦
          fourierCharacter ξ p.2 * g (orthogonalAction p.1⁻¹ p.2))
        ((radialOrthogonalHaar d).prod volume) :=
      (((continuous_fourierCharacter ξ).comp continuous_snd).mul
        (continuous_comp_orthogonalAction_inv hg)).aestronglyMeasurable
    refine (integrable_prod_iff hmeas).2 ⟨.of_forall fun U ↦
      integrable_fourierCharacter_mul hi ξ U⁻¹, ?_⟩
    exact (integrable_const (∫ x, ‖g x‖)).congr (.of_forall fun U ↦
      (integral_norm_fourierCharacter_mul g ξ U⁻¹).symm)
  calc 𝓕 (rotationalAverage g) ξ
      = ∫ x : Euclidean d, fourierCharacter ξ x * rotationalAverage g x := by
        rw [Real.fourier_eq']
        rfl
    _ = ∫ x : Euclidean d, ∫ U : OrthogonalGroup d,
          fourierCharacter ξ x * g (orthogonalAction U⁻¹ x) ∂radialOrthogonalHaar d := by
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        dsimp only
        unfold rotationalAverage
        rw [integral_const_mul]
    _ = ∫ U : OrthogonalGroup d, (∫ x : Euclidean d,
          fourierCharacter ξ x * g (orthogonalAction U⁻¹ x)) ∂radialOrthogonalHaar d :=
        (integral_integral_swap hkernel).symm
    _ = rotationalAverage (𝓕 g) ξ :=
        integral_congr_ae (.of_forall fun U ↦ integral_fourierCharacter_mul g ξ U⁻¹)

end

/-! ### The rotational average of a test function, as a test function -/

noncomputable section

open Filter MeasureTheory
open scoped ContDiff FourierTransform Topology

/-- Precomposition of a Schwartz function with a linear isometry of `ℝ^d`. -/
def compIsometry {d : ℕ} (U : Euclidean d ≃ₗᵢ[ℝ] Euclidean d) (f : TestFunction d) :
    TestFunction d :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ U.toContinuousLinearEquiv f

@[simp] theorem compIsometry_apply {d : ℕ} (U : Euclidean d ≃ₗᵢ[ℝ] Euclidean d) (f : TestFunction d)
    (x : Euclidean d) : compIsometry U f x = f (U x) := rfl

@[simp] theorem compIsometry_symm {d : ℕ} (U : Euclidean d ≃ₗᵢ[ℝ] Euclidean d)
    (f : TestFunction d) : compIsometry U.symm (compIsometry U f) = f := by
  ext x
  simp

theorem norm_iteratedFDeriv_compIsometry {d : ℕ} (U : Euclidean d ≃ₗᵢ[ℝ] Euclidean d)
    (f : TestFunction d) (n : ℕ) (x : Euclidean d) :
    ‖iteratedFDeriv ℝ n (compIsometry U f : Euclidean d → ℂ) x‖ =
      ‖iteratedFDeriv ℝ n (f : Euclidean d → ℂ) (U x)‖ := by
  change ‖iteratedFDeriv ℝ n ((f : Euclidean d → ℂ) ∘ (U : Euclidean d → Euclidean d)) x‖ = _
  exact U.norm_iteratedFDeriv_comp_right (f : Euclidean d → ℂ) x n

theorem iteratedFDeriv_compIsometry {d : ℕ} (U : Euclidean d ≃ₗᵢ[ℝ] Euclidean d)
    (f : TestFunction d) (n : ℕ) (x : Euclidean d) :
    iteratedFDeriv ℝ n (compIsometry U f : Euclidean d → ℂ) x =
      (iteratedFDeriv ℝ n (f : Euclidean d → ℂ) (U x)).compContinuousLinearMap
        fun _ ↦ U.toContinuousLinearMap := by
  change iteratedFDeriv ℝ n ((f : Euclidean d → ℂ) ∘ (U : Euclidean d → Euclidean d)) x = _
  exact U.toContinuousLinearMap.iteratedFDeriv_comp_right (f.smooth ⊤) x (mod_cast le_top)

theorem compIsometry_le_seminorm {d : ℕ} (U : Euclidean d ≃ₗᵢ[ℝ] Euclidean d) (f : TestFunction d)
    (k n : ℕ) (x : Euclidean d) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (compIsometry U f : Euclidean d → ℂ) x‖ ≤
      SchwartzMap.seminorm ℂ k n f := by
  rw [norm_iteratedFDeriv_compIsometry, ← U.norm_map x]
  exact SchwartzMap.le_seminorm ℂ k n f (U x)

theorem seminorm_compIsometry {d : ℕ} (U : Euclidean d ≃ₗᵢ[ℝ] Euclidean d) (f : TestFunction d)
    (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (compIsometry U f) = SchwartzMap.seminorm ℂ k n f := by
  have hle : ∀ (V : Euclidean d ≃ₗᵢ[ℝ] Euclidean d) (g : TestFunction d),
      SchwartzMap.seminorm ℂ k n (compIsometry V g) ≤ SchwartzMap.seminorm ℂ k n g := fun V g ↦
    SchwartzMap.seminorm_le_bound ℂ k n (compIsometry V g)
      (apply_nonneg (SchwartzMap.seminorm ℂ k n) g) (compIsometry_le_seminorm V g k n)
  refine le_antisymm (hle U f) ?_
  simpa using hle U.symm (compIsometry U f)

theorem continuous_orthogonalLinearIsometry_toCLM (d : ℕ) :
    Continuous fun U : OrthogonalGroup d ↦ (orthogonalLinearIsometry U).toContinuousLinearMap := by
  change Continuous fun U : OrthogonalGroup d ↦
    Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (U : Matrix (Fin d) (Fin d) ℝ)
  exact (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toLinearMap
    |>.continuous_of_finiteDimensional |>.comp continuous_subtype_val

theorem continuous_iteratedFDeriv_compIsometry {d : ℕ} (f : TestFunction d) (n : ℕ)
    (x : Euclidean d) :
    Continuous fun U : OrthogonalGroup d ↦
      iteratedFDeriv ℝ n (compIsometry (orthogonalLinearIsometry U) f : Euclidean d → ℂ) x := by
  have hderiv : Continuous fun U : OrthogonalGroup d ↦
      iteratedFDeriv ℝ n (f : Euclidean d → ℂ) (orthogonalAction U x) :=
    ((f.smooth ⊤).continuous_iteratedFDeriv (mod_cast le_top)).comp (continuous_orthogonalAction x)
  have hmaps : Continuous fun U : OrthogonalGroup d ↦
      fun _ : Fin n ↦ (orthogonalLinearIsometry U).toContinuousLinearMap :=
    continuous_pi fun _ ↦ continuous_orthogonalLinearIsometry_toCLM d
  have hcomp : Continuous fun p : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ Euclidean d) ℂ ×
      (Fin n → Euclidean d →L[ℝ] Euclidean d) ↦ p.1.compContinuousLinearMap p.2 :=
    continuous_iff_continuousAt.2 fun p ↦
      (ContinuousMultilinearMap.hasStrictFDerivAt_compContinuousLinearMap p).continuousAt
  simpa [Function.comp_def, iteratedFDeriv_compIsometry, orthogonalLinearIsometry_apply] using
    hcomp.comp (hderiv.prodMk hmaps)

/-- Measurability in `U ∈ O(d)` of the derivatives of the rotated Schwartz function. -/
theorem aestronglyMeasurable_iteratedFDeriv_compIsometry {d : ℕ} (f : TestFunction d) (n : ℕ)
    (x : Euclidean d) :
    AEStronglyMeasurable (fun U : OrthogonalGroup d ↦ iteratedFDeriv ℝ n
        (compIsometry (orthogonalLinearIsometry U⁻¹) f : Euclidean d → ℂ) x)
      (radialOrthogonalHaar d) :=
  ((continuous_iteratedFDeriv_compIsometry f n x).comp
    continuous_inv).aestronglyMeasurable_of_compactSpace

section ProbabilityAverage

variable {α : Type*} [MeasurableSpace α]
variable (μ : Measure α) [IsProbabilityMeasure μ]
variable {d : ℕ} (g : α → TestFunction d) (C : ℕ → ℕ → ℝ)

theorem integrable_iteratedFDeriv (hmeas : ∀ (n : ℕ) (x : Euclidean d),
      AEStronglyMeasurable (fun a : α ↦ iteratedFDeriv ℝ n (g a : Euclidean d → ℂ) x) μ)
    (hbound : ∀ (a : α) (k n : ℕ), SchwartzMap.seminorm ℂ k n (g a) ≤ C k n)
    (n : ℕ) (x : Euclidean d) :
    Integrable (fun a : α ↦ iteratedFDeriv ℝ n (g a : Euclidean d → ℂ) x) μ := by
  refine Integrable.of_bound (hmeas n x) (C 0 n) (.of_forall fun a ↦ ?_)
  exact (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ (g a) n x).trans (hbound a 0 n)

theorem hasFDerivAt_integral_iteratedFDeriv (hmeas : ∀ (n : ℕ) (x : Euclidean d),
      AEStronglyMeasurable (fun a : α ↦ iteratedFDeriv ℝ n (g a : Euclidean d → ℂ) x) μ)
    (hbound : ∀ (a : α) (k n : ℕ), SchwartzMap.seminorm ℂ k n (g a) ≤ C k n)
    (n : ℕ) (x : Euclidean d) :
    HasFDerivAt (fun y : Euclidean d ↦ ∫ a : α, iteratedFDeriv ℝ n (g a : Euclidean d → ℂ) y ∂μ)
      (∫ a : α, fderiv ℝ (iteratedFDeriv ℝ n (g a : Euclidean d → ℂ)) x ∂μ) x := by
  have hderiv_meas : AEStronglyMeasurable
      (fun a : α ↦ fderiv ℝ (iteratedFDeriv ℝ n (g a : Euclidean d → ℂ)) x) μ := by
    simpa only [fderiv_iteratedFDeriv, Function.comp_apply] using
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ Euclidean d)
        ℂ).continuous.comp_aestronglyMeasurable (hmeas (n + 1) x)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (F := fun y : Euclidean d ↦ fun a : α ↦ iteratedFDeriv ℝ n (g a : Euclidean d → ℂ) y)
    (F' := fun y : Euclidean d ↦ fun a : α ↦
      fderiv ℝ (iteratedFDeriv ℝ n (g a : Euclidean d → ℂ)) y)
    (bound := fun _ : α ↦ C 0 (n + 1)) (s := Set.univ) Filter.univ_mem
    (.of_forall fun y ↦ hmeas n y) (integrable_iteratedFDeriv μ g C hmeas hbound n x) hderiv_meas
    (.of_forall fun a y _ ↦ ?_) (integrable_const (C 0 (n + 1)))
  · filter_upwards with a y _
    exact (((g a).smooth ⊤).differentiable_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop (le_refl _) n)).differentiableAt.hasFDerivAt
  · calc ‖fderiv ℝ (iteratedFDeriv ℝ n (g a : Euclidean d → ℂ)) y‖
        = ‖iteratedFDeriv ℝ (n + 1) (g a : Euclidean d → ℂ) y‖ := norm_fderiv_iteratedFDeriv
      _ ≤ SchwartzMap.seminorm ℂ 0 (n + 1) (g a) :=
          SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ (g a) (n + 1) y
      _ ≤ C 0 (n + 1) := hbound a 0 (n + 1)

/-- Differentiation under the integral sign: iterated derivatives of a uniformly dominated
family of Schwartz functions commute with integration in the parameter. -/
theorem iteratedFDeriv_integral (hmeas : ∀ (n : ℕ) (x : Euclidean d),
      AEStronglyMeasurable (fun a : α ↦ iteratedFDeriv ℝ n (g a : Euclidean d → ℂ) x) μ)
    (hbound : ∀ (a : α) (k n : ℕ), SchwartzMap.seminorm ℂ k n (g a) ≤ C k n)
    (n : ℕ) (x : Euclidean d) :
    iteratedFDeriv ℝ n (fun y : Euclidean d ↦ ∫ a : α, (g a) y ∂μ) x =
      ∫ a : α, iteratedFDeriv ℝ n (g a : Euclidean d → ℂ) x ∂μ := by
  induction n generalizing x with
  | zero =>
      ext v
      rw [ContinuousMultilinearMap.integral_apply
        (integrable_iteratedFDeriv μ g C hmeas hbound 0 x)]
      simp
  | succ n ih =>
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply,
        show iteratedFDeriv ℝ n (fun y : Euclidean d ↦ ∫ a : α, (g a) y ∂μ) =
          fun y : Euclidean d ↦ ∫ a : α, iteratedFDeriv ℝ n (g a : Euclidean d → ℂ) y ∂μ from
          funext ih,
        (hasFDerivAt_integral_iteratedFDeriv μ g C hmeas hbound n x).fderiv]
      calc (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ Euclidean d) ℂ).symm
            (∫ a : α, fderiv ℝ (iteratedFDeriv ℝ n (g a : Euclidean d → ℂ)) x ∂μ)
          = ∫ a : α,
              (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ Euclidean d) ℂ).symm
                (fderiv ℝ (iteratedFDeriv ℝ n (g a : Euclidean d → ℂ)) x) ∂μ := by
            exact (LinearIsometry.integral_comp_comm (𝕜 := ℝ) (LinearIsometryEquiv.toLinearIsometry
                ((continuousMultilinearCurryLeftEquiv ℝ
                  (fun _ : Fin (n + 1) ↦ Euclidean d) ℂ).symm))
              fun a : α ↦ fderiv ℝ (iteratedFDeriv ℝ n (g a : Euclidean d → ℂ)) x).symm
        _ = ∫ a : α, iteratedFDeriv ℝ (n + 1) (g a : Euclidean d → ℂ) x ∂μ := by
            apply integral_congr_ae
            filter_upwards with a
            rw [iteratedFDeriv_succ_eq_comp_left]
            rfl

theorem pow_mul_norm_iteratedFDeriv_integral_le
    (hbound : ∀ (k n : ℕ) (a : α) (x : Euclidean d),
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y : Euclidean d ↦ g a y) x‖ ≤ C k n)
    (hderiv : ∀ (n : ℕ) (x : Euclidean d),
        iteratedFDeriv ℝ n (fun y : Euclidean d ↦ ∫ a, g a y ∂μ) x =
          ∫ a, iteratedFDeriv ℝ n (fun y : Euclidean d ↦ g a y) x ∂μ)
    (k n : ℕ) (x : Euclidean d) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y : Euclidean d ↦ ∫ a, g a y ∂μ) x‖ ≤ C k n := by
  rw [hderiv n x]
  calc ‖x‖ ^ k * ‖∫ a, iteratedFDeriv ℝ n (fun y : Euclidean d ↦ g a y) x ∂μ‖
      ≤ ‖x‖ ^ k * ∫ a, ‖iteratedFDeriv ℝ n (fun y : Euclidean d ↦ g a y) x‖ ∂μ :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = ∫ a, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y : Euclidean d ↦ g a y) x‖ ∂μ := by
        rw [integral_const_mul]
    _ ≤ ∫ _a : α, C k n ∂μ :=
        integral_mono_of_nonneg (.of_forall fun _ ↦ by positivity) (integrable_const _)
          (.of_forall fun a ↦ hbound k n a x)
    _ = C k n := by simp

/-- The average `x ↦ ∫ g a x ∂μ` of a uniformly dominated family of Schwartz functions, as a
Schwartz function. -/
def schwartzAverage (hsmooth : ContDiff ℝ ∞ fun x : Euclidean d ↦ ∫ a, g a x ∂μ)
    (hderiv : ∀ (n : ℕ) (x : Euclidean d),
        iteratedFDeriv ℝ n (fun y : Euclidean d ↦ ∫ a, g a y ∂μ) x =
          ∫ a, iteratedFDeriv ℝ n (fun y : Euclidean d ↦ g a y) x ∂μ)
    (hbound : ∀ (k n : ℕ) (a : α) (x : Euclidean d),
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y : Euclidean d ↦ g a y) x‖ ≤ C k n) :
    TestFunction d where
  toFun x := ∫ a, g a x ∂μ
  smooth' := hsmooth
  decay' k n := ⟨C k n, pow_mul_norm_iteratedFDeriv_integral_le μ g C hbound hderiv k n⟩

end ProbabilityAverage

/-- The rotational average of a test function, as a test function (report §2.1). -/
def rotationalAverageSchwartz {d : ℕ} (f : TestFunction d) : TestFunction d := by
  refine schwartzAverage (radialOrthogonalHaar d)
    (fun U : OrthogonalGroup d ↦ compIsometry (orthogonalLinearIsometry U⁻¹) f)
    (fun k n ↦ SchwartzMap.seminorm ℂ k n f) ?_ ?_ ?_
  · refine contDiff_of_differentiable_iteratedFDeriv fun n _ ↦ ?_
    rw [funext fun x ↦ iteratedFDeriv_integral (radialOrthogonalHaar d) _ _
      (fun n x ↦ aestronglyMeasurable_iteratedFDeriv_compIsometry f n x)
      (fun U k n ↦ (seminorm_compIsometry (orthogonalLinearIsometry U⁻¹) f k n).le) n x]
    exact fun x ↦ (hasFDerivAt_integral_iteratedFDeriv (radialOrthogonalHaar d) _ _
      (fun n x ↦ aestronglyMeasurable_iteratedFDeriv_compIsometry f n x)
      (fun U k n ↦ (seminorm_compIsometry (orthogonalLinearIsometry U⁻¹) f k n).le)
      n x).differentiableAt
  · exact fun n x ↦ iteratedFDeriv_integral (radialOrthogonalHaar d) _ _
      (fun n x ↦ aestronglyMeasurable_iteratedFDeriv_compIsometry f n x)
      (fun U k n ↦ (seminorm_compIsometry (orthogonalLinearIsometry U⁻¹) f k n).le) n x
  · exact fun k n U x ↦ compIsometry_le_seminorm (orthogonalLinearIsometry U⁻¹) f k n x

@[simp] theorem rotationalAverageSchwartz_apply {d : ℕ} (f : TestFunction d) (x : Euclidean d) :
    rotationalAverageSchwartz f x = rotationalAverage (f : Euclidean d → ℂ) x := rfl

/-- `𝓕(ℛf) = ℛ(𝓕f)` for a test function `f` (report §2.1). -/
theorem fourier_rotationalAverageSchwartz {d : ℕ} (f : TestFunction d) :
    (𝓕 (rotationalAverageSchwartz f) : TestFunction d) = rotationalAverageSchwartz (𝓕 f) := by
  have hcoe : (rotationalAverageSchwartz f : Euclidean d → ℂ) = rotationalAverage f :=
    funext (rotationalAverageSchwartz_apply f)
  ext x
  calc (𝓕 (rotationalAverageSchwartz f) : TestFunction d) x
      = 𝓕 (rotationalAverage (f : Euclidean d → ℂ)) x := by
        rw [congrFun (SchwartzMap.fourier_coe (rotationalAverageSchwartz f)) x, hcoe]
    _ = rotationalAverage (𝓕 (f : Euclidean d → ℂ)) x :=
        fourier_rotationalAverage f.continuous f.integrable x
    _ = rotationalAverageSchwartz (𝓕 f) x := by
        rw [rotationalAverageSchwartz_apply, SchwartzMap.fourier_coe]

end

end CohnElkies
