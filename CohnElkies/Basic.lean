import Mathlib

/-! # The objects of the main statements

The following block is a verbatim copy of the *definitions* of the comparator challenge
`ComparatorChallenges/CohnElkies.lean` (the admissible class `𝒜_d`, the linear program `LP_d`,
sphere packings and their densities, the sign-uncertainty class and constants). It is kept in one
contiguous block, in this order and with these `open`s, on purpose: Lean abstracts the proof terms
occurring in definitions (e.g. the `Nat.AtLeastTwo 2` instance behind the numeral `2`) into
auxiliary constants `foo._proof_n` that are shared *within a file*; the comparator compares the
challenge and the solution constant by constant, so the definitions must elaborate to exactly the
same terms, auxiliary names included. -/

section ComparatorDefinitions

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Metric
open scoped ENNReal NNReal FourierTransform SchwartzMap Topology Real

namespace CohnElkies

abbrev Euclidean (d : ℕ) := EuclideanSpace ℝ (Fin d)

abbrev TestFunction (d : ℕ) := 𝓢(Euclidean d, ℂ)

/-- The volume `v_d = π^{d/2}/Γ(d/2+1)` of the unit ball in `ℝ^d`. -/
def unitBallVolume (d : ℕ) : ℝ :=
  Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1)

end CohnElkies

namespace PackingBounds

/-- The admissible class `𝒜_d` of the report, equation (2): real Schwartz functions `f` with
`𝓕 f ≥ 0`, `𝓕 f (0) > 0` and `f ≤ 0` outside the unit ball (no radiality assumed). -/
structure FullAdmissible (d : ℕ) where
  /-- The Schwartz function `f : ℝ^d → ℂ`. -/
  function : CohnElkies.TestFunction d
  /-- `f` is real-valued. -/
  real : ∀ x : CohnElkies.Euclidean d, (function x).im = 0
  /-- `𝓕 f` is real-valued. -/
  fourier_real :
    ∀ x : CohnElkies.Euclidean d, ((𝓕 function) x).im = 0
  /-- `𝓕 f ≥ 0` on `ℝ^d`. -/
  fourier_nonneg :
    ∀ x : CohnElkies.Euclidean d, 0 ≤ ((𝓕 function) x).re
  /-- `𝓕 f (0) > 0`. -/
  fourier_zero_pos :
    0 < ((𝓕 function) (0 : CohnElkies.Euclidean d)).re
  /-- `f ≤ 0` outside the open unit ball. -/
  outside_nonpos :
    ∀ x : CohnElkies.Euclidean d, 1 ≤ ‖x‖ → (function x).re ≤ 0

/-- `f(0)/𝓕f(0)`. -/
def fullQuotient {d : ℕ} (f : FullAdmissible d) : ℝ :=
  (f.function (0 : CohnElkies.Euclidean d)).re /
    ((𝓕 f.function) (0 : CohnElkies.Euclidean d)).re

def fullQuotientSet (d : ℕ) : Set ℝ :=
  Set.range (fullQuotient (d := d))

/-- The Cohn–Elkies linear programming bound `LP_d = (v_d/2^d) inf_{f ∈ 𝒜_d} f(0)/𝓕f(0)`,
equation (3) of the report. -/
def fullLinearProgram (d : ℕ) : ℝ :=
  CohnElkies.unitBallVolume d / (2 : ℝ) ^ d *
    sInf (fullQuotientSet d)

end PackingBounds

/-- A sphere packing: a set of centers with pairwise distances at least `separation`. -/
structure SpherePacking (d : ℕ) where
  /-- The centers of the balls. -/
  centers : Set (EuclideanSpace ℝ (Fin d))
  /-- The minimal distance between centers; the balls have radius `separation / 2`. -/
  separation : ℝ
  /-- The separation is positive. -/
  separation_pos : 0 < separation := by positivity
  /-- Distinct centers are at distance at least `separation`. -/
  centers_dist : Pairwise (separation ≤ dist · · : centers → centers → Prop)

@[reducible] def SpherePacking.occupiedBallRegion {d : ℕ} (S : SpherePacking d) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  ⋃ x : S.centers, ball (x : EuclideanSpace ℝ (Fin d)) (S.separation / 2)

noncomputable def SpherePacking.densityInsideRadius {d : ℕ}
    (S : SpherePacking d) (R : ℝ) : ℝ≥0∞ :=
  volume (S.occupiedBallRegion ∩ ball 0 R) / volume (ball (0 : EuclideanSpace ℝ (Fin d)) R)

noncomputable def SpherePacking.upperPackingDensity {d : ℕ}
    (S : SpherePacking d) : ℝ≥0∞ :=
  limsup S.densityInsideRadius atTop

/-- The sphere-packing constant `Δ_d`: the supremum of the upper densities of all packings. -/
def SpherePackingConstant (d : ℕ) : ℝ≥0∞ :=
  ⨆ S : SpherePacking d, S.upperPackingDensity

namespace CohnElkies

/-- The class of (5)–(6) of the report: `0 ≠ g ∈ L¹(ℝ^d;ℝ)` with `𝓕 g = ς g` and `g(0) = 0`,
where `ς = ±1`. Pointwise values refer to the continuous Fourier-inversion representative:
requiring `𝓕 g = ς g` *everywhere* (not only almost everywhere) forces `g` to be that
representative, since the Fourier transform of an integrable function is continuous. -/
structure SignEigenfunction (d : ℕ) (ς : ℤˣ) where
  /-- The function `g : ℝ^d → ℝ`. -/
  toFun : Euclidean d → ℝ
  /-- `g` is integrable. -/
  integrable : Integrable toFun
  /-- `𝓕 g = ς g` everywhere. -/
  fourier_eq : ∀ ξ : Euclidean d, 𝓕 (fun x ↦ (toFun x : ℂ)) ξ = ((ς : ℤ) : ℂ) * toFun ξ
  /-- `g` is not the zero function. -/
  ne_zero : toFun ≠ 0
  /-- `g(0) = 0`. -/
  zero : toFun 0 = 0

/-- The last-sign radius `r(g) = inf {R ≥ 0 : g(x) ≥ 0 for ‖x‖ ≥ R}` of (5), with `r(g) = ⊤` when
no such radius exists. -/
def signRadius {d : ℕ} (g : Euclidean d → ℝ) : ℝ≥0∞ :=
  ⨅ R : {R : ℝ≥0 // ∀ x : Euclidean d, (R : ℝ) ≤ ‖x‖ → 0 ≤ g x}, (R : ℝ≥0∞)

/-- The sign-uncertainty constants `A_ς(d) = inf r(g)` of (6). -/
def signUncertaintyConstant (ς : ℤˣ) (d : ℕ) : ℝ≥0∞ :=
  ⨅ g : SignEigenfunction d ς, signRadius g.toFun

end CohnElkies

end -- noncomputable section

end ComparatorDefinitions

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory Real
open scoped FourierTransform SchwartzMap Topology

/-- A complex-valued function on `ℝ^d` is real valued if its imaginary part vanishes. -/
def IsRealValued {d : ℕ} (f : Euclidean d → ℂ) : Prop := ∀ x : Euclidean d, (f x).im = 0

/-- A function on `ℝ^d` is radial if it only depends on the norm of its argument. -/
def IsRadial {d : ℕ} {E : Type*} (f : Euclidean d → E) : Prop :=
  ∀ x y : Euclidean d, ‖x‖ = ‖y‖ → f x = f y

/-- The admissible class `𝒜_d` of the report, equation (2): real Schwartz functions `f` with
`𝓕 f ≥ 0`, `𝓕 f (0) > 0` and `f ≤ 0` outside the unit ball, no radiality assumed. This is the
comparator structure `PackingBounds.FullAdmissible`; the radial subclass is `RadialAdmissible`. -/
abbrev Admissible (d : ℕ) := PackingBounds.FullAdmissible d

/-- The radial admissible class `𝒜_d^rad = 𝒜_d ∩ 𝒮_rad(ℝ^d; ℝ)` of the report, §2.1: admissible
functions depending only on the norm of their argument. -/
structure RadialAdmissible (d : ℕ) extends toAdmissible : Admissible d where
  /-- The function is radial. -/
  radial : IsRadial function

theorem unitBallVolume_pos (d : ℕ) : 0 < unitBallVolume d :=
  div_pos (rpow_pos_of_pos pi_pos _) (Gamma_pos_of_pos (by positivity))

/-- The quotient `f(0) / 𝓕f(0)` of an admissible function (`PackingBounds.fullQuotient`). -/
abbrev quotient {d : ℕ} : Admissible d → ℝ := PackingBounds.fullQuotient

/-- The set of quotients `f(0) / 𝓕f(0)`, `f ∈ 𝒜_d` (`PackingBounds.fullQuotientSet`). -/
abbrev quotientSet (d : ℕ) : Set ℝ := PackingBounds.fullQuotientSet d

/-- The Cohn–Elkies linear programming bound `LP_d = 2^{-d} v_d inf_{f ∈ 𝒜_d} f(0)/𝓕f(0)` of the
report, equation (3) (`PackingBounds.fullLinearProgram`, the object of the main theorems). -/
abbrev LP (d : ℕ) : ℝ := PackingBounds.fullLinearProgram d

theorem geometricFactor_pos (d : ℕ) : 0 < unitBallVolume d / 2 ^ d :=
  div_pos (unitBallVolume_pos d) (by positivity)

/-- The normalized cost `(f(0)/𝓕f(0))^{1/d} / √d` of an admissible function (report (31)). -/
def normalizedCost {d : ℕ} (f : Admissible d) : ℝ := quotient f ^ (d : ℝ)⁻¹ / √d

/-- The infimum of the normalized costs over `𝒜_d`. -/
def normalizedProgram (d : ℕ) : ℝ := sInf (Set.range (normalizedCost (d := d)))

/-- The critical radius `1/π` of the sign-uncertainty obstruction. -/
def criticalRadius : ℝ := π⁻¹

/-- The constant `√(e / (2π))` of Theorem 1.1. -/
def criticalPackingBase : ℝ := √(exp 1 / (2 * π))

/-- The exponent `(1/2) log₂ (2π / e)` of Theorem 1.1. -/
def criticalBinaryExponent : ℝ := 1 / 2 * logb 2 (2 * π / exp 1)

theorem criticalRadius_pos : 0 < criticalRadius := inv_pos.mpr pi_pos

theorem criticalPackingBase_pos : 0 < criticalPackingBase := by
  unfold criticalPackingBase
  positivity

/-- The normalized programs converge to the critical radius `1/π`. -/
def SharpQuotientAsymptotic : Prop := Tendsto normalizedProgram atTop (𝓝 criticalRadius)

/-- `log (LP_d) / d → (1/2) log (e / (2π))`. -/
def SharpLogAsymptotic : Prop :=
  Tendsto (fun d : ℕ ↦ log (LP d) / d) atTop (𝓝 (1 / 2 * log (exp 1 / (2 * π))))

/-- `LP_d^{1/d} → √(e / (2π))` (Theorem 1.1). -/
def SharpPackingRootAsymptotic : Prop :=
  Tendsto (fun d : ℕ ↦ LP d ^ (d : ℝ)⁻¹) atTop (𝓝 criticalPackingBase)

end

noncomputable section

open Filter MeasureTheory
open scoped FourierTransform SchwartzMap

/-- `f(0) > 0` for admissible `f ∈ 𝒜_d`, by Fourier inversion: `f(0) = ∫ 𝓕 f > 0`. -/
theorem admissible_zero_pos {d : ℕ} (f : Admissible d) : 0 < (f.function 0).re := by
  have h : f.function 0 = ∫ x, 𝓕 f.function x := by
    have h := congrFun (SchwartzMap.fourierInv_coe (𝓕 f.function)) 0
    rw [FourierTransform.fourierInv_fourier_eq, Real.fourierInv_eq] at h
    simpa using h
  rw [h]
  refine lt_of_lt_of_eq ?_ (integral_re (𝓕 f.function).integrable)
  exact integral_pos_of_integrable_nonneg_nonzero
    (Complex.continuous_re.comp (𝓕 f.function).continuous) (𝓕 f.function).integrable.re
    f.fourier_nonneg f.fourier_zero_pos.ne'

theorem quotient_pos {d : ℕ} (f : Admissible d) : 0 < quotient f :=
  div_pos (admissible_zero_pos f) f.fourier_zero_pos

theorem quotientSet_bddBelow (d : ℕ) : BddBelow (quotientSet d) :=
  ⟨0, by rintro _ ⟨f, rfl⟩; exact (quotient_pos f).le⟩

theorem normalizedCost_nonneg {d : ℕ} (f : Admissible d) : 0 ≤ normalizedCost f :=
  div_nonneg (Real.rpow_nonneg (quotient_pos f).le _) (Real.sqrt_nonneg _)

theorem normalizedCostSet_bddBelow (d : ℕ) : BddBelow (Set.range (normalizedCost (d := d))) :=
  ⟨0, by rintro _ ⟨f, rfl⟩; exact normalizedCost_nonneg f⟩

/-- `𝓕 (𝓕 f) (x) = f (-x)` for Schwartz functions. -/
theorem fourier_sq_apply {d : ℕ} (f : TestFunction d) (x : Euclidean d) :
    (𝓕 (𝓕 f) : TestFunction d) x = f (-x) := by
  have h := congrFun (SchwartzMap.fourierInv_coe (𝓕 f)) (-x)
  rw [FourierTransform.fourierInv_fourier_eq, Real.fourierInv_eq_fourier_neg, neg_neg,
    ← SchwartzMap.fourier_coe] at h
  exact h.symm

/-- The anti-self-Fourier part `𝓕 f - f` of a test function (report, proof of Theorem 3.8). -/
def antiFourierPart {d : ℕ} (f : TestFunction d) : TestFunction d := 𝓕 f - f

/-- For radial `f`, `𝓕 f - f` is anti-self-Fourier. -/
theorem fourier_antiFourierPart {d : ℕ} (f : TestFunction d) (hf : IsRadial f) :
    (𝓕 (antiFourierPart f) : TestFunction d) = -antiFourierPart f := by
  have h : (𝓕 (𝓕 f) : TestFunction d) = f := by
    ext x
    rw [fourier_sq_apply]
    exact hf _ _ (norm_neg x)
  simp [antiFourierPart, sub_eq_add_neg, h]

theorem antiFourierPart_zero {d : ℕ} (f : TestFunction d)
    (hbalance : (𝓕 f : TestFunction d) 0 = f 0) : antiFourierPart f 0 = 0 :=
  sub_eq_zero.mpr hbalance

theorem antiFourierPart_nonneg_of_signs {d : ℕ} (f : TestFunction d) (R : ℝ)
    (hfourier : ∀ x : Euclidean d, 0 ≤ ((𝓕 f) x).re)
    (houtside : ∀ x : Euclidean d, R ≤ ‖x‖ → (f x).re ≤ 0) (x : Euclidean d) (hx : R ≤ ‖x‖) :
    0 ≤ (antiFourierPart f x).re := by
  change 0 ≤ ((𝓕 f) x).re - (f x).re
  linarith [hfourier x, houtside x hx]

/-- A nonzero real radial Schwartz function with `𝓕 g = ς g` (`ς = ±1`) and `g 0 = 0`
(report §3, the functions of Proposition 3.1). -/
structure RadialEigenfunction (d : ℕ) (ς : ℤˣ) where
  /-- The underlying test function. -/
  toFun : TestFunction d
  real : IsRealValued toFun
  radial : IsRadial toFun
  ne_zero : toFun ≠ 0
  fourier_eq : (𝓕 toFun : TestFunction d) = ((ς : ℤ) : ℂ) • toFun
  zero : toFun 0 = 0

/-- `𝓕 g (0) = ς g (0) = 0` for a radial eigenfunction `g`. -/
theorem RadialEigenfunction.fourier_zero {d : ℕ} {ς : ℤˣ} (g : RadialEigenfunction d ς) :
    (𝓕 g.toFun : TestFunction d) 0 = 0 := by
  rw [g.fourier_eq]
  simp [g.zero]

/-- A nonzero real radial anti-self-Fourier test function (`𝓕 g = -g`) vanishing at the origin
and nonnegative outside the ball of radius `R` (report (30)): a radial eigenfunction with
eigenvalue `-1` together with the sign condition. -/
structure AntiSelfFourierWitness (d : ℕ) (R : ℝ) extends RadialEigenfunction d (-1) where
  eventually_nonneg : ∀ x : Euclidean d, R ≤ ‖x‖ → 0 ≤ (toFun x).re

/-- Proposition 3.7 of the report: for every `0 < c < 1/π`, no anti-self-Fourier witness of
radius `c √d` exists in all sufficiently large dimensions `d`. -/
def UniformAntiFourierSignRadius : Prop :=
  ∀ c : ℝ, 0 < c → c < criticalRadius → ∀ᶠ d : ℕ in atTop,
    IsEmpty (AntiSelfFourierWitness d (c * √d))

end

end CohnElkies
