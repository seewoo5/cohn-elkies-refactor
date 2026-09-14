import Mathlib

/-!
# Comparator challenge: the Cohn–Elkies exponent and the sign-uncertainty constants

Self-contained statements (only Mathlib is imported) of the main results of Chapter 1 of the
report "Ten proofs" (OpenAI), formalized in this repository:

* Theorem 1.1: `LP_d^{1/d} → √(e/(2π))`, equivalently `log₂ LP_d / d → -½ log₂(2π/e)`;
* the packing consequence `Δ_d ≤ LP_d` and `Δ_d ≤ (√(e/(2π)) + o(1))^d`;
* Theorem 1.2: `A_±(d)/√d → 1/π` for the sign-uncertainty constants of `L¹` Fourier
  eigenfunctions;

The definitions of the linear program and of the packing constant are those of the original
challenge `ComparatorChallenges/A_SpherePacking.lean` of the repository `openai/ten-proofs`.
-/

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
  function : CohnElkies.TestFunction d
  real : ∀ x : CohnElkies.Euclidean d, (function x).im = 0
  fourier_real :
    ∀ x : CohnElkies.Euclidean d, ((𝓕 function) x).im = 0
  fourier_nonneg :
    ∀ x : CohnElkies.Euclidean d, 0 ≤ ((𝓕 function) x).re
  fourier_zero_pos :
    0 < ((𝓕 function) (0 : CohnElkies.Euclidean d)).re
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
  centers : Set (EuclideanSpace ℝ (Fin d))
  separation : ℝ
  separation_pos : 0 < separation := by positivity
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
  toFun : Euclidean d → ℝ
  integrable : Integrable toFun
  fourier_eq : ∀ ξ : Euclidean d, 𝓕 (fun x ↦ (toFun x : ℂ)) ξ = ((ς : ℤ) : ℂ) * toFun ξ
  ne_zero : toFun ≠ 0
  zero : toFun 0 = 0

/-- The last-sign radius `r(g) = inf {R ≥ 0 : g(x) ≥ 0 for ‖x‖ ≥ R}` of (5), with `r(g) = ⊤` when
no such radius exists. -/
def signRadius {d : ℕ} (g : Euclidean d → ℝ) : ℝ≥0∞ :=
  ⨅ R : {R : ℝ≥0 // ∀ x : Euclidean d, (R : ℝ) ≤ ‖x‖ → 0 ≤ g x}, (R : ℝ≥0∞)

/-- The sign-uncertainty constants `A_ς(d) = inf r(g)` of (6). -/
def signUncertaintyConstant (ς : ℤˣ) (d : ℕ) : ℝ≥0∞ :=
  ⨅ g : SignEigenfunction d ς, signRadius g.toFun

end CohnElkies

namespace PackingBounds.FullMain

/-- Theorem 1.1: `LP_d^{1/d} → √(e/(2π))`. -/
theorem exact_limit :
    Tendsto (fun d : ℕ ↦ PackingBounds.fullLinearProgram d ^ ((d : ℝ)⁻¹)) atTop
      (𝓝 (Real.sqrt (Real.exp 1 / (2 * Real.pi)))) := by
  sorry

/-- Theorem 1.1 in base-2 form: `log₂ LP_d / d → -½ log₂(2π/e)`. -/
theorem exact_binary_exponent :
    Tendsto (fun d : ℕ ↦ Real.logb 2 (PackingBounds.fullLinearProgram d) / (d : ℝ)) atTop
      (𝓝 (-(1 / 2 : ℝ) * Real.logb 2 (2 * Real.pi / Real.exp 1))) := by
  sorry

end PackingBounds.FullMain

namespace PackingBounds.PackingBridge

/-- The Cohn–Elkies bound `Δ_d ≤ LP_d`, equation (4). -/
theorem sphere_packing_le_linear_program (d : ℕ) (hd : 0 < d) :
    SpherePackingConstant d ≤ ENNReal.ofReal (PackingBounds.fullLinearProgram d) := by
  sorry

/-- The sharp exponential packing bound `Δ_d ≤ (√(e/(2π)) + o(1))^d`. -/
theorem sphere_packing_sharp_asymptotic_upper :
    ∃ e : ℕ → ℝ,
      Asymptotics.IsLittleO atTop e (fun _ : ℕ ↦ (1 : ℝ)) ∧
      ∀ d : ℕ, 0 < d →
        SpherePackingConstant d ≤
          ENNReal.ofReal ((Real.sqrt (Real.exp 1 / (2 * Real.pi)) + e d) ^ d) := by
  sorry

end PackingBounds.PackingBridge

namespace CohnElkies

/-- Theorem 1.2: `A_ς(d)/√d → 1/π` for both signs (in `ℝ≥0∞`, so in particular `A_ς(d) < ⊤`
for all large `d`). -/
theorem signUncertaintyConstant_div_sqrt_tendsto (ς : ℤˣ) :
    Tendsto (fun d : ℕ ↦ signUncertaintyConstant ς d / ENNReal.ofReal (Real.sqrt d)) atTop
      (𝓝 (ENNReal.ofReal (Real.pi⁻¹))) := by
  sorry

end CohnElkies

end
