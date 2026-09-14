import CohnElkies.SignUncertainty.LowerBound
import CohnElkies.SignUncertainty.UpperBound

/-! # Theorem 1.2 of the report: `A_±(d)/√d → 1/π`

The sign-uncertainty constants `A_ς(d)` of report (6) satisfy `A_ς(d)/√d → 1/π` as `d → ∞`, for
both signs `ς = ±1`. The lower bound `1/π ≤ liminf A_ς(d)/√d` is Proposition 3.7
(`CohnElkies.SignUncertainty.LowerBound`); the upper bound `limsup A_ς(d)/√d ≤ 1/π` comes from
the functions `f₊ - f₋` and `f₀` of Theorem 4.1 (`CohnElkies.SignUncertainty.UpperBound`).
The main statement is formulated in `ℝ≥0∞` (so it includes `A_ς(d) < ⊤` for all large `d`); the
real-valued form `A_ς(d).toReal/√d → 1/π` follows. -/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology

/-- Theorem 1.2 of the report: `A_±(d)/√d → 1/π`. -/
theorem signUncertaintyConstant_div_sqrt_tendsto (ς : ℤˣ) :
    Tendsto (fun d : ℕ ↦ signUncertaintyConstant ς d / ENNReal.ofReal (Real.sqrt d)) atTop
      (𝓝 (ENNReal.ofReal (Real.pi⁻¹))) :=
  tendsto_of_le_liminf_of_limsup_le (le_liminf_signUncertaintyConstant_div_sqrt ς)
    (limsup_signUncertaintyConstant_div_sqrt_le ς)

/-- The infimum `A_ς(d)` of report (6) is finite for all large `d` (report, proof of Theorem 1.2:
`A_ς(d) ≤ R_{ε,d}`). -/
theorem eventually_signUncertaintyConstant_lt_top (ς : ℤˣ) :
    ∀ᶠ d : ℕ in atTop, signUncertaintyConstant ς d < ⊤ := by
  obtain ⟨ε, hε⟩ := (eventually_signUncertaintyConstant_le ς).exists
  filter_upwards [hε] with d hd
  exact hd.trans_lt ENNReal.ofReal_lt_top

/-- Theorem 1.2 of the report in real form: `A_±(d)/√d → 1/π`, with `A_ς(d)` read as a real
number (`⊤.toReal = 0`, which only happens for finitely many `d`). -/
theorem tendsto_toReal_signUncertaintyConstant_div_sqrt (ς : ℤˣ) :
    Tendsto (fun d : ℕ ↦ (signUncertaintyConstant ς d).toReal / √(d : ℝ)) atTop (𝓝 π⁻¹) := by
  have h := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp
    (signUncertaintyConstant_div_sqrt_tendsto ς)
  rw [ENNReal.toReal_ofReal (inv_pos.2 Real.pi_pos).le] at h
  refine h.congr' (Eventually.of_forall fun d ↦ ?_)
  simp only [Function.comp_apply]
  rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]

end

end CohnElkies
