import CohnElkies.PackingBound
import CohnElkies.Manuscript
import CohnElkies.SignUncertainty.Main
import CohnElkies.SignUncertainty.AppendixA

/-!
# The Cohn–Elkies linear programming bound: exponential rate and sign uncertainty

Root module of the library. The leaves `CohnElkies.PackingBound` (Theorem 1.1: the exponential
rate of the Cohn–Elkies bound `LP_d`, and the sphere packing bound `Δ_d ≤ LP_d`),
`CohnElkies.Manuscript` (the conclusions of Chapter 1 of the report in the notation of the
manuscript), `CohnElkies.SignUncertainty.Main` (Theorem 1.2: `A_±(d)/√d → 1/π`) and
`CohnElkies.SignUncertainty.AppendixA` (Proposition A.1 and `A₊(d) ≤ A₋(d)`) import everything
else.
-/
