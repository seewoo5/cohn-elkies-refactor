import CohnElkies.PackingBound
import CohnElkies.Manuscript
import CohnElkies.SignUncertainty.Main
import CohnElkies.SignUncertainty.AppendixA
import CohnElkies.LowerBound.LogMomentDigamma
import CohnElkies.LowerBound.PhragmenLindelofMajorization

/-!
# The Cohn–Elkies linear programming bound: exponential rate and sign uncertainty

Root module of the library. The leaves `CohnElkies.PackingBound` (Theorem 1.1: the exponential
rate of the Cohn–Elkies bound `LP_d`, and the sphere packing bound `Δ_d ≤ LP_d`),
`CohnElkies.Manuscript` (the conclusions of Chapter 1 of the report in the notation of the
manuscript), `CohnElkies.SignUncertainty.Main` (Theorem 1.2: `A_±(d)/√d → 1/π`),
`CohnElkies.SignUncertainty.AppendixA` (Proposition A.1 and, through the existence of extremizers
for `A₋(d)` of Cohn–Gonçalves, `A₊(d) < A₋(d)` for every `d ≥ 1`),
`CohnElkies.LowerBound.LogMomentDigamma` (the log-moment identity (22) of the report, not used by
the other modules) and `CohnElkies.LowerBound.PhragmenLindelofMajorization` (the alternative proof
of the Poisson principle for the strip by Phragmén–Lindelöf, also not used by the other modules)
import everything else.
-/
