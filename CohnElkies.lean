import CohnElkies.PackingBound
import CohnElkies.Manuscript
import CohnElkies.SignUncertainty.Main
import CohnElkies.SignUncertainty.AppendixA
import CohnElkies.SignUncertainty.OriginCorrection
import CohnElkies.SignUncertainty.Finiteness
import CohnElkies.SignUncertainty.Extremizer

/-!
# The Cohn–Elkies linear programming bound: exponential rate and sign uncertainty

Root module of the library. The leaves `CohnElkies.PackingBound` (Theorem 1.1: the exponential
rate of the Cohn–Elkies bound `LP_d`, and the sphere packing bound `Δ_d ≤ LP_d`),
`CohnElkies.Manuscript` (the conclusions of Chapter 1 of the report in the notation of the
manuscript), `CohnElkies.SignUncertainty.Main` (Theorem 1.2: `A_±(d)/√d → 1/π`),
`CohnElkies.SignUncertainty.AppendixA` (Proposition A.1 and `A₊(d) ≤ A₋(d)`),
`CohnElkies.SignUncertainty.OriginCorrection` (the origin correction of Cohn–Gonçalves, Lemma 3.1,
towards the existence of extremizers for `A₋(d)`), `CohnElkies.SignUncertainty.Finiteness`
(`0 < A_ς(d) < ∞` for every `d ≥ 1`) and `CohnElkies.SignUncertainty.Extremizer` (Cohn–Gonçalves,
Theorem 1.4: `A₋(d)` is attained, hence the unconditional `A₊(d) < A₋(d)` of Appendix A) import
everything else.
-/
