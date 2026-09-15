import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import CohnElkiesBlueprint.Chapters.Introduction
import CohnElkiesBlueprint.Chapters.CohnElkiesBound
import CohnElkiesBlueprint.Chapters.Preliminaries
import CohnElkiesBlueprint.Chapters.LowerBound
import CohnElkiesBlueprint.Chapters.UpperBound
import CohnElkiesBlueprint.Chapters.AppendixA
import CohnElkiesBlueprint.Chapters.Differences

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The Cohn–Elkies exponent and sign uncertainty" =>

This blueprint follows Chapter 1 of the report *Ten proofs* (OpenAI): the exact exponential rate
$`\mathrm{LP}_d^{1/d} \to \sqrt{e/(2\pi)}` of the Cohn–Elkies linear programming bound for sphere
packings (Theorem 1.1) and the asymptotics $`\mathsf{A}_\pm(d)/\sqrt d \to 1/\pi` of the
sign-uncertainty constants (Theorem 1.2). Every node links to its Lean counterpart in the
`CohnElkies` library. The chapter *The Cohn–Elkies bound* proves the linear-programming bound
$`\Delta_d \le \mathrm{LP}_d`, which the report cites as an external input; the chapter *Report
versus formalization* records where the formal proofs deviate from the report; Appendix A is
formalized except for its strict inequality, which needs an extremizer.

{include 0 CohnElkiesBlueprint.Chapters.Introduction}
{include 0 CohnElkiesBlueprint.Chapters.CohnElkiesBound}
{include 0 CohnElkiesBlueprint.Chapters.Preliminaries}
{include 0 CohnElkiesBlueprint.Chapters.LowerBound}
{include 0 CohnElkiesBlueprint.Chapters.UpperBound}
{include 0 CohnElkiesBlueprint.Chapters.AppendixA}
{include 0 CohnElkiesBlueprint.Chapters.Differences}

{blueprint_graph}
{blueprint_summary}
