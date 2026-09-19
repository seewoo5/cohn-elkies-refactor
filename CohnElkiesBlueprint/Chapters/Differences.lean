import Verso
import VersoManual
import VersoBlueprint
import CohnElkies

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Report versus formalization" =>

The Lean development follows the report's strategy (a Poisson/Mellin lower bound and a
perturbed-Gaussian upper construction) but deviates from it in several places, either because a
statement was easier to formalize in a different form or because the original file chose
different numerical safety margins. This chapter records those deviations so that the nodes of
the preceding chapters can be matched with their Lean counterparts; the nodes below are the
formal replacements of the report's arguments, with their own Lean declarations. It also lists
what the formalization adds to the report (the Cohn–Elkies bound) and what is still missing.

# The Poisson principle: an alternative proof by Phragmén–Lindelöf

The report proves the interior bound of Lemma 3.2 by mapping the strip conformally onto the upper
half-plane and applying the Poisson principle to the subharmonic function $`\log|Z|`; this is the
proof formalized in {bpref "lemma_strip_poisson_principle"}[], on top of the subharmonic-function
library of the preliminaries chapter. The formalization also contains a second, independent proof
of the Poisson principle for the strip, which stays inside the strip: the holomorphic Poisson
integral $`W` of the boundary datum is built directly from the strip kernel, and a maximum-modulus
(Phragmén–Lindelöf) argument is applied to $`e^{-W}Z`. It gives the principle for functions of
Phragmén–Lindelöf growth rather than only for bounded ones
({bpref "lemma_strip_poisson_principle_phragmen_lindelof"}[]), and it re-derives the capped bound
of Lemma 3.2 (`CohnElkies.norm_Z_g_le_exp_integral_of_cap_phragmenLindelof`,
`CohnElkies.exists_capped_poisson_majorization_phragmenLindelof`, module
`CohnElkies/LowerBound/PhragmenLindelofMajorization.lean`); nothing else depends on it. Mathlib's
`PhragmenLindelof.horizontal_strip` cannot be applied directly, because it requires the function
itself, not only its modulus, to extend continuously to the closed strip (`DiffContOnCl`); only
$`\operatorname{Re}W`, not $`W`, extends continuously.

:::lemma_ "lemma_phragmen_lindelof_strip" (lean := "PhragmenLindelof.horizontal_strip_norm_extension")
Let $`a < b`, $`C > 0`, and let $`f : \mathbb{C} \to \mathbb{C}` be holomorphic on the open strip
$`\{a < \operatorname{Im}z < b\}`. Suppose $`|f|` has a continuous extension $`N \ge 0` to the
closed strip, that $`N \le C` on the two boundary lines, and that
$`|f(z)| = O\bigl(\exp(B\exp(c|\operatorname{Re}z|))\bigr)` in the strip as
$`|\operatorname{Re}z| \to \infty`,
for some $`B` and some $`c < \pi/(b-a)`. Then $`N \le C` throughout the closed strip.
:::

:::proof "lemma_phragmen_lindelof_strip"
Standard Phragmén–Lindelöf argument on the strip: multiply by $`\exp(-\eta\cosh(c'(z - z_0)))`-type
factors with $`c < c' < \pi/(b-a)` to kill the growth, apply the maximum-modulus principle on large
rectangles, and let the auxiliary parameter tend to zero. The distinction between continuity of
$`f` and continuity of its modulus matters: only the modulus is assumed to extend continuously,
so the maximum-modulus principle on the rectangles is applied to $`N` rather than to $`f`
(`Complex.norm_extension_le_of_forall_mem_frontier_le`).
:::

:::lemma_ "lemma_strip_poisson_principle_phragmen_lindelof" (lean := "CohnElkies.norm_le_exp_integral_P_σ_of_strip_of_isBigO")
(Poisson principle for the strip, functions of Phragmén–Lindelöf growth.) Let $`\lambda > 0` and
let $`Z` be holomorphic on the open strip $`\{|\operatorname{Im} t| < \lambda\}`, continuous on
its closure, and of growth $`|Z(t)| \le C\exp(Ce^{c|\operatorname{Re} t|})` there for some
$`c < \pi/(2\lambda)`. Let $`b : \mathbb{R} \to \mathbb{R}` be continuous with
$`|b(y)| \le A(1 + |y|)`, and suppose $`\log|Z(y - i\lambda)| \le b(y)` and
$`\log|Z(y + i\lambda)| \le 0` for all $`y \in \mathbb{R}`. Then for $`-1 < \sigma < 1` and
$`s \in \mathbb{R}`,
$`\log|Z(s + i\sigma\lambda)| \le \int_{\mathbb{R}}P_\sigma(T)\,b(s - \lambda T)\,dT`,
with $`P_\sigma` from {uses "def_strip_poisson_kernel"}[].
:::

:::proof "lemma_strip_poisson_principle_phragmen_lindelof"
The lower-edge harmonic measure $`\lambda^{-1}P_\sigma((s-y)/\lambda)\,dy` of
{uses "lemma_strip_harmonic_measure"}[] is the real part of the holomorphic kernel
$`K_\lambda(z,y) = \frac{i}{4\lambda}\frac{E+1}{E-1}`, $`E = e^{\pi(z-y+i\lambda)/(2\lambda)}`,
regularized to $`\widetilde K_\lambda(z,y) = K_\lambda(z,y) \pm i/(4\lambda)` so that it decays like
$`e^{-\pi|y|/(2\lambda)}` in $`y`. Let $`W(z) = \int_{\mathbb{R}}\widetilde K_\lambda(z,y)\,b(y)\,dy`.
Since $`|b(y)| \le A(1+|y|)`, $`W` is holomorphic on the open strip (differentiation under the
integral sign), $`\operatorname{Re}W(s + i\sigma\lambda) = \int P_\sigma(T)\,b(s-\lambda T)\,dT`, and
$`|\operatorname{Re}W(z)| \le B(1 + |\operatorname{Re}z|)` because $`M_\sigma \le 1` and
$`\int P_\sigma(T)|T|\,dT` is bounded uniformly in $`\sigma`. By dominated convergence
($`P_\sigma` concentrates at $`T = 0` as $`\sigma \downarrow -1` and tends to $`0` as
$`\sigma \uparrow 1`), $`\operatorname{Re}W` extends continuously to the closed strip with boundary
values $`b` on the lower edge and $`0` on the upper edge. Hence $`e^{-W}Z` is holomorphic on the
open strip, its modulus $`e^{-\operatorname{Re}W}|Z|` extends continuously to the closed strip with
values at most $`e^{-b(y)}|Z(y-i\lambda)| \le 1` on the lower edge and $`|Z(y+i\lambda)| \le 1` on
the upper edge, and it is $`O(\exp(B'e^{c'|\operatorname{Re}z|}))` for some $`c' < \pi/(2\lambda)`.
The Phragmén–Lindelöf principle for the strip ({uses "lemma_phragmen_lindelof_strip"}[]) gives
$`e^{-\operatorname{Re}W}|Z| \le 1` inside, i.e.
$`\log|Z(s+i\sigma\lambda)| \le \operatorname{Re}W(s+i\sigma\lambda) = \int P_\sigma(T)\,b(s-\lambda T)\,dT`.
:::

:::lemma_ "lemma_3_2_capped" (lean := "CohnElkies.norm_Z_g_le_exp_integral_of_cap")
(Capped Poisson majorization.) In the setting of {uses "def_normalized_profile"}[] there is
$`D_0 \in \mathbb{R}` such that for every $`D \ge D_0`, every $`-1 < \sigma < 1` and every
$`s \in \mathbb{R}`,
$`|Z(s + i\sigma\lambda)|`
$`\le \exp\Bigl(\int_{\mathbb{R}}P_\sigma(T)\,h_{\lambda,D}(s - \lambda T)\,dT\Bigr)`,
where $`h_{\lambda,D}(y) = \min\{h_\lambda(y), D\}` for $`y \ne 0` and $`h_{\lambda,D}(0) = D`
({uses "def_lower_boundary_majorant"}[], {uses "def_strip_poisson_kernel"}[]). Letting
$`D \to \infty` (dominated convergence) recovers the uncapped bound (18) of {bpref "lemma_3_2"}[].
:::

:::proof "lemma_3_2_capped"
The bottom boundary values of $`Z` satisfy $`|Z(y - i\lambda)| \le e^{h_\lambda(y)}` for $`y \ne 0`
({bpref "lemma_3_2"}[]) and $`Z` is bounded on the closed strip, so for $`D \ge D_0 :=
\max\{0, \sup_y \log|Z(y - i\lambda)|\}` also $`|Z(y - i\lambda)| \le e^{h_{\lambda,D}(y)}` for all
$`y`; the top boundary values satisfy $`|Z(y + i\lambda)| \le 1`. The capped majorant
$`h_{\lambda,D}` is continuous with $`|h_{\lambda,D}(y)| \le A(1 + |y|)` (it is $`-\lambda\log|y| +
O(1)` at infinity). The Poisson principle for the strip ({uses "lemma_strip_poisson_principle"}[])
gives the claim.
:::

# One-sided Riemann bound in Lemma 3.3

The report's Lemma 3.3 states the two-sided weighted error estimate (19). The formalization proves
only the one-sided upper bound that is needed later, with a unified error term for both parities
that is independent of the dimension.

:::lemma_ "lemma_3_3_one_sided" (lean := "CohnElkies.lowerGammaBoundaryLog_dimension_scaled_riemann_le")
For $`d \ge 2`, $`c > 0`, $`T \ne 0`, with $`f_T` as in {bpref "lemma_3_3"}[] and the endpoint phase
$`\Lambda(T) = -\tfrac{\pi|T|}{4} - \tfrac12\log(1 + \tfrac{T^2}{4})`
$`+ \tfrac{|T|}{2}\arctan\tfrac{|T|}{2}`,
one has the exact identity
$`-\int_0^1f_T(x)\,dx = 1 + \Lambda(T)`
and the one-sided bound
$`h_\lambda(\lambda T) \le \lambda\bigl(\log(2\pi ec^2) + \Lambda(T)\bigr) + E(T)`,
$`E(T) = 3|f_T(0)| + 2|f_T(1)| + \tfrac12\log\coth\tfrac{\pi|T|}{2}`,
for $`h_\lambda` as in {uses "def_lower_boundary_majorant"}[] with $`R = c\sqrt d`. Consequently,
for $`0 \le \sigma < 1`,
$`H_\sigma(0) \le \lambda M_\sigma\bigl(\log(2\pi c^2) + J_\sigma\bigr) + E_\sigma`
with $`J_\sigma = 1 + \int(P_\sigma/M_\sigma)\Lambda` and $`E_\sigma = \int P_\sigma E`
finite and independent of $`d` and $`c`: this is the upper half of (20) with an $`O_\sigma(1)`
error. Uses {uses "def_strip_poisson_kernel"}[].
:::

:::proof "lemma_3_3_one_sided"
The same even/odd Riemann-sum computation as in the report's proof of Lemma 3.3, keeping only
the upper estimates: the gamma product formulas of {uses "eq_7_gamma_identities"}[] express
$`h_\lambda(\lambda T)` through a left (even $`d`) or midpoint (odd $`d`) Riemann sum of $`f_T` on
$`[0,1]`, and monotonicity of $`f_T` bounds the Riemann-sum errors by $`f_T(1) - f_T(0)`
(`CohnElkies.monotone_leftRiemann_error`, `CohnElkies.monotone_midpointIntegral_error`); the
odd-dimensional endpoint correction $`\tfrac12\log(2\coth(\pi\lambda|T|/2)/|T|)` is at most
$`|f_T(0)| + \tfrac12\log\coth(\pi|T|/2)`, which makes $`E(T)` independent of $`d`. The identity
for $`\int_0^1 f_T` is an elementary integration (`CohnElkies.lowerRiemannLogPrimitive`), and the
central bound follows by integrating against $`P_\sigma` and using its mass $`M_\sigma`.
:::

# Lemma 3.4 without the digamma identity (22)

The report evaluates $`\lim_{\sigma\uparrow1}J_\sigma` with the digamma log-moment identity (22)
({bpref "eq_22_log_moment_digamma"}[]). The formalization does not use (22): it computes the
expectation of the endpoint phase against the limiting density $`p` of (21) by exchanging the
$`u`-integral with a Frullani-type integral in a parameter $`t`, which produces the Laplace kernel
of the Wallis product already used for (33).

:::lemma_ "lemma_3_4_frullani" (lean := "CohnElkies.integral_poissonLogistic_mul_wallisPhaseKernel")
Let $`p` be the density of {uses "eq_21_sech_characteristic"}[] and $`\Lambda` the endpoint phase of
{uses "lemma_3_3_one_sided"}[]. For $`t > 0` and $`u \in \mathbb{R}` put
$`K(u,t) = \dfrac{(1 - e^{-t})\cos(ut) - te^{-t}}{t^2}`, the real part of the complex Frullani kernel
$`((1 - e^{-t})e^{-zt} - te^{-t})/t^2` at $`z = -iu`. Then
$`\int_0^\infty K(u,t)\,dt = 1 + \Lambda(2u)` for every $`u`,
$`\int_{\mathbb{R}}p(u)K(u,t)\,du = \dfrac{e^{-t}(1 - e^{-t})}{t(1 + e^{-t})}` for every $`t > 0`,
and consequently
$`\int_{\mathbb{R}}p(u)\bigl(1 + \Lambda(2u)\bigr)\,du = \log\dfrac{\pi}{2}`,
$`\int_{\mathbb{R}}p(u)\Lambda(2u)\,du = \log\dfrac{\pi}{2} - 1`.
:::

:::proof "lemma_3_4_frullani"
The $`t`-integral of $`K(u,t)` is evaluated through the antiderivative
$`1 + z\log z - (z+1)\log(z+1)` of the complex Frullani kernel at $`z = a - iu`
(`CohnElkies.integral_wallisPhaseKernel`, `CohnElkies.wallisComplexLogPhase`), letting
$`a \downarrow 0` by dominated convergence (`CohnElkies.tendsto_integral_wallisPhaseKernel`); the
real part at $`z = -iu` is $`1 + \Lambda(2u)` (`CohnElkies.wallisComplexLogPhase_neg_I_mul`). The
$`u`-integral of $`p(u)K(u,t)` reduces, through the cosine transform of $`p` in
{uses "eq_21_sech_characteristic"}[], $`\int p(u)\cos(tu)\,du = t/\sinh t`, to
$`((1-e^{-t})\,t/\sinh t - te^{-t})/t^2`, which is the Laplace kernel. Fubini (the double integral
converges absolutely, `CohnElkies.poissonLogistic_wallisPhase_integrable`) exchanges the two
integrals, and $`\int_0^\infty e^{-t}(1-e^{-t})/(t(1+e^{-t}))\,dt = \log(\pi/2)` is the Wallis
product, {uses "eq_32_ideal_density"}[] (`Real.Wallis.integral_laplaceKernel`). Subtracting
$`\int p = 1` gives the last identity.
:::

# Inverse-quadratic tail majorant in Lemma 3.5

Rather than integrating the two bounds (24) and (25) separately over $`|s| \le B\lambda` and
$`|s| > B\lambda`, the formalization averages them into a single integrable majorant.

:::lemma_ "lemma_3_5_inverse_quadratic" (lean := "CohnElkies.exists_lowerStripPoissonMajorant_integrable_majorant")
For every $`0 < c < 1/\pi` there are $`\sigma \in (0,1)` and $`\gamma, C > 0` such that, for all
sufficiently large $`d` and all $`S \in \mathbb{R}`,
$`\exp\bigl(H_\sigma(\lambda S)\bigr) \le \dfrac{Ce^{-\gamma\lambda}}{(1 + |S|)^2}`, with
$`H_\sigma` from {uses "def_strip_poisson_kernel"}[] and $`R = c\sqrt d`. Consequently
$`\int_{\mathbb{R}}|Z(s + i\sigma\lambda)|\,ds \le CJ\lambda e^{-\gamma\lambda}` with
$`J = \int_{\mathbb{R}}(1 + |S|)^{-2}\,dS`, which is (26) of {bpref "lemma_3_5"}[].
:::

:::proof "lemma_3_5_inverse_quadratic"
Combine the uniform negativity $`H_\sigma(s) \le -\gamma\lambda`, which follows from the central
bound and the maximum property of {uses "lemma_3_3"}[] together with the negativity of the
bracket from {uses "lemma_3_4"}[], with the logarithmic tail
$`H_\sigma(\lambda S) \le -\kappa\lambda\log(|S|/A)` for $`|S| \ge B`, which follows from the
gamma identities of {uses "eq_7_gamma_identities"}[] applied to the majorant and the exponential
decay of the kernel of {uses "def_strip_poisson_kernel"}[]
(`CohnElkies.exists_lowerStripPoissonMajorant_logarithmic_tail`, with
$`\kappa = \int_{-1}^1P_\sigma(T)\,dT/2 > 0`): for large $`d`, $`\kappa\lambda \ge 4`, and averaging
the two bounds (halving $`\gamma`) gives the inverse-square decay; the bounded interval
$`|S| \le B` is absorbed into $`C`. Then $`|Z(s+i\sigma\lambda)| \le e^{H_\sigma(s)}`
({uses "lemma_3_2"}[]) and the substitution $`s = \lambda S` give the $`L^1` bound.
:::

# Parameters of the upper construction

The formalization uses exactly the parameters of {bpref "eq_34_parameters"}[]:
$`u_* = -1 + \tfrac{\log\lambda}{4\lambda}`, $`u_0 = 1 + \tfrac\epsilon4`,
$`U = 1 + \tfrac\epsilon2`, $`B = \epsilon^{-3}`, $`Q = e^{-3\epsilon B/8}`, $`\beta = \epsilon/4`,
$`a_0 = \epsilon^2`,
$`A = \log(1/\epsilon)`, $`b(a) = 1 - 2\epsilon(1+a)`, the exponents $`1/12` for the central
windows, and the residue cutoff $`N = \lceil\log\lambda\rceil` of Lemma 4.10 (`CohnElkies.N_ℓ`).
The original single-file formalization had larger safety margins ($`a_0 = \epsilon^3`,
$`A = 10\log(1/\epsilon)`, $`b(a) = 1 - 10\epsilon(1+a)`, $`N = \lceil 20\log\lambda\rceil`); each
was switched to the report's value and the proofs re-tuned. The margins had been used only
asymptotically ($`a_0 \to 0`, $`A \to \infty`, the ratio of Lemma 4.6, the factorial-tail majorant
of Lemma 4.10), except for the taper: with $`b(0) = 1 - 2\epsilon` the damping margin of Lemma 4.2
cannot exceed $`1 - 2\epsilon`, so the absolute constant of (54) is $`c = 2` and the constants
derived from it downstream (`2\epsilon D_\gamma \le D_u`, $`V_s \le (1 - 2\epsilon)V_\gamma`, the
cubic-window and negative-contour constants) were adjusted; the limiting radius constant
$`1/\pi` is unchanged.

Several lemmas of Section 4 are formalized in the weaker form that the sign conclusions need.
In {bpref "lemma_4_10"}[] the formal statement is the positivity consequence: uniformly on
$`0 \le r \le r_*`, $`e^y|S_N(y) - e^{-y}| < \tfrac12` and
$`e^y|\mathcal{R}_{\lambda}(r)| < \tfrac12`,
whose sum gives $`f_+(r)/f_+(0) > 0`, rather than the full relative asymptotic (82). Likewise the
formal versions of {bpref "lemma_4_8"}[] conclude with the strict inequality
$`|I_{\lambda,P}(u) - P(iu)\sqrt{2\pi/(\lambda V(u))}| < |P(iu)|\sqrt{2\pi/(\lambda V(u))}`,
uniformly on the stated ranges, which is all that the signs in {bpref "cor_4_9"}[] require. The
radius-coverage step of Corollary 4.9 is proved by continuity of $`v` and $`v(u) \to \infty` with
the intermediate value theorem; strict monotonicity of $`v` is not needed there. The absolute
constants of Lemmas 4.2 and 4.4–4.7 are made explicit ($`c = 2`, $`1/(8e)`, $`1/100`, $`1/5000`,
and so on) and the $`O(\epsilon)`-displacement of Lemma 4.2 is replaced by the limit
$`\epsilon \downarrow 0`.

# Theorem 1.1: the two halves are fused

The report proves Theorem 1.1 by combining the lower bound (28) with the upper bound (86) and
Stirling's formula. The formalization does not expose the limit superior half as a separate
theorem; instead it isolates an abstract sandwich argument on the normalized program
$`\inf_{f \in \mathcal{A}_d}(f(0)/\widehat f(0))^{1/d}/\sqrt d`.

:::theorem "thm_1_1_sandwich" (lean := "CohnElkies.sharpQuotient_of_uniform_lower_and_ordered_upper")
Suppose that (a) for every $`c < 1/\pi` and all sufficiently large $`d`, every
$`f \in \mathcal{A}_d` ({uses "def_admissible_class"}[]) has normalized cost
$`(f(0)/\widehat f(0))^{1/d}/\sqrt d \ge c`, and
(b) there is an ordered $`\epsilon`-construction as in {uses "thm_1_1_upper"}[]:
$`\epsilon_0 > 0`, radii with $`R_{\epsilon,d}/\sqrt d \to \alpha_\epsilon` as $`d \to \infty` and
$`\alpha_\epsilon \to 1/\pi` as $`\epsilon \downarrow 0`, and for every $`0 < \epsilon < \epsilon_0`
and all large $`d` an admissible function of normalized cost at most $`R_{\epsilon,d}/\sqrt d`.
Then
$`\inf_{f \in \mathcal{A}_d^{\mathrm{rad}}}(f(0)/\widehat f(0))^{1/d}/\sqrt d \to 1/\pi`,
and consequently, with {uses "def_lp"}[], $`\mathrm{LP}_d^{1/d} \to \sqrt{e/(2\pi)}`.
:::

:::proof "thm_1_1_sandwich"
Write $`\nu_d` for the normalized program. Fix $`c > 1/\pi`. By (b) choose $`\epsilon` with
$`\alpha_\epsilon < c`; for all large $`d` we have $`R_{\epsilon,d}/\sqrt d < c` and an admissible
function of cost at most $`R_{\epsilon,d}/\sqrt d`, so $`\nu_d \le c`
(`CohnElkies.ConstructivePrimalUpperBound`). Fix $`c < 1/\pi`; by (a), $`\nu_d \ge c` for all large
$`d`. Since the order topology of $`\mathbb{R}` is generated by such rays, $`\nu_d \to 1/\pi`
(`CohnElkies.sharpQuotient_of_uniform_lower_and_constructive_upper`). Finally
$`\mathrm{LP}_d^{1/d} = (v_d/2^d)^{1/d}\sqrt d\cdot\nu_d`
(`CohnElkies.linearProgram_root_eq_geometric_mul_normalizedProgram`, using
{uses "lemma_admissible_nonempty"}[]), and $`(v_d/2^d)^{1/d}\sqrt d \to \sqrt{2\pi e}/2` by
{uses "lemma_stirling_ball_volume"}[], so
$`\mathrm{LP}_d^{1/d} \to \sqrt{2\pi e}/(2\pi) = \sqrt{e/(2\pi)}`.
The hypothesis (a) is the content of {uses "thm_3_8"}[] before Stirling's formula is applied.
:::

# The Cohn–Elkies bound is proved

The report cites $`\Delta_d \le \mathrm{LP}_d` as an external input. The formalization proves it,
via Poisson summation for periodic packings and the reduction of arbitrary packings to periodic
ones; see the chapter on the Cohn–Elkies bound ({bpref "thm_lp_bound"}[] and
{bpref "thm_cohn_elkies_bound"}[]). The sphere-packing definitions and the periodic-packing
theory were adapted from the Sphere Packing in Lean project.

# Stirling's formula

Mathlib has Stirling's formula for factorials (`Stirling.tendsto_stirlingSeq_sqrt_pi`) but not
for $`\Gamma` at half-integers; the asymptotics of $`v_d^{1/d}\sqrt d` in
{bpref "lemma_stirling_ball_volume"}[] are therefore derived through an even/odd split in $`d`.
The report's gamma asymptotics (Stirling's expansion of $`\psi`, uniform trigamma and polygamma
bounds, the Malmstén–Binet representation of $`\log\Gamma`, and $`\log|\Gamma(a+ib)|` for
$`|b| \to \infty`) are correspondingly replaced by the elementary bounds
$`\log(x-1) \le \psi(x) \le \log x` ({bpref "lemma_gamma_asymptotics"}[]), explicit moment bounds
for the gamma damping density ({bpref "lemma_4_4"}[]), the exponentiated Binet representation
({bpref "eq_45_log_gamma_integral"}[]) and polynomial decay of $`\Gamma` along vertical lines.

# The digamma function

The original file defines the digamma function ad hoc, as the derivative of
$`\log \circ \Gamma` on the reals, and reproves the needed estimates. The real digamma function
`Real.digamma` of {bpref "def_digamma"}[] now lives in the project's Mathlib-candidate library
(`CohnElkiesForMathlib.Analysis.SpecialFunctions.Gamma.Digamma`), identified with the real part of
Mathlib's `Complex.digamma`, together with its recurrence, the bounds
$`\log(x-1) \le \psi(x) \le \log x`, the harmonic representation
$`\psi(m) = \lim_n(\log n - \sum_{k \le n}(m+k)^{-1})` and Gauss's integral representation
({bpref "lemma_digamma_gauss_integral"}[], listed as a TODO in Mathlib's digamma file). Mathlib (as
of the pinned version) has `Complex.digamma` with its basic values and recurrence but no real
digamma function and no series or asymptotic expansions.

# Subharmonic functions and the half-plane Poisson principle

The report's proof of Lemma 3.2 rests on the Poisson principle for the upper half-plane, applied
to the subharmonic function $`\log|Z \circ \Phi^{-1}|`. Mathlib (as of the pinned version) has
harmonic functions on inner product spaces (`InnerProductSpace.HarmonicOnNhd`, with the mean value
property, Liouville's theorem, and the harmonicity of the real and imaginary parts and of
$`\log|f|` away from the zeros of a holomorphic $`f`), the Poisson kernel and the Poisson
formula for discs, Jensen's formula (`AnalyticOnNhd.circleAverage_log_norm`), the maximum modulus
principle and the Phragmén–Lindelöf principles for strips, quadrants and half-planes, but no
subharmonic functions, no Poisson integral of the half-plane, no harmonic measure and no boundary
theory (Dirichlet problem, Fatou's theorem). The Mathlib-candidate modules
`CohnElkiesForMathlib/Analysis/Complex/Subharmonic/Basic.lean`,
`CohnElkiesForMathlib/Analysis/Complex/PoissonHalfPlane.lean` and
`CohnElkiesForMathlib/Analysis/Complex/Subharmonic/HalfPlane.lean` add what the proof needs:
subharmonic functions with values in $`[-\infty, \infty)` ({bpref "def_subharmonic"}[]), whose
circle averages are handled through truncations because Mathlib's convention `Real.log 0 = 0`
makes the real-valued $`\log|f|` unusable at zeros; the strong and weak maximum principles
({bpref "lemma_subharmonic_maximum_principle"}[]); the subharmonicity of $`\log|f|` from Jensen's
formula ({bpref "lemma_log_norm_subharmonic"}[]); the Poisson kernel and integral of the
half-plane with harmonicity and boundary values ({bpref "def_halfplane_poisson_kernel"}[],
{bpref "lemma_halfplane_poisson_harmonic"}[]); the extended maximum principle with a finite
exceptional set ({bpref "lemma_halfplane_extended_maximum_principle"}[]); and the Poisson
principle ({bpref "thm_halfplane_poisson_principle"}[]). The conformal transfer to the strip and
the harmonic-measure identity are {bpref "lemma_strip_harmonic_measure"}[] (module
`CohnElkies/LowerBound/StripToHalfPlane.lean`), and the report's proof of the strip principle is
{bpref "lemma_strip_poisson_principle"}[] (module `CohnElkies/LowerBound/CappedMajorization.lean`).

# Statements added in the reformalization

The original formalization proves Theorem 1.1 in full, including the passage from unrestricted
admissible functions to radial ones ({bpref "lemma_lp_radial_reduction"}[]) and the bridge to the
packing density ({bpref "thm_cohn_elkies_bound"}[]), but only an anti-self-Fourier Schwartz
obstruction in place of the sign-uncertainty results. The reformalization adds, following the
report's statements:

* Proposition 3.1 and the Schwartz case of Proposition 3.7 for both eigenvalues
  $`\varsigma \in \{-1,+1\}` ({bpref "prop_3_1"}[], {bpref "prop_3_7"}[]), through the structure
  `CohnElkies.RadialEigenfunction` (a radial eigenfunction without sign hypothesis), of which the
  former `CohnElkies.AntiSelfFourierWitness` is now the special case $`\varsigma = -1` with the
  exterior sign condition;
* the $`L^1` class $`\mathcal{E}_\varsigma(d)` with its continuous representative, the radius
  $`r(g)` and the constants $`\mathsf{A}_\pm(d)` ({bpref "def_sign_eigenfunction_class"}[],
  {bpref "def_sign_radius"}[], {bpref "def_sign_uncertainty_constant"}[]);
* the radial reduction and Schwartz approximation of Section 2.1 for integrable eigenfunctions
  ({bpref "lemma_rotational_average_nonzero"}[], {bpref "lemma_schwartz_approximation"}[]), the
  $`L^1` case of Proposition 3.7 and Theorem 1.2 ({bpref "thm_1_2"}[], {bpref "thm_1_2_upper"}[]),
  in the modules `CohnElkies.SignUncertainty.*`;
* the self-Fourier function $`f_0` with $`P_0(\zeta) = -(1+\zeta^2)` ({bpref "lemma_4_3"}[],
  {bpref "cor_4_9"}[]), obtained by making the saddle lemmas generic in the polynomial $`P`
  (`CohnElkies.IsSaddlePolynomial`, `CohnElkies.mellinProfile`,
  `CohnElkies.mellinMultiplier_mul_spectrum_neg`; module `CohnElkies.UpperBound.SelfFourier`);
* the nonemptiness of $`\mathcal{A}_d` ({bpref "lemma_admissible_nonempty"}[]) and the
  comparator statements of the main theorems (`ComparatorChallenges/CohnElkies.lean`).

Appendix A is formalized in $`L^1` generality ({bpref "prop_a_1"}[]); the strict inequality
({bpref "cor_a_plus_lt_a_minus"}[])
rests on the existence of extremizers for $`\mathsf{A}_-(d)` ({bpref "thm_cg19_1_4_existence"}[]),
which is not part of the report (see the next section).

# Existence of extremizers: deviations from Cohn–Gonçalves

The existence part of Theorem 1.4 of Cohn–Gonçalves (2019) is proved along the lines of their
§3.2, with three changes.

* *Uniform negative-mass bound.* Cohn–Gonçalves obtain $`\int_{B_{r(f_n)}} f_n \le K < 0` for the
  normalized minimizing sequence from Nazarov's uncertainty principle in Jaming's
  higher-dimensional form (alternatively from the Amrein–Berthier inequality), a quantitative
  statement with explicit constants. The formalization uses the qualitative lemma
  {bpref "lemma_fourier_eigenfunction_no_concentration"}[]: $`L^1`-normalized eigenfunctions of
  the Fourier transform have $`L^1` mass at least $`\kappa(c,R) > 0` outside any fixed ball, proved by
  contradiction from weak $`L^2` compactness ({bpref "lemma_weak_sequential_compactness"}[]) and
  the compact-support theorem ({bpref "lemma_compactly_supported_eigenfunction_zero"}[]).
* *No Mazur's lemma.* Cohn–Gonçalves upgrade the weak $`L^2` convergence of the minimizing
  sequence to convergence almost everywhere and in $`L^2` (Mazur's lemma, using the convexity of
  the class) and then apply Fatou's lemma. The formalization keeps the weak limit and reads off its
  properties by testing against explicit $`L^2` functions (indicators, $`1_K\operatorname{sign} g`)
  and smooth compactly supported functions (for the Fourier eigen-equation, through
  $`\int\widehat u\,\Phi = \int u\,\widehat\Phi`).
* *Origin correction.* Cohn–Gonçalves normalize the minimizing sequence with their Lemma 3.1
  ($`\widehat{f_n} = -f_n`, $`f_n(0) = 0`) and deduce $`f(0) = 0` for the limit from minimality.
  In the report's class $`\mathcal{E}_-(d)` both conditions are part of the definition, and the
  origin correction ({bpref "lemma_cg19_3_1_origin_correction"}[]) is applied once, to the
  continuous representative of the weak limit, which a priori only satisfies $`f(0) \ge 0`.

The infinitely-many-roots part of Theorem 1.4 is not formalized.

# Schwartz approximation with a bump mollifier

The report approximates a radial $`L^1` eigenfunction $`g` by
$`q_n = \eta_n\,(g * \kappa_n)` with the Gaussians $`\kappa_n(x) = n^de^{-\pi n^2|x|^2}`,
$`\eta_n(x) = e^{-\pi|x|^2/n^2}` ({bpref "def_schwartz_approximation"}[]). The formalization
convolves with a compactly supported normalized flat bump instead, which makes the smoothness and
the Schwartz decay of the approximant elementary, and keeps the Gaussians only on the Fourier side.

:::lemma_ "lemma_schwartz_approximation_bump" (lean := "CohnElkies.fourier_approximant_apply")
Let $`\varphi` be a smooth nonnegative radial function with compact support and
$`\int\varphi = 1`, $`\varphi_n(x) = n^d\varphi(nx)`, and let
$`g \in L^1_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})` be continuous with $`\widehat g = \varsigma g`.
Then $`q_n = (\eta_n g) * \varphi_n` is a real radial Schwartz function with
$`\widehat{q_n} = \varsigma\,(g * \kappa_n)\,\widehat{\varphi_n}`, and $`q_n \to g`,
$`\widehat{q_n} \to \varsigma g` in $`L^1`. Moreover, for a bump $`\varphi` as above, one of
$`\varphi + \varsigma\widehat\varphi` and $`\varphi(2\cdot) + \varsigma\widehat{\varphi(2\cdot)}` is a
real radial Schwartz function $`\psi_\varsigma` with $`\widehat{\psi_\varsigma} = \varsigma\psi_\varsigma`
and $`\psi_\varsigma(0) \ne 0` (the corrector of {bpref "def_schwartz_approximation"}[], in place of
the Gaussian and Hermite functions $`\psi_\pm` of the report).
:::

:::proof "lemma_schwartz_approximation_bump"
Convolution with a compactly supported smooth function of an integrable function is smooth with
all derivatives bounded; multiplied by the Gaussian factor inside $`\eta_n g` the result is a
Schwartz function ({uses "def_schwartz_approximation"}[]). The Fourier identity is the
convolution theorem $`\widehat{u * v} = \widehat u\,\widehat v` together with
$`\widehat{\eta_n g} = \kappa_n * \widehat g = \varsigma\,(\kappa_n * g)`
({uses "def_fourier_convention"}[]). Convergence: $`(\varphi_n)` and $`(\kappa_n)` are
approximate identities and $`\eta_n \to 1` boundedly, so both $`q_n \to g` and
$`\widehat{q_n} \to \varsigma g` in $`L^1` by continuity of translation in $`L^1` and dominated
convergence. The remaining steps are those of {uses "lemma_schwartz_approximation"}[].
:::
