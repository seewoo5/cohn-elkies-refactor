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

# The Poisson principle: Phragmén–Lindelöf on a strip

The report proves the interior bound of Lemma 3.2 by mapping the strip conformally onto the upper
half-plane and applying the Poisson principle to the subharmonic function $`\log|Z|`
({bpref "lemma_strip_poisson_principle"}[]). The formalization stays on the strip and uses a
maximum-modulus (Phragmén–Lindelöf) argument instead. Mathlib's `PhragmenLindelof.horizontal_strip`
cannot be applied directly, because it requires the function itself, not only its modulus, to
extend continuously to the closed strip (`DiffContOnCl`).

:::lemma_ "lemma_phragmen_lindelof_strip" (lean := "PhragmenLindelof.horizontal_strip_norm_extension")
Let $`a < b`, $`C > 0`, and let $`f : \mathbb{C} \to \mathbb{C}` be holomorphic on the open strip
$`\{a < \operatorname{Im}z < b\}`. Suppose $`|f|` has a continuous extension $`N \ge 0` to the
closed
strip, that $`N \le C` on the two boundary lines, and that
$`|f(z)| = O\bigl(\exp(B\exp(c|\operatorname{Re}z|))\bigr)` in the strip as
$`|\operatorname{Re}z| \to \infty`,
for some $`B` and some $`c < \pi/(b-a)`. Then $`N \le C` throughout the closed strip.
Formalized as `PhragmenLindelof.horizontal_strip_norm_extension`, built on the
maximum-modulus principle for a continuous extension of the modulus,
`Complex.norm_extension_le_of_forall_mem_frontier_le`.
:::

:::proof "lemma_phragmen_lindelof_strip"
Standard Phragmén–Lindelöf argument on the strip: multiply by $`\exp(-\eta\cosh(c'(z - z_0)))`-type
factors with $`c < c' < \pi/(b-a)` to kill the growth, apply the maximum-modulus principle on large
rectangles, and let the auxiliary parameter tend to zero. The distinction between continuity of
$`f` and continuity of its modulus matters: only the modulus is assumed to extend continuously,
so the maximum-modulus principle on the rectangles is applied to $`N` rather than to $`f`
(`Complex.norm_extension_le_of_forall_mem_frontier_le`).
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
Formalized as `CohnElkies.norm_Z_g_le_exp_integral_of_cap`, which assumes the capped boundary
bound $`|Z(y - i\lambda)| \le e^{h_{\lambda,D}(y)}`, together with
`CohnElkies.exists_norm_Z_g_bottom_le_exp_h_ℓD` (that bound holds for all $`D \ge D_0`) and
`CohnElkies.exists_capped_poisson_majorization` (their combination); the capped majorant is
`CohnElkies.h_ℓD`.
:::

:::proof "lemma_3_2_capped"
For $`z \in \mathbb{C}` and $`y \in \mathbb{R}` the holomorphic Poisson kernel
$`K_\lambda(z,y)`
$`= \dfrac{i}{4\lambda}\,\dfrac{E + 1}{E - 1}`, $`E = e^{\pi(z-y+i\lambda)/(2\lambda)}`,
has real part $`\lambda^{-1}P_\sigma((s-y)/\lambda)` at $`z = s + i\sigma\lambda`; its
regularization $`\widetilde K_\lambda(z,y) = K_\lambda(z,y) \pm i/(4\lambda)` (sign according to
$`y \ge 0` or $`y < 0`) tends to $`0` as $`|y| \to \infty` (`CohnElkies.K'_ℓ`). Put
$`W_D(z) = \int\widetilde K_\lambda(z,y)h_{\lambda,D}(y)\,dy` (`CohnElkies.W_D`, an instance of
the outer function `CohnElkies.W_b`), a holomorphic function on the open strip with
$`\operatorname{Re}W_D(s + i\sigma\lambda) = \int P_\sigma(T)h_{\lambda,D}(s - \lambda T)\,dT`, and
with a continuous real extension $`H_D` to the closed strip (`CohnElkies.W_D_reExtension`)
satisfying $`H_D(s - i\lambda) = h_{\lambda,D}(s)` and $`H_D(s + i\lambda) = 0`
(`CohnElkies.tendsto_W_D_re_bottom`, `CohnElkies.tendsto_W_D_re_top`). Apply
{uses "lemma_phragmen_lindelof_strip"}[] to $`F_D = e^{-W_D}Z` with $`N_D = e^{-H_D}|Z|`: the
boundary estimates (16)–(17) of {bpref "lemma_3_2"}[], which are proved before the interior bound
(`CohnElkies.RadialEigenfunction.norm_Z_g_top_le_one`,
`CohnElkies.RadialEigenfunction.norm_Z_g_bottom_le_exp_h_ℓ`), give $`N_D \le 1` on both boundary
lines, and boundedness of $`Z` together with
$`|\operatorname{Re}W_D(z)| \le B(1 + |\operatorname{Re}z|)`
gives the growth condition (`CohnElkies.isBigO_exp_neg_W_D_mul_Z_g`). Hence $`N_D \le 1` on the
strip, i.e. $`|Z(z)| \le e^{\operatorname{Re}W_D(z)}` in the interior.
:::

# One-sided Riemann bound in Lemma 3.3

The report's Lemma 3.3 states the two-sided weighted error estimate (19). The formalization proves
only the one-sided upper bound that is needed later, with a unified error term for both parities
that is independent of the dimension.

:::lemma_ "lemma_3_3_one_sided" (lean := "CohnElkies.lowerGammaBoundaryLog_dimension_scaled_riemann_le")
For $`d \ge 2`, $`c > 0`, $`T \ne 0`, with $`f_T` as in {bpref "lemma_3_3"}[] and the endpoint phase
$`\Lambda(T) = -\tfrac{\pi|T|}{4} - \tfrac12\log(1 + \tfrac{T^2}{4})`
$`+ \tfrac{|T|}{2}\arctan\tfrac{|T|}{2}`
(`CohnElkies.lowerEndpointPhase`), one has the exact identity
$`-\int_0^1f_T(x)\,dx = 1 + \Lambda(T)`
(`CohnElkies.integral_lowerRiemannLog`) and the one-sided bound
$`h_\lambda(\lambda T) \le \lambda\bigl(\log(2\pi ec^2) + \Lambda(T)\bigr) + E(T)`,
$`E(T) = 3|f_T(0)| + 2|f_T(1)| + \tfrac12\log\coth\tfrac{\pi|T|}{2}`
(`CohnElkies.lowerRiemannErrorMajorant`), for $`h_\lambda` as in
{uses "def_lower_boundary_majorant"}[] with $`R = c\sqrt d`. Consequently, for $`0 \le \sigma < 1`,
$`H_\sigma(0) \le \lambda M_\sigma\bigl(\log(2\pi ec^2) + J^{\mathrm{Lean}}_\sigma\bigr) + E_\sigma`
with $`J^{\mathrm{Lean}}_\sigma = \int(P_\sigma/M_\sigma)\Lambda` and $`E_\sigma = \int P_\sigma E`
finite and independent of $`d` and $`c`
(`CohnElkies.lowerStripPoissonMajorant_dimension_central_bound`); since
$`J_\sigma = 1 + J^{\mathrm{Lean}}_\sigma`, this is the upper half of (20) with an $`O_\sigma(1)`
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
$`K(u,t) = \dfrac{(1 - e^{-t})\cos(ut) - te^{-t}}{t^2}` (`CohnElkies.wallisPhaseKernel`, the real
part of the complex Frullani kernel `Frullani.shiftedCexpKernel`). Then
$`\int_0^\infty K(u,t)\,dt = 1 + \Lambda(2u)` for every $`u`
(`CohnElkies.integral_wallisPhaseKernel_zero`),
$`\int_{\mathbb{R}}p(u)K(u,t)\,du = \dfrac{e^{-t}(1 - e^{-t})}{t(1 + e^{-t})}` for every $`t > 0`
(`CohnElkies.integral_poissonLogistic_mul_wallisPhaseKernel`, with the Laplace kernel
`Real.Wallis.laplaceKernel`), and consequently
$`\int_{\mathbb{R}}p(u)\bigl(1 + \Lambda(2u)\bigr)\,du = \log\dfrac{\pi}{2}`,
$`\int_{\mathbb{R}}p(u)\Lambda(2u)\,du = \log\dfrac{\pi}{2} - 1`
(`CohnElkies.integral_poissonLogistic_one_add_lowerEndpointPhase`,
`CohnElkies.integral_poissonLogistic_lowerEndpointPhase`).
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
$`H_\sigma`
from {uses "def_strip_poisson_kernel"}[] and $`R = c\sqrt d`. Consequently
$`\int_{\mathbb{R}}|Z(s + i\sigma\lambda)|\,ds \le CJ\lambda e^{-\gamma\lambda}` with
$`J = \int_{\mathbb{R}}(1 + |S|)^{-2}\,dS` (`CohnElkies.lowerInverseQuadraticMass`), which is (26)
of {bpref "lemma_3_5"}[]; the integration step is
`CohnElkies.integral_norm_le_of_quadratic_majorant`
and `CohnElkies.integral_norm_Z_g_le_of_majorant`.
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
$`(f(0)/\widehat f(0))^{1/d}/\sqrt d \ge c` (`CohnElkies.UniformAdmissibleLowerBound`), and
(b) there is an ordered $`\epsilon`-construction as in {uses "thm_1_1_upper"}[]:
$`\epsilon_0 > 0`, radii with $`R_{\epsilon,d}/\sqrt d \to \alpha_\epsilon` as $`d \to \infty` and
$`\alpha_\epsilon \to 1/\pi` as $`\epsilon \downarrow 0`, and for every $`0 < \epsilon < \epsilon_0`
and all large $`d` an admissible function of normalized cost at most $`R_{\epsilon,d}/\sqrt d`
(`CohnElkies.OrderedEpsilonUpperConstruction`). Then
$`\inf_{f \in \mathcal{A}_d^{\mathrm{rad}}}(f(0)/\widehat f(0))^{1/d}/\sqrt d \to 1/\pi`
(`CohnElkies.SharpQuotientAsymptotic`), and consequently, with {uses "def_lp"}[],
$`\mathrm{LP}_d^{1/d} \to \sqrt{e/(2\pi)}`.
Formalized as `CohnElkies.sharpQuotient_of_uniform_lower_and_ordered_upper`; the hypothesis (a)
is supplied by `CohnElkies.uniformAdmissibleLowerBound_of_signRadius` (from Proposition 3.7 and
the scaling step of Theorem 3.8), (b) by `CohnElkies.saddleOrderedUpperConstruction`, and the
passage to $`\mathrm{LP}_d^{1/d}` is `CohnElkies.sharpPackingRoot_of_sharpQuotient`; everything is
assembled in `CohnElkies.sharpAsymptotics_of_saddleSourceEventualSigns`.
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
The gamma asymptotics of {bpref "lemma_gamma_asymptotics"}[] are correspondingly replaced by the
elementary bounds $`\log(x-1) \le \psi(x) \le \log x`, explicit moment bounds for the gamma damping
density, and polynomial decay of $`\Gamma` along vertical lines.

# The digamma function

The original file defines the digamma function ad hoc, as the derivative of
$`\log \circ \Gamma` on the reals, and reproves the needed estimates. This is still the state of
{bpref "def_digamma"}[]: `Real.digamma` is that derivative, identified with the real part of
Mathlib's `Complex.digamma` by `Real.digamma_eq_complex_re`. Mathlib (as of the
pinned version) has `Complex.digamma` with its basic values and recurrence but no real digamma
function and no series or asymptotic expansions; the planned refactoring defines a real digamma
function in the project's Mathlib-candidate library and moves the estimates there.

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

Appendix A is formalized in $`L^1` generality ({bpref "prop_a_1"}[],
{bpref "cor_a_plus_le_a_minus"}[]); the strict inequality ({bpref "cor_a_plus_lt_a_minus"}[])
rests on the existence of extremizers for $`\mathsf{A}_-(d)` ({bpref "thm_cg19_1_4_existence"}[]),
proved after Cohn–Gonçalves 2019 with their quantitative uncertainty principle (Nazarov–Jaming)
replaced by a compactness argument ({bpref "lemma_fourier_eigenfunction_no_concentration"}[]).

# Schwartz approximation with a bump mollifier

The report approximates a radial $`L^1` eigenfunction $`g` by
$`q_n = \eta_n\,(g * \kappa_n)` with the Gaussians $`\kappa_n(x) = n^de^{-\pi n^2|x|^2}`,
$`\eta_n(x) = e^{-\pi|x|^2/n^2}` ({bpref "def_schwartz_approximation"}[]). The formalization
convolves with a compactly supported normalized flat bump instead, which makes the smoothness and
the Schwartz decay of the approximant elementary, and keeps the Gaussians only on the Fourier side.

:::lemma_ "lemma_schwartz_approximation_bump" (lean := "CohnElkies.fourier_approximant_apply")
Let $`\varphi` be a smooth nonnegative radial function with compact support and
$`\int\varphi = 1`, $`\varphi_n(x) = (n+1)^d\varphi((n+1)x)`, and let
$`g \in L^1_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})` be continuous with $`\widehat g = \varsigma g`.
Then $`q_n = (\eta_n g) * \varphi_n` is a real
radial Schwartz function (`CohnElkies.approximant`, via `CohnElkies.schwartzConvolution`) with
$`\widehat{q_n} = \varsigma\,(g * \kappa_n)\,\widehat{\varphi_n}`, and $`q_n \to g`,
$`\widehat{q_n} \to \varsigma g` in $`L^1` (`CohnElkies.tendsto_approximant`,
`CohnElkies.tendsto_fourier_approximant`). The corrector used to enforce $`g_n(0) = 0` is
$`\psi_\varsigma = \varphi + \varsigma\widehat\varphi` for a bump $`\varphi` (or its dilate by
$`2`), one of which has $`\psi_\varsigma(0) \ne 0` (`CohnElkies.exists_eigenTest`), in place of the
Gaussian and Hermite functions $`\psi_\pm` of the report.
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
