import Verso
import VersoManual
import VersoBlueprint
import CohnElkies

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Introduction" =>

This blueprint follows Chapter 1 of the report *Ten proofs* (OpenAI, 2026), which determines the
exact exponential growth rate of the Cohn–Elkies sphere-packing linear program and the sharp
asymptotics of the two Fourier sign-uncertainty constants. The chapters follow the report. This
introduction fixes the setting and states the main results. The next chapter proves the
Cohn–Elkies bound itself, which the report cites as an external input and which the Lean
development proves from Poisson summation. The chapter on preliminaries collects the
gamma-function identities, the radial reduction and the radial Mellin transform; the chapter on
the lower bound proves the universal obstruction (Proposition 3.1) and the packing lower bound
(Theorem 3.8); the chapter on the upper bound constructs the asymptotically optimal functions
(Theorem 4.1). The appendix compares the two sign-uncertainty constants (Proposition A.1 and
$`\mathsf{A}_+(d) \le \mathsf{A}_-(d)` are formalized, and the strict inequality is formalized
under the extremizer assumption it needs), and a final chapter records where the Lean
formalization deviates from the report. Every node names its Lean counterpart in the
`CohnElkies` library, except the extremizer assumption of Appendix A.

# The sphere-packing problem and the Cohn–Elkies linear program

Sphere packing asks how densely congruent balls can fill Euclidean space.

:::definition "def_packing_density" (lean := "SpherePackingConstant")
Let $`d \ge 1`. A *sphere packing* in $`\mathbb{R}^d` is a set of balls of radius $`1/2` whose
centers are pairwise separated by at least $`1`. Its *upper density* is the limit superior, as
$`r \to \infty`, of the proportion of the ball $`B(0,r)` covered by the packing. The maximal
sphere-packing density $`\Delta_d` is the supremum of the upper densities of all sphere packings
in $`\mathbb{R}^d`.

Formalized as `SpherePackingConstant`, built from the structure `SpherePacking` (a set of
centers together with a separation $`s > 0` such that distinct centers are at distance at least
$`s`), the proportion `SpherePacking.densityInsideRadius` of $`B(0,r)` covered by the balls of
radius $`s/2` around the centers, and its limit superior `SpherePacking.upperPackingDensity`,
all valued in $`[0,\infty]`. The formal constant is the supremum over packings of every
separation; it agrees with the report's normalization because rescaling a packing to separation
$`1` preserves its upper density ({bpref "lemma_packing_unit_separation"}[]).
:::

Throughout we use the following Fourier convention.

:::definition "def_fourier_convention" (lean := "Real.fourier_eq")
For $`f \in L^1(\mathbb{R}^d)` the Fourier transform is
$`\widehat f(\xi) = \int_{\mathbb{R}^d} f(x)\,e^{-2\pi i x\cdot\xi}\,dx` (equation (1) of the
report). With this normalisation the Gaussian $`e^{-\pi|x|^2}` is its own Fourier transform,
$`\widehat{f(a\,\cdot)}(\xi) = a^{-d}\widehat f(\xi/a)` for $`a > 0`, the transform of a real even
function is real and even, Fourier inversion $`\widehat{\widehat f}(x) = f(-x)` holds for Schwartz
functions and, almost everywhere, for $`f \in L^1` with $`\widehat f \in L^1`, and the Fourier
transform of an integrable function is continuous and bounded.

The formalization uses Mathlib's Fourier transform $`\mathcal{F}` on the inner product space
`EuclideanSpace ℝ (Fin d)`, whose defining equation `Real.fourier_eq` is exactly (1). The
listed properties are Mathlib lemmas (for instance `fourier_gaussian_innerProductSpace`
for the Gaussian) or are proved where needed: inversion for Schwartz functions is
`CohnElkies.fourier_sq_apply`, the scaling rule is `CohnElkies.fourier_dilate_apply` for the
dilation `CohnElkies.dilate`, and the transform of a real radial Schwartz function is real by
`CohnElkies.IsRealValued.fourier_of_radial` and
`CohnElkies.IsRealValued.fourier_of_radial`.
:::

:::definition "def_ball_volume" (lean := "CohnElkies.unitBallVolume")
The volume of the unit ball in $`\mathbb{R}^d` is $`v_d = \pi^{d/2}/\Gamma(d/2+1)` (equation (1)).
A ball of radius $`1/2` has volume $`v_d/2^d`. Formalized as `CohnElkies.unitBallVolume`; the
identification of $`v_d/2^d` with the Lebesgue measure of the ball of radius $`1/2` is
`PackingBounds.PackingBridge.volume_half_ball`.
:::

:::definition "def_admissible_class" (lean := "PackingBounds.FullAdmissible")
Write $`\mathcal{S}(\mathbb{R}^d;\mathbb{R})` for the real Schwartz space. The *admissible class*
is (equation (2))
$`\mathcal{A}_d = \{ f \in \mathcal{S}(\mathbb{R}^d;\mathbb{R}) :`
$`\widehat f(0) > 0,\ \widehat f \ge 0 \text{ on } \mathbb{R}^d,`
$`f \le 0 \text{ on } \{|x| \ge 1\} \}`,
with the Fourier transform of {uses "def_fourier_convention"}[].

Formalized as the structure `PackingBounds.FullAdmissible` (the comparator's definition, of
which `CohnElkies.Admissible` is an abbreviation): a complex Schwartz function with vanishing
imaginary part, real nonnegative Fourier transform, positive Fourier transform at the origin, and
nonpositive real part on $`\{|x| \ge 1\}`; no radiality is assumed. The radial subclass
$`\mathcal{A}_d^{\mathrm{rad}}` of the preliminaries is the structure `CohnElkies.RadialAdmissible`
(the same fields plus `radial`); the lower and upper bounds are proved for it and transferred to
$`\mathcal{A}_d` by the radial reduction of {bpref "lemma_lp_radial_reduction"}[].
:::

:::lemma_ "lemma_admissible_origin_pos" (lean := "CohnElkies.admissible_zero_pos")
Every $`f \in \mathcal{A}_d` (see {uses "def_admissible_class"}[]) satisfies
$`f(0) = \int_{\mathbb{R}^d} \widehat f(\xi)\,d\xi > 0`. Formalized as
`CohnElkies.admissible_zero_pos`; for an arbitrary Schwartz function with real nonnegative
Fourier transform the same argument is `test_function_positive_at_origin`.
:::

:::proof "lemma_admissible_origin_pos"
Fourier inversion for Schwartz functions ({uses "def_fourier_convention"}[]) gives
$`f(0) = \int \widehat f`. The integrand is continuous, nonnegative and strictly positive at
$`\xi = 0`, so the integral is strictly positive.
:::

:::definition "def_lp" (lean := "PackingBounds.fullLinearProgram")
The Cohn–Elkies linear-programming bound is (equation (3))
$`\mathrm{LP}_d = \dfrac{v_d}{2^d}\ \inf_{f \in \mathcal{A}_d} \dfrac{f(0)}{\widehat f(0)}`,
with $`v_d` from {uses "def_ball_volume"}[] and $`\mathcal{A}_d` from
{uses "def_admissible_class"}[]. By {uses "lemma_admissible_origin_pos"}[] every quotient is
positive, and by {uses "lemma_admissible_nonempty"}[] the infimum is taken over a nonempty set,
so $`\mathrm{LP}_d \in [0,\infty)`.

Formalized as `PackingBounds.fullLinearProgram` (abbreviated `CohnElkies.LP`), the infimum of
the set of quotients `PackingBounds.fullQuotientSet` (`CohnElkies.quotientSet`) of
`CohnElkies.quotient` over $`\mathcal{A}_d`; the infimum over the radial subclass is the same by
`CohnElkies.LP_eq_radial` ({bpref "lemma_lp_radial_reduction"}[]).
:::

:::lemma_ "lemma_admissible_nonempty" (lean := "CohnElkies.admissible_nonempty")
For every $`d \ge 1` the radial admissible class $`\mathcal{A}_d^{\mathrm{rad}}`, and hence
$`\mathcal{A}_d` ({uses "def_admissible_class"}[]), is nonempty: the autocorrelation
$`\varphi * \varphi` of the flat bump $`\varphi(x) = \exp(-1/(1 - 4|x|^2))` for $`|x| < 1/2`,
$`\varphi(x) = 0` otherwise, is admissible. Formalized as `CohnElkies.admissible_nonempty` with
the witness `CohnElkies.autocorrelationAdmissible`; consequently the set of quotients is nonempty
(`CohnElkies.quotientSet_nonempty`), which makes the infimum in {bpref "def_lp"}[] well defined.
:::

:::proof "lemma_admissible_nonempty"
The bump `CohnElkies.bump` is smooth, real, radial, nonnegative and supported in the closed ball
of radius $`1/2`, with positive integral (`CohnElkies.integral_bumpReal_pos`). Its autocorrelation
`CohnElkies.autocorrelation` is again real and radial, and it vanishes for $`|x| \ge 1` because
the supports of $`\varphi` and of $`\varphi(x - \cdot)` are then disjoint
(`CohnElkies.autocorrelation_eq_zero`). Its Fourier transform is the square $`(\widehat\varphi)^2`
({uses "def_fourier_convention"}[], `CohnElkies.fourier_autocorrelation_apply`), which is real and
nonnegative because $`\widehat\varphi` is real for the real radial function $`\varphi`, and its
value at the origin is $`(\int\varphi)^2 > 0`.
:::

:::theorem "thm_cohn_elkies_bound" (lean := "PackingBounds.PackingBridge.sphere_packing_le_admissible")
(Gorbachev; Cohn–Elkies.) For every $`d \ge 1` and every $`f \in \mathcal{A}_d`, the packing
density of {uses "def_packing_density"}[] satisfies
$`\Delta_d \le \dfrac{v_d}{2^d}\,\dfrac{f(0)}{\widehat f(0)}`. Consequently (equation (4))
$`\Delta_d \le \mathrm{LP}_d`, with $`\mathrm{LP}_d` as in {uses "def_lp"}[].

The report cites this bound as an external input; the formalization proves it. The bound for a
single function is `PackingBounds.PackingBridge.sphere_packing_le_admissible` for radial $`f`
and `LinearProgrammingBound` for an arbitrary real Schwartz $`f` with
real nonnegative Fourier transform; the consequence $`\Delta_d \le \mathrm{LP}_d` is
`PackingBounds.PackingBridge.sphere_packing_le_linear_program`, with
$`\Delta_d \in [0,\infty]` and the right-hand side coerced by `ENNReal.ofReal`.
:::

:::proof "thm_cohn_elkies_bound"
The proof occupies the next chapter. For a periodic packing, Poisson summation over its lattice
turns the sum of $`f` over differences of centers into a spectral sum whose terms are
nonnegative and whose term at the origin already gives the bound
({uses "thm_lp_bound_periodic"}[]); arbitrary packings are approximated by periodic ones
({uses "thm_periodic_packing_constant"}[]), giving {uses "thm_lp_bound"}[] in the form
$`\Delta_d \le \operatorname{vol}(B(0,1/2))\,f(0)/\widehat f(0)`. The volume of the half ball is
$`v_d/2^d` ({uses "def_ball_volume"}[]), which gives the bound for a single $`f`; taking the
infimum over $`f \in \mathcal{A}_d` ({uses "def_lp"}[]) gives $`\Delta_d \le \mathrm{LP}_d`, and
the radial reduction {uses "lemma_lp_radial_reduction"}[] identifies the radial and the full
program.
:::

The first main theorem determines the exponential rate of the linear program, as conjectured by
Afkhami-Jeddi, Cohn, Hartman, de Laat and Tajdini.

:::theorem "thm_1_1" (lean := "CohnElkies.sharpPackingRootAsymptotic")
As $`d \to \infty`, $`\mathrm{LP}_d^{1/d} \longrightarrow \sqrt{e/(2\pi)}`, where
$`\mathrm{LP}_d` is defined in {uses "def_lp"}[]. Formalized as
`CohnElkies.sharpPackingRootAsymptotic` and, in the comparator's form,
`PackingBounds.FullMain.exact_limit`; the bundle
`PackingBounds.SharpFullCohnElkiesManuscriptConclusions` collects the equivalent forms
$`\log \mathrm{LP}_d/d \to \tfrac12\log(e/(2\pi))`,
$`\mathrm{LP}_d = (\sqrt{e/(2\pi)} + o(1))^d` and
$`\inf_{f\in\mathcal{A}_d}(f(0)/\widehat f(0))^{1/d} = (1/\pi + o(1))\sqrt d`, with explicit
error terms.
:::

:::proof "thm_1_1"
Lower bound. By {uses "thm_3_8"}[] there is a sequence $`\epsilon_d \to 0` such that every
$`F \in \mathcal{A}_d` satisfies
$`F(0)/\widehat F(0) \ge (2^d/v_d)\,(\sqrt{e/(2\pi)} - \epsilon_d)^d` for all sufficiently large
$`d`. Inserting this into {uses "def_lp"}[] gives
$`\mathrm{LP}_d \ge (\sqrt{e/(2\pi)} - \epsilon_d)^d`, hence
$`\liminf_{d\to\infty} \mathrm{LP}_d^{1/d} \ge \sqrt{e/(2\pi)}`.

Upper bound. By {uses "thm_1_1_upper"}[], for every small $`\epsilon > 0` and every large $`d`
there is an admissible function of normalized cost at most $`R_{\epsilon,d}/\sqrt d`, where
$`R_{\epsilon,d}/\sqrt d \to \alpha_\epsilon` as $`d \to \infty` and $`\alpha_\epsilon \to 1/\pi`
as $`\epsilon \downarrow 0`; together with {uses "lemma_stirling_ball_volume"}[] this gives
$`\limsup_{d\to\infty}\mathrm{LP}_d^{1/d} \le \sqrt{e/(2\pi)}`. In the formalization the two
halves are not taken separately: the sandwich argument {uses "thm_1_1_sandwich"}[] combines the
uniform lower bound with the $`\epsilon`-family of upper constructions and yields the limit
$`\inf_{f\in\mathcal{A}_d}(f(0)/\widehat f(0))^{1/d}/\sqrt d \to 1/\pi` directly, from which
`CohnElkies.sharpPackingRoot_of_sharpQuotient` and Stirling's formula give the claim.
:::

:::theorem "cor_packing_exponent" (lean := "PackingBounds.PackingBridge.sphere_packing_sharp_asymptotic_upper")
$`\Delta_d \le \mathrm{LP}_d = 2^{-(\alpha_* + o(1))d}` as $`d \to \infty`, where
$`\alpha_* = \tfrac12 \log_2(2\pi/e) = 0.6044\ldots`. This improves the Kabatianskii–Levenshtein
exponent $`0.59905576\ldots`, and the matching lower bound in {uses "thm_1_1"}[] shows that no
Cohn–Elkies auxiliary function can improve this exponent. Formalized as
`PackingBounds.PackingBridge.sphere_packing_sharp_asymptotic_upper`, namely
$`\Delta_d \le (\sqrt{e/(2\pi)} + o(1))^d`; the exponent is `CohnElkies.criticalBinaryExponent`,
its positivity is `CohnElkies.criticalBinaryExponent_pos`, and the base-two form
$`\log_2\mathrm{LP}_d/d \to -\alpha_*` is `PackingBounds.FullMain.exact_binary_exponent`.
:::

:::proof "cor_packing_exponent"
Combine {uses "thm_cohn_elkies_bound"}[] with {uses "thm_1_1"}[]:
$`\mathrm{LP}_d = (\sqrt{e/(2\pi)} + o(1))^d = 2^{-(\frac12\log_2(2\pi/e) + o(1))d}`.
:::

# Fourier sign uncertainty

The packing sign conditions are related to the Bourgain–Clozel–Kahane uncertainty principle for
eventually nonnegative Fourier eigenfunctions, and to its anti-self-Fourier counterpart introduced
by Cohn and Gonçalves. The report works with the class of nonzero
$`g \in L^1(\mathbb{R}^d;\mathbb{R})` satisfying $`\widehat g = \varsigma g` and $`g(0) = 0`, where
pointwise values refer to the continuous Fourier-inversion representative. We use the following
equivalent formulation.

:::definition "def_sign_eigenfunction_class" (lean := "CohnElkies.SignEigenfunction")
Let $`\varsigma \in \{-1,+1\}`. A *sign eigenfunction* of eigenvalue $`\varsigma` is a function
$`g : \mathbb{R}^d \to \mathbb{R}` that is continuous, integrable, not identically zero, satisfies
$`\widehat g(\xi) = \varsigma\, g(\xi)` for every $`\xi \in \mathbb{R}^d` (with the convention of
{uses "def_fourier_convention"}[]), and $`g(0) = 0`. Write $`\mathcal{E}_\varsigma(d)` for the set
of such functions.

This is equivalent to the report's formulation. If an $`L^1` class $`g` satisfies
$`\widehat g = \varsigma g` almost everywhere, then $`\widehat g \in L^1`, and Fourier inversion
gives $`g = \varsigma\,\widehat{g}` almost everywhere; the right-hand side is continuous and
bounded, so $`g` has a continuous representative, which is unique because two continuous
functions that agree almost everywhere agree everywhere, and this representative satisfies
$`\widehat g = \varsigma g` pointwise. Conversely, a continuous integrable $`g` with
$`\widehat g = \varsigma g` pointwise defines such an $`L^1` class. All pointwise values and sign
conditions below refer to this representative.

Formalized as the structure `CohnElkies.SignEigenfunction d ς`, where the eigenvalue is a unit
$`\varsigma` of $`\mathbb{Z}` (`ς : ℤˣ`): a real integrable function `toFun` on $`\mathbb{R}^d`,
not identically zero, vanishing at the origin, whose Fourier transform equals $`\varsigma g` at
every point. Requiring the identity everywhere rather than almost everywhere singles out the
continuous representative, as explained above.
:::

:::definition "def_sign_radius" (lean := "CohnElkies.signRadius")
For $`g : \mathbb{R}^d \to \mathbb{R}` define the *last-sign radius* (equation (5))
$`r(g) = \inf\{ R \ge 0 : g(x) \ge 0 \text{ for all } |x| \ge R \} \in [0,\infty]`,
with $`r(g) = \infty` when no such radius exists. Formalized as `CohnElkies.signRadius`, valued
in `ℝ≥0∞` with $`\top` in the role of $`\infty`.
:::

:::definition "def_sign_uncertainty_constant" (lean := "CohnElkies.signUncertaintyConstant")
For $`\varsigma \in \{-1,+1\}` and $`d \ge 1` define (equation (6))
$`\mathsf{A}_\varsigma(d) = \inf\{ r(g) : g \in \mathcal{E}_\varsigma(d) \} \in [0,\infty]`,
with $`r(g)` from {uses "def_sign_radius"}[] and $`\mathcal{E}_\varsigma(d)` from
{uses "def_sign_eigenfunction_class"}[]. The signs $`+1` and $`-1` give the original
(Bourgain–Clozel–Kahane) and the complementary (Cohn–Gonçalves) uncertainty problems.
Formalized as `CohnElkies.signUncertaintyConstant ς d`, the infimum in `ℝ≥0∞` of the sign
radii of all `g : SignEigenfunction d ς`.
:::

:::theorem "thm_1_2" (lean := "CohnElkies.signUncertaintyConstant_div_sqrt_tendsto")
The sign-uncertainty constants of {uses "def_sign_uncertainty_constant"}[] satisfy
$`\lim_{d\to\infty} \mathsf{A}_+(d)/\sqrt d = \lim_{d\to\infty} \mathsf{A}_-(d)/\sqrt d = 1/\pi`.
In particular $`\mathsf{A}_\pm(d) < \infty` for all sufficiently large $`d`. Formalized as
`CohnElkies.signUncertaintyConstant_div_sqrt_tendsto` (module `CohnElkies.SignUncertainty.Main`):
the convergence in $`[0,\infty]` of `signUncertaintyConstant ς d / ENNReal.ofReal √d` to
$`1/\pi`, which is the statement of the comparator challenge `ComparatorChallenges/CohnElkies.lean`;
the finiteness is `CohnElkies.eventually_signUncertaintyConstant_lt_top` and the real-valued form
is `CohnElkies.tendsto_toReal_signUncertaintyConstant_div_sqrt`.
:::

:::proof "thm_1_2"
Lower bound. Fix $`0 < c < 1/\pi` and $`\varsigma \in \{-1,+1\}`. By {uses "prop_3_7"}[] there is
$`d_0(c)` such that for $`d \ge d_0(c)` no $`g \in \mathcal{E}_\varsigma(d)` is nonnegative on
$`\{|x| \ge c\sqrt d\}`. If some $`g \in \mathcal{E}_\varsigma(d)` had $`r(g) < c\sqrt d`, the
definition {uses "def_sign_radius"}[] would give a radius $`R < c\sqrt d` with $`g \ge 0` on
$`\{|x| \ge R\} \supseteq \{|x| \ge c\sqrt d\}`, a contradiction. Hence
$`\mathsf{A}_\varsigma(d) \ge c\sqrt d` for $`d \ge d_0(c)`, and
$`\liminf_{d\to\infty} \mathsf{A}_\varsigma(d)/\sqrt d \ge 1/\pi` after letting
$`c \uparrow 1/\pi`.

Upper bound. By {uses "thm_1_2_upper"}[], $`\mathsf{A}_\varsigma(d)` is finite for large $`d` and
$`\limsup_{d\to\infty} \mathsf{A}_\varsigma(d)/\sqrt d \le 1/\pi`.
:::

Although the two asymptotics coincide, the appendix of the report shows that
$`\mathsf{A}_+(d) \le \mathsf{A}_-(d)` for every $`d`, with strict inequality whenever the infimum
defining $`\mathsf{A}_-(d)` is attained ({bpref "cor_a_plus_le_a_minus"}[] and
{bpref "cor_a_plus_lt_a_minus"}[]); formalized as
`CohnElkies.signUncertaintyConstant_one_le_neg_one` and, under the extremizer assumption,
`CohnElkies.signUncertaintyConstant_one_lt_neg_one`.

# Strategy

The proof reduces both problems to the last sign changes of Fourier eigenfunctions. Proposition
3.1 shows that a radial Schwartz function $`g` with $`\widehat g = \pm g` and $`g(0) = 0` has
exponentially little $`L^1` mass inside $`B(0, c\sqrt d)` whenever $`c < 1/\pi`. For an admissible
packing function $`F`, let $`a = (\widehat F(0)/F(0))^{1/d}` and $`h(x) = F(ax)`. Then
$`h(0) = \widehat h(0)`, while the nonzero function $`g = \widehat h - h` is anti-self-Fourier,
vanishes at the origin, and is nonnegative outside $`B(0,1/a)`. Since $`\int g = 0`, its negative
part has mass $`\|g\|_1/2`, all of which lies in this ball; the mass estimate therefore forces
$`1/a \ge (1/\pi - o(1))\sqrt d`. In the other direction, Theorem 4.1 modifies the Mellin transform
of a Gaussian to construct a Fourier pair and a self-Fourier function whose required exterior sign
conditions begin at $`(1/\pi + o(1))\sqrt d`. Stirling's formula converts the matching radius
bounds into the packing exponent $`\sqrt{e/(2\pi)}`.

In the formalization the lower bound is carried by the structure `CohnElkies.RadialEigenfunction`
(nonzero real radial Schwartz functions with $`\widehat g = \varsigma g` and $`g(0) = 0`), the
packing consequence by the scaling lemma `CohnElkies.normalizedCost_ge_of_no_antiFourierWitness`,
and the upper bound by the saddle pair `CohnElkies.fMinusFun`, `CohnElkies.fPlusFun`; the two
halves are assembled in `CohnElkies/Asymptotics/Framework.lean`.
