import Verso
import VersoManual
import VersoBlueprint
import CohnElkies

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Fourier-analytic preliminaries" =>

We reduce the packing and sign-uncertainty problems to radial functions and establish the
Mellin–Fourier identities used in both bounds. Throughout, Fourier transforms use the convention
of the introduction, $`\lambda = d/2`, and a radial function and its one-variable profile are
denoted by the same symbol: $`g(x) = g(|x|)`. In the formalization the profile of a test function
$`f` is `CohnElkies.radialProfile`, $`r \mapsto f(re_1)`, and the modules of this chapter are
`CohnElkies/Radial.lean`, `CohnElkies/MellinFourier.lean`,
`CohnElkies/Radialization.lean`
and `CohnElkies/Admissible/Radialization.lean`.

# Gamma-function identities

:::lemma_ "eq_7_gamma_identities" (lean := "Complex.norm_Gamma_I_mul_sq")
For all complex $`z` away from the poles, $`\Gamma(z+1) = z\Gamma(z)` and
$`\Gamma(z)\Gamma(1-z) = \pi/\sin(\pi z)`; moreover $`\Gamma(\bar z) = \overline{\Gamma(z)}`.
Consequently, for real $`b \ne 0` (equation (7)),
$`|\Gamma(ib)|^2 = \dfrac{\pi}{b\sinh(\pi b)}`, $`|\Gamma(1/2 + ib)|^2 = \dfrac{\pi}{\cosh(\pi b)}`,
and $`|\Gamma(-ib)| = |\Gamma(ib)|`; and, iterating the recurrence,
$`\Gamma(z+k) = \Gamma(z)\prod_{j<k}(z+j)` for $`k \in \mathbb{N}`.
:::

:::proof "eq_7_gamma_identities"
The recurrence and reflection formulas are standard. Conjugation symmetry gives
$`|\Gamma(ib)|^2 = \Gamma(ib)\Gamma(-ib) = \Gamma(ib)\Gamma(1-ib)/(-ib)`, which equals
$`\pi/(-ib\sin(i\pi b)) = \pi/(b\sinh(\pi b))`, and
$`|\Gamma(1/2+ib)|^2 = \Gamma(1/2+ib)\Gamma(1/2-ib) = \pi/\sin(\pi/2 + i\pi b) = \pi/\cosh(\pi b)`.
:::

:::definition "def_digamma" (lean := "Real.digamma")
The digamma function is $`\psi = \Gamma'/\Gamma`, the logarithmic derivative of $`\Gamma`; on the
positive real axis, $`\psi = (\log\Gamma)'`. Its derivatives are the trigamma function
$`\psi'` and $`\psi''`.
:::

:::lemma_ "lemma_gamma_asymptotics" (lean := "Real.tendsto_digamma_sub_log_atTop")
With $`\psi` as in {uses "def_digamma"}[]: $`\psi(x) - \log x \to 0` as real $`x \to +\infty`,
and $`\log(x-1) \le \psi(x) \le \log x` for real $`x > 1`.
:::

:::proof "lemma_gamma_asymptotics"
$`\log\Gamma` is convex on $`(0,\infty)` with $`\log\Gamma(x+1) - \log\Gamma(x) = \log x`, so its
derivative $`\psi` satisfies $`\log(x-1) = \log\Gamma(x) - \log\Gamma(x-1) \le \psi(x) \le
\log\Gamma(x+1) - \log\Gamma(x) = \log x` for $`x > 1`; since $`\log x - \log(x-1) \to 0`, this
gives $`\psi(x) - \log x \to 0`. (The report uses the sharper Stirling expansion
$`\psi(x) = \log x - 1/(2x) + O(x^{-2})`, together with trigamma and polygamma bounds and the
Binet-type representation of $`\log\Gamma`; the formalization replaces these by explicit moment
bounds for the gamma damping density, {bpref "lemma_4_4"}[], by the Binet-type representation
{bpref "eq_45_log_gamma_integral"}[], and by polynomial decay of $`\Gamma` along vertical lines.)
:::

:::lemma_ "lemma_digamma_gauss_integral" (lean := "Real.digamma_eq_integral")
(Gauss's integral.) For real $`m > 0`, with $`\psi` as in {uses "def_digamma"}[],
$`\psi(m) = \int_0^\infty\Bigl(\dfrac{e^{-t}}{t} - \dfrac{e^{-mt}}{1 - e^{-t}}\Bigr)\,dt`,
the integrand being integrable on $`(0,\infty)`.
:::

:::proof "lemma_digamma_gauss_integral"
By the recurrence $`\psi(m+1) = \psi(m) + 1/m` and $`\psi(x) - \log x \to 0`
({uses "lemma_gamma_asymptotics"}[]), $`\psi(m) = \lim_n\bigl(\log n - \sum_{k=0}^n (m+k)^{-1}\bigr)`.
For $`n \ge 1`, Frullani's formula $`\log n = \int_0^\infty (e^{-t} - e^{-nt})/t\,dt` and
$`(m+k)^{-1} = \int_0^\infty e^{-(m+k)t}\,dt` with the geometric sum
$`\sum_{k=0}^n e^{-(m+k)t} = e^{-mt}(1 - e^{-(n+1)t})/(1 - e^{-t})` write the $`n`-th term as
$`\int_0^\infty\bigl[(e^{-t}/t - e^{-mt}/(1-e^{-t})) - e^{-nt}g(t)\bigr]dt` with
$`g(t) = 1/t - e^{-(m+1)t}/(1-e^{-t})`. Since $`0 \le g \le m + 1` on $`(0,\infty)`, the
correction is at most $`(m+1)/n` in absolute value and tends to $`0`.
:::

:::lemma_ "lemma_stirling_ball_volume" (lean := "CohnElkies.tendsto_packingGeometricRoot")
With $`v_d` from {uses "def_ball_volume"}[], $`v_d^{1/d}\sqrt d \to \sqrt{2\pi e}` as
$`d \to \infty`; equivalently $`v_d^{1/d} = (1+o(1))\sqrt{2\pi e/d}`, or
$`\log v_d/d + \log d/2 \to (\log(2\pi) + 1)/2`.
:::

:::proof "lemma_stirling_ball_volume"
By Stirling's formula,
$`\log\Gamma(d/2+1) = (d/2)\log(d/2) - d/2 + O(\log d)`, so
$`\tfrac1d\log v_d = \tfrac12\log\pi - \tfrac12\log(d/2) + \tfrac12 + O(\tfrac{\log d}{d})`, which
is $`\tfrac12\log\tfrac{2\pi e}{d} + o(1)`. Since Mathlib has Stirling's formula for factorials
but not for $`\Gamma` on the half-integers, the formalization treats even and odd dimensions
separately: $`v_{2k} = \pi^k/k!` and $`v_{2k+1} = \pi^k 2^{2k+1}k!/(2k+1)!`
(`CohnElkies.unitBallVolume_odd`), and $`\log(k!)/k - \log k \to -1`
(`Stirling.tendsto_log_factorial_div_sub_log`, from
`Stirling.tendsto_stirlingSeq_sqrt_pi`)
gives the same limit along both subsequences (`Filter.tendsto_of_even_odd`).
:::

# Radial reduction

:::group "grp_radial_reduction"
Rotational averaging, the compact-support obstruction, and Schwartz approximation of integrable
radial eigenfunctions (Section 2.1 of the report).
:::

:::definition "def_rotational_average" (lean := "CohnElkies.rotationalAverage") (parent := "grp_radial_reduction")
With normalized Haar measure on the orthogonal group $`O(d)`, the *rotational average* of a
function $`f` on $`\mathbb{R}^d` is $`\mathcal{R}f(x) = \int_{O(d)} f(Ux)\,dU`. Write
$`\mathcal{S}_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})` for the real Schwartz functions depending
only on $`|x|`, $`L^1_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})` for the radial real integrable
functions, and
$`\mathcal{A}_d^{\mathrm{rad}}`
$`= \mathcal{A}_d \cap \mathcal{S}_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})`
(see {uses "def_admissible_class"}[]).
:::

:::lemma_ "lemma_rotational_average_properties" (lean := "CohnElkies.fourier_rotationalAverage") (parent := "grp_radial_reduction")
Let $`f` be continuous and integrable on $`\mathbb{R}^d`. Then $`\mathcal{R}f`
({uses "def_rotational_average"}[]) is continuous, integrable and radial, with
$`\|\mathcal{R}f\|_1 \le \|f\|_1`, $`\widehat{\mathcal{R}f} = \mathcal{R}\widehat f`,
$`(\mathcal{R}f)(0) = f(0)` and $`\widehat{\mathcal{R}f}(0) = \widehat f(0)`. If $`f` is real, so
is $`\mathcal{R}f`; if $`f` is Schwartz, so is $`\mathcal{R}f`. If $`f \ge 0` (resp. $`f \le 0`) on
$`\{|x| \ge R\}` then so is $`\mathcal{R}f`. Consequently: if $`f \in \mathcal{A}_d` then
$`\mathcal{R}f \in \mathcal{A}_d^{\mathrm{rad}}` with the same values $`f(0)` and $`\widehat f(0)`;
if $`\widehat g = \varsigma g` then $`\widehat{\mathcal{R}g} = \varsigma\mathcal{R}g`; and
$`r(\mathcal{R}g) \le r(g)` for $`r` as in {uses "def_sign_radius"}[].
:::

:::proof "lemma_rotational_average_properties"
All statements follow from Fubini–Tonelli for the probability measure $`dU`, the invariance
$`\widehat{f \circ U} = \widehat f \circ U` for orthogonal $`U` (change of variables in
{uses "def_fourier_convention"}[]; `CohnElkies.integral_fourierCharacter_mul`),
and the fact that exterior regions $`\{|x| \ge R\}` are rotation-invariant, so pointwise sign
conditions there are preserved by averaging. Derivatives of $`\mathcal{R}f` are averages of
derivatives of $`f` (differentiation under the integral sign,
`CohnElkies.iteratedFDeriv_integral`), and the Schwartz seminorms of
$`f \circ U` equal those of $`f` (`CohnElkies.seminorm_compIsometry`), whence the
Schwartz property (`CohnElkies.schwartzAverage`). Radiality uses that $`O(d)` acts
transitively on spheres (`CohnElkies.orthogonal_transitive`).
:::

:::lemma_ "lemma_lp_radial_reduction" (lean := "CohnElkies.LP_eq_radial") (parent := "grp_radial_reduction")
$`\inf_{f \in \mathcal{A}_d} f(0)/\widehat f(0)`
$`= \inf_{f \in \mathcal{A}_d^{\mathrm{rad}}} f(0)/\widehat f(0)`.
Hence $`\mathrm{LP}_d` in {uses "def_lp"}[] is unchanged when $`\mathcal{A}_d` is replaced by
$`\mathcal{A}_d^{\mathrm{rad}}`, as in the radial formulation of Cohn and Miller.
:::

:::proof "lemma_lp_radial_reduction"
The inequality $`\le` holds since $`\mathcal{A}_d^{\mathrm{rad}} \subseteq \mathcal{A}_d`. For
$`\ge`, given $`f \in \mathcal{A}_d`, {uses "lemma_rotational_average_properties"}[] gives
$`\mathcal{R}f \in \mathcal{A}_d^{\mathrm{rad}}` with the same quotient $`f(0)/\widehat f(0)`.
:::

:::lemma_ "lemma_sign_uncertainty_radial_reduction" (lean := "CohnElkies.signUncertaintyConstant_eq_radial") (parent := "grp_radial_reduction")
The constants $`\mathsf{A}_\varsigma(d)` of {uses "def_sign_uncertainty_constant"}[] are unchanged
when the infimum is restricted to radial eigenfunctions:
$`\mathsf{A}_\varsigma(d) = \inf\{r(g) : g \in \mathcal{E}_\varsigma(d) \text{ radial}\}`.
:::

:::proof "lemma_sign_uncertainty_radial_reduction"
The inequality $`\le` is immediate, the radial eigenfunctions being a subfamily. For $`\ge`, let
$`g \in \mathcal{E}_\varsigma(d)`. If $`r(g) = \infty` there is nothing to prove; otherwise $`g` is
nonnegative outside some ball, so {uses "lemma_rotational_average_properties"}[] and
{uses "lemma_rotational_average_nonzero"}[] make $`\mathcal{R}g` a radial member of
$`\mathcal{E}_\varsigma(d)` with $`r(\mathcal{R}g) \le r(g)`
(`CohnElkies.SignEigenfunction.radialize`, `CohnElkies.SignEigenfunction.signRadius_radialize_le`).
:::

:::lemma_ "lemma_compactly_supported_eigenfunction_zero" (lean := "CohnElkies.fourier_eq_zero_of_eq_zero_outside") (parent := "grp_radial_reduction")
Let $`g \in L^1(\mathbb{R}^d)` satisfy $`\widehat g = \varsigma g` almost everywhere for some
$`\varsigma \in \{-1,+1\}`, and suppose $`g` vanishes almost everywhere outside some ball. Then
$`g = 0`. More generally, an integrable function on a finite-dimensional real inner product
space which vanishes outside a ball and whose Fourier transform vanishes outside a ball is zero
almost everywhere.
:::

:::proof "lemma_compactly_supported_eigenfunction_zero"
Because $`g` is integrable with bounded support, the integral
$`\widehat g(\zeta) = \int g(x)e^{-2\pi i x\cdot\zeta}\,dx` converges for every
$`\zeta \in \mathbb{C}^d` and defines an entire function (differentiation under the integral
sign). Its restriction to $`\mathbb{R}^d` is therefore real-analytic. By hypothesis
$`\widehat g = \varsigma g` vanishes almost everywhere outside a ball, and $`\widehat g` is
continuous, so it vanishes on a nonempty open set; the identity theorem on the connected set
$`\mathbb{R}^d` gives $`\widehat g \equiv 0`. Injectivity of the Fourier transform on $`L^1`
({uses "def_fourier_convention"}[]) yields $`g = 0`.

The formal proof of the special case runs as follows. The finite measure $`g\,dx` has an entire
moment generating function $`z \mapsto \int e^{\langle z, x\rangle}g(x)\,dx`
(`CohnElkies.analyticOnNhd_complexMGF_nnMeasure`) whose values on the imaginary axis are the
Fourier transform (`CohnElkies.complexMGF_nnMeasure`). Since $`\widehat g = g` has compact
support, this entire function vanishes on the tail of every imaginary ray, hence identically
(`CohnElkies.eq_zero_of_forall_imaginary_ray`); so $`\widehat g = 0` and $`g = 0`.
:::

:::lemma_ "lemma_rotational_average_nonzero" (lean := "CohnElkies.SignEigenfunction.rotationalAverage_ne_zero") (parent := "grp_radial_reduction")
Let $`g` be continuous, integrable and real on $`\mathbb{R}^d` with $`\widehat g = \varsigma g`,
$`g \ne 0`, and $`g(x) \ge 0` for all $`|x| \ge R`, for some $`R \ge 0`. Then $`\mathcal{R}g \ne 0`.
:::

:::proof "lemma_rotational_average_nonzero"
Suppose $`\mathcal{R}g = 0`. For $`|x| \ge R`, $`(\mathcal{R}g)(x)` is the average of $`g` over the
sphere of radius $`|x|` (the image of Haar measure under $`U \mapsto Ux` is the normalized surface
measure). The integrand is continuous and nonnegative there and the average vanishes, so $`g`
vanishes on every sphere of radius at least $`R`, i.e. outside $`B(0,R)`. Then
{uses "lemma_compactly_supported_eigenfunction_zero"}[] forces $`g = 0`, a contradiction.
:::

:::definition "def_schwartz_approximation" (lean := "CohnElkies.approximant") (parent := "grp_radial_reduction")
Let $`g \in L^1_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})` (continuous representative) satisfy
$`\widehat g = \varsigma g` and $`g(0) = 0`, $`\varsigma \in \{-1,+1\}`. Let $`\varphi` be the
normalized flat bump, $`\varphi(x) = c\,e^{-1/(1-4|x|^2)}` for $`|x| < 1/2` and $`\varphi(x) = 0`
otherwise, with $`\int\varphi = 1`. For $`n \ge 1` set
$`\varphi_n(x) = n^d\varphi(nx)`, $`\eta_n(x) = e^{-\pi|x|^2/n^2}`,
$`q_n = (\eta_n g) * \varphi_n`, $`p_n = \tfrac12(q_n + \varsigma\widehat{q_n})`,
let $`\psi_\varsigma \in \mathcal{S}_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})` satisfy
$`\widehat{\psi_\varsigma} = \varsigma\psi_\varsigma` and $`\psi_\varsigma(0) \ne 0` (for instance
$`\varphi + \varsigma\widehat\varphi` or its dilate $`x \mapsto \varphi(2x) + \varsigma\widehat{\varphi(2\cdot)}(x)`,
one of which does not vanish at the origin), and define the corrected approximants
$`g_n = p_n - \dfrac{p_n(0)}{\psi_\varsigma(0)}\,\psi_\varsigma`.
(The report convolves with the Gaussians $`\kappa_n(x) = n^de^{-\pi n^2|x|^2}` instead of
$`\varphi_n`; see the final chapter.)
:::

:::lemma_ "lemma_schwartz_approximation" (lean := "CohnElkies.exists_schwartz_approximation") (parent := "grp_radial_reduction")
In the situation of {uses "def_schwartz_approximation"}[], each $`g_n` lies in
$`\mathcal{S}_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})`, satisfies $`\widehat{g_n} = \varsigma g_n`
and $`g_n(0) = 0`, and $`g_n \to g` in $`L^1(\mathbb{R}^d)` as $`n \to \infty`.
:::

:::proof "lemma_schwartz_approximation"
Gaussian mollification: $`g * \kappa_n` is smooth with all derivatives bounded, so
$`q_n = \eta_n(g*\kappa_n)` is Schwartz; it is radial and real because $`g`, $`\kappa_n`,
$`\eta_n` are. Since $`(\kappa_n)` is an approximate identity, $`g*\kappa_n \to g` in $`L^1`, and
$`\eta_n \to 1` boundedly, so $`q_n \to g` in $`L^1`. Using $`\widehat{\kappa_n} = \eta_n` and
$`\widehat{\eta_n} = \kappa_n` ({uses "def_fourier_convention"}[]),
$`\widehat{q_n} = \widehat{\eta_n} * \widehat{g*\kappa_n} = \kappa_n * (\eta_n \widehat g)`, and
since
$`\eta_n\widehat g \to \widehat g` in $`L^1` (dominated convergence) and $`\kappa_n*` is an
approximate identity, $`\widehat{q_n} \to \widehat g = \varsigma g` in $`L^1`. Moreover
$`q_n(0) = (g*\kappa_n)(0) \to g(0) = 0` by continuity of $`g`, and
$`\widehat{q_n}(0) = \int q_n \to \int g = \widehat g(0) = \varsigma g(0) = 0`.

Since $`q_n` is radial, hence even, $`\widehat{\widehat{q_n}} = q_n`, so
$`\widehat{p_n} = \tfrac12(\widehat{q_n} + \varsigma q_n) = \varsigma p_n`; also $`p_n` is real
radial Schwartz, $`p_n \to \tfrac12(g + \varsigma\widehat g) = g` in $`L^1`, and $`p_n(0) \to 0`.

The Gaussian satisfies $`\widehat{\psi_+} = \psi_+`, and the identity
$`\widehat{|x|^2e^{-\pi|x|^2}} = (\tfrac{d}{2\pi} - |\xi|^2)e^{-\pi|\xi|^2}` gives
$`\widehat{\psi_-} = -\psi_-`. Both are real radial Schwartz with $`\psi_+(0) = 1` and
$`\psi_-(0) = -d/(4\pi)`, nonzero. Hence $`g_n` is real radial Schwartz,
$`\widehat{g_n} = \varsigma g_n`, $`g_n(0) = p_n(0) - p_n(0) = 0`, and
$`\|g_n - g\|_1 \le \|p_n - g\|_1 + |p_n(0)|\,\|\psi_\varsigma\|_1/|\psi_\varsigma(0)| \to 0`.
:::

# The radial Mellin transform

:::group "grp_radial_mellin"
The radial Mellin transform, its logarithmic-profile description, and the Mellin–Hankel functional
equation (Section 2.2 of the report).
:::

:::definition "def_sphere_area_polar" (lean := "CohnElkies.sphereArea") (parent := "grp_radial_mellin")
Set $`\lambda = d/2` and $`S_d = 2\pi^{d/2}/\Gamma(d/2)`, the area of the unit sphere
($`S_d = d\,v_d` with $`v_d` from {uses "def_ball_volume"}[]). For radial integrable $`g`, polar
integration gives $`\int_{\mathbb{R}^d} g(x)\,dx = S_d\int_0^\infty g(r)\,r^{d-1}\,dr`, and more
generally $`\int_{\mathbb{R}^d} g(x)|x|^{s-d}\,dx = S_d\int_0^\infty g(r)\,r^{s-1}\,dr` for
$`\operatorname{Re} s > 0`.
:::

For $`\rho > 0` the Fourier transform of a radial function has the Hankel representation
$`\widehat g(\rho) = 2\pi\rho^{1-d/2}\int_0^\infty g(r)J_{d/2-1}(2\pi r\rho)\,r^{d/2}\,dr`.
Because its Bessel kernel depends only on $`r\rho`, the radial Fourier transform becomes
particularly simple after a Mellin transform: it reflects the Mellin variable and multiplies by an
explicit gamma factor. The functional equation below is proved here through Gaussian pairings and
Fubini rather than through the Hankel kernel, which is the route taken by the formalization.

:::definition "def_radial_mellin" (lean := "CohnElkies.X_fℝ") (parent := "grp_radial_mellin")
For $`g \in \mathcal{S}_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})`, $`\operatorname{Re} z > 0`, and
$`t \in \mathbb{R}`, define (equation (8)) the Mellin transform of the radial profile and its
restriction to the critical line,
$`M_g(z) = \int_0^\infty g(r)\,r^{z-1}\,dr`, $`X_g(t) = M_g(\lambda - it)`,
and in the logarithmic radius $`v = \log r` the profile $`\Phi_g(v) = e^{\lambda v}g(e^v)`.
:::

:::lemma_ "lemma_log_profile_schwartz" (lean := "CohnElkies.radialMellinFrequency_eq_fourier") (parent := "grp_radial_mellin")
For $`g \in \mathcal{S}_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})`, with the notation of
{uses "def_radial_mellin"}[]: $`\Phi_g \in \mathcal{S}(\mathbb{R};\mathbb{R})`, $`M_g` is
holomorphic on $`\operatorname{Re} z > 0`,
$`X_g(t) = \int_{\mathbb{R}}\Phi_g(v)e^{-itv}\,dv`,
$`\Phi_g(v) = \dfrac{1}{2\pi}\int_{\mathbb{R}}X_g(t)e^{itv}\,dt`,
so that Mellin inversion reads
$`g(r) = \dfrac{r^{-\lambda}}{2\pi}\int_{\mathbb{R}} X_g(t)\,r^{it}\,dt`
for $`r > 0`; in particular $`g` is determined by $`X_g`. Moreover
$`\widehat g(0) = \int_{\mathbb{R}^d} g = S_d\,M_g(d)` ({uses "def_sphere_area_polar"}[]).
:::

:::proof "lemma_log_profile_schwartz"
Smoothness of $`g` at $`r = 0` gives exponential decay of $`\Phi_g` and all its derivatives as
$`v \to -\infty`, while the Schwartz decay of $`g` gives rapid decay as $`v \to +\infty`; thus
$`\Phi_g \in \mathcal{S}(\mathbb{R})`. The substitution $`r = e^v` turns $`M_g(\lambda - it)` into
the Fourier transform of $`\Phi_g`, and ordinary one-dimensional Fourier inversion gives the
second formula; rewriting it with $`r = e^v` is the inversion formula (8). Holomorphy of $`M_g`
on $`\operatorname{Re} z > 0` follows by differentiating under the integral. The last identity is
polar integration.
:::

:::theorem "eq_9_mellin_hankel" (lean := "CohnElkies.radial_fourier_mellin_strip") (parent := "grp_radial_mellin")
(Mellin–Hankel functional equation.) For
$`g \in \mathcal{S}_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})`
and $`0 < \operatorname{Re} z < d`, with $`M` as in {uses "def_radial_mellin"}[],
$`M_{\widehat g}(z) = \pi^{\lambda - z}\,\dfrac{\Gamma(z/2)}{\Gamma((d-z)/2)}\,M_g(d-z)`.
:::

:::proof "eq_9_mellin_hankel"
For $`s > 0`, the Gaussian $`\phi_s(y) = e^{-\pi|y|^2/s}` has
$`\widehat{\phi_s}(x) = s^{\lambda}e^{-\pi s|x|^2}` ({uses "def_fourier_convention"}[]), and the
pairing identity $`\int g\,\widehat{\phi_s} = \int \widehat g\,\phi_s` (Fubini;
`CohnElkies.gaussianPairing_fourier`) gives, after polar integration
({uses "def_sphere_area_polar"}[]),
$`\int_0^\infty g(r)e^{-\pi s r^2}r^{d-1}\,dr`
$`= s^{-\lambda}\int_0^\infty \widehat g(\rho)e^{-\pi\rho^2/s}\rho^{d-1}\,d\rho`.
Multiply by $`s^{w-1}` with $`0 < \operatorname{Re} w < \lambda` and integrate over
$`s \in (0,\infty)`; Tonelli applies since $`g`, $`\widehat g` are Schwartz and
$`d - 2\operatorname{Re} w > 0`. On the left,
$`\int_0^\infty s^{w-1}e^{-\pi s r^2}\,ds = \Gamma(w)(\pi r^2)^{-w}` gives
$`\Gamma(w)\pi^{-w}M_g(d-2w)`. On the right, the substitution $`s = 1/\sigma` gives
$`\int_0^\infty s^{w-\lambda-1}e^{-\pi\rho^2/s}\,ds = \Gamma(\lambda-w)(\pi\rho^2)^{w-\lambda}`,
hence $`\Gamma(\lambda-w)\pi^{w-\lambda}M_{\widehat g}(2w)` (`CohnElkies.mellin_gaussianPairing`,
`CohnElkies.mellin_gaussianPairing_fourier`). Setting $`z = 2w` and solving for
$`M_{\widehat g}(z)` yields the claim on $`0 < \operatorname{Re} z < d`; in the formalization the
intermediate identity is the Riesz pairing `CohnElkies.fourier_riesz_pairing`,
$`\Gamma((d-s)/2)\int \widehat f(\xi)|\xi|^{s-d}\,d\xi`
$`= \pi^{\lambda-s}\Gamma(s/2)\int f(x)|x|^{-s}\,dx`.
:::

:::lemma_ "lemma_mellin_continuation" (lean := "CohnElkies.radial_fourier_mellin_regularized_closed") (parent := "grp_radial_mellin")
Let $`g \in \mathcal{S}_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})` with $`g(0) = 0`. Then
$`g(r) = O(r^2)` as $`r \to 0`, and $`M_g` ({uses "def_radial_mellin"}[]) converges and is
holomorphic on $`\operatorname{Re} z > -2`. Moreover the functional equation of
{bpref "eq_9_mellin_hankel"}[], divided by the gamma factors, holds on the closed strip
$`0 \le \operatorname{Re} z \le d`:
$`\dfrac{M_{\widehat g}(z)}{\Gamma(z/2)} = \pi^{\lambda-z}\,\dfrac{M_g(d-z)}{\Gamma((d-z)/2)}`;
on $`\operatorname{Re} z = 0` the apparent pole of $`\Gamma(z/2)` at $`z = 0` is thus harmless
(if $`\widehat g(0) = 0`, it is cancelled by the zero $`M_g(d) = S_d^{-1}\widehat g(0) = 0`).
:::

:::proof "lemma_mellin_continuation"
A smooth radial function is a smooth function of $`|x|^2`, so $`g(r) = g(0) + O(r^2) = O(r^2)`;
the integral defining $`M_g(z)` therefore converges absolutely and locally uniformly for
$`\operatorname{Re} z > -2`, giving the holomorphic extension. The same applies to $`\widehat g`,
which is radial Schwartz with $`\widehat g(0) = 0`. The right-hand side of (9) is holomorphic on
$`-2 < \operatorname{Re} z < d+2` except for the simple pole of $`\Gamma(z/2)` at $`z = 0`, which
is removable because $`M_g(d) = 0` ({uses "lemma_log_profile_schwartz"}[]). Both sides agree on
$`0 < \operatorname{Re} z < d` by {uses "eq_9_mellin_hankel"}[], hence everywhere on the
connected strip by the identity theorem; the regularized form follows by continuity of both
sides on the closed strip.
:::

:::lemma_ "eq_10_critical_line" (lean := "CohnElkies.radialMellinMultiplier") (parent := "grp_radial_mellin")
The line $`\operatorname{Re} z = d/2` is fixed by the reflection $`z \mapsto d - z`. For
$`g \in \mathcal{S}_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})` and $`t \in \mathbb{R}`,
$`X_{\widehat g}(t) = m_\lambda(t)\,X_g(-t)`, where
$`m_\lambda(t) = \pi^{it}\,\dfrac{\Gamma((\lambda - it)/2)}{\Gamma((\lambda + it)/2)}`
(equation (10)), a unimodular multiplier.
:::

:::proof "eq_10_critical_line"
Evaluate {uses "eq_9_mellin_hankel"}[] at $`z = \lambda - it`, for which $`d - z = \lambda + it`
and $`X_g(-t) = M_g(\lambda + it)` ({uses "def_radial_mellin"}[]). The properties of $`m_\lambda`
follow from $`\Gamma(\bar z) = \overline{\Gamma(z)}` ({uses "eq_7_gamma_identities"}[]) and
$`|\pi^{it}| = 1`.
:::

# Subharmonic functions and the Poisson principle for the half-plane

:::group "grp_poisson_principle"
Subharmonic functions, the maximum principle, the Poisson integral of the upper half-plane and
the Poisson principle of Ahlfors, cited by the report in the proof of Lemma 3.2. Mathlib provides
harmonic functions, the Poisson formula for discs, Jensen's formula and the maximum modulus
principle, but no subharmonic functions and no Poisson theory of the half-plane; these are
developed in the modules `CohnElkiesForMathlib/Analysis/Complex/Subharmonic/Basic.lean`,
`CohnElkiesForMathlib/Analysis/Complex/PoissonHalfPlane.lean` and
`CohnElkiesForMathlib/Analysis/Complex/Subharmonic/HalfPlane.lean`.
:::

:::definition "def_subharmonic" (lean := "SubharmonicOn") (parent := "grp_poisson_principle")
A function $`u : U \to [-\infty, \infty)` on a set $`U \subseteq \mathbb{C}` is *subharmonic* on
$`U` if it is upper semicontinuous on $`U` and satisfies the sub-mean-value inequality
$`u(z) \le \dfrac{1}{2\pi}\int_0^{2\pi} u(z + re^{i\phi})\,d\phi`
for every $`z \in U` and all sufficiently small $`r > 0`; the circle average of $`u`, which may be
$`-\infty`, is the infimum over $`a \in \mathbb{R}` of the circle averages of the truncations
$`\max\{u, a\}`. Harmonic functions are subharmonic, and the sum of a subharmonic function and a
harmonic function is subharmonic.
:::

:::lemma_ "lemma_log_norm_subharmonic" (lean := "AnalyticOnNhd.subharmonicOn_log_norm") (parent := "grp_poisson_principle")
If $`f` is holomorphic on an open set $`U \subseteq \mathbb{C}`, then $`\log|f|`, with the value
$`-\infty` at the zeros of $`f`, is subharmonic on $`U` ({uses "def_subharmonic"}[]).
:::

:::proof "lemma_log_norm_subharmonic"
Upper semicontinuity follows from the continuity of $`f` and of
$`\log : [0, \infty) \to [-\infty, \infty)`. At a zero of $`f` there is nothing to prove. At a
point $`z` with $`f(z) \ne 0` take $`r > 0` with $`\{|w - z| \le r\} \subseteq U`; Jensen's
formula gives
$`\log|f(z)| = \dfrac{1}{2\pi}\int_0^{2\pi}\log|f(z + re^{i\phi})|\,d\phi - \sum_{|w - z| < r}\operatorname{ord}_w(f)\log\dfrac{r}{|w - z|}`,
the sum running over the zeros $`w` of $`f` in the open disc, and the sum is nonnegative. As
$`\log|f|` is integrable on the circle, its circle average is the infimum of the averages of its
truncations, which differ from $`\log|f|` only on the finite set of zeros of $`f` on the circle.
:::

:::lemma_ "lemma_subharmonic_maximum_principle" (lean := "SubharmonicOn.le_zero_of_limsup_frontier") (parent := "grp_poisson_principle")
Let $`\Omega \subseteq \mathbb{C}` be open, bounded and connected, and let $`u` be subharmonic on
$`\Omega` ({uses "def_subharmonic"}[]) with $`\limsup_{z \to \zeta,\ z \in \Omega} u(z) \le 0` at
every boundary point $`\zeta \in \partial\Omega`. Then $`u \le 0` on $`\Omega`.
:::

:::proof "lemma_subharmonic_maximum_principle"
Strong maximum principle: if $`u` attains its supremum $`M` over $`\Omega` at $`z_0 \in \Omega`,
then $`u = M` on $`\Omega`. Indeed, for small $`r` the sub-mean-value inequality gives
$`M = u(z_0) \le \frac{1}{2\pi}\int_0^{2\pi}\max\{u(z_0 + re^{i\phi}), a\}\,d\phi \le M` for every
$`a \le M`, so $`u = M` almost everywhere on every small circle around $`z_0`; by upper
semicontinuity the set $`\{u \ge M\}` is closed and contains, with almost every point of every
small circle, a neighbourhood of $`z_0` (every point near $`z_0` lies on such a circle, and the
set $`\{u < M\}` is open, so it cannot meet the circles only in null sets unless it is empty
near $`z_0`); hence $`\{u = M\}` is open and closed in the connected set $`\Omega`
(`SubharmonicOn.eqOn_const_of_isMaxOn`). Now let $`g(\zeta) = \limsup_{z \to \zeta,\ z \in \Omega} u(z)`
for $`\zeta \in \overline{\Omega}`: $`g` is upper semicontinuous, equals $`u` on $`\Omega` and is
at most $`0` on $`\partial\Omega`, so it attains its maximum on the compact set $`\overline{\Omega}`.
If $`u` were positive somewhere, this maximum would be positive and attained at a point of
$`\Omega`, so $`u` would be a positive constant on $`\Omega`, contradicting the boundary condition
at a point of $`\partial\Omega \ne \emptyset`.
:::

:::definition "def_halfplane_poisson_kernel" (lean := "Complex.poissonKernelHalfPlane") (parent := "grp_poisson_principle")
For $`z = a + ih` in the upper half-plane $`\mathbb{H} = \{\operatorname{Im} z > 0\}` and
$`x \in \mathbb{R}`, the Poisson kernel of $`\mathbb{H}` is
$`P(z, x) = \dfrac{1}{\pi}\,\dfrac{h}{(x - a)^2 + h^2} = \dfrac{1}{\pi}\operatorname{Im}\dfrac{1}{x - z}`,
and the Poisson integral of a boundary datum $`b : \mathbb{R} \to \mathbb{R}` with $`b(x)/(1 + x^2)`
integrable is $`P[b](z) = \int_{\mathbb{R}} P(z, x)\,b(x)\,dx`. The kernel is positive with
$`\int_{\mathbb{R}} P(z, x)\,dx = 1`, so $`P[b]` is monotone in $`b`, and
$`\inf b \le P[b] \le \sup b`.
:::

:::lemma_ "lemma_halfplane_poisson_harmonic" (lean := "Complex.harmonicOnNhd_poissonIntegralHalfPlane") (parent := "grp_poisson_principle")
For $`b : \mathbb{R} \to \mathbb{R}` with $`b(x)/(1 + x^2)` integrable, the Poisson integral
$`P[b]` ({uses "def_halfplane_poisson_kernel"}[]) is harmonic on $`\mathbb{H}`, and
$`P[b](z) \to b(x_0)` as $`z \to x_0` within $`\mathbb{H}` at every point $`x_0 \in \mathbb{R}` at
which $`b` is continuous.
:::

:::proof "lemma_halfplane_poisson_harmonic"
$`P[b]` is the imaginary part of the Nevanlinna integral
$`N[b](z) = \dfrac{1}{\pi}\int_{\mathbb{R}}\Bigl(\dfrac{1}{x - z} - \dfrac{x}{1 + x^2}\Bigr)b(x)\,dx`,
whose kernel is $`O((1 + x^2)^{-1})` locally uniformly in $`z \in \mathbb{H}`, together with its
$`z`-derivative; differentiation under the integral sign shows that $`N[b]` is holomorphic on
$`\mathbb{H}`, so $`P[b] = \operatorname{Im} N[b]` is harmonic. For the boundary values
(`Complex.tendsto_poissonIntegralHalfPlane_of_continuousAt`), given $`\varepsilon > 0` choose
$`\delta > 0` with $`|b(x) - b(x_0)| \le \varepsilon` for $`|x - x_0| < \delta`; since the kernel has
total mass $`1`, $`|P[b](z) - b(x_0)| \le \varepsilon + \int_{|x - x_0| \ge \delta} P(z, x)\,|b(x) - b(x_0)|\,dx`,
and on $`|x - x_0| \ge \delta` one has $`P(z, x) \le C\,\operatorname{Im} z\,(1 + x^2)^{-1}` for $`z`
near $`x_0`, so the last integral tends to $`0` as $`z \to x_0`.
:::

:::lemma_ "lemma_halfplane_extended_maximum_principle" (lean := "SubharmonicOn.le_zero_of_halfPlane") (parent := "grp_poisson_principle")
Let $`u` be subharmonic on $`\mathbb{H}` ({uses "def_subharmonic"}[]) and bounded above, and let
$`E \subseteq \mathbb{R}` be finite. If $`\limsup_{z \to x,\ z \in \mathbb{H}} u(z) \le 0` for every
$`x \in \mathbb{R} \setminus E`, then $`u \le 0` on $`\mathbb{H}`.
:::

:::proof "lemma_halfplane_extended_maximum_principle"
Let $`u \le M` on $`\mathbb{H}` and $`\varepsilon > 0`. The function
$`h(z) = \sum_{x_0 \in E}\log\Bigl|\dfrac{z - x_0}{z - x_0 + 2i}\Bigr| - \log|z + i|`
is harmonic on $`\mathbb{H}`, nonpositive on the closed upper half-plane, tends to $`-\infty` at
the points of $`E`, and satisfies $`h(z) \le -\log(|z| - 1)` for $`|z| > 1`. Consider $`u + \varepsilon h`,
subharmonic on the half-disc $`\Omega_R = \{|z| < R\} \cap \mathbb{H}`, with $`R` so large that
$`M - \varepsilon\log(R - 2) \le 0`: at real boundary points outside $`E` its $`\limsup` is at most
$`0` because $`\varepsilon h \le 0`, at the points of $`E` because $`u \le M` and $`\varepsilon h \to -\infty`,
and at boundary points of modulus $`R` because $`u + \varepsilon h \le M - \varepsilon\log(R - 2)`
near them. The maximum principle ({uses "lemma_subharmonic_maximum_principle"}[]) gives
$`u \le -\varepsilon h` on $`\Omega_R`, hence on $`\mathbb{H}`, for every $`\varepsilon > 0`; let
$`\varepsilon \to 0`.
:::

:::theorem "thm_halfplane_poisson_principle" (lean := "SubharmonicOn.le_poissonIntegralHalfPlane") (parent := "grp_poisson_principle")
(Poisson principle for the upper half-plane.) Let $`u` be subharmonic on $`\mathbb{H}`
({uses "def_subharmonic"}[]) and bounded above, let $`b : \mathbb{R} \to \mathbb{R}` with
$`b(x)/(1 + x^2)` integrable be continuous outside a finite set $`E \subseteq \mathbb{R}`, and
suppose $`\limsup_{z \to x,\ z \in \mathbb{H}} u(z) \le b(x)` for every $`x \in \mathbb{R} \setminus E`.
Then $`u \le P[b]` on $`\mathbb{H}` ({uses "def_halfplane_poisson_kernel"}[]).
:::

:::proof "thm_halfplane_poisson_principle"
For $`n \in \mathbb{N}` the truncation $`b_n = \max\{b, -n\}` is bounded below, so $`P[b_n] \ge -n`
and $`u - P[b_n]` is subharmonic on $`\mathbb{H}` ({uses "lemma_halfplane_poisson_harmonic"}[]) and
bounded above by $`M + n`. At a real point $`x \notin E`,
$`\limsup u \le b(x) \le b_n(x) = \lim P[b_n]`, so $`u \le P[b_n]` on $`\mathbb{H}` by the extended
maximum principle ({uses "lemma_halfplane_extended_maximum_principle"}[]). Finally
$`P[b_n] \downarrow P[b]` as $`n \to \infty` by monotone convergence.
:::

:::corollary "cor_halfplane_poisson_principle_log" (lean := "AnalyticOnNhd.log_norm_le_poissonIntegralHalfPlane") (parent := "grp_poisson_principle")
Let $`f` be holomorphic and bounded on $`\mathbb{H}`, let $`b : \mathbb{R} \to \mathbb{R}` with
$`b(x)/(1 + x^2)` integrable be continuous outside a finite set $`E \subseteq \mathbb{R}`, and
suppose $`\limsup_{z \to x,\ z \in \mathbb{H}}\log|f(z)| \le b(x)` for every $`x \in \mathbb{R} \setminus E`.
Then $`|f| \le e^{P[b]}` on $`\mathbb{H}` ({uses "def_halfplane_poisson_kernel"}[]).
:::

:::proof "cor_halfplane_poisson_principle_log"
Apply {uses "thm_halfplane_poisson_principle"}[] to $`u = \log|f|`, which is subharmonic by
{uses "lemma_log_norm_subharmonic"}[] and bounded above by $`\log\sup|f|`.
:::
