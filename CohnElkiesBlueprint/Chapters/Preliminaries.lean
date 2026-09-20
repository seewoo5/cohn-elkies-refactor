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

:::lemma_ "lemma_gamma_basic_identities" (lean := "Complex.Gamma_add_one, Complex.Gamma_mul_Gamma_one_sub, Complex.Gamma_conj")
For all complex $`z` away from the poles, $`\Gamma(z+1) = z\Gamma(z)` and
$`\Gamma(z)\Gamma(1-z) = \pi/\sin(\pi z)`; moreover $`\Gamma(\bar z) = \overline{\Gamma(z)}`.
:::

:::proof "lemma_gamma_basic_identities"
The recurrence, reflection and conjugation formulas are standard (Mathlib).
:::

:::lemma_ "lemma_gamma_iterated_recurrence" (lean := "Complex.Gamma_add_nat_eq_mul_prod")
Iterating the recurrence of {uses "lemma_gamma_basic_identities"}[],
$`\Gamma(z+k) = \Gamma(z)\prod_{j<k}(z+j)` for $`k \in \mathbb{N}` and $`z \notin -\mathbb{N}`.
:::

:::proof "lemma_gamma_iterated_recurrence"
Induction on $`k`.
:::

:::lemma_ "eq_7_gamma_identities" (lean := "Complex.norm_Gamma_I_mul_sq, Complex.norm_Gamma_one_half_add_I_mul_sq")
For real $`b \ne 0` (equation (7)),
$`|\Gamma(ib)|^2 = \dfrac{\pi}{b\sinh(\pi b)}`, $`|\Gamma(1/2 + ib)|^2 = \dfrac{\pi}{\cosh(\pi b)}`,
and $`|\Gamma(-ib)| = |\Gamma(ib)|`.
:::

:::proof "eq_7_gamma_identities"
Conjugation symmetry ({uses "lemma_gamma_basic_identities"}[]) gives $`|\Gamma(-ib)| = |\Gamma(ib)|` and
$`|\Gamma(ib)|^2 = \Gamma(ib)\Gamma(-ib) = \Gamma(ib)\Gamma(1-ib)/(-ib)`, which equals
$`\pi/(-ib\sin(i\pi b)) = \pi/(b\sinh(\pi b))` by the reflection formula, and
$`|\Gamma(1/2+ib)|^2 = \Gamma(1/2+ib)\Gamma(1/2-ib) = \pi/\sin(\pi/2 + i\pi b) = \pi/\cosh(\pi b)`.
:::

:::definition "def_digamma" (lean := "Real.digamma")
The digamma function is $`\psi = \Gamma'/\Gamma`, the logarithmic derivative of $`\Gamma`; on the
positive real axis, $`\psi = (\log\Gamma)'`. Its derivatives are the trigamma function
$`\psi'` and $`\psi''`. (In Lean, the real digamma function is the real part of Mathlib's
`Complex.digamma`, which equals the logarithmic derivative of `Real.Gamma`,
`Real.digamma_eq_logDeriv_Gamma`.)
:::

:::lemma_ "lemma_digamma_log_bounds" (lean := "Real.log_sub_one_le_digamma_le_log")
With $`\psi` as in {uses "def_digamma"}[], $`\log(x-1) \le \psi(x) \le \log x` for real $`x > 1`.
:::

:::proof "lemma_digamma_log_bounds"
$`\log\Gamma` is convex on $`(0,\infty)` with $`\log\Gamma(x+1) - \log\Gamma(x) = \log x`, so its
derivative $`\psi` satisfies $`\log(x-1) = \log\Gamma(x) - \log\Gamma(x-1) \le \psi(x) \le
\log\Gamma(x+1) - \log\Gamma(x) = \log x` for $`x > 1`.
:::

:::lemma_ "lemma_gamma_asymptotics" (lean := "Real.tendsto_digamma_sub_log_atTop")
With $`\psi` as in {uses "def_digamma"}[], $`\psi(x) - \log x \to 0` as real $`x \to +\infty`.
:::

:::proof "lemma_gamma_asymptotics"
By {uses "lemma_digamma_log_bounds"}[], $`\log(x-1) - \log x \le \psi(x) - \log x \le 0`, and
$`\log x - \log(x-1) \to 0`. (The report uses the sharper Stirling expansion
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

:::lemma_ "lemma_stirling_ball_volume" (lean := "CohnElkies.tendsto_normalizedVolumeLog, CohnElkies.tendsto_packingGeometricRoot")
With $`v_d` from {uses "def_ball_volume"}[], $`\log v_d/d + \log d/2 \to (\log(2\pi) + 1)/2` as
$`d \to \infty`; equivalently $`v_d^{1/d}\sqrt d \to \sqrt{2\pi e}`, i.e.
$`v_d^{1/d} = (1+o(1))\sqrt{2\pi e/d}`, and $`(v_d/2^d)^{1/d}\sqrt d \to \sqrt{2\pi e}/2`.
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
Radial reduction
:::

Rotational averaging, the compact-support obstruction, and Schwartz approximation of integrable
radial eigenfunctions (Section 2.1 of the report).

:::definition "def_rotational_average" (lean := "CohnElkies.rotationalAverage") (parent := "grp_radial_reduction")
With normalized Haar measure on the orthogonal group $`O(d)`, the *rotational average* of a
function $`f` on $`\mathbb{R}^d` is $`\mathcal{R}f(x) = \int_{O(d)} f(Ux)\,dU`.
:::

:::definition "def_radial_admissible_class" (lean := "CohnElkies.IsRadial, CohnElkies.RadialAdmissible") (parent := "grp_radial_reduction")
A function on $`\mathbb{R}^d` is *radial* if it depends only on $`|x|`. Write
$`\mathcal{S}_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})` for the real radial Schwartz functions,
$`L^1_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})` for the radial real integrable functions, and
$`\mathcal{A}_d^{\mathrm{rad}}`
$`= \mathcal{A}_d \cap \mathcal{S}_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})`
for the radial admissible class (see {uses "def_admissible_class"}[]).
:::

:::lemma_ "lemma_rotational_average_basic" (lean := "CohnElkies.continuous_rotationalAverage, CohnElkies.integrable_rotationalAverage, CohnElkies.rotationalAverage_eq_of_norm_eq, CohnElkies.integral_norm_rotationalAverage_le, CohnElkies.rotationalAverage_zero, CohnElkies.rotationalAverage_im_eq_zero") (parent := "grp_radial_reduction")
Let $`f` be continuous and integrable on $`\mathbb{R}^d`. Then $`\mathcal{R}f`
({uses "def_rotational_average"}[]) is continuous, integrable and radial
({uses "def_radial_admissible_class"}[]), with $`\|\mathcal{R}f\|_1 \le \|f\|_1` and
$`(\mathcal{R}f)(0) = f(0)`; if $`f` is real, so is $`\mathcal{R}f`.
:::

:::proof "lemma_rotational_average_basic"
Continuity and integrability follow from Fubini–Tonelli for the probability measure $`dU`, as
does $`\|\mathcal{R}f\|_1 \le \int_{O(d)}\|f \circ U\|_1\,dU = \|f\|_1`; $`U0 = 0` gives the value
at the origin, and the average of a real function is real. Radiality uses that $`O(d)` acts
transitively on spheres (`CohnElkies.orthogonal_transitive`) and that $`dU` is right invariant,
so $`\mathcal{R}f(Ax) = \mathcal{R}f(x)` for $`A \in O(d)`.
:::

:::lemma_ "lemma_rotational_average_properties" (lean := "CohnElkies.fourier_rotationalAverage") (parent := "grp_radial_reduction")
Let $`f` be continuous and integrable on $`\mathbb{R}^d`. Then
$`\widehat{\mathcal{R}f} = \mathcal{R}\widehat f` ({uses "def_rotational_average"}[]); in
particular $`\widehat{\mathcal{R}f}(0) = \widehat f(0)` by {uses "lemma_rotational_average_basic"}[].
:::

:::proof "lemma_rotational_average_properties"
Fubini and the invariance $`\widehat{f \circ U} = \widehat f \circ U` for orthogonal $`U`
(change of variables in {uses "def_fourier_convention"}[];
`CohnElkies.integral_fourierCharacter_mul`).
:::

:::lemma_ "lemma_rotational_average_schwartz" (lean := "CohnElkies.rotationalAverageSchwartz, CohnElkies.fourier_rotationalAverageSchwartz") (parent := "grp_radial_reduction")
If $`f` is Schwartz, so is $`\mathcal{R}f` ({uses "def_rotational_average"}[]), and
$`\widehat{\mathcal{R}f} = \mathcal{R}\widehat f` as Schwartz functions.
:::

:::proof "lemma_rotational_average_schwartz"
Derivatives of $`\mathcal{R}f` are averages of derivatives of $`f` (differentiation under the
integral sign, `CohnElkies.iteratedFDeriv_integral`), and the Schwartz seminorms of $`f \circ U`
equal those of $`f` (`CohnElkies.seminorm_compIsometry`), whence the Schwartz property
(`CohnElkies.schwartzAverage`); the Fourier identity is {uses "lemma_rotational_average_properties"}[].
:::

:::lemma_ "lemma_rotational_average_signs" (lean := "CohnElkies.rotationalAverage_nonneg_of_norm_le, CohnElkies.rotationalAverage_nonpos_of_le_norm") (parent := "grp_radial_reduction")
If $`f \ge 0` (resp. $`f \le 0`) on $`\{|x| \ge R\}` then so is $`\mathcal{R}f`
({uses "def_rotational_average"}[]).
:::

:::proof "lemma_rotational_average_signs"
Exterior regions $`\{|x| \ge R\}` are rotation-invariant, so pointwise sign conditions there are
preserved by averaging.
:::

:::lemma_ "lemma_rotational_average_admissible" (lean := "CohnElkies.Admissible.radialize, CohnElkies.Admissible.radialize_apply_zero, CohnElkies.Admissible.fourier_radialize_apply_zero") (parent := "grp_radial_reduction")
If $`f \in \mathcal{A}_d` then $`\mathcal{R}f \in \mathcal{A}_d^{\mathrm{rad}}`
({uses "def_radial_admissible_class"}[]) with the same values $`f(0)` and $`\widehat f(0)`.
:::

:::proof "lemma_rotational_average_admissible"
By {uses "lemma_rotational_average_schwartz"}[], {uses "lemma_rotational_average_basic"}[],
{uses "lemma_rotational_average_properties"}[] and {uses "lemma_rotational_average_signs"}[]
(applied to $`f` with $`R = 1` and to $`\widehat f` with $`R = 0`).
:::

:::lemma_ "lemma_rotational_average_eigenfunction" (lean := "CohnElkies.SignEigenfunction.radialize, CohnElkies.SignEigenfunction.signRadius_radialize_le") (parent := "grp_radial_reduction")
If $`g \in \mathcal{E}_\varsigma(d)` ({uses "def_sign_eigenfunction_class"}[]) is nonnegative
outside some ball, then $`\mathcal{R}g` is a radial element of $`\mathcal{E}_\varsigma(d)`:
$`\widehat{\mathcal{R}g} = \varsigma\mathcal{R}g`, $`\mathcal{R}g(0) = 0`, $`\mathcal{R}g \ne 0`;
and $`r(\mathcal{R}g) \le r(g)` for $`r` as in {uses "def_sign_radius"}[].
:::

:::proof "lemma_rotational_average_eigenfunction"
{uses "lemma_rotational_average_basic"}[], {uses "lemma_rotational_average_properties"}[] and
{uses "lemma_rotational_average_signs"}[] give the eigenfunction identity, the value at the
origin and $`r(\mathcal{R}g) \le r(g)`; $`\mathcal{R}g \ne 0` is
{uses "lemma_rotational_average_nonzero"}[].
:::

:::lemma_ "lemma_lp_radial_reduction" (lean := "CohnElkies.LP_eq_radial") (parent := "grp_radial_reduction")
$`\inf_{f \in \mathcal{A}_d} f(0)/\widehat f(0)`
$`= \inf_{f \in \mathcal{A}_d^{\mathrm{rad}}} f(0)/\widehat f(0)`.
Hence $`\mathrm{LP}_d` in {uses "def_lp"}[] is unchanged when $`\mathcal{A}_d` is replaced by
$`\mathcal{A}_d^{\mathrm{rad}}`, as in the radial formulation of Cohn and Miller.
:::

:::proof "lemma_lp_radial_reduction"
The inequality $`\le` holds since $`\mathcal{A}_d^{\mathrm{rad}} \subseteq \mathcal{A}_d`. For
$`\ge`, given $`f \in \mathcal{A}_d`, {uses "lemma_rotational_average_admissible"}[] gives
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
nonnegative outside some ball, so {uses "lemma_rotational_average_eigenfunction"}[] makes
$`\mathcal{R}g` a radial member of $`\mathcal{E}_\varsigma(d)` with $`r(\mathcal{R}g) \le r(g)`.
:::

:::lemma_ "lemma_compact_support_fourier_zero" (lean := "Real.fourierIntegral_eq_zero_of_eq_zero_outside_ball, Real.ae_eq_zero_of_hasCompactSupport_fourierIntegral") (parent := "grp_radial_reduction")
An integrable function on a nontrivial finite-dimensional real inner product space which
vanishes outside a ball and whose Fourier transform vanishes outside a ball has identically
vanishing Fourier transform, hence is zero almost everywhere.
:::

:::proof "lemma_compact_support_fourier_zero"
Because $`g` is integrable with bounded support, the integral
$`\widehat g(\zeta) = \int g(x)e^{-2\pi i x\cdot\zeta}\,dx` converges for every
$`\zeta \in \mathbb{C}^d` and defines an entire function (differentiation under the integral
sign). Its restriction to $`\mathbb{R}^d` is therefore real-analytic. By hypothesis
$`\widehat g` vanishes outside a ball, and it is continuous, so it vanishes on a nonempty open set; the identity theorem on the connected set
$`\mathbb{R}^d` gives $`\widehat g \equiv 0`. Injectivity of the Fourier transform on $`L^1`
({uses "def_fourier_convention"}[]) yields $`g = 0`.
:::

:::lemma_ "lemma_compactly_supported_eigenfunction_zero" (lean := "CohnElkies.fourier_eq_zero_of_eq_zero_outside") (parent := "grp_radial_reduction")
Let $`g \in L^1(\mathbb{R}^d)` satisfy $`\widehat g = \varsigma g` almost everywhere for some
$`\varsigma \in \{-1,+1\}`, and suppose $`g` vanishes almost everywhere outside some ball. Then
$`g = 0`.
:::

:::proof "lemma_compactly_supported_eigenfunction_zero"
This is a special case of {uses "lemma_compact_support_fourier_zero"}[]; the formal proof runs as follows. The finite measure $`g\,dx` has an entire
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

:::definition "def_schwartz_approximation" (lean := "CohnElkies.approximant, CohnElkies.projected") (parent := "grp_radial_reduction")
Let $`g \in L^1_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})` (continuous representative) satisfy
$`\widehat g = \varsigma g` and $`g(0) = 0`, $`\varsigma \in \{-1,+1\}`. Let $`\varphi` be the
normalized flat bump, $`\varphi(x) = c\,e^{-1/(1-4|x|^2)}` for $`|x| < 1/2` and $`\varphi(x) = 0`
otherwise, with $`\int\varphi = 1`. For $`n \ge 1` set
$`\varphi_n(x) = n^d\varphi(nx)`, $`\eta_n(x) = e^{-\pi|x|^2/n^2}`,
$`q_n = (\eta_n g) * \varphi_n`, $`p_n = \tfrac12(q_n + \varsigma\widehat{q_n})`.
(The report convolves with the Gaussians $`\kappa_n(x) = n^de^{-\pi n^2|x|^2}` instead of
$`\varphi_n`; see the final chapter.)
:::

:::lemma_ "lemma_approximant_properties" (lean := "CohnElkies.approximant_real, CohnElkies.approximant_radial, CohnElkies.fourier_approximant_apply, CohnElkies.tendsto_approximant, CohnElkies.tendsto_fourier_approximant") (parent := "grp_radial_reduction")
In the situation of {uses "def_schwartz_approximation"}[], $`q_n` is a real radial Schwartz
function with $`\widehat{q_n} = \varsigma\,(g * \kappa_n)\,\widehat{\varphi_n}`, and $`q_n \to g`,
$`\widehat{q_n} \to \varsigma g` in $`L^1` as $`n \to \infty`.
:::

:::proof "lemma_approximant_properties"
Mollification of the integrable function $`\eta_ng` by the smooth compactly supported
$`\varphi_n` is smooth with all derivatives bounded, and $`\eta_n` decays like a Gaussian, so
$`q_n` is Schwartz; it is radial and real because $`g`, $`\varphi_n`, $`\eta_n` are. Since
$`(\varphi_n)` is an approximate identity, $`(\eta_ng)*\varphi_n \to g` in $`L^1` (as
$`\eta_n \to 1` boundedly). Using $`\widehat{\eta_n} = \kappa_n` ({uses "def_fourier_convention"}[]),
$`\widehat{q_n} = \widehat{\eta_ng}\,\widehat{\varphi_n} = (\kappa_n * \widehat g)\widehat{\varphi_n} = \varsigma(g*\kappa_n)\widehat{\varphi_n}`,
and since $`g*\kappa_n \to g` in $`L^1` and $`\widehat{\varphi_n} \to 1` boundedly,
$`\widehat{q_n} \to \varsigma g` in $`L^1`.
:::

:::lemma_ "lemma_projected_properties" (lean := "CohnElkies.projected_real, CohnElkies.projected_radial, CohnElkies.fourier_projected, CohnElkies.tendsto_projected, CohnElkies.tendsto_projected_zero") (parent := "grp_radial_reduction")
In the situation of {uses "def_schwartz_approximation"}[], $`p_n` is a real radial Schwartz
function with $`\widehat{p_n} = \varsigma p_n`, $`p_n \to g` in $`L^1` and $`p_n(0) \to 0`.
:::

:::proof "lemma_projected_properties"
Since $`q_n` is radial, hence even, $`\widehat{\widehat{q_n}} = q_n`, so
$`\widehat{p_n} = \tfrac12(\widehat{q_n} + \varsigma q_n) = \varsigma p_n`; $`p_n` is real radial
Schwartz by {uses "lemma_approximant_properties"}[], and
$`p_n \to \tfrac12(g + \varsigma\widehat g) = g` in $`L^1`. Moreover
$`q_n(0) = ((\eta_ng)*\varphi_n)(0) \to g(0) = 0` by continuity of $`g`, and
$`\widehat{q_n}(0) = \int q_n \to \int g = \widehat g(0) = \varsigma g(0) = 0`, so $`p_n(0) \to 0`.
:::

:::lemma_ "lemma_eigen_corrector" (lean := "CohnElkies.exists_eigenTest, CohnElkies.eigenProjection") (parent := "grp_radial_reduction")
For $`\varsigma \in \{-1,+1\}` there is $`\psi_\varsigma \in \mathcal{S}_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})`
with $`\widehat{\psi_\varsigma} = \varsigma\psi_\varsigma` and $`\psi_\varsigma(0) \ne 0`: one of
$`\varphi + \varsigma\widehat\varphi` and $`x \mapsto \varphi(2x) + \varsigma\widehat{\varphi(2\cdot)}(x)`,
for the bump $`\varphi` of {uses "def_schwartz_approximation"}[], does not vanish at the origin.
:::

:::proof "lemma_eigen_corrector"
Both are real radial Schwartz $`\varsigma`-eigenfunctions (the bump is even). Their values at the
origin are $`\varphi(0) + \varsigma\int\varphi` and $`\varphi(0) + \varsigma2^{-d}\int\varphi`,
which cannot both vanish since $`\int\varphi = 1 > 0` and $`2^{-d} \ne 1`. (The report uses the
Gaussian $`\psi_+ = e^{-\pi|x|^2}` and the Hermite function
$`\psi_- = (|x|^2 - \tfrac{d}{4\pi})e^{-\pi|x|^2}` instead.)
:::

:::lemma_ "lemma_schwartz_approximation" (lean := "CohnElkies.exists_schwartz_approximation") (parent := "grp_radial_reduction")
In the situation of {uses "def_schwartz_approximation"}[], with $`\psi_\varsigma` from
{uses "lemma_eigen_corrector"}[], the corrected approximants
$`g_n = p_n - \dfrac{p_n(0)}{\psi_\varsigma(0)}\,\psi_\varsigma`
lie in $`\mathcal{S}_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})`, satisfy
$`\widehat{g_n} = \varsigma g_n` and $`g_n(0) = 0`, and $`g_n \to g` in $`L^1(\mathbb{R}^d)` as
$`n \to \infty`.
:::

:::proof "lemma_schwartz_approximation"
By {uses "lemma_projected_properties"}[] and {uses "lemma_eigen_corrector"}[], $`g_n` is real
radial Schwartz, $`\widehat{g_n} = \varsigma g_n`, $`g_n(0) = p_n(0) - p_n(0) = 0`, and
$`\|g_n - g\|_1 \le \|p_n - g\|_1 + |p_n(0)|\,\|\psi_\varsigma\|_1/|\psi_\varsigma(0)| \to 0`.
:::

# The radial Mellin transform

:::group "grp_radial_mellin"
Radial Mellin transform
:::

The radial Mellin transform, its logarithmic-profile description, and the Mellin–Hankel functional
equation (Section 2.2 of the report).

:::definition "def_sphere_area" (lean := "CohnElkies.sphereArea") (parent := "grp_radial_mellin")
Set $`\lambda = d/2` and $`S_d = 2\pi^{d/2}/\Gamma(d/2)`, the area of the unit sphere
($`S_d = d\,v_d` with $`v_d` from {uses "def_ball_volume"}[]).
:::

:::lemma_ "lemma_polar_integration" (lean := "CohnElkies.integral_radialProfile_cpow") (parent := "grp_radial_mellin")
For radial $`g` with profile $`g(r)`, polar integration gives
$`\int_{\mathbb{R}^d} g(x)|x|^{s-d}\,dx = S_d\int_0^\infty g(r)\,r^{s-1}\,dr` whenever either
side converges absolutely, with $`S_d` from {uses "def_sphere_area"}[]; in particular
$`\int_{\mathbb{R}^d} g(x)\,dx = S_d\int_0^\infty g(r)\,r^{d-1}\,dr` for integrable radial $`g`.
:::

:::proof "lemma_polar_integration"
Integration in polar coordinates: the pushforward of Lebesgue measure under $`x \mapsto |x|` has
density $`S_dr^{d-1}` (Mathlib's `MeasureTheory.integral_fun_norm_addHaar`, with
$`\operatorname{vol}(B(0,1)) = v_d = S_d/d`).
:::

For $`\rho > 0` the Fourier transform of a radial function has the Hankel representation
$`\widehat g(\rho) = 2\pi\rho^{1-d/2}\int_0^\infty g(r)J_{d/2-1}(2\pi r\rho)\,r^{d/2}\,dr`.
Because its Bessel kernel depends only on $`r\rho`, the radial Fourier transform becomes
particularly simple after a Mellin transform: it reflects the Mellin variable and multiplies by an
explicit gamma factor. The functional equation below is proved here through Gaussian pairings and
Fubini rather than through the Hankel kernel, which is the route taken by the formalization.

:::definition "def_radial_profile" (lean := "CohnElkies.radialProfile") (parent := "grp_radial_mellin")
For $`g \in \mathcal{S}_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})` the *radial profile* is
$`r \mapsto g(re_1)`, and for $`\operatorname{Re} z > 0` its Mellin transform is (equation (8))
$`M_g(z) = \int_0^\infty g(r)\,r^{z-1}\,dr`
(Mathlib's `mellin` of the profile; the integral converges absolutely since $`g` is bounded
near $`0` and rapidly decreasing).
:::

:::definition "def_radial_mellin" (lean := "CohnElkies.X_fℝ") (parent := "grp_radial_mellin")
The restriction of $`M_g` ({uses "def_radial_profile"}[]) to the critical line is (equation (8))
$`X_g(t) = M_g(\lambda - it)` for $`t \in \mathbb{R}`.
:::

:::definition "def_critical_log_profile" (lean := "CohnElkies.radialCriticalLogProfile") (parent := "grp_radial_mellin")
In the logarithmic radius $`v = \log r` the *critical log profile* of $`g` is
$`\Phi_g(v) = e^{\lambda v}g(e^v)` ({uses "def_radial_profile"}[]). (The formalization uses the
reflected variable, $`u = -v`: `radialCriticalLogProfile` is $`u \mapsto e^{-\lambda u}g(e^{-u})`.)
:::

:::lemma_ "lemma_log_profile_schwartz" (lean := "CohnElkies.radialSchwartzProfile, CohnElkies.radialCriticalLogProfile_integrable, CohnElkies.radialCriticalLogProfile_fourier_integrable") (parent := "grp_radial_mellin")
For $`g \in \mathcal{S}_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})`, the profile
$`r \mapsto g(re_1)` is a Schwartz function on $`\mathbb{R}` and
$`\Phi_g \in \mathcal{S}(\mathbb{R};\mathbb{R})` ({uses "def_critical_log_profile"}[]); in
particular $`\Phi_g` and $`\widehat{\Phi_g}` are integrable.
:::

:::proof "lemma_log_profile_schwartz"
Smoothness of $`g` at $`r = 0` gives exponential decay of $`\Phi_g` and all its derivatives as
$`v \to -\infty`, while the Schwartz decay of $`g` gives rapid decay as $`v \to +\infty`; thus
$`\Phi_g \in \mathcal{S}(\mathbb{R})`. (The formalization proves only what is needed: the
profile is Schwartz as the composition of $`g` with the isometry $`r \mapsto re_1`, and
$`\Phi_g`, an exponential tilt of a Schwartz function, and its Fourier transform are integrable.)
:::

:::lemma_ "eq_8_mellin_fourier" (lean := "CohnElkies.radialMellinFrequency_eq_fourier, CohnElkies.radialMellinFrequency_eq_criticalLogFourier") (parent := "grp_radial_mellin")
For $`g \in \mathcal{S}_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})`, with the notation of
{uses "def_radial_mellin"}[] and {uses "def_critical_log_profile"}[],
$`X_g(t) = \int_{\mathbb{R}}\Phi_g(v)e^{-itv}\,dv`: $`X_g` is the Fourier transform of $`\Phi_g`
(at the frequency $`t/(2\pi)`, with the convention of {uses "def_fourier_convention"}[]).
:::

:::proof "eq_8_mellin_fourier"
The substitution $`r = e^v` in $`M_g(\lambda - it) = \int_0^\infty g(r)r^{\lambda-it-1}\,dr`.
:::

:::lemma_ "eq_8_mellin_inversion" (lean := "CohnElkies.radialMellinFrequency_injective, CohnElkies.criticalLogProfile_eq_fourierInv") (parent := "grp_radial_mellin")
For $`g \in \mathcal{S}_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})`,
$`\Phi_g(v) = \dfrac{1}{2\pi}\int_{\mathbb{R}}X_g(t)e^{itv}\,dt`, so that Mellin inversion reads
$`g(r) = \dfrac{r^{-\lambda}}{2\pi}\int_{\mathbb{R}} X_g(t)\,r^{it}\,dt`
for $`r > 0` ({uses "def_radial_mellin"}[], {uses "def_critical_log_profile"}[]); in particular
$`g` is determined by $`X_g`.
:::

:::proof "eq_8_mellin_inversion"
Ordinary one-dimensional Fourier inversion applied to {uses "eq_8_mellin_fourier"}[]
($`\Phi_g` and $`\widehat{\Phi_g}` are integrable by {uses "lemma_log_profile_schwartz"}[]);
rewriting it with $`r = e^v` is the inversion formula (8). Injectivity follows since a radial
function is determined by its profile.
:::

:::lemma_ "lemma_fourier_zero_mellin" (lean := "CohnElkies.fourier_zero_eq_integral, CohnElkies.integral_radialProfile_cpow") (parent := "grp_radial_mellin")
For $`g \in \mathcal{S}_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})`,
$`\widehat g(0) = \int_{\mathbb{R}^d} g = S_d\,M_g(d)` ({uses "def_radial_profile"}[],
{uses "lemma_polar_integration"}[]).
:::

:::proof "lemma_fourier_zero_mellin"
The Fourier transform at $`0` is the integral, and polar integration
({uses "lemma_polar_integration"}[]) with $`s = d`.
:::

:::theorem "eq_9_mellin_hankel" (lean := "CohnElkies.radial_fourier_mellin_strip") (parent := "grp_radial_mellin")
(Mellin–Hankel functional equation.) For
$`g \in \mathcal{S}_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})`
and $`0 < \operatorname{Re} z < d`, with $`M` as in {uses "def_radial_profile"}[],
$`M_{\widehat g}(z) = \pi^{\lambda - z}\,\dfrac{\Gamma(z/2)}{\Gamma((d-z)/2)}\,M_g(d-z)`.
:::

:::proof "eq_9_mellin_hankel"
For $`s > 0`, the Gaussian $`\phi_s(y) = e^{-\pi|y|^2/s}` has
$`\widehat{\phi_s}(x) = s^{\lambda}e^{-\pi s|x|^2}` ({uses "def_fourier_convention"}[]), and the
pairing identity $`\int g\,\widehat{\phi_s} = \int \widehat g\,\phi_s` (Fubini;
`CohnElkies.gaussianPairing_fourier`) gives, after polar integration
({uses "lemma_polar_integration"}[]),
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

:::lemma_ "lemma_radial_profile_quadratic" (lean := "CohnElkies.radialProfile_isBigO_rpow_two_zero, CohnElkies.radialProfile_mellinConvergent, CohnElkies.radialProfile_mellin_differentiableAt") (parent := "grp_radial_mellin")
Let $`g \in \mathcal{S}_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})` with $`g(0) = 0`. Then
$`g(r) = O(r^2)` as $`r \to 0`, and $`M_g` ({uses "def_radial_profile"}[]) converges and is
holomorphic on $`\operatorname{Re} z > -2`.
:::

:::proof "lemma_radial_profile_quadratic"
A smooth radial function is a smooth function of $`|x|^2`, so $`g(r) = g(0) + O(r^2) = O(r^2)`;
the integral defining $`M_g(z)` therefore converges absolutely and locally uniformly for
$`\operatorname{Re} z > -2`, giving the holomorphic extension (Mathlib's
`mellin_differentiableAt_of_isBigO_rpow`).
:::

:::lemma_ "lemma_mellin_continuation" (lean := "CohnElkies.radial_fourier_mellin_regularized_closed") (parent := "grp_radial_mellin")
Let $`g \in \mathcal{S}_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})` with $`g(0) = 0`. The
functional equation of {bpref "eq_9_mellin_hankel"}[], divided by the gamma factors, holds on the
closed strip $`0 \le \operatorname{Re} z \le d`:
$`\dfrac{M_{\widehat g}(z)}{\Gamma(z/2)} = \pi^{\lambda-z}\,\dfrac{M_g(d-z)}{\Gamma((d-z)/2)}`
({uses "def_radial_profile"}[]); on $`\operatorname{Re} z = 0` the apparent pole of
$`\Gamma(z/2)` at $`z = 0` is thus harmless (if $`\widehat g(0) = 0`, it is cancelled by the zero
$`M_g(d) = S_d^{-1}\widehat g(0) = 0`).
:::

:::proof "lemma_mellin_continuation"
By {uses "lemma_radial_profile_quadratic"}[], $`M_g` is holomorphic on
$`\operatorname{Re} z > -2`, and the same applies to $`\widehat g`, which is radial Schwartz with
$`\widehat g(0) = 0`. The right-hand side of (9) is holomorphic on
$`-2 < \operatorname{Re} z < d+2` except for the simple pole of $`\Gamma(z/2)` at $`z = 0`, which
is removable because $`M_g(d) = 0` ({uses "lemma_fourier_zero_mellin"}[]). Both sides agree on
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
follow from $`\Gamma(\bar z) = \overline{\Gamma(z)}` ({uses "lemma_gamma_basic_identities"}[]) and
$`|\pi^{it}| = 1`.
:::

# Subharmonic functions and the Poisson principle for the half-plane

:::group "grp_poisson_principle"
Poisson principle
:::

Subharmonic functions, the maximum principle, the Poisson integral of the upper half-plane and
the Poisson principle of Ahlfors, cited by the report in the proof of Lemma 3.2. Mathlib provides
harmonic functions, the Poisson formula for discs, Jensen's formula and the maximum modulus
principle, but no subharmonic functions and no Poisson theory of the half-plane; these are
developed in the modules `CohnElkiesForMathlib/Analysis/Complex/Subharmonic/Defs.lean`,
`CohnElkiesForMathlib/Analysis/Complex/Subharmonic/Basic.lean`,
`CohnElkiesForMathlib/Analysis/Complex/PoissonHalfPlane.lean` and
`CohnElkiesForMathlib/Analysis/Complex/Subharmonic/HalfPlane.lean`.

:::definition "def_subharmonic" (lean := "SubharmonicOn") (parent := "grp_poisson_principle")
A function $`u : U \to [-\infty, \infty)` on a set $`U \subseteq \mathbb{C}` is *subharmonic* on
$`U` if it is upper semicontinuous on $`U` and satisfies the sub-mean-value inequality
$`u(z) \le \dfrac{1}{2\pi}\int_0^{2\pi} u(z + re^{i\phi})\,d\phi`
for every $`z \in U` and all sufficiently small $`r > 0`; the circle average of $`u`, which may be
$`-\infty`, is the infimum over $`a \in \mathbb{R}` of the circle averages of the truncations
$`\max\{u, a\}`.
:::

:::lemma_ "lemma_harmonic_subharmonic" (lean := "InnerProductSpace.HarmonicOnNhd.subharmonicOn, SubharmonicOn.add_harmonic") (parent := "grp_poisson_principle")
Harmonic functions are subharmonic ({uses "def_subharmonic"}[]), and the sum of a subharmonic
function on an open set and a harmonic function is subharmonic.
:::

:::proof "lemma_harmonic_subharmonic"
A harmonic $`h` is continuous and satisfies the mean value property, so
$`h(z) = \frac{1}{2\pi}\int h(z + re^{i\phi})\,d\phi \le \frac{1}{2\pi}\int\max\{h, a\}(z + re^{i\phi})\,d\phi`.
For $`u + h`: the sum of an upper semicontinuous and a continuous function is upper
semicontinuous, and if $`|h| \le H` on a small circle then
$`\max\{u, a - H\} + h \le \max\{u + h, a\}` there, so the mean value property of $`h` gives
$`u(z) + h(z) \le \frac{1}{2\pi}\int\max\{u, a-H\} + \frac{1}{2\pi}\int h \le \frac{1}{2\pi}\int\max\{u + h, a\}`.
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
$`P(z, x) = \dfrac{1}{\pi}\,\dfrac{h}{(x - a)^2 + h^2} = \dfrac{1}{\pi}\operatorname{Im}\dfrac{1}{x - z}`.
:::

:::lemma_ "lemma_halfplane_poisson_kernel_properties" (lean := "Complex.poissonKernelHalfPlane_pos, Complex.integral_poissonKernelHalfPlane") (parent := "grp_poisson_principle")
For $`z \in \mathbb{H}` the kernel of {uses "def_halfplane_poisson_kernel"}[] is positive with
$`\int_{\mathbb{R}} P(z, x)\,dx = 1`.
:::

:::proof "lemma_halfplane_poisson_kernel_properties"
$`\int_{\mathbb{R}}\dfrac{h\,dx}{(x-a)^2 + h^2} = \bigl[\arctan\dfrac{x - a}{h}\bigr]_{-\infty}^{\infty} = \pi`.
:::

:::definition "def_halfplane_poisson_integral" (lean := "Complex.poissonIntegralHalfPlane") (parent := "grp_poisson_principle")
The Poisson integral of a boundary datum $`b : \mathbb{R} \to \mathbb{R}` with $`b(x)/(1 + x^2)`
integrable is $`P[b](z) = \int_{\mathbb{R}} P(z, x)\,b(x)\,dx` for $`z \in \mathbb{H}`, with the
kernel of {uses "def_halfplane_poisson_kernel"}[] (which is $`O((1 + x^2)^{-1})` for fixed $`z`).
:::

:::lemma_ "lemma_halfplane_poisson_integral_mono" (lean := "Complex.poissonIntegralHalfPlane_mono, Complex.poissonIntegralHalfPlane_le_of_le, Complex.le_poissonIntegralHalfPlane_of_le") (parent := "grp_poisson_principle")
The Poisson integral of {uses "def_halfplane_poisson_integral"}[] is monotone in $`b`, and
$`\inf b \le P[b] \le \sup b` on $`\mathbb{H}`.
:::

:::proof "lemma_halfplane_poisson_integral_mono"
The kernel is positive with total mass $`1` ({uses "lemma_halfplane_poisson_kernel_properties"}[]).
:::

:::lemma_ "lemma_halfplane_poisson_harmonic" (lean := "Complex.harmonicOnNhd_poissonIntegralHalfPlane") (parent := "grp_poisson_principle")
For $`b : \mathbb{R} \to \mathbb{R}` with $`b(x)/(1 + x^2)` integrable, the Poisson integral
$`P[b]` ({uses "def_halfplane_poisson_integral"}[]) is harmonic on $`\mathbb{H}`.
:::

:::proof "lemma_halfplane_poisson_harmonic"
$`P[b]` is the imaginary part of the Nevanlinna integral
$`N[b](z) = \dfrac{1}{\pi}\int_{\mathbb{R}}\Bigl(\dfrac{1}{x - z} - \dfrac{x}{1 + x^2}\Bigr)b(x)\,dx`,
whose kernel is $`O((1 + x^2)^{-1})` locally uniformly in $`z \in \mathbb{H}`, together with its
$`z`-derivative; differentiation under the integral sign shows that $`N[b]` is holomorphic on
$`\mathbb{H}`, so $`P[b] = \operatorname{Im} N[b]` is harmonic.
:::

:::lemma_ "lemma_halfplane_poisson_boundary_values" (lean := "Complex.tendsto_poissonIntegralHalfPlane_of_continuousAt") (parent := "grp_poisson_principle")
For $`b : \mathbb{R} \to \mathbb{R}` with $`b(x)/(1 + x^2)` integrable,
$`P[b](z) \to b(x_0)` as $`z \to x_0` within $`\mathbb{H}` at every point $`x_0 \in \mathbb{R}` at
which $`b` is continuous ({uses "def_halfplane_poisson_integral"}[]).
:::

:::proof "lemma_halfplane_poisson_boundary_values"
Given $`\varepsilon > 0` choose $`\delta > 0` with $`|b(x) - b(x_0)| \le \varepsilon` for
$`|x - x_0| < \delta`; since the kernel has total mass $`1`
({uses "lemma_halfplane_poisson_kernel_properties"}[]),
$`|P[b](z) - b(x_0)| \le \varepsilon + \int_{|x - x_0| \ge \delta} P(z, x)\,|b(x) - b(x_0)|\,dx`,
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
subharmonic ({uses "lemma_harmonic_subharmonic"}[]) on the half-disc $`\Omega_R = \{|z| < R\} \cap \mathbb{H}`, with $`R` so large that
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
Then $`u \le P[b]` on $`\mathbb{H}` ({uses "def_halfplane_poisson_integral"}[]).
:::

:::proof "thm_halfplane_poisson_principle"
For $`n \in \mathbb{N}` the truncation $`b_n = \max\{b, -n\}` is bounded below, so $`P[b_n] \ge -n`
and $`u - P[b_n]` is subharmonic on $`\mathbb{H}` ({uses "lemma_halfplane_poisson_harmonic"}[],
{uses "lemma_harmonic_subharmonic"}[]) and bounded above by $`M + n`
({uses "lemma_halfplane_poisson_integral_mono"}[]). At a real point $`x \notin E`,
$`\limsup u \le b(x) \le b_n(x) = \lim P[b_n]` ({uses "lemma_halfplane_poisson_boundary_values"}[]), so $`u \le P[b_n]` on $`\mathbb{H}` by the extended
maximum principle ({uses "lemma_halfplane_extended_maximum_principle"}[]). Finally
$`P[b_n] \downarrow P[b]` as $`n \to \infty` by monotone convergence.
:::

:::corollary "cor_halfplane_poisson_principle_log" (lean := "AnalyticOnNhd.log_norm_le_poissonIntegralHalfPlane") (parent := "grp_poisson_principle")
Let $`f` be holomorphic and bounded on $`\mathbb{H}`, let $`b : \mathbb{R} \to \mathbb{R}` with
$`b(x)/(1 + x^2)` integrable be continuous outside a finite set $`E \subseteq \mathbb{R}`, and
suppose $`\limsup_{z \to x,\ z \in \mathbb{H}}\log|f(z)| \le b(x)` for every $`x \in \mathbb{R} \setminus E`.
Then $`|f| \le e^{P[b]}` on $`\mathbb{H}` ({uses "def_halfplane_poisson_integral"}[]).
:::

:::proof "cor_halfplane_poisson_principle_log"
Apply {uses "thm_halfplane_poisson_principle"}[] to $`u = \log|f|`, which is subharmonic by
{uses "lemma_log_norm_subharmonic"}[] and bounded above by $`\log\sup|f|`.
:::
