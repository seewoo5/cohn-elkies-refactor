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
and $`|\Gamma(-ib)| = |\Gamma(ib)|`.

The recurrence, reflection and conjugation formulas are Mathlib's `Complex.Gamma_add_one`,
`Complex.Gamma_mul_Gamma_one_sub` and `Complex.Gamma_conj`. The two modulus identities are
`Complex.norm_Gamma_I_mul_sq` and `Complex.norm_Gamma_one_half_add_I_mul_sq`; the
iterated recurrences $`\Gamma(z+k) = \Gamma(z)\prod_{j<k}(z+j)` at $`z = iy/2` and
$`z = 1/2 + iy/2`, which the lower bound uses in even and odd dimension, are
`Complex.Gamma_add_nat_eq_mul_prod`, `CohnElkies.integer_gamma_product` and
`CohnElkies.half_integer_gamma_product`, and the quotient of the two modulus identities is
`Complex.log_norm_Gamma_I_mul_sub_log_norm_Gamma_one_half_add_I_mul`.
:::

:::proof "eq_7_gamma_identities"
The recurrence and reflection formulas are standard. Conjugation symmetry gives
$`|\Gamma(ib)|^2 = \Gamma(ib)\Gamma(-ib) = \Gamma(ib)\Gamma(1-ib)/(-ib)`, which equals
$`\pi/(-ib\sin(i\pi b)) = \pi/(b\sinh(\pi b))`, and
$`|\Gamma(1/2+ib)|^2 = \Gamma(1/2+ib)\Gamma(1/2-ib) = \pi/\sin(\pi/2 + i\pi b) = \pi/\cosh(\pi b)`.
:::

:::definition "def_digamma" (lean := "Real.digamma")
The digamma function is $`\psi = \Gamma'/\Gamma`, with derivatives $`\psi^{(1)} = \psi'`
(trigamma) and $`\psi^{(2)} = \psi''`. It has the series
$`\psi(z) = -\gamma_{E} + \sum_{k \ge 0}\bigl(\tfrac{1}{k+1} - \tfrac{1}{k+z}\bigr)`,
$`\psi'(z) = \sum_{k\ge 0} (k+z)^{-2}`, and in particular, for real $`a \ge 0` and $`b \ne 0`
(with $`a + ib` not a pole),
$`\operatorname{Im}\psi(a+ib) = \sum_{k \ge 0} \dfrac{b}{(k+a)^2 + b^2}`.

The formalization only needs $`\psi` on the positive real axis. It is defined there as
`Real.digamma`, the derivative of $`\log\circ\Gamma`, and identified with the real part of
Mathlib's `Complex.digamma` (the logarithmic derivative of $`\Gamma`) by
`Real.digamma_eq_complex_re`; it is continuous on $`(0,\infty)`
(`Real.continuousOn_digamma_Ioi`). The series above are not formalized: the monotonicity
statements that the report derives from the series of $`\operatorname{Im}\psi` are proved
directly from the gamma product formulas of {bpref "eq_7_gamma_identities"}[]
(`CohnElkies.lowerGammaBoundaryLog_dimension_antitoneOn`), and the trigamma and polygamma bounds
appear as explicit moment bounds ({bpref "lemma_gamma_asymptotics"}[]). Replacing the local
definition by a Mathlib `Real.digamma` is planned (see the final chapter).
:::

:::lemma_ "lemma_gamma_asymptotics" (lean := "Real.tendsto_digamma_sub_log_atTop")
With $`\psi` as in {uses "def_digamma"}[]:

(i) $`\psi(x) = \log x - \dfrac{1}{2x} + O(x^{-2})` as real $`x \to +\infty`, and
$`\log\Gamma(x+1) = x\log x - x + O(\log(2+x))` for $`x \ge 1` (Stirling).

(ii) There is an absolute constant $`C` such that for all real $`m \ge 1/2`:
$`\dfrac1m \le \psi'(m) \le \dfrac{C}{m}` and $`0 \le -\psi''(m) \le \dfrac{C}{m^2}`.

(iii) For $`\operatorname{Re} z > 0`: $`\psi'(z) = \int_0^\infty \dfrac{t e^{-zt}}{1-e^{-t}}\,dt`,
and
for $`\operatorname{Re} z > 0`, $`\operatorname{Re}(z+w) > 0`:
$`\log\Gamma(z+w) - \log\Gamma(z) - w\psi(z)`
$`= \int_0^\infty (e^{-ws} - 1 + ws)\,\dfrac{e^{-zs}}{s(1-e^{-s})}\,ds`
(Binet-type representation; the branch of $`\log\Gamma` is the one real on the positive axis).

(iv) For $`a` in a compact subset of $`\mathbb{R}` avoiding the poles and $`|b| \to \infty`:
$`\log|\Gamma(a+ib)| = (a - \tfrac12)\log|b| - \tfrac{\pi|b|}{2} + O_a(1)`, uniformly in $`a`.

The formalization proves weaker forms, sufficient for every use. For (i):
$`\psi(x) - \log x \to 0` (`Real.tendsto_digamma_sub_log_atTop`) and
$`\log(x-1) \le \psi(x) \le \log x` for $`x > 1` (`Real.log_sub_one_le_digamma_le_log`); Stirling's
formula is used only through Mathlib's `Stirling.tendsto_stirlingSeq_sqrt_pi` for factorials
(see {bpref "lemma_stirling_ball_volume"}[]). For (ii): the moments of the gamma damping
density of {bpref "eq_37_gamma_damping_density"}[] are bounded explicitly
(`CohnElkies.upperGammaMoment_bounds`, `CohnElkies.upperGammaVariance_bounds`,
`CohnElkies.upperGammaThirdMoment_bounds`), which is (51)–(52) of Lemma 4.4. For (iii): the
Binet-type representation in the form (45) is `CohnElkies.exp_G_ℓη`. For (iv): only polynomial
decay along vertical lines is needed,
$`|\operatorname{Im} z|^k|\Gamma(z)| \le \Gamma(\operatorname{Re} z + k)`
(`Complex.abs_im_pow_mul_norm_Gamma_le`, `CohnElkies.gamma_shiftedLine_polynomial_bound`),
together with the exact modulus identity $`|\Gamma(m - ib)| = \Gamma(m)e^{-D_\gamma}` of
{bpref "eq_45_log_gamma_integral"}[].
:::

:::proof "lemma_gamma_asymptotics"
All items are standard consequences of Stirling's formula and of the Malmstén–Binet integral
representation of $`\log\Gamma`; (iii) follows by subtracting the representations of
$`\log\Gamma(z+w)`, $`\log\Gamma(z)` and $`w\psi(z)`. The bounds in (ii) follow from the series
of {uses "def_digamma"}[] by comparison with integrals. In the formalization, the bounds of (i)
follow from $`\log\Gamma` being convex with $`\log\Gamma(x+1) - \log\Gamma(x) = \log x`, the
moment bounds of (ii) from $`x \le e^{x} - 1 \le x e^{x}` applied to the density
$`e^{-\eta a}/(a(1 - e^{-2a/\lambda}))`, (iii) from the Mathlib integral representation of
$`\log\Gamma`, and (iv) from the recurrence and $`|\Gamma(z)| \le \Gamma(\operatorname{Re} z)`.
:::

:::lemma_ "lemma_stirling_ball_volume" (lean := "CohnElkies.tendsto_packingGeometricRoot")
With $`v_d` from {uses "def_ball_volume"}[], $`v_d^{1/d}\sqrt d \to \sqrt{2\pi e}` as
$`d \to \infty`; equivalently $`v_d^{1/d} = (1+o(1))\sqrt{2\pi e/d}`. Formalized with the factor
$`2^{-d}` of the Cohn–Elkies bound already included, as
$`(v_d/2^d)^{1/d}\sqrt d \to \sqrt{2\pi e}/2` (`CohnElkies.tendsto_packingGeometricRoot`); the
underlying statement is $`\log v_d/d + \log d/2 \to (\log(2\pi) + 1)/2`
(`CohnElkies.tendsto_normalizedVolumeLog`, `CohnElkies.exp_normalizedVolumeLog_limit`).
:::

:::proof "lemma_stirling_ball_volume"
By Stirling ({uses "lemma_gamma_asymptotics"}[]),
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

Formalized, for Schwartz $`f`, as `CohnElkies.rotationalAverage` (the
integral of $`f(U^{-1}x)` against the Haar probability measure
`CohnElkies.radialOrthogonalHaar` of $`O(d)`), packaged as a Schwartz function
by `CohnElkies.rotationalAverageSchwartz`. Radiality is the predicate
`CohnElkies.IsRadial` (the value depends only on the norm); there are no separate types for
$`\mathcal{S}_{\mathrm{rad}}` and $`L^1_{\mathrm{rad}}`, and $`\mathcal{A}_d^{\mathrm{rad}}` is
`CohnElkies.RadialAdmissible` (the class `CohnElkies.Admissible` with the extra field `radial`).
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

The formalization covers the Schwartz case. Commutation with the Fourier transform is
`CohnElkies.fourier_rotationalAverage`; radiality, the value at the
origin, realness and the sign conditions are
`CohnElkies.rotationalAverage_eq_of_norm_eq`,
`radialSymmetrizationAverage_zero`, `radialSymmetrizationAverage_im_eq_zero`,
`radialSymmetrizationAverage_nonneg_of_nonneg` and
`radialSymmetrizationAverage_nonpos_of_le_norm` (nonpositivity outside a ball of any radius is
preserved); the Schwartz property is the construction
`CohnElkies.rotationalAverageSchwartz`; the admissibility consequence is
`CohnElkies.Admissible.radialize` with `CohnElkies.Admissible.quotient_radialize`,
`CohnElkies.Admissible.radialize_apply_zero`, `CohnElkies.Admissible.fourier_radialize_apply_zero`
and `CohnElkies.Admissible.radialize_nonpos_of_le_norm` (module
`CohnElkies/Admissible/Radialization.lean`). For continuous integrable $`g` (the
$`L^1` theory of Proposition 3.7, module `CohnElkies.SignUncertainty.Radialization`) the average
is `CohnElkies.rotationalAverage`, with `CohnElkies.fourier_rotationalAverage`
($`\widehat{\mathcal{R}g} = \mathcal{R}\widehat g`), `CohnElkies.continuous_rotationalAverage`,
`CohnElkies.integrable_rotationalAverage`, `CohnElkies.integral_norm_rotationalAverage_le`
($`\|\mathcal{R}g\|_1 \le \|g\|_1`) and, for an eigenfunction that is nonnegative outside a ball,
the eigenfunction `CohnElkies.SignEigenfunction.radialize` with
`CohnElkies.SignEigenfunction.signRadius_radialize_le` ($`r(\mathcal{R}g) \le r(g)`).
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
$`\mathcal{A}_d^{\mathrm{rad}}`, as in the radial formulation of Cohn and Miller. Formalized as
`CohnElkies.LP_eq_radial`, via the equality of the two sets of quotients
`CohnElkies.quotientSet_eq_radial` (from `CohnElkies.range_radialAdmissible_eq` and the
radialization `CohnElkies.Admissible.radialize`); likewise `CohnElkies.normalizedProgram_eq_radial`
for the normalized program.
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
Formalized as `CohnElkies.signUncertaintyConstant_eq_radial` (module
`CohnElkies.SignUncertainty.Radialization`), with the helper
`CohnElkies.exists_nonneg_outside_of_signRadius_lt_top`.
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
$`g = 0`.

Formalized as `Real.ae_eq_zero_of_hasCompactSupport_fourierIntegral` (module
`CohnElkiesForMathlib.Analysis.Fourier.CompactSupport`, on any nontrivial finite-dimensional real
inner product space; `Real.eq_zero_of_hasCompactSupport_fourierIntegral` for continuous $`f`), from
`Real.fourierIntegral_eq_zero_of_eq_zero_outside_ball`: the Fourier–Laplace transform along a ray
(`Real.fourierLaplaceRay`) is entire (`Real.differentiable_fourierLaplaceRay`) and vanishes on a
ray of the imaginary axis, so it vanishes identically
(`AnalyticOnNhd.eq_zero_of_forall_ofReal_mul_I_eq_zero`); the $`\mathbb{R}^d` form is
`CohnElkies.fourier_eq_zero_of_eq_zero_outside`. The special case used by Theorem 3.8, a real
nonnegative compactly supported Schwartz function $`g` with $`\widehat g = g` vanishes
(`CohnElkies.eq_zero_of_fourier_eq_self`), is proved by a moment-generating-function argument
rather than by Fourier analyticity.
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
Formalized as `CohnElkies.SignEigenfunction.rotationalAverage_ne_zero` (module
`CohnElkies.SignUncertainty.Radialization`), via `CohnElkies.eq_zero_of_rotationalAverage_eq_zero`.
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
$`\widehat g = \varsigma g` and $`g(0) = 0`, $`\varsigma \in \{-1,+1\}`. For $`n \ge 1` set
$`\kappa_n(x) = n^d e^{-\pi n^2|x|^2}`, $`\eta_n(x) = e^{-\pi|x|^2/n^2}`,
$`q_n = \eta_n\,(g * \kappa_n)`, $`p_n = \tfrac12(q_n + \varsigma\widehat{q_n})`,
$`\psi_+(x) = e^{-\pi|x|^2}`, $`\psi_-(x) = \bigl(|x|^2 - \tfrac{d}{4\pi}\bigr)e^{-\pi|x|^2}`,
and the corrected approximants
$`g_n = p_n - \dfrac{p_n(0)}{\psi_\varsigma(0)}\,\psi_\varsigma`.
The formalization (module `CohnElkies.SignUncertainty.SchwartzApproximation`) uses a compactly
supported flat bump $`\varphi_n(x) = (n+1)^d\varphi((n+1)x)` in place of $`\kappa_n` for the
convolution: `CohnElkies.approximant` is $`q_n = (\eta_n g) * \varphi_n`, a test function by
`CohnElkies.schwartzConvolution`, whose Fourier transform is
$`\varsigma\,(g * \kappa_n)\,\widehat{\varphi_n}` (`CohnElkies.fourier_approximant_apply`); the
Gaussians $`\kappa_n, \eta_n` (`CohnElkies.Mollifiers`) enter only through this identity. The
symmetrization is `CohnElkies.projected` ($`p_n`), and the corrector $`\psi_\varsigma` is
`CohnElkies.eigenProjection` of a bump (`CohnElkies.exists_eigenTest`: one of $`P_\varsigma\varphi`,
$`P_\varsigma\varphi(2\cdot)` with $`P_\varsigma\varphi = \varphi + \varsigma\widehat\varphi` has
nonzero value at the origin).
:::

:::lemma_ "lemma_schwartz_approximation" (lean := "CohnElkies.exists_schwartz_approximation") (parent := "grp_radial_reduction")
In the situation of {uses "def_schwartz_approximation"}[], each $`g_n` lies in
$`\mathcal{S}_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})`, satisfies $`\widehat{g_n} = \varsigma g_n`
and $`g_n(0) = 0`, and $`g_n \to g` in $`L^1(\mathbb{R}^d)` as $`n \to \infty`.
Formalized as `CohnElkies.exists_schwartz_approximation` (for radial $`g`, the case needed after
{bpref "lemma_rotational_average_properties"}[]; the sequence is the one of
{bpref "def_schwartz_approximation"}[], with `CohnElkies.tendsto_projected` for the $`L^1`
convergence and `CohnElkies.fourier_eigenProjection` for the eigenvalue).
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
integration gives $`\int_{\mathbb{R}^d} g(x)\,dx = S_d\int_0^\infty g(r)\,r^{d-1}\,dr`.
Formalized as `CohnElkies.sphereArea`, defined as $`d\,v_d`; polar integration appears in the
form $`\int f(x)|x|^{s-d}\,dx = S_d\,M_g(s)` for radial test functions $`f` with profile $`g`
(`CohnElkies.integral_radialProfile_cpow`, Mellin transform `mellin` from Mathlib).
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

Formalized in pieces: $`M_g` is Mathlib's `mellin` applied to the radial profile, $`X_g` on the
critical line is `CohnElkies.X_fℝ` (and `CohnElkies.Xline` on a general line
$`\operatorname{Re} z = \ell`, `CohnElkies.X_f` for complex $`t`), and the log-profile appears in
the reflected variable $`u = -v` as `CohnElkies.radialCriticalLogProfile`,
$`u \mapsto e^{-\lambda u}g(e^{-u})`.
:::

:::lemma_ "lemma_log_profile_schwartz" (lean := "CohnElkies.radialMellinFrequency_eq_fourier") (parent := "grp_radial_mellin")
For $`g \in \mathcal{S}_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})`, with the notation of
{uses "def_radial_mellin"}[]: $`\Phi_g \in \mathcal{S}(\mathbb{R};\mathbb{R})`, $`M_g` is
holomorphic on $`\operatorname{Re} z > 0`,
$`X_g(t) = \int_{\mathbb{R}}\Phi_g(v)e^{-itv}\,dv`,
$`\Phi_g(v) = \dfrac{1}{2\pi}\int_{\mathbb{R}}X_g(t)e^{itv}\,dt`,
so that Mellin inversion reads
$`g(r) = \dfrac{r^{-\lambda}}{2\pi}\int_{\mathbb{R}} X_g(t)\,r^{it}\,dt`
for $`r > 0`. Moreover $`\widehat g(0) = \int_{\mathbb{R}^d} g = S_d\,M_g(d)`
({uses "def_sphere_area_polar"}[]).

Formalized as `CohnElkies.radialMellinFrequency_eq_fourier` (with
`CohnElkies.mellinFrequency_eq_fourier`
for a general line), which expresses $`X_g` as the Fourier transform of the reflected log-profile
at $`-t/(2\pi)`; Mellin inversion is used in the form of injectivity,
`CohnElkies.radialMellinFrequency_injective`; the Schwartz property of the profile is
`CohnElkies.radialSchwartzProfile` with `CohnElkies.radialProfile_smooth`; and the value
$`\widehat g(0) = S_d M_g(d)` is the case $`s = d` of `CohnElkies.integral_radialProfile_cpow`.
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
Formalized as `CohnElkies.radial_fourier_mellin_strip`, for the radial profiles of a radial test
function and of its Fourier transform.
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
$`g(r) = O(r^2)` as $`r \to 0`, and $`M_g` ({uses "def_radial_mellin"}[]) extends holomorphically
to $`\operatorname{Re} z > -2`. If moreover $`\widehat g(0) = 0`, then both sides of
{bpref "eq_9_mellin_hankel"}[] extend holomorphically to the strip $`-2 < \operatorname{Re} z < d+2`
and the identity holds there; the apparent pole of $`\Gamma(z/2)` at $`z = 0` is cancelled by the
zero $`M_g(d) = S_d^{-1}\widehat g(0) = 0`, since $`M_g(d-z) = -zM_g'(d) + O(z^2)` and
$`\Gamma(z/2) = 2/z + O(1)`. In particular (9) holds on $`\operatorname{Re} z = 0`.

Formalized as follows: $`M_g` converges and is holomorphic on $`\operatorname{Re} z > -2`
(`CohnElkies.radialProfile_mellinConvergent`, `CohnElkies.radialProfile_mellin_differentiableAt`),
and the functional equation, divided on both sides by the gamma functions so that no pole
appears, extends by continuity to the closed strip $`0 \le \operatorname{Re} z \le d`:
$`M_{\widehat g}(z)/\Gamma(z/2) = \pi^{\lambda-z}\,M_g(d-z)/\Gamma((d-z)/2)`
(`CohnElkies.radial_fourier_mellin_regularized_closed`). The lower boundary of the strip of
Lemma 3.2 only needs the line $`\operatorname{Re} z = 0`.
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
(equation (10)). The multiplier satisfies
$`m_\lambda(-t) = \overline{m_\lambda(t)} = m_\lambda(t)^{-1}`
and $`|m_\lambda(t)| = 1` for real $`t`. Formalized as `CohnElkies.radialMellinMultiplier` with
the multiplier `CohnElkies.m_ℓ`; the unimodularity and conjugation properties of $`m_\lambda` are
not stated separately, only used implicitly.
:::

:::proof "eq_10_critical_line"
Evaluate {uses "eq_9_mellin_hankel"}[] at $`z = \lambda - it`, for which $`d - z = \lambda + it`
and $`X_g(-t) = M_g(\lambda + it)` ({uses "def_radial_mellin"}[]). The properties of $`m_\lambda`
follow from $`\Gamma(\bar z) = \overline{\Gamma(z)}` ({uses "eq_7_gamma_identities"}[]) and
$`|\pi^{it}| = 1`.
:::
