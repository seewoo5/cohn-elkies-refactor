import Verso
import VersoManual
import VersoBlueprint
import CohnElkies

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The universal Cohn–Elkies lower bound" =>

By the radial reduction of the preliminaries we may assume that an admissible packing function
$`F` is radial. Let $`a = (\widehat F(0)/F(0))^{1/d}` and $`h(x) = F(ax)`. Then
$`h(0) = \widehat h(0)`, and $`g = \widehat h - h` is anti-self-Fourier, vanishes at the origin, and
is nonnegative for $`|x| \ge 1/a`. Since $`\int g = 0`, its negative part has mass $`\|g\|_1/2`,
all of which lies in $`B(0,1/a)`. Proposition 3.1 shows that every radial Schwartz Fourier
eigenfunction vanishing at the origin, of either eigenvalue, has exponentially little $`L^1` mass
in $`B(0,c\sqrt d)` when $`c < 1/\pi`; the negative half-mass of $`g` cannot fit inside this ball,
forcing $`1/a \ge (1/\pi - o(1))\sqrt d`.

The obstruction comes from the Mellin–Fourier identity (9). Lemma 3.2 bounds a normalized Mellin
transform $`Z` on the strip $`|\operatorname{Im} t| \le \lambda`: total $`L^1` mass controls the
upper boundary, the functional equation controls the lower boundary, and Poisson interpolation
gives $`\log|Z(s+i\sigma\lambda)| \le H_\sigma(s) \le H_\sigma(0)`, with
$`H_\sigma(0) \le \lambda M_\sigma(\log(2\pi c^2) + J_\sigma) + O_\sigma(\log\lambda)` by Lemma 3.3.
The sharp constant enters through Lemma 3.4: $`J_\sigma \to \log(\pi/2)` as $`\sigma \uparrow 1`,
so the parenthesized rate tends to $`\log(\pi^2c^2)`, negative exactly when $`c < 1/\pi`. Lemmas
3.5 and 3.6 turn this negativity into the interior-mass estimate.

In the formalization the functions of this chapter are the structure
`CohnElkies.RadialEigenfunction d ς`: a nonzero real radial test function $`g` with
$`\widehat g = \varsigma g` and $`g(0) = 0`, for a unit $`\varsigma` of $`\mathbb{Z}`. The chapter
corresponds to the modules `CohnElkies/LowerBound/*.lean`; the interior bound of Lemma 3.2 is
proved by a Phragmén–Lindelöf argument and the limit of Lemma 3.4 by a Frullani-type
computation, both recorded in the final chapter.

# The Mellin-strip obstruction

:::definition "def_normalized_profile" (lean := "CohnElkies.Z_g")
Fix $`0 < c < 1/\pi`, $`d \in \mathbb{N}`, $`\lambda = d/2`, $`R = c\sqrt d`, and a nonzero
$`g \in \mathcal{S}_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})` with $`\widehat g = \varsigma g`,
$`\varsigma \in \{-1,+1\}`, and $`g(0) = 0`. With $`S_d` from {uses "def_sphere_area_polar"}[] and
$`X_g` from {uses "def_radial_mellin"}[], define in the logarithmic coordinate $`r = Re^v`
(equation (12))
$`\varphi(v) = \dfrac{S_d}{\|g\|_1}\,(Re^v)^d\,g(Re^v)` and
$`Z(t) = \dfrac{S_d}{\|g\|_1}\,R^{\lambda+it}\,X_g(t)`.
Formalized as `CohnElkies.φ_g` and `CohnElkies.Z_g` (with $`t` complex, through the complex
Mellin frequency `CohnElkies.X_f`), for an arbitrary test function $`g` and radius $`R > 0`;
$`\|g\|_1` is `CohnElkies.L1norm`.
:::

:::lemma_ "eq_13_normalization" (lean := "CohnElkies.RadialEigenfunction.integral_abs_logProfile")
In the setting of {uses "def_normalized_profile"}[] (equation (13)):
$`\|\varphi\|_1 = 1`, $`\int_{\mathbb{R}}\varphi = 0`,
$`\int_{-\infty}^0|\varphi(v)|\,dv = \dfrac{1}{\|g\|_1}\int_{|x|<R}|g(x)|\,dx`,
and $`Z(t) = \int_{\mathbb{R}}\varphi(v)e^{-(\lambda+it)v}\,dv` for every complex $`t` for which
the integral converges absolutely, in particular for real $`t`. Formalized as
`CohnElkies.RadialEigenfunction.integral_abs_logProfile`,
`CohnElkies.RadialEigenfunction.integral_logProfile`,
`CohnElkies.RadialEigenfunction.setIntegral_Iic_abs_logProfile`, and, for the last identity on
the line $`\operatorname{Im} t = \lambda - a`,
`CohnElkies.normalizedRadialMellinStrip_shifted_eq_fourier`,
which writes $`Z(s + i(\lambda - a))` as the Fourier transform of $`e^{-av}\varphi(v)`.
:::

:::proof "eq_13_normalization"
Polar integration ({uses "def_sphere_area_polar"}[]) with $`r = Re^v`, $`dr = r\,dv`, gives
$`\int|\varphi| = \frac{S_d}{\|g\|_1}\int_0^\infty |g(r)|r^{d-1}\,dr = 1`, and likewise
$`\int\varphi = \widehat g(0)/\|g\|_1 = \varsigma g(0)/\|g\|_1 = 0` and the identity for
$`\int_{-\infty}^0|\varphi|`. The last formula is the substitution $`r = Re^v` in
$`X_g(t) = \int_0^\infty g(r)r^{\lambda-it-1}\,dr`.
:::

:::group "grp_mellin_strip"
The strip estimates for the normalized Mellin transform `Z` (Lemmas 3.2–3.6 of the report).
:::

:::definition "def_lower_boundary_majorant" (lean := "CohnElkies.h_ℓ") (parent := "grp_mellin_strip")
The lower-boundary majorant is (equation (14)), for $`y \ne 0`,
$`h_\lambda(y) = \lambda\log(\pi R^2) + \log|\Gamma(-iy/2)| - \log|\Gamma(\lambda + iy/2)|`.
Formalized as `CohnElkies.h_ℓ`, a function of $`\lambda`, $`R` and $`y`.
:::

:::definition "def_strip_poisson_kernel" (lean := "CohnElkies.P_σ") (parent := "grp_mellin_strip")
For $`-1 < \sigma < 1` write $`\theta = \pi(1+\sigma)/2 \in (0,\pi)` and define (equation (15))
$`P_\sigma(T) = \dfrac{\sin\theta}{4(\cosh(\pi T/2) - \cos\theta)}`,
$`M_\sigma = \int_{\mathbb{R}}P_\sigma(T)\,dT = \dfrac{1-\sigma}{2}`,
and the Poisson majorant (equation (18))
$`H_\sigma(s) = \int_{\mathbb{R}}P_\sigma(T)\,h_\lambda(s - \lambda T)\,dT` with $`h_\lambda` from
{uses "def_lower_boundary_majorant"}[]. The kernel is positive, even, decreasing on $`(0,\infty)`,
and $`P_\sigma(T) \ll_\sigma e^{-\pi|T|/2}`. Formalized as `CohnElkies.θ`, `CohnElkies.P_σ`,
`CohnElkies.M_σ` and `CohnElkies.H_σ`, with the positivity `CohnElkies.stripPoissonKernel_pos`
and the exponential majorant `CohnElkies.P_σ_le_exponentialMajorant`.
:::

:::lemma_ "lemma_strip_poisson_principle" (parent := "grp_mellin_strip") (tags := "not-formalized")
(Poisson principle for the strip.) Let $`\lambda > 0` and let $`Z` be holomorphic on a
neighbourhood of the closed strip $`\{|\operatorname{Im} t| \le \lambda\}` and bounded there. Let
$`b : \mathbb{R} \to \mathbb{R}` be measurable and bounded above, with
$`\log|Z(y - i\lambda)| \le b(y)` and $`\log|Z(y + i\lambda)| \le 0` for all $`y \in \mathbb{R}`.
Then for $`-1 < \sigma < 1` and $`s \in \mathbb{R}`,
$`\log|Z(s + i\sigma\lambda)| \le \int_{\mathbb{R}}P_\sigma(T)\,b(s - \lambda T)\,dT`,
the integral being well defined in $`[-\infty,\infty)`. Here
$`\lambda^{-1}P_\sigma((s-y)/\lambda)\,dy` is the lower-edge harmonic measure of the strip at
$`s+i\sigma\lambda`, of mass $`M_\sigma`; the upper-edge measure has mass $`(1+\sigma)/2`. Uses
{uses "def_strip_poisson_kernel"}[].

This is the report's tool for the interior bound of Lemma 3.2. It is not formalized: the
formalization proves the interior bound instead by a Phragmén–Lindelöf argument on the strip,
{bpref "lemma_phragmen_lindelof_strip"}[] and {bpref "lemma_3_2_capped"}[].
:::

:::proof "lemma_strip_poisson_principle"
The map $`\Phi(t) = \exp(\pi(t+i\lambda)/(2\lambda))` is a biholomorphism from the open strip onto
the upper half-plane $`\mathbb{H}`; it sends the lower edge $`y - i\lambda` to
$`e^{\pi y/(2\lambda)} \in (0,\infty)`, the upper edge $`y + i\lambda` to
$`-e^{\pi y/(2\lambda)} \in (-\infty,0)`, and $`s + i\sigma\lambda` to $`\rho e^{i\theta}` with
$`\rho = e^{\pi s/(2\lambda)}`. The function $`u = \log|Z \circ \Phi^{-1}|` is subharmonic on
$`\mathbb{H}` (with value $`-\infty` at zeros) and bounded above, and its boundary values are at
most $`\tilde b(x) = b((2\lambda/\pi)\log x)` for $`x > 0` and $`0` for $`x < 0`, a function
bounded above. The upper-half-plane Poisson principle (Ahlfors) gives
$`u(\rho e^{i\theta})`
$`\le \frac1\pi\int_{\mathbb{R}}P_{\mathbb{H}}(\rho e^{i\theta}, x)\,\tilde b(x)\,dx`, with the
half-plane Poisson kernel
$`P_{\mathbb{H}}(\rho e^{i\theta}, x)`
$`= \dfrac{\rho\sin\theta}{(x-\rho\cos\theta)^2 + \rho^2\sin^2\theta}`,,
where only $`x > 0` contributes. Substituting $`x = e^{\pi y/(2\lambda)}`,
$`dx = (\pi x/(2\lambda))dy`, and
$`(x-\rho\cos\theta)^2 + \rho^2\sin^2\theta = x^2 - 2\rho x\cos\theta + \rho^2`, the measure
becomes $`\dfrac{\sin\theta}{2\lambda(x/\rho + \rho/x - 2\cos\theta)}\,dy`, which equals
$`\dfrac{\sin\theta}{4\lambda(\cosh(\pi(s-y)/(2\lambda)) - \cos\theta)}\,dy`
$`= \lambda^{-1}P_\sigma\bigl(\tfrac{s-y}{\lambda}\bigr)\,dy`.
The substitution $`T = (s-y)/\lambda` gives the claim. The mass $`M_\sigma = (1-\sigma)/2` is the
harmonic measure of $`(0,\infty)` seen from $`\rho e^{i\theta}`, namely $`(\pi-\theta)/\pi`.
:::

:::lemma_ "lemma_3_2" (lean := "CohnElkies.normalizedRadialMellinStrip_diffContOnCl") (parent := "grp_mellin_strip")
In the setting of {uses "def_normalized_profile"}[], for every $`-1 < \sigma < 1`: the function
$`Z` is bounded and holomorphic on a neighbourhood of the strip
$`|\operatorname{Im} t| \le \lambda`.
Its boundary values satisfy $`|Z(y + i\lambda)| \le 1` for all $`y`, and
$`\log|Z(y - i\lambda)| \le h_\lambda(y)` for $`y \ne 0`, with $`h_\lambda` from
{uses "def_lower_boundary_majorant"}[]. With $`P_\sigma`, $`H_\sigma` from
{uses "def_strip_poisson_kernel"}[],
$`|Z(s + i\sigma\lambda)| \le \exp(H_\sigma(s))`
$`= \exp\Bigl(\int_{\mathbb{R}}P_\sigma(T)h_\lambda(s-\lambda T)\,dT\Bigr)`
for every $`s \in \mathbb{R}`.

Formalized for `RadialEigenfunction`: holomorphy on the open strip together with continuity on
its closure is `CohnElkies.normalizedRadialMellinStrip_diffContOnCl`
(`CohnElkies.RadialEigenfunction.diffContOnCl_Z_g`), boundedness on the closed strip is
`CohnElkies.RadialEigenfunction.exists_norm_Z_g_le`, the boundary values (16) and (17) are
`CohnElkies.RadialEigenfunction.norm_Z_g_top_le_one` and
`CohnElkies.RadialEigenfunction.norm_Z_g_bottom_le_exp_h_ℓ`, and the interior bound (18) is
`CohnElkies.norm_Z_g_le_exp_H_σ`.
:::

:::proof "lemma_3_2"
Holomorphy. Since $`g(0) = \widehat g(0) = 0`, {uses "lemma_mellin_continuation"}[] shows that
$`M_g` is holomorphic on $`\operatorname{Re} z > -2`; as $`Z(t)` is a multiple of
$`R^{it}M_g(\lambda - it)` and $`\operatorname{Re}(\lambda - it) = \lambda + \operatorname{Im} t`,
$`Z` is holomorphic on $`\operatorname{Im} t > -\lambda - 2`, a neighbourhood of the closed strip.

Boundedness. For $`-\lambda \le \eta \le \lambda`, (12) gives
$`|Z(s+i\eta)| \le \frac{S_dR^{\lambda-\eta}}{\|g\|_1}\int_0^\infty|g(r)|r^{\lambda+\eta-1}\,dr`.
Splitting at $`r = 1`, using $`|g(r)| \le Cr^2` near $`0` (so the integrand is at most
$`Cr^{\lambda+\eta+1} \le C` on $`(0,1]`) and the Schwartz decay of $`g` on $`[1,\infty)`, bounds
the right-hand side uniformly in $`s` and $`\eta`. In particular
$`\sup_y|Z(y - i\lambda)| \le \frac{S_dR^d}{\|g\|_1}\int_0^\infty\frac{|g(r)|}{r}\,dr < \infty`.

Upper boundary (16). By {uses "eq_13_normalization"}[] with $`t = y + i\lambda`,
$`Z(y+i\lambda) = \int\varphi(v)e^{-iyv}\,dv`, so $`|Z(y+i\lambda)| \le \|\varphi\|_1 = 1`.

Lower boundary (17). Evaluating (9), continued to $`\operatorname{Re} z = 0` by
{uses "lemma_mellin_continuation"}[], at $`z = -iy` and using $`\widehat g = \varsigma g` gives
$`X_g(y - i\lambda)`
$`= \varsigma\pi^{\lambda+iy}\frac{\Gamma(-iy/2)}{\Gamma(\lambda+iy/2)}X_g(-y+i\lambda)`,
hence
$`Z(y - i\lambda)`
$`= \varsigma(\pi R^2)^{\lambda+iy}\frac{\Gamma(-iy/2)}{\Gamma(\lambda + iy/2)}Z(-y + i\lambda)`.
Taking absolute values and using (16) gives $`\log|Z(y - i\lambda)| \le h_\lambda(y)` for
$`y \ne 0`, independently of $`\varsigma`. At $`y = 0` the zero $`Z(i\lambda) = \int\varphi = 0`
cancels the gamma pole in (17), so $`Z(-i\lambda)` is finite, although
$`h_\lambda(y) = -\log|y| + O_\lambda(1)` as $`y \to 0`.

Interior. The logarithmic singularity of $`h_\lambda` requires a bounded truncation. Choose
$`D > \max\{0, \sup_y\log|Z(y - i\lambda)|\}` and let $`h_{\lambda,D} = \min\{h_\lambda, D\}`
(with value $`D` at $`0`). The report applies the Poisson principle
({bpref "lemma_strip_poisson_principle"}[]) to $`Z` with lower majorant $`h_{\lambda,D}` and
upper majorant $`0`; the formalization obtains the same capped bound
$`\log|Z(s+i\sigma\lambda)| \le \int P_\sigma(T)h_{\lambda,D}(s-\lambda T)\,dT`
from {uses "lemma_3_2_capped"}[]. The integral $`H_\sigma(s)` converges absolutely, because
$`P_\sigma` decays exponentially, the singularity of $`h_\lambda` at $`0` is locally integrable,
and $`h_\lambda(y) = -\lambda\log|y| + O_\lambda(1)` as $`|y| \to \infty` by
{uses "lemma_gamma_asymptotics"}[]. Since $`h_{\lambda,D} \le h_\lambda` and $`P_\sigma \ge 0`,
the capped majorant is at most $`H_\sigma(s)`; equivalently, dominated convergence lets
$`D \to \infty` (`CohnElkies.lowerStripCappedPoisson_tendsto`). This proves (18).
:::

:::lemma_ "lemma_convolution_symmetric_decreasing" (lean := "CohnElkies.even_antitone_poisson_convolution_max") (parent := "grp_mellin_strip")
Let $`f, q : \mathbb{R} \to [0,\infty)` be integrable, even, and nonincreasing on $`[0,\infty)`.
Then $`(f * q)(x) \le (f * q)(0)` for every $`x \in \mathbb{R}`. Formalized for the case needed
here, $`q = P_\sigma` of {uses "def_strip_poisson_kernel"}[] and $`f` compactly supported, as
`CohnElkies.even_antitone_poisson_convolution_max`.
:::

:::proof "lemma_convolution_symmetric_decreasing"
Layer-cake: $`f(x) = \int_0^\infty \mathbf 1_{\{f > \alpha\}}(x)\,d\alpha` and similarly for $`q`,
where, up to endpoints, $`\{f > \alpha\} = (-r_\alpha, r_\alpha)` and
$`\{q > \beta\} = (-R_\beta, R_\beta)` (`CohnElkies.even_antitone_superlevel_interval`). By
Tonelli, $`(f*q)(x)` is the double integral over $`\alpha, \beta` of the length of
$`(-R_\beta,R_\beta) \cap (x - r_\alpha, x + r_\alpha)`, and the length of the intersection of two
centred intervals, one translated by $`x`, is largest at $`x = 0`.
:::

:::lemma_ "lemma_3_3" (lean := "CohnElkies.lowerStripPoissonMajorant_dimension_central_bound") (parent := "grp_mellin_strip")
Put $`f_T(x) = \log\sqrt{x^2 + T^2/4}`. For every $`-1 < \sigma < 1` there is $`C_\sigma > 0`,
independent of $`d`, $`c` and $`g`, such that (equation (19))
$`\int_{\mathbb{R}}P_\sigma(T)\,\Bigl|h_\lambda(\lambda T)`
$`- \lambda\Bigl(\log(2\pi c^2) - \int_0^1 f_T(x)\,dx\Bigr)\Bigr|\,dT \le C_\sigma\log(2+\lambda)`.
Define $`J_\sigma = -\dfrac{1}{M_\sigma}\int_{\mathbb{R}}P_\sigma(T)\int_0^1 f_T(x)\,dx\,dT`. Then
for
every $`s \in \mathbb{R}` (equation (20))
$`H_\sigma(s) \le H_\sigma(0) = \lambda M_\sigma\bigl(\log(2\pi c^2) + J_\sigma\bigr)`
$`+ O_\sigma(\log(2+\lambda))`.
Uses {uses "def_lower_boundary_majorant"}[] and {uses "def_strip_poisson_kernel"}[].

The formalization proves the upper halves of these statements, which are all that is used later,
with an error term that is uniform in $`d`. Writing $`\Lambda(T) = -\int_0^1 f_T - 1` for the
endpoint phase `CohnElkies.lowerEndpointPhase` (so that
$`\log(2\pi c^2) - \int_0^1 f_T = \log(2\pi e c^2) + \Lambda(T)`), the one-sided form of (19) is
$`h_\lambda(\lambda T) \le \lambda(\log(2\pi e c^2) + \Lambda(T)) + E(T)` with an explicit
$`E(T)` independent of $`d` and $`c` ({bpref "lemma_3_3_one_sided"}[],
`CohnElkies.lowerGammaBoundaryLog_dimension_scaled_riemann_le`); the maximum property
$`H_\sigma(s) \le H_\sigma(0)` is `CohnElkies.lowerStripPoissonMajorant_dimension_centered_max`;
and the central bound is
`CohnElkies.lowerStripPoissonMajorant_dimension_central_bound`,
$`H_\sigma(0) \le \lambda M_\sigma(\log(2\pi e c^2) + J^{\mathrm{Lean}}_\sigma) + E_\sigma`, where
$`J^{\mathrm{Lean}}_\sigma = \int(P_\sigma/M_\sigma)(T)\Lambda(T)\,dT`
(`CohnElkies.lowerPoissonEndpointExpectation`) satisfies $`J_\sigma = 1 + J^{\mathrm{Lean}}_\sigma`,
and $`E_\sigma = \int P_\sigma E` (`CohnElkies.lowerRiemannPoissonError`) is finite and
independent of $`d` and $`c`. Thus the bracket $`\log(2\pi c^2) + J_\sigma` of the report and
the bracket $`\log(2\pi e c^2) + J^{\mathrm{Lean}}_\sigma` of the code coincide.
:::

:::proof "lemma_3_3"
Riemann sums. Since $`R = c\sqrt{2\lambda}`,
$`\lambda\log(\pi R^2) = \lambda\log(2\pi c^2) + \lambda\log\lambda`. Put $`b = \lambda T/2`. If
$`d = 2n` is even, the recurrence in {uses "eq_7_gamma_identities"}[] gives
$`|\Gamma(n+ib)| = |\Gamma(ib)|\prod_{k=0}^{n-1}\sqrt{k^2+b^2}` and $`|\Gamma(-ib)| = |\Gamma(ib)|`,
so for $`T \ne 0` we get $`h_n(nT) = n\log(2\pi c^2) - \sum_{k=0}^{n-1}f_T(k/n)`.
Monotonicity of $`f_T` on $`[0,1]` bounds the left Riemann-sum error by $`f_T(1) - f_T(0)`:
$`0 \le h_n(nT) - n\bigl(\log(2\pi c^2) - \int_0^1 f_T\bigr) \le \tfrac12\log(1 + 4/T^2)`.
If $`d = 2n+1`, so $`\lambda = n + \tfrac12`, then
$`|\Gamma(\lambda + ib)| = |\Gamma(\tfrac12 + ib)|\prod_{k=0}^{n-1}\sqrt{(k+\tfrac12)^2 + b^2}` and
$`|\Gamma(-ib)|^2/|\Gamma(\tfrac12+ib)|^2 = \coth(\pi|b|)/|b|` by (7), whence
$`h_\lambda(\lambda T) = \lambda\log(2\pi c^2)`
$`- \sum_{k=0}^{n-1}f_T\bigl(\tfrac{k+1/2}{\lambda}\bigr) + E_\lambda(T)`
with $`E_\lambda(T) = \tfrac12\log\lambda + \tfrac12\log(\coth(\pi|b|)/|b|)`.
The midpoint Riemann-sum error on $`[0, n/\lambda]` is at most $`f_T(n/\lambda) - f_T(0)`, and the
remaining interval $`[n/\lambda, 1]` has length $`1/(2\lambda)`; together these contribute at most
$`C(1 + \log(2+|T|) + \log(2+|T|^{-1}))`. Adding $`C\log(2+\lambda)` also bounds the endpoint
correction $`E_\lambda(T)`. Since $`P_\sigma(T) \ll_\sigma e^{-\pi|T|/2}` and $`\log(2+|T|^{-1})`
is locally integrable, integrating the even- and odd-dimensional bounds against $`P_\sigma`
proves (19). The formalization keeps only the upper bounds and absorbs $`E_\lambda(T)` into the
$`d`-independent majorant $`E(T)` ({uses "lemma_3_3_one_sided"}[]).

Value at $`0`. Both $`P_\sigma` and $`h_\lambda` are even, so
$`H_\sigma(0) = \int P_\sigma(T)h_\lambda(\lambda T)\,dT`, and (19) gives
$`|H_\sigma(0) - \lambda M_\sigma(\log(2\pi c^2) + J_\sigma)| \le C_\sigma\log(2+\lambda)`.

Maximum at $`0`. By the digamma series in {bpref "def_digamma"}[], for $`y > 0`,
$`h_\lambda'(y)`
$`= \tfrac12\bigl(\operatorname{Im}\psi(\lambda + iy/2) - \operatorname{Im}\psi(iy/2)\bigr) < 0`,
because $`\sum_k b/((k+\lambda)^2+b^2) < \sum_k b/(k^2+b^2)` termwise for $`b = y/2 > 0`; the
formalization instead reads off the monotonicity from the product formulas of
{uses "eq_7_gamma_identities"}[] (`CohnElkies.lowerGammaBoundaryLog_dimension_antitoneOn`).
Thus $`h_\lambda` is even and decreasing on $`(0,\infty)`, and so is $`P_\sigma`. For $`N > 0`,
the function $`q_N(u) = \max\{h_\lambda(\lambda u) + N, 0\}` is nonnegative, even, decreasing on
$`(0,\infty)`, and integrable (the singularity at $`0` is logarithmic and
$`h_\lambda \to -\infty` at infinity, so $`q_N` has compact support). Since
$`H_\sigma(s) = (P_\sigma * h_\lambda(\lambda\,\cdot))(s/\lambda)`,
{uses "lemma_convolution_symmetric_decreasing"}[] gives
$`(P_\sigma*q_N)(s/\lambda) \le (P_\sigma*q_N)(0)`. Subtracting $`NM_\sigma` turns this into
$`\int P_\sigma(T)\max\{h_\lambda(s-\lambda T), -N\}\,dT`
$`\le \int P_\sigma(T)\max\{h_\lambda(-\lambda T), -N\}\,dT`.
The left side is at least $`H_\sigma(s)`, and the right side tends to $`H_\sigma(0)` as
$`N \to \infty` by dominated convergence (exponential decay of $`P_\sigma`). Hence
$`H_\sigma(s) \le H_\sigma(0)`, and evaluating at $`0` with (19) proves (20).
:::

:::lemma_ "eq_21_sech_characteristic" (lean := "CohnElkies.poissonLogistic_characteristic") (parent := "grp_mellin_strip")
The probability density $`p(u) = \dfrac{\pi}{4}\operatorname{sech}^2\bigl(\dfrac{\pi u}{2}\bigr)` on
$`\mathbb{R}` has characteristic function (equation (21))
$`\int_{\mathbb{R}}p(u)e^{itu}\,du = \dfrac{t}{\sinh t}` for $`t \in \mathbb{R}`, interpreted as
$`1` at $`t = 0`. Formalized as `CohnElkies.poissonLogistic_characteristic` for the density
`CohnElkies.poissonLogisticDensity`, written as $`p(u) = \pi e^{\pi u}/(1 + e^{\pi u})^2`; the
real form $`\int p(u)\cos(tu)\,du = t/\sinh t` is `CohnElkies.poissonLogistic_cosine_transform`.
:::

:::proof "eq_21_sech_characteristic"
The report shifts the contour by $`2i`: the integrand $`p(u)e^{itu}` is $`2i`-periodic up to the
factor $`e^{-2t}`, and the only pole between the two lines is the double pole of
$`\operatorname{sech}^2(\pi u/2)` at $`u = i`, whose residue contributes $`2te^{-t}`; thus
$`(1 - e^{-2t})\int p(u)e^{itu}\,du = 2te^{-t}`, i.e. $`t/\sinh t` for $`t > 0`, and evenness
handles $`t < 0`. The formalization argues without contour integration: $`p` is the derivative
of the logistic function $`\ell(u) = e^{\pi u}/(1+e^{\pi u})`, and the substitution $`x = \ell(u)`
turns $`\int p(u)e^{\pi u w}\,du` into the beta integral $`B(1+w, 1-w)`
(`CohnElkies.poissonLogistic_betaIntegral`); with $`w = it/\pi` this is
$`\Gamma(1 + it/\pi)\Gamma(1 - it/\pi)`, which equals $`t/\sinh t` by the reflection formula
({uses "eq_7_gamma_identities"}[], `Complex.Gamma_one_add_I_mul_mul_Gamma_one_sub_I_mul`).
The value $`1` at $`t = 0` is $`\int p = 1`.
:::

:::lemma_ "eq_22_log_moment_digamma" (parent := "grp_mellin_strip") (tags := "not-formalized")
With $`p` from {uses "eq_21_sech_characteristic"}[] and $`\psi` from {uses "def_digamma"}[],
for every $`x \ge 0` (equation (22))
$`\int_{\mathbb{R}}p(u)\log\sqrt{x^2+u^2}\,du = \psi\Bigl(\dfrac{x+1}{2}\Bigr) + \log 2`.

This identity is not formalized: the formalization does not use it, and evaluates the limit of
Lemma 3.4 through a Frullani-type kernel instead ({bpref "lemma_3_4_frullani"}[]).
:::

:::proof "eq_22_log_moment_digamma"
Let $`I(x)` denote the left side. For $`x > 0`, the Laplace representation
$`x/(x^2+u^2) = \int_0^\infty e^{-xt}\cos(ut)\,dt`, Fubini, and {uses "eq_21_sech_characteristic"}[]
give $`I'(x) = \int_0^\infty e^{-xt}\dfrac{t}{\sinh t}\,dt`, which equals
$`\tfrac12\psi'((x+1)/2)` by the trigamma integral in {uses "lemma_gamma_asymptotics"}[] (iii)
after the substitution $`t = s/2`. Both $`I(x)` and $`\psi((x+1)/2) + \log 2` equal
$`\log x + o(1)` as $`x \to \infty`, so their integration constants agree. Local integrability of
$`\log|u|` at $`u = 0` extends the identity to $`x = 0` by dominated convergence.
:::

:::lemma_ "lemma_3_4" (lean := "CohnElkies.limitingPoissonEndpointExpectation_eq_log_pi_div_two_sub_one") (parent := "grp_mellin_strip")
For $`J_\sigma` defined in {uses "lemma_3_3"}[], $`\lim_{\sigma\uparrow 1}J_\sigma = \log(\pi/2)`.
Consequently, for every $`0 < c < 1/\pi` there is $`\sigma = \sigma(c) \in (-1,1)` such that
$`\delta_c = -(\log(2\pi c^2) + J_{\sigma(c)}) > 0` (equation (23)).

In the formalization the endpoint expectation is normalized as
$`J^{\mathrm{Lean}}_\sigma = J_\sigma - 1` ({bpref "lemma_3_3"}[]), so the limit reads
$`\lim_{\sigma\uparrow1}J^{\mathrm{Lean}}_\sigma = \log(\pi/2) - 1`:
this is `CohnElkies.limitingPoissonEndpointExpectation_eq_log_pi_div_two_sub_one` together with
`CohnElkies.tendsto_lowerPoissonEndpointExpectation`. The threshold identity
$`\log(2\pi e c^2) + \lim J^{\mathrm{Lean}}_\sigma = \log(\pi^2 c^2)` is
`CohnElkies.lowerPoissonEndpointSharpCoefficient_eq`, and (23), in the form that
$`\log(2\pi e c^2) + J^{\mathrm{Lean}}_\sigma < 0` for all $`\sigma < 1` close to $`1`, is
`CohnElkies.eventually_lowerPoissonEndpointSharpCoefficient_neg`.
:::

:::proof "lemma_3_4"
With $`T = 2u`, divide the lower-edge harmonic measure $`P_\sigma(T)\,dT` by its mass $`M_\sigma`.
The resulting probability density in $`u` is
$`p_\sigma(u) = \dfrac{2P_\sigma(2u)}{M_\sigma}`
$`= \dfrac{\sin\theta}{(1-\sigma)(\cosh(\pi u) - \cos\theta)}`,
and $`J_\sigma = -\int_{\mathbb{R}}p_\sigma(u)\int_0^1\log\sqrt{x^2+u^2}\,dx\,du`. As
$`\sigma \uparrow 1`, $`\theta \to \pi`, $`\sin\theta/(1-\sigma) \to \pi/2`, and the densities
$`p_\sigma` are uniformly bounded by $`Ce^{-\pi|u|}`
(`CohnElkies.stripNormalizedPoissonExtension_le_majorant`); they converge pointwise and in
$`L^1` to $`p(u) = \dfrac{\pi}{2(\cosh(\pi u) + 1)}`
$`= \dfrac{\pi}{4}\operatorname{sech}^2\bigl(\dfrac{\pi u}{2}\bigr)`
of {uses "eq_21_sech_characteristic"}[]. The uniform exponential bound and the local
integrability of $`\log|u|` justify dominated convergence in $`J_\sigma`
(`CohnElkies.tendsto_integral_stripNormalizedPoissonKernel_mul`), so
$`\lim_{\sigma\uparrow1}J_\sigma = -\int p(u)\int_0^1\log\sqrt{x^2+u^2}\,dx\,du`.

The report evaluates this limit with {bpref "eq_22_log_moment_digamma"}[] and
$`\int_0^1\psi\bigl(\tfrac{x+1}{2}\bigr)\,dx = 2\log\dfrac{\Gamma(1)}{\Gamma(1/2)} = -\log\pi`,
which give $`-\int_0^1(\psi(\tfrac{x+1}{2}) + \log 2)\,dx = \log\pi - \log 2`. The formalization
evaluates it instead by {uses "lemma_3_4_frullani"}[]: the inner integral is
$`1 + \Lambda(2u)` with the endpoint phase $`\Lambda` of {uses "lemma_3_3_one_sided"}[], the
expectation of $`1 + \Lambda(2u)` against $`p` is $`\log(\pi/2)`, and hence
$`\lim J^{\mathrm{Lean}}_\sigma = \int p(u)\Lambda(2u)\,du = \log(\pi/2) - 1`. Since
$`\log(2\pi c^2) + \log(\pi/2) = \log(\pi^2c^2) < 0` exactly when $`c < 1/\pi`, choosing
$`\sigma(c) < 1` close enough to $`1` gives (23).
:::

From now on fix $`\sigma = \sigma(c)` and $`\delta_c > 0` as in (23). We first bound $`Z` on the
horizontal line $`\operatorname{Im} t = \sigma\lambda`, and then use that bound to control the mass
of $`g` inside $`B(0,c\sqrt d)`.

:::lemma_ "lemma_3_5" (lean := "CohnElkies.exists_lowerStripPoissonMajorant_uniform_negative") (parent := "grp_mellin_strip")
There exist $`\gamma_c, C_c, B_c > 0`, depending only on $`c` (not on $`d`, $`g`, or $`\varsigma`),
such that for every sufficiently large $`d`, with $`\sigma = \sigma(c)` from {uses "lemma_3_4"}[]
and $`H_\sigma`, $`Z` as in {uses "def_strip_poisson_kernel"}[] and
{uses "def_normalized_profile"}[]:
$`H_\sigma(s) \le -\gamma_c\lambda` for all $`s \in \mathbb{R}` (equation (24)),
$`H_\sigma(\lambda S) \le -\dfrac{M_\sigma\lambda}{2}\log\dfrac{|S|}{C_c}` for $`|S| \ge B_c`
(equation (25)), and
$`\int_{\mathbb{R}}|Z(s + i\sigma\lambda)|\,ds \le C_c\lambda e^{-\gamma_c\lambda}` (equation (26)).

Formalized as `CohnElkies.exists_lowerStripPoissonMajorant_uniform_negative` (24), which also
produces the height $`\sigma(c) \in (0,1)`;
`CohnElkies.exists_lowerStripPoissonMajorant_logarithmic_tail` (25), with a constant
$`\kappa > 0` depending on $`\sigma` in place of $`M_\sigma/2`; and, for (26),
`CohnElkies.exists_lowerStripPoissonMajorant_integrable_majorant` combined with
`CohnElkies.integral_norm_Z_g_le_of_majorant`, which integrate a single inverse-quadratic
majorant of $`e^{H_\sigma}` ({bpref "lemma_3_5_inverse_quadratic"}[]) rather than the two bounds
(24) and (25) separately.
:::

:::proof "lemma_3_5"
Uniform negativity. The maximum estimate (20) of {uses "lemma_3_3"}[] and
$`\log(2\pi c^2) + J_\sigma = -\delta_c` from {uses "lemma_3_4"}[] give
$`H_\sigma(s) \le -\lambda M_\sigma\delta_c + O_\sigma(\log\lambda) \le -\gamma_c\lambda` for all
$`s` once $`d` is large, with $`\gamma_c > 0` independent of $`s`, $`g` and $`\varsigma`.

All frequencies. Apply the gamma identities of {uses "eq_7_gamma_identities"}[] to (14): each
factor of the recurrence $`|\Gamma(\lambda + ib)|/|\Gamma(ib)|` has modulus at least
$`|b| = \lambda|U|/2` at $`y = \lambda U`, so in both parities
$`h_\lambda(\lambda U) \le \lambda\log\dfrac{4\pi c^2}{|U|} + E_\lambda(U)` for $`U \ne 0`, where
$`E_\lambda(U) = 0` for $`\lambda \in \mathbb{N}` and
$`E_\lambda(U) = \tfrac12\log\coth(\pi\lambda|U|/2)` for $`\lambda \in \mathbb{N} + \tfrac12`
(`CohnElkies.lowerGammaBoundaryLog_dimension_scaled_log_tail`). Expanding $`\log\coth x` in its
odd exponential series gives
$`\int_{\mathbb{R}}E_\lambda(U)\,dU = \frac{2}{\pi\lambda}\int_0^\infty\log\coth x\,dx`
$`= \frac{\pi}{4\lambda}`,
so the $`P_\sigma`-convolution of $`E_\lambda` is at most $`\pi\|P_\sigma\|_\infty/(4\lambda)`.
Consequently (18) gives
$`H_\sigma(\lambda S) \le \lambda M_\sigma\log(4\pi c^2)`
$`- \lambda\int_{\mathbb{R}}P_\sigma(T)\log|S - T|\,dT + O_\sigma(\lambda^{-1})`.
Split the logarithmic integral at $`|T| = |S|/2`. On $`|T| \le |S|/2` we have $`|S-T| \ge |S|/2`
and the mass of $`P_\sigma` there is $`M_\sigma + O_\sigma(e^{-\pi|S|/4})`; on $`|T| > |S|/2` the
only possible negative contribution comes from $`|S - T| < 1`, which is $`O_\sigma(e^{-\pi|S|/2})`
by local integrability of $`\log|S-T|` and exponential decay of $`P_\sigma`. Hence there are
$`B_c, C_c' > 0` with $`\int P_\sigma(T)\log|S-T|\,dT \ge \frac{M_\sigma}{2}\log|S| - C_c'` for
$`|S| \ge B_c`, and after increasing $`C_c'` this yields (25).

Integration. Choose $`B > \max\{B_c, C_c'\}` and $`q = M_\sigma\lambda/2 > 1`. By (24),
$`\int_{|s| \le B\lambda}e^{H_\sigma(s)}\,ds \le 2B\lambda e^{-\gamma_c\lambda}`, while the
substitution $`s = \lambda S` and (25) give
$`\int_{|s| > B\lambda}e^{H_\sigma(s)}\,ds \le \lambda\int_{|S|>B}(|S|/C_c')^{-q}\,dS`
$`= \dfrac{2\lambda C_c'}{q-1}\Bigl(\dfrac{B}{C_c'}\Bigr)^{1-q}`,
which decays at exponential rate $`(M_\sigma/2)\log(B/C_c') > 0` in $`\lambda`. Decreasing
$`\gamma_c` if necessary and applying $`|Z(s+i\sigma\lambda)| \le e^{H_\sigma(s)}` from
{uses "lemma_3_2"}[] gives (26). The formalization merges the two integrals into the single
majorant of {uses "lemma_3_5_inverse_quadratic"}[].
:::

:::lemma_ "lemma_3_6" (lean := "CohnElkies.RadialEigenfunction.setIntegral_ball_norm_le") (parent := "grp_mellin_strip")
For every $`0 < c < 1/\pi` there exist $`C_c, \gamma_c > 0` and $`d_0(c) \in \mathbb{N}`,
independent of $`g` and $`\varsigma`, such that in the setting of {uses "def_normalized_profile"}[]
$`\int_{-\infty}^0|\varphi(v)|\,dv \le C_c e^{-\gamma_c d}` for all $`d \ge d_0(c)` (equation (27)).

The formalization states the inversion step separately from the $`L^1` bound (26): for every
$`-1 < \sigma < 1`,
$`\dfrac{1}{\|g\|_1}\int_{|x|<R}|g(x)|\,dx`
$`\le \dfrac{1}{2\pi(1-\sigma)\lambda}\int_{\mathbb{R}}|Z(s+i\sigma\lambda)|\,ds`
(`CohnElkies.RadialEigenfunction.setIntegral_ball_norm_le`, whose left side is
$`\int_{-\infty}^0|\varphi|` by (13)), obtained from the abstract inversion estimate
`CohnElkies.negativeHalfline_le_of_fourierInversion`; inserting (26) gives (27).
:::

:::proof "lemma_3_6"
Let $`G(v) = e^{(\sigma-1)\lambda v}\varphi(v)`. By (12) and the substitution $`r = Re^v`,
$`\int_{\mathbb{R}}|G(v)|\,dv`
$`= \dfrac{S_dR^{(1-\sigma)\lambda}}{\|g\|_1}\int_0^\infty|g(r)|r^{(1+\sigma)\lambda-1}\,dr`
$`< \infty`,
so $`G \in L^1(\mathbb{R})`, and {uses "eq_13_normalization"}[] with $`t = s + i\sigma\lambda`
identifies its Fourier transform $`\int G(v)e^{-isv}\,dv` with $`Z(s + i\sigma\lambda)`. This
transform is integrable by (26) of {uses "lemma_3_5"}[]
(`CohnElkies.RadialEigenfunction.integrable_Z_g_shifted`), so Fourier inversion gives
$`\varphi(v)`
$`= \dfrac{e^{(1-\sigma)\lambda v}}{2\pi}\int_{\mathbb{R}}Z(s+i\sigma\lambda)e^{isv}\,ds`.
Taking absolute values and integrating over $`v < 0` contributes
$`\int_{-\infty}^0e^{(1-\sigma)\lambda v}\,dv = ((1-\sigma)\lambda)^{-1}`, hence
$`\int_{-\infty}^0|\varphi(v)|\,dv`
$`\le \dfrac{1}{2\pi(1-\sigma)\lambda}\int_{\mathbb{R}}|Z(s+i\sigma\lambda)|\,ds`,
which is at most $`\dfrac{C_c}{2\pi(1-\sigma)}e^{-\gamma_c d/2}`. Renaming the constants (recall
$`\lambda = d/2`) gives (27).
:::

:::proposition "prop_3_1" (lean := "CohnElkies.exists_interior_mass_bound") (parent := "grp_mellin_strip")
For every $`0 < c < 1/\pi` there exist $`C_c, \gamma_c > 0` and $`d_0(c) \in \mathbb{N}` such
that, for every $`d \ge d_0(c)`, every $`\varsigma \in \{-1,+1\}`, and every nonzero
$`g \in \mathcal{S}_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})` satisfying $`\widehat g = \varsigma g`
and $`g(0) = 0`, one has (equation (11))
$`\int_{|x| < c\sqrt d}|g(x)|\,dx \le C_c e^{-\gamma_c d}\,\|g\|_1`.
Formalized as `CohnElkies.exists_interior_mass_bound`, stated for `g : RadialEigenfunction d ς`
with the constants $`C_c, \gamma_c` quantified before the eventually-in-$`d` statement, exactly
as here.
:::

:::proof "prop_3_1"
By {uses "eq_13_normalization"}[], the left side of (27) is exactly
$`\|g\|_1^{-1}\int_{|x|<c\sqrt d}|g(x)|\,dx`. Thus {uses "lemma_3_6"}[], fed with the $`L^1`
bound (26) of {uses "lemma_3_5"}[], proves (11), uniformly in $`g` and in its Fourier
eigenvalue $`\varsigma`.
:::

# The packing lower bound

:::proposition "prop_3_7" (lean := "CohnElkies.eventually_not_nonneg_outside_signEigenfunction")
For every $`0 < c < 1/\pi` there exists $`d_0(c) \in \mathbb{N}` such that, for every
$`d \ge d_0(c)` and $`\varsigma \in \{-1,+1\}`, no $`g \in \mathcal{E}_\varsigma(d)`
({uses "def_sign_eigenfunction_class"}[]) satisfies $`g(x) \ge 0` for all $`|x| \ge c\sqrt d`.
In words: no nonzero $`g \in L^1(\mathbb{R}^d;\mathbb{R})` with $`\widehat g = \varsigma g` and
$`g(0) = 0` is nonnegative outside $`B(0,c\sqrt d)`, where $`g` denotes its continuous
Fourier-inversion representative.

Formalized as `CohnElkies.eventually_not_nonneg_outside_signEigenfunction` (module
`CohnElkies.SignUncertainty.LowerBound`), for `g : SignEigenfunction d ς` and both signs; the
Schwartz case, for `g : RadialEigenfunction d ς`, is `CohnElkies.eventually_not_nonneg_outside`
(`CohnElkies.LowerBound.Main`). The Schwartz case with $`\varsigma = -1` is what
Theorem 3.8 uses, in the form `CohnElkies.uniformAntiFourierSignRadius`: for $`c < 1/\pi` and
all large $`d` there is no `CohnElkies.AntiSelfFourierWitness d (c√d)`, that is, no radial
anti-self-Fourier eigenfunction that is nonnegative outside $`B(0,c\sqrt d)`.
:::

:::proof "prop_3_7"
Schwartz case. Suppose first that $`g` is a radial Schwartz eigenfunction. Since
$`\int g = \widehat g(0) = \varsigma g(0) = 0`, its negative part $`g_- = \max\{-g,0\}` has
integral $`\|g\|_1/2`. If $`g \ge 0` for $`|x| \ge c\sqrt d`, then $`g_-` vanishes outside
$`B(0,c\sqrt d)`, so
$`\|g\|_1/2 = \int g_- \le \int_{|x|<c\sqrt d}|g| \le C_ce^{-\gamma_c d}\|g\|_1`
by {uses "prop_3_1"}[], which is impossible once $`C_ce^{-\gamma_c d} < 1/2`.

General case. Let $`g \in \mathcal{E}_\varsigma(d)` be nonnegative outside $`B(0,R)`,
$`R = c\sqrt d`. By {uses "lemma_rotational_average_properties"}[] and
{uses "lemma_rotational_average_nonzero"}[], $`h = \mathcal{R}g` is a nonzero radial element of
$`\mathcal{E}_\varsigma(d)` with the same eigenvalue, origin value and exterior sign. Let $`h_n`
be the radial Schwartz eigenfunctions of {uses "lemma_schwartz_approximation"}[], so
$`\widehat{h_n} = \varsigma h_n`, $`h_n(0) = 0`, $`h_n \to h` in $`L^1`. They need not be
nonnegative outside the ball, but there $`(h_n)_- \le |h_n - h|` because $`h \ge 0`; hence
$`\tfrac12\|h_n\|_1 = \int(h_n)_- \le \int_{|x|<R}|h_n| + \|h_n - h\|_1`, which is at most
$`C_ce^{-\gamma_c d}\|h_n\|_1 + \|h_n - h\|_1` by {uses "prop_3_1"}[]. Letting $`n \to \infty`
gives $`\|h\|_1/2 \le C_ce^{-\gamma_c d}\|h\|_1`, contradicting $`h \ne 0` for all sufficiently
large $`d`.
:::

:::theorem "thm_3_8" (lean := "CohnElkies.exists_manuscriptUniversalPackingIsLittleO")
There is a sequence $`\epsilon_d \to 0` such that, for every sufficiently large $`d` and every
$`F \in \mathcal{A}_d` ({uses "def_admissible_class"}[]), (equation (28))
$`\dfrac{F(0)}{\widehat F(0)}`
$`\ge \dfrac{2^d}{v_d}\Bigl(\sqrt{\dfrac{e}{2\pi}} - \epsilon_d\Bigr)^d`,
with $`v_d` from {uses "def_ball_volume"}[]. Formalized as
`CohnElkies.exists_manuscriptUniversalPackingIsLittleO`, with a nonnegative $`o(1)` sequence
$`\epsilon_d` and the inequality for every $`d \ge 1` and every $`F \in \mathcal{A}_d` (the radial
bound is transferred by `CohnElkies.Admissible.normalizedCost_radialize`); the explicit deficit
is `CohnElkies.manuscriptPackingDeficit` (`CohnElkies.manuscriptUniversalQuotientBound`), also
recorded in the field `universal_nonnegative_delta` of
`PackingBounds.SharpFullCohnElkiesManuscriptConclusions`. The scaling step is
`CohnElkies.normalizedCost_ge_of_no_antiFourierWitness`, and the resulting uniform lower bound
on normalized costs is `CohnElkies.uniformAdmissibleLowerBound_of_signRadius`.
:::

:::proof "thm_3_8"
By {uses "lemma_rotational_average_properties"}[] we may replace $`F` by its rotational average,
which preserves $`F(0)`, $`\widehat F(0)` and admissibility; so assume $`F` radial. Both
$`\widehat F(0) > 0` and $`F(0) > 0` ({uses "lemma_admissible_origin_pos"}[]), so
$`a = (\widehat F(0)/F(0))^{1/d} > 0` is defined (`CohnElkies.balancingScale`). Put $`h(x) = F(ax)`
(`CohnElkies.balanced`) and $`g = \widehat h - h` (`CohnElkies.antiFourierPart`). Fourier scaling
({uses "def_fourier_convention"}[]) and admissibility give (29)–(30):
$`\widehat h(\xi) = a^{-d}\widehat F(\xi/a)`, $`h(0) = \widehat h(0) = F(0)`, $`\widehat g = -g`
(as $`h` is even, $`\widehat{\widehat h} = h`), $`g(0) = 0`, and
$`g(x) = a^{-d}\widehat F(x/a) - F(ax) \ge 0` for $`|x| \ge 1/a`. Moreover $`g \ne 0`: otherwise
$`h = \widehat h \ge 0` while $`h(x) = F(ax) \le 0` for $`|x| \ge 1/a`, so $`h` would vanish outside
a ball and be self-Fourier, hence $`h = 0` by
{uses "lemma_compactly_supported_eigenfunction_zero"}[], contradicting $`h(0) = F(0) > 0`
(`CohnElkies.antiFourierPart_balanced_ne_zero`). Thus $`g` is a nonzero real radial Schwartz
anti-self-Fourier function with $`g(0) = 0`, nonnegative outside $`B(0,1/a)`. Fix
$`0 < c < 1/\pi`. If $`1/a \le c\sqrt d` then $`g \ge 0` outside $`B(0,c\sqrt d)`, which
{uses "prop_3_7"}[] forbids for $`d \ge d_0(c)`. Hence
$`(F(0)/\widehat F(0))^{1/d} = 1/a > c\sqrt d`
uniformly in $`F`, so
$`\liminf_{d\to\infty}\frac{1}{\sqrt d}\inf_{F\in\mathcal{A}_d}(F(0)/\widehat F(0))^{1/d} \ge c` for
every $`c < 1/\pi`. Taking the supremum over $`c` (a diagonal choice $`c_d \uparrow 1/\pi`) yields
(31): $`\inf_{F\in\mathcal{A}_d}(F(0)/\widehat F(0))^{1/d} \ge (1/\pi - o(1))\sqrt d` with the
$`o(1)` independent of $`F`. Combining (31) with $`v_d^{1/d} = (1+o(1))\sqrt{2\pi e/d}` from
{uses "lemma_stirling_ball_volume"}[], and $`\sqrt{2\pi e}/(2\pi) = \sqrt{e/(2\pi)}`, gives (28)
for a sequence $`\epsilon_d \to 0` independent of $`F`.
:::
