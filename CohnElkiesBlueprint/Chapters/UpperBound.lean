import Verso
import VersoManual
import VersoBlueprint
import CohnElkies

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The admissible primal upper bound" =>

The previous chapter established
$`\min\{\inf_{F\in\mathcal{A}_d}(F(0)/\widehat F(0))^{1/d},\ \mathsf{A}_-(d),\ \mathsf{A}_+(d)\}`
$`\ge (1/\pi - o(1))\sqrt d`.
We now explain how the upper bounds in the introduction reduce to constructing functions whose
sign changes occur at the same radius. Throughout, $`\ll` denotes an inequality up to an absolute
constant, $`\ll_\epsilon` up to a constant depending only on $`\epsilon`, and $`\asymp` means both
$`\ll` and $`\gg`. The chapter corresponds to the modules `CohnElkies/UpperBound/*.lean`; the
construction is generic in the polynomial factor (`CohnElkies.IsSaddlePolynomial`,
`CohnElkies.mellinProfile`), the Fourier pair $`(f_-, f_+)` being the case $`P = P_\pm` and the
self-Fourier function $`f_0` the case $`P = P_0` (module `CohnElkies.UpperBound.SelfFourier`,
`CohnElkies.fZero`, `CohnElkies.PZero`).

:::lemma_ "lemma_upper_bound_reduction" (lean := "CohnElkies.saddleSourceAdmissible")
Let $`R > 0` and let $`f_-, f_+` be real radial Schwartz functions on $`\mathbb{R}^d` with
$`\widehat{f_-} = f_+ > 0` everywhere, $`f_-(0) = f_+(0)`, and $`f_-(x) < 0` for $`|x| \ge R`. Then
$`F(x) = f_-(Rx)` belongs to $`\mathcal{A}_d` ({uses "def_admissible_class"}[]) with
$`F(0)/\widehat F(0) = R^d`, so $`\mathrm{LP}_d \le v_d(R/2)^d` ({uses "def_lp"}[]). The difference
$`g_- = f_+ - f_-` lies in $`\mathcal{E}_-(d)` with $`r(g_-) \le R`, so $`\mathsf{A}_-(d) \le R`.
If $`f_0` is a real radial Schwartz function with $`\widehat{f_0} = f_0`, $`f_0(0) = 0` and
$`f_0(x) > 0` for $`|x| \ge R`, then $`f_0 \in \mathcal{E}_+(d)` with $`r(f_0) \le R`, so
$`\mathsf{A}_+(d) \le R` (see {uses "def_sign_eigenfunction_class"}[],
{uses "def_sign_radius"}[], {uses "def_sign_uncertainty_constant"}[]).

The formalization proves the packing half for the saddle pair of Theorem 4.1, with the weak
signs $`f_+ \ge 0` everywhere and $`f_- \le 0` for $`|x| \ge R`: `CohnElkies.saddleSourceAdmissible`
builds the admissible function $`x \mapsto f_-(Rx)` and
`CohnElkies.saddleSourceAdmissible_normalizedCost` computes its normalized cost
$`(F(0)/\widehat F(0))^{1/d}/\sqrt d = R/\sqrt d`. The consequences for $`\mathsf{A}_\pm(d)`
are `CohnElkies.RadialEigenfunction.signUncertaintyConstant_le_of_nonneg_outside` (module
`CohnElkies.SignUncertainty.UpperBound`): a radial Schwartz eigenfunction that is nonnegative
outside $`B(0,R)` is, through its real part, an element of $`\mathcal{E}_\varsigma(d)` with
$`r \le R`, so $`\mathsf{A}_\varsigma(d) \le R`.
:::

:::proof "lemma_upper_bound_reduction"
Fourier scaling ({uses "def_fourier_convention"}[]) gives $`\widehat F(\xi) = R^{-d}f_+(\xi/R) > 0`,
$`F(x) = f_-(Rx) < 0` for $`|x| \ge 1`, and $`F(0)/\widehat F(0) = R^df_-(0)/f_+(0) = R^d`. For
$`g_- = f_+ - f_-`: since $`f_-` is even, $`\widehat{f_+} = \widehat{\widehat{f_-}} = f_-`, so
$`\widehat{g_-} = f_- - f_+ = -g_-`; $`g_-(0) = 0`; $`g_-(x) = f_+(x) - f_-(x) > 0` for
$`|x| \ge R`,
so $`g_- \ne 0` and $`r(g_-) \le R`. Schwartz functions are continuous and integrable, so
$`g_-` and $`f_0` lie in the respective classes and the infima give the bounds on
$`\mathsf{A}_\pm(d)`.
:::

Thus all the upper bounds reduce to producing one Fourier pair, one self-Fourier function, and a
radius $`R = (1/\pi + o(1))\sqrt d`.

:::theorem "thm_4_1" (lean := "CohnElkies.saddleSourceEventualSigns")
There is $`\epsilon_0 > 0` such that, for every fixed $`0 < \epsilon < \epsilon_0` and every
sufficiently large dimension $`d`, there exist real radial Schwartz functions $`f_-, f_+, f_0` on
$`\mathbb{R}^d` and a radius $`R_{\epsilon,d} > 0` such that $`f_+ > 0` everywhere,
$`f_-(x) < 0 < f_0(x)` whenever $`|x| \ge R_{\epsilon,d}`, and
$`\widehat{f_-} = f_+`, $`\widehat{f_0} = f_0`, $`f_-(0) = f_+(0) > 0`, $`f_0(0) = 0`.
Moreover $`\lim_{\epsilon\downarrow0}\lim_{d\to\infty}R_{\epsilon,d}/\sqrt d = 1/\pi`, where the
inner limit exists for each fixed $`\epsilon`.

Formalized for the Fourier pair: the functions are `CohnElkies.fMinusFun` and
`CohnElkies.fPlusFun` (radial extensions of the profiles `CohnElkies.fMinus`, `CohnElkies.fPlus`),
Schwartz by `CohnElkies.minusSaddleSchwartz`, `CohnElkies.plusSaddleSchwartz` and realized as
test functions by `CohnElkies.saddleSourceSchwartzRealization`; the radius is `CohnElkies.R_ε`;
the sign pattern $`f_+ \ge 0` everywhere and $`f_- \le 0` for $`|x| \ge R_{\epsilon,d}`, for all
small $`\epsilon` and large $`d`, is `CohnElkies.saddleSourceEventualSigns` (strict signs hold at
the saddle radii, {bpref "cor_4_9"}[]); the limits are
`CohnElkies.tendsto_saddleSourceRadius_normalized`
($`R_{\epsilon,d}/\sqrt d \to \alpha_\epsilon`, `CohnElkies.α_ε`) and
`CohnElkies.tendsto_limitingSaddleRadius` ($`\alpha_\epsilon \to 1/\pi`). The self-Fourier
function is `CohnElkies.fZero` with `CohnElkies.fourier_zeroSaddleSchwartz`
($`\widehat{f_0} = f_0`) and the strict positivity `CohnElkies.eventually_fZero_re_pos_of_radius`
for $`|x| \ge R_{\epsilon,d}`; the three functions together are
`CohnElkies.eventually_exists_radialEigenfunction_fZero` and `CohnElkies.saddleSourceEventualSigns`.
:::

# Outline of the construction

In Mellin coordinates, (10) reduces the Fourier symmetries to reflection of the frequency.

:::lemma_ "lemma_gaussian_mellin" (lean := "CohnElkies.mellinMultiplier_mul_E_neg")
The Gaussian $`g_G(r) = 2\pi^{\lambda/2}e^{-\pi r^2}` has critical-line Mellin transform
({uses "def_radial_mellin"}[])
$`E^G_\lambda(t) = X_{g_G}(t) = \pi^{it/2}\Gamma\bigl(\tfrac{\lambda - it}{2}\bigr)`,
and with $`m_\lambda` from {uses "eq_10_critical_line"}[] it obeys
$`m_\lambda(t)E^G_\lambda(-t) = E^G_\lambda(t)`. Consequently multiplication of $`E^G_\lambda`
by an even factor preserves the Fourier symmetry.

The formalization states the consequence directly for the perturbed envelope
$`E_\lambda = E^G_\lambda e^{\lambda h_\epsilon(\cdot/\lambda)}` of
{bpref "eq_38_envelope_polynomials"}[]: `CohnElkies.mellinMultiplier_mul_E_neg` is
$`m_\lambda(t)E_\lambda(-t) = E_\lambda(t)`, from which
`CohnElkies.mellinMultiplier_mul_spectrum_neg` derives $`m_\lambda(t)X_P(-t) = X_Q(t)` for
Mellin data $`X_P(t) = E_\lambda(t)P(t/\lambda)` whenever $`P(-\zeta) = Q(\zeta)`; the
conjugation symmetry is `CohnElkies.saddleEnvelope_conj`, and `CohnElkies.mellinEnvelope_vertical`
passes between the frequency $`t` and the Mellin variable $`z = \lambda - it`. The Gaussian case
$`h_\epsilon = 0` is not isolated.
:::

:::proof "lemma_gaussian_mellin"
$`\int_0^\infty e^{-\pi r^2}r^{z-1}\,dr = \tfrac12\pi^{-z/2}\Gamma(z/2)` at $`z = \lambda - it`
gives
the formula, and the identity $`m_\lambda(t)E^G_\lambda(-t) = E^G_\lambda(t)` is immediate from the
definition of $`m_\lambda`.
:::

We choose $`E_\lambda(t) = E^G_\lambda(t)e^{\lambda h_\epsilon(t/\lambda)}` with an even
perturbation
$`h_\epsilon` determined by a signed density $`w` (equation (36) below). The variable $`a` in that
density parametrizes radial dilations: the Mellin multiplier $`\cos(at/\lambda) - 1` corresponds to
$`g(r) \mapsto \tfrac12\bigl(e^ag(re^{a/\lambda}) + e^{-a}g(re^{-a/\lambda})\bigr) - g(r)`. A shell
is an interval of these dilation parameters supporting one component of $`w`: a negative
component $`w_s` moves the sign radius inward, and a positive component $`w_B`, supported on much
larger dilation parameters, restores decay at every nonzero Mellin frequency. The common envelope
is multiplied by polynomials $`P_-, P_+, P_0`; reflection exchanges $`P_-` and $`P_+` and fixes
$`P_0`. The first gamma pole, at normalized frequency $`\zeta = -i`, controls the value at the
origin: $`P_0` cancels it, while $`P_\pm` retain equal positive residues. On the imaginary axis
$`P_+(iu) > 0` for $`u > -1`, whereas $`P_-(iu) < 0` and $`P_0(iu) > 0` just above $`u = 1`; the
essential contour is $`t = \lambda(T + iu)` with $`u \approx 1`. On this contour the radius
$`r = e^{v(u)}` at which the Mellin integrand is stationary at $`T = 0` satisfies, for fixed
$`u > -1`,
$`e^{v(u)}/\sqrt d \to \sqrt{(1+u)/(4\pi)}\,\exp\bigl(\int_0^\infty w(a)a\sinh(ua)\,da\bigr)`.
Negative $`w` decreases the stationary radius when $`u > 0`, but also reduces the decay of the
Mellin integrand away from $`T = 0`. At $`u = 1`, after dividing the damping by $`\lambda`, the
limiting gamma contribution has density $`e^{-2a}/(2a^2)`, while the perturbation contributes
$`w(a)\cosh a`; a sufficient pointwise condition for nonnegative total damping is
$`|w(a)|\cosh a \le e^{-2a}/(2a^2)`.

:::lemma_ "eq_32_ideal_density" (lean := "CohnElkies.integral_wallisRadiusIntegrand")
The ideal density $`w_*(a) = -\dfrac{e^{-2a}}{2a^2\cosh a}` saturates the pointwise damping
constraint and gives the greatest inward displacement (equation (32)):
$`\int_0^\infty w_*(a)\,a\sinh a\,da = -\tfrac12\log\dfrac{\pi}{2}`.
Since the Gaussian stationary radius at $`u = 1` is $`(2\pi)^{-1/2}\sqrt d`, this displacement
gives $`\dfrac{1}{\sqrt{2\pi}}\exp\bigl(-\tfrac12\log\tfrac{\pi}{2}\bigr) = \dfrac{1}{\pi}`
(equation (33)). Formalized as `CohnElkies.integral_wallisRadiusIntegrand` for the integrand
`CohnElkies.wallisRadiusIntegrand`, $`-e^{-2a}\tanh(a)/(2a)`; the constant $`1/\pi` is reached in
`CohnElkies.tendsto_limitingSaddleRadius`.
:::

:::proof "eq_32_ideal_density"
Since $`w_*(a)a\sinh a = -e^{-2a}\tanh(a)/(2a)`, the substitution $`x = 2a` turns the integral into
$`-\tfrac12\int_0^\infty K(x)\,dx` with the Laplace kernel
$`K(x) = e^{-x}(1 - e^{-x})/(x(1 + e^{-x}))` (`Real.Wallis.laplaceKernel`). Expand
$`e^{-2a}\tanh a = \sum_{k\ge0}(-1)^k(e^{-2(k+1)a} - e^{-2(k+2)a})` and apply Frullani's integral
$`\int_0^\infty(e^{-\alpha a} - e^{-\beta a})\,da/a = \log(\beta/\alpha)` termwise (the alternating
partial sums are dominated):
$`\int_0^\infty e^{-2a}\tanh(a)\,da/a = \sum_{k\ge0}(-1)^k\log\frac{k+2}{k+1}`,
the logarithm of the Wallis product $`\frac21\cdot\frac23\cdot\frac43\cdot\frac45\cdots = \pi/2`
(`Real.Wallis.integral_laplaceKernel`, from Mathlib's `Real.Wallis.tendsto_W_nhds_pi_div_two`),
equivalently a consequence of the gamma duplication formula.
:::

Although its Mellin perturbation is well defined, $`w_*` has infinite mass at zero and saturates
the gamma damping, so its Mellin factor lacks the strict decay needed for a Schwartz function.
Instead we truncate it to a bounded interval and taper it slightly, obtaining a negative shell
$`w_s` that preserves the displacement up to $`O(\epsilon)` while leaving a definite damping
margin. This margin suffices near $`u = 1` but not on contours with arbitrarily large $`u`; a
second shell $`w_B`, supported on $`[B, B+1]`, has negligible effect on the stationary radius at
$`u = u_0` while dominating the negative shell at every frequency when $`u \ge U > u_0`. Using an
interval rather than a single dilation avoids frequencies at which its damping would vanish.

# The Mellin ansatz

:::group "grp_mellin_ansatz"
Parameters, shells, perturbation, envelope and polynomials of the construction (Section 4.2).
:::

:::definition "eq_34_parameters" (lean := "CohnElkies.a₀ε") (parent := "grp_mellin_ansatz")
Put $`\lambda = d/2`; throughout the construction $`\epsilon` is fixed before $`d \to \infty`.
Constants in $`O_\epsilon(\cdot)`, $`\ll_\epsilon` may depend on $`\epsilon` but not on $`d` or on
the saddle parameter. Introduce cutoffs $`0 < a_0 < A < B`, a positive-shell amplitude $`Q > 0`,
and $`u_0 = 1 + \dfrac{\epsilon}{4}`, $`U = 1 + \dfrac{\epsilon}{2}`, $`C_0 = A + a_0^{-1}`.
The requirements as $`\epsilon \downarrow 0` are $`a_0 = o(\epsilon)`, $`e^{-2A}/A = o(\epsilon)`,
$`\epsilon A = o(1)`, $`A = o(B)`, $`BQe^{(u_0-1)B} = o(1)` and $`C_0Q^{-1}e^{-(U-1)(B-A)} = o(1)`.
The report's realization (equation (34)) is
$`a_0 = \epsilon^2`, $`A = \log(1/\epsilon)`, $`B = \epsilon^{-3}`,
$`q_\epsilon = \dfrac{(u_0-1)+(U-1)}{2} = \dfrac{3\epsilon}{8}`, $`Q = e^{-q_\epsilon B}`,
$`b(a) = 1 - 2\epsilon(1+a)`, $`\beta = u_0 - 1 = \dfrac{\epsilon}{4}`.

The formalization uses exactly these values (the original formalization had larger safety
margins, $`a_0 = \epsilon^3`, $`A = 10\log(1/\epsilon)`, $`b(a) = 1 - 10\epsilon(1+a)` and
$`N = \lceil 20\log\lambda\rceil` in Lemma 4.10; they were switched to the report's values, see
the final chapter). For sufficiently small
$`\epsilon`, $`b > 0` on $`[a_0, A]` and $`B > A + 1`. The parameters are `CohnElkies.a₀ε`,
`CohnElkies.Aε`, `CohnElkies.Bε`, `CohnElkies.Qε`, `CohnElkies.bε` and `CohnElkies.β`;
$`u_0`, $`U` and $`C_0` appear inline as `1 + ε/4`, `1 + ε/2` and
`CohnElkies.upperShellShortCoefficient`.
:::

:::definition "eq_35_shells" (lean := "CohnElkies.w_s") (parent := "grp_mellin_ansatz")
With the parameters of {uses "eq_34_parameters"}[], the negative and positive shells are
$`w_s(a) = -\dfrac{b(a)e^{-2a}}{2a^2\cosh a}\,\mathbf 1_{[a_0,A]}(a)`,
$`w_B(a) = \dfrac{Q}{\cosh a}\,\mathbf 1_{[B,B+1]}(a)`,
and $`w = w_s + w_B` (equation (35)). Formalized as `CohnElkies.w_s` and `CohnElkies.w_B`, the
densities without their indicator functions; the intervals $`[a_0, A]` and $`[B, B+1]` enter as
integration domains.
:::

:::definition "eq_36_mellin_perturbation" (lean := "CohnElkies.h_ε") (parent := "grp_mellin_ansatz")
The signed density $`w` of {uses "eq_35_shells"}[] determines the even entire function
$`h_\epsilon(\zeta) = \int_0^\infty w(a)\bigl(\cos(a\zeta) - 1\bigr)\,da` (equation (36)). It is
real on the real and imaginary axes, with
$`h_\epsilon(iu) = \int_0^\infty w(a)(\cosh(au) - 1)\,da` and
$`ih_\epsilon'(iu) = \int_0^\infty w(a)\,a\sinh(ua)\,da`. Formalized as `CohnElkies.h_ε`.
:::

:::definition "eq_37_gamma_damping_density" (lean := "CohnElkies.μ_ℓ") (parent := "grp_mellin_ansatz")
For $`\eta > 0` and $`\lambda > 0`, the positive density describing the unperturbed gamma damping
is $`\mu_{\lambda,\eta}(a) = \dfrac{e^{-\eta a}}{a(1 - e^{-2a/\lambda})}` for $`a > 0`
(equation (37)). Formalized as `CohnElkies.μ_ℓ`.
:::

:::lemma_ "lemma_4_2" (lean := "CohnElkies.positiveShellRadiusContribution_bounds") (parent := "grp_mellin_ansatz")
There are absolute constants $`\epsilon_0, c, C > 0` such that, for every
$`0 < \epsilon < \epsilon_0`,
the shells of {uses "eq_35_shells"}[] have the following properties, with
$`\mu_{\lambda,\eta}` from {uses "eq_37_gamma_damping_density"}[]. For every $`\lambda > 0`,
$`-1 < u \le U` and $`a \in [a_0, A]`:
$`\lambda|w_s(a)|\cosh(ua) \le (1 - c\epsilon)\,\mu_{\lambda,1+u}(a)`.
At the target saddle,
$`\int_{a_0}^Aw_s(a)\,a\sinh(u_0a)\,da = -\tfrac12\log\dfrac{\pi}{2} + O(\epsilon)`,
$`0 \le \int_B^{B+1}w_B(a)\,a\sinh(u_0a)\,da \le Ce^{-c/\epsilon^2}`.
Finally, the target-saddle contribution and the remote-saddle domination ratio satisfy
$`BQe^{(u_0-1)B} \le Ce^{-c/\epsilon^2}` and $`C_0Q^{-1}e^{-(U-1)(B-A)} \le Ce^{-c/\epsilon^2}`.
The implicit constant in $`O(\epsilon)` is absolute.

The four claims are formalized separately, in the forms the later lemmas use. The damping
margin is `CohnElkies.upperFirstBranch_shortRatio_le`:
$`b(a)e^{(u-1)a}\cosh(ua)/\cosh a \le 1 - 2\epsilon` for $`-1 \le u \le U`, which gives
the absolute constant $`c = 2` (with the report's taper $`b(0) = 1 - 2\epsilon`, no larger
constant is possible). The negative-shell displacement is stated as a limit,
$`\int_{a_0}^A w_s(a)a\sinh(u_0a)\,da \to -\tfrac12\log(\pi/2)` as $`\epsilon \downarrow 0`
(`CohnElkies.tendsto_shortShellRadiusContribution` with
`CohnElkies.integral_wallisRadiusIntegrand`),
which replaces the $`O(\epsilon)` rate. The positive-shell displacement is
`CohnElkies.positiveShellRadiusContribution_bounds`,
$`0 \le \int_B^{B+1}w_B(a)a\sinh(u_0a)\,da \le (B+1)Qe^{(u_0-1)(B+1)}`, with the majorant
`CohnElkies.shellRadiusMajorant` tending to $`0` (`CohnElkies.tendsto_shellRadiusMajorant`).
The separation is `CohnElkies.eventually_upper_shell_parameter_margin`,
$`C_0e^{(U-1)A} \le Qe^{(U-1)B}/5000` for all small $`\epsilon`.
:::

:::proof "lemma_4_2"
Displacement. The negative shell agrees with $`w_*` of {uses "eq_32_ideal_density"}[] up to its
taper on $`[a_0,A]`. Since $`\tanh a \le \min(a,1)`, the omitted contributions are
$`\int_0^{a_0}|w_*|a\sinh a\,da = O(a_0)` and $`\int_A^\infty|w_*|a\sinh a\,da = O(e^{-2A}/A)`,
both $`o(\epsilon)`. The taper changes the integral by
$`\int_{a_0}^A|1 - b(a)||w_*(a)|a\sinh a\,da`
$`= O\bigl(\epsilon\int_0^\infty(1+a)e^{-2a}\tanh(a)\,da/a\bigr)`,
which is $`O(\epsilon)`. Moving from $`u = 1` to $`u = u_0` costs another $`O(\epsilon)`: the
mean-value theorem gives $`|\sinh(u_0a) - \sinh a| \le (u_0-1)a\cosh(u_0a)`, so
$`\int_{a_0}^A|w_s(a)|a|\sinh(u_0a) - \sinh a|\,da`
$`\ll \epsilon\int_0^\infty e^{-2a}\cosh(u_0a)/\cosh a\,da \ll \epsilon`.
Together with (32) this gives the negative-shell displacement.

Damping margin. Divide the negative density by $`\mu_{\lambda,1+u}`:
$`\dfrac{\lambda|w_s(a)|\cosh(ua)}{\mu_{\lambda,1+u}(a)}`
$`= b(a)\,\Theta_\lambda(a)\,e^{(u-1)a}\,\dfrac{\cosh(ua)}{\cosh a}`,
$`\Theta_\lambda(a) = \dfrac{1 - e^{-2a/\lambda}}{2a/\lambda} \in (0,1]`
(by $`1 - e^{-x} \le x`). For $`-1 < u \le 1`, both $`e^{(u-1)a}` and $`\cosh(ua)/\cosh a` are at
most $`1`, so the ratio is at most $`b(a) \le 1 - 2\epsilon`. For $`1 \le u \le U`, the inequality
$`\cosh(ua) \le e^{(u-1)a}\cosh a` bounds it by $`b(a)e^{2(u-1)a} \le b(a)e^{\epsilon a}`, and
$`b(a)e^{\epsilon a} \le e^{-2\epsilon(1+a)}e^{\epsilon a} \le e^{-2\epsilon} \le 1 - c\epsilon`.
Thus the taper retains a damping margin of order $`\epsilon` on every contour $`-1 < u \le U`.

Positive shell. At $`u_0`, $`\sinh(u_0a)/\cosh a \le e^{(u_0-1)a}`, hence
$`0 \le \int_B^{B+1}w_B(a)a\sinh(u_0a)\,da \le (B+1)Qe^{(u_0-1)(B+1)}`. The amplitude in (34) has
exponential slope $`q_\epsilon` strictly between $`u_0 - 1` and $`U - 1`, so
$`Qe^{(u_0-1)B} = e^{-\epsilon B/8}` and $`Qe^{(U-1)B} = e^{\epsilon B/8}`. Since
$`\epsilon B = \epsilon^{-2}` while $`B`, $`C_0` and $`e^{(U-1)A}` grow only polynomially in
$`1/\epsilon`, all three separation quantities are $`O(e^{-c'/\epsilon^2})`.
:::

The shells determine the common envelope; it remains to impose the Fourier symmetries and
select the signs. The first gamma pole occurs at $`t = -i\lambda`, i.e. $`\zeta = -i`.

:::definition "eq_38_envelope_polynomials" (lean := "CohnElkies.E") (parent := "grp_mellin_ansatz")
With $`h_\epsilon` from {uses "eq_36_mellin_perturbation"}[] and $`\beta` from
{uses "eq_34_parameters"}[], define (equation (38))
$`E_\lambda(t)`
$`= \pi^{it/2}\,\Gamma\Bigl(\dfrac{\lambda - it}{2}\Bigr)\,e^{\lambda h_\epsilon(t/\lambda)}`,
$`P_\pm(\zeta) = 1 + \zeta^2 + \beta \pm i\zeta(1+\zeta^2)`, $`P_0(\zeta) = -(1+\zeta^2)`,
and for $`j \in \{-, 0, +\}` the Mellin data and radial profiles
$`X_{f_j}(t) = E_\lambda(t)P_j(t/\lambda)`,
$`f_j(r) = \dfrac{r^{-\lambda}}{2\pi}\int_{\mathbb{R}}X_{f_j}(t)r^{it}\,dt` ($`r > 0`).

Formalized as `CohnElkies.E` (the envelope), `CohnElkies.PPlus`, `CohnElkies.PMinus`,
`CohnElkies.XPlus`, `CohnElkies.XMinus` and, in the Mellin variable $`z = \lambda - it`,
`CohnElkies.mellinEnvelope`, `CohnElkies.MPlus`, `CohnElkies.MMinus` (instances of
`CohnElkies.mellinData` for a polynomial factor $`P`); the profiles are `CohnElkies.fPlus` and
`CohnElkies.fMinus`, defined for $`r > 0` by the inverse Mellin integral and at $`r = 0` by the
value `CohnElkies.originValue` of (42). The polynomial $`P_0` is `CohnElkies.PZero`, its spectrum
and Mellin data are `CohnElkies.XZero`, `CohnElkies.MZero`, and the profile $`f_0` is
`CohnElkies.fZero` (origin value $`0`, since $`P_0(-i) = 0`: `CohnElkies.poleResidue_PZero_zero`).
:::

:::lemma_ "eq_39_polynomial_values" (lean := "CohnElkies.plusPolynomial_imaginary") (parent := "grp_mellin_ansatz")
The polynomials of {uses "eq_38_envelope_polynomials"}[] satisfy $`P_-(-\zeta) = P_+(\zeta)`,
$`P_0(-\zeta) = P_0(\zeta)`, $`\overline{P_j(\zeta)} = P_j(-\bar\zeta)`,
$`P_\pm(-i) = \beta > 0`, $`P_0(-i) = 0`, and on the imaginary axis (equation (39))
$`P_+(iu) = \beta + (1-u)^2(1+u)`, $`P_-(iu) = \beta + (1-u)(1+u)^2`, $`P_0(iu) = u^2 - 1`.
Consequently $`P_+(iu) > 0` for every $`u > -1`, whereas $`\beta = u_0 - 1` gives
$`P_-(iu_0) = -\beta(3 + 4\beta + \beta^2) < 0` and $`P_0(iu_0) = \beta(2+\beta) > 0`, and these
signs persist for all $`u \ge u_0`.

Formalized, for $`P_\pm`, as `CohnElkies.plusPolynomial_imaginary`,
`CohnElkies.minusPolynomial_imaginary` (the values on the imaginary axis),
`CohnElkies.plusPolynomial_imaginary_re_pos`, `CohnElkies.minusPolynomial_imaginary_re_neg`
(their signs for $`u > -1`, resp. $`u \ge u_0`), `CohnElkies.plusPolynomial_neg_I`,
`CohnElkies.minusPolynomial_neg_I` (the value $`\beta` at $`-i`),
`CohnElkies.minusPolynomial_neg` (reflection) and `CohnElkies.plusPolynomial_conj`,
`CohnElkies.minusPolynomial_conj` (conjugation).
:::

:::proof "eq_39_polynomial_values"
Direct substitution of $`\zeta = iu` and $`\zeta = -i`.
:::

:::lemma_ "lemma_4_3" (lean := "CohnElkies.saddleSource_fourier_minus_eq_plus") (parent := "grp_mellin_ansatz")
For every sufficiently small $`\epsilon > 0` and every integer $`d \ge 1`, with $`\lambda = d/2`,
the
inverse Mellin integrals of {uses "eq_38_envelope_polynomials"}[], initially defined for $`r > 0`,
extend to $`f_j \in \mathcal{S}_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})` for $`j \in \{-,0,+\}`.
These
extensions satisfy (equations (40), (42))
$`\widehat{f_-} = f_+`, $`\widehat{f_0} = f_0`,
$`f_+(0) = f_-(0) = 2\pi^{\lambda/2}e^{\lambda h_\epsilon(i)}\beta > 0`,
$`f_0(0) = 0`. More generally the pole $`t = -i(\lambda+2n)`, $`n \ge 0`, contributes to $`f_j(r)`
the term (equation (41))
$`2\pi^{\lambda/2+n}\,r^{2n}\,\dfrac{(-1)^n}{n!}\,e^{\lambda h_\epsilon(\zeta_n)}\,P_j(\zeta_n)`,
where
$`\zeta_n = -i(1 + 2n/\lambda)`.

Formalized for the pair: the Fourier identity (40) is
`CohnElkies.saddleSource_fourier_minus_eq_plus`,
the Schwartz extensions are `CohnElkies.plusSaddleSchwartz` and `CohnElkies.minusSaddleSchwartz`
(smoothness `CohnElkies.mellinProfileFun_contDiff` and the generic Schwartz construction
`CohnElkies.mellinProfileSchwartz`, both for an arbitrary polynomial factor),
the origin values (42) are `CohnElkies.saddleSource_zero_pos` with `CohnElkies.originValue`, and
the pole decomposition behind (41) is `CohnElkies.mellinData_nthPole_decomposition` with the
residues `CohnElkies.poleResidue`. The counterparts for $`f_0` are `CohnElkies.zeroSaddleSchwartz`
(`CohnElkies.fZeroFun_contDiff`, `CohnElkies.fZeroFun_im`) and
`CohnElkies.fourier_zeroSaddleSchwartz`, obtained from the generic construction
(`CohnElkies.mellinProfileSchwartz`, `CohnElkies.fourier_eq_of_mellinProfile` with $`P = Q = P_0`
and $`P_0(-z) = P_0(z)`).
:::

:::proof "lemma_4_3"
Fix $`d` and $`\epsilon`. Compact support of $`w` makes $`h_\epsilon` entire, and on each horizontal
line $`t = s + i\tau` it satisfies
$`|h_\epsilon((s+i\tau)/\lambda)| \le 2\int_0^\infty|w(a)|\cosh(a\tau/\lambda)\,da`,
so the perturbation is bounded on every fixed horizontal strip. Uniformly for $`\tau` in compact
pole-free intervals, the gamma bounds of {uses "lemma_gamma_asymptotics"}[] (iv) give
$`|X_{f_j}(s+i\tau)| \le C_{d,\epsilon,\tau}(1+|s|)^{-2}` (the report has the sharper
$`(1+|s|)^{(\lambda+\tau-1)/2+3}e^{-\pi|s|/4}`), so the vertical sides of rectangular contour
shifts tend to zero. The only poles of the integrand are those of $`\Gamma((\lambda - it)/2)`, at
$`t = -i(\lambda + 2n)`, $`n = 0,1,2,\ldots`. Shifting the contour upward to
$`\operatorname{Im} t = \tau > 0` gives $`f_j(r) = O_\tau(r^{-\lambda-\tau})` as $`r \to \infty`,
for every $`\tau`, also after differentiation in $`r`: rapid decay. Shifting downward past the
poles, the residue $`\operatorname{Res}_{z=-n}\Gamma(z) = (-1)^n/n!` (equivalently $`2i(-1)^n/n!`
in the variable $`t`) gives the terms (41), an expansion of $`f_j` in even powers $`r^{2n}` with
a remainder of arbitrarily high order; thus $`f_j` extends to a smooth radial function on
$`\mathbb{R}^d`, and it is Schwartz. Conjugate symmetry $`X_{f_j}(-t) = \overline{X_{f_j}(t)}` for
real $`t` (from {uses "eq_39_polynomial_values"}[], realness of $`h_\epsilon` on $`\mathbb{R}`,
and $`\Gamma(\bar z) = \overline{\Gamma(z)}`) makes the extension real.

Fourier symmetries. Because $`h_\epsilon` is even, {uses "lemma_gaussian_mellin"}[] gives
$`m_\lambda(t)E_\lambda(-t) = E_\lambda(t)`; with $`P_-(-\zeta) = P_+(\zeta)` and $`P_0` even,
$`m_\lambda(t)X_{f_-}(-t) = X_{f_+}(t)` and $`m_\lambda(t)X_{f_0}(-t) = X_{f_0}(t)`. By
{uses "eq_10_critical_line"}[], $`X_{\widehat{f_-}} = X_{f_+}` and $`X_{\widehat{f_0}} = X_{f_0}`,
and
injectivity of the Mellin transform on the critical line ({uses "lemma_log_profile_schwartz"}[])
gives (40).

Origin values. The term $`n = 0` of (41) is the value at $`r = 0`; evenness gives
$`h_\epsilon(-i) = h_\epsilon(i)`, and $`P_\pm(-i) = \beta`, $`P_0(-i) = 0` give (42).
:::

# Saddle geometry

:::group "grp_saddle_geometry"
Stationary radii, the centered phase, damping and moment quantities, and the damping estimates
(Section 4.3: (43)–(49) and Lemmas 4.4–4.7).
:::

:::definition "eq_43_saddle_parameters" (lean := "CohnElkies.u_star") (parent := "grp_saddle_geometry")
Recall $`u_0`, $`U` from {uses "eq_34_parameters"}[] and set (equation (43))
$`u_* = -1 + \dfrac{\log\lambda}{4\lambda}`. For $`u > -1` put $`\eta = 1 + u > 0`,
$`m = \dfrac{\lambda\eta}{2}`, and use $`\psi = (\log\Gamma)'` from {uses "def_digamma"}[], with the
branch of $`\log\Gamma` real on the positive axis. Note
$`m \ge \lambda(1+u_*)/2 = \tfrac18\log\lambda`
for $`u \ge u_*`. Formalized as `CohnElkies.u_star`; $`\eta` and $`m` have no separate names and
appear as the arguments `1 + u` and `ℓ * (1 + u) / 2`.
:::

:::definition "eq_44_stationary_radius" (lean := "CohnElkies.vℓ") (parent := "grp_saddle_geometry")
On the contour $`t = \lambda(T + iu)`, the logarithm of $`E_\lambda(t)r^{it}` is
$`\tfrac{i\lambda(T+iu)}{2}\log\pi + \log\Gamma\bigl(m - \tfrac{i\lambda T}{2}\bigr)`
$`+ \lambda h_\epsilon(T+iu) + i\lambda(T+iu)\log r`,
whose $`T`-derivative at $`T = 0` is
$`i\lambda(\tfrac12\log\pi - \tfrac12\psi(m) - \int_0^\infty w(a)a\sinh(ua)\,da + \log r)`.
Thus $`T = 0` is stationary precisely when $`r = e^{v(u)}`, where (equation (44))
$`v(u) = -\tfrac12\log\pi + \tfrac12\psi(m) + \int_0^\infty w(a)\,a\sinh(ua)\,da`,
$`V(u) = v'(u) = \dfrac{\lambda}{4}\psi^{(1)}(m) + \int_0^\infty w(a)\,a^2\cosh(ua)\,da`.
Uses {uses "eq_43_saddle_parameters"}[], {uses "eq_36_mellin_perturbation"}[]. Formalized as
`CohnElkies.vℓ` (also `CohnElkies.logRadius` in terms of $`d`) and `CohnElkies.V_u`; the
formalization does not differentiate $`v`, it defines $`V(u)` directly as the saddle variance
`CohnElkies.upperSaddleVariance` of {bpref "eq_48_moments"}[].
:::

:::lemma_ "eq_45_log_gamma_integral" (lean := "CohnElkies.exp_G_ℓη") (parent := "grp_saddle_geometry")
For $`\lambda, \eta > 0`, $`m = \lambda\eta/2`, and $`T \in \mathbb{R}`, with $`\mu_{\lambda,\eta}`
from
{uses "eq_37_gamma_damping_density"}[] (equation (45)),
$`G_{\lambda,\eta}(T) := \log\Gamma\bigl(m - \tfrac{i\lambda T}{2}\bigr) - \log\Gamma(m)`
$`+ \tfrac{i\lambda T}{2}\psi(m)`
equals $`\int_0^\infty(e^{iaT} - 1 - iaT)\,\mu_{\lambda,\eta}(a)\,da`,
and $`D_\gamma(T) := -\operatorname{Re}G_{\lambda,\eta}(T)`
$`= \int_0^\infty(1 - \cos(aT))\,\mu_{\lambda,\eta}(a)\,da \ge 0`.
Moreover $`\int_0^\infty a^2\mu_{\lambda,\eta}(a)\,da = \tfrac{\lambda^2}{4}\psi^{(1)}(m)` and
$`\int_0^\infty a^3\mu_{\lambda,\eta}(a)\,da = -\tfrac{\lambda^3}{8}\psi^{(2)}(m)`.

Formalized with $`G_{\lambda,\eta}` defined by the integral (`CohnElkies.G_ℓη`) and the identity
stated in exponentiated form,
$`e^{G_{\lambda,\eta}(T)} = \Gamma(m - i\lambda T/2)\,e^{i\lambda T\psi(m)/2}/\Gamma(m)`
(`CohnElkies.exp_G_ℓη`); the damping is `CohnElkies.D_γ`, and the moments appear as the
quantities `CohnElkies.V_γ` and `CohnElkies.M₃_γ` of {bpref "eq_48_moments"}[] with explicit
bounds instead of the polygamma identities.
:::

:::proof "eq_45_log_gamma_integral"
Apply the Binet-type representation of {uses "lemma_gamma_asymptotics"}[] (iii) with $`z = m`,
$`w = -i\lambda T/2`, and substitute $`a = \lambda s/2`. The moment identities follow by
differentiating (45) twice and three times at $`T = 0`. In particular the gamma function in the
Mellin envelope always damps the integrand away from $`T = 0`.
:::

:::definition "eq_46_centered_phase" (lean := "CohnElkies.L_u") (parent := "grp_saddle_geometry")
Normalize $`E_\lambda(\lambda(T+iu))r^{i\lambda T}` by the positive number
$`E_\lambda(i\lambda u) = \pi^{-\lambda u/2}\Gamma(m)e^{\lambda h_\epsilon(iu)}` and set
$`r = e^{v(u)}`.
The linear terms cancel by the saddle equation, and (36) gives (equations (46), (47))
$`\mathcal{L}_u(T) := \log\dfrac{E_\lambda(\lambda(T+iu))}{E_\lambda(i\lambda u)} + i\lambda Tv(u)`,
which equals
$`G_{\lambda,\eta}(T) + \lambda\int_0^\infty w(a)\cosh(ua)(\cos(aT)-1)\,da`
$`+ i\lambda\int_0^\infty w(a)\sinh(ua)(aT - \sin(aT))\,da`,
and
$`D_u(T) := -\operatorname{Re}\mathcal{L}_u(T) = D_\gamma(T)`
$`+ \lambda\int_0^\infty w(a)\cosh(ua)(1 - \cos(aT))\,da`.
Uses {uses "eq_44_stationary_radius"}[] and {uses "eq_45_log_gamma_integral"}[]. Equation (47)
isolates the main difficulty: $`w_s` reduces $`D_u`, while $`w_B` increases it. We must prove
$`D_u(T) > 0` for every $`T \ne 0` and $`V(u) > 0` for every $`u \ge u_*`. Formalized as
`CohnElkies.L_u` (gamma phase plus the shell phase `CohnElkies.shellPhase`) and, for the
damping, `CohnElkies.saddleSourceContourDamping` and `CohnElkies.D_u`.
:::

:::definition "eq_48_moments" (lean := "CohnElkies.upperSaddleVariance") (parent := "grp_saddle_geometry")
The quadratic and cubic sizes of the phase are measured by (equation (48))
$`V_\gamma = \dfrac1\lambda\int_0^\infty a^2\mu_{\lambda,\eta}(a)\,da`
$`= \dfrac{\lambda}{4}\psi^{(1)}(m)`,
$`M_3 = \dfrac1\lambda\int_0^\infty a^3\mu_{\lambda,\eta}(a)\,da`
$`+ \int_0^\infty\bigl(|w_s(a)| + w_B(a)\bigr)a^3\cosh(ua)\,da`,
and the shell contributions (equation (49))
$`D_s(T) = \lambda\int_{a_0}^A|w_s(a)|\cosh(ua)(1-\cos(aT))\,da`,
$`D_B(T) = \lambda\int_B^{B+1}w_B(a)\cosh(ua)(1-\cos(aT))\,da`,
$`V_s = \int_{a_0}^A|w_s(a)|a^2\cosh(ua)\,da`, $`V_B = \int_B^{B+1}w_B(a)a^2\cosh(ua)\,da`.
In particular $`D_u = D_\gamma - D_s + D_B` and $`V(u) = V_\gamma - V_s + V_B`
({uses "eq_46_centered_phase"}[], {uses "eq_44_stationary_radius"}[]). Formalized as
`CohnElkies.V_γ`, `CohnElkies.M₃_γ`, `CohnElkies.D_s`, `CohnElkies.D_B`, `CohnElkies.V_s`,
`CohnElkies.V_B`, `CohnElkies.upperSaddleVariance` ($`V(u)`) and `CohnElkies.M₃`, mostly in
terms of $`\delta = u - 1`.
:::

:::lemma_ "lemma_4_4" (lean := "CohnElkies.norm_L_u_add_le") (parent := "grp_saddle_geometry")
There are absolute constants $`c, C > 0` such that, for every $`\lambda > 0`, $`u > -1` with
$`\lambda(1+u) \ge 1`, and $`T \in \mathbb{R}`, the quantities of {uses "eq_46_centered_phase"}[]
and
{uses "eq_48_moments"}[] satisfy (equation (50))
$`\Bigl|\mathcal{L}_u(T) + \dfrac{\lambda V(u)}{2}T^2\Bigr| \le C\lambda M_3|T|^3`.
Moreover, with $`\eta = 1+u` (equations (51)–(53)),
$`\dfrac{1}{2\eta} \le V_\gamma \le \dfrac{C}{\eta}`,
$`\dfrac1\lambda\int_0^\infty a^3\mu_{\lambda,\eta}(a)\,da \le \dfrac{C}{\eta^2}`,
$`D_\gamma(T) \ge c\lambda\min\Bigl(\dfrac{T^2}{\eta}, |T|\Bigr)`.

Formalized with explicit constants: (50) is `CohnElkies.norm_L_u_add_le` with $`C = 1/6`;
(51) and (52) are `CohnElkies.upperGammaVariance_bounds`,
$`1/(2\eta) \le V_\gamma \le 1/(2\eta) + 1/(\lambda\eta^2)`, and
`CohnElkies.upperGammaThirdMoment_bounds`,
$`1/(2\eta^2) \le M_{3,\gamma} \le 1/(2\eta^2) + 2/(\lambda\eta^3)`
(general moments: `CohnElkies.upperGammaMoment_bounds`); (53) is
`CohnElkies.upperGammaDamping_lower_bound` with $`c = 1/(8e)`.
:::

:::proof "lemma_4_4"
The globally valid Taylor estimates $`e^{ix} - 1 - ix = -x^2/2 + O(|x|^3)` and
$`x - \sin x = O(|x|^3)`, applied to (45) and (46) with $`|\sinh(ua)| \le \cosh(ua)`, give (50).
Since $`m = \lambda\eta/2 \ge 1/2`, the bounds (51)–(52) are the uniform trigamma and polygamma
estimates of {uses "lemma_gamma_asymptotics"}[] (ii) inserted into the moment identities of
{uses "eq_45_log_gamma_integral"}[]; the formalization computes the moments of
$`\mu_{\lambda,\eta}` directly from $`x \le e^x - 1 \le xe^x`. For (53), $`1 - e^{-x} \le x` in (37)
gives $`\mu_{\lambda,\eta}(a) \ge \lambda e^{-\eta a}/(2a^2)`. For $`T \ne 0` take
$`L = \min(\eta^{-1}, |T|^{-1})`; on $`0 < a < L` both $`e^{-\eta a}` and $`(1-\cos(aT))/(a^2T^2)`
are
bounded below by absolute positive constants, so $`D_\gamma(T) \ge c\lambda T^2L`, which is (53).
:::

Lemma 4.4 controls the gamma contribution and cubic remainder. For $`u_* \le u \le U` the negative
shell removes at most a $`(1 - c\epsilon)`-fraction of the gamma damping, while $`w_B` contributes
nonnegative damping.

:::lemma_ "lemma_4_5" (lean := "CohnElkies.upperFirstBranchSaddleDamping_lower_bound") (parent := "grp_saddle_geometry")
There is $`\epsilon_0 > 0` and an absolute $`c > 0` such that, for every
$`0 < \epsilon < \epsilon_0`,
there are constants $`C_\epsilon, \lambda_\epsilon > 0` with the following property. For every
$`\lambda \ge \lambda_\epsilon`, every $`u_* \le u \le U`, and $`\eta = 1 + u` (equations
(54)–(57)):
$`\lambda|w_s(a)|\cosh(ua) \le (1 - c\epsilon)\mu_{\lambda,\eta}(a)` for $`a \in [a_0,A]`;
$`D_u(T) \ge c\epsilon D_\gamma(T)` for all $`T`;
$`\dfrac{c\epsilon}{\eta} \le V(u) \le \dfrac{C_\epsilon}{\eta}`;
$`M_3 \le \dfrac{C_\epsilon}{\eta^2}`. Moreover $`\lambda\eta \ge (\log\lambda)/4`.
Uses {uses "eq_43_saddle_parameters"}[], {uses "eq_48_moments"}[].

Formalized with $`c = 2`: (54) is the ratio bound `CohnElkies.upperFirstBranch_shortRatio_le`,
(55) is `CohnElkies.upperFirstBranchSaddleDamping_lower_bound`, $`2\epsilon D_\gamma \le D_u`,
the lower half of (56) follows from `CohnElkies.upperFirstBranch_shortVariance_le_gamma`,
$`V_s \le (1 - 2\epsilon)V_\gamma`, giving
`CohnElkies.eventually_saddleSourceGaussianVariance_firstBranch_pos`;
the upper bounds of (56)–(57) enter the tail estimates of {bpref "lemma_4_8"}[] through
`CohnElkies.eventually_upperSaddleThirdMoment_le_variance`.
:::

:::proof "lemma_4_5"
{uses "lemma_4_2"}[] gives (54). Integrating (54) against $`1 - \cos(aT) \ge 0` shows that the
negative shell removes at most a $`(1-c\epsilon)`-fraction of the gamma damping, and the
contribution of $`w_B` is nonnegative, so
$`D_u(T) \ge D_\gamma(T) - (1-c\epsilon)\int_{a_0}^A(1-\cos(aT))\mu_{\lambda,\eta}(a)\,da`
$`\ge c\epsilon D_\gamma(T)`,
proving (55). For the curvature, integrating (54) against $`a^2/\lambda` gives
$`V_s \le (1 - c\epsilon)V_\gamma`, hence $`V(u) \ge c\epsilon V_\gamma + V_B \ge c\epsilon/\eta` by
(51).
For $`u_* \le u \le U` the positive-shell variance satisfies
$`V_B \le (B+1)^2Qe^{(U-1)(B+1)} = O_\epsilon(1)`, and since $`\lambda\eta \ge (\log\lambda)/4` and
$`\eta \le 2 + \epsilon/2`, (51) gives $`V(u) \le V_\gamma + V_B = O_\epsilon(\eta^{-1})`, proving
(56).
Similarly (54) bounds the negative-shell third moment by the gamma third moment
$`\frac1\lambda\int a^3\mu_{\lambda,\eta}`, the positive-shell third moment is $`O_\epsilon(1)`, and
(52) gives (57) using {uses "lemma_4_4"}[].
:::

When $`u > U`, the factor $`\cosh(ua)` in (47) can make $`w_s` overwhelm the gamma contribution.
Put $`\delta = u - 1`. For $`T \ne 0` the ratios $`D_s(T)/(\lambda\min(T^2,1))` and
$`D_B(T)/(\lambda\min(T^2,1))` have respective sizes at most $`C_0e^{\delta A}` and at least
$`Qe^{\delta B}`, so the separation in Lemma 4.2 makes $`w_B` dominate $`w_s` throughout $`u \ge U`.
The interval support of $`w_B` prevents frequency resonances: a shell concentrated at one $`a`
would have $`D_B(T) = 0` whenever $`aT \in 2\pi\mathbb{Z}`, whereas (equation (58))
$`\int_B^{B+1}(1 - \cos(aT))\,da = 1 - \operatorname{sinc}(T/2)\cos\bigl((B+\tfrac12)T\bigr)`,
$`\operatorname{sinc}(x) = \sin(x)/x`, and $`1 - |\operatorname{sinc}(T/2)| \asymp \min(T^2,1)`, so
(58) is
positive for every $`T \ne 0`, uniformly at small and large frequencies. Define the separation
error $`\rho_\epsilon = (A + a_0^{-1})Q^{-1}\exp\bigl(-\tfrac{\epsilon}{2}(B-A)\bigr)`
$`= C_0Q^{-1}e^{-(U-1)(B-A)}`;
{bpref "lemma_4_2"}[] gives $`\rho_\epsilon = O(e^{-c/\epsilon^2}) = o(1)` as
$`\epsilon \downarrow 0`.

:::lemma_ "lemma_4_6" (lean := "CohnElkies.eventually_upper_shortShell_domination") (parent := "grp_saddle_geometry")
There are absolute constants $`c, C > 0` and $`\epsilon_0 > 0` such that, for every
$`0 < \epsilon < \epsilon_0`, there are constants $`\lambda_\epsilon, C_\epsilon, c_\epsilon > 0`
with the
following property. For every $`\lambda \ge \lambda_\epsilon`, every $`u \ge U`, and every
$`T \in \mathbb{R}`, writing $`\delta = u - 1` (equations (59)–(66)):
$`D_s(T) \le C\lambda C_0e^{\delta A}\min(T^2,1)`, $`D_B(T) \ge c\lambda Qe^{\delta B}\min(T^2,1)`;
consequently $`D_s(T) \le C\rho_\epsilon D_B(T)`, $`D_u(T) \ge D_\gamma(T) + cD_B(T)`, and
$`cV_B \le V(u) \le CV_B`. The shell variance and third moments obey
$`cB^2Qe^{\delta B} \le V_B \le (B+1)^2Qe^{\delta(B+1)}`,
$`\int_{a_0}^A|w_s(a)|a^3\cosh(ua)\,da \le CA\rho_\epsilon V_B`,
$`\int_B^{B+1}w_B(a)a^3\cosh(ua)\,da \le (B+1)V_B`.
In particular $`M_3 \le C_\epsilon V(u)` and $`V(u) \ge c_\epsilon > 0` for $`u \ge U`.
Uses {uses "eq_48_moments"}[] and {uses "eq_35_shells"}[].

Formalized with explicit constants and for every $`\lambda \ge 0`: (61) is
`CohnElkies.eventually_upper_shortShell_domination`, $`D_s \le D_B/100`, obtained from the
parameter separation `CohnElkies.eventually_upper_shell_parameter_margin`; (64) is
`CohnElkies.upperPositiveShellVariance_bounds` with $`c = 1/2`; and the consequence (66) is
`CohnElkies.eventually_upperSaddleThirdMoment_le_variance`, $`M_3 \le C_\epsilon V(u)` with an
explicit $`C_\epsilon`.
:::

:::proof "lemma_4_6"
For $`u = 1 + \delta` the explicit densities satisfy $`|w_s(a)|\cosh(ua) \ll e^{\delta a}/a^2` and
$`w_B(a)\cosh(ua) \asymp Qe^{\delta a}` on their supports. If $`|T| \le 1`,
$`1 - \cos(aT) = O(a^2T^2)`
gives $`D_s(T) \ll \lambda T^2\int_{a_0}^Ae^{\delta a}\,da \ll \lambda Ae^{\delta A}T^2`; if
$`|T| \ge 1`,
$`1 - \cos(aT) = O(1)` gives
$`D_s(T) \ll \lambda e^{\delta A}\int_{a_0}^Aa^{-2}\,da \ll \lambda a_0^{-1}e^{\delta A}`.
These give (59). On the positive shell, (58) yields
$`D_B(T) \gg \lambda Qe^{\delta B}\int_B^{B+1}(1-\cos(aT))\,da`
$`\gg \lambda Qe^{\delta B}\min(T^2,1)`,
which is (60). For $`T \ne 0`, division gives (61) since
$`D_s(T)/D_B(T) \ll C_0Q^{-1}e^{-\delta(B-A)} \le \rho_\epsilon`. At $`T = 0` both damping terms
vanish; comparing their quadratic coefficients gives $`V_s = O(\rho_\epsilon V_B)`. Choose
$`\epsilon_0` so that the implicit constant times $`\rho_\epsilon` is less than $`1/2`; then
$`D_u = D_\gamma - D_s + D_B` proves (62), and $`V(u) = V_\gamma - V_s + V_B` gives
$`V_\gamma + cV_B \le V(u) \le V_\gamma + V_B`. Integrating $`w_B(a)\cosh(ua) \asymp Qe^{\delta a}`
against $`a^2` gives (64). Since $`\delta \ge \epsilon/2`,
$`V_B \gg B^2Qe^{\epsilon B/2} = B^2e^{\epsilon B/8} \gg 1`, while $`V_\gamma \ll \eta^{-1} \ll 1`
by
(51); thus $`V_\gamma = O(V_B)` and (63) follows. Since $`a \le A` on the negative shell,
$`\int_{a_0}^A|w_s|a^3\cosh(ua) \le AV_s \ll A\rho_\epsilon V_B`, while $`a \le B+1` bounds the
positive-shell third moment by $`(B+1)V_B`; this proves (65). Finally, since
$`\eta \ge 2 + \epsilon/2`, (51)–(52) of {uses "lemma_4_4"}[] bound the gamma third moment by
$`O(V_\gamma)`; the shell third moments are $`O_\epsilon(V_B)`, and $`V_\gamma = O(V_B)`,
$`V_B \asymp V(u)` give $`M_3 = O_\epsilon(V(u))`. Also (64) and (63) give
$`V(u) \gg V_B \gg B^2Qe^{\epsilon B/2} =: c_\epsilon > 0`, proving (66).
:::

Set $`T_0 = (2(B+1))^{-1}`. To bound the tails of the saddle integral for $`u \ge U`, we sharpen
the damping on three frequency ranges: $`|T| \le T_0`, where $`D_u` is quadratic;
$`T_0 \le |T| \le \eta`, where $`w_B` supplies a uniform positive floor; and $`|T| \ge \eta`, where
the gamma contribution also grows linearly.

:::lemma_ "lemma_4_7" (lean := "CohnElkies.eventually_secondBranch_damping_pointwise") (parent := "grp_saddle_geometry")
There is $`\epsilon_0 > 0` and an absolute $`c > 0` such that, for every
$`0 < \epsilon < \epsilon_0`,
there are constants $`c_\epsilon, \lambda_\epsilon > 0` with the following property. For every
$`\lambda \ge \lambda_\epsilon` and $`u \ge U`, with $`\eta = 1 + u`, $`\delta = u - 1` and
$`T_0 = (2(B+1))^{-1}` (equations (67)–(69)):
$`D_u(T) \ge c_\epsilon\lambda V(u)T^2` for $`|T| \le T_0`;
$`D_u(T) \ge c_\epsilon\lambda Qe^{\delta B}` for $`T_0 \le |T| \le \eta`;
$`D_u(T) \ge c\lambda|T| + c_\epsilon\lambda Qe^{\delta B}` for $`|T| \ge \eta`.
Uses {uses "eq_46_centered_phase"}[].

Formalized as a single pointwise splitting of $`e^{-D_u(T)}` (weighted by $`1 + |T|^3`) into a
Gaussian part $`e^{-\kappa_\epsilon T^2}` and a part suppressed by the barrier
$`e^{-\lambda Qe^{\delta B}\cdot c_\epsilon}` (`CohnElkies.secondBranchBarrier`) times Gaussian and
exponential tails: `CohnElkies.eventually_secondBranch_damping_pointwise`. The corresponding tail
integrals, before and after the Gaussian rescaling $`T \mapsto T\sqrt{\lambda V(u)}`, are
`CohnElkies.eventually_secondBranch_weighted_tail_le` and
`CohnElkies.eventually_secondBranch_normalized_tail_le`.
:::

:::proof "lemma_4_7"
If $`|T| \le T_0`, then $`|aT| \le 1/2` on $`[B,B+1]`, so $`1 - \cos(aT) \asymp a^2T^2` and
$`D_B(T) \asymp \lambda V_BT^2`. Since $`\eta \ge 2 + \epsilon/2` and $`|T| \le \eta`, (53) and (51)
of
{uses "lemma_4_4"}[] give $`D_\gamma(T) \gg \lambda T^2/\eta \gg \lambda V_\gamma T^2`. Combining
these
through (62) and (63) of {uses "lemma_4_6"}[] proves (67). If $`T_0 \le |T| \le \eta`, then
$`\min(T^2,1) \ge T_0^2`, so (62) and (60) give
$`D_u(T) \gg \lambda T_0^2Qe^{\delta B} \gg_\epsilon \lambda Qe^{\delta B}`, which is (68). If
$`|T| \ge \eta`, then $`\min(T^2,1) = 1` and (53) gives $`D_\gamma(T) \gg \lambda|T|`; adding the
positive shell through (62) and (60) yields (69).
:::

# Global saddle asymptotics

The damping bounds now determine the exterior signs of $`f_+, f_-, f_0`. On each contour, the
centered phase is quadratic near $`T = 0`, the factor $`P_j(T+iu)` is asymptotic to $`P_j(iu)`, and
the remaining contour is negligible.

:::lemma_ "lemma_4_8" (lean := "CohnElkies.eventually_firstBranch_fullGaussianError")
Fix $`0 < \epsilon < \epsilon_0`, let $`\lambda = d/2`, and recall $`u_0, U` from
{uses "eq_34_parameters"}[] and $`u_*` from {uses "eq_43_saddle_parameters"}[]. For $`u > -1` and
$`P \in \{P_+, P_-, P_0\}` put
$`I_{\lambda,P}(u) = \int_{\mathbb{R}}e^{\mathcal{L}_u(T)}P(T + iu)\,dT`
with $`\mathcal{L}_u` from {uses "eq_46_centered_phase"}[]. As $`d \to \infty` (equation (70)),
$`I_{\lambda,P}(u) = P(iu)\sqrt{\dfrac{2\pi}{\lambda V(u)}}\,(1 + o_\epsilon(1))`,
uniformly for $`u \ge u_*` when $`P = P_+`, and uniformly for $`u \ge u_0` when $`P = P_-` or
$`P = P_0`. More precisely,
$`\sup_{u\ge u_*}\Bigl|\dfrac{\sqrt{\lambda V(u)}\,I_{\lambda,P_+}(u)}{\sqrt{2\pi}\,P_+(iu)}`
$`- 1\Bigr| \to 0`,
$`\sup_{u\ge u_0}\Bigl|\dfrac{\sqrt{\lambda V(u)}\,I_{\lambda,P_j}(u)}{\sqrt{2\pi}\,P_j(iu)}`
$`- 1\Bigr| \to 0`
for $`j \in \{-,0\}`.

The formalization proves the strict inequality
$`\bigl|I_{\lambda,P}(u) - P(iu)\sqrt{2\pi/(\lambda V(u))}\bigr|`
$`< |P(iu)|\sqrt{2\pi/(\lambda V(u))}`,
uniformly on the stated ranges for all small $`\epsilon` and large $`\lambda`, which is what the
signs in {bpref "cor_4_9"}[] require, rather than the relative asymptotic (70). It is stated for
an arbitrary saddle polynomial $`P` (`CohnElkies.IsSaddlePolynomial`) together with a lower
bound $`u_0(P)` on the range where $`P(iu)` stays away from $`0` (`CohnElkies.SaddleRangeBounds`),
which covers $`P_+` on $`u \ge u_*`, $`P_-` on $`u \ge u_0` and, once it is added, $`P_0`:
`CohnElkies.eventually_firstBranch_fullGaussianError` on $`u_* \le u \le U` and
`CohnElkies.eventually_secondBranch_fullGaussianError` on $`u \ge U`, with the uniform tail
bound `CohnElkies.eventually_saddleSource_secondBranch_uniform_tail`.
:::

:::proof "lemma_4_8"
Contour shift. The poles of the integrand in (38) are $`t = -i(\lambda + 2n)`, $`n \ge 0`, so
{uses "lemma_4_3"}[] allows the contour to be shifted to $`t = \lambda(T + iu)` whenever $`u > -1`.
At $`r = e^{v(u)}` the shifted Mellin inversion formula reads (equation (71))
$`f_j(e^{v(u)})`
$`= \dfrac{\lambda E_\lambda(i\lambda u)}{2\pi}\,e^{-(1+u)\lambda v(u)}\,I_{\lambda,P_j}(u)`,
with a positive prefactor. By {uses "eq_39_polynomial_values"}[], $`P_+(iu) > 0` for $`u > -1`,
while $`P_-(iu) < 0` and $`P_0(iu) > 0` for $`u \ge u_0`; their fixed degrees and uniform lower
bounds on those ranges give (equation (72))
$`\dfrac{|P(T+iu)|}{|P(iu)|} \ll_\epsilon 1 + |T|^3`,
$`\dfrac{P(T+iu)}{P(iu)} = 1 + O_\epsilon(|T| + |T|^3)`.

Central interval. Choose $`K \to \infty` (depending on $`d` and $`u`) and set
$`T_* = K/\sqrt{\lambda V(u)}`. By (50) of {uses "lemma_4_4"}[], the phase on $`|T| \le T_*` is
$`\mathcal{L}_u(T) = -\tfrac{\lambda V(u)}{2}T^2 + O(\lambda M_3|T|^3)`. The approximation is
uniform
if the central interval shrinks and the cubic error tends to zero:
$`T_* = o_\epsilon(1)`, $`K^3M_3/(\sqrt\lambda\,V(u)^{3/2}) = o_\epsilon(1)`. Under these
conditions,
(72) and the substitution $`x = \sqrt{\lambda V(u)}\,T` give
$`\int_{|T|\le T_*}e^{\mathcal{L}_u(T)}P(T+iu)\,dT`
$`= P(iu)\sqrt{2\pi/(\lambda V(u))}\,(1 + o_\epsilon(1))`,
using $`\int_{-K}^Ke^{-x^2/2}\,dx \to \sqrt{2\pi}`. It remains to show that the integral over
$`|T| > T_*` is $`o_\epsilon(|P(iu)|/\sqrt{\lambda V(u)})`; we verify the conditions and the tail
bound separately on $`[u_*, U]` and $`[U,\infty)`.

Gamma-controlled range $`u_* \le u \le U`. Put $`\eta = 1+u` and $`L = \lambda\eta`. By (56)–(57) of
{uses "lemma_4_5"}[], $`L \ge \tfrac14\log\lambda`, $`V(u) \asymp_\epsilon \eta^{-1}`,
$`M_3 \ll_\epsilon \eta^{-2}`. Choosing $`K = L^{1/12}`, so that $`K \to \infty` and
$`K^3 = o(\sqrt L)`,
gives $`T_*/\eta \ll_\epsilon L^{-5/12}` and
$`K^3M_3/(\sqrt\lambda V(u)^{3/2}) \ll_\epsilon L^{-1/4}`. The
damping bounds (55) and (53) are quadratic for $`|T| \le \eta` and linear for $`|T| \ge \eta`.
Consequently
$`\sup_{|T|\le T_*}|\mathcal{L}_u(T) + \tfrac{\lambda V(u)}{2}T^2| \ll_\epsilon L^{-1/4}`,
$`\sqrt{\lambda V(u)}\int_{T_*\le|T|\le\eta}(1+|T|^3)e^{-D_u(T)}\,dT`
$`\ll_\epsilon e^{-c_\epsilon K^2}`,
$`\sqrt{\lambda V(u)}\int_{|T|\ge\eta}(1+|T|^3)e^{-D_u(T)}\,dT \ll_\epsilon e^{-c_\epsilon L}`
(the Gaussian tail via $`\int_K^\infty e^{-cx^2}\,dx \le e^{-cK^2}/(2cK)`, the exponential tail via
$`\int_\eta^\infty(1+T^3)e^{-c\epsilon\lambda T}\,dT \ll (1+\eta^3)e^{-c\epsilon L}/\lambda`). Both
tail
estimates tend to zero uniformly because $`L \ge (\log\lambda)/4`, proving (70) on $`[u_*, U]`.

Shell-controlled range $`u \ge U`. Write $`\delta = u - 1`. By (63) and (66) of
{uses "lemma_4_6"}[],
the remote shell controls both curvature and third moment:
$`V(u) \asymp_\epsilon V_B \gg_\epsilon 1`
and $`M_3 \ll_\epsilon V(u)`. Take $`K = \lambda^{1/12}`; then $`T_* \ll_\epsilon \lambda^{-5/12}`
and
$`K^3M_3/(\sqrt\lambda V(u)^{3/2}) \ll_\epsilon \lambda^{-1/4}`; in particular $`T_* < T_0` for
large
$`\lambda`. The quadratic bound (67) of {uses "lemma_4_7"}[] on $`|T| \le T_0` yields (equation
(73))
$`\sup_{|T|\le T_*}|\mathcal{L}_u(T) + \tfrac{\lambda V(u)}{2}T^2| \ll_\epsilon \lambda^{-1/4}` and
$`\sqrt{\lambda V(u)}\int_{T_*\le|T|\le T_0}(1+|T|^3)e^{-D_u(T)}\,dT`
$`\ll_\epsilon e^{-c_\epsilon K^2}`.
For $`T_0 \le |T| \le \eta`, the variance bound (64) and the damping estimate (68) give
(equation (74))
$`\sqrt{\lambda V(u)}\int_{T_0\le|T|\le\eta}(1+|T|^3)e^{-D_u(T)}\,dT`
$`\ll_\epsilon \sqrt\lambda\,e^{\Phi(\delta)}`,
$`\Phi(\delta) = \dfrac{B+1}{2}\delta + 4\log(2+\delta) - c_\epsilon\lambda Qe^{B\delta}`, which is
$`o_\epsilon(1)`. The exponent $`\Phi` decreases in $`\delta \ge \epsilon/2`, since its derivative
$`(B+1)/2 + 4/(2+\delta) - c_\epsilon\lambda BQe^{B\delta}` is negative for large $`\lambda`; at
$`\delta = \epsilon/2` it equals $`-c_\epsilon'\lambda + O_\epsilon(1)`. Thus the middle-frequency
contribution tends to zero uniformly even as $`u \to \infty`. Finally, for $`|T| \ge \eta`, (69)
supplies the positive-shell damping and a linear gamma tail, so (equation (75))
$`\sqrt{\lambda V(u)}\int_{|T|\ge\eta}(1+|T|^3)e^{-D_u(T)}\,dT \ll_\epsilon e^{-c_\epsilon\lambda}`
uniformly in $`\delta`: as in (74), the damping $`-c_\epsilon\lambda Qe^{B\delta}` absorbs the
growth
of $`\sqrt{V(u)}`. Equations (73)–(75) prove the saddle formula on every $`u \ge U`.
:::

:::theorem "cor_4_9" (lean := "CohnElkies.eventually_fPlus_nonneg_of_star")
For every fixed $`0 < \epsilon < \epsilon_0` there is $`d_\epsilon` such that, for every integer
$`d \ge d_\epsilon`, with $`v` from {uses "eq_44_stationary_radius"}[] (equation (76)):
$`f_+(r) > 0` for $`r \ge e^{v(u_*)}`, $`f_-(r) < 0` for $`r \ge e^{v(u_0)}`, and $`f_0(r) > 0` for
$`r \ge e^{v(u_0)}`.

Formalized for the pair, for all small $`\epsilon` and large $`d`: the strict signs at the
saddle radii $`r = e^{v(u)}` are `CohnElkies.eventually_fPlus_re_pos_firstBranch`,
`CohnElkies.eventually_fPlus_re_pos_secondBranch` and, generically in the polynomial factor
with the sign of $`P(iu)`, `CohnElkies.eventually_mellinProfile_re_mul_pos_firstBranch` and
`CohnElkies.eventually_mellinProfile_re_mul_pos_secondBranch`; the radius coverage, by continuity of
$`v` and $`v(u) \to \infty` with the intermediate value theorem
(`CohnElkies.eventually_saddleLogRadius_covers_Ici`), gives the weak signs
$`f_+(r) \ge 0` for $`r \ge r_* = e^{v(u_*)}` (`CohnElkies.eventually_fPlus_nonneg_of_star`)
and $`f_-(r) \le 0` for $`r \ge R_{\epsilon,d} = e^{v(u_0)}` (
`CohnElkies.eventually_fMinus_nonpos_of_radius`),
which are the inequalities that the admissibility in {bpref "lemma_upper_bound_reduction"}[]
needs; the strict versions for $`r \ge R_{\epsilon,d}` are
`CohnElkies.eventually_fMinus_re_neg_of_radius` and, for $`f_0`,
`CohnElkies.eventually_fZero_re_pos_of_radius`
(from `CohnElkies.eventually_mellinProfile_re_mul_pos_of_radius` with $`P_0(iu) = u^2 - 1 > 0`).
:::

:::proof "cor_4_9"
For $`u > -1` the prefactor of $`I_{\lambda,P_j}(u)` in (71) is positive, so (70) of
{uses "lemma_4_8"}[] identifies the sign of $`f_j(e^{v(u)})` with that of $`P_j(iu)` for all
sufficiently large $`d`, uniformly on the stated ranges of $`u`. Equations (56) and (63) of
{uses "lemma_4_5"}[] and {uses "lemma_4_6"}[] give $`v'(u) = V(u) > 0` on $`[u_*,\infty)`, and
(44) with the positive shell $`w_B` gives $`v(u) \to \infty` as $`u \to \infty`. Thus
$`[u_*,\infty)`
parametrizes every radius $`r \ge e^{v(u_*)}` and $`[u_0,\infty)` every radius $`r \ge e^{v(u_0)}`;
the formalization only uses continuity of $`v` and its divergence, not the strict monotonicity.
The signs in {uses "eq_39_polynomial_values"}[] now give (76).
:::

# Positivity and the sharp upper bound

Corollary 4.9 proves the required signs outside the saddle radii. To finish the construction we
must also show $`f_+(r) > 0` for $`0 \le r \le r_* = e^{v(u_*)}`. Shifting the Mellin contour below
$`O(\log\lambda)` gamma poles expresses $`f_+(r)/f_+(0)` as a truncated exponential series plus a
uniformly negligible remainder.

:::lemma_ "lemma_4_10" (lean := "CohnElkies.eventually_plusSaddleProfile_re_pos_on_star")
Fix $`0 < \epsilon < \epsilon_0`, let $`\lambda = d/2`, set $`r_* = e^{v(u_*)}`
({uses "eq_44_stationary_radius"}[], {uses "eq_43_saddle_parameters"}[]), and write
$`h_1' = \int_0^\infty w(a)\,a\sinh a\,da` ({uses "eq_35_shells"}[]). As $`d \to \infty`,
$`\sup_{0\le r\le r_*}\Bigl|e^{\pi e^{2h_1'}r^2}\,\dfrac{f_+(r)}{f_+(0)} - 1\Bigr|`
$`\longrightarrow 0`.
In particular $`f_+(r) > 0` on $`[0, r_*]` for all sufficiently large $`d`.

The formalization proves the positivity consequence, for all small $`\epsilon` and large $`d`,
as `CohnElkies.eventually_plusSaddleProfile_re_pos_on_star`, with the radius `CohnElkies.r_star`.
It truncates the residue series at $`N = \lceil\log\lambda\rceil` (`CohnElkies.N_ℓ`) as in the
report and shows, uniformly on $`0 \le r \le r_*` with $`y = \pi e^{2h_1'}r^2`
(`CohnElkies.y_r`), the two bounds $`e^y|S_N(y) - e^{-y}| < \tfrac12` for the truncated series
$`S_N` with coefficients `CohnElkies.A_ℓn`
(`CohnElkies.eventually_plusSaddleSmallRadius_relativeFiniteResidue_lt_half`) and
$`e^y|\mathcal{R}_{\lambda}(r)| < \tfrac12` for the remainder
(`CohnElkies.eventually_saddleNegative_relativeGammaTail_lt_half`), whose sum gives
$`f_+(r)/f_+(0) > 0` (`CohnElkies.plusSaddleProfile_re_pos_of_relative_residue_bounds`); the
expansion itself is `CohnElkies.plusSaddleProfile_div_origin_eq_small_radius_residue_series`.
:::

:::proof "lemma_4_10"
Range of $`y`. Put $`y = \pi e^{2h_1'}r^2`, $`H(u) = \int_0^\infty w(a)a\sinh(ua)\,da` (so
$`H(1) = h_1'`), and $`\eta_* = 1 + u_* = (\log\lambda)/(4\lambda)`. The height $`u_*` tends to
$`-1`, the normalized height of the first gamma pole, while the gamma shape parameter
$`\lambda\eta_*/2 = (\log\lambda)/8` still diverges; this makes (70) applicable and keeps $`y(r_*)`
logarithmic. Indeed $`H` is odd with bounded derivative near $`-1` (for fixed $`\epsilon`), so
$`H(u_*) + h_1' = H(-1+\eta_*) - H(-1) = O_\epsilon(\eta_*)`, and by (44)
$`y(r_*) = \exp\bigl(\psi(\lambda\eta_*/2) + 2H(u_*) + 2h_1'\bigr)`. The digamma asymptotic
({uses "lemma_gamma_asymptotics"}[]) gives (equation (77))
$`0 \le y \le y(r_*) = \tfrac18\log\lambda + O_\epsilon(1)`. Since $`e^{-y}` can be as small as a
negative power of $`\lambda`, the errors must be controlled relative to $`e^{-y}`.

Contour shift. Set $`N = \lceil\log\lambda\rceil`, $`p = N + \tfrac12`,
$`\kappa = 1 + 2p/\lambda`. The contour
$`t = s - i(\lambda + 2p)` lies strictly between consecutive gamma poles, and
$`p \asymp \log\lambda`
makes the exponential-series tail negligible on (77). The multiplier
$`e^{\lambda h_\epsilon(t/\lambda)}` preserves a uniform decay margin: $`pA/\lambda = o_\epsilon(1)`
, so
the taper satisfies $`b(a)e^{2pa/\lambda} \le 1 - c\epsilon` on $`[a_0, A]` for large $`\lambda`;
for
every intermediate height $`0 \le q \le \kappa`, the positive shell contributes nonpositively to
$`\operatorname{Re}h_\epsilon(s/\lambda - iq) - h_\epsilon(iq)`, and the negative shell gives
$`\lambda\bigl(\operatorname{Re}h_\epsilon(s/\lambda - iq) - h_\epsilon(iq)\bigr)`
$`\le \dfrac{(1-c\epsilon)\lambda}{2}\int_0^\infty\dfrac{1-\cos(as/\lambda)}{a^2}\,da`,
which equals $`(1-c\epsilon)\pi|s|/4`. The gamma factor supplies the complementary
$`e^{-\pi|s|/4}` ({uses "lemma_gamma_asymptotics"}[]), so the integrand decays like
$`e^{-c\epsilon|s|}` on the vertical sides, permitting the shift of (38) to
$`t = s - i(\lambda+2p)`, which crosses exactly the poles $`t = -i(\lambda+2n)`, $`0 \le n \le N`.

Residue expansion. The residue formula (41) and the origin value (42) of {uses "lemma_4_3"}[]
give (equations (78)–(79))
$`\dfrac{f_+(r)}{f_+(0)} = \sum_{n=0}^N\dfrac{(-y)^n}{n!}A_{\lambda,n}`
$`+ \mathcal{R}_{\lambda,p}(r)`,
$`A_{\lambda,n}`
$`= e^{\lambda[h_\epsilon(\zeta_n) - h_\epsilon(i)] - 2nh_1'}\,\dfrac{P_+(\zeta_n)}{\beta}`, with
$`\zeta_n = -i(1+2n/\lambda)` as in (41) and $`h_\epsilon` even,,
$`|A_{\lambda,n} - 1| \ll_\epsilon \dfrac{n(1+n)}{\lambda}` for $`0 \le n \le N`:
Taylor expansion at $`u = 1` gives
$`\lambda[h_\epsilon(i(1+2n/\lambda)) - h_\epsilon(i)] = 2nh_1' + O_\epsilon(n^2/\lambda)` and
$`P_+(-i(1+2n/\lambda))/\beta = 1 - \tfrac{2n}{\lambda}(2 + \tfrac{2n}{\lambda})^2/\beta = 1`
$`+ O_\epsilon(n/\lambda)`,
uniformly for $`n \le N`, where $`N^2/\lambda = o(1)`. For $`r > 0` the remainder is the integral
over the shifted contour,
$`\mathcal{R}_{\lambda,p}(r)`
$`= \dfrac{\pi^{\lambda/2+p}r^{2p}}{2\pi f_+(0)}\int_{\mathbb{R}}\Xi(s)\,r^{is}\,ds`,
$`\Xi(s)`
$`= \pi^{is/2}\Gamma(-p - is/2)e^{\lambda h_\epsilon(s/\lambda - i\kappa)}P_+(s/\lambda - i\kappa)`.
The gamma reflection and product estimates ({uses "eq_7_gamma_identities"}[],
{uses "lemma_gamma_asymptotics"}[]) with $`p \in \mathbb{Z} + \tfrac12` give
$`|\Gamma(-p - is/2)| \ll e^{-\pi|s|/4}/\Gamma(1+p)`, the shell bound above gives
$`\lambda(\operatorname{Re}h_\epsilon(s/\lambda - i\kappa) - h_\epsilon(i\kappa))`
$`\le (1-c\epsilon)\pi|s|/4`,
and $`P_+(s/\lambda - i\kappa)/\beta = O_\epsilon(1 + |s|^3)`. Integrating in $`s`, and using
$`\lambda[h_\epsilon(i\kappa) - h_\epsilon(i)] = 2ph_1' + O_\epsilon(p^2/\lambda)` with
$`(\pi r^2)^pe^{2ph_1'} = y^p` and $`p^2/\lambda = o(1)`, gives (equation (80))
$`|\mathcal{R}_{\lambda,p}(r)| \ll_\epsilon y^p/\Gamma(1+p)`, which extends to $`r = 0` by
continuity.

Comparison with $`e^{-y}`. Equations (79), (80), (77) and
$`\sum_{n\ge0}n(1+n)y^n/n! = (y^2+2y)e^y` give (equation (81))
$`e^y\sum_{n=0}^N\dfrac{y^n}{n!}|A_{\lambda,n} - 1| \ll_\epsilon \dfrac{(1+y)^2e^{2y}}{\lambda}`
$`\ll_\epsilon \dfrac{(\log\lambda)^2}{\lambda^{3/4}}`,
$`e^y|\mathcal{R}_{\lambda,p}(r)| \ll_\epsilon \dfrac{e^yy^p}{\Gamma(1+p)}`,
$`e^y\sum_{n>N}\dfrac{y^n}{n!} \le \dfrac{e^yy^{N+1}}{(N+1)!}`.
For the two tails put $`L = \log\lambda`. Since $`y \le L/8 + O_\epsilon(1)` and $`p = L + O(1)`,
Stirling's formula gives
$`\log\bigl(e^yy^p/\Gamma(1+p)\bigr) \le (\tfrac18 + 1 - \log 8)L + O_\epsilon(\log L)`,
and the same holds with $`p` replaced by $`N+1`. Since $`\tfrac18 + 1 - \log 8 < 0`, both tails are
smaller than the coefficient error in (81). Therefore (78) yields, uniformly on $`0 \le r \le r_*`
(equation (82)),
$`\dfrac{f_+(r)}{f_+(0)}`
$`= e^{-y}\Bigl(1 + O_\epsilon\Bigl(\dfrac{(\log\lambda)^2}{\lambda^{3/4}}\Bigr)\Bigr) > 0`.
:::

:::proof "thm_4_1"
Set $`R_{\epsilon,d} = e^{v(u_0)}` with $`v` from {uses "eq_44_stationary_radius"}[]. The Fourier
identities and origin values follow from (40) and (42) of {uses "lemma_4_3"}[].
{uses "cor_4_9"}[] gives the required exterior signs, and (82) of {uses "lemma_4_10"}[] supplies
positivity of $`f_+` on the remaining interval $`[0, r_*]`. Thus (equation (83))
$`\widehat{f_-} = f_+ > 0`, $`f_-(0) = f_+(0) > 0`, $`\widehat{f_0} = f_0`, $`f_0(0) = 0`,
$`f_-(r) < 0 < f_0(r)` for $`r \ge R_{\epsilon,d}`.
For fixed $`\epsilon`, the saddle equation (44) and the digamma asymptotic
$`\psi(\lambda(1+u_0)/2) = \log(d(1+u_0)/4) + o(1)` ({uses "lemma_gamma_asymptotics"}[]) give
(equation (84))
$`\lim_{d\to\infty}\dfrac{R_{\epsilon,d}}{\sqrt d}`
$`= \sqrt{\frac{1+u_0}{4\pi}}\exp\bigl(\int_0^\infty w(a)a\sinh(u_0a)\,da\bigr) =: \alpha_\epsilon`.
The two shell contributions in {uses "lemma_4_2"}[] give
$`\int_0^\infty w(a)a\sinh(u_0a)\,da = -\tfrac12\log\tfrac\pi2 + O(\epsilon)`. Since $`u_0 \to 1`,
(33)
of {uses "eq_32_ideal_density"}[] and (84) give (equation (85))
$`\lim_{\epsilon\downarrow0}\lim_{d\to\infty}R_{\epsilon,d}/\sqrt d`
$`= \lim_{\epsilon\downarrow0}\alpha_\epsilon = 1/\pi`.
:::

:::theorem "thm_1_1_upper" (lean := "CohnElkies.saddleOrderedUpperConstruction")
$`\limsup_{d\to\infty}\mathrm{LP}_d^{1/d} \le \sqrt{e/(2\pi)}`, with $`\mathrm{LP}_d` from
{uses "def_lp"}[].

The formalization does not state this limit superior separately. It packages the primal
construction as an *ordered $`\epsilon`-construction*
(`CohnElkies.OrderedEpsilonUpperConstruction`, realized by
`CohnElkies.saddleOrderedUpperConstruction`):
a bound $`\epsilon_0 > 0`, normalized radii $`R_{\epsilon,d}/\sqrt d` converging as $`d \to \infty`
to limits $`\alpha_\epsilon` that tend to $`1/\pi` as $`\epsilon \downarrow 0`, and, for every
$`0 < \epsilon < \epsilon_0` and all large $`d`, an admissible function of normalized cost at most
$`R_{\epsilon,d}/\sqrt d`. The limit superior is then extracted together with the lower bound in
the sandwich argument {bpref "thm_1_1_sandwich"}[].
:::

:::proof "thm_1_1_upper"
Fix $`0 < \epsilon < \epsilon_0` and let $`d` be large. By (83) of {uses "thm_4_1"}[] and
{uses "lemma_upper_bound_reduction"}[], the dilation $`F_{\epsilon,d}(x) = f_-(R_{\epsilon,d}x)` is
admissible with $`F_{\epsilon,d}(0)/\widehat{F_{\epsilon,d}}(0) = R_{\epsilon,d}^d`, so (equation
(86))
$`\mathrm{LP}_d \le \dfrac{v_d}{2^d}R_{\epsilon,d}^d`, i.e.
$`\mathrm{LP}_d^{1/d} \le \dfrac{v_d^{1/d}\sqrt d}{2}\cdot\dfrac{R_{\epsilon,d}}{\sqrt d}`. By
{uses "lemma_stirling_ball_volume"}[] and (84), the right side tends to
$`\tfrac12\sqrt{2\pi e}\,\alpha_\epsilon` as $`d \to \infty`. Hence
$`\limsup_d\mathrm{LP}_d^{1/d} \le \tfrac12\sqrt{2\pi e}\,\alpha_\epsilon` for every $`\epsilon`,
and
letting $`\epsilon \downarrow 0` with (85) gives $`\tfrac12\sqrt{2\pi e}/\pi = \sqrt{e/(2\pi)}`.
:::

:::theorem "thm_1_2_upper" (lean := "CohnElkies.limsup_signUncertaintyConstant_div_sqrt_le")
For each $`\varsigma \in \{-1,+1\}`, $`\mathsf{A}_\varsigma(d)`
({uses "def_sign_uncertainty_constant"}[]) is finite for all sufficiently large $`d`, and
$`\limsup_{d\to\infty}\mathsf{A}_\varsigma(d)/\sqrt d \le 1/\pi`. Formalized in
`CohnElkies.SignUncertainty.UpperBound` from the functions of {bpref "thm_4_1"}[]:
`CohnElkies.eventually_signUncertaintyConstant_le` ($`\mathsf{A}_\varsigma(d) \le R_{\epsilon,d}`
for all small $`\epsilon` and large $`d`, through
`CohnElkies.RadialEigenfunction.signUncertaintyConstant_le_of_nonneg_outside`),
`CohnElkies.eventually_limsup_signUncertaintyConstant_div_sqrt_le` (the bound $`\alpha_\epsilon`)
and `CohnElkies.limsup_signUncertaintyConstant_div_sqrt_le`.
:::

:::proof "thm_1_2_upper"
Fix $`0 < \epsilon < \epsilon_0` and let $`d` be large. Define $`g_{\epsilon,d,-} = f_+ - f_-` and
$`g_{\epsilon,d,+} = f_0` with $`f_\pm, f_0` from {uses "thm_4_1"}[]. Equation (40) and Fourier
inversion give $`\widehat{g_{\epsilon,d,-}} = -g_{\epsilon,d,-}` and
$`\widehat{g_{\epsilon,d,+}} = g_{\epsilon,d,+}`. By (83) both vanish at the origin and are
strictly positive outside $`B(0,R_{\epsilon,d})`; in particular neither is zero. By
{uses "lemma_upper_bound_reduction"}[], $`\mathsf{A}_\varsigma(d) \le R_{\epsilon,d} < \infty` for
both signs. Hence
$`\limsup_d\mathsf{A}_\varsigma(d)/\sqrt d \le \lim_d R_{\epsilon,d}/\sqrt d = \alpha_\epsilon`
by (84), and letting $`\epsilon \downarrow 0` with (85) gives $`1/\pi`.
:::
