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

:::lemma_ "lemma_upper_bound_reduction" (lean := "CohnElkies.saddleSourceAdmissible, CohnElkies.saddleSourceAdmissible_normalizedCost")
Let $`R > 0` and let $`f_-, f_+` be real radial Schwartz functions on $`\mathbb{R}^d` with
$`\widehat{f_-} = f_+ \ge 0` everywhere, $`f_-(0) = f_+(0) > 0`, and $`f_-(x) \le 0` for $`|x| \ge R`.
Then $`F(x) = f_-(Rx)` belongs to $`\mathcal{A}_d^{\mathrm{rad}}` ({uses "def_admissible_class"}[],
{uses "def_radial_admissible_class"}[]) with $`F(0)/\widehat F(0) = R^d`, so
$`\mathrm{LP}_d \le v_d(R/2)^d` ({uses "def_lp"}[]).
:::

:::proof "lemma_upper_bound_reduction"
Fourier scaling ({uses "def_fourier_convention"}[]) gives $`\widehat F(\xi) = R^{-d}f_+(\xi/R) \ge 0`,
$`F(x) = f_-(Rx) \le 0` for $`|x| \ge 1`, and $`F(0)/\widehat F(0) = R^df_-(0)/f_+(0) = R^d`.
:::

:::lemma_ "lemma_sign_uncertainty_reduction" (lean := "CohnElkies.RadialEigenfunction.signUncertaintyConstant_le_of_nonneg_outside, CohnElkies.minusSaddleEigenfunction, CohnElkies.zeroSaddleEigenfunction")
If $`g` is a real radial Schwartz function with $`\widehat g = \varsigma g`, $`g(0) = 0`, $`g \ne 0`
and $`g(x) \ge 0` for $`|x| \ge R`, then $`g \in \mathcal{E}_\varsigma(d)` with $`r(g) \le R`, so
$`\mathsf{A}_\varsigma(d) \le R` (see {uses "def_sign_eigenfunction_class"}[],
{uses "def_sign_radius"}[], {uses "def_sign_uncertainty_constant"}[]). This applies to
$`g_- = f_+ - f_-` for a pair $`f_\pm` as in {uses "lemma_upper_bound_reduction"}[] with
$`f_+ > 0` on $`\{|x| \ge R\}`, and to a self-Fourier $`f_0` with $`f_0(0) = 0` and $`f_0 > 0` on
$`\{|x| \ge R\}`.
:::

:::proof "lemma_sign_uncertainty_reduction"
Schwartz functions are continuous and integrable, so $`g` lies in $`\mathcal{E}_\varsigma(d)`
and the infimum gives the bound. For $`g_- = f_+ - f_-`: since $`f_-` is even,
$`\widehat{f_+} = \widehat{\widehat{f_-}} = f_-`, so $`\widehat{g_-} = f_- - f_+ = -g_-`;
$`g_-(0) = 0`; $`g_-(x) = f_+(x) - f_-(x) > 0` for $`|x| \ge R`, so $`g_- \ne 0` and
$`r(g_-) \le R`.
:::

Thus all the upper bounds reduce to producing one Fourier pair, one self-Fourier function, and a
radius $`R = (1/\pi + o(1))\sqrt d`.

:::theorem "thm_4_1" (lean := "CohnElkies.saddleSourceEventualSigns, CohnElkies.eventually_exists_radialEigenfunction_fZero")
There is $`\epsilon_0 > 0` such that, for every fixed $`0 < \epsilon < \epsilon_0` and every
sufficiently large dimension $`d`, there exist real radial Schwartz functions $`f_-, f_+, f_0` on
$`\mathbb{R}^d` and a radius $`R_{\epsilon,d} > 0` such that $`f_+ \ge 0` everywhere,
$`f_-(x) \le 0 < f_0(x)` whenever $`|x| \ge R_{\epsilon,d}`, and
$`\widehat{f_-} = f_+`, $`\widehat{f_0} = f_0`, $`f_-(0) = f_+(0) > 0`, $`f_0(0) = 0`.
Moreover $`R_{\epsilon,d}/\sqrt d \to \alpha_\epsilon` as $`d \to \infty` for each fixed
$`\epsilon`, and $`\alpha_\epsilon \to 1/\pi` as $`\epsilon \downarrow 0`
({uses "eq_84_saddle_radius_limit"}[], {uses "eq_85_critical_radius"}[]).
:::

# Outline of the construction

The functions $`f_-, f_+, f_0` are constructed through their Mellin transforms on the critical
line, which are then inverted ({bpref "eq_8_mellin_inversion"}[]); by (10) the Fourier symmetries
become reflections of the frequency. The ansatz perturbs the Mellin transform of a Gaussian.

:::lemma_ "lemma_gaussian_mellin" (lean := "CohnElkies.mellinMultiplier_mul_E_neg, CohnElkies.saddleEnvelope_conj, CohnElkies.mellinMultiplier_mul_spectrum_neg")
The Gaussian $`g_G(r) = 2\pi^{\lambda/2}e^{-\pi r^2}` has critical-line Mellin transform
({uses "def_radial_mellin"}[])
$`E^G_\lambda(t) = X_{g_G}(t) = \pi^{it/2}\Gamma\bigl(\tfrac{\lambda - it}{2}\bigr)`
(in the formalization this formula is the definition of the envelope, `CohnElkies.E`).
For every even entire $`h` real on the imaginary axis, the perturbed envelope
$`E_\lambda(t) = E^G_\lambda(t)e^{\lambda h(t/\lambda)}` obeys, with $`m_\lambda` from
{uses "eq_10_critical_line"}[], $`m_\lambda(t)E_\lambda(-t) = E_\lambda(t)` and
$`\overline{E_\lambda(t)} = E_\lambda(-t)` for real $`t`; consequently, for polynomials with
$`P(-\zeta) = Q(\zeta)`, the Mellin data $`X_P(t) = E_\lambda(t)P(t/\lambda)` and
$`X_Q(t) = E_\lambda(t)Q(t/\lambda)` satisfy $`m_\lambda(t)X_P(-t) = X_Q(t)`, i.e. multiplication
of $`E^G_\lambda` by an even factor preserves the Fourier symmetry of {uses "eq_10_critical_line"}[].
:::

:::proof "lemma_gaussian_mellin"
$`\int_0^\infty e^{-\pi r^2}r^{z-1}\,dr = \tfrac12\pi^{-z/2}\Gamma(z/2)` at $`z = \lambda - it`
gives
the formula, and the identity $`m_\lambda(t)E^G_\lambda(-t) = E^G_\lambda(t)` is immediate from the
definition of $`m_\lambda`.
:::

*The polynomials.* For $`j \in \{-, +, 0\}` we choose a polynomial $`P_j` and set
$`X_{f_j}(t) = E_\lambda(t)P_j(t/\lambda)`, $`f_j` its inverse Mellin transform. Without the
perturbation ($`h = 0`), $`f_j` is a Gaussian times a polynomial in $`r^2`, since multiplying
$`X_f(t)` by $`t` corresponds to the operator $`-i(r\,d/dr + \lambda)`. The requirements are:
$`P_+(-\zeta) = P_-(\zeta)` and $`P_0(-\zeta) = P_0(\zeta)`, which by
{bpref "lemma_gaussian_mellin"}[] give $`\widehat{f_-} = f_+` and $`\widehat{f_0} = f_0`;
$`\overline{P_j(\zeta)} = P_j(-\bar\zeta)`, which makes $`f_j` real; $`P_+(-i) = P_-(-i) > 0` and
$`P_0(-i) = 0`, since the first gamma pole $`t = -i\lambda` (normalized frequency $`\zeta = -i`)
determines $`f_j(0)` ({bpref "lemma_4_3"}[]); and, since the sign of $`P_j(iu)` will control the
sign of $`f_j` on the saddle contour of height $`u` ({bpref "lemma_4_8"}[]), $`P_+(iu) > 0` for
$`u > -1` while $`P_-(iu) < 0 < P_0(iu)` for $`u` slightly above $`1`. The simplest choice is
{bpref "eq_38_envelope_polynomials"}[], with a parameter $`\beta = \epsilon/4`. Unperturbed,
$`f_0` already gives the Bourgain–Clozel–Kahane bound $`\mathsf{A}_+(d) \le \sqrt{(d+2)/(2\pi)}`,
and $`f_+ - f_-` a sign radius $`\sim\sqrt{d/(2\pi)}`; Gaussian times polynomial cannot beat the
constant $`1/\sqrt{2\pi}` (Cohn–Dong–Gonçalves), so the perturbation is essential.

*The perturbation.* Shifting the contour to $`t = \lambda(T + iu)`, $`u > -1`, and writing
$`r = e^{v(u)}` gives
$`f_j(r) = \dfrac{\lambda E_\lambda(i\lambda u)}{2\pi}\,r^{-(1+u)\lambda}\int_{\mathbb{R}}e^{\mathcal{L}_u(T)}P_j(T+iu)\,dT`
with the centered phase $`\mathcal{L}_u` of {bpref "eq_46_centered_phase"}[]; $`v(u)` is
*defined* so that $`\mathcal{L}_u'(0) = 0` ({bpref "eq_44_stationary_radius"}[]), and then
$`\mathcal{L}_u(T) = -\tfrac{\lambda V(u)}{2}T^2 + O(T^3)` with $`V = v'`. The Laplace method
({bpref "lemma_4_8"}[]) shows that the integral has the sign of $`P_j(iu)` for large $`d`,
provided the damping $`D_u(T) = -\operatorname{Re}\mathcal{L}_u(T)` is positive for $`T \ne 0` and
$`V(u) > 0`; this covers $`u \ge u_* = -1 + \tfrac{\log\lambda}{4\lambda}` for $`f_+` and
$`u \ge u_0 = 1 + \epsilon/4` for $`f_-, f_0`, and {bpref "lemma_4_10"}[] handles $`f_+` on
$`0 \le r \le e^{v(u_*)}`. Taking $`h(\zeta) = \int_0^\infty w(a)(\cos(a\zeta) - 1)\,da` for a
signed density $`w` ({bpref "eq_36_mellin_perturbation"}[]; the variable $`a` parametrizes radial
dilations), the damping becomes
$`D_u(T) = \int_0^\infty\bigl[\mu_{\lambda,1+u}(a) + \lambda w(a)\cosh(au)\bigr](1 - \cos(aT))\,da`
with the gamma damping density $`\mu` of {bpref "eq_37_gamma_damping_density"}[], while the
radius $`R_{\epsilon,d} = e^{v(u_0)}` satisfies
$`R_{\epsilon,d}/\sqrt d \to \sqrt{(1+u_0)/(4\pi)}\,\exp\bigl(\int_0^\infty w(a)a\sinh(u_0a)\,da\bigr)`.
So a more negative $`w` gives a smaller radius, but $`D_u \ge 0` needs
$`w(a) \ge -\mu_{\lambda,1+u}(a)/(\lambda\cosh(au))`, whose limit as $`\lambda \to \infty`,
$`u \to 1` is the ideal density $`w_*` below.

:::lemma_ "eq_32_ideal_density" (lean := "CohnElkies.integral_wallisRadiusIntegrand")
The ideal density $`w_*(a) = -\dfrac{e^{-2a}}{2a^2\cosh a}` saturates the pointwise damping
constraint and gives the greatest inward displacement (equation (32)):
$`\int_0^\infty w_*(a)\,a\sinh a\,da = \int_0^\infty -\dfrac{e^{-2a}\tanh a}{2a}\,da = -\tfrac12\log\dfrac{\pi}{2}`.
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

:::lemma_ "eq_33_critical_radius" (lean := "CohnElkies.saddleRadius_wallis_constant")
Since the Gaussian stationary radius at $`u = 1` is $`(2\pi)^{-1/2}\sqrt d`, the displacement of
{uses "eq_32_ideal_density"}[] gives the critical radius (equation (33))
$`\dfrac{1}{\sqrt{2\pi}}\exp\bigl(-\tfrac12\log\tfrac{\pi}{2}\bigr) = \dfrac{1}{\pi}`.
:::

:::proof "eq_33_critical_radius"
$`\exp(-\tfrac12\log\tfrac\pi2) = \sqrt{2/\pi}` and $`\sqrt{2/\pi}/\sqrt{2\pi} = 1/\pi`.
:::

One cannot take $`w = w_*` itself: it is not integrable at $`0` ($`w_*(a) = -1/(2a^2) + O(1/a)`),
and at $`u = 1` it cancels the gamma damping exactly, so $`V(1) \sim 1/(8\lambda)` and the
Gaussian width $`1/\sqrt{\lambda V(1)}` does not shrink. We therefore truncate $`w_*` to an
interval $`[a_0, A]` and taper it slightly, $`w_s = b\,w_*\mathbf 1_{[a_0,A]}` with
$`b(a) = 1 - 2\epsilon(1+a)`, which changes the radius exponent by $`O(\epsilon)` while keeping a
damping margin of order $`\epsilon` near $`u = 1` ({bpref "lemma_4_2"}[], {bpref "eq_54_shell_domination"}[]). But then
$`V(u) = V_\gamma - \int_{a_0}^A|w_s|a^2\cosh(ua)\,da` becomes negative for large $`u`, since
$`V_\gamma \sim 1/(2(1+u))` while the shell term grows exponentially in $`u`; this is repaired by
a small positive shell $`w_B = (Q/\cosh a)\mathbf 1_{[B,B+1]}` at much larger dilation parameters
$`B > A`, which is negligible at $`u = u_0` but dominates $`w_s` at every frequency when
$`u \ge U = 1 + \epsilon/2` ({bpref "lemma_4_6"}[]); its interval support avoids frequencies at
which its damping would vanish. With $`w = w_s + w_B` and the parameters below, letting first
$`d \to \infty` and then $`\epsilon \downarrow 0` gives
$`R_{\epsilon,d}/\sqrt d \to \sqrt{2/(4\pi)}\exp(-\tfrac12\log\tfrac\pi2) = 1/\pi`, which matches the
lower bound.

# The Mellin ansatz

:::group "grp_mellin_ansatz"
Mellin ansatz
:::

Parameters, shells, perturbation, envelope and polynomials of the construction (Section 4.2).

:::definition "eq_34_parameters" (lean := "CohnElkies.a₀ε, CohnElkies.Aε, CohnElkies.Bε, CohnElkies.Qε, CohnElkies.bε, CohnElkies.β") (parent := "grp_mellin_ansatz")
Put $`\lambda = d/2`; throughout the construction $`\epsilon` is fixed before $`d \to \infty`.
Constants in $`O_\epsilon(\cdot)`, $`\ll_\epsilon` may depend on $`\epsilon` but not on $`d` or on
the saddle parameter. Introduce cutoffs $`0 < a_0 < A < B`, a positive-shell amplitude $`Q > 0`,
and $`u_0 = 1 + \dfrac{\epsilon}{4}`, $`U = 1 + \dfrac{\epsilon}{2}`, $`C_0 = A + a_0^{-1}`.
The requirements as $`\epsilon \downarrow 0` are $`a_0 = o(\epsilon)`, $`e^{-2A}/A = o(\epsilon)`,
$`\epsilon A = o(1)`, $`A = o(B)`, $`BQe^{(u_0-1)B} = o(1)` and $`C_0Q^{-1}e^{-(U-1)(B-A)} = o(1)`.
The realization used (equation (34)) is
$`a_0 = \epsilon^2`, $`A = \log(1/\epsilon)`, $`B = \epsilon^{-3}`,
$`q_\epsilon = \dfrac{(u_0-1)+(U-1)}{2} = \dfrac{3\epsilon}{8}`, $`Q = e^{-q_\epsilon B}`,
$`b(a) = 1 - 2\epsilon(1+a)`, $`\beta = u_0 - 1 = \dfrac{\epsilon}{4}`.
For sufficiently small $`\epsilon`, $`b > 0` on $`[a_0, A]` and $`B > A + 1`.
:::

:::definition "eq_35_shells" (lean := "CohnElkies.w_s") (parent := "grp_mellin_ansatz")
With the parameters of {uses "eq_34_parameters"}[], the negative shell is (equation (35))
$`w_s(a) = -\dfrac{b(a)e^{-2a}}{2a^2\cosh a}\,\mathbf 1_{[a_0,A]}(a)`.
:::

:::definition "eq_35_positive_shell" (lean := "CohnElkies.w_B") (parent := "grp_mellin_ansatz")
With the parameters of {uses "eq_34_parameters"}[], the positive shell is (equation (35))
$`w_B(a) = \dfrac{Q}{\cosh a}\,\mathbf 1_{[B,B+1]}(a)`, and the signed density of the
construction is $`w = w_s + w_B` ({uses "eq_35_shells"}[]).
:::

:::definition "eq_36_mellin_perturbation" (lean := "CohnElkies.h_ε") (parent := "grp_mellin_ansatz")
The signed density $`w` of {uses "eq_35_positive_shell"}[] determines the even entire function
$`h_\epsilon(\zeta) = \int_0^\infty w(a)\bigl(\cos(a\zeta) - 1\bigr)\,da` (equation (36)).
:::

:::lemma_ "lemma_mellin_perturbation_axes" (lean := "CohnElkies.mellinShellPhase_neg, CohnElkies.mellinShellPhase_ofReal, CohnElkies.mellinShellPhase_imaginary, CohnElkies.h_εI, CohnElkies.saddleSourceShellDerivative") (parent := "grp_mellin_ansatz")
The perturbation $`h_\epsilon` of {uses "eq_36_mellin_perturbation"}[] is even and real on the
real and imaginary axes, with
$`h_\epsilon(iu) = \int_0^\infty w(a)(\cosh(au) - 1)\,da` and
$`ih_\epsilon'(iu) = \int_0^\infty w(a)\,a\sinh(ua)\,da`.
:::

:::proof "lemma_mellin_perturbation_axes"
$`\cos` is even, $`\cos(iau) = \cosh(au)` and $`\frac{d}{du}\cosh(au) = a\sinh(au)`; the
compactly supported $`w` allows differentiation under the integral sign.
:::

:::definition "eq_37_gamma_damping_density" (lean := "CohnElkies.μ_ℓ") (parent := "grp_mellin_ansatz")
For $`\eta > 0` and $`\lambda > 0`, the positive density describing the unperturbed gamma damping
is $`\mu_{\lambda,\eta}(a) = \dfrac{e^{-\eta a}}{a(1 - e^{-2a/\lambda})}` for $`a > 0`
(equation (37)).
:::

:::lemma_ "eq_54_shell_domination" (lean := "CohnElkies.upperFirstBranch_shortMeasure_pointwise, CohnElkies.upperFirstBranch_shortRatio_le") (parent := "grp_mellin_ansatz")
For every $`0 < \epsilon \le 1/4`, $`\lambda > 0`, $`-1 \le u \le U` and $`a \in [a_0, A]`, the
negative shell of {uses "eq_35_shells"}[] satisfies, with $`\mu_{\lambda,\eta}` from
{uses "eq_37_gamma_damping_density"}[],
$`\lambda|w_s(a)|\cosh(ua) \le (1 - 2\epsilon)\,\mu_{\lambda,1+u}(a)`
(indeed $`b(a)e^{(u-1)a}\cosh(ua)/\cosh a \le 1 - 2\epsilon`); equation (54).
:::

:::proof "eq_54_shell_domination"
Divide the negative density by $`\mu_{\lambda,1+u}`:
$`\dfrac{\lambda|w_s(a)|\cosh(ua)}{\mu_{\lambda,1+u}(a)}`
$`= b(a)\,\Theta_\lambda(a)\,e^{(u-1)a}\,\dfrac{\cosh(ua)}{\cosh a}`,
$`\Theta_\lambda(a) = \dfrac{1 - e^{-2a/\lambda}}{2a/\lambda} \in (0,1]`
(by $`1 - e^{-x} \le x`). For $`-1 < u \le 1`, both $`e^{(u-1)a}` and $`\cosh(ua)/\cosh a` are at
most $`1`, so the ratio is at most $`b(a) \le 1 - 2\epsilon`. For $`1 \le u \le U`, the inequality
$`\cosh(ua) \le e^{(u-1)a}\cosh a` bounds it by $`b(a)e^{2(u-1)a} \le b(a)e^{\epsilon a}`, and
$`b(a)e^{\epsilon a} \le e^{-2\epsilon(1+a)}e^{\epsilon a} \le e^{-2\epsilon} \le 1 - c\epsilon`.
Thus the taper retains a damping margin of order $`\epsilon` on every contour $`-1 < u \le U`.
:::

:::lemma_ "lemma_4_2" (lean := "CohnElkies.tendsto_shortShellRadiusContribution, CohnElkies.shortShellRadiusContribution") (parent := "grp_mellin_ansatz")
At the target saddle, the negative shell of {uses "eq_35_shells"}[] satisfies
$`\int_{a_0}^Aw_s(a)\,a\sinh(u_0a)\,da \longrightarrow \int_0^\infty w_*(a)a\sinh a\,da = -\tfrac12\log\dfrac{\pi}{2}`
as $`\epsilon \downarrow 0` ({uses "eq_32_ideal_density"}[]).
:::

:::proof "lemma_4_2"
The negative shell agrees with $`w_*` of {uses "eq_32_ideal_density"}[] up to its
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
:::

:::lemma_ "lemma_4_2_positive_shell" (lean := "CohnElkies.positiveShellRadiusContribution_bounds, CohnElkies.tendsto_positiveShellRadiusContribution, CohnElkies.positiveShellRadiusContribution") (parent := "grp_mellin_ansatz")
The positive shell of {uses "eq_35_positive_shell"}[] satisfies
$`0 \le \int_B^{B+1}w_B(a)\,a\sinh(u_0a)\,da \le (B+1)Qe^{(u_0-1)(B+1)} \longrightarrow 0`
as $`\epsilon \downarrow 0`.
:::

:::proof "lemma_4_2_positive_shell"
At $`u_0`, $`\sinh(u_0a)/\cosh a \le e^{(u_0-1)a}`, hence
$`0 \le \int_B^{B+1}w_B(a)a\sinh(u_0a)\,da \le (B+1)Qe^{(u_0-1)(B+1)}`, and
$`(B+1)Qe^{(u_0-1)(B+1)} = (B+1)e^{-\epsilon B/8 + \epsilon/4} \to 0`.
:::

:::lemma_ "lemma_4_2_separation" (lean := "CohnElkies.eventually_upper_shell_parameter_margin") (parent := "grp_mellin_ansatz")
For all sufficiently small $`\epsilon` the shells of {uses "eq_35_shells"}[] and
{uses "eq_35_positive_shell"}[] are separated: $`C_0e^{(U-1)A} \le Qe^{(U-1)B}/5000`.
:::

:::proof "lemma_4_2_separation"
At $`u_0`, $`\sinh(u_0a)/\cosh a \le e^{(u_0-1)a}`, hence
$`0 \le \int_B^{B+1}w_B(a)a\sinh(u_0a)\,da \le (B+1)Qe^{(u_0-1)(B+1)}`. The amplitude in (34) has
exponential slope $`q_\epsilon` strictly between $`u_0 - 1` and $`U - 1`, so
$`Qe^{(u_0-1)B} = e^{-\epsilon B/8}` and $`Qe^{(U-1)B} = e^{\epsilon B/8}`. Since
$`\epsilon B = \epsilon^{-2}` while $`B`, $`C_0` and $`e^{(U-1)A}` grow only polynomially in
$`1/\epsilon`, all three separation quantities are $`O(e^{-c'/\epsilon^2})`.
:::

The shells determine the common envelope; it remains to impose the Fourier symmetries and
select the signs. The first gamma pole occurs at $`t = -i\lambda`, i.e. $`\zeta = -i`.

:::definition "eq_38_envelope" (lean := "CohnElkies.E") (parent := "grp_mellin_ansatz")
With $`h_\epsilon` from {uses "eq_36_mellin_perturbation"}[], the envelope is (equation (38))
$`E_\lambda(t)`
$`= \pi^{it/2}\,\Gamma\Bigl(\dfrac{\lambda - it}{2}\Bigr)\,e^{\lambda h_\epsilon(t/\lambda)}`.
:::

:::definition "eq_38_envelope_polynomials" (lean := "CohnElkies.PPlus, CohnElkies.PMinus, CohnElkies.PZero") (parent := "grp_mellin_ansatz")
With $`\beta` from {uses "eq_34_parameters"}[], the polynomials are (equation (38))
$`P_\pm(\zeta) = 1 + \zeta^2 + \beta \pm i\zeta(1+\zeta^2)`, $`P_0(\zeta) = -(1+\zeta^2)`.
:::

:::definition "eq_38_mellin_data" (lean := "CohnElkies.spectrum, CohnElkies.XPlus, CohnElkies.XMinus, CohnElkies.XZero") (parent := "grp_mellin_ansatz")
For $`j \in \{-, 0, +\}` the Mellin data are (equation (38))
$`X_{f_j}(t) = E_\lambda(t)P_j(t/\lambda)`, with $`E_\lambda` from {uses "eq_38_envelope"}[] and
$`P_j` from {uses "eq_38_envelope_polynomials"}[].
:::

:::definition "eq_38_profiles" (lean := "CohnElkies.mellinProfile, CohnElkies.fPlus, CohnElkies.fMinus, CohnElkies.fZero") (parent := "grp_mellin_ansatz")
The radial profiles are the inverse Mellin transforms of {uses "eq_38_mellin_data"}[]
(equation (38)),
$`f_j(r) = \dfrac{r^{-\lambda}}{2\pi}\int_{\mathbb{R}}X_{f_j}(t)r^{it}\,dt` ($`r > 0`),
extended to $`r = 0` by the value (42) of {bpref "lemma_4_3_origin"}[].
:::

:::lemma_ "eq_39_polynomial_symmetries" (lean := "CohnElkies.minusPolynomial_neg, CohnElkies.PZero_neg, CohnElkies.plusPolynomial_conj, CohnElkies.minusPolynomial_conj, CohnElkies.PZero_conj, CohnElkies.plusPolynomial_neg_I, CohnElkies.minusPolynomial_neg_I, CohnElkies.PZero_neg_I") (parent := "grp_mellin_ansatz")
The polynomials of {uses "eq_38_envelope_polynomials"}[] satisfy $`P_-(-\zeta) = P_+(\zeta)`,
$`P_0(-\zeta) = P_0(\zeta)`, $`\overline{P_j(\zeta)} = P_j(-\bar\zeta)`,
$`P_\pm(-i) = \beta > 0` and $`P_0(-i) = 0`.
:::

:::proof "eq_39_polynomial_symmetries"
Direct substitution of $`-\zeta`, $`\bar\zeta` and $`\zeta = -i`.
:::

:::lemma_ "eq_39_polynomial_values" (lean := "CohnElkies.plusPolynomial_imaginary, CohnElkies.minusPolynomial_imaginary, CohnElkies.PZero_imaginary, CohnElkies.plusPolynomial_imaginary_re_pos, CohnElkies.minusPolynomial_imaginary_re_neg, CohnElkies.PZero_imaginary_re_pos") (parent := "grp_mellin_ansatz")
On the imaginary axis the polynomials of {uses "eq_38_envelope_polynomials"}[] are real
(equation (39)):
$`P_+(iu) = \beta + (1-u)^2(1+u)`, $`P_-(iu) = \beta + (1-u)(1+u)^2`, $`P_0(iu) = u^2 - 1`.
Consequently $`P_+(iu) > 0` for every $`u > -1`, whereas $`\beta = u_0 - 1` gives
$`P_-(iu_0) = -\beta(3 + 4\beta + \beta^2) < 0` and $`P_0(iu_0) = \beta(2+\beta) > 0`, and these
signs persist for all $`u \ge u_0`.
:::

:::proof "eq_39_polynomial_values"
Direct substitution of $`\zeta = iu`.
:::

:::lemma_ "lemma_4_3" (lean := "CohnElkies.plusSaddleSchwartz, CohnElkies.minusSaddleSchwartz, CohnElkies.zeroSaddleSchwartz, CohnElkies.mellinProfileSchwartz") (parent := "grp_mellin_ansatz")
For every sufficiently small $`\epsilon > 0` and every integer $`d \ge 1`, with $`\lambda = d/2`,
the inverse Mellin integrals of {uses "eq_38_profiles"}[], initially defined for $`r > 0`,
extend to $`f_j \in \mathcal{S}_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})` for $`j \in \{-,0,+\}`.
More generally the pole $`t = -i(\lambda+2n)`, $`n \ge 0`, contributes to $`f_j(r)` the term
(equation (41))
$`2\pi^{\lambda/2+n}\,r^{2n}\,\dfrac{(-1)^n}{n!}\,e^{\lambda h_\epsilon(\zeta_n)}\,P_j(\zeta_n)`,
where $`\zeta_n = -i(1 + 2n/\lambda)` (`CohnElkies.poleResidue`,
`CohnElkies.mellinData_nthPole_decomposition`).
:::

:::proof "lemma_4_3"
Fix $`d` and $`\epsilon`. Compact support of $`w` makes $`h_\epsilon` entire, and on each horizontal
line $`t = s + i\tau` it satisfies
$`|h_\epsilon((s+i\tau)/\lambda)| \le 2\int_0^\infty|w(a)|\cosh(a\tau/\lambda)\,da`,
so the perturbation is bounded on every fixed horizontal strip. Uniformly for $`\tau` in compact
pole-free intervals, the polynomial decay of $`\Gamma` along vertical lines
($`|\operatorname{Im} z|^k|\Gamma(z)| \le \Gamma(\operatorname{Re} z + k)`, from
{uses "eq_7_gamma_identities"}[] and $`|\Gamma(z)| \le \Gamma(\operatorname{Re} z)`) gives
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
real $`t` (from {uses "eq_39_polynomial_symmetries"}[], realness of $`h_\epsilon` on $`\mathbb{R}`,
and $`\Gamma(\bar z) = \overline{\Gamma(z)}`) makes the extension real.
:::

:::lemma_ "lemma_4_3_fourier" (lean := "CohnElkies.saddleSource_fourier_minus_eq_plus, CohnElkies.fourier_zeroSaddleSchwartz") (parent := "grp_mellin_ansatz")
The extensions of {uses "lemma_4_3"}[] satisfy (equation (40))
$`\widehat{f_-} = f_+` and $`\widehat{f_0} = f_0`.
:::

:::proof "lemma_4_3_fourier"
Because $`h_\epsilon` is even, {uses "lemma_gaussian_mellin"}[] gives
$`m_\lambda(t)E_\lambda(-t) = E_\lambda(t)`; with $`P_-(-\zeta) = P_+(\zeta)` and $`P_0` even ({uses "eq_39_polynomial_symmetries"}[]),
$`m_\lambda(t)X_{f_-}(-t) = X_{f_+}(t)` and $`m_\lambda(t)X_{f_0}(-t) = X_{f_0}(t)`. By
{uses "eq_10_critical_line"}[], $`X_{\widehat{f_-}} = X_{f_+}` and $`X_{\widehat{f_0}} = X_{f_0}`,
and
injectivity of the Mellin transform on the critical line ({uses "eq_8_mellin_inversion"}[])
gives (40).
:::

:::lemma_ "lemma_4_3_origin" (lean := "CohnElkies.originValue, CohnElkies.saddleSource_zero_pos, CohnElkies.saddleSource_zero_eq, CohnElkies.fZero_zero") (parent := "grp_mellin_ansatz")
The extensions of {uses "lemma_4_3"}[] satisfy (equation (42))
$`f_+(0) = f_-(0) = 2\pi^{\lambda/2}e^{\lambda h_\epsilon(i)}\beta > 0` and $`f_0(0) = 0`.
:::

:::proof "lemma_4_3_origin"
The term $`n = 0` of (41) is the value at $`r = 0`; evenness gives
$`h_\epsilon(-i) = h_\epsilon(i)`, and $`P_\pm(-i) = \beta`, $`P_0(-i) = 0` give (42).
:::

# Saddle geometry

:::group "grp_saddle_geometry"
Saddle geometry
:::

Stationary radii, the centered phase, damping and moment quantities, and the damping estimates
(Section 4.3: (43)–(49) and Lemmas 4.4–4.7).

:::definition "eq_43_saddle_parameters" (lean := "CohnElkies.u_star") (parent := "grp_saddle_geometry")
Recall $`u_0`, $`U` from {uses "eq_34_parameters"}[] and set (equation (43))
$`u_* = -1 + \dfrac{\log\lambda}{4\lambda}`. For $`u > -1` put $`\eta = 1 + u > 0`,
$`m = \dfrac{\lambda\eta}{2}`, and use $`\psi = (\log\Gamma)'` from {uses "def_digamma"}[], with the
branch of $`\log\Gamma` real on the positive axis. Note
$`m \ge \lambda(1+u_*)/2 = \tfrac18\log\lambda`
for $`u \ge u_*`.
:::

:::definition "eq_44_stationary_radius" (lean := "CohnElkies.vℓ, CohnElkies.logRadius, CohnElkies.saddleLogRadius_eq_digamma_add_shellDerivative") (parent := "grp_saddle_geometry")
On the contour $`t = \lambda(T + iu)`, the logarithm of $`E_\lambda(t)r^{it}`
({uses "eq_38_envelope"}[]) is
$`\tfrac{i\lambda(T+iu)}{2}\log\pi + \log\Gamma\bigl(m - \tfrac{i\lambda T}{2}\bigr)`
$`+ \lambda h_\epsilon(T+iu) + i\lambda(T+iu)\log r`,
whose $`T`-derivative at $`T = 0` is
$`i\lambda(\tfrac12\log\pi - \tfrac12\psi(m) - \int_0^\infty w(a)a\sinh(ua)\,da + \log r)`
({uses "lemma_mellin_perturbation_axes"}[]). Thus $`T = 0` is stationary precisely when
$`r = e^{v(u)}`, where (equation (44))
$`v(u) = -\tfrac12\log\pi + \tfrac12\psi(m) + \int_0^\infty w(a)\,a\sinh(ua)\,da`.
Uses {uses "eq_43_saddle_parameters"}[], {uses "eq_36_mellin_perturbation"}[].
:::

:::definition "eq_44_saddle_variance" (lean := "CohnElkies.upperSaddleVariance, CohnElkies.V_γ, CohnElkies.V_s, CohnElkies.V_B") (parent := "grp_saddle_geometry")
The saddle variance is $`V(u) = V_\gamma - V_s + V_B` with the moments of
{bpref "eq_48_moments"}[] (formally $`V = v'` for $`v` of {uses "eq_44_stationary_radius"}[]).
:::

:::definition "eq_45_log_gamma_phase" (lean := "CohnElkies.G_ℓη") (parent := "grp_saddle_geometry")
For $`\lambda, \eta > 0` and $`T \in \mathbb{R}`, with $`\mu_{\lambda,\eta}` from
{uses "eq_37_gamma_damping_density"}[], the centered log-gamma phase is (equation (45))
$`G_{\lambda,\eta}(T) := \int_0^\infty(e^{iaT} - 1 - iaT)\,\mu_{\lambda,\eta}(a)\,da`.
:::

:::lemma_ "eq_45_log_gamma_integral" (lean := "CohnElkies.exp_G_ℓη") (parent := "grp_saddle_geometry")
For $`\lambda, \eta > 0`, $`m = \lambda\eta/2`, and $`T \in \mathbb{R}`, the phase of
{uses "eq_45_log_gamma_phase"}[] satisfies
$`e^{G_{\lambda,\eta}(T)} = \dfrac{\Gamma\bigl(m - \tfrac{i\lambda T}{2}\bigr)}{\Gamma(m)}\,e^{i\lambda T\psi(m)/2}`,
that is, $`G_{\lambda,\eta}(T) = \log\Gamma\bigl(m - \tfrac{i\lambda T}{2}\bigr) - \log\Gamma(m) + \tfrac{i\lambda T}{2}\psi(m)`
(Binet-type representation; {uses "def_digamma"}[]).
:::

:::proof "eq_45_log_gamma_integral"
Apply the Malmstén–Binet integral representation of $`\log\Gamma`,
$`\log\Gamma(z+w) - \log\Gamma(z) - w\psi(z) = \int_0^\infty (e^{-ws} - 1 + ws)\,\dfrac{e^{-zs}}{s(1-e^{-s})}\,ds`
($`\operatorname{Re} z > 0`, $`\operatorname{Re}(z+w) > 0`), with $`z = m`, $`w = -i\lambda T/2`,
and substitute $`a = \lambda s/2`. (The formalization proves the exponentiated identity through
the Euler product of $`\Gamma`: truncating the geometric series in
$`1/(1 - e^{-2a/\lambda})` gives the ratios $`\Gamma_N(m - ib)/\Gamma_N(m)` of the partial
products, which converge to the gamma ratio.)
:::

:::definition "eq_45_gamma_damping" (lean := "CohnElkies.D_γ") (parent := "grp_saddle_geometry")
The gamma damping is
$`D_\gamma(T) := -\operatorname{Re}G_{\lambda,\eta}(T) = \int_0^\infty(1 - \cos(aT))\,\mu_{\lambda,\eta}(a)\,da`
({uses "eq_45_log_gamma_phase"}[]).
:::

:::lemma_ "lemma_gamma_damping_nonneg" (lean := "CohnElkies.upperGammaDamping_nonneg") (parent := "grp_saddle_geometry")
$`D_\gamma(T) \ge 0` for every $`T` ({uses "eq_45_gamma_damping"}[]): the gamma function in the
Mellin envelope always damps the integrand away from $`T = 0`.
:::

:::proof "lemma_gamma_damping_nonneg"
$`1 - \cos(aT) \ge 0` and $`\mu_{\lambda,\eta} > 0`.
:::

:::definition "eq_46_centered_phase" (lean := "CohnElkies.L_u") (parent := "grp_saddle_geometry")
Normalize $`E_\lambda(\lambda(T+iu))r^{i\lambda T}` by the positive number
$`E_\lambda(i\lambda u) = \pi^{-\lambda u/2}\Gamma(m)e^{\lambda h_\epsilon(iu)}` and set
$`r = e^{v(u)}`.
The linear terms cancel by the saddle equation, and (36) gives (equations (46), (47))
$`\mathcal{L}_u(T) := \log\dfrac{E_\lambda(\lambda(T+iu))}{E_\lambda(i\lambda u)} + i\lambda Tv(u)`,
which equals
$`G_{\lambda,\eta}(T) + \lambda\int_0^\infty w(a)\cosh(ua)(\cos(aT)-1)\,da`
$`+ i\lambda\int_0^\infty w(a)\sinh(ua)(aT - \sin(aT))\,da`.
Uses {uses "eq_44_stationary_radius"}[], {uses "eq_45_log_gamma_phase"}[] and
{uses "eq_45_log_gamma_integral"}[].
:::

:::definition "eq_47_total_damping" (lean := "CohnElkies.D_u, CohnElkies.saddleSourceContourDamping") (parent := "grp_saddle_geometry")
The total damping is (equation (47))
$`D_u(T) := -\operatorname{Re}\mathcal{L}_u(T) = D_\gamma(T)`
$`+ \lambda\int_0^\infty w(a)\cosh(ua)(1 - \cos(aT))\,da`
({uses "eq_46_centered_phase"}[], {uses "eq_45_gamma_damping"}[]). Equation (47) isolates the
main difficulty: $`w_s` reduces $`D_u`, while $`w_B` increases it. We must prove $`D_u(T) > 0`
for every $`T \ne 0` and $`V(u) > 0` for every $`u \ge u_*`.
:::

:::definition "eq_48_moments" (lean := "CohnElkies.V_γ, CohnElkies.M₃_γ, CohnElkies.M₃") (parent := "grp_saddle_geometry")
The quadratic and cubic sizes of the phase are measured by (equation (48))
$`V_\gamma = \dfrac1\lambda\int_0^\infty a^2\mu_{\lambda,\eta}(a)\,da`,
$`M_3 = \dfrac1\lambda\int_0^\infty a^3\mu_{\lambda,\eta}(a)\,da`
$`+ \int_0^\infty\bigl(|w_s(a)| + w_B(a)\bigr)a^3\cosh(ua)\,da`
({uses "eq_37_gamma_damping_density"}[], {uses "eq_35_positive_shell"}[]).
:::

:::definition "eq_49_shell_contributions" (lean := "CohnElkies.D_s, CohnElkies.D_B, CohnElkies.V_s, CohnElkies.V_B") (parent := "grp_saddle_geometry")
The shell contributions are (equation (49))
$`D_s(T) = \lambda\int_{a_0}^A|w_s(a)|\cosh(ua)(1-\cos(aT))\,da`,
$`D_B(T) = \lambda\int_B^{B+1}w_B(a)\cosh(ua)(1-\cos(aT))\,da`,
$`V_s = \int_{a_0}^A|w_s(a)|a^2\cosh(ua)\,da`, $`V_B = \int_B^{B+1}w_B(a)a^2\cosh(ua)\,da`
({uses "eq_35_shells"}[], {uses "eq_35_positive_shell"}[]). In particular
$`D_u = D_\gamma - D_s + D_B` and $`V(u) = V_\gamma - V_s + V_B`
({uses "eq_47_total_damping"}[], {uses "eq_44_saddle_variance"}[]).
:::

:::lemma_ "lemma_4_4" (lean := "CohnElkies.norm_L_u_add_le") (parent := "grp_saddle_geometry")
For every $`\lambda > 0`, $`u > -1` and $`T \in \mathbb{R}`, the quantities of
{uses "eq_46_centered_phase"}[], {uses "eq_44_saddle_variance"}[] and {uses "eq_48_moments"}[]
satisfy (equation (50))
$`\Bigl|\mathcal{L}_u(T) + \dfrac{\lambda V(u)}{2}T^2\Bigr| \le \dfrac{\lambda M_3}{6}|T|^3`.
:::

:::proof "lemma_4_4"
The globally valid Taylor estimates $`e^{ix} - 1 - ix = -x^2/2 + O(|x|^3)` and
$`x - \sin x = O(|x|^3)`, applied to (45) and (46) with $`|\sinh(ua)| \le \cosh(ua)`.
:::

:::lemma_ "eq_51_gamma_moments" (lean := "CohnElkies.upperGammaVariance_bounds, CohnElkies.upperGammaThirdMoment_bounds") (parent := "grp_saddle_geometry")
For $`\lambda, \eta > 0` the gamma moments of {uses "eq_48_moments"}[] satisfy (equations
(51)–(52))
$`\dfrac{1}{2\eta} \le V_\gamma \le \dfrac{1}{2\eta} + \dfrac{1}{\lambda\eta^2}`,
$`\dfrac{1}{2\eta^2} \le \dfrac1\lambda\int_0^\infty a^3\mu_{\lambda,\eta}(a)\,da \le \dfrac{1}{2\eta^2} + \dfrac{2}{\lambda\eta^3}`.
:::

:::proof "eq_51_gamma_moments"
Both follow from $`x \le e^x - 1 \le xe^x` applied to the density $`\mu_{\lambda,\eta}` of
{uses "eq_37_gamma_damping_density"}[] (the report instead inserts uniform trigamma and
polygamma estimates into the polygamma expressions of the moments).
:::

:::lemma_ "eq_53_gamma_damping_lower" (lean := "CohnElkies.upperGammaDamping_lower_bound") (parent := "grp_saddle_geometry")
For $`\lambda, \eta > 0` and all $`T` (equation (53)),
$`D_\gamma(T) \ge \dfrac{\lambda}{8e}\min\Bigl(\dfrac{T^2}{\eta}, |T|\Bigr)`
({uses "eq_45_gamma_damping"}[]).
:::

:::proof "eq_53_gamma_damping_lower"
$`1 - e^{-x} \le x` in (37) gives $`\mu_{\lambda,\eta}(a) \ge \lambda e^{-\eta a}/(2a^2)`. For
$`T \ne 0` take $`L = \min(\eta^{-1}, |T|^{-1})`; on $`0 < a < L` both $`e^{-\eta a}` and
$`(1-\cos(aT))/(a^2T^2)` are bounded below by absolute positive constants, so
$`D_\gamma(T) \ge c\lambda T^2L`, which is (53).
:::

Lemma 4.4 and (51)–(53) control the gamma contribution and cubic remainder. For $`u_* \le u \le U` the negative
shell removes at most a $`(1 - c\epsilon)`-fraction of the gamma damping, while $`w_B` contributes
nonnegative damping.

:::lemma_ "lemma_4_5" (lean := "CohnElkies.upperFirstBranchSaddleDamping_lower_bound") (parent := "grp_saddle_geometry")
For every $`0 < \epsilon \le 1/4`, $`\lambda > 0` and $`-1 < u \le U`, the total damping of
{uses "eq_47_total_damping"}[] satisfies (equation (55))
$`D_u(T) \ge 2\epsilon D_\gamma(T)` for all $`T`.
:::

:::proof "lemma_4_5"
Integrating (54) of {uses "eq_54_shell_domination"}[] against $`1 - \cos(aT) \ge 0` shows that the
negative shell removes at most a $`(1-2\epsilon)`-fraction of the gamma damping, and the
contribution of $`w_B` is nonnegative, so
$`D_u(T) \ge D_\gamma(T) - (1-2\epsilon)\int_{a_0}^A(1-\cos(aT))\mu_{\lambda,\eta}(a)\,da`
$`\ge 2\epsilon D_\gamma(T)`.
:::

:::lemma_ "eq_56_first_branch_variance" (lean := "CohnElkies.upperFirstBranch_shortVariance_le_gamma, CohnElkies.upperFirstBranch_saddleSourceGaussianVariance_lower_bound, CohnElkies.eventually_saddleSourceGaussianVariance_firstBranch_pos") (parent := "grp_saddle_geometry")
For every $`0 < \epsilon \le 1/4`, $`\lambda > 0` and $`-1 < u \le U`, with $`\eta = 1 + u`,
the variances of {uses "eq_49_shell_contributions"}[] and {uses "eq_44_saddle_variance"}[]
satisfy (equation (56))
$`V_s \le (1 - 2\epsilon)V_\gamma`, hence $`V(u) \ge 2\epsilon V_\gamma \ge \dfrac{\epsilon}{\eta} > 0`.
:::

:::proof "eq_56_first_branch_variance"
Integrating (54) of {uses "eq_54_shell_domination"}[] against $`a^2/\lambda` gives
$`V_s \le (1 - 2\epsilon)V_\gamma`, hence $`V(u) \ge 2\epsilon V_\gamma + V_B \ge \epsilon/\eta` by
(51) of {uses "eq_51_gamma_moments"}[].
:::

:::lemma_ "eq_57_first_branch_third_moment" (lean := "CohnElkies.upperFirstBranch_saddleSourceThirdMoment_scaled_le") (parent := "grp_saddle_geometry")
There is $`\epsilon_0 > 0` such that, for every $`0 < \epsilon < \epsilon_0`, there are
constants $`C_\epsilon, \lambda_\epsilon > 0` with: for every $`\lambda \ge \lambda_\epsilon` and
$`u_* \le u \le U` (equation (57)), $`M_3 \le C_\epsilon V(u)` ({uses "eq_48_moments"}[],
{uses "eq_44_saddle_variance"}[]); moreover $`\lambda\eta \ge (\log\lambda)/4` on this range
({uses "eq_43_saddle_parameters"}[]).
:::

:::proof "eq_57_first_branch_third_moment"
For $`u_* \le u \le U` the positive-shell variance satisfies
$`V_B \le (B+1)^2Qe^{(U-1)(B+1)} = O_\epsilon(1)`, and since $`\lambda\eta \ge (\log\lambda)/4` and
$`\eta \le 2 + \epsilon/2`, (51) gives $`V(u) \le V_\gamma + V_B = O_\epsilon(\eta^{-1})`, while
$`V(u) \ge \epsilon/\eta` by {uses "eq_56_first_branch_variance"}[]. Similarly (54) bounds the
negative-shell third moment by the gamma third moment $`\frac1\lambda\int a^3\mu_{\lambda,\eta}`,
the positive-shell third moment is $`O_\epsilon(1)`, and (52) of {uses "eq_51_gamma_moments"}[]
gives $`M_3 = O_\epsilon(\eta^{-2}) = O_\epsilon(V(u))`.
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
{bpref "lemma_4_2_separation"}[] gives $`\rho_\epsilon = O(e^{-c/\epsilon^2}) = o(1)` as
$`\epsilon \downarrow 0`.

:::lemma_ "eq_59_60_shell_damping_bounds" (lean := "CohnElkies.upperShortShellDamping_global_bound, CohnElkies.positiveShellDamping_lower_bound") (parent := "grp_saddle_geometry")
For $`\lambda \ge 0`, $`u = 1 + \delta \ge 1` and all $`T`, the shell dampings of
{uses "eq_49_shell_contributions"}[] satisfy (equations (59)–(60))
$`D_s(T) \le \lambda C_0e^{\delta A}\min(T^2, 1)` and
$`D_B(T) \ge \dfrac{\lambda}{50}Qe^{\delta B}\min(T^2, 1)`, with $`C_0 = A + a_0^{-1}`
({uses "eq_34_parameters"}[]).
:::

:::proof "eq_59_60_shell_damping_bounds"
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
which is (60).
:::

:::lemma_ "lemma_4_6" (lean := "CohnElkies.eventually_upper_shortShell_domination, CohnElkies.eventually_upperSaddleDamping_gamma_add_shell") (parent := "grp_saddle_geometry")
There is $`\epsilon_0 > 0` such that, for every $`0 < \epsilon < \epsilon_0`, every
$`\lambda \ge 0`, every $`u \ge U` and every $`T \in \mathbb{R}` (equations (61)–(62)),
$`D_s(T) \le \dfrac{1}{100}D_B(T)`, hence $`D_u(T) \ge D_\gamma(T) + \dfrac{99}{100}D_B(T)`
({uses "eq_49_shell_contributions"}[], {uses "eq_47_total_damping"}[]).
:::

:::proof "lemma_4_6"
For $`T \ne 0`, division of (59) by (60) ({uses "eq_59_60_shell_damping_bounds"}[]) gives
$`D_s(T)/D_B(T) \ll C_0Q^{-1}e^{-\delta(B-A)} \le \rho_\epsilon`, and
{uses "lemma_4_2_separation"}[] makes the right side less than $`1/100` for small $`\epsilon`;
at $`T = 0` both damping terms vanish. Then $`D_u = D_\gamma - D_s + D_B` proves (62).
:::

:::lemma_ "eq_64_positive_shell_variance" (lean := "CohnElkies.upperPositiveShellVariance_bounds") (parent := "grp_saddle_geometry")
For $`u = 1 + \delta \ge 1` the positive-shell variance of {uses "eq_49_shell_contributions"}[]
satisfies (equation (64))
$`\tfrac12B^2Qe^{\delta B} \le V_B \le (B+1)^2Qe^{\delta(B+1)}`.
:::

:::proof "eq_64_positive_shell_variance"
Integrate $`w_B(a)\cosh(ua) \asymp Qe^{\delta a}` against $`a^2` over $`[B, B+1]`.
:::

:::lemma_ "eq_66_second_branch_variance" (lean := "CohnElkies.eventually_upper_shortShellVariance_domination, CohnElkies.eventually_upperSaddleVariance_bounds, CohnElkies.eventually_upperSaddleVariance_pos, CohnElkies.eventually_upperSaddleThirdMoment_le_variance") (parent := "grp_saddle_geometry")
There is $`\epsilon_0 > 0` such that, for every $`0 < \epsilon < \epsilon_0`, there is
$`C_\epsilon > 0` with: for every $`\lambda \ge 1` and $`u \ge U` (equations (63), (65)–(66)),
$`V_s \le \dfrac{1}{100}V_B`, hence
$`V_\gamma + \dfrac{99}{100}V_B \le V(u) \le V_\gamma + V_B` and $`V(u) > 0`, and
$`M_3 \le C_\epsilon V(u)` ({uses "eq_44_saddle_variance"}[], {uses "eq_48_moments"}[],
{uses "eq_49_shell_contributions"}[]).
:::

:::proof "eq_66_second_branch_variance"
Comparing the quadratic coefficients of (59) and (60) gives $`V_s = O(\rho_\epsilon V_B)`, with
$`\rho_\epsilon < 1/100` for small $`\epsilon` by {uses "lemma_4_2_separation"}[]; then
$`V(u) = V_\gamma - V_s + V_B` gives (63). Since $`\delta \ge \epsilon/2`,
$`V_B \gg B^2Qe^{\epsilon B/2} = B^2e^{\epsilon B/8} \gg 1` by
{uses "eq_64_positive_shell_variance"}[], while $`V_\gamma \ll \eta^{-1} \ll 1` by (51); thus
$`V_\gamma = O(V_B)`. Since $`a \le A` on the negative shell,
$`\int_{a_0}^A|w_s|a^3\cosh(ua) \le AV_s \ll A\rho_\epsilon V_B`, while $`a \le B+1` bounds the
positive-shell third moment by $`(B+1)V_B`; this proves (65). Finally, since
$`\eta \ge 2 + \epsilon/2`, (51)–(52) of {uses "eq_51_gamma_moments"}[] bound the gamma third
moment by $`O(V_\gamma)`; the shell third moments are $`O_\epsilon(V_B)`, and $`V_\gamma = O(V_B)`,
$`V_B \asymp V(u)` give $`M_3 = O_\epsilon(V(u))`, which is (66).
:::

Set $`T_0 = (2(B+1))^{-1}`. To bound the tails of the saddle integral for $`u \ge U`, we sharpen
the damping on three frequency ranges: $`|T| \le T_0`, where $`D_u` is quadratic;
$`T_0 \le |T| \le \eta`, where $`w_B` supplies a uniform positive floor; and $`|T| \ge \eta`, where
the gamma contribution also grows linearly.

:::lemma_ "lemma_4_7" (lean := "CohnElkies.eventually_secondBranch_damping_pointwise") (parent := "grp_saddle_geometry")
There is $`\epsilon_0 > 0` such that, for every $`0 < \epsilon < \epsilon_0`, every
$`\lambda > 0` and every $`u \ge U`, with $`\delta = u - 1` and $`T_0 = (2(B+1))^{-1}`
(equations (67)–(69)), the damping $`D_u` of {uses "eq_47_total_damping"}[] admits the
pointwise splitting
$`(1+|T|^3)e^{-D_u(T)} \le (1+|T|^3)e^{-\frac{\lambda V(u)}{100e}T^2}`
$`+ e^{-\Xi}\Bigl((1+|T|^3)e^{-\frac{\lambda}{8e(2+\delta)}T^2} + (1+|T|^3)e^{-\frac{\lambda}{8e}|T|}\Bigr)`
for all $`T \in \mathbb{R}`, with the barrier $`\Xi = \dfrac{99}{5000}\lambda Qe^{\delta B}T_0^2`:
on $`|T| \le T_0` the damping is Gaussian with rate proportional to $`\lambda V(u)`, and for
$`|T| \ge T_0` it exceeds the shell barrier $`\Xi` plus the gamma damping $`D_\gamma`
(quadratic up to $`|T| \approx \eta`, linear beyond).
:::

:::proof "lemma_4_7"
If $`|T| \le T_0`, then $`|aT| \le 1/2` on $`[B,B+1]`, so $`1 - \cos(aT) \asymp a^2T^2` and
$`D_B(T) \asymp \lambda V_BT^2`. Since $`\eta \ge 2 + \epsilon/2` and $`|T| \le \eta`, (53) and (51)
of {uses "eq_53_gamma_damping_lower"}[] and {uses "eq_51_gamma_moments"}[] give
$`D_\gamma(T) \gg \lambda T^2/\eta \gg \lambda V_\gamma T^2`. Combining these through (62) of
{uses "lemma_4_6"}[] and (63) of {uses "eq_66_second_branch_variance"}[] proves (67). If
$`T_0 \le |T| \le \eta`, then $`\min(T^2,1) \ge T_0^2`, so (62) and (60)
({uses "eq_59_60_shell_damping_bounds"}[]) give
$`D_u(T) \gg \lambda T_0^2Qe^{\delta B} \gg_\epsilon \lambda Qe^{\delta B}`, which is (68). If
$`|T| \ge \eta`, then $`\min(T^2,1) = 1` and (53) gives $`D_\gamma(T) \gg \lambda|T|`; adding the
positive shell through (62) and (60) yields (69).
:::

# Global saddle asymptotics

The damping bounds now determine the exterior signs of $`f_+, f_-, f_0`. On each contour, the
centered phase is quadratic near $`T = 0`, the factor $`P_j(T+iu)` is asymptotic to $`P_j(iu)`, and
the remaining contour is negligible.

:::lemma_ "lemma_4_8" (lean := "CohnElkies.eventually_firstBranch_fullGaussianError, CohnElkies.eventually_secondBranch_fullGaussianError, CohnElkies.eventually_mellinProfile_re_mul_pos_firstBranch, CohnElkies.eventually_mellinProfile_re_mul_pos_secondBranch")
Fix $`0 < \epsilon < \epsilon_0`, let $`\lambda = d/2`, and recall $`u_0, U` from
{uses "eq_34_parameters"}[] and $`u_*` from {uses "eq_43_saddle_parameters"}[]. For $`u > -1` and
$`P \in \{P_+, P_-, P_0\}` put
$`I_{\lambda,P}(u) = \int_{\mathbb{R}}e^{\mathcal{L}_u(T)}P(T + iu)\,dT`
with $`\mathcal{L}_u` from {uses "eq_46_centered_phase"}[]. For all sufficiently large $`d`
(equation (70)),
$`\Bigl|I_{\lambda,P}(u) - P(iu)\sqrt{\dfrac{2\pi}{\lambda V(u)}}\Bigr| < |P(iu)|\sqrt{\dfrac{2\pi}{\lambda V(u)}}`
uniformly for $`u \ge u_*` when $`P = P_+`, and uniformly for $`u \ge u_0` when $`P = P_-` or
$`P = P_0`; in particular $`I_{\lambda,P}(u)`, and hence $`f_j(e^{v(u)})`, has the sign of
$`P(iu)` there. The same holds for every polynomial $`P` of degree at most $`3` with
$`\overline{P(\zeta)} = P(-\bar\zeta)`, on any range $`u \ge u_0(P) > -1` on which $`P(iu)` stays
bounded away from $`0`; the formalization treats the two branches $`u \le U` (gamma-controlled)
and $`u \ge U` (shell-controlled) separately.
:::

:::proof "lemma_4_8"
Contour shift. The poles of the integrand in (38) are $`t = -i(\lambda + 2n)`, $`n \ge 0`, so
{uses "lemma_4_3"}[] allows the contour to be shifted to $`t = \lambda(T + iu)` whenever $`u > -1`
(`CohnElkies.expL_stationary_eq`).
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
{uses "eq_56_first_branch_variance"}[] and {uses "eq_57_first_branch_third_moment"}[],
$`L \ge \tfrac14\log\lambda`, $`V(u) \asymp_\epsilon \eta^{-1}`,
$`M_3 \ll_\epsilon \eta^{-2}`. Choosing $`K = L^{1/12}`, so that $`K \to \infty` and
$`K^3 = o(\sqrt L)`,
gives $`T_*/\eta \ll_\epsilon L^{-5/12}` and
$`K^3M_3/(\sqrt\lambda V(u)^{3/2}) \ll_\epsilon L^{-1/4}`. The
damping bounds (55) and (53) ({uses "lemma_4_5"}[], {uses "eq_53_gamma_damping_lower"}[]) are
quadratic for $`|T| \le \eta` and linear for $`|T| \ge \eta`.
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
{uses "eq_66_second_branch_variance"}[],
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
For $`T_0 \le |T| \le \eta`, the variance bound (64) ({uses "eq_64_positive_shell_variance"}[])
and the damping estimate (68) give
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

:::theorem "cor_4_9" (lean := "CohnElkies.eventually_fPlus_re_pos_firstBranch, CohnElkies.eventually_fPlus_re_pos_secondBranch, CohnElkies.eventually_fPlus_nonneg_of_star, CohnElkies.eventually_fMinus_re_neg_of_radius, CohnElkies.eventually_fZero_re_pos_of_radius")
For every fixed $`0 < \epsilon < \epsilon_0` there is $`d_\epsilon` such that, for every integer
$`d \ge d_\epsilon`, with $`v` from {uses "eq_44_stationary_radius"}[] (equation (76)):
$`f_+(r) > 0` at every saddle radius $`r = e^{v(u)}`, $`u \ge u_*`, and $`f_+(r) \ge 0` for all
$`r \ge r_* = e^{v(u_*)}`; $`f_-(r) < 0` for $`r \ge R_{\epsilon,d} = e^{v(u_0)}`; and
$`f_0(r) > 0` for $`r \ge R_{\epsilon,d}`.
:::

:::proof "cor_4_9"
For $`u > -1` the prefactor of $`I_{\lambda,P_j}(u)` in (71) is positive, so (70) of
{uses "lemma_4_8"}[] identifies the sign of $`f_j(e^{v(u)})` with that of $`P_j(iu)` for all
sufficiently large $`d`, uniformly on the stated ranges of $`u`. Equations (56) and (63) of
{uses "eq_56_first_branch_variance"}[] and {uses "eq_66_second_branch_variance"}[] give
$`v'(u) = V(u) > 0` on $`[u_*,\infty)`, and (44) with the positive shell $`w_B` gives
$`v(u) \to \infty` as $`u \to \infty`. Thus $`[u_*,\infty)` parametrizes every radius
$`r \ge e^{v(u_*)}` and $`[u_0,\infty)` every radius $`r \ge e^{v(u_0)}`
({uses "lemma_saddle_radius_coverage"}[]). The signs in {uses "eq_39_polynomial_values"}[] now
give (76).
:::

:::lemma_ "lemma_saddle_radius_coverage" (lean := "CohnElkies.eventually_saddleLogRadius_covers_Ici, CohnElkies.logRadius_continuousOn_Ici")
For every sufficiently small $`\epsilon`, every $`d \ge 1` and every $`u_0 > -1`, the map
$`u \mapsto v(u)` of {uses "eq_44_stationary_radius"}[] is continuous on $`[u_0, \infty)` and
every radius $`r \ge e^{v(u_0)}` is attained: $`r = e^{v(u)}` for some $`u \ge u_0`.
:::

:::proof "lemma_saddle_radius_coverage"
Continuity of the digamma function on $`(0, \infty)` ({uses "def_digamma"}[]) and of the shell
integral, and $`v(u) \to \infty` as $`u \to \infty` (the positive shell makes
$`\int w(a)a\sinh(ua)\,da \to +\infty`, and $`\psi(\lambda(1+u)/2) \to \infty`); the intermediate
value theorem does the rest. The formalization only uses continuity of $`v` and its divergence,
not the strict monotonicity.
:::

# Positivity and the sharp upper bound

Corollary 4.9 proves the required signs outside the saddle radii. To finish the construction we
must also show $`f_+(r) > 0` for $`0 \le r \le r_* = e^{v(u_*)}`. Shifting the Mellin contour below
$`O(\log\lambda)` gamma poles expresses $`f_+(r)/f_+(0)` as a truncated exponential series plus a
uniformly negligible remainder.

:::definition "def_small_radius_expansion" (lean := "CohnElkies.r_star, CohnElkies.h₁', CohnElkies.y_r, CohnElkies.A_ℓn, CohnElkies.N_ℓ")
Fix $`0 < \epsilon < \epsilon_0`, let $`\lambda = d/2`, set $`r_* = e^{v(u_*)}`
({uses "eq_44_stationary_radius"}[], {uses "eq_43_saddle_parameters"}[]), and write
$`h_1' = \int_0^\infty w(a)\,a\sinh a\,da` ({uses "eq_35_positive_shell"}[]),
$`y = \pi e^{2h_1'}r^2` and $`N = \lceil\log\lambda\rceil`. The coefficients of the residue
expansion (41) are
$`A_{\lambda,n} = e^{\lambda[h_\epsilon(\zeta_n) - h_\epsilon(i)] - 2nh_1'}\,P_+(\zeta_n)/\beta`,
$`\zeta_n = -i(1+2n/\lambda)`.
:::

:::lemma_ "eq_78_residue_expansion" (lean := "CohnElkies.plusSaddleProfile_div_origin_eq_small_radius_residue_series")
With the notation of {uses "def_small_radius_expansion"}[], the residue expansion (41) of
{uses "lemma_4_3"}[] splits, for $`r > 0` and every $`N`,
$`\dfrac{f_+(r)}{f_+(0)} = \sum_{n=0}^N\dfrac{(-y)^n}{n!}A_{\lambda,n} + \mathcal{R}_{\lambda,N}(r)`
(equation (78)) into the sum over the first $`N + 1` poles and a remainder, the integral over
the contour $`t = s - i(\lambda + 2N + 1)`.
:::

:::proof "eq_78_residue_expansion"
Shift the Mellin contour of {uses "eq_38_profiles"}[] downward past the poles
$`t = -i(\lambda + 2n)`, $`0 \le n \le N`, and evaluate the residues by (41) and the origin value
(42) of {uses "lemma_4_3_origin"}[]; the justification of the shift is in the proof of
{uses "lemma_4_10"}[].
:::

:::lemma_ "lemma_4_10" (lean := "CohnElkies.eventually_plusSaddleSmallRadius_relativeFiniteResidue_lt_half_on_star, CohnElkies.eventually_plusSaddleTaylorRemainder_relative_lt_half_on_star, CohnElkies.eventually_plusSaddleProfile_re_pos_on_star")
With the notation of {uses "def_small_radius_expansion"}[] and {uses "eq_78_residue_expansion"}[],
for all sufficiently large $`d`, uniformly on $`0 \le r \le r_*`,
$`e^y\Bigl|\sum_{n=0}^N\dfrac{(-y)^n}{n!}A_{\lambda,n} - e^{-y}\Bigr| < \tfrac12` and
$`e^y|\mathcal{R}_{\lambda,N}(r)| < \tfrac12`.
In particular $`f_+(r) > 0` on $`[0, r_*]` for all sufficiently large $`d` (equation (82)).
:::

:::proof "lemma_4_10"
Range of $`y`. Put $`y = \pi e^{2h_1'}r^2`, $`H(u) = \int_0^\infty w(a)a\sinh(ua)\,da` (so
$`H(1) = h_1'`), and $`\eta_* = 1 + u_* = (\log\lambda)/(4\lambda)`. The height $`u_*` tends to
$`-1`, the normalized height of the first gamma pole, while the gamma shape parameter
$`\lambda\eta_*/2 = (\log\lambda)/8` still diverges; this makes (70) applicable and keeps $`y(r_*)`
logarithmic. Indeed $`H` is odd with bounded derivative near $`-1` (for fixed $`\epsilon`), so
$`H(u_*) + h_1' = H(-1+\eta_*) - H(-1) = O_\epsilon(\eta_*)`, and by (44)
$`y(r_*) = \exp\bigl(\psi(\lambda\eta_*/2) + 2H(u_*) + 2h_1'\bigr)`. The digamma asymptotic
$`\psi(x) \le \log x` ({uses "lemma_gamma_asymptotics"}[]) gives (equation (77))
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
$`e^{-\pi|s|/4}` (by {uses "eq_7_gamma_identities"}[]), so the integrand decays like
$`e^{-c\epsilon|s|}` on the vertical sides, permitting the shift of (38) to
$`t = s - i(\lambda+2p)`, which crosses exactly the poles $`t = -i(\lambda+2n)`, $`0 \le n \le N`.

Residue expansion. The residue formula (41) of {uses "lemma_4_3"}[] and the origin value (42) of {uses "lemma_4_3_origin"}[]
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
The gamma reflection and product estimates ({uses "eq_7_gamma_identities"}[]) with
$`p \in \mathbb{Z} + \tfrac12` give
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

:::lemma_ "eq_84_saddle_radius_limit" (lean := "CohnElkies.R_ε, CohnElkies.α_ε, CohnElkies.tendsto_saddleSourceRadius_normalized")
Set $`R_{\epsilon,d} = e^{v(u_0)}` with $`v` from {uses "eq_44_stationary_radius"}[]. For fixed
$`\epsilon` (equation (84)),
$`\lim_{d\to\infty}\dfrac{R_{\epsilon,d}}{\sqrt d}`
$`= \sqrt{\frac{1+u_0}{4\pi}}\exp\bigl(\int_0^\infty w(a)a\sinh(u_0a)\,da\bigr) =: \alpha_\epsilon`.
:::

:::proof "eq_84_saddle_radius_limit"
The saddle equation (44) and the digamma asymptotic
$`\psi(\lambda(1+u_0)/2) = \log(d(1+u_0)/4) + o(1)` ({uses "lemma_gamma_asymptotics"}[]).
:::

:::lemma_ "eq_85_critical_radius" (lean := "CohnElkies.tendsto_limitingSaddleRadius, CohnElkies.tendsto_limitingSaddleRadius_wallisIntegral")
With $`\alpha_\epsilon` from {uses "eq_84_saddle_radius_limit"}[] (equation (85)),
$`\lim_{\epsilon\downarrow0}\lim_{d\to\infty}R_{\epsilon,d}/\sqrt d`
$`= \lim_{\epsilon\downarrow0}\alpha_\epsilon = 1/\pi`.
:::

:::proof "eq_85_critical_radius"
The two shell contributions in {uses "lemma_4_2"}[] and {uses "lemma_4_2_positive_shell"}[] give
$`\int_0^\infty w(a)a\sinh(u_0a)\,da \to -\tfrac12\log\tfrac\pi2`. Since $`u_0 \to 1`,
{uses "eq_33_critical_radius"}[] gives the limit $`1/\pi`.
:::

:::proof "thm_4_1"
Set $`R_{\epsilon,d} = e^{v(u_0)}` ({uses "eq_84_saddle_radius_limit"}[]). The Fourier
identities and origin values are (40) and (42) of {uses "lemma_4_3_fourier"}[] and
{uses "lemma_4_3_origin"}[]. {uses "cor_4_9"}[] gives the required exterior signs, and (82) of
{uses "lemma_4_10"}[] supplies positivity of $`f_+` on the remaining interval $`[0, r_*]`. Thus
(equation (83))
$`\widehat{f_-} = f_+ > 0`, $`f_-(0) = f_+(0) > 0`, $`\widehat{f_0} = f_0`, $`f_0(0) = 0`,
$`f_-(r) < 0 < f_0(r)` for $`r \ge R_{\epsilon,d}`.
The limits (84) and (85) are {uses "eq_84_saddle_radius_limit"}[] and
{uses "eq_85_critical_radius"}[].
:::

:::theorem "thm_1_1_upper" (lean := "CohnElkies.saddleOrderedUpperConstruction")
There are $`\epsilon_0 > 0` and, for every $`0 < \epsilon < \epsilon_0`, radii
$`R_{\epsilon,d} > 0` with $`R_{\epsilon,d}/\sqrt d \to \alpha_\epsilon` as $`d \to \infty` and
$`\alpha_\epsilon \to 1/\pi` as $`\epsilon \downarrow 0`, such that for every
$`0 < \epsilon < \epsilon_0` and all sufficiently large $`d` there is $`F \in \mathcal{A}_d` with
$`(F(0)/\widehat F(0))^{1/d} \le R_{\epsilon,d}`. Consequently
$`\limsup_{d\to\infty}\mathrm{LP}_d^{1/d} \le \sqrt{e/(2\pi)}`, with $`\mathrm{LP}_d` from
{uses "def_lp"}[] (in the formalization the upper bound enters the sandwich argument
{bpref "thm_1_1_sandwich"}[] directly, without a separate $`\limsup` statement).
:::

:::proof "thm_1_1_upper"
Fix $`0 < \epsilon < \epsilon_0` and let $`d` be large. By (83) of {uses "thm_4_1"}[] and
{uses "lemma_upper_bound_reduction"}[], the dilation $`F_{\epsilon,d}(x) = f_-(R_{\epsilon,d}x)` is
admissible with $`F_{\epsilon,d}(0)/\widehat{F_{\epsilon,d}}(0) = R_{\epsilon,d}^d`, so (equation
(86))
$`\mathrm{LP}_d \le \dfrac{v_d}{2^d}R_{\epsilon,d}^d`, i.e.
$`\mathrm{LP}_d^{1/d} \le \dfrac{v_d^{1/d}\sqrt d}{2}\cdot\dfrac{R_{\epsilon,d}}{\sqrt d}`. By
{uses "lemma_stirling_ball_volume"}[] and (84) of {uses "eq_84_saddle_radius_limit"}[], the right
side tends to $`\tfrac12\sqrt{2\pi e}\,\alpha_\epsilon` as $`d \to \infty`. Hence
$`\limsup_d\mathrm{LP}_d^{1/d} \le \tfrac12\sqrt{2\pi e}\,\alpha_\epsilon` for every $`\epsilon`,
and letting $`\epsilon \downarrow 0` with (85) of {uses "eq_85_critical_radius"}[] gives $`\tfrac12\sqrt{2\pi e}/\pi = \sqrt{e/(2\pi)}`.
:::

:::theorem "thm_1_2_upper" (lean := "CohnElkies.eventually_signUncertaintyConstant_le, CohnElkies.eventually_signUncertaintyConstant_lt_top, CohnElkies.limsup_signUncertaintyConstant_div_sqrt_le")
For each $`\varsigma \in \{-1,+1\}`, $`\mathsf{A}_\varsigma(d) \le R_{\epsilon,d}`
({uses "def_sign_uncertainty_constant"}[], {uses "eq_84_saddle_radius_limit"}[]) for every
$`0 < \epsilon < \epsilon_0` and all sufficiently large $`d`; in particular
$`\mathsf{A}_\varsigma(d)` is finite for all sufficiently large $`d`, and
$`\limsup_{d\to\infty}\mathsf{A}_\varsigma(d)/\sqrt d \le 1/\pi`.
:::

:::proof "thm_1_2_upper"
Fix $`0 < \epsilon < \epsilon_0` and let $`d` be large. Define $`g_{\epsilon,d,-} = f_+ - f_-` and
$`g_{\epsilon,d,+} = f_0` with $`f_\pm, f_0` from {uses "thm_4_1"}[]. Equation (40) and Fourier
inversion give $`\widehat{g_{\epsilon,d,-}} = -g_{\epsilon,d,-}` and
$`\widehat{g_{\epsilon,d,+}} = g_{\epsilon,d,+}`. By (83) both vanish at the origin and are
strictly positive outside $`B(0,R_{\epsilon,d})`; in particular neither is zero. By
{uses "lemma_sign_uncertainty_reduction"}[], $`\mathsf{A}_\varsigma(d) \le R_{\epsilon,d} < \infty` for
both signs. Hence
$`\limsup_d\mathsf{A}_\varsigma(d)/\sqrt d \le \lim_d R_{\epsilon,d}/\sqrt d = \alpha_\epsilon`
by (84), and letting $`\epsilon \downarrow 0` with (85) of {uses "eq_85_critical_radius"}[] gives
$`1/\pi`.
:::
