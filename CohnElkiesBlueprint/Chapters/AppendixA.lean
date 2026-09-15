import Verso
import VersoManual
import VersoBlueprint
import CohnElkies

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Comparison of the sign-uncertainty constants" =>

This chapter follows Appendix A of the report. Proposition A.1 and the comparison
$`\mathsf{A}_+(d) \le \mathsf{A}_-(d)` are formalized in $`L^1` generality (modules
`CohnElkies.SignUncertainty.MellinCancellation`, `CohnElkies.SignUncertainty.TailIntegral`,
`CohnElkies.SignUncertainty.AppendixA`). The appendix's strict conclusion
$`\mathsf{A}_+(d) < \mathsf{A}_-(d)` needs, in addition, an extremizer attaining
$`\mathsf{A}_-(d)` (Cohn–Gonçalves 2019, Theorem 1.4), whose proof (weak compactness in $`L^2`,
Mazur's lemma, Fatou's lemma and a uniform negative-mass bound from Nazarov's uncertainty
principle in Jaming's form) is not part of the report; that assumption and the strict inequality
are the only nodes left informal, tagged `not-formalized`. The nodes depend on the definitions of
the introduction and on the radial reduction of the preliminaries.

For an anti-self-Fourier radial function $`g`, the central Mellin moment $`M_g(d/2)` vanishes.
Integrating the radial tail of $`g` therefore produces a self-Fourier function with a strictly
smaller last-sign radius. Throughout, $`d \ge 1`, $`\lambda = d/2`, and $`g` denotes the continuous
Fourier-inversion representative, as in {bpref "def_sign_eigenfunction_class"}[].

:::definition "eq_87_tail_integration" (lean := "CohnElkies.tailIntegral")
Let $`g \in \mathcal{E}_-(d)` ({uses "def_sign_eigenfunction_class"}[]) be radial, i.e.
$`0 \ne g \in L^1_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})` with $`\widehat g = -g` and $`g(0) = 0`.
Define $`T_dg(0) = 0` and, for $`x \ne 0` (equation (87)),
$`(T_dg)(x) = \dfrac{\lambda}{2}\int_1^\infty t^{\lambda-1}g(tx)\,dt`.
In terms of the radial profile,
$`(T_dg)(r) = \dfrac{\lambda}{2}r^{-\lambda}\int_r^\infty s^{\lambda-1}g(s)\,ds` for $`r > 0`
(large-scale representation).
:::

:::lemma_ "eq_88_central_mellin_cancellation" (lean := "CohnElkies.SignEigenfunction.integral_mul_norm_rpow_eq_zero")
Let $`g` be as in {uses "eq_87_tail_integration"}[]. Then $`g` is bounded and continuous,
$`\int_{\mathbb{R}^d}|g(x)||x|^{-\lambda}\,dx < \infty`, and the central Mellin moment vanishes
(equation (88)): $`M_g(\lambda) = \int_0^\infty g(r)\,r^{\lambda-1}\,dr = 0`, the integral
converging
absolutely.
:::

:::proof "eq_88_central_mellin_cancellation"
Since $`g = -\widehat g \in L^1`, Fourier inversion makes $`g` bounded and continuous
({uses "def_fourier_convention"}[]); splitting at $`|x| = 1` and using $`\lambda < d` gives the
finiteness of $`\int|g||x|^{-\lambda}`. The Mellin–Fourier identity (9) was established only for
Schwartz functions, so we verify its central consequence directly. Set
$`J(t) = \int_{\mathbb{R}^d}g(x)e^{-\pi t|x|^2}\,dx` for $`t > 0`. Gaussian duality
$`e^{-\pi t|x|^2} = t^{-\lambda}\widehat{e^{-\pi|\cdot|^2/t}}(x)`, the pairing
$`\int g\widehat\phi = \int\widehat g\phi`, and $`\widehat g = -g` give
$`J(t) = -t^{-\lambda}J(1/t)`.
Tonelli's theorem gives
$`\int_0^\infty t^{\lambda/2-1}|J(t)|\,dt`
$`\le \dfrac{\Gamma(\lambda/2)}{\pi^{\lambda/2}}\int_{\mathbb{R}^d}|g(x)||x|^{-\lambda}\,dx`
$`< \infty`.
Hence the substitution $`t \mapsto 1/t` makes $`\int_0^\infty t^{\lambda/2-1}J(t)\,dt` equal to its
own negative, so it vanishes. On the other hand, Fubini and Gaussian integration express the
same quantity as
$`\dfrac{\Gamma(\lambda/2)}{\pi^{\lambda/2}}\int_{\mathbb{R}^d}g(x)|x|^{-\lambda}\,dx`,
which in polar coordinates ({uses "def_sphere_area_polar"}[]) equals
$`\dfrac{\Gamma(\lambda/2)}{\pi^{\lambda/2}}S_d\int_0^\infty g(r)r^{\lambda-1}\,dr`. This proves
(88).
:::

:::lemma_ "eq_89_small_scale_representation" (lean := "CohnElkies.SignEigenfunction.tailIntegral_eq_neg_integral_Ioo")
Let $`g` be as in {uses "eq_87_tail_integration"}[]. The integral defining $`T_dg(x)` converges
absolutely for $`x \ne 0`, $`T_dg` is integrable with $`\|T_dg\|_1 \le \tfrac12\|g\|_1`, and
(equation (89))
$`\widehat{T_dg}(\xi) = \dfrac{\lambda}{2}\int_1^\infty t^{\lambda-d-1}\widehat g(\xi/t)\,dt`
$`= -\dfrac{\lambda}{2}\int_0^1s^{\lambda-1}g(s\xi)\,ds`,
which equals $`\dfrac{\lambda}{2}\int_1^\infty s^{\lambda-1}g(s\xi)\,ds = T_dg(\xi)` for every
$`\xi`. The small-scale representation $`-\tfrac\lambda2\int_0^1s^{\lambda-1}g(sx)\,ds` is
continuous on all of $`\mathbb{R}^d`, equals $`T_dg(x)` for $`x \ne 0`, and equals $`-g(0)/2 = 0` at
$`x = 0`. Hence $`T_dg` is continuous, radial, $`\widehat{T_dg} = T_dg`, and $`T_dg(0) = 0`.
:::

:::proof "eq_89_small_scale_representation"
For $`x \ne 0`, in the radial profile
$`\int_1^\infty t^{\lambda-1}|g(tx)|\,dt = |x|^{-\lambda}\int_{|x|}^\infty s^{\lambda-1}|g(s)|\,ds`,
and $`s^{\lambda-1} \le |x|^{-\lambda}s^{d-1}` for $`s \ge |x|`, so the integral is at most
$`|x|^{-d}\|g\|_1/S_d`: absolute convergence. Tonelli and $`d = 2\lambda` give
$`\|T_dg\|_1 \le \tfrac\lambda2\|g\|_1\int_1^\infty t^{-\lambda-1}\,dt = \tfrac12\|g\|_1`, which
also
justifies Fourier transformation under the integral. Fourier scaling
$`\widehat{g(t\,\cdot)}(\xi) = t^{-d}\widehat g(\xi/t)` and $`\widehat g = -g` give the first two
expressions in (89) after the substitution $`s = 1/t`. By
{uses "eq_88_central_mellin_cancellation"}[], for $`\xi \ne 0`,
$`\int_0^\infty s^{\lambda-1}g(s\xi)\,ds = |\xi|^{-\lambda}M_g(\lambda) = 0`, so
$`-\int_0^1 = \int_1^\infty`, giving $`\widehat{T_dg}(\xi) = T_dg(\xi)`; at $`\xi = 0` both sides
equal $`-g(0)/2 = 0`. Continuity of the small-scale representation follows from dominated
convergence, $`g` being bounded and continuous, and its value at $`0` is
$`-\tfrac\lambda2g(0)\int_0^1s^{\lambda-1}ds = -g(0)/2 = 0`.
:::

:::proposition "prop_a_1" (lean := "CohnElkies.SignEigenfunction.tailIntegral")
Let $`d \ge 1`, $`\lambda = d/2`, and let $`0 \ne g \in L^1_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})`
satisfy $`\widehat g = -g` and $`g(0) = 0`, with $`T_dg` as in {uses "eq_87_tail_integration"}[].
Then $`T_dg` is nonzero, continuous, radial and integrable, with
$`\widehat{T_dg} = T_dg`, $`T_dg(0) = 0`, $`\|T_dg\|_1 \le \tfrac12\|g\|_1`;
in particular $`T_dg \in \mathcal{E}_+(d)`. If $`r(g) < \infty` then $`r(T_dg) < r(g)`
({uses "def_sign_radius"}[]); if $`g` is Schwartz, so is $`T_dg`.
Formalized as the bundled eigenfunction `CohnElkies.SignEigenfunction.tailIntegral` (with
`CohnElkies.SignEigenfunction.continuous_tailIntegral`,
`CohnElkies.SignEigenfunction.integrable_tailIntegral`,
`CohnElkies.SignEigenfunction.integral_norm_tailIntegral_le`,
`CohnElkies.SignEigenfunction.fourier_tailIntegral`,
`CohnElkies.SignEigenfunction.tailIntegral_ne_zero`, `CohnElkies.IsRadial.tailIntegral`) and the
radius comparison `CohnElkies.SignEigenfunction.signRadius_tailIntegral_le` with its strict form
`CohnElkies.SignEigenfunction.signRadius_tailIntegral_lt`. The nonvanishing uses the compact-support
theorem `Real.ae_eq_zero_of_hasCompactSupport_fourierIntegral`
({uses "lemma_compactly_supported_eigenfunction_zero"}[]) through the positivity
`CohnElkies.SignEigenfunction.tailIntegral_pos` outside the ball of radius $`r(g)`. Schwartz
preservation is not formalized (it is not needed for the comparison).
:::

:::proof "prop_a_1"
Continuity, integrability, the norm bound, self-Fourier property and vanishing at the origin are
{uses "eq_89_small_scale_representation"}[]. Differentiating the large-scale representation of
{uses "eq_87_tail_integration"}[] in $`r` gives
$`(r\tfrac{d}{dr} + \lambda)T_dg = -\tfrac\lambda2g`,
i.e. $`(x\cdot\nabla + \lambda)T_dg = -\lambda g/2`; since $`g \ne 0`, also $`T_dg \ne 0`. If $`g`
is Schwartz, differentiating the small-scale representation gives smoothness at the origin, and
differentiating the large-scale representation gives rapid decay at infinity; thus $`T_dg` is
Schwartz.

Sign radius. Let $`R = r(g) < \infty`. Then $`R > 0`: otherwise $`g \ge 0` everywhere and
$`\int g = \widehat g(0) = -g(0) = 0` would force the continuous nonnegative $`g` to vanish. For
$`r \ge R` we have $`g(s) \ge 0` for all $`s \ge r`, so by (87)
$`(T_dg)(r) = \tfrac\lambda2r^{-\lambda}\int_r^\infty s^{\lambda-1}g(s)\,ds \ge 0`, and in fact
$`> 0`: equality would force $`g = 0` on $`[r,\infty)`, making both $`g` and $`\widehat g = -g`
compactly supported, which {uses "lemma_compactly_supported_eigenfunction_zero"}[] forbids. In
particular $`T_dg(R) > 0`, so by continuity $`T_dg > 0` on some $`[R - \delta, R]` with
$`\delta > 0`, hence $`T_dg \ge 0` on $`\{|x| \ge R - \delta\}` and $`r(T_dg) \le R - \delta < R`.
:::

:::theorem "assumption_cg19_extremizer" (tags := "not-formalized, external-input")
(External input; Cohn–Gonçalves 2019, Theorem 1.4.) For every $`d \ge 1`, the infimum defining
$`\mathsf{A}_-(d)` in {uses "def_sign_uncertainty_constant"}[] is finite and attained: there
exists $`g \in \mathcal{E}_-(d)` with $`r(g) = \mathsf{A}_-(d) < \infty`. This statement is not
proved in the report; it is recorded here as a hypothesis for {bpref "cor_a_plus_lt_a_minus"}[].
:::

:::proof "assumption_cg19_extremizer"
External input, not proved in the report or in this blueprint: the existence of an extremizer
for $`\mathsf{A}_-(d)` is Theorem 1.4 of Cohn and Gonçalves (2019), obtained from weak
compactness in $`L^2`, Mazur's lemma, Fatou's lemma and a uniform negative-mass bound derived
from Nazarov's uncertainty principle in Jaming's form.
:::

:::theorem "cor_a_plus_le_a_minus" (lean := "CohnElkies.signUncertaintyConstant_one_le_neg_one")
For every $`d \ge 1`, $`\mathsf{A}_+(d) \le \mathsf{A}_-(d)` (see
{uses "def_sign_uncertainty_constant"}[]). Formalized as
`CohnElkies.signUncertaintyConstant_one_le_neg_one`, in $`[0,\infty]`.
:::

:::proof "cor_a_plus_le_a_minus"
If $`\mathsf{A}_-(d) = \infty` there is nothing to prove. Otherwise let $`g \in \mathcal{E}_-(d)`
with $`r(g) < \infty`. By {uses "lemma_rotational_average_properties"}[] and
{uses "lemma_rotational_average_nonzero"}[] (applicable since $`g \ge 0` outside a ball),
$`h = \mathcal{R}g` is a nonzero radial element of $`\mathcal{E}_-(d)` with $`r(h) \le r(g)`. By
{uses "prop_a_1"}[], $`T_dh \in \mathcal{E}_+(d)` and $`r(T_dh) < r(h) \le r(g)`. Hence
$`\mathsf{A}_+(d) \le r(g)` for every such $`g`, and taking the infimum over $`g` gives the claim.
(In the formalization the infimum is first restricted to radial $`g` by
{uses "lemma_sign_uncertainty_radial_reduction"}[], and only $`r(T_dh) \le r(h)` is used; the strict
decrease is what an extremizer would turn into $`\mathsf{A}_+(d) < \mathsf{A}_-(d)`.)
:::

:::theorem "cor_a_plus_lt_a_minus" (tags := "not-formalized")
Let $`d \ge 1` and assume {uses "assumption_cg19_extremizer"}[] for this $`d`. Then
$`\mathsf{A}_+(d) < \mathsf{A}_-(d)`.
:::

:::proof "cor_a_plus_lt_a_minus"
Let $`g \in \mathcal{E}_-(d)` be an extremizer, $`r(g) = \mathsf{A}_-(d) < \infty`, and put
$`h = \mathcal{R}g`, a nonzero radial element of $`\mathcal{E}_-(d)` with $`r(h) \le r(g)`
({uses "lemma_rotational_average_properties"}[], {uses "lemma_rotational_average_nonzero"}[]).
By {uses "prop_a_1"}[], $`\mathsf{A}_+(d) \le r(T_dh) < r(h) \le r(g) = \mathsf{A}_-(d)`.
:::
