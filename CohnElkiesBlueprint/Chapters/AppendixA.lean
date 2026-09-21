import Verso
import VersoManual
import VersoBlueprint
import CohnElkies

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Comparison of the sign-uncertainty constants" =>

:::group "grp_appendix_a"
Comparison of the constants
:::

This chapter follows Appendix A of the report. Proposition A.1 is formalized in $`L^1`
generality (modules `CohnElkies.SignUncertainty.MellinCancellation`,
`CohnElkies.SignUncertainty.TailIntegral`, `CohnElkies.SignUncertainty.AppendixA`). The appendix's
conclusion $`\mathsf{A}_+(d) < \mathsf{A}_-(d)` needs, in addition, an extremizer attaining
$`\mathsf{A}_-(d)` (Cohn–Gonçalves 2019, Theorem 1.4), whose proof is not part of the report. The
second half of the chapter formalizes that existence theorem, following Cohn–Gonçalves (§3.2):
the origin correction of their Lemma 3.1, the positivity and finiteness of the constants in every
dimension, weak sequential compactness in $`L^2`, and — in place of the quantitative uncertainty
principle of Nazarov and Jaming they invoke — a qualitative "no concentration" lemma for
eigenfunctions of the Fourier transform, proved by compactness (modules
`CohnElkies.SignUncertainty.OriginCorrection`, `CohnElkies.SignUncertainty.Finiteness`,
`CohnElkies.SignUncertainty.AppendixA`,
`CohnElkiesForMathlib.Analysis.InnerProductSpace.WeakSequentialCompactness`,
`CohnElkiesForMathlib.Analysis.Fourier.EigenfunctionConcentration`). The nodes depend on the
definitions of the introduction and on the radial reduction of the preliminaries.

# Proposition A.1: the tail-integration operator

The tail-integration operator $`T_d` and the comparison $`\mathsf{A}_+(d) < \mathsf{A}_-(d)`
(Proposition A.1 of the report). For an anti-self-Fourier radial function $`g`, the central Mellin
moment $`M_g(d/2)` vanishes. Integrating the radial tail of $`g` therefore produces a self-Fourier
function with a strictly smaller last-sign radius; applied to a radial extremizer for
$`\mathsf{A}_-(d)`, whose existence is proved in the next section, this gives the strict
inequality. Throughout, $`d \ge 1`, $`\lambda = d/2`, and $`g` denotes the continuous
Fourier-inversion representative, as in {bpref "def_sign_eigenfunction_class"}[].

:::definition "eq_87_tail_integration" (lean := "CohnElkies.tailIntegral, CohnElkies.tailIntegral_of_ne_zero") (parent := "grp_appendix_a")
Let $`g \in \mathcal{E}_-(d)` ({uses "def_sign_eigenfunction_class"}[]) be radial, i.e.
$`0 \ne g \in L^1_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})` with $`\widehat g = -g` and $`g(0) = 0`.
Define $`T_dg(0) = 0` and, for $`x \ne 0` (equation (87)),
$`(T_dg)(x) = \dfrac{\lambda}{2}\int_1^\infty t^{\lambda-1}g(tx)\,dt`.
In terms of the radial profile,
$`(T_dg)(r) = \dfrac{\lambda}{2}r^{-\lambda}\int_r^\infty s^{\lambda-1}g(s)\,ds` for $`r > 0`
(large-scale representation).
:::

:::lemma_ "lemma_eigenfunction_bounded_weighted" (lean := "CohnElkies.SignEigenfunction.continuous, CohnElkies.SignEigenfunction.norm_apply_le, CohnElkies.integrable_mul_norm_rpow_neg_half") (parent := "grp_appendix_a")
Let $`g` be as in {uses "eq_87_tail_integration"}[]. Then $`g` is bounded and continuous, and
$`\int_{\mathbb{R}^d}|g(x)||x|^{-\lambda}\,dx < \infty`.
:::

:::proof "lemma_eigenfunction_bounded_weighted"
Since $`g = -\widehat g \in L^1`, Fourier inversion makes $`g` bounded and continuous
({uses "def_fourier_convention"}[]); splitting at $`|x| = 1` and using $`\lambda < d` gives the
finiteness of $`\int|g||x|^{-\lambda}`.
:::

:::lemma_ "eq_88_central_mellin_cancellation" (lean := "CohnElkies.SignEigenfunction.integral_mul_norm_rpow_eq_zero") (parent := "grp_appendix_a")
Let $`g` be as in {uses "eq_87_tail_integration"}[]. Then the central Mellin moment vanishes
(equation (88)): $`\int_{\mathbb{R}^d}g(x)|x|^{-\lambda}\,dx = 0`, i.e.
$`M_g(\lambda) = \int_0^\infty g(r)\,r^{\lambda-1}\,dr = 0`, the integrals converging absolutely
by {uses "lemma_eigenfunction_bounded_weighted"}[].
:::

:::proof "eq_88_central_mellin_cancellation"
The Mellin–Fourier identity (9) was established only for
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
which in polar coordinates ({uses "lemma_polar_integration"}[]) equals
$`\dfrac{\Gamma(\lambda/2)}{\pi^{\lambda/2}}S_d\int_0^\infty g(r)r^{\lambda-1}\,dr`. This proves
(88).
:::

:::lemma_ "lemma_tail_integral_integrable" (lean := "CohnElkies.SignEigenfunction.integrable_tailIntegral_kernel, CohnElkies.SignEigenfunction.integrable_tailIntegral, CohnElkies.SignEigenfunction.integral_norm_tailIntegral_le") (parent := "grp_appendix_a")
Let $`g` be as in {uses "eq_87_tail_integration"}[]. The integral defining $`T_dg(x)` converges
absolutely for $`x \ne 0`, and $`T_dg` is integrable with $`\|T_dg\|_1 \le \tfrac12\|g\|_1`.
:::

:::proof "lemma_tail_integral_integrable"
For $`x \ne 0`, in the radial profile
$`\int_1^\infty t^{\lambda-1}|g(tx)|\,dt = |x|^{-\lambda}\int_{|x|}^\infty s^{\lambda-1}|g(s)|\,ds`,
and $`s^{\lambda-1} \le |x|^{-\lambda}s^{d-1}` for $`s \ge |x|`, so the integral is at most
$`|x|^{-d}\|g\|_1/S_d`: absolute convergence. Tonelli and $`d = 2\lambda` give
$`\|T_dg\|_1 \le \tfrac\lambda2\|g\|_1\int_1^\infty t^{-\lambda-1}\,dt = \tfrac12\|g\|_1`.
:::

:::lemma_ "eq_89_small_scale_representation" (lean := "CohnElkies.SignEigenfunction.tailIntegral_eq_neg_integral_Ioo, CohnElkies.SignEigenfunction.continuous_tailIntegral") (parent := "grp_appendix_a")
Let $`g` be as in {uses "eq_87_tail_integration"}[]. For every $`x`,
$`T_dg(x) = -\dfrac{\lambda}{2}\int_0^1s^{\lambda-1}g(sx)\,ds` (small-scale representation,
equation (89)); this representation is continuous on all of $`\mathbb{R}^d` and equals
$`-g(0)/2 = 0` at $`x = 0`. Hence $`T_dg` is continuous and radial with $`T_dg(0) = 0`.
:::

:::proof "eq_89_small_scale_representation"
By {uses "eq_88_central_mellin_cancellation"}[], for $`x \ne 0`,
$`\int_0^\infty s^{\lambda-1}g(sx)\,ds = |x|^{-\lambda}M_g(\lambda) = 0`, so
$`-\int_0^1 = \int_1^\infty`; at $`x = 0` both sides vanish. Continuity of the small-scale
representation follows from dominated convergence, $`g` being bounded and continuous
({uses "lemma_eigenfunction_bounded_weighted"}[]), and its value at $`0` is
$`-\tfrac\lambda2g(0)\int_0^1s^{\lambda-1}ds = -g(0)/2 = 0`.
:::

:::lemma_ "eq_89_self_fourier" (lean := "CohnElkies.SignEigenfunction.fourier_tailIntegral") (parent := "grp_appendix_a")
Let $`g` be as in {uses "eq_87_tail_integration"}[]. Then (equation (89))
$`\widehat{T_dg}(\xi) = \dfrac{\lambda}{2}\int_1^\infty t^{\lambda-d-1}\widehat g(\xi/t)\,dt`
$`= -\dfrac{\lambda}{2}\int_0^1s^{\lambda-1}g(s\xi)\,ds = T_dg(\xi)`
for every $`\xi`: $`\widehat{T_dg} = T_dg`.
:::

:::proof "eq_89_self_fourier"
The absolute convergence of {uses "lemma_tail_integral_integrable"}[] justifies Fourier
transformation under the integral. Fourier scaling
$`\widehat{g(t\,\cdot)}(\xi) = t^{-d}\widehat g(\xi/t)` and $`\widehat g = -g` give the first two
expressions after the substitution $`s = 1/t`, and {uses "eq_89_small_scale_representation"}[]
identifies the last one with $`T_dg(\xi)`.
:::

:::proposition "prop_a_1" (lean := "CohnElkies.SignEigenfunction.tailIntegral, CohnElkies.SignEigenfunction.tailIntegral_ne_zero") (parent := "grp_appendix_a")
Let $`d \ge 1`, $`\lambda = d/2`, and let $`0 \ne g \in L^1_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})`
satisfy $`\widehat g = -g` and $`g(0) = 0`, with $`T_dg` as in {uses "eq_87_tail_integration"}[].
Then $`T_dg` is nonzero, continuous, radial and integrable, with
$`\widehat{T_dg} = T_dg`, $`T_dg(0) = 0`, $`\|T_dg\|_1 \le \tfrac12\|g\|_1`;
in particular $`T_dg \in \mathcal{E}_+(d)`.
:::

:::proof "prop_a_1"
Continuity and vanishing at the origin are {uses "eq_89_small_scale_representation"}[],
integrability and the norm bound {uses "lemma_tail_integral_integrable"}[], and the
self-Fourier property {uses "eq_89_self_fourier"}[]. Differentiating the large-scale representation of
{uses "eq_87_tail_integration"}[] in $`r` gives
$`(r\tfrac{d}{dr} + \lambda)T_dg = -\tfrac\lambda2g`,
i.e. $`(x\cdot\nabla + \lambda)T_dg = -\lambda g/2`; since $`g \ne 0`, also $`T_dg \ne 0`. If $`g`
is Schwartz, differentiating the small-scale representation gives smoothness at the origin, and
differentiating the large-scale representation gives rapid decay at infinity; thus $`T_dg` is
Schwartz.
:::

:::proposition "prop_a_1_sign_radius" (lean := "CohnElkies.SignEigenfunction.tailIntegral_pos, CohnElkies.SignEigenfunction.signRadius_tailIntegral_le, CohnElkies.SignEigenfunction.signRadius_tailIntegral_lt") (parent := "grp_appendix_a")
In the situation of {uses "prop_a_1"}[], $`r(T_dg) \le r(g)`, and if $`r(g) < \infty` then
$`T_dg > 0` on $`\{|x| \ge r(g)\}` and $`r(T_dg) < r(g)` ({uses "def_sign_radius"}[]).
:::

:::proof "prop_a_1_sign_radius"
Let $`R = r(g) < \infty`. Then $`R > 0`: otherwise $`g \ge 0` everywhere and
$`\int g = \widehat g(0) = -g(0) = 0` would force the continuous nonnegative $`g` to vanish. For
$`r \ge R` we have $`g(s) \ge 0` for all $`s \ge r`, so by (87)
$`(T_dg)(r) = \tfrac\lambda2r^{-\lambda}\int_r^\infty s^{\lambda-1}g(s)\,ds \ge 0`, and in fact
$`> 0`: equality would force $`g = 0` on $`[r,\infty)`, making both $`g` and $`\widehat g = -g`
compactly supported, which {uses "lemma_compactly_supported_eigenfunction_zero"}[] forbids. In
particular $`T_dg(R) > 0`, so by continuity $`T_dg > 0` on some $`[R - \delta, R]` with
$`\delta > 0`, hence $`T_dg \ge 0` on $`\{|x| \ge R - \delta\}` and $`r(T_dg) \le R - \delta < R`.
:::

:::theorem "cor_a_plus_lt_a_minus" (lean := "CohnElkies.signUncertaintyConstant_one_lt_neg_one") (parent := "grp_appendix_a")
For every $`d \ge 1`, $`\mathsf{A}_+(d) < \mathsf{A}_-(d)` ({uses "def_sign_uncertainty_constant"}[]).
:::

:::proof "cor_a_plus_lt_a_minus"
By {uses "thm_cg19_1_4_existence"}[] there is an extremizer $`g \in \mathcal{E}_-(d)`,
$`r(g) = \mathsf{A}_-(d) < \infty` ({uses "lemma_sign_uncertainty_constant_neg_one_lt_top"}[]). Put
$`h = \mathcal{R}g`, a nonzero radial element of $`\mathcal{E}_-(d)` with $`r(h) \le r(g)`
({uses "lemma_rotational_average_eigenfunction"}[], {uses "lemma_rotational_average_signs"}[]).
By {uses "prop_a_1"}[] and {uses "prop_a_1_sign_radius"}[],
$`\mathsf{A}_+(d) \le r(T_dh) < r(h) \le r(g) = \mathsf{A}_-(d)`.
:::

:::theorem "cor_sign_uncertainty_constant_lt_top" (lean := "CohnElkies.signUncertaintyConstant_lt_top, CohnElkies.signUncertaintyConstant_pos_lt_top") (parent := "grp_appendix_a")
For every $`d \ge 1` and $`\varsigma = \pm 1`, $`\mathsf{A}_\varsigma(d) < \infty`
({uses "def_sign_uncertainty_constant"}[]); together with
{uses "lemma_sign_uncertainty_constant_pos"}[], $`0 < \mathsf{A}_\varsigma(d) < \infty`.
:::

:::proof "cor_sign_uncertainty_constant_lt_top"
$`\mathsf{A}_+(d) < \mathsf{A}_-(d) < \infty` by {uses "cor_a_plus_lt_a_minus"}[] and
{uses "lemma_sign_uncertainty_constant_neg_one_lt_top"}[].
:::

# Existence of extremizers

The existence part of Theorem 1.4 of Cohn–Gonçalves (2019), used in
{bpref "cor_a_plus_lt_a_minus"}[], following their §3.2 with the modifications described at the
beginning of the chapter.

:::definition "def_cg19_gaussian_difference" (lean := "CohnElkies.gaussianDifference") (parent := "grp_appendix_a")
(Cohn–Gonçalves 2019, (3.1).) For $`t > 0` let
$`\varphi_t(x) = \dfrac{e^{-t\pi|x|^2} - e^{-2t\pi|x|^2}}{t^{-d/2} - (2t)^{-d/2}}`.
:::

:::definition "def_cg19_gaussian_perturbation" (lean := "CohnElkies.gaussianPerturbation") (parent := "grp_appendix_a")
With $`\varphi_t` as in {uses "def_cg19_gaussian_difference"}[], let
$`\psi_t = \varphi_t - \widehat{\varphi_t}`.
:::

:::lemma_ "lemma_cg19_gaussian_difference_properties" (lean := "CohnElkies.fourier_gaussianDifference, CohnElkies.gaussianDifference_nonneg, CohnElkies.gaussianDifference_apply_zero, CohnElkies.fourier_gaussianDifference_zero, CohnElkies.fourier_fourier_gaussianDifference, CohnElkies.fourierGaussianDifference_neg_of_lt") (parent := "grp_appendix_a")
Let $`d \ge 1` and $`t > 0`, with $`\varphi_t` as in {uses "def_cg19_gaussian_difference"}[].
Then
$`\widehat{\varphi_t}(\xi) = \dfrac{t^{-d/2}e^{-\pi|\xi|^2/t} - (2t)^{-d/2}e^{-\pi|\xi|^2/(2t)}}{t^{-d/2} - (2t)^{-d/2}}`,
$`\varphi_t \ge 0`, $`\varphi_t(0) = 0`, $`\widehat{\varphi_t}(0) = 1`,
$`\widehat{\widehat{\varphi_t}} = \varphi_t`, and $`\widehat{\varphi_t}(\xi) < 0` whenever
$`|\xi|^2 > t\,d\log 2/\pi` (nonpositive when $`\ge`).
:::

:::proof "lemma_cg19_gaussian_difference_properties"
The Fourier transform of $`e^{-b\pi|x|^2}` is $`b^{-d/2}e^{-\pi|\xi|^2/b}`, which gives the formula;
taking logarithms, $`t^{-d/2}e^{-\pi|\xi|^2/t} < (2t)^{-d/2}e^{-\pi|\xi|^2/(2t)}` if and only
if $`\pi|\xi|^2/(2t) > (d/2)\log 2`, i.e. $`|\xi|^2 > t\,d\log 2/\pi`. Applying the transform
formula twice gives $`\widehat{\widehat{\varphi_t}} = \varphi_t`.
:::

:::lemma_ "lemma_cg19_gaussian_perturbation_properties" (lean := "CohnElkies.fourier_gaussianPerturbation, CohnElkies.gaussianPerturbation_apply_zero, CohnElkies.gaussianPerturbation_pos") (parent := "grp_appendix_a")
Let $`d \ge 1` and $`t > 0`, with $`\psi_t` as in {uses "def_cg19_gaussian_perturbation"}[].
Then $`\widehat{\psi_t} = -\psi_t`, $`\psi_t(0) = -1`, and $`\psi_t > 0` outside the ball of
radius $`\sqrt{t\,d\log 2/\pi}`.
:::

:::proof "lemma_cg19_gaussian_perturbation_properties"
Immediate from {uses "lemma_cg19_gaussian_difference_properties"}[]:
$`\widehat{\psi_t} = \widehat{\varphi_t} - \varphi_t = -\psi_t`,
$`\psi_t(0) = 0 - 1`, and $`\psi_t = \varphi_t - \widehat{\varphi_t} > 0` where
$`\widehat{\varphi_t} < 0`.
:::

:::lemma_ "lemma_cg19_3_1_origin_correction" (lean := "CohnElkies.originCorrection, CohnElkies.originCorrection_nonneg_outside, CohnElkies.originCorrection_eq_of_zero") (parent := "grp_appendix_a")
(Cohn–Gonçalves 2019, Lemma 3.1, last paragraph.) Let $`d \ge 1`, $`R > 0`, and let
$`g \in L^1(\mathbb{R}^d;\mathbb{R})` satisfy $`\widehat g = -g` pointwise, $`g \ne 0`,
$`g \ge 0` on $`\{|x| \ge R\}` and $`g(0) \ge 0`. With $`t = \pi R^2/(d\log 2)` and $`\psi_t` as in
{uses "def_cg19_gaussian_perturbation"}[], the function $`h = g + g(0)\psi_t` belongs to
$`\mathcal{E}_-(d)` ({uses "def_sign_eigenfunction_class"}[]) and satisfies $`h \ge 0` on
$`\{|x| \ge R\}`, so $`r(h) \le R`; moreover $`h = g` if $`g(0) = 0`.
:::

:::proof "lemma_cg19_3_1_origin_correction"
By {uses "lemma_cg19_gaussian_perturbation_properties"}[], $`\widehat h = -g + g(0)(-\psi_t) = -h`,
$`h(0) = g(0) + g(0)\psi_t(0) = 0`, and for $`|x| \ge R` one has $`|x|^2 \ge t\,d\log 2/\pi`, so
$`\psi_t(x) \ge 0` and $`h(x) \ge g(x) \ge 0`. If $`g(0) > 0` then $`h(x) > g(x) \ge 0` for
$`|x| > R`, so $`h \ne 0`; if $`g(0) = 0` then $`h = g \ne 0`.
:::

:::lemma_ "lemma_sign_uncertainty_constant_pos" (lean := "CohnElkies.signUncertaintyConstant_pos") (parent := "grp_appendix_a")
For every $`d \ge 1` and $`\varsigma = \pm 1`, $`\mathsf{A}_\varsigma(d) > 0`
({uses "def_sign_uncertainty_constant"}[]).
:::

:::proof "lemma_sign_uncertainty_constant_pos"
(Cohn–Gonçalves 2019, §3.1.) If $`g \in \mathcal{E}_\varsigma(d)` with $`\|g\|_1 = 1` is
nonnegative outside $`B_\rho`, then $`\int g = \widehat g(0) = \varsigma g(0) = 0` gives
$`\int g_- = \tfrac12`, while $`g_- \le |g| \le \|\widehat g\|_1 = 1` vanishes outside $`B_\rho`,
so $`\tfrac12 \le \operatorname{vol}(B_\rho)`; choosing $`\rho` with
$`\operatorname{vol}(B_\rho) < \tfrac12` shows $`\mathsf{A}_\varsigma(d) \ge \rho > 0`.
:::

:::lemma_ "lemma_explicit_eigenfunction" (lean := "CohnElkies.explicitSignEigenfunction, CohnElkies.explicitEigenfunction_pos_of_le, CohnElkies.signRadius_explicitSignEigenfunction_lt_top") (parent := "grp_appendix_a")
For every $`d \ge 1`, with $`\psi_t` as in {uses "def_cg19_gaussian_perturbation"}[],
$`G = \psi_{1/4} - \psi_{1/2}` belongs to $`\mathcal{E}_-(d)` and is positive outside a ball, so
$`r(G) < \infty`.
:::

:::proof "lemma_explicit_eigenfunction"
$`G` satisfies $`\widehat G = -G` and $`G(0) = -1 - (-1) = 0`
({uses "lemma_cg19_gaussian_perturbation_properties"}[]). Writing $`E_b(x) = e^{-\pi b|x|^2}`,
$`D = 2^d - 2^{d/2}`, $`D' = 2^{d/2} - 1`,
$`\psi_{1/4} = (E_{1/4} - E_{1/2} - 2^dE_4 + 2^{d/2}E_2)/D` and $`\psi_{1/2} = (E_{1/2} - 2^{d/2}E_2)/D'`,
so that $`G \ge E_{1/4}\bigl(1 - e^{-\pi|x|^2/4}(1 + D/D' + 2^d)\bigr)/D > 0` once
$`|x|^2 > (4/\pi)\log(1 + D/D' + 2^d)`; hence $`G \ne 0` and $`G \in \mathcal{E}_-(d)`.
:::

:::lemma_ "lemma_sign_uncertainty_constant_neg_one_lt_top" (lean := "CohnElkies.signUncertaintyConstant_neg_one_lt_top") (parent := "grp_appendix_a")
For every $`d \ge 1`, $`\mathsf{A}_-(d) < \infty` ({uses "def_sign_uncertainty_constant"}[]).
:::

:::proof "lemma_sign_uncertainty_constant_neg_one_lt_top"
$`\mathsf{A}_-(d) \le r(G) < \infty` for the explicit $`G` of {uses "lemma_explicit_eigenfunction"}[].
:::

:::lemma_ "lemma_weak_sequential_compactness" (lean := "InnerProductSpace.tendsto_subseq_inner_left_of_norm_le") (parent := "grp_appendix_a")
Every bounded sequence $`(x_n)` in a separable Hilbert space $`E` has a weakly convergent
subsequence: there are $`\varphi` strictly increasing and $`y \in E` with
$`\|y\| \le \sup_n\|x_n\|` and $`\langle x_{\varphi(n)}, z\rangle \to \langle y, z\rangle` for
every $`z \in E`.
:::

:::proof "lemma_weak_sequential_compactness"
By the Fréchet–Riesz theorem the functionals $`\langle x_n, \cdot\rangle` lie in a closed ball of
the dual $`E^*`, which is weak-star sequentially compact for separable $`E` (sequential
Banach–Alaoglu, Mathlib's `WeakDual.isSeqCompact_closedBall`); transporting the limit functional
back along the Riesz isometry gives $`y`.
:::

:::lemma_ "lemma_fourier_eigenfunction_no_concentration" (lean := "Real.exists_pos_le_setIntegral_norm_compl_closedBall_of_fourier_eq_mul") (parent := "grp_appendix_a")
Let $`V` be a nontrivial finite-dimensional real inner product space, $`c \in \mathbb{C}\setminus\{0\}`
and $`R \ge 0`. There is $`\kappa > 0` such that every integrable $`f : V \to \mathbb{C}` with
$`\widehat f = cf` pointwise and $`\|f\|_1 = 1` satisfies $`\int_{|x| > R}|f| \ge \kappa`.
:::

:::proof "lemma_fourier_eigenfunction_no_concentration"
Suppose not: there are such $`f_n` with $`\delta_n = \int_{B^c}|f_n| \to 0`, $`B` the closed ball of
radius $`R`. Each $`f_n = c^{-1}\widehat{f_n}` is continuous with $`|f_n| \le |c|^{-1}`. The
truncations $`1_Bf_n` are bounded in $`L^2`, so by {uses "lemma_weak_sequential_compactness"}[]
a subsequence converges weakly to some $`g \in L^2`; testing against the kernels
$`1_B(x)e^{2\pi i\langle x,\xi\rangle}` shows $`\widehat{1_Bf_n}(\xi) \to \widehat{1_Bg}(\xi)` for
every $`\xi`, and $`|\widehat{f_n} - \widehat{1_Bf_n}| \le \delta_n`, so $`f_n \to G := c^{-1}\widehat{1_Bg}`
pointwise, with $`G` continuous. Bounded convergence on $`B` gives
$`\int_B|G| = \lim(1 - \delta_n) = 1`; Fatou on $`B^c` gives $`G = 0` a.e., hence everywhere, off
$`B`; and bounded convergence on $`B` again gives
$`\widehat G(\xi) = \lim\int_B e^{-2\pi i\langle x,\xi\rangle}f_n = \lim(\widehat{f_n}(\xi) + O(\delta_n)) = cG(\xi)`.
Thus $`G` and $`\widehat G` are compactly supported and $`G \ne 0`, contradicting
{uses "lemma_compactly_supported_eigenfunction_zero"}[].
:::

:::theorem "thm_cg19_1_4_existence" (lean := "CohnElkies.exists_signRadius_eq_signUncertaintyConstant_neg_one") (parent := "grp_appendix_a")
(Cohn–Gonçalves 2019, Theorem 1.4, existence part.) For every $`d \ge 1` there exists
$`g \in \mathcal{E}_-(d)` with $`r(g) = \mathsf{A}_-(d)` ({uses "def_sign_uncertainty_constant"}[]).
:::

:::proof "thm_cg19_1_4_existence"
By {uses "lemma_sign_uncertainty_constant_pos"}[] and
{uses "lemma_sign_uncertainty_constant_neg_one_lt_top"}[], $`0 < a := \mathsf{A}_-(d) < \infty`.
Pick $`f_n \in \mathcal{E}_-(d)` with $`r(f_n) \le a + 1/(n+1)`, normalized so that
$`\|f_n\|_1 = 1`; then $`|f_n| = |\widehat{f_n}| \le 1`, $`\int f_n = 0`, and $`f_n \ge 0` on
$`\{|x| \ge a + 1/(n+1)\}`. By {uses "lemma_fourier_eigenfunction_no_concentration"}[] with
$`R = a + 1` there is $`\kappa > 0` with $`\int_{|x| \le a+1} f_n = -\int_{|x| > a+1} f_n \le -\kappa`
for all $`n`. Since $`\|f_n\|_2^2 \le \|f_n\|_\infty\|f_n\|_1 \le 1`,
{uses "lemma_weak_sequential_compactness"}[] gives a subsequence converging weakly in $`L^2` to
some $`g`. Testing the weak convergence against bounded compactly supported functions shows:
$`g \in L^1` with $`\int_K|g| \le 1` for every compact $`K` (test with $`1_K\operatorname{sign} g`);
$`\int_{|x| \le a+1} g \le -\kappa`, so $`g \ne 0`; $`\int_K g \le 0` for all balls $`K \supseteq B_{a+1}`,
hence $`\int g \le 0`; and $`g \ge 0` a.e. on $`\{|x| > a\}` (test with indicators of
$`\{a + 1/(m+1) \le |x| \le m+1\} \cap \{g < 0\}`). Testing against Schwartz functions $`\Phi` and
using $`\int\widehat u\,\Phi = \int u\,\widehat\Phi` for $`u \in L^1` yields
$`\int(\widehat g + g)\Phi = 0` for all smooth compactly supported $`\Phi`, so $`\widehat g = -g`
a.e. The continuous function $`G = -\widehat g` therefore satisfies $`G = g` a.e., $`\widehat G = -G`
pointwise, $`G \ne 0`, $`G(0) = -\int g \ge 0`, and $`G \ge 0` on $`\{|x| \ge a\}` (a.e. on the open
exterior, hence everywhere by continuity). Finally {uses "lemma_cg19_3_1_origin_correction"}[]
with $`R = a` produces $`h \in \mathcal{E}_-(d)` with $`r(h) \le a`, and $`r(h) \ge \mathsf{A}_-(d) = a`
by definition of the infimum.

This differs from the proof of Cohn–Gonçalves in three places: their uniform negative-mass bound
$`\int_{B} f_n \le K < 0` is deduced from Nazarov's uncertainty principle in Jaming's form (or
from the Amrein–Berthier inequality), here from the compactness lemma
{uses "lemma_fourier_eigenfunction_no_concentration"}[]; they pass from weak to almost-everywhere
and $`L^2` convergence by Mazur's lemma before applying Fatou's lemma, whereas here the weak limit is
only tested against explicit $`L^2` and smooth compactly supported functions; and they normalize
the minimizing sequence by their Lemma 3.1 and infer $`f(0) = 0` for the limit from minimality,
whereas here every element of $`\mathcal{E}_-(d)` already has $`\widehat g = -g` and $`g(0) = 0`,
and the origin correction is applied once, to the limit.
:::
