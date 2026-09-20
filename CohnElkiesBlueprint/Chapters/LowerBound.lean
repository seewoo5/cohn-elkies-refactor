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
proved, as in the report, by mapping the strip onto the upper half-plane and applying the
Poisson principle for subharmonic functions (the preliminaries chapter), and the limit of Lemma
3.4 by a Frullani-type computation recorded in the final chapter, which also contains an
alternative proof of the Poisson principle for the strip by Phragmén–Lindelöf.

# The Mellin-strip obstruction

:::definition "def_log_profile" (lean := "CohnElkies.φ_g")
Fix $`0 < c < 1/\pi`, $`d \in \mathbb{N}`, $`\lambda = d/2`, $`R = c\sqrt d`, and a nonzero
$`g \in \mathcal{S}_{\mathrm{rad}}(\mathbb{R}^d;\mathbb{R})` with $`\widehat g = \varsigma g`,
$`\varsigma \in \{-1,+1\}`, and $`g(0) = 0`. With $`S_d` from {uses "def_sphere_area"}[],
define in the logarithmic coordinate $`r = Re^v` the normalized profile (equation (12))
$`\varphi(v) = \dfrac{S_d}{\|g\|_1}\,(Re^v)^d\,g(Re^v)`.
:::

:::definition "def_normalized_profile" (lean := "CohnElkies.Z_g")
In the setting of {uses "def_log_profile"}[], with $`X_g` from {uses "def_radial_mellin"}[], the
normalized Mellin transform is (equation (12))
$`Z(t) = \dfrac{S_d}{\|g\|_1}\,R^{\lambda+it}\,X_g(t)`
(for complex $`t` as well, through the Mellin transform of the profile, `CohnElkies.X_f`).
:::

:::lemma_ "eq_13_normalization" (lean := "CohnElkies.RadialEigenfunction.integral_abs_logProfile")
In the setting of {uses "def_log_profile"}[] (equation (13)), $`\|\varphi\|_1 = 1`.
:::

:::proof "eq_13_normalization"
Polar integration ({uses "lemma_polar_integration"}[]) with $`r = Re^v`, $`dr = r\,dv`, gives
$`\int|\varphi| = \frac{S_d}{\|g\|_1}\int_0^\infty |g(r)|r^{d-1}\,dr = 1`.
:::

:::lemma_ "eq_13_mean_zero" (lean := "CohnElkies.RadialEigenfunction.integral_logProfile")
In the setting of {uses "def_log_profile"}[] (equation (13)), $`\int_{\mathbb{R}}\varphi = 0`.
:::

:::proof "eq_13_mean_zero"
As in {uses "eq_13_normalization"}[], polar integration gives
$`\int\varphi = \widehat g(0)/\|g\|_1 = \varsigma g(0)/\|g\|_1 = 0`.
:::

:::lemma_ "eq_13_interior_mass" (lean := "CohnElkies.RadialEigenfunction.setIntegral_Iic_abs_logProfile")
In the setting of {uses "def_log_profile"}[] (equation (13)),
$`\int_{-\infty}^0|\varphi(v)|\,dv = \dfrac{1}{\|g\|_1}\int_{|x|<R}|g(x)|\,dx`.
:::

:::proof "eq_13_interior_mass"
The substitution $`r = Re^v` of {uses "eq_13_normalization"}[], where $`v < 0` corresponds to
$`r < R`.
:::

:::lemma_ "eq_13_mellin_fourier" (lean := "CohnElkies.normalizedRadialMellinStrip_shifted_eq_fourier")
In the setting of {uses "def_normalized_profile"}[] (equation (13)),
$`Z(t) = \int_{\mathbb{R}}\varphi(v)e^{-(\lambda+it)v}\,dv` for every complex $`t` for which the
integral converges absolutely, in particular for real $`t`: on the horizontal line
$`\operatorname{Im} t = \lambda - a` of the strip, $`Z` is the Fourier transform of the weighted
profile $`v \mapsto e^{-av}\varphi(v)`.
:::

:::proof "eq_13_mellin_fourier"
The substitution $`r = Re^v` in $`X_g(t) = \int_0^\infty g(r)r^{\lambda-it-1}\,dr`.
:::

:::group "grp_mellin_strip"
Mellin-strip estimates
:::

The strip estimates for the normalized Mellin transform $`Z` (Lemmas 3.2–3.6 of the report).

:::definition "def_lower_boundary_majorant" (lean := "CohnElkies.h_ℓ") (parent := "grp_mellin_strip")
The lower-boundary majorant is (equation (14)), for $`y \ne 0`,
$`h_\lambda(y) = \lambda\log(\pi R^2) + \log|\Gamma(-iy/2)| - \log|\Gamma(\lambda + iy/2)|`.
:::

:::definition "def_strip_poisson_kernel" (lean := "CohnElkies.P_σ, CohnElkies.θ") (parent := "grp_mellin_strip")
For $`-1 < \sigma < 1` write $`\theta = \pi(1+\sigma)/2 \in (0,\pi)` and define the strip Poisson
kernel (equation (15))
$`P_\sigma(T) = \dfrac{\sin\theta}{4(\cosh(\pi T/2) - \cos\theta)}`.
:::

:::lemma_ "lemma_strip_poisson_kernel_properties" (lean := "CohnElkies.stripPoissonKernel_pos, CohnElkies.stripPoissonKernel_neg, CohnElkies.stripPoissonKernel_antitone_abs, CohnElkies.integral_stripPoissonKernel, CohnElkies.stripPoissonKernel_le_mass_mul_exponential") (parent := "grp_mellin_strip")
For $`-1 < \sigma < 1` the kernel $`P_\sigma` of {uses "def_strip_poisson_kernel"}[] is positive,
even and decreasing in $`|T|`, and integrable with
$`\int_{\mathbb{R}}P_\sigma(T)\,dT = \dfrac{1-\sigma}{2}`. For $`0 \le \sigma < 1`,
$`P_\sigma(T) \le \dfrac{1-\sigma}{2}\cdot\dfrac{\pi}{2}e^{-\pi|T|/2}`; in particular
$`P_\sigma(T) \ll_\sigma e^{-\pi|T|/2}`.
:::

:::proof "lemma_strip_poisson_kernel_properties"
$`\cosh(\pi T/2) \ge 1 > \cos\theta` and $`\sin\theta > 0` give positivity; evenness and
monotonicity in $`|T|` are those of $`\cosh`. The primitive
$`Q_\sigma(T) = \pi^{-1}\arctan\bigl((e^{\pi T/2} - \cos\theta)/\sin\theta\bigr)`
(`CohnElkies.Q_σ`) satisfies $`Q_\sigma' = P_\sigma`, $`Q_\sigma(+\infty) = \tfrac12` and
$`Q_\sigma(-\infty) = \theta/\pi - \tfrac12`, so $`\int P_\sigma = 1 - \theta/\pi = (1-\sigma)/2`.
For $`\sigma \ge 0` one has $`\cos\theta \le 0`, so $`\cosh(\pi T/2) - \cos\theta \ge \tfrac12e^{\pi|T|/2}`,
while $`\sin\theta = \sin(\pi(1-\sigma)/2) \le \pi(1-\sigma)/2`.
:::

:::definition "def_strip_poisson_mass" (lean := "CohnElkies.M_σ") (parent := "grp_mellin_strip")
The mass of the lower edge is (equation (15)) $`M_\sigma = \dfrac{1-\sigma}{2}`, the total mass
$`\int_{\mathbb{R}}P_\sigma(T)\,dT` of the kernel of {uses "def_strip_poisson_kernel"}[]
({uses "lemma_strip_poisson_kernel_properties"}[]).
:::

:::definition "def_strip_poisson_majorant" (lean := "CohnElkies.H_σ") (parent := "grp_mellin_strip")
The Poisson majorant of the lower-boundary majorant $`h_\lambda` of
{uses "def_lower_boundary_majorant"}[] is (equation (18))
$`H_\sigma(s) = \int_{\mathbb{R}}P_\sigma(T)\,h_\lambda(s - \lambda T)\,dT`,
with $`P_\sigma` from {uses "def_strip_poisson_kernel"}[].
:::

:::definition "def_strip_conformal_map" (lean := "CohnElkies.stripToHalfPlane, CohnElkies.halfPlaneToStrip") (parent := "grp_mellin_strip")
Let $`\lambda > 0`. The conformal map of the strip $`\{|\operatorname{Im} t| < \lambda\}` onto the
upper half-plane $`\mathbb{H}` is $`\Phi(t) = \exp(\pi(t + i\lambda)/(2\lambda))`, with inverse
$`\Phi^{-1}(w) = (2\lambda/\pi)\log w - i\lambda` (principal branch of the logarithm).
:::

:::lemma_ "lemma_strip_conformal_map" (lean := "CohnElkies.stripToHalfPlane_im_pos, CohnElkies.halfPlaneToStrip_mem_strip, CohnElkies.halfPlaneToStrip_stripToHalfPlane, CohnElkies.stripToHalfPlane_ofReal_add_I_mul_mul, CohnElkies.tendsto_halfPlaneToStrip_ofReal_of_pos, CohnElkies.tendsto_halfPlaneToStrip_ofReal_of_neg") (parent := "grp_mellin_strip")
The map $`\Phi` of {uses "def_strip_conformal_map"}[] sends the open strip into $`\mathbb{H}`,
$`\Phi^{-1}` sends $`\mathbb{H}` into the open strip, and $`\Phi^{-1} \circ \Phi` is the identity
on the strip. The lower edge $`y - i\lambda` goes to $`e^{\pi y/(2\lambda)} \in (0, \infty)`, the
upper edge $`y + i\lambda` to $`-e^{\pi y/(2\lambda)} \in (-\infty, 0)`, and
$`t_0 = s + i\sigma\lambda` to $`\rho e^{i\theta}` with $`\rho = e^{\pi s/(2\lambda)}` and
$`\theta = \pi(1 + \sigma)/2` the angle of {uses "def_strip_poisson_kernel"}[]. The inverse
extends continuously to $`\mathbb{R} \setminus \{0\}`: as $`w \to x` within $`\mathbb{H}`,
$`\Phi^{-1}(w) \to (2\lambda/\pi)\log x - i\lambda` for $`x > 0` and
$`\Phi^{-1}(w) \to (2\lambda/\pi)\log(-x) + i\lambda` for $`x < 0`.
:::

:::proof "lemma_strip_conformal_map"
$`\operatorname{Im}\Phi(t) = e^{\pi\operatorname{Re}t/(2\lambda)}\sin\bigl(\pi(\operatorname{Im}t + \lambda)/(2\lambda)\bigr) > 0`
for $`|\operatorname{Im} t| < \lambda`, and
$`\operatorname{Im}\Phi^{-1}(w) = (2\lambda/\pi)\arg w - \lambda \in (-\lambda, \lambda)` for
$`\arg w \in (0, \pi)`. The boundary correspondence is read off from
$`\exp(\pi(y \mp i\lambda + i\lambda)/(2\lambda))` and $`e^{i\pi} = -1`, and $`\Phi^{-1}` is
continuous on $`\mathbb{H} \cup (\mathbb{R} \setminus \{0\})` because the principal logarithm is
continuous on the slit plane and, on the negative axis approached from above, tends to
$`\log|x| + i\pi`.
:::

:::definition "def_halfplane_datum" (lean := "CohnElkies.halfPlaneDatum") (parent := "grp_mellin_strip")
For a lower-edge datum $`b : \mathbb{R} \to \mathbb{R}` of the strip, the transferred datum on
$`\mathbb{R} = \partial\mathbb{H}` is $`\tilde b(x) = b((2\lambda/\pi)\log x)` for $`x > 0`, the
image of the lower edge under $`\Phi` of {uses "def_strip_conformal_map"}[], and
$`\tilde b(x) = 0` for $`x \le 0`, the image of the upper edge.
:::

:::lemma_ "lemma_halfplane_datum_integrable" (lean := "CohnElkies.halfPlaneDatum_continuousAt, CohnElkies.integrable_halfPlaneDatum_div_one_add_sq") (parent := "grp_mellin_strip")
If $`b` is continuous with $`|b(y)| \le A(1 + |y|)`, then $`\tilde b` of
{uses "def_halfplane_datum"}[] is continuous on $`\mathbb{R} \setminus \{0\}` and
$`\tilde b(x)/(1 + x^2)` is integrable: $`\tilde b` is an admissible boundary datum for the
Poisson integral of {uses "def_halfplane_poisson_integral"}[].
:::

:::proof "lemma_halfplane_datum_integrable"
Continuity off $`0` is clear. Under $`x = e^{u}`, $`\tilde b(x)/(1 + x^2)` on $`(0, \infty)`
becomes $`e^{u}b((2\lambda/\pi)u)/(1 + e^{2u})`, which is dominated by
$`A(1 + (2\lambda/\pi)|u|)e^{-|u|}`.
:::

:::lemma_ "lemma_strip_harmonic_measure" (lean := "CohnElkies.poissonIntegralHalfPlane_halfPlaneDatum, CohnElkies.poissonKernelHalfPlane_stripToHalfPlane_mul, CohnElkies.poissonIntegralHalfPlane_halfPlaneDatum_eq_integral_P_σ") (parent := "grp_mellin_strip")
(Harmonic measure of the strip.) With $`\Phi` from {uses "def_strip_conformal_map"}[], $`\tilde b`
from {uses "def_halfplane_datum"}[], $`P_\sigma` from {uses "def_strip_poisson_kernel"}[] and the
Poisson integral $`P[\,\cdot\,]` of {uses "def_halfplane_poisson_integral"}[], for
$`-1 < \sigma < 1` and $`s \in \mathbb{R}`,
$`P[\tilde b](\Phi(s + i\sigma\lambda)) = \int_{\mathbb{R}}\lambda^{-1}P_\sigma\Bigl(\dfrac{s - y}{\lambda}\Bigr)b(y)\,dy = \int_{\mathbb{R}}P_\sigma(T)\,b(s - \lambda T)\,dT`:
$`\lambda^{-1}P_\sigma((s - y)/\lambda)\,dy` is the harmonic measure of the lower edge at
$`s + i\sigma\lambda`.
:::

:::proof "lemma_strip_harmonic_measure"
On $`(0, \infty)` substitute $`x = e^{\pi y/(2\lambda)}`, $`dx = (\pi/(2\lambda))\,x\,dy`: the
half-plane kernel at $`\rho e^{i\theta} = \Phi(s + i\sigma\lambda)`
({uses "lemma_strip_conformal_map"}[]) satisfies
$`\dfrac{1}{\pi}\dfrac{\rho\sin\theta}{(x - \rho\cos\theta)^2 + \rho^2\sin^2\theta}\cdot\dfrac{\pi x}{2\lambda} = \dfrac{\sin\theta}{4\lambda\bigl(\tfrac12(\rho/x + x/\rho) - \cos\theta\bigr)} = \dfrac{1}{\lambda}P_\sigma\Bigl(\dfrac{s - y}{\lambda}\Bigr)`,
since $`(x - \rho\cos\theta)^2 + \rho^2\sin^2\theta = \rho x\,(x/\rho + \rho/x - 2\cos\theta)` and
$`\tfrac12(\rho/x + x/\rho) = \cosh(\pi(s - y)/(2\lambda))`; the substitution
$`T = (s - y)/\lambda` gives the second form.
:::

:::lemma_ "lemma_strip_harmonic_measure_mass" (lean := "CohnElkies.poissonIntegralHalfPlane_halfPlaneDatum_one, CohnElkies.poissonIntegralHalfPlane_indicator_Iic") (parent := "grp_mellin_strip")
The harmonic measure of the lower edge at $`s + i\sigma\lambda`
({uses "lemma_strip_harmonic_measure"}[]) has total mass $`M_\sigma = (1 - \sigma)/2`
({uses "def_strip_poisson_mass"}[]), and the upper edge has harmonic measure $`(1 + \sigma)/2`.
:::

:::proof "lemma_strip_harmonic_measure_mass"
The datum $`b = 1` in {uses "lemma_strip_harmonic_measure"}[] gives
$`\int P_\sigma = M_\sigma` ({uses "lemma_strip_poisson_kernel_properties"}[]), and the
complementary mass of $`(-\infty, 0]` is $`1 - M_\sigma = (1 + \sigma)/2` since the half-plane
kernel has total mass $`1`.
:::

:::lemma_ "lemma_strip_poisson_principle" (lean := "CohnElkies.norm_le_exp_integral_P_σ_of_strip") (parent := "grp_mellin_strip")
(Poisson principle for the strip.) Let $`\lambda > 0` and let $`Z` be holomorphic and bounded on
the open strip $`\{|\operatorname{Im} t| < \lambda\}` and continuous on its closure. Let
$`b : \mathbb{R} \to \mathbb{R}` be continuous with $`|b(y)| \le A(1 + |y|)`, and suppose
$`\log|Z(y - i\lambda)| \le b(y)` and $`\log|Z(y + i\lambda)| \le 0` for all $`y \in \mathbb{R}`.
Then for $`-1 < \sigma < 1` and $`s \in \mathbb{R}`,
$`\log|Z(s + i\sigma\lambda)| \le \int_{\mathbb{R}}P_\sigma(T)\,b(s - \lambda T)\,dT`,
with $`P_\sigma` from {uses "def_strip_poisson_kernel"}[].
:::

:::proof "lemma_strip_poisson_principle"
Let $`\Phi` and $`\tilde b` be as in {uses "def_strip_conformal_map"}[] and
{uses "def_halfplane_datum"}[]. The function $`F = Z \circ \Phi^{-1}` is holomorphic and bounded
on $`\mathbb{H}` ({uses "lemma_strip_conformal_map"}[]), so $`\log|F|` is subharmonic and bounded
above ({uses "lemma_log_norm_subharmonic"}[]). As $`w \to x` within $`\mathbb{H}`,
$`F(w) \to Z((2\lambda/\pi)\log x - i\lambda)` for $`x > 0` and
$`F(w) \to Z((2\lambda/\pi)\log(-x) + i\lambda)` for $`x < 0`, by the continuity of $`\Phi^{-1}`
up to $`\mathbb{R} \setminus \{0\}` and of $`Z` on the closed strip; hence $`\limsup_{w \to x}\log|F(w)| \le \tilde b(x)` for every $`x \ne 0`, the
lower-edge bound giving $`\tilde b(x) = b((2\lambda/\pi)\log x)` on $`(0, \infty)` and the
upper-edge bound giving $`0` on $`(-\infty, 0)`. The datum $`\tilde b` is continuous off $`0` with
$`\tilde b(x)/(1 + x^2)` integrable ({uses "lemma_halfplane_datum_integrable"}[]), so the Poisson
principle for the upper half-plane
({uses "cor_halfplane_poisson_principle_log"}[], with the exceptional set $`E = \{0\}`) gives
$`\log|F| \le P[\tilde b]` on $`\mathbb{H}`. At $`w = \Phi(s + i\sigma\lambda)` this reads
$`\log|Z(s + i\sigma\lambda)| \le P[\tilde b](\Phi(s + i\sigma\lambda)) = \int_{\mathbb{R}}P_\sigma(T)\,b(s - \lambda T)\,dT`
by {uses "lemma_strip_harmonic_measure"}[].
:::

:::lemma_ "lemma_3_2_holomorphic" (lean := "CohnElkies.RadialEigenfunction.diffContOnCl_Z_g, CohnElkies.RadialEigenfunction.exists_norm_Z_g_le") (parent := "grp_mellin_strip")
In the setting of {uses "def_normalized_profile"}[], the function $`Z` is holomorphic on a
neighbourhood of the strip $`|\operatorname{Im} t| \le \lambda` (in particular holomorphic on
the open strip and continuous on its closure), and it is bounded on the closed strip.
:::

:::proof "lemma_3_2_holomorphic"
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
:::

:::lemma_ "eq_16_upper_boundary" (lean := "CohnElkies.RadialEigenfunction.norm_Z_g_top_le_one") (parent := "grp_mellin_strip")
In the setting of {uses "def_normalized_profile"}[], $`|Z(y + i\lambda)| \le 1` for all real
$`y` (equation (16)).
:::

:::proof "eq_16_upper_boundary"
By {uses "eq_13_mellin_fourier"}[] with $`t = y + i\lambda`,
$`Z(y+i\lambda) = \int\varphi(v)e^{-iyv}\,dv`, so $`|Z(y+i\lambda)| \le \|\varphi\|_1 = 1` by
{uses "eq_13_normalization"}[].
:::

:::lemma_ "eq_17_lower_boundary" (lean := "CohnElkies.RadialEigenfunction.norm_Z_g_bottom_le_exp_h_ℓ") (parent := "grp_mellin_strip")
In the setting of {uses "def_normalized_profile"}[], $`\log|Z(y - i\lambda)| \le h_\lambda(y)`
for $`y \ne 0`, with $`h_\lambda` from {uses "def_lower_boundary_majorant"}[] (equation (17)).
:::

:::proof "eq_17_lower_boundary"
Evaluating (9), continued to $`\operatorname{Re} z = 0` by
{uses "lemma_mellin_continuation"}[], at $`z = -iy` and using $`\widehat g = \varsigma g` gives
$`X_g(y - i\lambda)`
$`= \varsigma\pi^{\lambda+iy}\frac{\Gamma(-iy/2)}{\Gamma(\lambda+iy/2)}X_g(-y+i\lambda)`,
hence
$`Z(y - i\lambda)`
$`= \varsigma(\pi R^2)^{\lambda+iy}\frac{\Gamma(-iy/2)}{\Gamma(\lambda + iy/2)}Z(-y + i\lambda)`.
Taking absolute values and using (16) ({uses "eq_16_upper_boundary"}[]) gives
$`\log|Z(y - i\lambda)| \le h_\lambda(y)` for $`y \ne 0`, independently of $`\varsigma`. At
$`y = 0` the zero $`Z(i\lambda) = \int\varphi = 0` ({uses "eq_13_mean_zero"}[]) cancels the gamma
pole in (17), so $`Z(-i\lambda)` is finite, although $`h_\lambda(y) = -\log|y| + O_\lambda(1)` as
$`y \to 0`.
:::

:::lemma_ "lemma_3_2" (lean := "CohnElkies.norm_Z_g_le_exp_H_σ") (parent := "grp_mellin_strip")
In the setting of {uses "def_normalized_profile"}[], for every $`-1 < \sigma < 1` and every
$`s \in \mathbb{R}`, with $`P_\sigma` from {uses "def_strip_poisson_kernel"}[] and $`H_\sigma`
from {uses "def_strip_poisson_majorant"}[] (equation (18)),
$`|Z(s + i\sigma\lambda)| \le \exp(H_\sigma(s))`
$`= \exp\Bigl(\int_{\mathbb{R}}P_\sigma(T)h_\lambda(s-\lambda T)\,dT\Bigr)`.
:::

:::proof "lemma_3_2"
$`Z` is bounded and holomorphic on the strip and continuous on its closure
({uses "lemma_3_2_holomorphic"}[]), with the boundary bounds (16) and (17) of
{uses "eq_16_upper_boundary"}[] and {uses "eq_17_lower_boundary"}[]. The logarithmic singularity
of $`h_\lambda` requires a bounded truncation. Choose
$`D > \max\{0, \sup_y\log|Z(y - i\lambda)|\}` and let $`h_{\lambda,D} = \min\{h_\lambda, D\}`
(with value $`D` at $`0`), a continuous function of logarithmic growth. The Poisson principle
({uses "lemma_strip_poisson_principle"}[]) applied to the bounded function $`Z` with lower majorant
$`h_{\lambda,D}` and upper majorant $`0` gives the capped bound
$`\log|Z(s+i\sigma\lambda)| \le \int P_\sigma(T)h_{\lambda,D}(s-\lambda T)\,dT`
({uses "lemma_3_2_capped"}[]). The integral $`H_\sigma(s)` converges absolutely, because
$`P_\sigma` decays exponentially ({uses "lemma_strip_poisson_kernel_properties"}[]), the
singularity of $`h_\lambda` at $`0` is locally integrable, and
$`h_\lambda(y) = -\lambda\log|y| + O_\lambda(1)` as $`|y| \to \infty` by Stirling's formula. Since
$`h_{\lambda,D} \le h_\lambda` and $`P_\sigma \ge 0`, the capped majorant is at most
$`H_\sigma(s)`; equivalently, dominated convergence lets $`D \to \infty`
(`CohnElkies.lowerStripCappedPoisson_tendsto`). This proves (18).
:::

:::lemma_ "lemma_convolution_symmetric_decreasing" (lean := "CohnElkies.even_antitone_poisson_convolution_max") (parent := "grp_mellin_strip")
Let $`f : \mathbb{R} \to [0,\infty)` be integrable, compactly supported, even, and nonincreasing on
$`[0,\infty)`, and let $`-1 < \sigma < 1`. Then $`(f * P_\sigma)(x) \le (f * P_\sigma)(0)` for every
$`x \in \mathbb{R}`, with $`P_\sigma` from {uses "def_strip_poisson_kernel"}[] (which is
positive, even and nonincreasing on $`[0,\infty)`).
:::

:::proof "lemma_convolution_symmetric_decreasing"
Layer-cake: $`f(x) = \int_0^\infty \mathbf 1_{\{f > \alpha\}}(x)\,d\alpha` and similarly for $`q`,
where, up to endpoints, $`\{f > \alpha\} = (-r_\alpha, r_\alpha)` and
$`\{q > \beta\} = (-R_\beta, R_\beta)` (`CohnElkies.even_antitone_superlevel_interval`). By
Tonelli, $`(f*q)(x)` is the double integral over $`\alpha, \beta` of the length of
$`(-R_\beta,R_\beta) \cap (x - r_\alpha, x + r_\alpha)`, and the length of the intersection of two
centred intervals, one translated by $`x`, is largest at $`x = 0`.
:::

:::definition "def_lower_endpoint_expectation" (lean := "CohnElkies.f_T, CohnElkies.lowerPoissonEndpointExpectation") (parent := "grp_mellin_strip")
Put $`f_T(x) = \log\sqrt{x^2 + T^2/4}` and
$`J_\sigma = -\dfrac{1}{M_\sigma}\int_{\mathbb{R}}P_\sigma(T)\int_0^1 f_T(x)\,dx\,dT`,
with $`P_\sigma`, $`M_\sigma` from {uses "def_strip_poisson_kernel"}[] and
{uses "def_strip_poisson_mass"}[]. The formalization uses instead
$`J^{\mathrm{Lean}}_\sigma = J_\sigma - 1 = \dfrac{1}{M_\sigma}\int_{\mathbb{R}}P_\sigma(T)\Lambda(T)\,dT`,
the expectation against $`P_\sigma/M_\sigma` of the endpoint phase
$`\Lambda(T) = -\int_0^1 f_T(x)\,dx - 1` of {bpref "lemma_3_3_one_sided"}[], so that
$`\log(2\pi c^2) + J_\sigma = \log(2\pi ec^2) + J^{\mathrm{Lean}}_\sigma`.
:::

:::lemma_ "lemma_3_3_max_at_zero" (lean := "CohnElkies.lowerStripPoissonMajorant_dimension_centered_max") (parent := "grp_mellin_strip")
In the setting of {uses "def_normalized_profile"}[] with $`d \ge 2`, for every $`-1 < \sigma < 1`
and every $`s \in \mathbb{R}`, $`H_\sigma(s) \le H_\sigma(0)`, with $`H_\sigma` from
{uses "def_strip_poisson_majorant"}[] and $`h_\lambda` from {uses "def_lower_boundary_majorant"}[].
:::

:::proof "lemma_3_3_max_at_zero"
By the digamma series in {bpref "def_digamma"}[], for $`y > 0`,
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
$`H_\sigma(s) \le H_\sigma(0)`.
:::

:::lemma_ "lemma_3_3" (lean := "CohnElkies.lowerStripPoissonMajorant_dimension_central_bound") (parent := "grp_mellin_strip")
For every $`0 \le \sigma < 1` there is $`E_\sigma < \infty`, independent of $`d`, $`c` and $`g`,
such that in the setting of {uses "def_normalized_profile"}[] (with $`d \ge 2`), with $`J_\sigma`
from {uses "def_lower_endpoint_expectation"}[] (equation (20)),
$`H_\sigma(0) \le \lambda M_\sigma\bigl(\log(2\pi c^2) + J_\sigma\bigr) + E_\sigma`;
hence, by {uses "lemma_3_3_max_at_zero"}[],
$`H_\sigma(s) \le \lambda M_\sigma\bigl(\log(2\pi c^2) + J_\sigma\bigr) + E_\sigma` for every
$`s \in \mathbb{R}`. Uses {uses "def_lower_boundary_majorant"}[],
{uses "def_strip_poisson_kernel"}[], {uses "def_strip_poisson_mass"}[] and
{uses "def_strip_poisson_majorant"}[].
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
:::

:::lemma_ "eq_21_sech_characteristic" (lean := "CohnElkies.poissonLogistic_characteristic") (parent := "grp_mellin_strip")
The probability density $`p(u) = \dfrac{\pi}{4}\operatorname{sech}^2\bigl(\dfrac{\pi u}{2}\bigr)`
$`= \dfrac{\pi e^{\pi u}}{(1 + e^{\pi u})^2}` on $`\mathbb{R}` has characteristic function
(equation (21))
$`\int_{\mathbb{R}}p(u)e^{itu}\,du = \int_{\mathbb{R}}p(u)\cos(tu)\,du = \dfrac{t}{\sinh t}`
for $`t \in \mathbb{R}`, interpreted as $`1` at $`t = 0`.
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

:::lemma_ "eq_22_log_moment_digamma" (lean := "CohnElkies.integral_poissonLogisticDensity_mul_log_sqrt") (parent := "grp_mellin_strip")
With $`p` from {uses "eq_21_sech_characteristic"}[] and $`\psi` from {uses "def_digamma"}[],
for every $`x \ge 0` (equation (22))
$`\int_{\mathbb{R}}p(u)\log\sqrt{x^2+u^2}\,du = \psi\Bigl(\dfrac{x+1}{2}\Bigr) + \log 2`.
:::

:::proof "eq_22_log_moment_digamma"
Let $`x > 0`. Taking real parts in the complex Frullani formula
$`\int_0^\infty (e^{-t} - e^{-(x+iu)t})/t\,dt = \log(x+iu)` gives
$`\log\sqrt{x^2+u^2} = \int_0^\infty\dfrac{e^{-t} - e^{-xt}\cos(ut)}{t}\,dt`. The integrand times
$`p(u)` is integrable on $`\mathbb{R} \times (0,\infty)` (it is bounded by $`p(u)(1 + x + |u|)`
for $`t \le 1`, using $`|1 - \cos(ut)| \le |u|t`, and by $`p(u)(e^{-t} + e^{-xt})` for $`t \ge 1`),
so by Fubini, $`\int p = 1` and {uses "eq_21_sech_characteristic"}[],
$`\int_{\mathbb{R}}p(u)\log\sqrt{x^2+u^2}\,du = \int_0^\infty\Bigl(\dfrac{e^{-t}}{t} - \dfrac{e^{-xt}}{\sinh t}\Bigr)dt`.
Gauss's integral ({uses "lemma_digamma_gauss_integral"}[]) at $`m = (x+1)/2`, after the substitution
$`t = 2s`, reads $`\psi((x+1)/2) = \int_0^\infty\bigl(e^{-2s}/s - e^{-xs}/\sinh s\bigr)ds`. Subtracting,
the difference of the two sides is $`\int_0^\infty (e^{-s} - e^{-2s})/s\,ds = \log 2` (Frullani).
The case $`x = 0` follows by letting $`x \downarrow 0`: the left side converges by dominated
convergence (for $`0 \le x \le 1`, $`|\log\sqrt{x^2+u^2}| \le |\log|u|| + |u|`, and $`\log|u|` is
locally integrable against the bounded density $`p`), and $`\psi` is continuous at $`1/2`.
:::

:::lemma_ "lemma_3_4" (lean := "CohnElkies.tendsto_lowerPoissonEndpointExpectation, CohnElkies.limitingPoissonEndpointExpectation_eq_log_pi_div_two_sub_one") (parent := "grp_mellin_strip")
For $`J_\sigma` from {uses "def_lower_endpoint_expectation"}[],
$`\lim_{\sigma\uparrow 1}J_\sigma = \log(\pi/2)`, that is,
$`J^{\mathrm{Lean}}_\sigma \to \log(\pi/2) - 1`.
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
$`\lim J^{\mathrm{Lean}}_\sigma = \int p(u)\Lambda(2u)\,du = \log(\pi/2) - 1`.
:::

:::lemma_ "eq_23_sharp_coefficient" (lean := "CohnElkies.lowerPoissonEndpointSharpCoefficient_eq, CohnElkies.eventually_lowerPoissonEndpointSharpCoefficient_neg") (parent := "grp_mellin_strip")
For every $`0 < c < 1/\pi`, with $`J_\sigma` from {uses "def_lower_endpoint_expectation"}[],
$`\log(2\pi c^2) + \lim_{\sigma\uparrow1}J_\sigma = \log(\pi^2c^2) < 0`, so
$`\delta_c(\sigma) = -(\log(2\pi c^2) + J_\sigma) > 0` for all $`\sigma < 1` close enough to $`1`;
fix such a $`\sigma = \sigma(c) \in (0,1)` (equation (23)).
:::

:::proof "eq_23_sharp_coefficient"
By {uses "lemma_3_4"}[], $`\log(2\pi c^2) + J_\sigma \to \log(2\pi c^2) + \log(\pi/2) = \log(\pi^2c^2)`
as $`\sigma \uparrow 1`, which is negative exactly when $`c < 1/\pi`.
:::

From now on fix $`\sigma = \sigma(c)` and $`\delta_c > 0` as in (23). We first bound $`Z` on the
horizontal line $`\operatorname{Im} t = \sigma\lambda`, and then use that bound to control the mass
of $`g` inside $`B(0,c\sqrt d)`.

:::lemma_ "lemma_3_5" (lean := "CohnElkies.exists_lowerStripPoissonMajorant_uniform_negative") (parent := "grp_mellin_strip")
There is $`\gamma_c > 0`, depending only on $`c` (not on $`d`, $`g`, or $`\varsigma`), such that
for every sufficiently large $`d`, with $`\sigma = \sigma(c)` from
{uses "eq_23_sharp_coefficient"}[] and $`H_\sigma` from {uses "def_strip_poisson_majorant"}[]
(in the setting of {uses "def_normalized_profile"}[]),
$`H_\sigma(s) \le -\gamma_c\lambda` for all $`s \in \mathbb{R}` (equation (24)).
:::

:::proof "lemma_3_5"
Uniform negativity. The maximum estimate (20) of {uses "lemma_3_3"}[] and
$`\log(2\pi c^2) + J_\sigma = -\delta_c` from {uses "eq_23_sharp_coefficient"}[] give
$`H_\sigma(s) \le -\lambda M_\sigma\delta_c + O_\sigma(\log\lambda) \le -\gamma_c\lambda` for all
$`s` once $`d` is large, with $`\gamma_c > 0` independent of $`s`, $`g` and $`\varsigma`.
:::

:::lemma_ "eq_25_logarithmic_tail" (lean := "CohnElkies.exists_lowerStripPoissonMajorant_logarithmic_tail") (parent := "grp_mellin_strip")
For every $`0 \le \sigma < 1` there are $`B_c, C_c, \kappa_c > 0`, depending only on $`c` and
$`\sigma`, such that for all $`d \ge 2` and all $`|S| \ge B_c`, in the setting of
{uses "def_normalized_profile"}[] and with $`H_\sigma` from {uses "def_strip_poisson_majorant"}[],
$`H_\sigma(\lambda S) \le -\kappa_c\lambda\log\dfrac{|S|}{C_c}` (equation (25)).
:::

:::proof "eq_25_logarithmic_tail"
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
:::

:::lemma_ "eq_26_integral_bound" (lean := "CohnElkies.integral_norm_Z_g_le_of_majorant") (parent := "grp_mellin_strip")
There are $`\gamma_c, C_c > 0`, depending only on $`c`, such that for every sufficiently large
$`d`, with $`\sigma = \sigma(c)` from {uses "eq_23_sharp_coefficient"}[] and $`Z` as in
{uses "def_normalized_profile"}[],
$`\int_{\mathbb{R}}|Z(s + i\sigma\lambda)|\,ds \le C_c\lambda e^{-\gamma_c\lambda}` (equation (26)).
:::

:::proof "eq_26_integral_bound"
Integration. Choose $`B > \max\{B_c, C_c'\}` and $`q = M_\sigma\lambda/2 > 1`. By (24) of {uses "lemma_3_5"}[],
$`\int_{|s| \le B\lambda}e^{H_\sigma(s)}\,ds \le 2B\lambda e^{-\gamma_c\lambda}`, while the
substitution $`s = \lambda S` and (25) of {uses "eq_25_logarithmic_tail"}[] give
$`\int_{|s| > B\lambda}e^{H_\sigma(s)}\,ds \le \lambda\int_{|S|>B}(|S|/C_c')^{-q}\,dS`
$`= \dfrac{2\lambda C_c'}{q-1}\Bigl(\dfrac{B}{C_c'}\Bigr)^{1-q}`,
which decays at exponential rate $`(M_\sigma/2)\log(B/C_c') > 0` in $`\lambda`. Decreasing
$`\gamma_c` if necessary and applying $`|Z(s+i\sigma\lambda)| \le e^{H_\sigma(s)}` from
{uses "lemma_3_2"}[] gives (26). The formalization merges the two integrals into the single
majorant of {uses "lemma_3_5_inverse_quadratic"}[].
:::

:::lemma_ "lemma_3_6" (lean := "CohnElkies.RadialEigenfunction.setIntegral_ball_norm_le") (parent := "grp_mellin_strip")
In the setting of {uses "def_normalized_profile"}[], for every $`-1 < \sigma < 1`,
$`\int_{-\infty}^0|\varphi(v)|\,dv = \dfrac{1}{\|g\|_1}\int_{|x|<R}|g(x)|\,dx`
$`\le \dfrac{1}{2\pi(1-\sigma)\lambda}\int_{\mathbb{R}}|Z(s+i\sigma\lambda)|\,ds`,
the equality being {uses "eq_13_interior_mass"}[]. Consequently, by (26) of
{uses "eq_26_integral_bound"}[], for every $`0 < c < 1/\pi` there exist $`C_c, \gamma_c > 0` and
$`d_0(c)` such that $`\int_{-\infty}^0|\varphi(v)|\,dv \le C_c e^{-\gamma_c d}` for all
$`d \ge d_0(c)` (equation (27)); in the formalization this consequence is
{bpref "prop_3_1"}[] in the form (11).
:::

:::proof "lemma_3_6"
Let $`G(v) = e^{(\sigma-1)\lambda v}\varphi(v)`. By (12) and the substitution $`r = Re^v`,
$`\int_{\mathbb{R}}|G(v)|\,dv`
$`= \dfrac{S_dR^{(1-\sigma)\lambda}}{\|g\|_1}\int_0^\infty|g(r)|r^{(1+\sigma)\lambda-1}\,dr`
$`< \infty`,
so $`G \in L^1(\mathbb{R})`, and {uses "eq_13_mellin_fourier"}[] with $`t = s + i\sigma\lambda`
identifies its Fourier transform $`\int G(v)e^{-isv}\,dv` with $`Z(s + i\sigma\lambda)`. This
transform is integrable by (26) of {uses "eq_26_integral_bound"}[]
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
:::

:::proof "prop_3_1"
By {uses "eq_13_interior_mass"}[], the left side of (27) is exactly
$`\|g\|_1^{-1}\int_{|x|<c\sqrt d}|g(x)|\,dx`. Thus {uses "lemma_3_6"}[], fed with the $`L^1`
bound (26) of {uses "eq_26_integral_bound"}[], proves (11), uniformly in $`g` and in its Fourier
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
:::

:::proof "prop_3_7"
Schwartz case. Suppose first that $`g` is a radial Schwartz eigenfunction. Since
$`\int g = \widehat g(0) = \varsigma g(0) = 0`, its negative part $`g_- = \max\{-g,0\}` has
integral $`\|g\|_1/2`. If $`g \ge 0` for $`|x| \ge c\sqrt d`, then $`g_-` vanishes outside
$`B(0,c\sqrt d)`, so
$`\|g\|_1/2 = \int g_- \le \int_{|x|<c\sqrt d}|g| \le C_ce^{-\gamma_c d}\|g\|_1`
by {uses "prop_3_1"}[], which is impossible once $`C_ce^{-\gamma_c d} < 1/2`.

General case. Let $`g \in \mathcal{E}_\varsigma(d)` be nonnegative outside $`B(0,R)`,
$`R = c\sqrt d`. By {uses "lemma_rotational_average_eigenfunction"}[] and
{uses "lemma_rotational_average_signs"}[], $`h = \mathcal{R}g` is a nonzero radial element of
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
There is a sequence $`\epsilon_d \to 0`, $`\epsilon_d \ge 0`, such that for every $`d \ge 1` and
every $`F \in \mathcal{A}_d` ({uses "def_admissible_class"}[]), (equation (28))
$`\dfrac{F(0)}{\widehat F(0)}`
$`\ge \dfrac{2^d}{v_d}\Bigl(\sqrt{\dfrac{e}{2\pi}} - \epsilon_d\Bigr)^d`,
with $`v_d` from {uses "def_ball_volume"}[].
:::

:::proof "thm_3_8"
By {uses "lemma_rotational_average_admissible"}[] we may replace $`F` by its rotational average,
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
