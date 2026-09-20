import Verso
import VersoManual
import VersoBlueprint
import CohnElkies

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The Cohn–Elkies bound" =>

The report uses the linear-programming bound $`\Delta_d \le \mathrm{LP}_d` of Gorbachev and
Cohn–Elkies as an external input. The Lean development proves it, following the original
argument of Cohn and Elkies: for a periodic packing, Poisson summation over the packing lattice
converts a sum of the auxiliary function over differences of centers into a sum over the polar
lattice whose terms are nonnegative, and the term at the origin already gives the bound; general
packings are then approximated by periodic ones. The sphere-packing fundamentals (periodic
packings, their density formula and the passage from arbitrary to periodic packings) were adapted
from the Sphere Packing in Lean project, and Poisson summation for a general lattice of
$`\mathbb{R}^d` was formalized for this purpose. The chapter corresponds to the modules
`CohnElkies/SpherePacking/{Basic,Periodic,PeriodicApproximation,CohnElkiesBound}.lean` and
`CohnElkiesForMathlib/Analysis/Fourier/PoissonSummation.lean`.
Throughout, $`d \ge 1`, Lebesgue measure on $`\mathbb{R}^d` is written $`\operatorname{vol}`, and
$`B(x,r)` is the open ball.

# Periodic packings

:::definition "def_periodic_packing" (lean := "PeriodicSpherePacking")
A sphere packing with set of centers $`X` and separation $`s` ({uses "def_packing_density"}[])
is *periodic* if $`X` is invariant under translation by a lattice $`\Lambda \subseteq \mathbb{R}^d`,
that is, a discrete subgroup of rank $`d`: $`\Lambda + X \subseteq X`.
:::

:::definition "def_periodic_packing_constant" (lean := "PeriodicSpherePackingConstant")
The *periodic packing constant* is the supremum of the upper densities of all periodic packings
({uses "def_periodic_packing"}[]).
:::

:::definition "def_center_orbits" (lean := "PeriodicSpherePacking.centerOrbitCardinality")
For a periodic packing ({uses "def_periodic_packing"}[]) the number $`N` of $`\Lambda`-orbits of
centers.
:::

:::lemma_ "lemma_center_orbits_finite" (lean := "PeriodicSpherePacking.finiteCenterTranslationQuotient, PeriodicSpherePacking.encard_centers_in_fundamental_region")
For a periodic packing the $`\Lambda`-orbits of centers are finite in number, and their number
$`N` ({uses "def_center_orbits"}[]) equals the number of centers in any bounded region $`D`
whose $`\Lambda`-translates tile $`\mathbb{R}^d`.
:::

:::proof "lemma_center_orbits_finite"
Each orbit meets $`D` exactly once, and $`D` is bounded while the centers are $`1`-separated,
so $`X \cap D` is finite.
:::

:::definition "def_polar_lattice" (lean := "SchwartzMap.polarIntegerLattice")
For a lattice $`\Lambda \subseteq \mathbb{R}^d` write $`\operatorname{covol}(\Lambda)` for the
volume of a fundamental domain of $`\Lambda` (Mathlib's `ZLattice.covolume`) and
$`\Lambda^*`
$`= \{ y \in \mathbb{R}^d : \langle x, y\rangle \in \mathbb{Z} \text{ for all } x \in \Lambda\}`
for the polar lattice.
:::

:::lemma_ "lemma_polar_lattice_coordinates" (lean := "SchwartzMap.latticeCoordinateEquiv, SchwartzMap.lattice_covolume_eq_coordinate_determinant, SchwartzMap.integerVectorPolarEquiv, SchwartzMap.wInner_latticeCoordinateEquiv_symm")
The standard lattice $`\mathbb{Z}^d` is its own polar lattice ({uses "def_polar_lattice"}[]),
and if $`A` is the linear automorphism of $`\mathbb{R}^d` sending the standard basis to a
$`\mathbb{Z}`-basis of $`\Lambda`, then $`A\mathbb{Z}^d = \Lambda`,
$`|\det A| = \operatorname{covol}(\Lambda)` and $`(A^{-1})^{*}\mathbb{Z}^d = \Lambda^*`, where
$`(A^{-1})^*` is the adjoint of $`A^{-1}`; moreover
$`\langle A^{-1}v, n\rangle = \langle v, (A^{-1})^*n\rangle`.
:::

:::proof "lemma_polar_lattice_coordinates"
$`\langle Am, y\rangle = \langle m, A^*y\rangle`, so $`y \in \Lambda^*` iff $`A^*y \in \mathbb{Z}^d`,
i.e. $`y \in (A^*)^{-1}\mathbb{Z}^d = (A^{-1})^*\mathbb{Z}^d`; the covolume of $`A\mathbb{Z}^d` is
$`|\det A|` (Mathlib's `ZLattice.covolume_eq_measure_fundamentalDomain`).
:::

:::lemma_ "lemma_packing_unit_separation" (lean := "SpherePacking.packing_supremum_eq_unit_separation, periodic_packing_supremum_eq_unit_separation")
The constant $`\Delta_d` of {uses "def_packing_density"}[] is the supremum of the upper densities
of the sphere packings of separation exactly $`1`; likewise the periodic packing constant of
{uses "def_periodic_packing_constant"}[] is the supremum over periodic packings of separation
$`1`.
:::

:::proof "lemma_packing_unit_separation"
For $`c > 0` the rescaled packing $`cX` (`SpherePacking.rescaleConfiguration`) has separation
$`cs` and its balls are the images of the original balls under $`x \mapsto cx`. Hence the
proportion of $`B(0,r)` covered by $`cX` equals the proportion of $`B(0,r/c)` covered by $`X`
(`SpherePacking.rescale_densityInsideRadius`), and the limit superior as $`r \to \infty` is the
same for both (`SpherePacking.rescale_upper_packing_density`). Taking $`c = 1/s` normalizes the
separation to $`1` without changing the upper density; for a periodic packing the lattice is
rescaled as well (`PeriodicSpherePacking.rescaleConfiguration`).
:::

:::lemma_ "lemma_periodic_density_formula" (lean := "PeriodicSpherePacking.upperPackingDensity_eq_div_volume_fundamentalDomain, PeriodicSpherePacking.density_eq_numReps_mul_volume_ball_div_covolume, PeriodicSpherePacking.packing_density_zero_of_empty_centers")
Let $`P` be a periodic packing ({uses "def_periodic_packing"}[]) with lattice $`\Lambda`,
separation $`s` and $`N` orbits of centers ({uses "def_center_orbits"}[]), and let $`F` be the
fundamental domain of a $`\mathbb{Z}`-basis of $`\Lambda` (a bounded half-open parallelotope).
Then the upper density of $`P` is a limit, namely
$`\dfrac{N\operatorname{vol}(B(0,s/2))}{\operatorname{vol}(F)}`
$`= \dfrac{N\operatorname{vol}(B(0,s/2))}{\operatorname{covol}(\Lambda)}`,
with the covolume of {uses "def_polar_lattice"}[]; a periodic packing without centers has
density $`0`.
:::

:::proof "lemma_periodic_density_formula"
Let $`L` bound the norm of the points of $`F`. The translates $`F + \lambda`,
$`\lambda \in \Lambda`,
tile $`\mathbb{R}^d` (`PeriodicSpherePacking.exists_unique_vadd_mem_fundamentalDomain`), each
containing exactly $`N` centers ({uses "lemma_center_orbits_finite"}[],
`PeriodicSpherePacking.encard_centers_in_translated_region`).
Counting the translates that meet $`B(0,R)` gives
$`N\,|\Lambda \cap B(0,R-L)| \le |X \cap B(0,R)| \le N\,|\Lambda \cap B(0,R+L)|`
(`PeriodicSpherePacking.nsmul_encard_lattice_le_encard_centers` and
`PeriodicSpherePacking.encard_centers_le_nsmul_encard_lattice`), while comparing the union of the
translates $`F + \lambda` with balls gives
$`\operatorname{vol}(B(0,R-L))/\operatorname{vol}(F) \le |\Lambda \cap B(0,R)|`
$`\le \operatorname{vol}(B(0,R+L))/\operatorname{vol}(F)`
(`PeriodicSpherePacking.volume_div_le_encard_lattice` and
`PeriodicSpherePacking.encard_lattice_le_volume_div`). Since the balls of radius $`s/2` around
the centers are disjoint, the covered proportion of $`B(0,R)` is sandwiched between
$`N\operatorname{vol}(B(0,s/2))/\operatorname{vol}(F)` times the ratios
$`\operatorname{vol}(B(0,R \mp s/2 \mp 2L))/\operatorname{vol}(B(0,R))`
(`densityInsideRadius_le_mul_ratio`, `densityInsideRadius_ge_mul_ratio`), and these ratios tend
to $`1` (`volume_ball_add_div_volume_ball_add_tendsto_one`). Hence the covered proportion
converges (`PeriodicSpherePacking.tendsto_densityInsideRadius`) and its limit superior is the
stated value. The identification of $`\operatorname{vol}(F)` with $`\operatorname{covol}(\Lambda)`
is Mathlib's `ZLattice.covolume_eq_measure_fundamentalDomain`.
:::

# Poisson summation

:::theorem "thm_lattice_poisson_summation" (lean := "SchwartzMap.latticePoissonSummationFormula")
Let $`\Lambda \subseteq \mathbb{R}^d` be a lattice with polar lattice $`\Lambda^*`
({uses "def_polar_lattice"}[]), let $`f` be a complex Schwartz function on $`\mathbb{R}^d`, and
let $`v \in \mathbb{R}^d`. Then, with the Fourier transform of {uses "def_fourier_convention"}[],
$`\displaystyle\sum_{\lambda \in \Lambda} f(v + \lambda)`
$`= \frac{1}{\operatorname{covol}(\Lambda)}\sum_{m \in \Lambda^*}\widehat f(m)\,\mathbf{e}_m(v)`,
$`\mathbf{e}_m(v) = e^{2\pi i\langle v, m\rangle}`,,
both series converging absolutely.
:::

:::proof "thm_lattice_poisson_summation"
Standard lattice. The periodization $`v \mapsto \sum_{n\in\mathbb{Z}^d} f(v+n)`
(`SchwartzMap.PoissonSummation.Standard.periodization`) converges locally uniformly by the
Schwartz decay of $`f` (`summable_norm_restrict_translate`) and descends to a continuous function
on the torus $`(\mathbb{R}/\mathbb{Z})^d` (`torusPeriodization`). Its Fourier coefficient at
$`n \in \mathbb{Z}^d` is $`\widehat f(n)`: unfold the sum over the lattice into an integral over
$`\mathbb{R}^d` of $`f(x)e^{-2\pi i\langle x,n\rangle}` (`mFourierCoeff_torusPeriodization`).
These coefficients are absolutely summable (`summable_mFourierCoeff_torusPeriodization`), because
$`\widehat f` is again Schwartz, so the Fourier series of the periodization converges uniformly
and, the periodization being continuous, converges to it (Mathlib's Fourier inversion on the
torus). Evaluating at $`v` gives the formula for $`\mathbb{Z}^d`, which is self-polar.

General lattice. Let $`A` be the coordinate automorphism of {uses "lemma_polar_lattice_coordinates"}[] and put
$`g = f \circ A` (`SchwartzMap.latticePullback`), a Schwartz function. Then
$`\sum_{\lambda\in\Lambda} f(v+\lambda) = \sum_{n\in\mathbb{Z}^d} g(A^{-1}v + n)`, and the change
of variables $`\widehat{g}(w) = |\det A|^{-1}\widehat f((A^{-1})^*w)` (
`Real.fourier_comp_linearEquiv`,
`SchwartzMap.fourier_latticePullback`) together with $`(A^{-1})^*\mathbb{Z}^d = \Lambda^*`,
$`|\det A| = \operatorname{covol}(\Lambda)` and
$`\langle A^{-1}v, n\rangle = \langle v, (A^{-1})^*n\rangle` (`wInner_latticeCoordinateEquiv_symm`)
turns the $`\mathbb{Z}^d`-formula for $`g` into the formula for $`f`.
:::

# The bound for periodic packings

:::theorem "thm_lp_bound_periodic" (lean := "LinearProgrammingBound'")
Let $`P` be a periodic packing ({uses "def_periodic_packing"}[]) of separation $`1` with lattice
$`\Lambda`, a nonempty set of centers $`X`, and a bounded region $`D` whose $`\Lambda`-translates
tile $`\mathbb{R}^d` (each point lies in exactly one translate). Let $`f` be a nonzero complex
Schwartz function on $`\mathbb{R}^d` that is real valued with real valued Fourier transform
({uses "def_fourier_convention"}[]), such that $`f(x) \le 0` for $`|x| \ge 1` and
$`\widehat f \ge 0`. Then the upper density of $`P` is at most
$`\dfrac{f(0)}{\widehat f(0)}\operatorname{vol}(B(0,1/2))`.
:::

:::proof "thm_lp_bound_periodic"
Let $`X_D = X \cap D` be the $`N` centers in the fundamental region. Since every center is
uniquely $`y + \lambda` with $`y \in X_D` and $`\lambda \in \Lambda`
(`SpherePacking.CohnElkies.fundamentalCentersLatticeProductEquiv`), the double sum of $`f` over
$`X \times X_D` can be written as
$`\sum_{x \in X_D}\sum_{y \in X_D}\sum_{\lambda\in\Lambda} f(x - y + \lambda)`
(`SpherePacking.CohnElkies.center_double_sum_eq_region_lattice_sum`). For $`x \ne y`, or for
$`x = y` and $`\lambda \ne 0`, the point $`x - y + \lambda` is a difference of distinct centers,
so it has norm at least $`1` and $`f` is nonpositive there; hence each inner lattice sum is at most
$`f(0)` if $`x = y` and at most $`0` otherwise
(`SpherePacking.CohnElkies.real_lattice_sum_bounded_by_origin_term`), and the double sum is at
most $`N f(0)` (`packing_bound_auxiliary_estimate`).

On the other hand, Poisson summation {uses "thm_lattice_poisson_summation"}[] applied to each
inner sum with $`v = x - y`, followed by an exchange of the finite sums over $`x, y` with the
absolutely convergent spectral sum (`SpherePacking.CohnElkies.packing_spectral_sum_exchange`),
identifies the double sum with
$`\dfrac{1}{\operatorname{covol}(\Lambda)}\sum_{m\in\Lambda^*}\widehat f(m)\,|S(m)|^2`,
$`S(m) = \sum_{x\in X_D}e^{2\pi i\langle x,m\rangle}`,
(`packing_bound_geometric_estimate`). Every term is nonnegative because $`\widehat f \ge 0`
(`SpherePacking.CohnElkies.nonnegative_weighted_nonzero_frequency_sum`), and the term $`m = 0`
equals $`N^2\widehat f(0)/\operatorname{covol}(\Lambda)` (`packing_bound_spectral_estimate`).
Combining the two estimates gives $`N/\operatorname{covol}(\Lambda) \le f(0)/\widehat f(0)`, and
the density formula {uses "lemma_periodic_density_formula"}[] turns this into the claim.
:::

# From arbitrary to periodic packings

:::theorem "thm_periodic_packing_constant" (lean := "periodic_packing_supremum_eq_unrestricted, SpherePacking.exists_periodic_unit_packing_above_density_threshold")
For every $`d \ge 1` the periodic packing constant of {uses "def_periodic_packing_constant"}[]
equals $`\Delta_d` ({uses "def_packing_density"}[]). More precisely, for every sphere packing
$`S` of separation $`1` and every $`b` below the upper density of $`S` there is a periodic
packing of separation $`1` with upper density above $`b`.
:::

:::proof "thm_periodic_packing_constant"
Periodic packings are packings, so the periodic constant is at most $`\Delta_d`; by
{uses "lemma_packing_unit_separation"}[] it suffices to prove the second statement. Let $`X` be
the centers of $`S`. For $`L > 0` consider the cube $`C_L = [0,L)^d` (`axisAlignedCell`), the
cubic lattice $`\Lambda_L = L\mathbb{Z}^d` (`axisCellLattice`), whose translates of $`C_L` tile
space, and the inset cube $`[1/2, L-1/2]^d` (`insetAxisAlignedCell`). For a translate
$`g + C_L`, $`g \in \Lambda_L`, keep the centers $`x \in X \cap (g + C_L)` whose ball
$`B(x,1/2)` lies inside $`g + C_L`, and repeat them $`\Lambda_L`-periodically
(`latticeReplicatedCenters`): since the balls of the kept centers lie in one tile and the tiles
are disjoint, distinct replicated centers are still at distance at least $`1`, so this is a
periodic packing of separation $`1` (`replicateToPeriodicPacking`). By
{uses "lemma_periodic_density_formula"}[] its density is
$`|X_{\mathrm{kept}}|\operatorname{vol}(B(0,1/2))/L^d`, and the discarded centers lie in the
boundary shell $`[-1/2, L+1/2]^d \setminus [1, L-1]^d` (`boundaryShell`), whose volume is
$`(L+1)^d - (L-2)^d = o(L^d)` (`volume_boundaryShell`, `tendsto_volume_boundaryShell_div_cell`).
Averaging over the translates $`g + C_L` meeting a large ball $`B(0,R)`
(`lattice_count_mul_volume_cell_le_volume_ball`) and using that the covered proportion of
$`B(0,R)` exceeds $`b` for arbitrarily large $`R`, one finds $`L` and $`g` for which the kept
centers alone give density above $`b` (`exists_replicated_packing_density_eq`).
:::

:::theorem "thm_lp_bound" (lean := "LinearProgrammingBound")
(Cohn–Elkies linear programming bound.) Let $`f` be a nonzero complex Schwartz function on
$`\mathbb{R}^d` that is real valued with real valued Fourier transform
({uses "def_fourier_convention"}[]), such that $`f(x) \le 0` for $`|x| \ge 1` and
$`\widehat f \ge 0`. Then
$`\Delta_d \le \dfrac{f(0)}{\widehat f(0)}\operatorname{vol}(B(0,1/2))`,
with $`\Delta_d` from {uses "def_packing_density"}[]. No radiality is assumed.
:::

:::proof "thm_lp_bound"
By {uses "thm_periodic_packing_constant"}[] and {uses "lemma_packing_unit_separation"}[],
$`\Delta_d` is the supremum of the upper densities of the periodic packings of separation $`1`,
so it suffices to bound each of them. A periodic packing without centers has density $`0`. For a
periodic packing $`P` with centers, choose a $`\mathbb{Z}`-basis of its lattice
(`PeriodicSpherePacking.canonicalPackingLatticeBasis`); its fundamental domain is bounded
(`PeriodicSpherePacking.fundamental_region_admits_norm_bound`) and its lattice translates tile
space (`PeriodicSpherePacking.basis_region_translates_cover_uniquely`), so
{uses "thm_lp_bound_periodic"}[] applies to $`P` and gives the bound.
:::

The bridge from this statement to equation (4) of the report is short: for $`f \in \mathcal{A}_d`
the hypotheses hold, $`\operatorname{vol}(B(0,1/2)) = v_d/2^d`
(`PackingBounds.PackingBridge.volume_half_ball`), and taking the infimum over $`f` gives
$`\Delta_d \le \mathrm{LP}_d` ({bpref "eq_4_cohn_elkies_bound"}[]). Note that the formal packing
constant lives in $`[0,\infty]`, so these inequalities are stated with the real right-hand sides
coerced by `ENNReal.ofReal`; that $`\Delta_d \le 1` is `SpherePacking.upper_packing_density_le_one`
for every packing.
