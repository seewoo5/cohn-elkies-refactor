# Refactoring notes

Working log for the refactoring of `SpherePacking.lean` (OpenAI ten-proofs, commit `94bc0fe`,
55,616 lines, 2,218 declarations, no `sorry`, standard axioms) following `RefactoringPlan.md`.
The references used are the report (`ten-proofs-oai.pdf`, Chapter 1 and Appendix A), the
walkthrough notes (`reasoning-walkthroughs.pdf`, Chapter 1) and the two blog posts.

## 0. Starting point (measured on the original file)

| Quantity | Value |
|---|---|
| Lines | 55,616 (2,822 blank; no docstrings, no comments) |
| Lines of length ≤ 60 characters | 49,979 (90 %) |
| Declarations | 2,218 (1,807 theorems, 375 defs, 10 structures, 20 instances) |
| Theorems never used elsewhere in the file | 69 (1,037 lines) |
| Theorems used exactly once | 1,127 (34,566 lines) |
| Longest declaration | `horizontalStrip_norm_extension_majorization` (271 lines) |

Names of the report that were *not* formalized: the Schwartz/radial reduction of §2.1 for `L¹`
eigenfunctions, Proposition 3.1 in its general form (both eigenvalues, no sign hypothesis),
Proposition 3.7 for `L¹` functions, the self-Fourier function `f₀`, the constants `A₊(d)`,
`A₋(d)`, Theorem 1.2, and Appendix A.

## 1. Step 1 — the golfed single file `SpherePackingRefactored.lean`

(filled in as the work progresses)

### 1.0 Result in numbers (final state, 2026-09-14)

| | lines |
|---|---|
| original `SpherePacking.lean` | 55,616 |
| `CohnElkies/` after golfing, before the new theorems (Step 1, 52 modules) | 24,242 (−56 %) |
| final `CohnElkies/` (53 modules, including the new material: `SignUncertainty/*` ≈ 2,350 lines, `UpperBound/SelfFourier` ≈ 220, Propositions 3.1/3.7) | 24,647 |
| final `CohnElkiesForMathlib/` (12 modules) | 2,169 |
| total (single file `SpherePackingRefactored.lean`, assembled from both) | 26,816 (−52 %) |

Excluding the newly formalized material (≈ 2,700 lines), the refactored code is ≈ 57 % shorter
than the original. The whole library compiles with the lakefile options
(`maxSynthPendingDepth = 3`, Mathlib's standard linter set) under the default `maxHeartbeats`,
with no `set_option backward.*`, no `sorry`, no axiom beyond `propext`, `Classical.choice`,
`Quot.sound`. After the cleanup pass (§2.3) the only warnings left are the five `sorry`s of the
comparator challenge file (by design) and three `linter.unnecessarySeqFocus` hits in
`Parameters.lean`, where the suggested `(tac1; tac2)` does not work because `simp` already closes
one of the two `Complex.ext` goals. The lakefile option
`maxSynthPendingDepth = 3` (inherited from the original project) is still needed by at least one
proof (`SignUncertainty/SchwartzFamily.lean`); it is applied by `lake build` but not by a bare
`lake env lean <file>`. The single file is the library `SpherePackingRefactored`
(`lake build SpherePackingRefactored`), assembled by the scratchpad script `assemble.py` from the
modules in topological order, each wrapped in a named section.

### 1.1 Method

The refactoring was carried out on a modular copy of the file and the single file
`SpherePackingRefactored.lean` is assembled from the modules at the end (Step 2 modules are
therefore the primary artefact; the single file is their concatenation with imports removed).

1. *Mechanical split.* The original file was cut at (balanced) section boundaries into 52
   modules forming an import chain; each cut reproduces the exact scope stack (namespaces,
   sections, `open`/`variable`/`set_option` commands in force) so the modules compile with no
   change of meaning. Verified by a full build.
2. *Mechanical reformatting.* A conservative line joiner rewrote the ~65-column source to
   100 columns (mathlib width), joining continuation lines only where a newline is not
   syntactically significant (not inside `by`/`=>`/`calc`/structure-instance blocks, not into
   `·` bullets or `|` alternatives, not after `let`/tactic combinators). Every module was
   re-checked with `lake env lean`. Effect: 56,056 → 40,011 lines (−28 %) with unchanged proofs.
3. *Global scripted pass.* Renaming table (see §1.2), `Real.pi → π`, `Complex.I → I`,
   `Real.sqrt → √`, and iterated deletion of declarations that are never used.
4. *Per-module golfing* by parallel agents with a fixed contract: declarations used by later
   modules keep their name and statement, everything else may be inlined, merged or removed;
   proofs are golfed; Mathlib lemmas replace local reproofs; plus/minus duplicates become
   statements generic in the polynomial `P`.
5. *Semantic changes* (two-sign generalization of Proposition 3.1/3.7, generic polynomial `P`
   and `f₀`, digamma via Mathlib, new statements of §1.6), then module reorganization,
   `mathlib-quality:cleanup`, and the blueprint.

### 1.2 Renaming table (report notation ↔ Lean)

Lean 4 identifiers cannot contain `λ` (a keyword), `₊`, `₋`, or superscripts, and single
letters such as `A`, `B`, `Q`, `b`, `v`, `V`, `E` occur as bound variables in hundreds of
declarations. Hence: `ℓ` stands for `λ = d/2`; `Aε`, `Bε`, `Qε`, `a₀ε`, `bε` for the
ε-dependent parameters; `PPlus`/`PMinus`/`fPlus`/`fMinus` for `P₊`/`P₋`/`f₊`/`f₋` (with the
notations `P₊`, `P₋`, `f₊`, `f₋`, `f₀` available for statements). Definitions renamed globally
(theorem names were renamed module by module, see the per-module notes):

| Report | Original Lean name | New Lean name |
|---|---|---|
| LP_d (3) | `linearProgram` | `LP` |
| a₀ (34) | `shortCutoff` | `a₀ε` |
| A (34) | `shortEndpoint` | `Aε` |
| B (34) | `shellLocation` | `Bε` |
| Q (34) | `shellWeight` | `Qε` |
| b(a) (34) | `shortMargin` | `bε` |
| β (34) | `beta` | `β` |
| w_s (35) | `shortShellDensity` | `w_s` |
| w_B (35) | `positiveShellDensity` | `w_B` |
| h_ε (36) | `mellinShellPhase` | `h_ε` |
| h_ε(iu) (real) | `realHyperbolicShellPhase` | `h_εI` |
| P₊ (38) | `plusPolynomial` | `PPlus` |
| P₋ (38) | `minusPolynomial` | `PMinus` |
| E_λ(t) (38) | `saddleEnvelope` | `E` |
| X_{f₊}(t) (38) | `plusSaddleSpectrum` | `XPlus` |
| X_{f₋}(t) (38) | `minusSaddleSpectrum` | `XMinus` |
| E_λ in the variable z = λ − it | `saddleMellinEnvelope` | `mellinEnvelope` |
| M_{f₊}(z) | `plusSaddleMellinData` | `MPlus` |
| M_{f₋}(z) | `minusSaddleMellinData` | `MMinus` |
| f₊(r) (38) | `plusSaddleProfile` | `fPlus` |
| f₋(r) (38) | `minusSaddleProfile` | `fMinus` |
| x ↦ f₊(|x|) | `plusSaddleFunction` | `fPlusFun` |
| x ↦ f₋(|x|) | `minusSaddleFunction` | `fMinusFun` |
| f₊(0) = f₋(0) (42) | `saddleOriginValue` | `originValue` |
| ψ = Γ'/Γ | `saddleDigamma` | `digamma` |
| v(u) (44) | `saddleLogRadius` | `logRadius` |
| R_{ε,d} (Thm 4.1) | `saddleSourceRadius` | `R_ε` |
| u_* (43) | `saddleSmallRadiusStarOrdinate` | `u_star` |
| r_* = e^{v(u_*)} | `saddleSmallRadiusStar` | `r_star` |
| N (Lemma 4.10) | `saddleSmallResidueTruncation` | `N_ℓ` |
| y = π e^{2h₁'} r² (Lemma 4.10) | `saddleSmallRadiusVariable` | `y_r` |
| A_{λ,n} (78) | `plusSaddleSmallRadiusCoefficient` | `A_ℓn` |
| h₁' (Lemma 4.10) | `saddleShellDerivativeOne` | `h₁'` |
| θ = π(1+σ)/2 (15) | `stripAngle` | `θ` |
| P_σ (15) | `stripPoissonKernel` | `P_σ` |
| M_σ (15) | `stripBottomMass` | `M_σ` |
| h_λ (14) | `lowerGammaBoundaryLog` | `h_ℓ` |
| H_σ (18) | `lowerStripPoissonMajorant` | `H_σ` |
| h_{λ,D} (Lemma 3.2) | `lowerGammaBoundaryCapped` | `h_ℓD` |
| f_T (Lemma 3.3) | `lowerRiemannLog` | `f_T` |
| K_λ (holomorphic Poisson kernel, blog) | `stripHolomorphicPoissonKernel` | `K_ℓ` |
| K̃_λ | `stripRegularizedHolomorphicPoissonKernel` | `K'_ℓ` |
| W[b] | `stripRegularizedOuter` | `W_b` |
| W_D | `lowerStripCappedGammaOuter` | `W_D` |
| μ_{λ,η} (37) | `upperGammaMeasureDensity` | `μ_ℓ` |
| V_γ (48) | `upperGammaVariance` | `V_γ` |
| third moment of μ_{λ,η} (48) | `upperGammaThirdMoment` | `M₃_γ` |
| V(u) (44) | `saddleSourceGaussianVariance` | `V_u` |
| S_d | `radialSurfaceArea` | `sphereArea` |
| ‖g‖₁ | `radialL1Mass` | `L1norm` |
| φ (12) | `normalizedRadialLogProfile` | `φ_g` |
| Z (12) | `normalizedRadialMellinStrip` | `Z_g` |
| X_f (8), complex argument | `radialMellinStrip` | `X_f` |
| m_λ (10) | `mellinMultiplier` | `m_ℓ` |
| v(u) with real λ | `saddleSourceStationaryLogRadius` | `vℓ` |
| anti-self-Fourier witness (Thm 3.8) | `AntiFourierWitness` | `AntiSelfFourierWitness` |
| α_ε = lim R_{ε,d}/√d (84) | `limitingSaddleRadius` | `α_ε` |
| z = λ(1+u) − iλT | `saddleSourceMellinContour` | `z_contour` |
| e^{L_u(T)} (46) | `saddleSourceCenteredEnvelope` | `expL` |
| G_{λ,η} (45) | `upperGammaCenteredPhase` | `G_ℓη` |
| L_u (46) | `saddleSourceCenteredPhase` | `L_u` |
| D_γ (45) | `upperGammaDamping` | `D_γ` |
| D_u (47) | `upperSaddleDamping` | `D_u` |
| D_s (49) | `upperShortShellDamping` | `D_s` |
| D_B (49) | `positiveShellDamping` | `D_B` |
| V_s (49) | `upperShortShellVariance` | `V_s` |
| V_B (49) | `upperPositiveShellVariance` | `V_B` |
| M₃ (48) | `upperSaddleThirdMoment` | `M₃` |
| X for a profile | `mellinFrequency` | `Xline` |
| X_f(t) (8) | `radialMellinFrequency` | `X_fℝ` |

### 1.3 Differences from the report that were kept (proof arguments)

The formalized proofs follow the report's strategy; where the original Lean file proved a step by
a different argument, that argument was kept (rewriting it would not make the file more readable).
The blueprint (Step 3) has a chapter "Report versus formalization" with the precise statements;
the list:

- **Lemma 3.2, interior bound (Poisson principle → Phragmén–Lindelöf).** The report maps the strip
  to the upper half-plane and applies the Poisson principle to `log|Z|`. The formalization stays on
  the strip: it builds the holomorphic Poisson integral `W_D` of the capped majorant `h_{λ,D}`
  (`CohnElkies/LowerBound/CappedMajorization.lean`) and applies a Phragmén–Lindelöf maximum
  principle for a horizontal strip to `e^{-W_D} Z`
  (`horizontalStrip_norm_extension_majorization` in `LowerBound/PhragmenLindelof.lean`), where only
  the *modulus* of the function is assumed to extend continuously to the closed strip. Mathlib's
  `PhragmenLindelof.horizontal_strip` cannot be used directly for that reason (it needs
  `DiffContOnCl`). The uncapped bound is recovered by dominated convergence in `D`.
- **Lemma 3.3 (one-sided).** Only the upper half of the two-sided Riemann-sum estimate (19) is
  proved, with a unified error term for even and odd `d` (`LowerBound/CenteredMax*.lean`).
- **Lemma 3.5 (single tail majorant).** Instead of integrating the bounds (24), (25) separately
  over `|s| ≤ Bλ` and `|s| > Bλ`, the two are averaged into one inverse-quadratic majorant
  `exp H_σ(λS) ≤ C e^{-γλ} (1+|S|)^{-2}` (`LowerBound/CappedMajorant.lean`, `LowerBound/Main.lean`).
- **Lemma 4.8 / Corollary 4.9 (strict inequality instead of asymptotic).** The saddle-point lemmas
  conclude with the uniform strict bound `|I_{λ,P}(u) - P(iu)√(2π/(λV(u)))| < |P(iu)|√(2π/(λV(u)))`
  on the stated ranges, which is what the sign conclusions need, rather than the full relative
  asymptotic; the radius coverage uses continuity of `v` and the intermediate value theorem, not
  strict monotonicity (`UpperBound/SaddleTails*.lean`, `UpperBound/Coverage.lean`).
- **Lemma 4.10 (positivity form).** The residue truncation is stated as the two bounds
  `e^y |S_N(y) - e^{-y}| < ½`, `e^y |𝓡_λ(r)| < ½` uniformly on `0 ≤ r ≤ r_*`, whose sum gives
  `f₊(r)/f₊(0) > 0`, instead of the relative asymptotic (82) (`UpperBound/SmallRadius*.lean`).
- **Lemma 3.4 / equation (22).** The digamma log-moment identity (22) is not used: the limit
  `lim_{σ↑1} J_σ` is computed through a Frullani/Wallis-kernel integral
  (`integral_poissonLogistic_mul_wallisPhaseKernel`, `LowerBound/LimitingDensity.lean`), and the
  endpoint expectation is normalized so that the limiting value reads `log(π/2) − 1`
  (`limitingPoissonEndpointExpectation_eq_log_pi_div_two_sub_one`); the conclusion (23) is the same.
- **Theorem 1.1, upper half.** The `limsup ≤ √(e/2π)` half is not a separate theorem: it is fused
  with the lower bound in the sandwich argument of `Asymptotics/Framework.lean`
  (`sharpQuotient_of_uniform_lower_and_ordered_upper`).
- **Cohn–Elkies bound.** The report cites `Δ_d ≤ LP_d` as an external input; the formalization
  proves it (`SpherePacking/CohnElkiesBound.lean`, via Poisson summation and the reduction to
  periodic packings from the Sphere-Packing-Lean project).
- **Stirling input.** Mathlib has Stirling's formula for `n!` but not for `Real.Gamma`; the
  asymptotics of `v_d^{1/d} √d` are therefore derived from `Stirling.tendsto_stirlingSeq_sqrt_pi`
  through an even/odd split in `d` (`Asymptotics/Stirling.lean`).
- **Rotational average.** The report writes `ℛf(x) = ∫_{O(d)} f(Ux) dU`; the formalization uses
  `∫_{O(d)} f(U⁻¹x) dU` (inherited from the original file and kept). The two agree, since the Haar
  measure of the compact group `O(d)` is inversion invariant, and only *left* invariance is needed
  for the rotation invariance of the average in the `U⁻¹` form, which is what Mathlib's
  `IsHaarMeasure` supplies. See §5.1.
- **Radial reduction.** The passage from unrestricted to radial admissible functions (report §2.1)
  is done by averaging over the Haar probability measure of `O(d)` exactly as in the report
  (`Radialization.lean`, `Admissible/Radialization.lean`); no change.

### 1.4 Parameter choices

The original file used larger safety margins than the report (§4, equation (34)): `a₀ = ε³`
instead of `ε²`, `A = 10 log(1/ε)` instead of `log(1/ε)`, `b(a) = 1 − 10ε(1+a)` instead of
`1 − 2ε(1+a)`, and the residue cutoff `N = ⌈20 log λ⌉` instead of `⌈log λ⌉` (Lemma 4.10). After the
main refactor each of the four was switched to the report's value, one at a time (on an isolated
copy, then merged): **all four go through**, and the final code uses exactly the report's
parameters (`CohnElkies/Parameters.lean`, `N_ℓ` in `UpperBound/SmallRadius.lean`):

| quantity | report | Lean (now) | what the old margin had been used for |
|---|---|---|---|
| `u_*, u₀, U, B, Q, β`, window exponent `1/12` | as in (34)/(43) | same | — |
| `N` (Lemma 4.10) | `⌈log λ⌉` | same | `(1/2)^{N+1} ≤ e^{-10 log λ}` in the factorial-tail majorant; with `N ≥ log λ` the majorant is `exp(3C − log λ/8)`, still `→ 0` because the window costs only `λ^{3/8}` |
| `a₀` | `ε²` | same | only `a₀ → 0` and the ratio of Lemma 4.6 (`1/a₀` against the Gaussian `e^{-x²/8}`) |
| `A` | `log(1/ε)` | same | only `A → ∞`, `ε(1+A) → 0` and `e^{εA/2}` in the ratio of Lemma 4.6 |
| `b(a)` | `1 − 2ε(1+a)` | same | the damping margin of Lemma 4.2/(54): `b(a) e^{(u−1)a} cosh(ua)/cosh a ≤ 1 − cε`; with the report's taper `c = 4` is false near `a = 0`, so the absolute constant is `c = 2` (the report only says "absolute constants `ε₀, c, C`"), and the constants derived from it were adjusted downstream (`2ε D_γ ≤ D_u`, `V_s ≤ (1−2ε) V_γ`, `εℓ/(4e)` in the damping bound, the cubic-window constants, the negative-contour Gamma majorant) |

Changed modules: `Parameters`, `UpperBound/{WallisRadius, ShellEstimates, SaddleDamping,
SaddleContour, SaddleTails, GaussianError, SmallRadius}` (−163/+164 lines); no statement used
outside these modules changed; the limiting radius constant `1/π` is untouched.

### 1.5 Mathlib reuse

Hand-rolled material replaced by Mathlib (details per module in the golfing notes below):

- **Special functions.** `Real.digamma` (the file defined `saddleDigamma` as `(log ∘ Γ)'` and
  reproved its properties), `Real.Gamma_nat_add_one_add_half`, `Real.Wallis`
  (`Real.Wallis.W`, `Real.Wallis.tendsto_W_nhds_pi_div_two` for the radius normalization),
  `Stirling.tendsto_stirlingSeq_sqrt_pi`, `Stirling.log_stirlingSeq_formula`,
  `Real.log_two_gt_d9`, `Real.isLittleO_log_id_atTop`, `Real.one_lt_cosh`, `Real.cosh_le_cosh`.
- **Fourier analysis.** `fourier_gaussian_innerProductSpace`, `Real.fourier_comp_linearEquiv`
  usage pattern (candidate for Mathlib), `UnitAddTorus.mFourierCoeff_eq_integral`,
  `UnitAddTorus.integral_preimage`, `QuotientAddGroup.isOpenQuotientMap_mk`,
  `IsOpenQuotientMap.piMap` (Poisson summation on the torus).
- **Complex analysis.** `hasDerivAt_ofReal_cpow_const`, `Complex.re_add_im`, `Complex.exp_conj`,
  `RCLike.re_to_complex`; the strip maximum principle is structured along
  `PhragmenLindelof.horizontal_strip`.
- **Measure theory / integration.** `integral_gaussian`, `integral_add_compl`,
  `setIntegral_mono_set`, `integral_sub_left_eq_self`, `Measure.integral_comp_mul_left`,
  `integral_eq_zero_iff_of_nonneg`, `integral_re`/`integral_im`, `Integrable.of_bound`,
  `Integrable.congr`, `Measure.haarMeasure_self`, the `IsHaarMeasure`/`IsProbabilityMeasure`
  instance paths on `O(d)`.
- **Sphere packings / lattices.** `measure_ball_pos`, `measure_ball_lt_top`,
  `Measure.finite_const_le_meas_of_disjoint_iUnion`, `ZSpan.setFinite_inter`, `ZLattice.rank`,
  `Homeomorph.smulOfNeZero`, `Measure.addHaar_ball`, `Metric.finite_isBounded_inter_isClosed`.
- **Asymptotics / topology.** `IsBigO.of_bound`, `Filter.Tendsto.congr'`,
  `Tendsto.atTop_div_const`, `Real.pow_rpow_inv_natCast`, `Real.exp_half`, `Real.sqrt_div`,
  `Convex.linear_preimage`, `abs_le_one_iff_mul_self_le_one`.

Material with **no** Mathlib counterpart, kept in the project and marked as Mathlib candidates
(Step 2 moves them to `CohnElkiesForMathlib/`): Stirling asymptotics for `Real.Gamma`, the
`ENat`-valued infinite sum API, the Phragmén–Lindelöf principle for a strip with a merely
continuous modulus, the Poisson kernel of a strip, the Fourier transform under a linear
equivalence, convolution of symmetric decreasing functions, Poisson summation for a general
lattice with Schwartz functions.

### 1.6 Newly formalized statements

- **Radial reduction (report §2.1) and the non-radial admissible class.** On the owner's request the
  class `Admissible` lost its `radial` field: it is now the report's `𝒜_d` (the comparator's
  `PackingBounds.FullAdmissible`), the radial subclass is `RadialAdmissible`, and the module
  `CohnElkies/Admissible/Radialization.lean` proves that the rotational average `Admissible.radialize f`
  of an admissible function is radial admissible with the same `f(0)/𝓕f(0)` and remains nonpositive
  outside any ball where `f` is (`radialize_nonpos_of_le_norm`), hence `LP_eq_radial`; Theorem 3.8
  and Theorem 1.1 are stated for all of `𝒜_d`. Details and the rename table: §5.
- **Two-sign lower bound (Propositions 3.1 and 3.7, Schwartz case).** The original file's
  `AntiSelfFourierWitness d R` (real radial Schwartz `f ≠ 0`, `𝓕 f = -f`, `f 0 = 0`, `f ≥ 0` outside
  the ball of radius `R`) is now a special case of
  `RadialEigenfunction d ς` (`ς : ℤˣ`, fields `real`, `radial`, `ne_zero`,
  `fourier_eq : 𝓕 g = (ς : ℂ) • g`, `zero : g 0 = 0`), and the whole Mellin-strip chain of §3 is
  stated for it (the eigenvalue enters only through `∫ g = 𝓕 g 0 = ς g 0 = 0` and `|ς| = 1` in the
  bottom-boundary identity (17)). New theorems in `CohnElkies/LowerBound/Main.lean`:
  `exists_interior_mass_bound` (Proposition 3.1: `∃ C γ > 0, ∀ᶠ d, ∀ ς g, ∫_{‖x‖<c√d} |g| ≤
  C e^{-γ d} ‖g‖₁` for `0 < c < π⁻¹`), `eventually_not_nonneg_outside` (Proposition 3.7 for
  Schwartz eigenfunctions of either sign), and the identity (13)
  `setIntegral_Iic_abs_logProfile : ∫_{v ≤ 0} |φ_g| = (∫_{‖x‖<R} |g|)/‖g‖₁`
  (`LowerBound/LogProfile.lean`); the former `uniformAntiFourierSignRadius` is a two-line corollary.
- **Generic saddle polynomial and the self-Fourier function `f₀` (Lemma 4.3, Corollary 4.9 for
  `P₀`).** The upper construction is now stated once for a polynomial `P` with the hypotheses
  actually used: `IsSaddlePolynomial ε P` (entire, `‖P z‖ ≤ (1+|β|)(1+‖z‖)³`,
  `conj (P z) = P (-conj z)`) and, on the saddle range `u ≥ u₀`, `SaddleRangeBounds P u₀`
  (`0 < ‖P(iu)‖`, `‖P(T+iu) − P(iu)‖ ≤ C(|T|+|T|³)‖P(iu)‖`); the objects `spectrum` (`X_P`),
  `mellinData`, `mellinProfile` (`f_P`, with a prescribed origin value), `mellinProfileSchwartz`,
  `fourier_eq_of_mellinProfile` (`𝓕 f_P = f_Q` when `P(−z) = Q(z)`), and the sign chain
  `eventually_mellinProfile_re_mul_pos_of_radius` (`0 < s·Re f_P(r)` for `r ≥ R_{ε,d}` whenever
  `0 < s·Re P(iu)` on the range) replace about forty `plus…`/`minus…` pairs; `f₊`, `f₋` are the
  specializations `P = P₊, P₋` (by `rfl`). The new module `CohnElkies/UpperBound/SelfFourier.lean`
  defines `PZero z = -(1+z²)`, `XZero`, `MZero`, `fZero` (origin value `0`, since
  `P₀(−i) = 0` kills the residue at `z = 0`), the Schwartz realization `zeroSaddleSchwartz` with
  `fourier_zeroSaddleSchwartz : 𝓕 f₀ = f₀` (from `P₀(−z) = P₀(z)`), and the strict exterior
  positivity `eventually_fZero_re_pos_of_radius` (for all small `ε`, large `d`, `r ≥ R_{ε,d}`),
  bundled as `eventually_exists_radialEigenfunction_fZero : ∃ g : RadialEigenfunction d 1, …`.
  Since `P₀` has degree 2, its range bounds are proved directly rather than through the degree-3
  machinery of Lemma 4.4. The strict version `eventually_fMinus_re_neg_of_radius` was added.
- **The `L¹` class, `A₊(d)`, `A₋(d)` and the lower bound of Theorem 1.2 (report §2.1 and
  Proposition 3.7).** `SignEigenfunction d ς` (comparator block of `Basic.lean`) is the class (6)
  represented by continuous Fourier-inversion representatives: `𝓕 g = ς g` is required pointwise,
  which forces `g = ς 𝓕 g` to be continuous (`SignEigenfunction.continuous`,
  `CohnElkies/SignUncertainty/Basic.lean`); `signRadius g = r(g)` and
  `signUncertaintyConstant ς d = A_ς(d)` are `ℝ≥0∞`-valued infima (scoped notations `A₊`, `A₋`).
  The reduction of §2.1 is formalized in `CohnElkies/SignUncertainty/`:
  `Radialization.lean` (the rotational average `rotationalAverage g x = ∫ g (U⁻¹ x) dU` over the
  Haar probability measure of `O(d)`: continuous, integrable, radial, `𝓕(Rg) = R(𝓕 g)`,
  `‖Rg‖₁ ≤ ‖g‖₁`, signs preserved; `SignEigenfunction.rotationalAverage_ne_zero` for an
  eigenfunction nonnegative outside a ball, via the entire Fourier–Laplace transform along rays
  and `fourier_eq_zero_of_eq_zero_outside`, the signed version of the compact-support lemma; the
  eigenfunction `SignEigenfunction.radialize` with `signRadius_radialize_le`),
  `L1Approximation.lean` (continuity of translation in `L¹`, Young's inequality, approximate
  identities), `SchwartzFamily.lean` (parametric integrals of Schwartz families are Schwartz;
  `schwartzConvolution`), `Mollifiers.lean` (the Gaussians `κ_n`, `η_n`, flat bump mollifiers),
  `Radialization.lean` also carries the radial reduction for the constants themselves,
  `signUncertaintyConstant_eq_radial : A_ς(d) = ⨅ (g : SignEigenfunction d ς) (_ : g radial),
  signRadius g` (report §2.1), with the helper `exists_nonneg_outside_of_signRadius_lt_top`;
  `SchwartzApproximation.lean` (`approximant` `q_n`, `projected` `p_n`, `eigenProjection`,
  `exists_schwartz_approximation`: radial Schwartz eigenfunctions `g_n` with `g_n 0 = 0` and
  `g_n → g` in `L¹`) and `LowerBound.lean` (`eventually_not_nonneg_outside_signEigenfunction`,
  Proposition 3.7 for the `L¹` class; `eventually_ofReal_le_signUncertaintyConstant`:
  `c √d ≤ A_ς(d)` eventually for `c < π⁻¹`; `le_liminf_signUncertaintyConstant_div_sqrt`).
  Deviation from the report (documented in the module docstrings): the convolution uses a compactly
  supported normalized bump `φ_n` instead of the Gaussian `κ_n` (so `q_n = (η_n g) ⋆ φ_n` is a
  test function by `schwartzConvolution`; the Gaussians enter through
  `𝓕 q_n = ς (g ⋆ κ_n) 𝓕 φ_n`), and the corrector `ψ_ς` is `φ + ς 𝓕 φ` for a bump `φ` (or its
  dilate by 2) rather than the Gaussian/Hermite functions `ψ_±`.
- **Theorem 1.2** (`CohnElkies/SignUncertainty/UpperBound.lean`, `Main.lean`). Upper bound: a
  `RadialEigenfunction d ς` that is nonnegative outside the ball of radius `R` yields a
  `SignEigenfunction d ς` (its real part) with `signRadius ≤ R`
  (`RadialEigenfunction.signUncertaintyConstant_le_of_nonneg_outside`); applied to `f₊ − f₋`
  (`= antiFourierPart f₋`, eigenvalue `−1`, positive outside `R_{ε,d}` by `f₊ ≥ 0 > f₋`) and to
  `f₀` (eigenvalue `+1`) this gives `A_ς(d) ≤ R_{ε,d}` eventually
  (`eventually_signUncertaintyConstant_le`), hence
  `limsup A_ς(d)/√d ≤ α_ε → π⁻¹` (`limsup_signUncertaintyConstant_div_sqrt_le`). Combined with the
  lower bound: `signUncertaintyConstant_div_sqrt_tendsto (ς) : Tendsto (fun d ↦ A_ς(d) / ofReal √d)
  atTop (𝓝 (ofReal π⁻¹))` in `ℝ≥0∞` (the comparator statement), with the corollaries
  `eventually_signUncertaintyConstant_lt_top` and the real-valued
  `tendsto_toReal_signUncertaintyConstant_div_sqrt : (A_ς(d)).toReal / √d → π⁻¹`.
  All four new results depend only on `propext`, `Classical.choice`, `Quot.sound`.

**Appendix A is deliberately not formalized** (decision of the project owner, 2026-09-13).
Proposition A.1 constructs, from an anti-self-Fourier `L¹` function `g` with `g(0) = 0`, the
self-Fourier function `T_d g(x) = (λ/2)∫_1^∞ t^{λ-1} g(tx) dt` with a strictly smaller last-sign
radius, and deduces `A₊(d) < A₋(d)`. The deduction of the strict inequality uses the existence of
an extremizer for `A₋(d)` (Cohn–Gonçalves 2019, Theorem 1.4), whose proof (weak compactness in
`L²`, Mazur's lemma, Fatou, and a uniform negative-mass bound from Jaming's form of Nazarov's
uncertainty principle) is not part of the report; without it only `A₊(d) ≤ A₋(d)` would follow.
Neither Proposition A.1 nor the inequality is stated in Lean; the blueprint keeps the appendix
as informal text marked as not formalized.

## 2. Step 2 — module layout

Done 2026-09-14. The 63 modules of Step 1 formed a linear import chain in the order of the
original file, interleaving lower-bound and upper-bound material. The textual usage analysis
(scratchpad `depgraph.py`) showed the real structure is a DAG, and the tree was reorganized
accordingly: every module now has minimal imports, the lower and upper bounds are importable
independently of each other, the numbered fragments were merged into modules named after their
content (none above 1,500 lines; every file starts with a module docstring citing the report
sections it covers), and the two `set_option backward.*` lines inherited from the original file
were removed from all modules (51 compiled unchanged, 2 needed small proof adjustments, no
statement changed). Totals: `CohnElkies/` 53 modules, 24,833 lines; `CohnElkiesForMathlib/` 12
modules, 2,193 lines.

### 2.1 `CohnElkies/` (namespace `CohnElkies` unless noted)

| module | content |
|---|---|
| `Basic` | comparator block (see §4), `Euclidean`, `TestFunction`, `Admissible` (= `PackingBounds.FullAdmissible`, the class `𝒜_d` of (2)), `RadialAdmissible` (`𝒜_d^rad`), `LP` (= `fullLinearProgram`), `normalizedCost`, `RadialEigenfunction`, … |
| `Parameters` | `a₀ε, Aε, Bε, Qε, bε, β`, the polynomials `PPlus`, `PMinus`, `PZero` (imports only Mathlib) |
| `Radial`, `MellinFourier` | `v_d`, radial profiles, `X_f`, the multiplier `m_ℓ`, the Mellin–Fourier functional equation (report §2.2) |
| `SchwartzTools` | `dilate`, `IsRadial.fourier`, `IsRealValued.fourier_of_radial`, exponential tilts, the change of variables `r = R e^v` |
| `Admissible/{Nonempty, Radialization}` | `𝒜_d^rad ≠ ∅` via a bump autocorrelation; the radial reduction of report §2.1 (`Admissible.radialize`, `LP_eq_radial`) |
| `LowerBound/{Balanced, LogProfile, MellinStrip, PoissonKernel, GammaBoundary, LimitingDensity, CappedMajorant, CappedMajorization, CenteredMax, Main}` | report §3: `φ_g`, `Z_g`, the strip and its boundary values, `P_σ`, `h_ℓ`, Lemma 3.2 (capped, Phragmén–Lindelöf), Lemma 3.3–3.6, Propositions 3.1 and 3.7 |
| `UpperBound/{Envelope, MellinProfile, Residues, WallisRadius, ShellEstimates, SaddleDamping, FourierPair, SmallRadius, Schwartz, SaddleContour, GammaPhase, SaddleTails, GaussianError, Coverage, Signs, SelfFourier}` | report §4: envelope and generic `mellinProfile`, residues, the radius `R_{ε,d}`, Lemmas 4.2–4.10 (generic in the polynomial), `f₊`, `f₋`, `f₀`, exterior signs |
| `Asymptotics/{Framework, Stirling, Main, Manuscript}` | the sandwich argument, Stirling for `v_d`, Theorem 1.1 in all its forms |
| `SpherePacking/{Basic, Periodic, PeriodicApproximation, CohnElkiesBound, Radialization}` | packings, periodic packings, the Cohn–Elkies bound via Poisson summation, the `O(d)` radial symmetrization of test functions |
| `PackingBound`, `Manuscript` | `Δ_d ≤ LP_d` and Theorem 1.1 in the form of the comparator (`PackingBounds.*`), the manuscript conclusions |
| `SignUncertainty/{Basic, Radialization, L1Approximation, SchwartzFamily, Mollifiers, SchwartzApproximation, LowerBound, UpperBound, Main}` | report §2.1 and Theorem 1.2 (§1.6) |

Root `CohnElkies.lean` imports `PackingBound`, `Manuscript` and `SignUncertainty.Main`. Import graph (scratchpad
`depgraph_after.txt`): shared infrastructure `Basic`, `Parameters`, `Radial`, `MellinFourier`,
`SchwartzTools`; `LowerBound/*` imports none of `UpperBound/*` and vice versa; the two bounds meet
in `Asymptotics/Main`; the sphere-packing modules depend only on `Basic` and `Asymptotics`.

### 2.2 `CohnElkiesForMathlib/` (Mathlib directory structure, Mathlib namespaces, imports only Mathlib)

| module | content |
|---|---|
| `Analysis/Complex/PhragmenLindelof` | maximum principle in a horizontal strip for a function whose *modulus* extends continuously (`PhragmenLindelof.horizontal_strip_norm_extension`) |
| `Analysis/Complex/Trigonometric` | the hyperbolic cotangent `Real.coth = cosh / sinh`, which Mathlib lacks (it has `tanh`, `artanh`, `cot`): positivity, derivative, antitonicity of `coth` and of `log ∘ coth`, the bounds `log (coth x) ≤ 4 exp (-2x)` and `abs_log_coth_div_le`, and the integrability of `log (coth (π|y|/2))` and of its damped quotient |
| `Analysis/Fourier/FourierTransform` | `Real.fourier_comp_linearEquiv` |
| `Analysis/Fourier/FourierTransformDeriv` | `𝓕 g ∈ L¹` when `g` has two integrable derivatives |
| `Analysis/Fourier/PoissonSummation` | Poisson summation for lattices in `ℝ^d` and Schwartz functions (from the Sphere-Packing-Lean project) |
| `Analysis/SpecialFunctions/FrullaniIntegral` | real and complex exponential Frullani integrals, the Wallis product as a Laplace integral (`Frullani.*`, `Real.Wallis.*`) |
| `Analysis/SpecialFunctions/Gamma/{Basic, Beta, Digamma}` | `Γ(z+k)`, `‖Γ z‖ ≤ Γ(Re z)`, residues, `‖Γ(½+ix)‖²`, `‖Γ(ix)‖²`, the `coth` form of their quotient (`Complex.log_norm_Gamma_I_mul_sub_log_norm_Gamma_one_half_add_I_mul`); `Real.digamma := logDeriv Real.Gamma` with recurrence, `log(x−1) ≤ ψ ≤ log x`, `ψ − log → 0`, the harmonic representation and `Real.digamma_eq_complex_re` |
| `Analysis/SpecialFunctions/ImproperIntegrals` | integrability of even functions, `e^{-a|x|}`, `|x|^n e^{-a|x|}`, `e^{-a|x|}|log|x||` |
| `Analysis/SpecialFunctions/Stirling` | `log k!/k − log k → −1` |
| `Topology/Algebra/InfiniteSum/ENat` | the `ℕ∞`-valued `tsum` API |
| `Topology/Sequences` | `Filter.tendsto_of_even_odd` |

Kept in the project by judgement (entangled with project notions): the strip Poisson kernels
`P_σ`, the `O(d)` Haar/radial-symmetrization block (stated for `Fin d`; a Mathlib version should
use `Matrix.orthogonalGroup`), the "even antitone weight ⇒ Poisson convolution maximal at 0"
lemma, the `r = R e^v` change of variables. The rename table (89 entries, `CohnElkies.*` →
Mathlib-style names) is in the scratchpad file `rename_table.md`; merged duplicates:
`SpherePacking.Alternative.{Ambient, Schwartz, IsRealValued, IsRadial, quotient, IsAdmissible,
IsUnrestrictedAdmissible}` → `CohnElkies.{Euclidean, TestFunction, IsRealValued, IsRadial,
quotient, Admissible}`, `PackingBounds.FullAdmissible` (with `FullAdmissible.radialization`),
`upperFirstBranchSaddleDamping` → `saddleSourceContourDamping`, three proofs of `IsRadial (𝓕 f)`
→ `IsRadial.fourier`. `Numerics.lean` (empty after the removal of the decimal certificate) is gone.

Lake targets: `defaultTargets = ["CohnElkiesForMathlib", "CohnElkies", "ComparatorChallenges",
"SpherePackingRefactored"]`; the original `SpherePacking` library (the 55,616-line reference file)
is kept but no longer a default target, so `lake build` and the CI (`lean-action`) build only the
refactored code. Because the modules form a DAG, Lake starts one Lean process per core; each one
needs 2–4 GB, so the workflows and `scripts/ci-pages.sh` set `LEAN_NUM_THREADS=2` (verified to
cap Lake at two concurrent processes).

### 2.3 Cleanup pass

The `mathlib-quality:cleanup` checklist (lint fixes, `have` inlining, the instant-win golfing
rules, formatting, docstrings, extraction of long `have` blocks) was applied per module by three
agents after the reorganization (its per-declaration procedure is not affordable at 27k lines);
the mechanical `show` → `change` replacement (37 places) was done by script. The project is licensed Apache-2.0 (`LICENSE`, `NOTICE`; owner decision 2026-09-14), like the
`SpherePacking.lean` it derives from. Mathlib's header linter (`linter.style.header`), which
demands a per-file copyright header, is turned off in the lakefile: the 65 module files carry no
such headers.

## 3. Step 3 — blueprint

Tooling: `verso-blueprint` is versioned by branches/tags; the plan points at the `v4.34.0`
template (toolchain `v4.34.0-rc2`), while this project is on `v4.33.1`, so the `v4.33.0` tag
(toolchain `v4.33.1`) is used, with the same layout as the template: the library
`CohnElkiesBlueprint` in the same Lake workspace (`lakefile.toml`: `require VersoBlueprint`,
`lean_lib CohnElkiesBlueprint`; Mathlib is required *last* so that its pins of the shared
dependencies win over Verso's — otherwise `lake update` switches `proofwidgets` and invalidates
the Mathlib cache), the top-level document `CohnElkiesBlueprint/Blueprint.lean`, the chapters
`CohnElkiesBlueprint/Chapters/*.lean` (each imports `CohnElkies`, so that every `(lean := …)`
link is checked against the actual declaration), the generator `CohnElkiesBlueprintMain.lean`,
`scripts/ci-pages.sh` (`lake exe vbp build`, output in `_out/site/html-multi/`) and the GitHub
Pages workflows `pages.yml`/`blueprint-pages.yml` copied from the template. No toolchain or
Mathlib bump was needed. (The template's `lean_action_ci.yml` also deploys `docgen` output to
Pages; both workflows target the same Pages site — which one should own it is the repository
owner's decision.)

Content (100 nodes, 67 proof sketches, 86 `lean :=` links, written to follow the report's
statements and proofs in natural language):

| chapter | nodes | content |
|---|---|---|
| Introduction | 14 | setting, (1)–(6), `𝒜_d`, `LP_d`, Theorems 1.1 and 1.2, the packing exponent, nonemptiness of `𝒜_d` |
| The Cohn–Elkies bound | 8 | periodic packings, Poisson summation, `Δ_d ≤ LP_d` (proved in the formalization, cited in the report) |
| Preliminaries | 19 | Gamma identities, digamma, Stirling, radial reduction (Schwartz and `L¹`), Schwartz approximation, radial Mellin transform, (9)–(10) |
| Lower bound | 17 | (12)–(13), Lemmas 3.2–3.6, Propositions 3.1, 3.7, Theorem 3.8 |
| Upper bound | 28 | Theorem 4.1, the ansatz (34)–(39), saddle geometry (43)–(49), Lemmas 4.2–4.10, the upper halves of Theorems 1.1 and 1.2 |
| Appendix A | 7 | `T_d`, Proposition A.1, `A₊(d) ≤ A₋(d)` and the strict version — informal only, deliberately not formalized (see §1.6) |
| Report versus formalization | 7 | the Phragmén–Lindelöf replacement of the Poisson principle, capped Lemma 3.2, one-sided Lemma 3.3, the Frullani route for Lemma 3.4, the inverse-quadratic Lemma 3.5, the fused Theorem 1.1, the bump-mollifier Schwartz approximation, the parameter table |

Every node names its Lean counterpart (checked by the scratchpad scripts `check_bp.py` and
`check_names.py` against the sources; the rename table of Step 2 was applied). The rendered
summary page reports 95 entries (groups excluded): 86 fully closed (statement and proof
formalized, no `sorry` anywhere), 0 with incomplete dependencies, and 8 informal-only nodes (the
seven of Appendix A and the report's Poisson-principle and digamma log-moment lemmas, which the
formalization replaces by other arguments). The site builds with
`LEAN_NUM_THREADS=2 ./scripts/ci-pages.sh` (`_out/site/html-multi/`, ~21 MB). Verso `v4.33.0`
specifics learned: the lemma directive is `:::lemma_`, directive arguments must sit on one line
(so a few headers exceed 100 characters), there is no `notReady`/status flag (Appendix A nodes
are tagged `not-formalized` and carry no `lean`).

### Per-module golfing notes

- **B01 (Basic, LowerBound/Balanced, Radial, MellinFourier)**: 1,455 → 879 lines. Inlined
  single-use lemmas (`mellinDenominator_re_pos`, `IsEven`, `fourierInv_apply_zero`, …), merged
  the two `balancingScale_inv_*` lemmas, folded the compactly-supported-eigenfunction argument
  into `analyticOnNhd_complexMGF_nnMeasure`/`eq_zero_of_fourier_eq_self`, collapsed the 17
  Gaussian-pairing lemmas behind the Mellin–Hankel identity (9) into four
  (`gaussianPairing_fourier`, `mellin_gaussianPairing`, `mellin_gaussianPairing_fourier`,
  `fourier_riesz_pairing`). Mathlib substitutions: `Real.fourierInv_eq_fourier_neg`,
  `integral_eq_zero_iff_of_nonneg`, `Continuous.ae_eq_iff_eq`, `EuclideanSpace.single`,
  `Real.rpow_inv_natCast_pow`, `Measurable.pow_const`, `Complex.inv_cpow`. Not in Mathlib: a
  Fourier dilation lemma (`fourier_dilate_apply` keeps its change of variables) and the
  `a ↦ a^{b-1}e^{-ra}` Gaussian-mixture Fubini step. `IsRadial (𝓕 f)` is proved in three places
  (to be unified in the module reorganization).
- **B03 (UpperBound/Envelope2)**: 1,395 → 821 lines. The ~430-line verbatim plus/minus
  pole-subtraction block (Lemma 4.3) became one development for an abstract
  `IsPoleDatum M ρ` (meromorphic, simple poles at `z = -2n` with residues `ρ n`), instantiated by
  `isPoleDatum_plus`/`isPoleDatum_minus`; the horizontal-line growth bounds became
  `mellinEnvelope_mul_shiftedLine_bound`, generic in `P` under the single hypothesis
  `‖P z‖ ≤ (1 + |β|)(1 + ‖z‖)³`. `try dsimp`/`simpa using!` removed throughout; `open Real`.
- **B02 (UpperBound/Envelope1)**: 1,500 → 910 lines. New generic layer for an arbitrary
  polynomial `P` (`regularMellinFactor`, `mellinData`, `nthPoleNumerator`, `poleResidue`,
  `nthPoleRegularPart` and their meromorphy/pole-decomposition lemmas), of which the plus/minus
  statements are one-line corollaries; continuity results now come from
  `Differentiable.continuous` instead of parametric-integral arguments; the `sinc` bounds and the
  shell integrals were factored. Not in Mathlib: the residues of `Γ(z/2)` at `z = -2n` for `n ≥ 1`
  (`Complex.tendsto_self_mul_Gamma_nhds_zero` covers only `n = 0`).
- **B04 (UpperBound/Envelope3)**: 1,351 → 699 lines, 73 → 49 declarations. Growth/integrability of
  the Mellin data on horizontal lines, the rectangular contour shifts and the Fourier
  representation of the profiles are now stated once for an abstract Mellin datum
  (`shiftedLine_moment_integrable`, `IsRapidContourIntegrand`, `spectrum_norm_moment_integrable`,
  `mellinInv_eq_fourier`, `contDiffOn_profile`, `mellinData_conj_vertical`); the plus/minus
  results are corollaries. `HasDerivAt.congr_deriv`, `tendsto_nhds_unique`, `pow_le_one₀`,
  `one_le_pow₀` replaced ad-hoc arguments.
- **B05 (UpperBound/Residues, UpperBound/WallisRadius)**: 1,620 → 1,054 lines. The residue
  expansions (41)/(78) are proved once for an abstract triple (Mellin datum, regular part, residues)
  (`integral_regularPart_eq`, `normalized_eq_residue_sum_add_remainder`), the plus/minus versions
  being 19-line corollaries; pos/neg principal-value limits merged. **Mathlib reuse**: the local
  `wallisProduct` and its limit were replaced by `Real.Wallis.W`, `Real.Wallis.W_pos`,
  `Real.Wallis.tendsto_W_nhds_pi_div_two`; `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`
  is now used through one generic rectangle lemma. Not in Mathlib: `tanh a ≤ a`
  (`sinh_le_mul_cosh`).
- **B06 (LowerBound/LogProfile, LowerBound/MellinStrip)**: 1,410 → 905 lines. The polar
  change of variables `v ↦ R e^v` and the `L¹`/`∫` computations for `φ` (12)–(13) are shared
  helpers (`mul_exp_changeOfVariables`, `integral_comp_radialProfile`,
  `integral_logProfile_weight`); the modulus of `Z` on the strip is one lemma `norm_Z_g`; the
  exponential-tilt derivative lemmas are stated at function level. Mathlib: `DFunLike.ne_iff`,
  `mul_pow_sub_one`, `Complex.ofReal_cpow`, `VectorFourier.fourierIntegral_const_smul`.
- **B07 (LowerBound/PoissonKernel, LowerBound/GammaBoundary1)**: 1,960 → 1,205 lines. The
  strip Cayley map `E_ℓ` and the Poisson primitive `Q_σ` carry the kernel computations; the
  pos/neg halves of the regularized holomorphic kernel and of the half-line integrability
  arguments were merged (`K'_ℓ_eq`, `integrable_of_even`); the ∫_{v≤0}|φ| ≥ ½ chain and the
  Fourier-inversion bound of Lemma 3.6 became two lemmas (`half_le_setIntegral_Iic_abs`,
  `negativeHalfline_le_of_fourierInversion`). Observation: the hypothesis `y ≠ 0` of
  `lowerGammaBoundaryLog_halfInteger_factorized` is unnecessary (kept for the contract).
- **B08 (LowerBound/GammaBoundary2, LowerBound/ComplexFrullani)**: 1,315 → 833 lines. Shared
  helpers for the even/odd dimension dispatch (`natCast_div_two_cases`), the monotone Riemann
  bracketing of Lemma 3.3 (`monotone_riemann_bracket`, from `MonotoneOn.sum_le_integral`), and
  the `log √(c² + (x/2)²)` monotonicity. Mathlib: `Real.log_two_gt_d9`, `inv_le_comm₀`,
  `abs_choice`. Unused hypothesis found: `hd : 0 < d` in
  `lowerGammaBoundaryLog_dimension_exp_integrable` (kept for the contract).
- **B09 (LowerBound/LimitingDensity)**: 1,378 → 821 lines. The two Wallis phase kernels
  (plain and regularized) became one kernel `wallisPhaseKernel a` with a parameter, halving the
  moment/tail estimates behind Lemma 3.4; `wallisComplexLogPhase` names the antiderivative
  `1 + z log z − (z+1) log(z+1)` once. Mathlib: `Real.cos_lt_cos_of_nonneg_of_le_pi`,
  `Real.arctan_tan`, `Set.range`. Kept the report's route through `|Γ(ix)|²` for (7) rather than
  `Complex.Gamma_mul_Gamma_one_sub`.
- **B10 (UpperBound/ShellEstimates1, ShellEstimates2)**: 2,013 → 1,281 lines. The polynomial
  bounds (72) of Lemma 4.8 are four statements generic in `P` (`norm_imaginary_cubic_growth`,
  `norm_div_norm_imaginary_le`, `norm_translation_coeffs`, `norm_sub_div_norm_imaginary_le`), the
  plus/minus versions being corollaries; the gamma second/third moments (48) come from one lemma
  `upperGammaMoment_bounds` generic in the exponent; `intervalIntegral_thirdMoment_le` serves both
  shells. Mathlib: `Real.add_one_le_exp`, `pow_le_pow_left₀`, `div_eq_div_iff`.
- **B11 (UpperBound/ShellEstimates3, UpperBound/FourierPair)**: 1,542 → 1,055 lines. The
  exponential-series tail estimates of Lemma 4.10 (79)–(81) collapsed into two lemmas
  (`hasSum_expSeries_polynomialMoment`, `expSeries_alternating_tail_bound`); the identification of
  the radial Mellin transform with the Fourier datum and the Fourier-pair proof (40) are generic in
  the profile (`criticalLogProfile_eq_fourierInv`, `radialMellinFrequency_of_source`,
  `isRadial_of_source`), so `f₀` can reuse them. Mathlib: `sum_le_hasSum`,
  `Finset.abs_sum_le_sum_abs`, `SchwartzMap.ext`, `gcongr`. Not in Mathlib: exponential-series
  tail bounds in the regime `2y ≤ m + 1` (`Real.exp_bound` needs `|x| ≤ 1`).
- **B12 (UpperBound/SmallRadius1, SmallRadius2)**: 2,393 → 1,414 lines. Lemma 4.10's tail
  majorants are generic (`saddleSmallResidue_tail_le_majorant` with parameters, one
  `tendsto_pow_mul_exp_neg_mul_atTop`, `tendsto_log_pow_div_atTop`), the negative-contour gamma
  estimates were compressed with three exp/Gamma helpers; the artificial `let _sourceParameter`
  wrapper of `u_star` was removed (its `ε` argument is unused: `u_*` depends only on `d`).
  Mathlib: `Nat.le_ceil`, `Nat.ceil_lt_add_one`, `Real.log_sqrt`, `squeeze_zero'`,
  `Filter.Tendsto.atTop_mul_const`.
- **B13 (UpperBound/Schwartz, UpperBound/SaddleContour)**: 2,114 → 1,283 lines. Smoothness at
  the origin and rapid decay (Lemma 4.3) are proved once for an abstract Mellin datum
  (`saddleSquaredContour`, `saddleProfile_eq_squaredTaylor`, `saddleFunction_contDiff`,
  `saddleOuterSchwartz`), with one differentiation-under-the-integral lemma
  (`saddlePositiveContourMoment_hasDerivAt_of_bounds`) and a generic `Cⁿ`-by-induction helper;
  the contour identity (71) is generic in `P`. Mathlib: `hasDerivAt_ofReal_cpow_const`
  replaces a 37-line derivative computation. Observation: `saddleSourceContourDamping` is
  definitionally `upperFirstBranchSaddleDamping` (duplicate definition; to be merged).
- **B14 (UpperBound/GammaPhase)**: 1,595 → 849 lines. The Taylor estimate for `e^{ix}` is one
  lemma on `uIcc 0 x` (`norm_expI_sub_taylor_le`, via
  `intervalIntegral.norm_integral_le_abs_integral_norm`); the log-gamma integral representation
  (45) and its cubic remainder are `Gker`/`Lker`/`GkerN` with `exp_G_ℓη`; the centered phase
  (46) and its Gaussian approximation are `expL_eq`, `expL_stationary_eq`,
  `norm_expL_sub_gaussian_le`; the digamma recurrence lemmas are `digamma_add_one/_nat`.
  Mathlib: `Complex.norm_exp_I_mul_ofReal`, `tendsto_nhds_unique_of_eventuallyEq`,
  `linear_combination` with `Complex.I_sq`.
- **B15 (UpperBound/SaddleTails1, SaddleTails2)**: 2,232 → 1,254 lines. The Gaussian/exponential
  tail integrals of Lemma 4.8 are one lemma generic in the damping profile
  (`saddleGaussianTailWeight_tail_integral_le`), the normalized tail bound is generic in
  `(V, η, c, C)`, the central window (72) generic in `P` (`exists_uniform_central_window`), the
  positive-shell moments generic in the exponent; duplicated `√(ℓη)√(ηV)` and `rpow` limits
  factored. Mathlib: `integral_comp_abs`, `integral_exp_mul_Ioi`, `Integrable.mono'`,
  `max_le_add_of_nonneg`, `Tendsto.sqrt`.
- **B16 (UpperBound/SaddleTails3, SaddleTails4, Coverage)**: 2,259 → 1,198 lines. The full-line
  Gaussian error of Lemma 4.8 is one lemma `fullLine_error_lt_gaussian`; the tail integrals of the
  centered integrand are generic in `P` (`centered_tail_integral_le`,
  `gaussianIntegrand_tail_norm_eq`); the wrapper chain of Corollary 4.9's coverage argument
  (`v(u) → ∞`, continuity, intermediate values) collapsed into `eventually_saddleLogRadius_covers_Ici`.
  Mathlib: `integral_gaussian`, `integral_add_compl`, `setIntegral_mono_set`,
  `Tendsto.atTop_div_const`, `Real.exp_half`.
- **B17 (Asymptotics/Framework, LowerBound/CappedMajorant, LowerBound/PhragmenLindelof)**:
  1,061 → 645 lines. The abstract lower/upper-bound framework lost its two intermediate `Prop`s
  and four wrappers; the capped majorant `h_{λ,D}` and the outer functions `W_b`, `W_D` of Lemma 3.2
  are `h_ℓD`, `W_b`, `W_D` with short lemma names; the Phragmén–Lindelöf strip principle
  (`horizontalStrip_norm_extension_majorization`) was restructured along Mathlib's
  `PhragmenLindelof.horizontal_strip` (which cannot be used directly: it needs `DiffContOnCl`, but
  only the modulus of `e^{-W_D} Z` extends continuously) and is ready for `ForMathlib`. Mathlib:
  `Convex.linear_preimage`, `Real.one_lt_cosh`, `Real.cosh_le_cosh`, `RCLike.re_to_complex`.
- **B18 (LowerBound/CappedMajorization)**: 1,420 → 755 lines. Lemma 3.2's capped majorization
  `|Z(s+iσλ)| ≤ exp ∫ P_σ h_{λ,D}` now rests on one dominated-convergence workhorse
  (`tendsto_setIntegral_P_σ_mul`, generic in kernel, set and filter) for the boundary behaviour of
  `Re W_D`, a shared Riemann-sum estimate `abs_sum_log_sqrtFactor_le`, and the growth bound
  `exists_abs_W_D_re_le`; the strip-trace extension is `stripTraceExtension`/`W_D_reExtension`.
  Mathlib: `Complex.re_add_im`, `IsBigO.of_bound`, `integral_add_compl`, `Filter.Tendsto.congr'`.

  default heartbeat budget with no exceptions. The centered-maximum argument of Lemma 3.3 is one
  `even_antitone_poisson_convolution_max`; the Poisson products and clipping limits are generic in
  the boundary datum (`scaled_poisson_product_integrable`, `tendsto_integral_poisson_clip`); the
  analytic core of the `L¹` bound for `Z` is `integral_norm_le_of_quadratic_majorant`, generic in
  `Z`. Mathlib: `Real.log_two_gt_d9`, `integral_sub_left_eq_self`, `Measure.integral_comp_mul_left`.
- **B20 (Asymptotics/Stirling, Admissible/Nonempty, Asymptotics/Main, UpperBound/Signs,
  Asymptotics/Manuscript)**: 1,367 → 842 lines, default heartbeats. The Stirling input for
  `v_d^{1/d}√d → √(2πe)` now comes from `Stirling.tendsto_stirlingSeq_sqrt_pi` +
  `Stirling.log_stirlingSeq_formula` in 15 lines; the even/odd dimension split remains because
  Mathlib has no Stirling asymptotic for `Real.Gamma` (only Bohr–Mollerup and the Euler limit);
  the `o(1)` "manuscript" forms of Theorem 1.1 collapsed into one lemma per form. Mathlib:
  `Real.exp_half`, `Real.pow_rpow_inv_natCast`, `Real.isLittleO_log_id_atTop`,
  `Real.Gamma_nat_add_one_add_half`, `Real.sqrt_div`.
- **B21 (SpherePacking/Basic, Periodic1, Periodic2)**: 2,354 → 1,889 lines (this code, from the
  Sphere-Packing-Lean project, was already dense), default heartbeats. **Mathlib reuse**:
  `measure_ball_pos`, `measure_ball_lt_top`, `Measure.finite_const_le_meas_of_disjoint_iUnion`,
  `ZSpan.setFinite_inter`, `ZLattice.rank`, `Homeomorph.smulOfNeZero`, `Measure.addHaar_ball`
  replaced ~150 lines of hand-rolled arguments; the `ENat` infinite-sum API (no Mathlib
  counterpart) is kept as a documented Mathlib-candidate block; the comparator definitions
  (`SpherePacking`, `SpherePackingConstant`, …) keep their exact bodies.
- **B22 (SpherePacking/PoissonSummation, SpherePacking/CohnElkiesBound)**: 2,350 → 1,413 lines,
  default heartbeats. **Mathlib reuse**: `UnitAddTorus.integral_preimage`,
  `UnitAddTorus.mFourierCoeff_eq_integral`, `IsOpenQuotientMap.piMap`,
  `QuotientAddGroup.isOpenQuotientMap_mk`, `Summable.tsum_finsetSum`,
  `integral_eq_zero_iff_of_nonneg`, `Complex.exp_conj`, `Metric.finite_isBounded_inter_isClosed`
  replaced ~300 lines; `Real.fourier_comp_linearEquiv` (Fourier transform under a linear
  equivalence) is a clear Mathlib candidate; the summability of lattice translates is stated for
  an arbitrary discrete lattice. Contract gap found: `CohnElkiesBound` uses two `Periodic1`
  declarations missing from the export list (kept by that agent).
- **B23 (PackingBound, SpherePacking/Radialization, Numerics, Manuscript, FullAdmissible)**:
  1,807 → 1,080 lines, default heartbeats. **Decimal certificate removed** (user instruction): all
  13 declarations of `Numerics` (the 30/33/36/40-digit bounds on `π`, `log 2`, `log(4/π)` and the
  exponent `criticalBinaryExponent_mem_Ioo_d30`) are gone; the module remains as a docstring-only
  stub and the field `base_two_decimal_certificate` was dropped from the two manuscript-conclusion
  structures. The main theorem now states the exact exponent `-½ log₂(2π/e)`
  (`FullMain.exact_binary_exponent`), whose positivity is `criticalBinaryExponent_pos`.
  **Radialization**: the generic orthogonal-average and Fourier-orbit layers (14 declarations) were
  replaced by direct proofs from the definition of `radialSymmetrizationAverage` plus one Fubini
  swap; `radialIsometrySchwartzOrbit` is `compIsometry` with mathlib-style lemma names.
  **FullAdmissible**: the nine-lemma symmetrization chain is three lemmas, the theorem →
  10-fold conjunction → theorem round trip is one `sharpFullCohnElkiesManuscriptConclusions`,
  and the toReal/`ℝ≥0∞` LP bounds are one `sphere_packing_le_radial_linear_program`.
  The comparator bound `PackingBridge.sphere_packing_le_linear_program : SpherePackingConstant d ≤
  ENNReal.ofReal (fullLinearProgram d)` (`0 < d`) was added. Comparator definitions/statements
  verified byte-identical to the originals. Duplication left in place (needs `Basic.lean` and the
  comparator-frozen structure): `SpherePacking.Alternative.{Ambient, Schwartz, IsRealValued,
  IsRadial, quotient}` mirror `CohnElkies.{Euclidean, TestFunction, IsRealValued, IsRadial,
  quotient}`, and `PackingBounds.FullAdmissible` bundles `Alternative.IsUnrestrictedAdmissible`.
  Mathlib: `abs_le_one_iff_mul_self_le_one`, `integral_re`/`integral_im`, `Integrable.of_bound`,
  `Measure.haarMeasure_self`, `IsHaarMeasure`/`IsProbabilityMeasure` instance paths.

- **C2 (UpperBound/Envelope1–3, Residues, Schwartz, SaddleContour, GammaPhase, SaddleTails1,2,4,
  FourierPair, Signs; new SelfFourier)**: 7,457 → 7,085 lines plus 271 new; see §1.6 for the
  generic-`P` design. Left in place (now unused): `exists_±Polynomial_uniform_norm_ratio` in
  `ShellEstimates1`.

### Heartbeats

The original file sets `maxHeartbeats 800000` globally (and `1600000` for the numeric
certificates). Following the user's instruction the default budget is kept: the global options
are removed from every module and proofs are made to compile under the default; the only
exceptions are scoped `set_option maxHeartbeats N in` declarations, listed here:

Result of the pass (groups D0a–D0d, plus the golfing groups B19–B23 which removed the option
themselves): **no declaration needed a scoped exception**. In every module the global
`set_option maxHeartbeats 800000` (and the `1600000` of the numeric certificates) turned out to be
vestigial: deleting the line was enough, and the proofs compile under the default `200000` with
large margins (spot checks: all modules of D0c compile at `maxHeartbeats 50000`, i.e. a 4× margin,
also with the lakefile options `maxSynthPendingDepth = 3`, `relaxedAutoImplicit = false`
applied by `-D`; note that `lake env lean` ignores the lakefile's `[leanOptions]`, so the final
`lake build` is the authoritative check). Two golfs in B23 were reverted because they would have
exceeded the default budget (`Measurable.comp'` for `measurable_orthogonalAction_inv` times out
at `whnf`; `orthogonalMatrixOfIsometry_action` needs an intermediate `change`). The two
`set_option backward.*` lines are kept for now (to be tested separately).

Scoped exceptions: **none**.

## 4. Comparator

Set up as in `openai/ten-proofs`: `lakefile.toml` requires `Comparator` (tag `v4.33.0`, matching the
toolchain) and defines the library `ComparatorChallenges` with the single module
`ComparatorChallenges/CohnElkies.lean`, which imports only Mathlib and states (with `sorry`)
Theorem 1.1 in both forms (`PackingBounds.FullMain.exact_limit`, `exact_binary_exponent`), the
packing consequences (`PackingBounds.PackingBridge.sphere_packing_le_linear_program`, which was
missing from the original file and is now proved, and `sphere_packing_sharp_asymptotic_upper`)
and Theorem 1.2 (`CohnElkies.signUncertaintyConstant_div_sqrt_tendsto`, in `ℝ≥0∞`, for the `L¹`
class `SignEigenfunction`). The linear-program and packing definitions are those of OpenAI's
challenge `A_SpherePacking.lean` (its three redundant ad-hoc instances are dropped; the decimal
certificate and the bundled conclusions are not part of the challenge). Configuration:
`ComparatorChallenges/CohnElkies.json` (permitted axioms `propext`, `Quot.sound`,
`Classical.choice`; `enable_nanoda`); run `lake exe comparator ComparatorChallenges/CohnElkies.json`
with `landrun`, `lean4export` and `nanoda_bin` on `PATH`; the workflow
`.github/workflows/comparator.yml` builds those tools (landrun needs Linux) and runs the check in CI.
Locally (macOS) the check was run with the `fake-landrun.sh` shim shipped with the comparator:
after the semantic tasks, `lake exe comparator` on all five theorems reported
"Your solution is okay!" (statements identical, axioms `propext`/`Quot.sound`/`Classical.choice`
only, Lean kernel replay accepted; nanoda disabled locally, enabled in CI).

Two facts learned the hard way:
- `lean4export` must be built with the project's exact toolchain (`lake build
  @lean4export/lean4export` from the project root does this), since it loads the project's
  `.olean` files;
- the comparator compares the challenge and the solution constant by constant, including the
  auxiliary constants `foo._proof_n` into which Lean abstracts proof terms occurring in
  definitions (e.g. the `Nat.AtLeastTwo 2` instance behind a numeral `2`). Those auxiliaries are
  deduplicated only *within one file* and named after the first declaration that needs them, so a
  definition split over several modules elaborates to *different* constants than the same
  definition in the single-file challenge (`fullLinearProgram` referred to
  `PackingBounds.fullLinearProgram._proof_1` instead of `CohnElkies.unitBallVolume._proof_1`).
  Therefore all challenge definitions are kept as one verbatim, contiguous block at the top of
  `CohnElkies/Basic.lean` (`section ComparatorDefinitions`), which must never be edited.

## 5. Radial reduction: `𝒜_d` without radiality (2026-09-14, task R1)

The owner asked to drop the field `radial` from `Admissible` and to prove the reduction step of
report §2.1. Result:

- `CohnElkies.Admissible d` is now `abbrev Admissible (d) := PackingBounds.FullAdmissible d`, the
  class `𝒜_d` of equation (2) (no radiality); `quotient`, `quotientSet`, `LP` are `abbrev`s of the
  comparator's `fullQuotient`, `fullQuotientSet`, `fullLinearProgram`, so `LP_d` (equation (3)) is
  defined once. The radial class is `structure RadialAdmissible (d) extends toAdmissible :
  Admissible d where radial : IsRadial function` (`𝒜_d^rad`, §2.1).
- New module `CohnElkies/Admissible/Radialization.lean` (report §2.1): `Admissible.radialize :
  Admissible d → RadialAdmissible d` (rotational average over `O(d)`), `radialize_apply`,
  `radialize_apply_zero`, `fourier_radialize_apply_zero`, `quotient_radialize`,
  `normalizedCost_radialize`, `radialize_nonpos_of_le_norm` (nonpositivity outside a ball of any
  radius is preserved), `range_radialAdmissible_eq`, `quotientSet_eq_radial`, `LP_eq_radial`,
  `normalizedProgram_eq_radial`.
- Radiality is used only in `LowerBound/Balanced` (the anti-self-Fourier witness `𝓕h - h`), now
  stated for `RadialAdmissible`; `uniformAdmissibleLowerBound_of_signRadius` (Theorem 3.8 before
  Stirling) holds for every `f ∈ 𝒜_d` by radializing first. The saddle-source construction
  (`saddleSourceAdmissible`) and the bump autocorrelation (`autocorrelationAdmissible`) are
  `RadialAdmissible` and enter `𝒜_d` through `toAdmissible`. Everything downstream (sandwich
  framework, Stirling, Theorem 1.1 in all forms, `Δ_d ≤ LP_d`) is stated for `𝒜_d`/`LP_d` directly.
- The "full" layer disappeared: `FullAdmissible.lean` was deleted (its content is in
  `Admissible/Radialization`, `PackingBound`, `Manuscript`, `SpherePacking/Radialization`). The
  comparator theorem names and statements are unchanged (now in `PackingBound.lean`), and
  `PackingBounds.SharpFullCohnElkiesManuscriptConclusions` is kept (in `Manuscript.lean`).

Rename table (old → new; "deleted: …" means subsumed):

| old | new |
|---|---|
| `CohnElkies.Admissible` (structure, radial) | `CohnElkies.Admissible` (abbrev of `PackingBounds.FullAdmissible`; meaning: `𝒜_d`, no radiality) |
| `CohnElkies.Admissible.mk`/`.radial` | `CohnElkies.RadialAdmissible.mk`/`.radial` (parent projection `RadialAdmissible.toAdmissible`) |
| `CohnElkies.quotient`, `quotientSet`, `LP` (defs, radial program) | same names, `abbrev`s of `PackingBounds.fullQuotient`, `fullQuotientSet`, `fullLinearProgram` |
| `PackingBounds.FullAdmissible.radialization` | `CohnElkies.Admissible.radialize` |
| `PackingBounds.FullAdmissible.quotient_radialization` | `CohnElkies.Admissible.quotient_radialize` |
| `PackingBounds.fullQuotientSet_eq_radial` | `CohnElkies.quotientSet_eq_radial` |
| `PackingBounds.fullLinearProgram_eq_radial` | `CohnElkies.LP_eq_radial` |
| `PackingBounds.fullQuotientRootSet_eq_radial` | deleted: the two sets are definitionally equal |
| `PackingBounds.radialToFull` | deleted: subsumed by `CohnElkies.RadialAdmissible.toAdmissible` |
| `PackingBounds.fullQuotient_radialToFull` | deleted: `rfl` |
| `PackingBounds.fullQuotientSet_eq_radial_iff` | deleted: subsumed by `CohnElkies.range_radialAdmissible_eq` |
| `PackingBounds.RadialMain.exact_limit`, `exact_binary_exponent` | deleted: subsumed by `PackingBounds.FullMain.exact_limit`, `exact_binary_exponent` |
| `PackingBounds.PackingBridge.sphere_packing_le_radial_linear_program` | deleted: subsumed by `PackingBounds.PackingBridge.sphere_packing_le_linear_program` |
| `CohnElkies.SharpCohnElkiesManuscriptConclusions`, `sharpCohnElkiesManuscriptConclusions` | deleted: subsumed by `PackingBounds.SharpFullCohnElkiesManuscriptConclusions`, `sharpFullCohnElkiesManuscriptConclusions` |
| `CohnElkies.manuscriptQuotientRootSet_eq_literal` | `PackingBounds.manuscriptQuotientRootSet_eq_literal` |
| `SpherePacking.Alternative.radialSymmetrizationAverage_nonpos_of_one_le_norm` | `SpherePacking.Alternative.radialSymmetrizationAverage_nonpos_of_le_norm` (any radius) |
| `SpherePacking.Alternative.fourier_radialSymmetrization` | unchanged, moved to `SpherePacking/Radialization.lean` |
| `CohnElkies.autocorrelationAdmissible`, `saddleSourceAdmissible` | unchanged names, type `RadialAdmissible d` |
| `CohnElkies.balancingScale`, `balanced`, … , `normalizedCost_ge_of_no_antiFourierWitness` (`LowerBound/Balanced`) | unchanged names, argument `f : RadialAdmissible d`, costs of `f.toAdmissible` |
| module `CohnElkies.FullAdmissible` | deleted |

### 5.1 One rotational average (2026-09-14, task R2)

The project had two copies of the report's rotational average: `radialSymmetrizationAverage` for
Schwartz functions (namespace `SpherePacking.Alternative`, inherited from the original file) and
`rotationalAverage` for integrable functions (added with the `L¹` theory). They are now one
definition in the new module `CohnElkies/Radialization.lean` (namespace `CohnElkies`, imports
`Basic` and `SchwartzTools`), which also holds the orthogonal group, its action and its Haar
probability measure:

```
def rotationalAverage (g : Euclidean d → E) (x : Euclidean d) : E :=
  ∫ U : OrthogonalGroup d, g (orthogonalAction U⁻¹ x) ∂radialOrthogonalHaar d
def rotationalAverageSchwartz (f : TestFunction d) : TestFunction d
@[simp] theorem rotationalAverageSchwartz_apply : rotationalAverageSchwartz f x = rotationalAverage f x
theorem fourier_rotationalAverageSchwartz : 𝓕 (rotationalAverageSchwartz f) = rotationalAverageSchwartz (𝓕 f)
```

Every general property (rotation invariance, radiality, value at the origin, real and imaginary
parts, sign preservation outside a ball of any radius, continuity, integrability, `‖ℛg‖₁ ≤ ‖g‖₁`,
commutation with `𝓕`) is stated once for `rotationalAverage`; the Schwartz lemmas are
specializations, and `Admissible.radialize` and `SignEigenfunction.radialize` are both built on it.
`CohnElkies/SpherePacking/Radialization.lean` is deleted and the namespace `SpherePacking.Alternative`
is gone; the three radialization modules went from 1,062 to 945 lines. Three lemmas gained a
`Continuous g` hypothesis, which the `ℂ`-valued statement genuinely needs (`integral_re` requires
integrability); the Schwartz call sites supply it.

**Why `g(U⁻¹x)` and not `g(Ux)`**: only *left* invariance of the Haar measure is then needed for
rotation invariance of the average (the substitution `U ↦ AU` gives `(AU)⁻¹(Ax) = U⁻¹x`), and that
is what Mathlib's `IsHaarMeasure` provides. The two forms agree because the Haar measure of the
compact group `O(d)` is inversion invariant, but Mathlib v4.33.1 has `IsInvInvariant` only for
commutative groups and no unimodularity API, so the equivalence is documented in the module
docstring rather than proved.
