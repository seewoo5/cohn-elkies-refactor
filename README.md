# The Cohn–Elkies exponent and sign uncertainty, in Lean

A readable reformalization of Chapter 1 of OpenAI's report *Ten proofs*
(["Ten advances in mathematics and theoretical computer science"](https://cdn.openai.com/pdf/ten-proofs-oai.pdf)),
starting from the original single-file formalization `SpherePacking.lean` of
[`openai/ten-proofs`](https://github.com/openai/ten-proofs) (55,616 lines), following
`RefactoringPlan.md`. The refactored formalization has 24,647 lines in 53 modules (`CohnElkies/`)
plus 2,169 lines of Mathlib-ready material in 12 modules (`CohnElkiesForMathlib/`), and adds
the results the original did not contain (both signs in the lower bound, the self-Fourier function
`f₀`, the `L¹` theory and Theorem 1.2). The results are

* **Theorem 1.1.** The Cohn–Elkies linear programming bound for sphere packings satisfies
  $\mathrm{LP}_d^{1/d} \to \sqrt{e/(2\pi)}$; in base-2 form,
  $\log_2 \mathrm{LP}_d / d \to -\tfrac12 \log_2(2\pi/e)$
  (`PackingBounds.FullMain.exact_limit`, `PackingBounds.FullMain.exact_binary_exponent`), together
  with the packing consequences $\Delta_d \le \mathrm{LP}_d$ and
  $\Delta_d \le (\sqrt{e/(2\pi)} + o(1))^d$
  (`PackingBounds.PackingBridge.sphere_packing_le_linear_program`,
  `PackingBounds.PackingBridge.sphere_packing_sharp_asymptotic_upper`).
* **Theorem 1.2.** The sign-uncertainty constants of $L^1$ Fourier eigenfunctions satisfy
  $\mathsf A_\pm(d)/\sqrt d \to 1/\pi$ (`CohnElkies.signUncertaintyConstant_div_sqrt_tendsto`;
  the definitions `SignEigenfunction`, `signRadius`, `signUncertaintyConstant` are in `CohnElkies/Basic.lean`).

Appendix A of the report ($\mathsf A_+(d) < \mathsf A_-(d)$) is deliberately not formalized
(see `RefactoringResult.md`, §1.6).

**[Blueprint](https://seewoo5.github.io/cohn-elkies-refactor/)** — the natural-language statements
and proofs, each linked to its Lean declaration, with a dependency graph and a progress summary
(built and deployed by the `Blueprint Pages` workflow).

## Layout

| path | content |
|---|---|
| `CohnElkies/` | the formalization (library `CohnElkies`, root module `CohnElkies.lean`): `Basic` (the objects of the main statements: the admissible class `𝒜_d`, its radial subclass, `LP_d`), `Parameters`, `Radial`, `MellinFourier`, `SchwartzTools`, `Radialization` (the rotational average over `O(d)`), `Admissible/` (`𝒜_d ≠ ∅`, the radial reduction of report §2.1), `LowerBound/` (report §3: Mellin strip, Poisson majorants, Propositions 3.1 and 3.7), `UpperBound/` (report §4: the saddle-point construction of `f₊`, `f₋`, `f₀`), `Asymptotics/` (Theorem 1.1), `SpherePacking/` (packings, periodic packings, Poisson summation, the Cohn–Elkies bound), `SignUncertainty/` (report §2.1 and Theorem 1.2), `PackingBound` (`Δ_d ≤ LP_d`, Theorem 1.1 in the form of the comparator), `Manuscript` |
| `CohnElkiesForMathlib/` | general material ready for Mathlib, in Mathlib's directory structure (library `CohnElkiesForMathlib`) |
| `ComparatorChallenges/` | the [comparator](https://github.com/leanprover/comparator) challenge: self-contained statements of the main theorems (imports only Mathlib), JSON config, instructions |
| `CohnElkiesBlueprint/` | the blueprint (natural-language statements and proofs following the report, linked to the Lean declarations; rendered with `lake exe vbp build`) |
| `SpherePacking.lean` | the original single-file formalization, kept as an untouched reference |
| `SpherePackingRefactored.lean` | the refactored formalization as a single file (Step 1 of the plan) |
| `RefactoringPlan.md`, `RefactoringResult.md` | the plan and the notes on what was done (renamings, differences from the report, Mathlib reuse, new statements, module layout, comparator, blueprint) |

## License

Apache License 2.0 (see `LICENSE` and `NOTICE`). The development started from `SpherePacking.lean`
of [`openai/ten-proofs`](https://github.com/openai/ten-proofs) (Apache-2.0), which itself reuses
material from [Sphere-Packing-Lean](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean)
(Apache-2.0).

## Building

```sh
lake exe cache get          # Mathlib cache
LEAN_NUM_THREADS=2 lake build CohnElkiesForMathlib CohnElkies ComparatorChallenges
```

(The modules form a DAG, so Lake would otherwise start one Lean process per core; each process
needs 2–4 GB. `LEAN_NUM_THREADS` caps the number of concurrent processes.)

Lean `v4.33.1`, Mathlib `v4.33.1`; the default `maxHeartbeats` is used throughout, there is no
`sorry`, and the main theorems depend only on `propext`, `Classical.choice` and `Quot.sound`.

### Comparator

The statements in `ComparatorChallenges/CohnElkies.lean` are compared with the proofs in the
`CohnElkies` library by

```sh
lake exe comparator ComparatorChallenges/CohnElkies.json
```

with `landrun` (Linux only), `lean4export` (built with this project's toolchain:
`lake build @lean4export/lean4export`) and optionally `nanoda_bin` on `PATH`; the workflow
`.github/workflows/comparator.yml` runs this in CI. See `ComparatorChallenges/README.md`.

### Blueprint

```sh
LEAN_NUM_THREADS=2 ./scripts/ci-pages.sh   # lake exe vbp build; writes _out/site/html-multi/
```

The workflow `.github/workflows/pages.yml` runs the same script and deploys the site to
<https://seewoo5.github.io/cohn-elkies-refactor/>.
