# Refactored Cohn–Elkies and the sign uncertainty principle formalization

**[Blueprint](https://seewoo5.github.io/cohn-elkies-refactor/)**

This repository contains a refactored version of [OpenAI's formalization](https://github.com/openai/ten-proofs) of [their results](https://cdn.openai.com/pdf/ten-proofs-oai.pdf) on the Cohn–Elkies linear programming bound for sphere packings and Bourgain-Clozel-Kahane's sign uncertainty principle for Fourier eigenfunctions.
One-file version can be found in `SpherePackingRefactored.lean`, and the original OpenAI formalization is preserved in `SpherePacking.lean`, where the former is about 44\% of the latter in term of LoC.
More organized formalization are under `CohnElkies` and `CohnElkiesForMathlib`, with a blueprint of the statements and proofs in `CohnElkiesBlueprint`.

Some results in the original report were missing in their formalization, and we have added them here. In particular, we have formalized both signs of the uncertainty principle, the self-Fourier function $f_0$, $L^1$ to Schwartz reduction, and radial reduction.
The 30-digits approximation of the Cohn-Elkies exponent is removed, since it is unnecessary.
The Proposition A.1 of the report ($\mathsf A_+(d) < \mathsf A_-(d)$) is also missing in the original formalization, but we decided to not to formalized it here, too (see `RefactoringResult.md`, §1.6).

Every code is written by Claude (mostly Fable 5.1 and Opus 5), where the details can be found under `formalization.yaml`.
It was asked to follow `RefactoringPlan.md` (which is completely human-written) with the original OpenAI's report, original Lean file, and my two blog posts as references, and the result is summarized in `RefactoringResult.md`.

### Comparator

The statements in `ComparatorChallenges/CohnElkies.lean` are compared with the proofs in the
`CohnElkies` library by

```sh
lake exe comparator ComparatorChallenges/CohnElkies.json
```

with `landrun` (Linux only), `lean4export` (built with this project's toolchain:
`lake build @lean4export/lean4export`) and optionally `nanoda_bin` on `PATH`; the workflow
`.github/workflows/comparator.yml` runs this in CI. See `ComparatorChallenges/README.md`.

### License

Apache License 2.0 (see `LICENSE` and `NOTICE`). The development started from `SpherePacking.lean`
of [`openai/ten-proofs`](https://github.com/openai/ten-proofs) (Apache-2.0), which itself reuses
material from [Sphere-Packing-Lean](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean)
(Apache-2.0).