# [Comparator](https://github.com/leanprover/comparator) challenge

`CohnElkies.lean` states, importing only Mathlib, the main results of Chapter 1 of the report
"Ten proofs" (OpenAI) that this repository formalizes:

* Theorem 1.1 (`PackingBounds.FullMain.exact_limit`, `exact_binary_exponent`): the Cohn–Elkies
  linear programming bound satisfies `LP_d^{1/d} → √(e/(2π))`, i.e. `log₂ LP_d / d → -½ log₂(2π/e)`;
* the packing consequences (`PackingBounds.PackingBridge.sphere_packing_le_linear_program`,
  `sphere_packing_sharp_asymptotic_upper`): `Δ_d ≤ LP_d` and `Δ_d ≤ (√(e/(2π)) + o(1))^d`;
* Theorem 1.2 (`CohnElkies.signUncertaintyConstant_div_sqrt_tendsto`): `A_±(d)/√d → 1/π` for the
  sign-uncertainty constants of `L¹` Fourier eigenfunctions.

The definitions of the linear program and of the packing constant are those of the original
challenge `ComparatorChallenges/A_SpherePacking.lean` of `openai/ten-proofs`; the sign-uncertainty
definitions follow (5)–(6) of the report (`L¹` functions represented by their continuous
Fourier-inversion representative).

To check the proofs of the `CohnElkies` library against these statements, install `landrun`
(Linux only), `lean4export` (built with this project's toolchain, e.g.
`lake build @lean4export/lean4export`) and optionally `nanoda_bin`, then run from the root:

```sh
lake exe cache get
lake build CohnElkies ComparatorChallenges
lake exe comparator ComparatorChallenges/CohnElkies.json
```

The workflow `.github/workflows/comparator.yml` does this in CI.
