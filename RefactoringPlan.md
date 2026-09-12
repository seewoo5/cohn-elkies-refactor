You are going to refactor the `SpherePacking.lean` file.
There are several references that you are going to use:

- The original report: [`ten-proofs-oai.pdf`](https://cdn.openai.com/pdf/ten-proofs-oai.pdf) and the reasoning walkthrough: [`reasoning-walkthroughs.pdf`](https://cdn.openai.com/pdf/reasoning-walkthroughs.pdf)
- Two blog posts: `2026-09-12-openai-sphere-packing-digest-part1.md` and `2026-09-12-openai-sphere-packing-digest-part2.md`

While refactoring, you are going to log some important notes in `RefactoringResult.md`. You should be simple, but also detailed and concise.


# Step 1

First, you are going to write a single lean file, `SpherePackingRefactored.lean`, which will be a golfed version of the original `SpherePacking.lean` file. The main goal is to make it more readable.

- Prove the misisng theorems. Two big theorems are on self-Fourier functions $f_0$, radial and $L^1$ to Schwartz reduction, and the theorem in Appendix ($A_+(d) < A_-(d)$). In particular, you need to properly define the uncertainty principle constants $A_+(d)$ and $A_-(d)$. You can use the original report as a reference.
- `open` or `open scoped` appropriate files so that you don't need to use long names. For example, you should use `π` instead of `Real.pi`.
- There are a lot of unnecessary typecasts. Remove them.
- Replace the project-specific definitions' names as in the original report. For example, `plusSaddleFunction` should be renamed to `f₊`. Same for the theorem names; even if it does not follow the mathlib's naming convention, it is better to understand. In particular, they will not be upstreamed to mathlib.
- Many of the theorems are stated once and then used once. It means that they can be inlined.
- There are some notations that are unnecessary or incompatible with the report. For example, `ℓ` should be repplaced with `λ`.
- As described in the part 2 of the blog post, there are some differences between the original report and the `SpherePacking.lean` file. For the parameter choices, try to follow the original report. If there is a reason that you cannot follow the original report, please explain it in `RefactoringResult.md`. For the proof arguments, keep the formalized proof in the `SpherePacking.lean` file (e.g. use Phragmén–Lindelöf principle instead of the upper half plane Poisson principle). But you also need to record these differences in `RefactoringResult.md`.
- If a theorem that you use may exists in mathlib, you should check it and use it if it exists. For example, (complex) digamma function exists [here](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Gamma/Digamma.html#Complex.digamma), where `SpherePacking.lean` redefine it as `saddleDigamma`. If it does not exist, you can keep the original proof. But you need to record this in `RefactoringResult.md`.
- Use `mathlib-quality:cleanup` skill to clean up the code.
- Although line count is not the main goal, try to reduce it as much as possible (keeping the readability). I expect to reduce at least 50% of the line count.

# Step 2

Second, you are going to separate the file into multiple files/directories under `CohnElkies` and `CohnElkiesForMathlib`.
Under `CohnElkiesForMathlib`, there will be definitions and theorems that are more likely to be upstreamed to mathlib.
It should follow the exact same directory structure as the original mathlib.
For

# Step 3

Write blueprint using [verso-blueprint](https://github.com/leanprover/verso-blueprint). You can find example template [here](https://github.com/leanprover/verso-blueprint/tree/v4.34.0/project_template).
In particular, the natural language statements and proofs should be very readable and follow the original report (except for the differences mentioned in step 1).
