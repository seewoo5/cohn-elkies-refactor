---
layout: posts
title:  "Understanding Astra's result on the high-dimensional sphere packing — Part 2: Formalization"
date:   2026-09-12
categories: jekyll update
tags: math ai
---

In the [previous post]({% post_url 2026-08-16-openai-sphere-packing-digest-part1 %}), I explained the main ideas behind Astra's proof of the optimal Cohn-Elkies LP exponent and the sharp sign-uncertainty constant.
OpenAI released Lean formalizations accompanying all ten results in the report, including the sphere-packing result.
Here I dig into the sphere-packing formalization and ask how faithfully it follows the report: what is the same, what is different, and what is missing?
My aim is to match the informal statements and proofs with their Lean counterparts. Comments inside the displayed Lean snippets are sometimes added for explanation and are not part of the original source.

## Overview of the formalization

The Lean code can be found in [`SpherePacking.lean`](https://github.com/openai/ten-proofs/blob/main/SpherePacking.lean). I checked [commit `94bc0fe`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/SpherePacking.lean), in which it is a single file of 55,616 lines.

- The repository includes [Comparator configurations](https://github.com/openai/ten-proofs/tree/main/ComparatorChallenges) and an informative [`formalization.yaml`](https://github.com/openai/ten-proofs/blob/main/formalization.yaml). The latter identifies `PackingBounds.sharpFullCohnElkiesManuscriptConclusions` as the main sphere-packing result and records its axiom and `sorry` status.
- There are *many* definitions, which makes the file difficult to navigate linearly.
- On the first day of the announcement, I remember the repository being repeatedly force-pushed, so earlier versions may not be recoverable from its public Git history.
- Some parts of the code are borrowed from the [sphere packing project](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean).
- There is no blueprint explaining the dependency structure.

So how can I read 55K lines of Lean code? There are several choices:

1. Do not read it.
2. Spend months reading it manually and put other important work aside.
3. Use AI.

I chose option 3 and used ChatGPT and Claude, relying somewhat more on ChatGPT for reading the code because the Lean code was itself produced by an OpenAI model.
I asked the models to build a table matching the theorems and lemmas in the report with declarations in the Lean file, and then checked the suggested declarations against the source.

The current file fully formalizes the Cohn-Elkies LP asymptotic in Theorem 1.1, including the passage from unrestricted admissible functions to radial ones and the bridge to the packing-density bound. Its coverage of the sign-uncertainty theorem is more limited:

| Paper item | Status in the current Lean file |
|---|---|
| LP definitions and exact limit in Theorem 1.1 | Formalized |
| Equality of the full and radial LP problems | Formalized |
| Cohn-Elkies packing bound and its sharp asymptotic consequence | Formalized |
| $L^1$ sign-eigenfunction radialization and Schwartz approximation | Not formalized in the paper's form |
| Mellin/Fourier identities | Formalized |
| Quantitative Proposition 3.1 for both eigenvalues | Not stated in this generality; estimates specialized to `AntiFourierWitness` |
| Proposition 3.7 for general $L^1$ eigenfunctions of both signs | Not formalized; Lean proves an anti-self-Fourier Schwartz obstruction |
| LP lower-bound scaling argument in Theorem 3.8 | Formalized |
| Upper Fourier pair $(f\_-,f\_+)$ | Formalized, with modified safety margins |
| Self-Fourier function $f\_0$ | Not formalized |
| Definitions and limits of $\mathsf A\_\pm(d)$ in Theorem 1.2 | Not formalized |
| Appendix A: $\mathsf A\_+(d)<\mathsf A\_-(d)$ | Not formalized |

Thus the formalization proves the main Cohn-Elkies result and an anti-self-Fourier lower sign-radius obstruction, but not the full sign-uncertainty Theorem 1.2. For the LP result, it follows the report's main strategy: a Poisson/Mellin lower bound and a perturbed-Gaussian upper construction. The main differences are the scope of the intermediate statements, the treatment of the Poisson principle, and the quantitative form of the upper-bound estimates.

## Basic definitions

Some basic definitions, including the Schwartz space and radiality, are formalized as follows:

```lean
abbrev Euclidean (d : ℕ) := EuclideanSpace ℝ (Fin d)

abbrev TestFunction (d : ℕ) := 𝓢(Euclidean d, ℂ)

def IsRealValued {d : ℕ} (f : TestFunction d) : Prop :=
  ∀ x : Euclidean d, (f x).im = 0

def IsRadial {d : ℕ} (f : TestFunction d) : Prop :=
  ∀ x y : Euclidean d, ‖x‖ = ‖y‖ → f x = f y

structure AntiFourierWitness (d : ℕ) (R : ℝ) where
  function : TestFunction d
  real : IsRealValued function
  radial : IsRadial function
  nonzero : function ≠ 0
  anti_fourier : (𝓕 function : TestFunction d) = -function
  zero_value : function (0 : Euclidean d) = 0
  eventually_nonneg :
    ∀ x : Euclidean d, R ≤ ‖x‖ → 0 ≤ (function x).re
```

An `AntiFourierWitness` is the main object in the formal lower-bound argument. It consists of a nonzero real-valued radial Schwartz function $g$ satisfying $\widehat g=-g$, $g(0)=0$, and $g(x)\ge0$ for $\lVert x\rVert\ge R$. There is no analogous "`SelfFourierWitness`" for $\widehat g=g$ in the Lean file.


### Lower bound

The main goal of the lower bound argument is to prove the following statement:

```lean
def criticalRadius : ℝ := (Real.pi)⁻¹

def UniformAntiFourierSignRadius : Prop :=
  ∀ c : ℝ, 0 < c → c < criticalRadius →
    ∀ᶠ d : ℕ in atTop,
      IsEmpty (AntiFourierWitness d (c * Real.sqrt (d : ℝ)))
```

Note that it has a dedicated name for the constant $1/\pi$, `criticalRadius`!
`UniformAntiFourierSignRadius` asserts that for every $0<c<1/\pi$, there exists a dimension threshold $d_0(c)$ such that, for all $d\ge d_0(c)$, there is no nonzero radial Schwartz function $g$ satisfying $\widehat g=-g$, $g(0)=0$, and $g(x)\ge0$ for $\lvert x\rvert\ge c\sqrt d$.
The final theorem supplies a proof of this proposition:

```lean
theorem uniformAntiFourierSignRadius :
    UniformAntiFourierSignRadius := by ...
```

To prove this, recall that we worked with the normalization $\varphi$ of $g$ and its (normalized) Mellin transform $Z$.
These definitions are formalized as follows:

```lean
-- theta
def stripAngle (σ : ℝ) : ℝ :=
  Real.pi * (1 + σ) / 2

-- P_σ
def stripPoissonKernel (σ T : ℝ) : ℝ :=
  Real.sin (stripAngle σ) /
    (4 * (Real.cosh (Real.pi * T / 2) - Real.cos (stripAngle σ)))

-- M_σ
def stripBottomMass (σ : ℝ) : ℝ :=
  (1 - σ) / 2

-- |S_d|
def radialSurfaceArea (d : ℕ) : ℝ :=
  (d : ℝ) * unitBallVolume d

-- ||g||_1
def radialL1Mass {d : ℕ} (g : TestFunction d) : ℝ :=
  ∫ x : Euclidean d, ‖g x‖

def radialUnitDirection {d : ℕ} (hd : 0 < d) : Euclidean d :=
  (EuclideanSpace.basisFun (Fin d) ℝ) ⟨0, hd⟩

def radialProfile {d : ℕ} (hd : 0 < d)
    (f : TestFunction d) (r : ℝ) : ℂ :=
  f (r • radialUnitDirection hd)

-- M
def radialMellinStrip {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (z : ℂ) : ℂ :=
  mellin (radialProfile hd f)
    ((d : ℂ) / 2 - Complex.I * z)

-- Z
def normalizedRadialMellinStrip {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (R : ℝ) (z : ℂ) : ℂ :=
  (radialSurfaceArea d / radialL1Mass f : ℝ) *
    Complex.exp
      (((d : ℂ) / 2 + Complex.I * z) *
        (Real.log R : ℂ)) *
      radialMellinStrip hd f z

-- φ
def normalizedRadialLogProfile {d : ℕ} (hd : 0 < d)
    (g : TestFunction d) (R v : ℝ) : ℝ :=
  radialSurfaceArea d / radialL1Mass g *
    (R * Real.exp v) ^ d *
    (radialProfile hd g (R * Real.exp v)).re
```

The paper's main analytic estimate for the lower bound is Proposition 3.1:

> **Proposition 3.1.** For every $0<c<1/\pi$, there exist $C\_c,\gamma\_c>0$ and $d\_0(c)\in\mathbb N$ such that, for every $d\ge d\_0(c)$, every $\varsigma\in\lbrace-1,+1\rbrace$, and every nonzero $g\in\mathcal S\_{\mathrm{rad}}(\mathbb R^d;\mathbb R)$ satisfying $\widehat g=\varsigma g$ and $g(0)=0$, one has
>
> $$
> \int_{|x| < c \sqrt{d}} |g(x)| \mathrm{d}x \le C_c e^{-\gamma_c d} \|g\|_1.
> $$

There is no theorem stating Proposition 3.1 in this generality. Lean proves the estimates needed for an `AntiFourierWitness`: besides $\widehat g=-g$, this already assumes $g(x)\ge0$ outside the given radius. This is sufficient for the LP lower bound, but it is not equivalent to Proposition 3.1, even after restricting that proposition to $\varsigma=-1$.

Here is a summary of the actual argument. Both the report and Lean use $\varphi$ and $Z$; Lean specializes the argument to these witnesses and directly derives a contradiction.

> *Proof (Lean).* One checks that $\lVert \varphi\rVert\_1=1$, $\int\varphi=0$, and $\varphi(v)\ge0$ for $v\ge0$. Therefore
>
> $$
> \int_{-\infty}^{0} |\varphi(v)| \mathrm{d}v \ge \frac{1}{2}.
> $$
>
> There exists $D\_0\in\mathbb R$ such that, for every $D\ge D\_0$, every $-1<\sigma<1$, and every $s\in\mathbb R$, the normalized Mellin transform satisfies
>
> $$
> |Z(s + i\sigma\lambda)| \le e^{H_{\sigma, D}(s)}
> $$
>
> where
>
> $$
> H_{\sigma,D}(s)=\int_{\mathbb R}P_\sigma(T)\min\{h_\lambda(s-\lambda T),D\}\,\mathrm dT\le H_\sigma(s).
> $$
>
> We can show that $H\_\sigma(s)$ is maximized at $s=0$. For $0\le\sigma<1$, the formalized bound for $H\_\sigma(0)$ is
>
> $$
> \begin{align*}
> H_\sigma(0) &\le \lambda M_\sigma \underbrace{\left(\log(2\pi e c^2) + \int_{\mathbb{R}} \frac{P_\sigma(T)}{M_\sigma} \left(-\frac{\pi|T|}{4} - \frac{1}{2} \log \left(1 + \frac{T^2}{4}\right) + \frac{|T|}{2} \arctan \left(\frac{|T|}{2}\right)\right)\mathrm{d}T\right)}_{A_\sigma} \\
> &\quad + \int_{\mathbb{R}} P_\sigma(T) \left(3 \left|\log \frac{|T|}{2}\right| + \log\left(1 + \frac{T^2}{4} \right) + \frac12 \log\coth\frac{\pi|T|}{2}\right) \mathrm{d}T
> \end{align*}
> $$
>
> Taking $\sigma \to 1^{-}$ on the right-hand side gives
>
> $$ \lim_{\sigma \to 1^{-}} \frac{P_\sigma(T)}{M_\sigma} = \frac{\pi}{4\left(\cosh\frac{\pi T}{2} + 1\right)}, \qquad \lim_{\sigma \to 1^{-}} A_\sigma = \log(\pi^2 c^2) $$
>
> where the latter limit is negative when $c<1/\pi$. Hence, for any given $0<c<1/\pi$, we can choose $\sigma=\sigma(c)<1$ and $\gamma=\gamma(c)>0$ such that
>
> $$H_\sigma(s) \le -\gamma \lambda$$
>
> for sufficiently large $\lambda = d/2$ and all $s \in \mathbb{R}$.
> We also have a separate logarithmic tail estimate: for suitable $A,B,\kappa>0$,
>
> $$ H_\sigma(\lambda S)\le-\kappa\lambda\log\frac{|S|}{A} \qquad (|S|\ge B). $$
>
> By averaging these two estimates, we obtain
>
> $$ e^{H_\sigma(\lambda S)} \le C \frac{e^{-\gamma\lambda}}{(1 + |S|)^2} $$
>
> for some constants $C,\gamma>0$, all sufficiently large $d$, and every $S\in\mathbb R$. Combining this with the pointwise estimate $\lvert Z(s+i\sigma\lambda)\rvert\le e^{H_\sigma(s)}$ above and then making the change of variables $s=\lambda S$, we obtain
>
> $$ \int_{\mathbb R}|Z(s+i\sigma\lambda)|\,\mathrm ds \le CJ\lambda e^{-\gamma\lambda}, $$
>
> where $J=\int\_{\mathbb R}(1+\lvert S\rvert)^{-2}\,\mathrm dS$.
> Mellin inversion gives
>
> $$ \int_{-\infty}^{0} |\varphi(v)| \mathrm{d}v \le \frac{1}{2\pi (1 - \sigma) \lambda} \int_{\mathbb{R}} |Z(s + i\sigma\lambda)| \mathrm{d}s $$
>
> and hence
>
> $$ \frac12\le\int_{-\infty}^{0}|\varphi(v)|\,\mathrm dv\le K e^{-\gamma\lambda}, $$
>
> which is a contradiction for sufficiently large $\lambda = d/2$.

Here is how these steps are formalized.

#### The lower bound $\frac12\le\int\_{-\infty}^{0}\lvert \varphi(v)\rvert\,\mathrm dv$

This straightforward step follows almost directly from the definition of $\varphi$ and the properties of $g$.
The formal statement is as follows:

```lean
theorem normalizedProfile_negativeHalfline_mass_ge_half {φ : ℝ → ℝ}
    (hφ : Integrable φ)
    (hmean : (∫ v : ℝ, φ v) = 0)
    (hmass : (∫ v : ℝ, |φ v|) = 1)
    (hsign : ∀ v : ℝ, 0 ≤ v → 0 ≤ φ v) :
    (1 / 2 : ℝ) ≤ ∫ v in Iic (0 : ℝ), |φ v| := by ...
```

#### The upper bound $\lvert Z(s+i\sigma\lambda)\rvert\le e^{H\_{\sigma,D}(s)}$

This is a capped version of Lemma 3.2, formalized as follows:

```lean
-- |Z(s + iσλ)| ≤ exp(∫ P_σ(T) h_{λ,D}(s - λT) dT) for sufficiently large D
theorem exists_antiFourierWitness_capped_poisson_majorization
    {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R)
    (w : AntiFourierWitness d R) :
    ∃ D₀ : ℝ,
      ∀ D : ℝ, D₀ ≤ D →
        ∀ {σ : ℝ}, -1 < σ → σ < 1 →
          ∀ s : ℝ,
            ‖normalizedRadialMellinStrip hd w.function R
              ((s : ℂ) + Complex.I *
                (((σ * ((d : ℝ) / 2) : ℝ) : ℂ)))‖ ≤
              Real.exp
                (∫ T : ℝ,
                  stripPoissonKernel σ T *
                    lowerGammaBoundaryCapped
                      ((d : ℝ) / 2) R D
                      (s - ((d : ℝ) / 2) * T)) := by ...
```

The truncation argument is explained in the final part of the proof of Lemma 3.2.
The exponent on the right-hand side is the capped Poisson majorant

$$
\int_{\mathbb{R}} P_\sigma(T) \min\{h_\lambda(s - \lambda T), D\} \mathrm{d}T
$$

Taking $D\to\infty$ gives the uncapped bound from Lemma 3.2. This is formalized as follows: `lowerStripCappedPoisson_tendsto_radius` proves convergence of the capped Poisson integrals, and `antiFourierWitness_norm_le_poisson_of_eventually_capped_radius` transfers the norm bound to the limit.

```lean
theorem lowerStripCappedPoisson_tendsto_radius
    {d : ℕ} (hd : 0 < d) {R σ : ℝ}
    (hσbelow : -1 < σ) (hσabove : σ < 1) (s : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ∫ T : ℝ,
          stripPoissonKernel σ T *
            lowerGammaBoundaryCapped ((d : ℝ) / 2)
              R (n : ℝ)
              (s - ((d : ℝ) / 2) * T))
      atTop
      (𝓝 (lowerStripPoissonMajorant ((d : ℝ) / 2)
        R σ s)) := by ...

theorem antiFourierWitness_norm_le_poisson_of_eventually_capped_radius
    {d : ℕ} (hd : 0 < d) {R σ : ℝ}
    (w : AntiFourierWitness d R)
    (hσbelow : -1 < σ) (hσabove : σ < 1) (s : ℝ)
    (hcapped : ∀ᶠ n : ℕ in atTop,
      ‖normalizedRadialMellinStrip hd w.function R
        ((s : ℂ) + Complex.I *
          (((σ * ((d : ℝ) / 2) : ℝ) : ℂ)))‖ ≤
        Real.exp
          (∫ T : ℝ,
            stripPoissonKernel σ T *
              lowerGammaBoundaryCapped ((d : ℝ) / 2)
                R (n : ℝ)
                  (s - ((d : ℝ) / 2) * T))) :
      ‖normalizedRadialMellinStrip hd w.function R
        ((s : ℂ) + Complex.I *
          (((σ * ((d : ℝ) / 2) : ℝ) : ℂ)))‖ ≤
        Real.exp
          (lowerStripPoissonMajorant ((d : ℝ) / 2)
            R σ s) := by ...
```

The Lean argument proceeds as follows.

> *Proof (Lean).* For $z\in\mathbb C$ and $y\in\mathbb R$, define
>
> $$
> K_\lambda(z,y)=\frac{i}{4\lambda}
> \frac{\exp\left(\frac{\pi(z-y+i\lambda)}{2\lambda}\right)+1}
> {\exp\left(\frac{\pi(z-y+i\lambda)}{2\lambda}\right)-1},
> $$
>
> and
>
> $$
> \widetilde K_\lambda(z,y)=K_\lambda(z,y)+
> \begin{cases}
> \dfrac{i}{4\lambda},&y\ge0,\\
> -\dfrac{i}{4\lambda},&y<0.
> \end{cases}
> $$
>
> Here $K\_\lambda$ is a holomorphic version of the Poisson kernel, while $\widetilde K\_\lambda$ is regularized so that $\widetilde K\_\lambda(z,y)\to0$ as $\lvert y\rvert\to\infty$. Define
>
> $$
> h_{\lambda,D}(y)=
> \begin{cases}
> \min\{h_\lambda(y),D\},&y\ne0,\\
> D,&y=0,
> \end{cases}
> $$
>
> and
>
> $$W_D(z) = \int_{\mathbb{R}} \widetilde{K}_\lambda(z, y) h_{\lambda, D}(y) \mathrm{d}y.$$
>
> At $z=s+i\sigma\lambda$ in the open strip, with $-1<\sigma<1$, the real part of $W_D$ is
>
> $$
> \Re W_D(s+i\sigma\lambda)
> =\int_{\mathbb R}P_\sigma(T)h_{\lambda,D}(s-\lambda T)\,\mathrm dT.
> $$
>
> The function $\Re W\_D$ has a continuous real-valued extension $H\_D$ to the closed strip, with $H\_D(s-i\lambda)=h\_{\lambda,D}(s)$ and $H\_D(s+i\lambda)=0$.
> Set $F\_D(z)=e^{-W\_D(z)}Z(z)$ in the open strip and $N\_D(z)=e^{-H\_D(z)}\lvert Z(z)\rvert$ on the closed strip. Then $F\_D$ is holomorphic, $N\_D$ is continuous, and $N\_D=\lvert F\_D\rvert$ in the interior. The boundary estimates for $Z$ give $N\_D\le1$ on both boundary lines.
> The growth condition also needs checking: boundedness of $Z$ and the bound $\lvert\Re W\_D(z)\rvert\le B(1+\lvert\Re z\rvert)$ give $\lvert F\_D(z)\rvert\le C\exp(B\lvert\Re z\rvert)$, which is sufficient for the strip Phragmén-Lindelöf principle. It follows that $N\_D\le1$ throughout the strip, and hence $\lvert Z(z)\rvert\le e^{\Re W\_D(z)}$ in the interior.

Thus, the proof starts with the complex Poisson kernel and takes its real part to recover the Poisson kernel itself; this is another difference from the report.
Note that the code uses the variable `ℓ`, which is the same as $\lambda$.
The definition `stripComplexPoissonKernel σ T` is the dimensionless version: its real part is $P\_\sigma(T)$, as proved by `stripComplexPoissonKernel_re`. More precisely,

$$
K_\lambda(s+i\sigma\lambda,y)
=\frac1\lambda\,\texttt{stripComplexPoissonKernel}\left(\sigma,\frac{s-y}{\lambda}\right).
$$

```lean
-- K_λ(z,y) = i/(4λ) * (exp(π(z-y+iλ)/(2λ)) + 1)/(exp(π(z-y+iλ)/(2λ)) - 1)
-- ℓ = λ
def stripHolomorphicPoissonKernel (ℓ : ℝ) (z : ℂ) (y : ℝ) : ℂ :=
  (Complex.I *
      ((Complex.exp
          (((Real.pi : ℂ) *
            (z - (y : ℂ) + Complex.I * (ℓ : ℂ))) /
              (2 * (ℓ : ℂ))) + 1) /
        (Complex.exp
          (((Real.pi : ℂ) *
            (z - (y : ℂ) + Complex.I * (ℓ : ℂ))) /
              (2 * (ℓ : ℂ))) - 1)) /
    4) / (ℓ : ℂ)

-- K̃_λ(z,y) = K_λ(z,y) + (if 0 ≤ y then i/(4λ) else -i/(4λ))
def stripRegularizedHolomorphicPoissonKernel
    (ℓ : ℝ) (z : ℂ) (y : ℝ) : ℂ :=
  stripHolomorphicPoissonKernel ℓ z y +
    (if 0 ≤ y then Complex.I else -Complex.I) /
      ((4 * ℓ : ℝ) : ℂ)

-- W[b](z) = ∫ K̃_λ(z,y) b(y) dy
def stripRegularizedOuter (ℓ : ℝ) (b : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ y : ℝ,
    stripRegularizedHolomorphicPoissonKernel ℓ z y *
      (b y : ℂ)

-- W_D(z) = W[h_{λ,D}](z) = ∫ K̃_λ(z,y) h_{λ,D}(y) dy
def lowerStripCappedGammaOuter
    (ℓ R D : ℝ) (z : ℂ) : ℂ :=
  stripRegularizedOuter ℓ
    (lowerGammaBoundaryCapped ℓ R D) z

-- Re K_λ(s + iσλ, y) = P_σ((s - y)/λ)/λ
theorem stripHolomorphicPoissonKernel_re
    {ℓ σ : ℝ} (hℓ : 0 < ℓ)
    (hbelow : -1 < σ) (habove : σ < 1) (s y : ℝ) :
    (stripHolomorphicPoissonKernel ℓ
      ((s : ℂ) + Complex.I * ((σ * ℓ : ℝ) : ℂ)) y).re =
      stripPoissonKernel σ ((s - y) / ℓ) / ℓ := by ...

-- Re W_D(s + iσλ) = ∫ P_σ(T) h_{λ,D}(s - λT) dT
theorem lowerStripCappedGammaOuter_re_dimension
    {d : ℕ} (hd : 0 < d) {σ R D : ℝ}
    (hσbelow : -1 < σ) (hσabove : σ < 1) (s : ℝ) :
    (lowerStripCappedGammaOuter ((d : ℝ) / 2) R D
      ((s : ℂ) + Complex.I *
        ((σ * ((d : ℝ) / 2) : ℝ) : ℂ))).re =
      ∫ T : ℝ, stripPoissonKernel σ T *
        lowerGammaBoundaryCapped
          ((d : ℝ) / 2) R D
          (s - ((d : ℝ) / 2) * T) := by ...
```

The informal proof in the report applies the upper-half-plane Poisson principle to the subharmonic function $\log\lvert Z\circ\Phi^{-1}\rvert$.
The formalized proof is slightly different: it uses a horizontal-strip version of the Phragmén-Lindelöf principle, which is a maximum-principle argument for holomorphic functions on a horizontal strip, although the underlying argument is essentially the same.

> **Phragmén–Lindelöf principle for a horizontal strip.** Let $f:\mathbb C\to\mathbb C$ be holomorphic on $\lbrace z:a<\Im z<b\rbrace$, and suppose its modulus has a continuous extension $N$ to the closed strip. Suppose that $\lvert f(z)\rvert=O(\exp(B\exp(c\lvert \Re z\rvert)))$ for some constants $B$ and $c$ with $c<\pi/(b-a)$, uniformly in the strip as $\lvert \Re z\rvert\to\infty$. If $N\le C$ on the two boundary lines for some $C>0$, then $N\le C$ throughout the strip.

This is a version of the maximum-modulus principle for a horizontal strip. The file proves it as `horizontalStrip_norm_extension_majorization`. The distinction between continuity of $f$ and continuity of its modulus matters here: the proof constructs the latter, not a continuous boundary extension of $F\_D$ itself. Mathlib's related theorem [`PhragmenLindelof.horizontal_strip`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Complex/PhragmenLindelof.html#PhragmenLindelof.horizontal_strip) assumes that $f$ is continuous on the closed strip, so it is not a direct replacement without additional boundary regularity.

The application is `antiFourierWitness_capped_poisson_majorization_of_real_extension`; the growth estimate comes from `lowerStripCappedGammaOuter_abs_re_le_linear` and `antiFourierWitness_cappedWeightedMellinStrip_growth`.

```lean
theorem horizontalStrip_norm_extension_majorization
    {a b C : ℝ} (hab : a < b) (hC : 0 < C)
    (f : ℂ → ℂ) (N : ℂ → ℝ)
    (hf : DifferentiableOn ℂ f
      (Complex.im ⁻¹' Ioo a b))
    (hN : ContinuousOn N
      (Complex.im ⁻¹' Icc a b))
    (hNnonneg : ∀ w : ℂ,
      w.im ∈ Icc a b → 0 ≤ N w)
    (hinterior : ∀ w : ℂ,
      w.im ∈ Ioo a b → N w = ‖f w‖)
    (hbottom : ∀ w : ℂ, w.im = a → N w ≤ C)
    (htop : ∀ w : ℂ, w.im = b → N w ≤ C)
    (hgrowth :
      ∃ c < Real.pi / (b - a), ∃ B : ℝ,
        Asymptotics.IsBigO
          (Filter.comap (fun w : ℂ => |w.re|)
              Filter.atTop ⊓
            Filter.principal
              (Complex.im ⁻¹' Ioo a b))
          f
          (fun w : ℂ =>
            Real.exp (B * Real.exp (c * |w.re|))))
    {z : ℂ} (hza : a ≤ z.im) (hzb : z.im ≤ b) :
    N z ≤ C := by ...
```

#### $H\_\sigma(s)\le H\_\sigma(0)$

Here is the formalization of the inequality:

```lean
theorem lowerStripPoissonMajorant_dimension_centered_max
    {d : ℕ} (hd : 2 ≤ d) {c σ : ℝ}
    (hc : 0 < c)
    (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    lowerStripPoissonMajorant ((d : ℝ) / 2)
      (c * Real.sqrt d) σ s ≤
      lowerStripPoissonMajorant ((d : ℝ) / 2)
        (c * Real.sqrt d) σ 0 := by ...
```

As mentioned in part 1, the convolution of two even, nonnegative functions that are nonincreasing on $(0,\infty)$ is maximized at the origin.
The Lean code includes a formalization of this fact, specialized to the Poisson kernel:

```lean
theorem even_antitone_poisson_convolution_max
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    {f : ℝ → ℝ} {B : ℝ}
    (hf : Integrable f)
    (hfmeas : Measurable f)
    (hfnonneg : ∀ x : ℝ, 0 ≤ f x)
    (heven : ∀ x : ℝ, f (-x) = f x)
    (hanti : AntitoneOn f (Ici (0 : ℝ)))
    (hsupport : Function.support f ⊆ Icc (-B) B)
    (s : ℝ) :
    (∫ x : ℝ, stripPoissonKernel σ (s - x) * f x) ≤
      ∫ x : ℝ, stripPoissonKernel σ (0 - x) * f x := by ...
```

The function $h\_\lambda$ itself is neither nonnegative nor compactly supported, so the lemma is not applied directly to it. Lean first uses the even, nonnegative, compactly supported function $q\_{N,D}(Y)=\max\lbrace h\_{\lambda,D}(\lambda Y)+N,0\rbrace$ (`lowerGammaScaledCappedClipped`). After applying the lemma, it subtracts $NM\_\sigma$ and removes the lower and upper truncations by dominated convergence. Finally, `lowerStripPoissonMajorant_scaled_convolution` identifies the convolution at $s/\lambda$ with $H\_\sigma(s)$.

#### $H\_\sigma(0) \le \lambda M\_\sigma (\log(2\pi c^2) + J\_\sigma) + O\_\sigma(1)$

Recall that Lemma 3.3 proves the upper bound for $H\_\sigma(0)$, treating the even- and odd-dimensional cases separately in order to estimate the difference

$$
h_\lambda(\lambda T) - \lambda\left(\log(2\pi c^2) - \int_0^1 f_T(x) \mathrm{d}x\right).
$$

The Lean proof uses the same even/odd Riemann-sum calculation, but only proves the upper estimate needed later, not the report's full weighted absolute-error estimate (19). Its unified error, `lowerRiemannPoissonError σ`, is finite and independent of $d$ and $c$ for each fixed $0\le\sigma<1$. Thus `lowerStripPoissonMajorant_dimension_central_bound` gives a one-sided $O\_\sigma(1)$ error; this does not assert a two-sided approximation.

```lean
-- f_T
def lowerRiemannLog (T x : ℝ) : ℝ :=
  Real.log (Real.sqrt (x ^ 2 + T ^ 2 / 4))

-- Combined error term
def lowerRiemannErrorMajorant (T : ℝ) : ℝ :=
  3 * |lowerRiemannLog T 0| +
    2 * |lowerRiemannLog T 1| +
      (1 / 2 : ℝ) *
        Real.log (lowerCoth (Real.pi * |T| / 2))

def lowerRiemannPoissonError (σ : ℝ) : ℝ :=
  ∫ T : ℝ,
    stripPoissonKernel σ T * lowerRiemannErrorMajorant T

-- P_σ(T)/M_σ
def stripNormalizedPoissonKernel (σ T : ℝ) : ℝ :=
  stripPoissonKernel σ T / stripBottomMass σ

def lowerEndpointPhase (T : ℝ) : ℝ :=
  -Real.pi * |T| / 4 - (1 / 2 : ℝ) * Real.log (1 + T ^ 2 / 4) +
    |T| / 2 * Real.arctan (|T| / 2)

def lowerPoissonEndpointExpectation (σ : ℝ) : ℝ :=
  ∫ T : ℝ,
    stripNormalizedPoissonKernel σ T * lowerEndpointPhase T

-- H_σ(0) ≤ λ M_σ (log(2πc^2)+J_σ) + error
theorem lowerStripPoissonMajorant_dimension_central_bound
    {d : ℕ} (hd : 2 ≤ d) {c σ : ℝ}
    (hc : 0 < c) (hzero : 0 ≤ σ) (habove : σ < 1) :
    lowerStripPoissonMajorant ((d : ℝ) / 2)
        (c * Real.sqrt d) σ 0 ≤
      ((d : ℝ) / 2) * stripBottomMass σ *
        (Real.log (2 * Real.pi * Real.exp 1 * c ^ 2) +
          lowerPoissonEndpointExpectation σ) +
        lowerRiemannPoissonError σ := by ...
```

There are some differences between the formalization and the report.
For example, the main estimate reads

$$
\begin{align*}
H_\sigma(0) &\le \lambda M_\sigma \left(\log(2\pi e c^2) + \int_{\mathbb{R}} \frac{P_\sigma(T)}{M_\sigma} \left(-\frac{\pi|T|}{4} - \frac{1}{2} \log \left(1 + \frac{T^2}{4}\right) + \frac{|T|}{2} \arctan \left(\frac{|T|}{2}\right)\right)\mathrm{d}T\right) \\
&\quad + \int_{\mathbb{R}} P_\sigma(T) \left(3 |f_T(0)| + 2 |f_T(1)| + \frac12 \log\coth\frac{\pi|T|}{2}\right) \mathrm{d}T
\end{align*}
$$

which looks different from the one in the report.
In fact, for $T\ne0$, we have

$$
-\int_{0}^{1} f_T(x)\mathrm{d}x = 1 + \left(-\frac{\pi|T|}{4} - \frac{1}{2} \log \left(1 + \frac{T^2}{4}\right) + \frac{|T|}{2} \arctan \left(\frac{|T|}{2}\right)\right)
$$

Therefore, we have

$$
\log(2\pi e c^2) + \int_{\mathbb{R}} \frac{P_\sigma(T)}{M_\sigma} \left(-\frac{\pi|T|}{4} - \frac{1}{2} \log \left(1 + \frac{T^2}{4}\right) + \frac{|T|}{2} \arctan \left(\frac{|T|}{2}\right)\right)\mathrm{d}T = \log(2\pi c^2) + J_\sigma.
$$

```lean
theorem integral_lowerRiemannLog
    {T : ℝ} (hT : T ≠ 0) :
    -(∫ x in (0 : ℝ)..1, lowerRiemannLog T x) =
      1 + lowerEndpointPhase T := by ...
```

The expression for $h\_\lambda(\lambda T)$ in terms of a Riemann sum for $f\_T$, together with an error estimate for that Riemann sum, is formalized by:

- for even $d$: `lowerGammaBoundaryLog_integer_scaled` and `lower_integer_leftRiemann_error`;
- for odd $d$: `lowerGammaBoundaryLog_halfInteger_scaled`, `lower_halfInteger_midpointRiemann_error`, and `lowerRiemannLog_halfInteger_tail_integral_le`.

The error term is slightly different: it uses the unified bound `lowerRiemannErrorMajorant` for both even and odd dimensions:

$$
3 |f_T(0)| + 2 |f_T(1)| + \frac12 \log\coth\frac{\pi|T|}{2}
$$

(`lowerCoth` is just $\coth$, but with a fancier name!)
The even- and odd-dimensional cases are then combined in the proof of `lowerGammaBoundaryLog_dimension_riemann_le` (the proof begins with `rcases d.even_or_odd ...`).
This proves the upper bound for $h\_\lambda(\lambda T)$, which is then used to prove the upper bound for $H\_\sigma(0)$.

```lean
-- h_λ(λT) ≤ λ(log(2πe c^2) + lowerEndpointPhase T) + error
theorem lowerGammaBoundaryLog_dimension_scaled_riemann_le
    {d : ℕ} (hd : 2 ≤ d) {c T : ℝ}
    (hc : 0 < c) (hT : T ≠ 0) :
    lowerGammaBoundaryLog ((d : ℝ) / 2)
        (c * Real.sqrt d) (((d : ℝ) / 2) * T) ≤
      ((d : ℝ) / 2) *
        (Real.log (2 * Real.pi * Real.exp 1 * c ^ 2) +
          lowerEndpointPhase T) +
        lowerRiemannErrorMajorant T := by ...
```

#### The limit $A\_\sigma \to \log(\pi^2 c^2)$ as $\sigma\to1^{-}$

This is essentially Lemma 3.4 of the report. More precisely, it proves

$$
\lim_{\sigma\to1^{-}} \int_{\mathbb{R}} \frac{P_\sigma(T)}{M_\sigma} \left(-\frac{\pi|T|}{4} - \frac{1}{2} \log \left(1 + \frac{T^2}{4}\right) + \frac{|T|}{2} \arctan \left(\frac{|T|}{2}\right)\right)\mathrm{d}T = \log\left(\frac{\pi}{2}\right) - 1.
$$

The argument uses the pointwise limit

$$
\lim_{\sigma\to1^{-}} \frac{P_\sigma(T)}{M_\sigma} = \frac{\pi}{4\left(\cosh\frac{\pi T}{2} + 1\right)}
$$

and the dominated convergence theorem. In Lean, this appears as `apply tendsto_integral_filter_of_dominated_convergence` in the proof of `tendsto_integral_stripNormalizedPoissonKernel_mul`.

```lean
def limitingStripPoissonDensity (T : ℝ) : ℝ :=
  Real.pi /
    (4 * (Real.cosh (Real.pi * T / 2) + 1))

theorem tendsto_stripNormalizedPoissonKernel (T : ℝ) :
    Tendsto (fun σ : ℝ => stripNormalizedPoissonKernel σ T)
      (𝓝[<] 1) (𝓝 (limitingStripPoissonDensity T)) := by ...

def limitingPoissonEndpointExpectation : ℝ :=
  ∫ T : ℝ,
    limitingStripPoissonDensity T * lowerEndpointPhase T

theorem tendsto_lowerPoissonEndpointExpectation :
    Tendsto lowerPoissonEndpointExpectation (𝓝[<] 1)
      (𝓝 limitingPoissonEndpointExpectation) := by ...

theorem limitingPoissonEndpointExpectation_eq_log_pi_div_two_sub_one :
    limitingPoissonEndpointExpectation =
      Real.log (Real.pi / 2) - 1 := by ...
```

#### $H\_\sigma(s) \le -\gamma \lambda$ for some $0 < \sigma < 1$ and $\gamma>0$, and for all sufficiently large $\lambda=d/2$

By combining the previous estimates, we obtain the first half of Lemma 3.5: $H\_\sigma(s)$ is uniformly negative, with a bound linear in $\lambda=d/2$.

```lean
theorem exists_lowerStripPoissonMajorant_uniform_negative
    {c : ℝ} (hc : 0 < c)
    (hsharp : c < Real.pi⁻¹) :
    ∃ σ γ : ℝ, 0 < σ ∧ σ < 1 ∧ 0 < γ ∧
      ∀ᶠ d : ℕ in atTop,
        ∀ s : ℝ,
          lowerStripPoissonMajorant ((d : ℝ) / 2)
            (c * Real.sqrt d) σ s ≤
              -γ * ((d : ℝ) / 2) := by ...
```

#### $e^{H\_\sigma(\lambda S)}\le C\dfrac{e^{-\gamma\lambda}}{(1+\lvert S\rvert)^2}$

The estimate is formalized as follows:

```lean
theorem exists_lowerStripPoissonMajorant_integrable_majorant
    {c : ℝ} (hc : 0 < c) (hsharp : c < Real.pi⁻¹) :
    ∃ σ γ C : ℝ, 0 < σ ∧ σ < 1 ∧ 0 < γ ∧ 0 < C ∧
      ∀ᶠ d : ℕ in atTop,
        ∀ S : ℝ,
          Real.exp
            (lowerStripPoissonMajorant ((d : ℝ) / 2)
              (c * Real.sqrt d) σ (((d : ℝ) / 2) * S)) ≤
            C * Real.exp (-γ * ((d : ℝ) / 2)) /
              (1 + |S|) ^ 2 := by ...
```

To prove this, we combine the uniform-negativity estimate (`exists_lowerStripPoissonMajorant_uniform_negative`) with the separate logarithmic-tail estimate (`exists_lowerStripPoissonMajorant_logarithmic_tail`):

```lean
theorem exists_lowerStripPoissonMajorant_logarithmic_tail
    {c σ : ℝ} (hc : 0 < c)
    (hσ : 0 ≤ σ) (hσone : σ < 1) :
    ∃ A B κ : ℝ, 0 < A ∧ 0 < B ∧ 0 < κ ∧
      ∀ d : ℕ, 2 ≤ d →
        ∀ S : ℝ, B ≤ |S| →
          lowerStripPoissonMajorant ((d : ℝ) / 2)
            (c * Real.sqrt d) σ (((d : ℝ) / 2) * S) ≤
              -κ * ((d : ℝ) / 2) * Real.log (|S| / A) := by ...
```

This says that there exist constants $A,B,\kappa>0$ such that, for all $d\ge2$ and $\lvert S\rvert\ge B$,

$$
H_\sigma(\lambda S) \le -\kappa \lambda \log\left(\frac{\lvert S\rvert}{A}\right).
$$

Here $\kappa$ is chosen as

$$
\kappa = \frac{1}{2} \int_{-1}^{1} P_\sigma(T) \mathrm{d}T.
$$

Inside `exists_lowerStripPoissonMajorant_integrable_majorant`, Lean first evaluates the uniform bound at $s=\lambda S$ (`have hnegative := hcen ...`). For sufficiently large $d$, we have $\kappa\lambda\ge4$; averaging the two bounds and halving $\gamma$ gives the inverse-square tail. The remaining bounded interval is absorbed into $C$.

#### $\int_{\mathbb R}|Z(s+i\sigma\lambda)|\,\mathrm ds \le CJ\lambda e^{-\gamma\lambda}$

```lean
theorem antiFourierWitness_interiorMellinL1_le_of_integrable_majorant
    {d : ℕ} (hd : 0 < d) {R σ γ C : ℝ}
    (hR : 0 < R) (hσbelow : -1 < σ) (hσabove : σ < 1)
    (w : AntiFourierWitness d R)
    (hpoint : ∀ s : ℝ,
      ‖normalizedRadialMellinStrip hd w.function R
        ((s : ℂ) + Complex.I *
          (((σ * ((d : ℝ) / 2) : ℝ) : ℂ)))‖ ≤
        Real.exp
          (lowerStripPoissonMajorant ((d : ℝ) / 2) R σ s))
    (hmajor : ∀ S : ℝ,
      Real.exp
        (lowerStripPoissonMajorant ((d : ℝ) / 2)
          R σ (((d : ℝ) / 2) * S)) ≤
        C * Real.exp (-γ * ((d : ℝ) / 2)) /
          (1 + |S|) ^ 2) :
    (∫ s : ℝ,
      ‖normalizedRadialMellinStrip hd w.function R
        ((s : ℂ) + Complex.I *
          (((σ * ((d : ℝ) / 2) : ℝ) : ℂ)))‖) ≤
      (C * lowerInverseQuadraticMass) *
        ((d : ℝ) / 2) * Real.exp (-γ * ((d : ℝ) / 2)) := by ...
```

The inverse-quadratic estimate is therefore a convenient corollary of the uniform-negativity and logarithmic-tail estimates already present in Lemma 3.5; it is not substantively stronger than the result in the report. The declaration `antiFourierWitness_interiorMellinL1_le_of_integrable_majorant` then integrates this and obtains

$$
\int_{\mathbb R}|Z(s+i\sigma\lambda)|\,\mathrm ds
\le C J\lambda e^{-\gamma\lambda},
\qquad
J=\int_{\mathbb R}\frac{\mathrm dS}{(1+|S|)^2}.
$$

#### $\int\_{-\infty}^{0} \lvert \varphi(v)\rvert \mathrm{d}v \le \frac{1}{2\pi (1 - \sigma) \lambda} \int\_{\mathbb{R}} \lvert Z(s + i\sigma\lambda)\rvert \mathrm{d}s$

This is the first inequality in equation (27) of the report, formalized abstractly as follows:

```lean
theorem negativeHalfline_le_of_fourierInversion
    {φ : ℝ → ℝ} (hφ : Integrable φ)
    {a : ℝ} (ha : 0 < a) (Z : ℝ → ℂ)
    (hinversion : ∀ v : ℝ,
      (φ v : ℂ) = (Real.exp (a * v) : ℂ) *
        ((𝓕⁻ (fun ξ : ℝ => Z (2 * Real.pi * ξ)) : ℝ → ℂ) v)) :
    (∫ v in Iic (0 : ℝ), |φ v|) ≤
      ((2 * Real.pi)⁻¹ * ∫ s : ℝ, ‖Z s‖) / a := by ...
```

`𝓕⁻` is the [inverse Fourier transform](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Fourier/Notation.html#FourierTransformInv). In our application, the theorem's real-frequency function `Z` is instantiated by $s\mapsto Z(s+i\sigma\lambda)$, and `hinversion` becomes

$$
\varphi(v) = \frac{e^{(1-\sigma)\lambda v}}{2\pi} \int_{\mathbb{R}} Z(s + i\sigma\lambda) e^{i s v} \mathrm{d}s.
$$

But what is $a$?
In the final application, it is

$$
a=(1-\sigma)\frac d2=(1-\sigma)\lambda.
$$

This choice becomes visible only after tracing a chain of four small wrapper theorems down to `no_antiFourierWitness_of_interiorMellinL1_lt_half`:

```lean
theorem no_antiFourierWitness_of_interiorMellinL1_lt_half
    {d : ℕ} (hd : 0 < d) {R σ : ℝ} (hR : 0 < R)
    (hσbelow : -1 < σ) (hσabove : σ < 1)
    (w : AntiFourierWitness d R)
    (hsmall :
      ((2 * Real.pi)⁻¹ *
        ∫ s : ℝ,
          ‖normalizedRadialMellinStrip hd w.function R
            ((s : ℂ) + Complex.I *
              (((σ * ((d : ℝ) / 2) : ℝ) : ℂ)))‖) /
          ((1 - σ) * ((d : ℝ) / 2)) <
        (1 / 2 : ℝ)) : False := by
  have hℓ : 0 < (d : ℝ) / 2 :=
    half_pos (Nat.cast_pos.mpr hd)
  have ha : 0 < (1 - σ) * ((d : ℝ) / 2) :=
    mul_pos (sub_pos.mpr hσabove) hℓ
  have haless :
      (1 - σ) * ((d : ℝ) / 2) < (d : ℝ) := by
    nlinarith [mul_pos (by linarith : 0 < 1 + σ) hℓ]
  have hheight :
      (d : ℝ) / 2 - (1 - σ) * ((d : ℝ) / 2) =
        σ * ((d : ℝ) / 2) := by
    ring
  apply no_antiFourierWitness_of_shiftedMellinL1_lt_half
    hd hR w ha haless
  simpa [hheight] using! hsmall
```

The local hypothesis `ha` proves that this choice of $a$ is positive. After this specialization, `negativeHalfline_le_of_fourierInversion` gives

$$
\int_{-\infty}^{0} |\varphi(v)| \mathrm{d}v \le \frac{1}{2\pi (1 - \sigma) \lambda} \int_{\mathbb{R}} |Z(s + i\sigma\lambda)| \mathrm{d}s.
$$

The proof takes absolute values in the inversion formula and integrates over $v\in(-\infty,0]$, using

$$
\int_{-\infty}^{0}e^{(1-\sigma)\lambda v}\,\mathrm dv
=\frac{1}{(1-\sigma)\lambda}.
$$

Finally, `balancedAntiFourierWitness` implements the dilation and the difference $\widehat h-h$ from Theorem 3.8. The declarations `normalizedCost_ge_of_no_antiFourierWitness` and `uniformAdmissibleLowerBound_of_signRadius` turn the obstruction just proved into the LP lower bound. Thus this last step follows the report's scaling argument as well.

### Upper bound

The formalization of the proof of the upper bound is similar to the original proof in the report.
However, there are still some differences in the details, including the fact that the formalization does not construct $f_0$ and uses slightly different parameters in the construction of $h$.
The natural language translation of the Lean proof is given below.

> *Proof (Lean).* Fix a sufficiently small $\varepsilon>0$, put $\lambda=d/2$ and $\beta=\varepsilon/4$, and use the negative and positive weights $w=w\_s+w\_B$ to define
>
> $$
> h(\zeta)=\int_0^\infty w(a)(\cos(a\zeta)-1)\,\mathrm da,
> \qquad
> E_\lambda(t)=\pi^{it/2}\Gamma\left(\frac{\lambda-it}{2}\right)e^{\lambda h(t/\lambda)}.
> $$
>
> With $P\_\pm(\zeta)=1+\zeta^2+\beta\pm i\zeta(1+\zeta^2)$, define
>
> $$
> f_\pm(r)=\frac{r^{-\lambda}}{2\pi}
> \int_{\mathbb R}E_\lambda(t)P_\pm(t/\lambda)r^{it}\,\mathrm dt
> \qquad(r>0).
> $$
>
> Upward contour shifts prove rapid decay at infinity. Downward shifts past the poles $t=-i(\lambda+2n)$ give polynomials in $r^2$ with controlled remainders, proving smoothness at zero. The first residue gives
>
> $$
> f_-(0)=f_+(0)=2\pi^{\lambda/2}e^{\lambda h(-i)}\beta>0.
> $$
>
> The symmetries of $h$ and $P\_\pm$, together with the Mellin/Fourier identity, show that these are real-valued radial Schwartz functions satisfying $\widehat f\_-=f\_+$.
>
> To determine their signs, shift to $t=\lambda(T+iu)$ with $u>-1$, crossing no poles. Choose
>
> $$
> v(u)=-\frac12\log\pi+\frac12\psi\left(\frac{\lambda(1+u)}2\right)+ih'(iu),
> \qquad r(u)=e^{v(u)}.
> $$
>
> Define $\mathcal L\_u$ as
>
> $$
> \mathcal{L}_u(T) = \log\frac{E_\lambda(\lambda(T+iu))}{E_\lambda(i\lambda u)} + i\lambda T v(u).
> $$
>
> Then we can rewrite $f\_\pm(r(u))$ as
>
> $$
> f_\pm(r(u))=
> \underbrace{\frac{\lambda E_\lambda(i\lambda u)}{2\pi}
> r(u)^{-(1+u)\lambda}}_{>0}
> I_\pm(u),
> \qquad
> I_\pm(u)=\int_{\mathbb R}e^{\mathcal L_u(T)}P_\pm(T+iu)\,\mathrm dT.
> $$
>
> Here $\mathcal L\_u(0)=\mathcal L\_u^{\prime}(0)=0$ and $\mathcal L\_u^{\prime\prime}(0)=-\lambda V(u)$, where $V(u)=v^{\prime}(u)$. Put
>
> $$
> u_\ast=-1+\frac{\log\lambda}{4\lambda},\qquad
> u_0=1+\frac\varepsilon4,\qquad U=1+\frac\varepsilon2.
> $$
>
> The weight estimates give $V(u)>0$ and control the tails of the integral in two ranges: on $[u\_\ast,U]$, the Gamma factor controls the negative weight; for $u\ge U$, the positive weight supplies the required bounds. On the central interval $\lvert T\rvert\le T\_\ast$, Taylor estimates compare the integrand with $P\_\pm(iu)e^{-\lambda V(u)T^2/2}$, using
>
> $$
> T_\ast=\frac{K}{\sqrt{\lambda V(u)}},\qquad
> K=\begin{cases}
> (\lambda(1+u))^{1/12},&u_\ast\le u\le U,\\
> \lambda^{1/12},&u>U.
> \end{cases}
> $$
>
> Combining the central error with the two tails (of the original integrand and of the Gaussian) gives, for all sufficiently large $d$,
>
> $$
> \left|I_\pm(u)-P_\pm(iu)\sqrt{\frac{2\pi}{\lambda V(u)}}\right|
> <|P_\pm(iu)|\sqrt{\frac{2\pi}{\lambda V(u)}}.
> $$
>
> This holds uniformly for $u\ge u\_\ast$ for the plus sign and $u\ge u\_0$ for the minus sign. Thus $P\_+(iu)>0$ and $P\_-(iu)<0$ on the respective ranges determine the signs of $f\_\pm(r(u))$. The radius-coverage lemmas show that every $r\ge r\_\ast:=r(u\_\ast)$ and every $r\ge R\_{\varepsilon,d}:=r(u\_0)$ is reached in the corresponding range.
>
> It remains to prove $f\_+(r)>0$ for $0\le r\le r\_\ast$. For $r>0$, the downward contour shift gives
>
> $$
> \frac{f_+(r)}{f_+(0)}
> =\underbrace{\sum_{n=0}^N\frac{(-y)^n}{n!}A_{\lambda,n}}_{S_N(y)}
> +\mathcal R_\lambda(r),
> \qquad
> y=\pi r^2\exp\left(2\int_0^\infty w(a)a\sinh(a)\,\mathrm da\right).
> $$
>
> The coefficients $A\_{\lambda,n}$ are close to $1$. Since $y\le\frac18\log\lambda+O\_\varepsilon(1)$ on this interval, taking $N=\lceil20\log\lambda\rceil$ gives
>
> $$
> e^y|S_N(y)-e^{-y}|<\frac12,
> \qquad e^y|\mathcal R_\lambda(r)|<\frac12.
> $$
>
> Their sum gives $f\_+(r)/f\_+(0)>0$; the value at $r=0$ was already checked. We now have $f\_+>0$ everywhere and $f\_-<0$ for $r\ge R\_{\varepsilon,d}$.
>
> Finally, the digamma asymptotic and the weight integrals give $R\_{\varepsilon,d}/\sqrt d\to\alpha\_\varepsilon$ as $d\to\infty$, with $\alpha\_\varepsilon\to1/\pi$ as $\varepsilon\to0^+$. Rescaling $F(x)=f\_-(R\_{\varepsilon,d}x)$ produces an LP-admissible function, with
>
> $$
> \frac{F(0)}{\widehat F(0)}=R_{\varepsilon,d}^{\,d},
> \qquad
> \mathrm{LP}_d^{1/d}\le\frac{v_d^{1/d}}2 R_{\varepsilon,d}.
> $$
>
> Here $v\_d$ is the unit-ball volume. Stirling's formula, first letting $d\to\infty$ and then $\varepsilon\to0^+$, gives $\limsup\_{d\to\infty}\mathrm{LP}\_d^{1/d}\le\sqrt{e/(2\pi)}$, matching the lower bound. $\square$


#### Definition of $f\_\pm$ and parameter choices

The following definitions are the parameters $a_0$, $A$, $B$, $Q$, $b(a)$, $\beta$, the weight functions $w_s$, $w_B$, perturbation $h$, and the polynomials $P_+, P_-$, in terms of $\varepsilon$.

```lean
-- a₀ = ε³.
def shortCutoff (ε : ℝ) : ℝ := ε ^ 3

-- A = 10 log(1/ε).
def shortEndpoint (ε : ℝ) : ℝ := 10 * Real.log (1 / ε)

-- B = ε⁻³.
def shellLocation (ε : ℝ) : ℝ := ε⁻¹ ^ 3

-- Q = exp(−3εB/8).
def shellWeight (ε : ℝ) : ℝ :=
  Real.exp (-(3 : ℝ) * ε * shellLocation ε / 8)

-- b(a) = 1 − 10ε(1 + a).
def shortMargin (ε a : ℝ) : ℝ := 1 - 10 * ε * (1 + a)

-- β = ε/4.
def beta (ε : ℝ) : ℝ := ε / 4

-- wₛ(a) = −b(a)e⁻²ᵃ/(2a² cosh a), used on [a₀, A].
def shortShellDensity (ε a : ℝ) : ℝ :=
  -(shortMargin ε a * Real.exp (-2 * a) /
    (2 * a ^ 2 * Real.cosh a))

-- w_B(a) = Q/cosh a, used on [B, B + 1].
def positiveShellDensity (ε a : ℝ) : ℝ :=
  shellWeight ε / Real.cosh a

-- h(ζ) = ∫ w(a)(cos(aζ) − 1) da = ∫ w_S(a)(cos(aζ) − 1) da + ∫ w_B(a)(cos(aζ) − 1) da.
def mellinShellPhase (ε : ℝ) (z : ℂ) : ℂ :=
  (∫ a in shortCutoff ε..shortEndpoint ε,
    (shortShellDensity ε a : ℂ) *
      (Complex.cos ((a : ℂ) * z) - 1)) +
  (∫ a in shellLocation ε..shellLocation ε + 1,
    (positiveShellDensity ε a : ℂ) *
      (Complex.cos ((a : ℂ) * z) - 1))

-- P₊(ζ) = 1 + ζ² + β + iζ(1 + ζ²).
def plusPolynomial (ε : ℝ) (z : ℂ) : ℂ :=
  1 + z ^ 2 + (beta ε : ℂ) + Complex.I * z * (1 + z ^ 2)

-- P₋(ζ) = 1 + ζ² + β − iζ(1 + ζ²).
def minusPolynomial (ε : ℝ) (z : ℂ) : ℂ :=
  1 + z ^ 2 + (beta ε : ℂ) - Complex.I * z * (1 + z ^ 2)
```

You can see that the parameter choices are slightly different from the report (their "scales" are the same). The following table summarizes the differences.

| Parameter | Report | Lean |
|---|---|---|
| Lower cutoff $a\_0$ | $\varepsilon^2$ | $\varepsilon^3$ (`shortCutoff`) |
| Upper cutoff $A$ | $\log(1/\varepsilon)$ | $10\log(1/\varepsilon)$ (`shortEndpoint`) |
| Factor $b(a)$ in the negative weight $w_s$ | $1-2\varepsilon(1+a)$ | $1-10\varepsilon(1+a)$ (`shortMargin`) |
| Residue cutoff $N$ | $\lceil\log\lambda\rceil$ | $\lceil20\log\lambda\rceil$ (`saddleSmallResidueTruncation`) |

The next three definitions are exactly the perturbed Gamma factor $E_\lambda(t) := E_\lambda^G(T) \exp(\lambda h(t/\lambda))$ and the Mellin transforms $X_+$, $X_-$.

```lean
-- Eλ(t) = π^(it/2) Γ((λ − it)/2) exp(λh(t/λ)).
def saddleEnvelope (ε ℓ t : ℝ) : ℂ :=
  Complex.exp
      (Complex.I * (t : ℂ) * (Real.log Real.pi : ℂ) / 2) *
    Complex.Gamma (((ℓ : ℂ) - Complex.I * (t : ℂ)) / 2) *
    Complex.exp ((ℓ : ℂ) *
      mellinShellPhase ε ((t : ℂ) / (ℓ : ℂ)))

-- X₊(t) = Eλ(t)P₊(t/λ).
def plusSaddleSpectrum (ε ℓ t : ℝ) : ℂ :=
  saddleEnvelope ε ℓ t *
    plusPolynomial ε ((t : ℂ) / (ℓ : ℂ))

-- X₋(t) = Eλ(t)P₋(t/λ).
def minusSaddleSpectrum (ε ℓ t : ℝ) : ℂ :=
  saddleEnvelope ε ℓ t *
    minusPolynomial ε ((t : ℂ) / (ℓ : ℂ))
```

For contour integration, Lean switches to the usual Mellin variable $z=\lambda-it$. Thus $t/\lambda=i(z-\lambda)/\lambda$, and the Gamma factor becomes $\Gamma(z/2)$. The following definitions express the same functions in this coordinate; `plusSaddleMellinData_vertical` checks the correspondence explicitly. There is an analogous theorem for the minus sign.

```lean
-- Eλ in the coordinate z = λ − it.
def saddleMellinEnvelope (ε ℓ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp
      (((ℓ : ℂ) - z) * (Real.log Real.pi : ℂ) / 2) *
    Complex.Gamma (z / 2) *
    Complex.exp ((ℓ : ℂ) *
      mellinShellPhase ε
        (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ)))

-- M₊(z) = Eλ(i(z − λ))P₊(i(z − λ)/λ).
def plusSaddleMellinData (ε ℓ : ℝ) (z : ℂ) : ℂ :=
  saddleMellinEnvelope ε ℓ z *
    plusPolynomial ε
      (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ))

-- M₋(z) = Eλ(i(z − λ))P₋(i(z − λ)/λ).
def minusSaddleMellinData (ε ℓ : ℝ) (z : ℂ) : ℂ :=
  saddleMellinEnvelope ε ℓ z *
    minusPolynomial ε
      (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ))

-- M₊(λ − it) = X₊(t).
theorem plusSaddleMellinData_vertical (ε ℓ t : ℝ) :
    plusSaddleMellinData ε ℓ
      ((ℓ : ℂ) - Complex.I * (t : ℂ)) =
        plusSaddleSpectrum ε ℓ t := by ...
```

The radializations $f\_\pm(r)$ are inverse Mellin transforms away from zero. Their common value at zero is defined as `saddleOriginValue`, whose agreement with the smooth extension is justified in the next subsection. The functions on $\mathbb R^d$ are obtained by substituting $r=\lVert x\rVert$.

```lean
-- f₊(r): inverse Mellin transform for r ≠ 0, prescribed value at r = 0.
def plusSaddleProfile (ε ℓ r : ℝ) : ℂ :=
  if r = 0 then (saddleOriginValue ε ℓ : ℂ)
  else mellinInv ℓ (plusSaddleMellinData ε ℓ) r

-- f₋(r): inverse Mellin transform for r ≠ 0, the same value at r = 0.
def minusSaddleProfile (ε ℓ r : ℝ) : ℂ :=
  if r = 0 then (saddleOriginValue ε ℓ : ℂ)
  else mellinInv ℓ (minusSaddleMellinData ε ℓ) r

-- x ↦ f₊(‖x‖), with λ = d/2.
def plusSaddleFunction (ε : ℝ) (d : ℕ) (x : Euclidean d) : ℂ :=
  plusSaddleProfile ε ((d : ℝ) / 2) ‖x‖

-- x ↦ f₋(‖x‖), with λ = d/2.
def minusSaddleFunction (ε : ℝ) (d : ℕ) (x : Euclidean d) : ℂ :=
  minusSaddleProfile ε ((d : ℝ) / 2) ‖x‖

-- The common value at the origin.
def saddleOriginValue (ε ℓ : ℝ) : ℝ :=
  2 * Real.pi ^ (ℓ / 2) *
    Real.exp (ℓ * realHyperbolicShellPhase ε 1) * beta ε
```

To see the normalization hidden in `mellinInv`, one can use the next identity. It parametrizes the upward vertical line by $z=\lambda+it$, so $\mathrm{d}z=i\,\mathrm{d}t$ cancels the $i$ in $1/(2\pi i)$. Replacing $t$ by $-t$ recovers the inverse-transform formula in the overview.

```lean
-- The inverse-Mellin factor r⁻ᶻ.
def saddleMellinInversePower (r : ℝ) (z : ℂ) : ℂ :=
  (r : ℂ) ^ (-z)

-- f₊(r) = (1/2π) ∫ r^(−λ−it) M₊(λ + it) dt, for r > 0.
theorem plusSaddleProfile_eq_normalized_vertical_integral
    {ε ℓ r : ℝ} (hr : 0 < r) :
    plusSaddleProfile ε ℓ r =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          saddleMellinInversePower r
            ((ℓ : ℂ) + (t : ℂ) * Complex.I) *
            plusSaddleMellinData ε ℓ
              ((ℓ : ℂ) + (t : ℂ) * Complex.I)) := by ...

-- f₋(r) = (1/2π) ∫ r^(−λ−it) M₋(λ + it) dt, for r > 0.
theorem minusSaddleProfile_eq_normalized_vertical_integral
    {ε ℓ r : ℝ} (hr : 0 < r) :
    minusSaddleProfile ε ℓ r =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          saddleMellinInversePower r
            ((ℓ : ℂ) + (t : ℂ) * Complex.I) *
            minusSaddleMellinData ε ℓ
              ((ℓ : ℂ) + (t : ℂ) * Complex.I)) := by ...
```

The profiles are real-valued by conjugation symmetry. Radiality follows directly from the definitions above.

```lean
-- Im f₊(x) = 0.
theorem plusSaddleFunction_real (ε : ℝ) (d : ℕ)
    (x : Euclidean d) :
    (plusSaddleFunction ε d x).im = 0 := by ...

-- Im f₋(x) = 0.
theorem minusSaddleFunction_real (ε : ℝ) (d : ℕ)
    (x : Euclidean d) :
    (minusSaddleFunction ε d x).im = 0 := by ...
```

These raw functions still have to be proved Schwartz. `SaddleSourceSchwartzRealization` states that they are represented by actual `TestFunction` objects, and `saddleSourceSchwartzRealization` proves it using `plusSaddleSchwartz` and `minusSaddleSchwartz`. Those constructions combine smoothness at zero with rapid decay obtained by shifting the Mellin contour.

```lean
-- The explicit functions f₋ and f₊ have Schwartz realizations.
def SaddleSourceSchwartzRealization : Prop :=
  ∀ ε : ℝ, 0 < ε →
    shortCutoff ε ≤ shortEndpoint ε →
      ∀ d : ℕ, 0 < d →
        ∃ fminus fplus : TestFunction d,
          (∀ x : Euclidean d,
            fminus x = minusSaddleFunction ε d x) ∧
          (∀ x : Euclidean d,
            fplus x = plusSaddleFunction ε d x)

-- Construct those Schwartz realizations.
theorem saddleSourceSchwartzRealization :
    SaddleSourceSchwartzRealization := by ...
```

Finally, the Fourier-pair theorem applies to any Schwartz realizations of these explicit functions. Its proof compares their radial Mellin transforms, uses the Mellin/Fourier multiplier identity, and then applies injectivity. Thus `hminus` and `hplus` identify the functions; they are not additional analytic assumptions.

```lean
-- Fourier(f₋) = f₊.
theorem saddleSource_fourier_minus_eq_plus
    {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (fminus fplus : TestFunction d)
    (hminus : ∀ x : Euclidean d,
      fminus x = minusSaddleFunction ε d x)
    (hplus : ∀ x : Euclidean d,
      fplus x = plusSaddleFunction ε d x) :
    (𝓕 fminus : TestFunction d) = fplus := by ...
```

#### Values at the origin

Lean names the real function $u\mapsto h(iu)$ separately. Since $h$ is even, its value at $u=1$ is also $h(-i)$. This explains the formula for `saddleOriginValue`.

```lean
-- h(iu) = ∫ w(a)(cosh(au) − 1) da, as a real number.
def realHyperbolicShellPhase (ε u : ℝ) : ℝ :=
  (∫ a in shortCutoff ε..shortEndpoint ε,
    shortShellDensity ε a * (Real.cosh (a * u) - 1)) +
  (∫ a in shellLocation ε..shellLocation ε + 1,
    positiveShellDensity ε a * (Real.cosh (a * u) - 1))

-- The complex phase at iu equals its real hyperbolic expression.
theorem mellinShellPhase_imaginary (ε u : ℝ) :
    mellinShellPhase ε (Complex.I * (u : ℂ)) =
      (realHyperbolicShellPhase ε u : ℂ) := by ...

-- f₊(0) = f₋(0) = 2π^(λ/2) exp(λh(−i))β.
def saddleOriginValue (ε ℓ : ℝ) : ℝ :=
  2 * Real.pi ^ (ℓ / 2) *
    Real.exp (ℓ * realHyperbolicShellPhase ε 1) * beta ε

-- The common origin value is positive when ε > 0.
theorem saddleOriginValue_pos {ε : ℝ} (hε : 0 < ε) (ℓ : ℝ) :
    0 < saddleOriginValue ε ℓ := by ...

-- P₊(−i) = β.
theorem plusPolynomial_neg_I (ε : ℝ) :
    plusPolynomial ε (-Complex.I) = (beta ε : ℂ) := by ...

-- P₋(−i) = β.
theorem minusPolynomial_neg_I (ε : ℝ) :
    minusPolynomial ε (-Complex.I) = (beta ε : ℂ) := by ...
```

To relate this assigned value to the inverse Mellin integral, factor the Mellin data as $\Gamma(z/2)$ times a holomorphic factor. The residues at $z=-2n$ are then $2(-1)^n/n!$ times that factor.

```lean
-- The common Mellin factor after removing Γ(z/2).
def saddleRegularMellinFactor (ε ℓ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp
      (((ℓ : ℂ) - z) * (Real.log Real.pi : ℂ) / 2) *
    Complex.exp ((ℓ : ℂ) *
      mellinShellPhase ε
        (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ)))

-- M₊(z) = Γ(z/2) times this holomorphic factor.
def plusSaddleRegularMellinFactor (ε ℓ : ℝ) (z : ℂ) : ℂ :=
  saddleRegularMellinFactor ε ℓ z *
    plusPolynomial ε
      (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ))

-- M₋(z) = Γ(z/2) times this holomorphic factor.
def minusSaddleRegularMellinFactor (ε ℓ : ℝ) (z : ℂ) : ℂ :=
  saddleRegularMellinFactor ε ℓ z *
    minusPolynomial ε
      (Complex.I * (z - (ℓ : ℂ)) / (ℓ : ℂ))

-- Residue of M₊ at z = −2n.
def plusSaddlePoleResidue (ε ℓ : ℝ) (n : ℕ) : ℂ :=
  (2 : ℂ) * (-1 : ℂ) ^ n / (n.factorial : ℂ) *
    plusSaddleRegularMellinFactor ε ℓ
      (-((2 * n : ℕ) : ℂ))

-- Residue of M₋ at z = −2n.
def minusSaddlePoleResidue (ε ℓ : ℝ) (n : ℕ) : ℂ :=
  (2 : ℂ) * (-1 : ℂ) ^ n / (n.factorial : ℂ) *
    minusSaddleRegularMellinFactor ε ℓ
      (-((2 * n : ℕ) : ℂ))

-- The residue at z = 0 is the assigned value f₊(0).
theorem plusSaddlePoleResidue_zero
    {ε ℓ : ℝ} (hℓ : 0 < ℓ) :
    plusSaddlePoleResidue ε ℓ 0 =
      (saddleOriginValue ε ℓ : ℂ) := by ...

-- The residue at z = 0 is the assigned value f₋(0).
theorem minusSaddlePoleResidue_zero
    {ε ℓ : ℝ} (hℓ : 0 < ℓ) :
    minusSaddlePoleResidue ε ℓ 0 =
      (saddleOriginValue ε ℓ : ℂ) := by ...
```

There is no missing factor $i$: these are residues in the $z$-coordinate, where $\operatorname{Res}_{z=0}\Gamma(z/2)=2$. In Part 1's $t$-coordinate, the corresponding Gamma residue is $2i$.

The contour-shift identity below makes the connection with the radial function. The term $n=0$ is the origin value, and all other residue terms contain positive powers of $r^2$. The minus version is `minusSaddleProfile_eq_residue_sum_add_remainder`.

```lean
-- f₊(r) = Σₙ₌₀ᴺ Resₙ r²ⁿ + contour remainder.
theorem plusSaddleProfile_eq_residue_sum_add_remainder
    {ε ℓ r : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r) (N : ℕ) :
    plusSaddleProfile ε ℓ r =
      (∑ n ∈ Finset.range (N + 1),
        plusSaddlePoleResidue ε ℓ n *
          ((r ^ (2 * n) : ℝ) : ℂ)) +
      plusSaddleTaylorRemainder ε ℓ N r := by ...
```

Controlling the remainder as $r\to0$ justifies continuity. Shifting farther left gives as much differentiability as needed. In particular, `plusSaddleProfile_eq_squaredTaylor` and its minus counterpart rewrite the expansion as a function of $r^2$; composing with $x\mapsto\lVert x\rVert^2$ proves smoothness even at $x=0$. This is stronger than simply assigning a value in the definition.

```lean
-- The radial function f₊ is C∞, including at x = 0.
theorem plusSaddleFunction_contDiff
    {ε : ℝ} (hε : 0 < ε)
    {d : ℕ} (hd : 0 < d)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    ContDiff ℝ ∞ (plusSaddleFunction ε d) := by ...

-- The radial function f₋ is C∞, including at x = 0.
theorem minusSaddleFunction_contDiff
    {ε : ℝ} (hε : 0 < ε)
    {d : ℕ} (hd : 0 < d)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    ContDiff ℝ ∞ (minusSaddleFunction ε d) := by ...

-- The defined f₊ takes the common origin value at x = 0.
@[simp] theorem plusSaddleFunction_zero (ε : ℝ) (d : ℕ) :
    plusSaddleFunction ε d (0 : Euclidean d) =
      (saddleOriginValue ε ((d : ℝ) / 2) : ℂ) := by ...

-- The defined f₋ takes the same origin value at x = 0.
@[simp] theorem minusSaddleFunction_zero (ε : ℝ) (d : ℕ) :
    minusSaddleFunction ε d (0 : Euclidean d) =
      (saddleOriginValue ε ((d : ℝ) / 2) : ℂ) := by ...
```

#### Sign analysis

First, here are the logarithmic radius $v(u)$ and the two radius thresholds. The integral terms in `saddleLogRadius` equal $ih^{\prime}(iu)$. Notice that the parameter `ε` in `saddleSmallRadiusStarOrdinate` is unused mathematically: $u\_\ast$ depends only on $d$.

```lean
-- ψ(x) = (log Γ)′(x).
def saddleDigamma (x : ℝ) : ℝ :=
  deriv (Real.log ∘ Real.Gamma) x

-- v(u) = −½ log π + ½ψ(λ(1 + u)/2) + ih′(iu).
def saddleLogRadius (ε : ℝ) (d : ℕ) (u : ℝ) : ℝ :=
  -(Real.log Real.pi) / 2 +
    saddleDigamma (((d : ℝ) / 2) * (1 + u) / 2) / 2 +
    (∫ a in shortCutoff ε..shortEndpoint ε,
      shortShellDensity ε a * a * Real.sinh (u * a)) +
    (∫ a in shellLocation ε..shellLocation ε + 1,
      positiveShellDensity ε a * a * Real.sinh (u * a))

-- u★ = −1 + log λ/(4λ).
def saddleSmallRadiusStarOrdinate (ε : ℝ) (d : ℕ) : ℝ :=
  let _sourceParameter : ℝ := ε
  show ℝ from
    -1 + Real.log ((d : ℝ) / 2) /
      (4 * ((d : ℝ) / 2))

-- r★ = exp(v(u★)).
def saddleSmallRadiusStar (ε : ℝ) (d : ℕ) : ℝ :=
  Real.exp
    (saddleLogRadius ε d
      (saddleSmallRadiusStarOrdinate ε d))

-- Rε,d = exp(v(1 + ε/4)).
def saddleSourceRadius (ε : ℝ) (d : ℕ) : ℝ :=
  Real.exp (saddleLogRadius ε d (1 + ε / 4))
```

The analytic estimates often take a real parameter `ℓ`, rather than a dimension `d`. `saddleSourceStationaryLogRadius` is the same $v(u)$ in that notation; the equality below lets Lean move between the two forms.

```lean
-- The stationary logarithmic radius v(u), with λ a real parameter.
def saddleSourceStationaryLogRadius
    (ε ℓ u : ℝ) : ℝ :=
  -(Real.log Real.pi) / 2 +
    saddleDigamma (ℓ * (1 + u) / 2) / 2 +
      saddleSourceShellDerivative ε u

-- The two definitions of v(u) agree when λ = d/2.
theorem saddleSourceStationaryLogRadius_eq_saddleLogRadius
    (ε : ℝ) (d : ℕ) (u : ℝ) :
    saddleSourceStationaryLogRadius ε ((d : ℝ) / 2) u =
      saddleLogRadius ε d u := by ...
```

**The shifted integral.** The contour $t=\lambda(T+iu)$ becomes $z=\lambda(1+u)-i\lambda T$. Lean divides the Mellin factor on this contour by the positive number $E\_\lambda(i\lambda u)$, then multiplies by $e^{i\lambda Tv}$. At $v=v(u)$, `saddleSourceCenteredEnvelope` is precisely $e^{\mathcal L_u(T)}$.

```lean
-- z(T) = λ(1 + u) − iλT.
def saddleSourceMellinContour (ℓ u T : ℝ) : ℂ :=
  ((ℓ * (1 + u) : ℝ) : ℂ) -
    Complex.I * ((ℓ * T : ℝ) : ℂ)

-- Eλ(iλu), a positive real number for λ > 0 and u > −1.
def saddleSourceContourEnvelopeScale
    (ε ℓ u : ℝ) : ℝ :=
  Real.exp (-(ℓ * u) * Real.log Real.pi / 2) *
    Real.Gamma (ℓ * (1 + u) / 2) *
      Real.exp (ℓ * realHyperbolicShellPhase ε u)

-- Eλ(λ(T + iu))/Eλ(iλu).
def saddleSourceNormalizedEnvelope
    (ε ℓ u T : ℝ) : ℂ :=
  saddleMellinEnvelope ε ℓ
      (saddleSourceMellinContour ℓ u T) /
    (saddleSourceContourEnvelopeScale ε ℓ u : ℂ)

-- The normalized factor multiplied by exp(iλTv).
def saddleSourceCenteredEnvelope
    (ε ℓ u v T : ℝ) : ℂ :=
  saddleSourceNormalizedEnvelope ε ℓ u T *
    Complex.exp (Complex.I * ((ℓ * T * v : ℝ) : ℂ))

-- At v = v(u): exp(ℒᵤ(T))P₊(T + iu).
def saddleSourceCenteredPlusIntegrand
    (ε ℓ u v T : ℝ) : ℂ :=
  saddleSourceCenteredEnvelope ε ℓ u v T *
    plusPolynomial ε ((T : ℂ) + Complex.I * (u : ℂ))

-- At v = v(u): exp(ℒᵤ(T))P₋(T + iu).
def saddleSourceCenteredMinusIntegrand
    (ε ℓ u v T : ℝ) : ℂ :=
  saddleSourceCenteredEnvelope ε ℓ u v T *
    minusPolynomial ε ((T : ℂ) + Complex.I * (u : ℂ))

-- The real prefactor λEλ(iλu) exp(−λ(1 + u)v)/(2π).
def saddleSourceCenteredPrefactor
    (ε ℓ u v : ℝ) : ℝ :=
  (ℓ / (2 * Real.pi)) *
    Real.exp (-(ℓ * (1 + u) * v)) *
      saddleSourceContourEnvelopeScale ε ℓ u

-- The prefactor is positive for λ > 0 and u > −1.
theorem saddleSourceCenteredPrefactor_pos
    {ε ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : -1 < u)
    (v : ℝ) :
    0 < saddleSourceCenteredPrefactor ε ℓ u v := by ...

-- f₊(exp v) = positive prefactor × centered integral.
theorem plusSaddleProfile_exp_eq_centeredIntegral
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ) (hu : -1 < u)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (v : ℝ) :
    plusSaddleProfile ε ℓ (Real.exp v) =
      (saddleSourceCenteredPrefactor ε ℓ u v : ℂ) *
        (∫ T : ℝ,
          saddleSourceCenteredPlusIntegrand ε ℓ u v T) := by ...
```

The analogous identity for $f\_-$ is `minusSaddleProfile_exp_eq_centeredIntegral`. Both identities hold for any real $v$; only later is $v$ chosen to make $T=0$ stationary.

**The Gaussian approximation.** The variance is assembled from the Gamma contribution and the signed weight contribution. Here `δ = u - 1`, so `2 + δ = 1 + u`. These quantities give the same $V(u)=v^{\prime}(u)$ as in Part 1.

```lean
-- The Gamma contribution: λ⁻¹ ∫ a² μλ,u(a) da, with u = η − 1.
def upperGammaVariance (ℓ η : ℝ) : ℝ :=
  ℓ⁻¹ * ∫ a : ℝ in Set.Ioi 0,
    a ^ 2 * upperGammaMeasureDensity ℓ η a

-- The positive-weight variance minus the negative-weight magnitude.
def upperNetShellVariance (ε δ : ℝ) : ℝ :=
  upperPositiveShellVariance ε δ -
    upperShortShellVariance ε δ

-- V(1 + δ) = Gamma variance + signed weight variance.
def upperSaddleVariance (ε ℓ δ : ℝ) : ℝ :=
  upperGammaVariance ℓ (2 + δ) +
    upperNetShellVariance ε δ

-- V(u), obtained by substituting δ = u − 1.
def saddleSourceGaussianVariance
    (ε ℓ u : ℝ) : ℝ :=
  upperSaddleVariance ε ℓ (u - 1)

-- Gᵤ(T) = exp(−λV(u)T²/2).
def saddleSourceGaussianKernel
    (ε ℓ u T : ℝ) : ℝ :=
  Real.exp
    (-(ℓ * saddleSourceGaussianVariance ε ℓ u / 2) * T ^ 2)

-- Gᵤ(T)P₊(iu).
def saddleSourceGaussianPlusIntegrand
    (ε ℓ u T : ℝ) : ℂ :=
  (saddleSourceGaussianKernel ε ℓ u T : ℂ) *
    plusPolynomial ε (Complex.I * (u : ℂ))

-- Gᵤ(T)P₋(iu).
def saddleSourceGaussianMinusIntegrand
    (ε ℓ u T : ℝ) : ℂ :=
  (saddleSourceGaussianKernel ε ℓ u T : ℂ) *
    minusPolynomial ε (Complex.I * (u : ℂ))

-- For λ > 0 and V(u) > 0, ∫ Gᵤ(T) dT = √(2π/(λV(u))).
theorem saddleSourceGaussianKernel_integral
    (ε ℓ u : ℝ) :
    (∫ T : ℝ, saddleSourceGaussianKernel ε ℓ u T) =
      Real.sqrt
        (Real.pi /
          (ℓ * saddleSourceGaussianVariance ε ℓ u / 2)) := by ...

-- T★ = (λ(1 + u))^(1/12)/√(λV(u)).
def saddleSourceFirstBranchCentralRadius
    (ε ℓ u : ℝ) : ℝ :=
  (ℓ * (1 + u)) ^ (1 / 12 : ℝ) /
    Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u)

-- T★ = λ^(1/12)/√(λV(u)).
def saddleSourceSecondBranchCentralRadius
    (ε ℓ u : ℝ) : ℝ :=
  ℓ ^ (1 / 12 : ℝ) /
    Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u)
```

The variance positivity is proved in `eventually_saddleSourceGaussianVariance_firstBranch_pos` and `eventually_saddleSourceGaussianVariance_secondBranch_pos`. The following two theorems then give the full-line error bounds used for the signs.

For the first range, the condition $\log\lambda/4\le\lambda(1+u)$ is exactly $u\ge u\_\ast$. The extra hypothesis for the minus sign is $u\ge u\_0=1+\varepsilon/4$.

```lean
-- For u★ ≤ u ≤ U, the total Gaussian error is smaller than the main term.
theorem eventually_saddleSourceFirstBranch_fullGaussianErrors :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ᶠ ℓ : ℝ in atTop,
        ∀ u : ℝ, -1 < u → u ≤ 1 + ε / 2 →
          Real.log ℓ / 4 ≤ ℓ * (1 + u) →
            (‖(∫ T : ℝ,
                saddleSourceCenteredPlusIntegrand ε ℓ u
                  (saddleSourceStationaryLogRadius ε ℓ u) T) -
              (∫ T : ℝ,
                saddleSourceGaussianPlusIntegrand ε ℓ u T)‖ <
              ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ *
                (∫ T : ℝ,
                  saddleSourceGaussianKernel ε ℓ u T)) ∧
            (1 + ε / 4 ≤ u →
              ‖(∫ T : ℝ,
                  saddleSourceCenteredMinusIntegrand ε ℓ u
                    (saddleSourceStationaryLogRadius ε ℓ u) T) -
                (∫ T : ℝ,
                  saddleSourceGaussianMinusIntegrand ε ℓ u T)‖ <
                ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ *
                  (∫ T : ℝ,
                    saddleSourceGaussianKernel ε ℓ u T)) := by ...
```

For the second range, the theorem uses $\delta=u-1$, so its condition $\delta\ge\varepsilon/2$ means $u\ge U$.

```lean
-- For u ≥ U, both Gaussian errors are smaller than their main terms.
theorem eventually_saddleSourceSecondBranch_fullGaussianErrors :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ᶠ ℓ : ℝ in atTop,
        ∀ δ : ℝ, ε / 2 ≤ δ →
          (‖(∫ T : ℝ,
              saddleSourceCenteredPlusIntegrand ε ℓ (1 + δ)
                (saddleSourceStationaryLogRadius
                  ε ℓ (1 + δ)) T) -
            (∫ T : ℝ,
              saddleSourceGaussianPlusIntegrand ε ℓ (1 + δ) T)‖ <
            ‖plusPolynomial ε
              (Complex.I * ((1 + δ : ℝ) : ℂ))‖ *
              (∫ T : ℝ,
                saddleSourceGaussianKernel ε ℓ (1 + δ) T)) ∧
          (‖(∫ T : ℝ,
              saddleSourceCenteredMinusIntegrand ε ℓ (1 + δ)
                (saddleSourceStationaryLogRadius
                  ε ℓ (1 + δ)) T) -
            (∫ T : ℝ,
              saddleSourceGaussianMinusIntegrand ε ℓ (1 + δ) T)‖ <
            ‖minusPolynomial ε
              (Complex.I * ((1 + δ : ℝ) : ℂ))‖ *
              (∫ T : ℝ,
                saddleSourceGaussianKernel ε ℓ (1 + δ) T)) := by ...
```

In these statements, `∀ᶠ ε in 𝓝[>] 0` means “for every sufficiently small positive $\varepsilon$”, and `∀ᶠ ℓ in atTop` means “for every sufficiently large $\lambda$”. Since these quantifiers come before `∀ u` or `∀ δ`, the threshold is uniform over the indicated range. Substituting $\lambda=d/2$ gives the eventual dimension statements.

Each proof combines three estimates: the error on the central interval, the tail of the original integrand, and the Gaussian tail. For example, the first range uses `eventually_saddleSourceFirstBranch_centralGaussianErrors`, `eventually_saddleSourceFirstBranch_sourceL1Tails`, and `eventually_saddleSourceFirstBranch_gaussianL1Tails`. The second range has the corresponding `SecondBranch` lemmas. This is the same splitting as in Part 1; the final statements retain the strict inequality needed for signs rather than the full relative asymptotic.

**From an integral estimate to a sign.** The polynomial signs are elementary:

```lean
-- P₊(iu) > 0 for ε > 0 and u > −1.
theorem plusPolynomial_imaginary_re_pos {ε u : ℝ}
    (hε : 0 < ε) (hu : -1 < u) :
    0 < (plusPolynomial ε (Complex.I * (u : ℂ))).re := by ...

-- P₋(iu) < 0 for ε > 0 and u ≥ 1 + ε/4.
theorem minusPolynomial_imaginary_re_neg {ε u : ℝ}
    (hε : 0 < ε) (hu : 1 + ε / 4 ≤ u) :
    (minusPolynomial ε (Complex.I * (u : ℂ))).re < 0 := by ...
```

The next two theorems isolate the last step. If the complex error is smaller than the magnitude of the real Gaussian main term, its real part cannot change the sign. Multiplication by the positive prefactor preserves that sign.

```lean
-- A Gaussian error smaller than the positive main term gives f₊(exp v) > 0.
theorem plusSaddleProfile_exp_re_pos_of_gaussian_error
    {ε ℓ u v : ℝ}
    (hε : 0 < ε)
    (hℓ : 0 < ℓ)
    (hu : -1 < u)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u)
    (herror :
      ‖(∫ T : ℝ,
          saddleSourceCenteredPlusIntegrand ε ℓ u v T) -
        (∫ T : ℝ,
          saddleSourceGaussianPlusIntegrand ε ℓ u T)‖ <
        (∫ T : ℝ,
          saddleSourceGaussianPlusIntegrand ε ℓ u T).re) :
    0 < (plusSaddleProfile ε ℓ (Real.exp v)).re := by ...

-- A Gaussian error smaller than the negative main term's magnitude gives f₋(exp v) < 0.
theorem minusSaddleProfile_exp_re_neg_of_gaussian_error
    {ε ℓ u v : ℝ}
    (hε : 0 < ε)
    (hℓ : 0 < ℓ)
    (hu : -1 < u)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u)
    (herror :
      ‖(∫ T : ℝ,
          saddleSourceCenteredMinusIntegrand ε ℓ u v T) -
        (∫ T : ℝ,
          saddleSourceGaussianMinusIntegrand ε ℓ u T)‖ <
        -(∫ T : ℝ,
          saddleSourceGaussianMinusIntegrand ε ℓ u T).re) :
    (minusSaddleProfile ε ℓ (Real.exp v)).re < 0 := by ...
```

Finally, estimates at radii $e^{v(u)}$ must cover all the radii we need. Lean proves this using continuity of $v$ and $v(u)\to\infty$, followed by the intermediate value theorem; strict monotonicity is not required for this particular step.

```lean
-- Every r ≥ r★ equals exp(v(u)) for some u ≥ u★.
theorem eventually_saddleSmallRadiusStar_log_coverage :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ᶠ d : ℕ in atTop,
        ∀ r : ℝ,
          saddleSmallRadiusStar ε d ≤ r →
            ∃ u : ℝ,
              saddleSmallRadiusStarOrdinate ε d ≤ u ∧
                saddleLogRadius ε d u = Real.log r := by ...

-- Every r ≥ Rε,d equals exp(v(u)) for some u ≥ u₀.
theorem eventually_saddleSourceRadius_log_coverage :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ d : ℕ, 0 < d →
        ∀ r : ℝ,
          saddleSourceRadius ε d ≤ r →
            ∃ u : ℝ,
              1 + ε / 4 ≤ u ∧
                saddleLogRadius ε d u = Real.log r := by ...
```

Combining these with the sign estimates proves $f\_+(r)>0$ for $r\ge r\_\ast$ and $f\_-(r)<0$ for $r\ge R\_{\varepsilon,d}$. Only the interval $0\le r\le r\_\ast$ for $f\_+$ remains.

#### Positivity of $f\_+$ for small radii

Here are the scaled variable $y$ and the coefficients $A\_{\lambda,n}$ in the residue expansion. The quantity `saddleShellDerivativeOne` is $ih^{\prime}(i)=\int w(a)a\sinh(a)\,da$, not a derivative at the real point $1$.

```lean
-- h₁′ = ih′(i) = ∫ w(a)a sinh(a) da.
def saddleShellDerivativeOne (ε : ℝ) : ℝ :=
  (∫ a in shortCutoff ε..shortEndpoint ε,
    shortShellDensity ε a * a * Real.sinh a) +
  (∫ a in shellLocation ε..shellLocation ε + 1,
    positiveShellDensity ε a * a * Real.sinh a)

-- y = πr² exp(2h₁′).
def saddleSmallRadiusVariable (ε r : ℝ) : ℝ :=
  Real.pi * Real.exp (2 * saddleShellDerivativeOne ε) * r ^ 2

-- Aλ,n: the normalized coefficient of (−y)ⁿ/n! in the residue sum.
def plusSaddleSmallRadiusCoefficient
    (ε ℓ : ℝ) (n : ℕ) : ℝ :=
  Real.exp
      (ℓ *
        (realHyperbolicShellPhase ε
          (1 + 2 * (n : ℝ) / ℓ) -
            realHyperbolicShellPhase ε 1) -
        2 * (n : ℝ) * saddleShellDerivativeOne ε) *
    ((beta ε - (2 * (n : ℝ) / ℓ) *
        (2 + 2 * (n : ℝ) / ℓ) ^ 2) /
      beta ε)
```

To make the remainder precise, Lean shifts the Mellin contour to $\Re z=-(2N+1)$, between the poles $-2N$ and $-2(N+1)$. The next definition is the remaining contour integral before dividing by $f\_+(0)$.

```lean
-- The shifted line has Re z = −(2N + 1).
def saddleTaylorContour (N : ℕ) : ℝ :=
  -((2 * N + 1 : ℕ) : ℝ)

-- The unnormalized contour remainder after crossing N + 1 poles.
def plusSaddleTaylorRemainder
    (ε ℓ : ℝ) (N : ℕ) (r : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ t : ℝ,
      saddleMellinInversePower r
        ((saddleTaylorContour N : ℂ) +
          (t : ℂ) * Complex.I) *
        plusSaddleMellinData ε ℓ
          ((saddleTaylorContour N : ℂ) +
            (t : ℂ) * Complex.I))

-- f₊(r)/f₊(0) = Σₙ₌₀ᴺ (−y)ⁿAλ,n/n! + normalized remainder.
theorem plusSaddleProfile_div_origin_eq_small_radius_residue_series
    {ε ℓ r : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r) (N : ℕ) :
    plusSaddleProfile ε ℓ r /
        (saddleOriginValue ε ℓ : ℂ) =
      ((∑ n ∈ Finset.range (N + 1),
        (-saddleSmallRadiusVariable ε r) ^ n /
          (n.factorial : ℝ) *
            plusSaddleSmallRadiusCoefficient ε ℓ n : ℝ) : ℂ) +
      plusSaddleTaylorRemainder ε ℓ N r /
        (saddleOriginValue ε ℓ : ℂ) := by ...
```

Thus the `plusSaddleTaylorRemainder` in the code is not itself $\mathcal R\_\lambda$ from the overview: it must be divided by `saddleOriginValue`.

The coefficient estimate below is a quantitative version of $A\_{\lambda,n}=1+O\_\varepsilon(n(1+n)/\lambda)$. Its exponential factor is harmless when $n\le N$ and $N^2/\lambda\to0$.

```lean
-- Bound |Aλ,n − 1| by C(n + n²)exp(Cn²/λ)/λ, for 2n ≤ λ.
theorem exists_plusSaddleSmallRadiusCoefficient_error
    {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ℓ : ℝ), 0 < ℓ →
        ∀ n : ℕ, 2 * (n : ℝ) ≤ ℓ →
          |plusSaddleSmallRadiusCoefficient ε ℓ n - 1| ≤
            (C * ((n : ℝ) + (n : ℝ) ^ 2) / ℓ) *
              Real.exp (C * (n : ℝ) ^ 2 / ℓ) := by ...

-- N = ⌈20 log λ⌉.
def saddleSmallResidueTruncation (ℓ : ℝ) : ℕ :=
  Nat.ceil (20 * Real.log ℓ)

-- Uniformly for 0 ≤ r ≤ r★, y ≤ (log λ)/8 + Cε.
theorem exists_eventually_y_star_le_log_eighth_add
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ d : ℕ in atTop,
        ∀ r : ℝ, 0 ≤ r →
          r ≤ saddleSmallRadiusStar ε d →
            saddleSmallRadiusVariable ε r ≤
              Real.log ((d : ℝ) / 2) / 8 + C := by ...
```

The finite residue sum differs from $e^{-y}$ for two reasons: its coefficients are not exactly $1$, and the exponential series has been truncated. Bounding these two errors gives the first theorem below. The separate contour estimate gives the second. Both are **relative** errors, after multiplying by $e^y$.

```lean
-- Uniformly on 0 ≤ r ≤ r★, eʸ|S_N(y) − e⁻ʸ| < 1/2.
theorem eventually_plusSaddleSmallRadius_relativeFiniteResidue_lt_half_on_star
    {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    ∀ᶠ d : ℕ in atTop,
      ∀ r : ℝ,
        0 ≤ r → r ≤ saddleSmallRadiusStar ε d →
          let ℓ : ℝ := (d : ℝ) / 2
          let y : ℝ := saddleSmallRadiusVariable ε r
          Real.exp y *
            |(∑ n ∈ Finset.range
                (saddleSmallResidueTruncation ℓ + 1),
              ((-y) ^ n / (n.factorial : ℝ)) *
                plusSaddleSmallRadiusCoefficient ε ℓ n) -
              Real.exp (-y)| < 1 / 2 := by ...

-- Uniformly on 0 < r ≤ r★, eʸ|normalized remainder| < 1/2.
theorem eventually_plusSaddleTaylorRemainder_relative_lt_half_on_star
    {ε : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε) (shortEndpoint ε),
      0 ≤ shortMargin ε a) :
    ∀ᶠ d : ℕ in atTop,
      ∀ r : ℝ, 0 < r → r ≤ saddleSmallRadiusStar ε d →
        let ℓ : ℝ := (d : ℝ) / 2
        let N : ℕ := saddleSmallResidueTruncation ℓ
        let y : ℝ := saddleSmallRadiusVariable ε r
        Real.exp y *
          ‖plusSaddleTaylorRemainder ε ℓ N r /
            (saddleOriginValue ε ℓ : ℂ)‖ < 1 / 2 := by ...
```

The first bound allows $r=0$; the contour bound is stated only for $r>0$. The extra `hmargin` assumption says that $b(a)\ge0$ on the short interval, so the designated negative weight really is nonpositive. All these parameter conditions hold for sufficiently small positive $\varepsilon$.

The final implication is now elementary: the finite sum is greater than $e^{-y}/2$, while the real part of the normalized remainder is greater than $-e^{-y}/2$. Their sum is positive. Lean packages this as follows:

```lean
-- The two strict relative errors below 1/2 imply f₊(r) > 0.
theorem plusSaddleProfile_re_pos_of_relative_residue_bounds
    {ε ℓ r : ℝ}
    (hε : 0 < ε)
    (hℓ : 0 < ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hr : 0 < r)
    (N : ℕ)
    (hfinite :
      Real.exp (saddleSmallRadiusVariable ε r) *
        |(∑ n ∈ Finset.range (N + 1),
            (-saddleSmallRadiusVariable ε r) ^ n /
              (n.factorial : ℝ) *
                plusSaddleSmallRadiusCoefficient ε ℓ n) -
          Real.exp (-(saddleSmallRadiusVariable ε r))| <
        (1 / 2 : ℝ))
    (hremainder :
      Real.exp (saddleSmallRadiusVariable ε r) *
        ‖plusSaddleTaylorRemainder ε ℓ N r /
          (saddleOriginValue ε ℓ : ℂ)‖ <
        (1 / 2 : ℝ)) :
    0 < (plusSaddleProfile ε ℓ r).re := by ...

-- For small ε and large d, f₊(r) > 0 throughout 0 ≤ r ≤ r★.
theorem eventually_plusSaddleProfile_re_pos_on_star :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ᶠ d : ℕ in atTop,
        ∀ r : ℝ, 0 ≤ r → r ≤ saddleSmallRadiusStar ε d →
          0 < (plusSaddleProfile ε ((d : ℝ) / 2) r).re := by ...
```

The last theorem handles $r=0$ using `saddleOriginValue_pos`. Compared with Lemma 4.10 in Part 1, it uses the larger cutoff $N=\lceil20\log\lambda\rceil$ and states the positivity consequence rather than the full uniform relative asymptotic.

Combining this with the saddle-radius argument completes the signs required by the LP construction. The final interface keeps only weak inequalities, which are sufficient for admissibility.

```lean
-- For small ε and large d: f₊ ≥ 0 everywhere, and f₋ ≤ 0 for ‖x‖ ≥ Rε,d.
def SaddleSourceEventualSigns : Prop :=
  ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    ∀ᶠ d : ℕ in atTop,
      (∀ x : Euclidean d,
        0 ≤ (plusSaddleFunction ε d x).re) ∧
      (∀ x : Euclidean d,
        saddleSourceRadius ε d ≤ ‖x‖ →
          (minusSaddleFunction ε d x).re ≤ 0)

-- Assemble the small-radius and saddle-radius sign proofs.
theorem saddleSourceEventualSigns : SaddleSourceEventualSigns := by ...
```



<!-- WILL RELOCATE THESE LATER -->
The main correspondences and differences from Part 1 are:

- **Construction and Fourier symmetry:** `saddleSourceSchwartzRealization` and `saddleSource_fourier_minus_eq_plus`. Lean often uses the Mellin variable $z=\lambda-it$, so the horizontal shifts above become vertical-line shifts and the poles become $z=-2n$. It makes the pole subtraction explicit. The general Fourier/Mellin identity is proved through Gaussian pairings and Fubini, rather than the Bessel-kernel calculation in the report.
- **Saddle estimates:** `eventually_saddleSourceFirstBranch_fullGaussianErrors` and `eventually_saddleSourceSecondBranch_fullGaussianErrors`. These use the same Gaussian approximation as Lemma 4.8, but their conclusions are the strict error inequalities displayed above, not its relative $1+o(1)$ statement. The central and tail estimates are still uniform in $u$.
- **Small radii:** `eventually_plusSaddleProfile_re_pos_on_star` combines the two relative bounds below $1/2$. This is the residue argument of Lemma 4.10, with a larger cutoff $N$ and a conclusion tailored to positivity rather than the full relative asymptotic.
- **Assembly:** `saddleSourceEventualSigns` retains weak sign inequalities, although the preceding arguments prove strict ones. `saddleOrderedUpperConstruction_of_sourceSigns` then constructs the admissible functions, and `sharpAsymptotics` combines the upper and lower bounds. No $f\_0$ construction is included.

Some numerical choices differ. With $\lambda=d/2$, the main changes are:



The ordinates $u\_\ast,u\_0,U$ and the powers $1/12$ defining the central Gaussian windows are unchanged. The modified cutoffs and margins preserve the limiting radius constant $1/\pi$.
Interestingly, these choice coincide with the choices in the separate pdf ["reasoning-walkthroughs"](https://cdn.openai.com/pdf/reasoning-walkthroughs.pdf), which means that two pdfs are using different parameters for the proofs.


The final LP statements also include the passage beyond radial functions: `PackingBounds.fullLinearProgram_eq_radial` and `PackingBounds.FullMain.exact_limit` prove equality of the two programs and the exact unrestricted LP limit. The packing-density consequence is `PackingBounds.PackingBridge.sphere_packing_sharp_asymptotic_upper`, and `PackingBounds.sharpFullCohnElkiesManuscriptConclusions` collects the manuscript-level LP conclusions. This completes Theorem 1.1, but not the sign-uncertainty results listed as missing in the overview.



## Reformalization

<!-- (add later) -->

## Use of LLM

LLMs - ChatGPT and Claude - were used to help understanding the original proof and the formalization. In particular, I had a conversation with ChatGPT in Codex app where I moastly asked questions about the intuitions and choice of parameters in the proof.
For example, I asked why the perturbation $h$ is chosen of the form $h(\zeta) = \int_0^\infty w(a) (\cos(a\zeta) - 1) \mathrm{d} a$, and why $u_\ast$ is chosen as $-1 + \log \lambda / 4\lambda$, not something like $-1 + \log \lambda / 2\lambda$ or $-1 + \delta$ for some fixed $\delta > 0$.
Most of the proofs are very analytical and the technical details are mostly about "how to choose the right parameters so that this is larger than that".

Also, these were used to understand the formalization.
My first question was to give one-to-one correspondence between the nonformal statement and proof of the report and the formal statements and proof in Lean, and found the missing formalizations.
I also asked it to make a bluprint out of it (not with official Lean blueprint or Verso), which was not helpful at all.
I could make it better, but I found that it is not worth the time, and I decided to refactor it first.


## Conclusion

My guess for why the formalization is incomplete is that the original input for Astra was only sphere packing and Cohn-Elkies linear programming bound, but not on sign uncertainty principle.
It is only used as intermediate step, so they do not need to formalize all of them (e.g. $L^1$ formulation, self-Fourier function, etc.).

So the LP theorem is formalized, but the chapter as a whole is not.
Someone may say that I'm too picky, since the main LP argument is formalized. But the report makes additional sign-uncertainty claims, and those deserve separate statements and proofs.
There are a lot of autoformalized results (and there will be more in the future) where the formalized statement $A^{\prime}$ is not exactly the same as the natural language statement $A$, but $A^{\prime}$ is just a few *trivial* steps away from $A$ so that you can think it is fine.
But if that is really the case, why don't you just formalize $A$ directly?
The reason is because most of the time people don't read the AI's autoformalized proof and just believe them.
This belief will makes more sense as AI gets better and better, but then it will generate longer slop formalizations, and similar issue will keep persists.
If you want to autoformalize a natural language proof, the best thing you can to is to make every formal statement and argument as close to the natural language proof as possible - using the same notations, no more or less lemmas, and more importantly, make a blueprint.
If your AI is good enough to autoformalize a natural language proof, then it should be good enough to automatically write *a* blueprint that is *not too bad* for a human to read and understand (just push the button few more times), which is way better than having no blueprint at all.
I recently wrote a blog post about this (prompted by [other news](https://www.anthropic.com/research/formalizing-fermats-last-theorem)) - check it out [here](https://proofsandprompts.com/2026/09/08/autoformalization-but-why/).


Let me end this post with a question and answer:

> Q. Does this proof give any further insight into these problems?
>
> A. `¯\_(ツ)_/¯`
