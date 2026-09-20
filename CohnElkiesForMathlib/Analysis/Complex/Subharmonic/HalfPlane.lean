import CohnElkiesForMathlib.Analysis.Complex.PoissonHalfPlane
import CohnElkiesForMathlib.Analysis.Complex.Subharmonic.Basic

/-!
# The Poisson principle for the upper half-plane

Let `ℍ = {z : ℂ | 0 < Im z}` be the upper half-plane. We prove two maximum principles for a
subharmonic function `u : ℂ → EReal` on `ℍ` (`SubharmonicOn u {z | 0 < z.im}`) that is bounded
above by a real constant `M`, with boundary conditions imposed at all real points outside a
finite exceptional set `E`:

* `SubharmonicOn.le_zero_of_halfPlane` (extended maximum principle): if
  `limsup u (𝓝[ℍ] x) ≤ 0` for every real `x ∉ E`, then `u ≤ 0` on `ℍ`;
* `SubharmonicOn.le_poissonIntegralHalfPlane` (**Poisson principle**, Ahlfors): if
  `limsup u (𝓝[ℍ] x) ≤ b x` for every real `x ∉ E`, where the boundary datum `b : ℝ → ℝ` has
  `b x / (1 + x ^ 2)` integrable and is continuous outside `E`, then `u ≤ P[b]` on `ℍ`, where
  `P[b] = Complex.poissonIntegralHalfPlane b` is the Poisson integral of `b`;

together with the corollary `AnalyticOnNhd.log_norm_le_poissonIntegralHalfPlane` for the
function `log ‖f‖` of an analytic function `f` bounded on `ℍ`: `‖f z‖ ≤ exp (P[b] z)` on `ℍ`.

The extended maximum principle is proved from the weak maximum principle for subharmonic
functions on bounded open sets (`SubharmonicOn.le_zero_of_limsup_frontier`). For `ε > 0`, the
auxiliary harmonic function `h z = ∑ x₀ ∈ E, log ‖(z - x₀) / (z - x₀ + 2i)‖ - log ‖z + i‖` is
nonpositive on the closed upper half-plane and tends to `-∞` at every point of `E` and as
`‖z‖ → ∞`; `u + ε h` is subharmonic on `ℍ` (`SubharmonicOn.add_harmonic`), and the weak maximum
principle on the half-disc `{‖z‖ < R} ∩ ℍ` gives `u + ε h ≤ 0` there for `R` large; then let
`ε → 0`. (The auxiliary function `ε h`, which absorbs the exceptional points and the point at
infinity, is the device of the Phragmén–Lindelöf principle; no Phragmén–Lindelöf theorem for
analytic functions is used.) The Poisson principle follows by applying the extended maximum
principle to `u - P[bₙ]` for the truncations `bₙ = max b (-n)`, which are bounded below, and
letting `n → ∞`.
-/

open Filter InnerProductSpace MeasureTheory Metric Set Topology

/-!
### Finite sums of harmonic functions
-/

namespace InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Finite sums of harmonic functions are harmonic. -/
theorem HarmonicAt.sum {ι : Type*} {s : Finset ι} {f : ι → E → F} {x : E}
    (h : ∀ i ∈ s, HarmonicAt (f i) x) : HarmonicAt (fun y ↦ ∑ i ∈ s, f i y) x :=
  Finset.sum_fn s f ▸ Finset.sum_induction f (HarmonicAt · x) (fun _ _ ↦ HarmonicAt.add)
    (harmonicAt_const 0) h

/-- Finite sums of harmonic functions are harmonic. -/
theorem HarmonicOnNhd.sum {ι : Type*} {s : Finset ι} {f : ι → E → F} {U : Set E}
    (h : ∀ i ∈ s, HarmonicOnNhd (f i) U) : HarmonicOnNhd (fun y ↦ ∑ i ∈ s, f i y) U :=
  fun x hx ↦ HarmonicAt.sum fun i hi ↦ h i hi x hx

end InnerProductSpace

/-!
### The boundary condition for `log ‖f‖`
-/

/-- If `f` tends to `f₀` along `l` with `‖f₀‖ ≤ exp c`, then `limsup log ‖f‖ ≤ c` along `l`, where
`log ‖f‖` is extended by `⊥ = -∞` at the zeros of `f`: this is the form in which boundary
conditions enter the Poisson principle for `log ‖f‖`. -/
theorem Filter.Tendsto.limsup_log_norm_le {α : Type*} {l : Filter α} {f : α → ℂ} {f₀ : ℂ} {c : ℝ}
    (hf : Tendsto f l (𝓝 f₀)) (hf₀ : ‖f₀‖ ≤ Real.exp c) :
    limsup (fun z ↦ if f z = 0 then ⊥ else ((Real.log ‖f z‖ : ℝ) : EReal)) l ≤ (c : EReal) := by
  refine EReal.le_of_forall_lt_iff_le.1 fun d hd ↦ limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [hf.norm.eventually
    (gt_mem_nhds (hf₀.trans_lt (Real.exp_lt_exp.2 (EReal.coe_lt_coe_iff.1 hd))))] with z hz
  split_ifs with hfz
  exacts [bot_le, EReal.coe_le_coe_iff.2 ((Real.log_le_iff_le_exp (norm_pos_iff.2 hfz)).2 hz.le)]

namespace Complex

/-!
### Auxiliary harmonic functions on the upper half-plane

The functions `logNormRatio x₀ z = log ‖(z - x₀) / (z - x₀ + 2i)‖` (for a real `x₀`) and
`negLogNormAddI z = -log ‖z + i‖` are harmonic on `ℍ` and nonpositive on the closed upper
half-plane, and they tend to `-∞` as `z → x₀`, respectively as `‖z‖ → ∞`. They are the barriers
of the extended maximum principle below: added to `u` with a small weight `ε`, they absorb the
exceptional points and the point at infinity.
-/

/-- `logNormRatio x₀ z = log ‖(z - x₀) / (z - x₀ + 2i)‖`: a harmonic function on `ℍ` which is
nonpositive on the closed upper half-plane and tends to `-∞` at the real point `x₀`. -/
noncomputable def logNormRatio (x₀ : ℝ) (z : ℂ) : ℝ := Real.log ‖(z - x₀) / (z - x₀ + 2 * I)‖

/-- `negLogNormAddI z = -log ‖z + i‖`: a harmonic function on `ℍ` which is nonpositive on the
closed upper half-plane and tends to `-∞` as `‖z‖ → ∞`. -/
noncomputable def negLogNormAddI (z : ℂ) : ℝ := -Real.log ‖z + I‖

/-- `z - x₀ ≠ 0` for `z` in the upper half-plane and real `x₀`. -/
theorem sub_ofReal_ne_zero_of_im_pos {x₀ : ℝ} {z : ℂ} (hz : 0 < z.im) : z - x₀ ≠ 0 :=
  ne_of_apply_ne Complex.im (by simpa using hz.ne')

/-- `z - x₀ + 2i ≠ 0` for `z` in the closed upper half-plane and real `x₀`. -/
theorem sub_ofReal_add_two_mul_I_ne_zero {x₀ : ℝ} {z : ℂ} (hz : 0 ≤ z.im) :
    z - x₀ + 2 * I ≠ 0 :=
  ne_of_apply_ne Complex.im (by simpa using (by positivity : z.im + 2 ≠ 0))

/-- `logNormRatio x₀` is harmonic on the upper half-plane. -/
theorem harmonicOnNhd_logNormRatio (x₀ : ℝ) :
    HarmonicOnNhd (logNormRatio x₀) {z | 0 < z.im} := fun z hz ↦
  have h₂ : z - x₀ + 2 * I ≠ 0 := sub_ofReal_add_two_mul_I_ne_zero (le_of_lt hz)
  AnalyticAt.harmonicAt_log_norm (by fun_prop (disch := exact h₂))
    (div_ne_zero (sub_ofReal_ne_zero_of_im_pos hz) h₂)

/-- `‖w‖ ≤ ‖w + 2i‖` for `Im w ≥ 0`, as `‖w + 2i‖² = ‖w‖² + 4 Im w + 4`. -/
theorem norm_le_norm_add_two_mul_I {w : ℂ} (hw : 0 ≤ w.im) : ‖w‖ ≤ ‖w + 2 * I‖ := by
  refine Real.sqrt_le_sqrt ?_
  simp only [normSq_apply, add_re, add_im, mul_re, mul_im, I_re, I_im, re_ofNat, im_ofNat]
  linarith

/-- `logNormRatio x₀` is nonpositive on the closed upper half-plane. -/
theorem logNormRatio_nonpos {x₀ : ℝ} {z : ℂ} (hz : 0 ≤ z.im) : logNormRatio x₀ z ≤ 0 :=
  Real.log_nonpos (norm_nonneg _) <| (norm_div _ _).trans_le <|
    div_le_one_of_le₀ (norm_le_norm_add_two_mul_I (by simpa using hz)) (norm_nonneg _)

/-- `logNormRatio x₀ z → -∞` as `z → x₀` within the upper half-plane. -/
theorem tendsto_logNormRatio_atBot (x₀ : ℝ) :
    Tendsto (logNormRatio x₀) (𝓝[{z | 0 < z.im}] (x₀ : ℂ)) atBot := by
  refine Real.tendsto_log_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
  · have hc : ContinuousAt (fun w : ℂ ↦ ‖(w - x₀) / (w - x₀ + 2 * I)‖) x₀ := by
      fun_prop (disch := exact sub_ofReal_add_two_mul_I_ne_zero (by simp))
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  · exact eventually_nhdsWithin_of_forall fun z hz ↦ norm_pos_iff.2 (div_ne_zero
      (sub_ofReal_ne_zero_of_im_pos hz) (sub_ofReal_add_two_mul_I_ne_zero (le_of_lt hz)))

/-- `negLogNormAddI` is harmonic on the upper half-plane. -/
theorem harmonicOnNhd_negLogNormAddI : HarmonicOnNhd negLogNormAddI {z | 0 < z.im} :=
  fun z (hz : 0 < z.im) ↦ ((analyticAt_id.add analyticAt_const).harmonicAt_log_norm
    (ne_of_apply_ne Complex.im (by simpa using (by positivity : z.im + 1 ≠ 0)))).neg

/-- `negLogNormAddI` is nonpositive on the closed upper half-plane. -/
theorem negLogNormAddI_nonpos {z : ℂ} (hz : 0 ≤ z.im) : negLogNormAddI z ≤ 0 :=
  neg_nonpos.2 (Real.log_nonneg (le_trans (by simpa using hz) (im_le_norm (z + I))))

/-- `-log ‖z + i‖ ≤ -log (R - 1)` for `‖z‖ ≥ R > 1`. -/
theorem negLogNormAddI_le {z : ℂ} {R : ℝ} (hR : 1 < R) (hz : R ≤ ‖z‖) :
    negLogNormAddI z ≤ -Real.log (R - 1) :=
  neg_le_neg (Real.log_le_log (by linarith) (by linarith [norm_le_add_norm_add z I, norm_I]))

/-- A boundary point `ζ` of the half-disc `{‖z‖ < R} ∩ ℍ` lies in the closed upper half-plane,
and it is either real or of modulus at least `R`. -/
theorem frontier_ball_inter_halfPlane_subset (R : ℝ) :
    frontier (ball (0 : ℂ) R ∩ {z | 0 < z.im}) ⊆ {ζ | 0 ≤ ζ.im ∧ (ζ.im = 0 ∨ R ≤ ‖ζ‖)} := by
  rw [(isOpen_ball.inter UpperHalfPlane.isOpen_upperHalfPlaneSet).frontier_eq]
  rintro ζ ⟨hcl, hnot⟩
  have him : 0 ≤ ζ.im :=
    closure_lt_subset_le continuous_const continuous_im (closure_mono inter_subset_right hcl)
  exact ⟨him, or_iff_not_imp_left.2 fun h ↦ le_of_not_gt fun hR ↦
    hnot ⟨mem_ball_zero_iff.2 hR, him.lt_of_ne' h⟩⟩

end Complex

/-!
### The extended maximum principle and the Poisson principle
-/

namespace SubharmonicOn

open Complex

variable {u : ℂ → EReal}

/-- **Extended maximum principle** for the upper half-plane: a subharmonic function `u` on `ℍ`
that is bounded above by a real constant and satisfies `limsup u (𝓝[ℍ] x) ≤ 0` at every real
point `x` outside a finite set `E` is nonpositive on `ℍ`.

Proof: let `u ≤ M` on `ℍ` and `ε > 0`. The harmonic function
`h z = ∑ x₀ ∈ E, log ‖(z - x₀) / (z - x₀ + 2i)‖ - log ‖z + i‖` (`Complex.logNormRatio`,
`Complex.negLogNormAddI`) is nonpositive on the closed upper half-plane, tends to `-∞` at the
points of `E`, and satisfies `h z ≤ -log (‖z‖ - 1)`. The function `u + ε h` is subharmonic on `ℍ`
(`SubharmonicOn.add_harmonic`), and the weak maximum principle for subharmonic functions
(`SubharmonicOn.le_zero_of_limsup_frontier`) on the half-disc `Ω_R = {‖z‖ < R} ∩ ℍ` gives
`u + ε h ≤ 0` there, once `R` is so large that `M - ε log (R - 2) ≤ 0`: at real boundary points
outside `E` the boundary condition holds since `ε h ≤ 0`, at points of `E` since `u ≤ M` and
`ε h → -∞`, and at boundary points of modulus `R` since `u + ε h ≤ M - ε log (R - 2)` near them.
Thus `u z ≤ -ε h z` for every `z ∈ ℍ` and every `ε > 0`; let `ε → 0`. (The auxiliary function
`ε h` is the device of the Phragmén–Lindelöf principle, but no Phragmén–Lindelöf theorem for
analytic functions is used: everything rests on the subharmonic maximum principle.) -/
theorem le_zero_of_halfPlane {E : Finset ℝ} {M : ℝ}
    (hu : SubharmonicOn u {z | 0 < z.im}) (hM : ∀ z : ℂ, 0 < z.im → u z ≤ M)
    (hbdry : ∀ x : ℝ, x ∉ E → limsup u (𝓝[{z | 0 < z.im}] (x : ℂ)) ≤ 0) :
    ∀ z : ℂ, 0 < z.im → u z ≤ 0 := by
  intro z hz
  set h : ℂ → ℝ := fun w ↦ ∑ x₀ ∈ E, logNormRatio x₀ w + negLogNormAddI w
  have hharm : HarmonicOnNhd h {w | 0 < w.im} :=
    (HarmonicOnNhd.sum fun x₀ _ ↦ harmonicOnNhd_logNormRatio x₀).add harmonicOnNhd_negLogNormAddI
  have hle : ∀ w : ℂ, 0 ≤ w.im → h w ≤ negLogNormAddI w := fun w hw ↦
    add_le_of_nonpos_left (Finset.sum_nonpos fun x₀ _ ↦ logNormRatio_nonpos hw)
  -- for every `ε > 0`, `u z ≤ -ε h z`
  have key : ∀ ε : ℝ, 0 < ε → u z ≤ ((-(ε * h z) : ℝ) : EReal) := by
    intro ε hε
    obtain ⟨R, hR₂, hRz, hRlog⟩ : ∃ R : ℝ, 2 < R ∧ ‖z‖ < R ∧ M / ε ≤ Real.log (R - 1 - 1) :=
      ⟨Real.exp (M / ε) + 2 + ‖z‖, by linarith [Real.exp_pos (M / ε), norm_nonneg z],
        by linarith [Real.exp_pos (M / ε)], (Real.log_exp (M / ε)).symm.trans_le
          (Real.log_le_log (Real.exp_pos _) (by linarith [norm_nonneg z]))⟩
    -- the values `u w + ε h w` are nonpositive wherever `h w ≤ -M / ε`
    have hbound : ∀ w : ℂ, 0 < w.im → h w ≤ -(M / ε) → u w + ((ε * h w : ℝ) : EReal) ≤ 0 := by
      intro w hw hhw
      have h₁ : ε * h w ≤ -M := (mul_le_mul_of_nonneg_left hhw hε.le).trans_eq (by field_simp)
      exact (add_le_add_left (hM w hw) _).trans (by norm_cast; linarith)
    -- the weak maximum principle on the half-disc `Ω`
    set Ω : Set ℂ := ball 0 R ∩ {w | 0 < w.im}
    have hΩsub : Ω ⊆ {w | 0 < w.im} := inter_subset_right
    have hw : SubharmonicOn (fun w ↦ u w + ((ε * h w : ℝ) : EReal)) Ω :=
      (hu.add_harmonic UpperHalfPlane.isOpen_upperHalfPlaneSet
        (hharm.const_smul (c := ε))).mono hΩsub
    have hfr : ∀ ζ ∈ frontier Ω, limsup (fun w ↦ u w + ((ε * h w : ℝ) : EReal)) (𝓝[Ω] ζ) ≤ 0 := by
      intro ζ hζ
      obtain ⟨-, him | hnorm⟩ := frontier_ball_inter_halfPlane_subset R hζ
      · -- a real boundary point `x`
        obtain ⟨x, rfl⟩ : ∃ x : ℝ, (x : ℂ) = ζ := ⟨ζ.re, Complex.ext rfl him.symm⟩
        by_cases hE : x ∈ E
        · -- `x ∈ E`: `u ≤ M` and `ε h → -∞`
          refine limsup_le_of_le (by isBoundedDefault) ?_
          filter_upwards [nhdsWithin_mono _ hΩsub
            ((tendsto_logNormRatio_atBot x).eventually (eventually_le_atBot (-(M / ε)))),
            self_mem_nhdsWithin] with w hw₁ hwΩ
          have hwim : 0 < w.im := hΩsub hwΩ
          have hsum : ∑ x₀ ∈ E, logNormRatio x₀ w ≤ logNormRatio x w :=
            (Finset.sum_le_sum_of_subset_of_nonpos (Finset.singleton_subset_iff.2 hE)
              fun i _ _ ↦ logNormRatio_nonpos (x₀ := i) hwim.le).trans_eq (Finset.sum_singleton _ _)
          exact hbound w hwim ((add_le_of_nonpos_right (negLogNormAddI_nonpos hwim.le)).trans
            (hsum.trans hw₁))
        · -- `x ∉ E`: the boundary condition, as `ε h ≤ 0`
          refine (limsup_le_limsup (eventually_nhdsWithin_of_forall fun w hw ↦ ?_)).trans
            ((limsup_le_limsup_of_le (nhdsWithin_mono _ hΩsub)).trans (hbdry x hE))
          exact add_le_of_nonpos_right (EReal.coe_nonpos.2 (mul_nonpos_of_nonneg_of_nonpos hε.le
            ((hle w (hΩsub hw).le).trans (negLogNormAddI_nonpos (hΩsub hw).le))))
      · -- a boundary point of modulus `R`: `u + ε h ≤ 0` nearby
        refine limsup_le_of_le (by isBoundedDefault) ?_
        filter_upwards [eventually_nhdsWithin_of_eventually_nhds
          ((continuous_norm.tendsto ζ).eventually (lt_mem_nhds (by linarith : R - 1 < ‖ζ‖))),
          self_mem_nhdsWithin] with w hw₁ hwΩ
        have hwim : 0 < w.im := hΩsub hwΩ
        exact hbound w hwim <| by
          linarith [hle w hwim.le, negLogNormAddI_le (R := R - 1) (by linarith) hw₁.le]
    have hz₀ := hw.le_zero_of_limsup_frontier
      (isOpen_ball.inter UpperHalfPlane.isOpen_upperHalfPlaneSet)
      (isBounded_ball.subset inter_subset_left)
      ((convex_ball 0 R).inter (convex_halfSpace_im_gt 0)).isPreconnected hfr z
      ⟨mem_ball_zero_iff.2 hRz, hz⟩
    exact EReal.sub_nonpos.1 (by rwa [sub_eq_add_neg, ← EReal.coe_neg, neg_neg])
  -- let `ε → 0`
  have hlim : Tendsto (fun ε : ℝ ↦ ((-(ε * h z) : ℝ) : EReal)) (𝓝[>] 0) (𝓝 0) :=
    ((continuous_coe_real_ereal.comp (by fun_prop)).tendsto' 0 0 (by simp)).mono_left
      nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall key)

/-- **Poisson principle for the upper half-plane** (Ahlfors): let `u` be subharmonic on `ℍ` and
bounded above by a real constant, and let `b : ℝ → ℝ` be a boundary datum with `b x / (1 + x²)`
integrable, continuous at every real point outside a finite set `E`. If `limsup u (𝓝[ℍ] x) ≤ b x`
for every real `x ∉ E`, then `u ≤ P[b]` on `ℍ`, where `P[b]` is the Poisson integral of `b`.

Proof: for `n : ℕ` the truncation `bₙ = max b (-n)` is bounded below, so `P[bₙ] ≥ -n` and
`u - P[bₙ]` is subharmonic on `ℍ` and bounded above; at a real point `x ∉ E` we have
`limsup u ≤ b x ≤ bₙ x = lim P[bₙ]`, so the extended maximum principle gives `u ≤ P[bₙ]` on `ℍ`,
and `P[bₙ] → P[b]` as `n → ∞`. -/
theorem le_poissonIntegralHalfPlane {b : ℝ → ℝ} {E : Finset ℝ} {M : ℝ}
    (hu : SubharmonicOn u {z | 0 < z.im}) (hM : ∀ z : ℂ, 0 < z.im → u z ≤ M)
    (hb : Integrable fun x ↦ b x / (1 + x ^ 2)) (hbc : ∀ x : ℝ, x ∉ E → ContinuousAt b x)
    (hbdry : ∀ x : ℝ, x ∉ E → limsup u (𝓝[{z | 0 < z.im}] (x : ℂ)) ≤ (b x : EReal)) :
    ∀ z : ℂ, 0 < z.im → u z ≤ (poissonIntegralHalfPlane b z : EReal) := by
  intro z hz
  -- `u ≤ P[bₙ]` for the truncations `bₙ = max b (-n)`
  have key : ∀ n : ℕ,
      u z ≤ (poissonIntegralHalfPlane (fun x ↦ max (b x) (-(n : ℝ))) z : EReal) := by
    intro n
    have hbn : Integrable fun x ↦ max (b x) (-(n : ℝ)) / (1 + x ^ 2) :=
      integrable_max_neg_div_one_add_sq hb n
    set P : ℂ → ℝ := poissonIntegralHalfPlane fun x ↦ max (b x) (-(n : ℝ))
    have hvM : ∀ w : ℂ, 0 < w.im → u w - (P w : EReal) ≤ ((M + n : ℝ) : EReal) := fun w hw ↦
      (EReal.sub_le_sub (hM w hw) (EReal.coe_le_coe_iff.2
        (le_poissonIntegralHalfPlane_of_le hbn (fun x ↦ le_max_right _ _) hw))).trans_eq
        (by rw [← EReal.coe_sub, sub_neg_eq_add])
    have hvb : ∀ x : ℝ, x ∉ E →
        limsup (fun w ↦ u w - (P w : EReal)) (𝓝[{z | 0 < z.im}] (x : ℂ)) ≤ 0 := by
      intro x hx
      have hPt : Tendsto P (𝓝[{z | 0 < z.im}] (x : ℂ)) (𝓝 (max (b x) (-(n : ℝ)))) :=
        tendsto_poissonIntegralHalfPlane_of_continuousAt hbn ((hbc x hx).max continuousAt_const)
      refine EReal.le_of_forall_lt_iff_le.1 fun δ hδ ↦ limsup_le_of_le (by isBoundedDefault) ?_
      have hδ' : 0 < δ := EReal.coe_pos.1 hδ
      filter_upwards [eventually_lt_of_limsup_lt
        ((hbdry x hx).trans_lt (EReal.coe_lt_coe_iff.2 (by linarith : b x < b x + δ / 2))),
        hPt.eventually (lt_mem_nhds (by linarith [le_max_left (b x) (-n : ℝ)] : b x - δ / 2 < _))]
        with w hw₁ hw₂
      exact (EReal.sub_le_sub hw₁.le le_rfl).trans ((EReal.coe_sub _ _).symm.trans_le
        (EReal.coe_le_coe_iff.2 (by linarith)))
    exact EReal.sub_nonpos.1 ((hu.sub_harmonic UpperHalfPlane.isOpen_upperHalfPlaneSet
      (harmonicOnNhd_poissonIntegralHalfPlane hbn)).le_zero_of_halfPlane hvM hvb z hz)
  -- let `n → ∞`
  exact ge_of_tendsto' (EReal.tendsto_coe.2 (tendsto_poissonIntegralHalfPlane_max hb hz)) key

/-- **Poisson principle for `log ‖f‖`**: let `f` be analytic and bounded on `ℍ`, and let
`b : ℝ → ℝ` be a boundary datum with `b x / (1 + x²)` integrable, continuous at every real point
outside a finite set `E`. If `limsup log ‖f‖ ≤ b x` as `z → x` within `ℍ` for every real `x ∉ E`
(where `log ‖f‖` is extended by `⊥ = -∞` at the zeros of `f`; see
`Filter.Tendsto.limsup_log_norm_le`), then `‖f‖ ≤ exp P[b]` on `ℍ`. -/
theorem _root_.AnalyticOnNhd.log_norm_le_poissonIntegralHalfPlane {f : ℂ → ℂ} {b : ℝ → ℝ}
    {E : Finset ℝ} {K : ℝ} (hf : AnalyticOnNhd ℂ f {z | 0 < z.im})
    (hK : ∀ z : ℂ, 0 < z.im → ‖f z‖ ≤ K) (hb : Integrable fun x ↦ b x / (1 + x ^ 2))
    (hbc : ∀ x : ℝ, x ∉ E → ContinuousAt b x)
    (hbdry : ∀ x : ℝ, x ∉ E →
      limsup (fun z ↦ if f z = 0 then ⊥ else ((Real.log ‖f z‖ : ℝ) : EReal))
        (𝓝[{z | 0 < z.im}] (x : ℂ)) ≤ (b x : EReal)) :
    ∀ z : ℂ, 0 < z.im → ‖f z‖ ≤ Real.exp (poissonIntegralHalfPlane b z) := by
  intro z hz
  have hM : ∀ w : ℂ, 0 < w.im →
      (if f w = 0 then ⊥ else ((Real.log ‖f w‖ : ℝ) : EReal)) ≤ (Real.log (max K 1) : EReal) := by
    intro w hw
    split_ifs with hfw
    exacts [bot_le, EReal.coe_le_coe_iff.2
      (Real.log_le_log (norm_pos_iff.2 hfw) ((hK w hw).trans (le_max_left _ _)))]
  have h := (hf.subharmonicOn_log_norm UpperHalfPlane.isOpen_upperHalfPlaneSet)
    |>.le_poissonIntegralHalfPlane hM hb hbc hbdry z hz
  by_cases hfz : f z = 0
  · exact hfz ▸ norm_zero.trans_le (Real.exp_pos _).le
  · exact (Real.log_le_iff_le_exp (norm_pos_iff.2 hfz)).1 (by simpa [hfz] using h)

end SubharmonicOn
