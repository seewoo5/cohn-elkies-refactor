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

The extended maximum principle is proved by a Phragmén–Lindelöf-type argument. For `ε > 0`, the
auxiliary harmonic function `h z = ∑ x₀ ∈ E, log ‖(z - x₀) / (z - x₀ + 2i)‖ - log ‖z + i‖` is
nonpositive on the closed upper half-plane, tends to `-∞` at every point of `E` and as
`‖z‖ → ∞`, so the weak maximum principle `SubharmonicOn.le_zero_of_limsup_frontier` on the
half-disc `{‖z‖ < R} ∩ ℍ` gives `u + ε h ≤ 0` there for `R` large; then let `ε → 0`. The Poisson
principle follows by applying it to `u - P[bₙ]` for the truncations `bₙ = max b (-n)`, which
are bounded below, and letting `n → ∞`.
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
    (h : ∀ i ∈ s, HarmonicAt (f i) x) : HarmonicAt (fun y ↦ ∑ i ∈ s, f i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

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
  refine EReal.le_of_forall_lt_iff_le.1 fun d hd ↦ ?_
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [hf.norm.eventually
    (gt_mem_nhds (hf₀.trans_lt (Real.exp_lt_exp.2 (EReal.coe_lt_coe_iff.1 hd))))] with z hz
  split_ifs with hfz
  · exact bot_le
  · exact EReal.coe_le_coe_iff.2 ((Real.log_le_iff_le_exp (norm_pos_iff.2 hfz)).2 hz.le)

namespace Complex

/-!
### Auxiliary harmonic functions on the upper half-plane

The functions `logNormRatio x₀ z = log ‖(z - x₀) / (z - x₀ + 2i)‖` (for a real `x₀`) and
`negLogNormAddI z = -log ‖z + i‖` are harmonic on `ℍ` and nonpositive on the closed upper
half-plane, and they tend to `-∞` as `z → x₀`, respectively as `‖z‖ → ∞`. They are the barriers
of the Phragmén–Lindelöf argument for the extended maximum principle below.
-/

/-- `logNormRatio x₀ z = log ‖(z - x₀) / (z - x₀ + 2i)‖`: a harmonic function on `ℍ` which is
nonpositive on the closed upper half-plane and tends to `-∞` at the real point `x₀`. -/
noncomputable def logNormRatio (x₀ : ℝ) (z : ℂ) : ℝ := Real.log ‖(z - x₀) / (z - x₀ + 2 * I)‖

/-- `negLogNormAddI z = -log ‖z + i‖`: a harmonic function on `ℍ` which is nonpositive on the
closed upper half-plane and tends to `-∞` as `‖z‖ → ∞`. -/
noncomputable def negLogNormAddI (z : ℂ) : ℝ := -Real.log ‖z + I‖

/-- `z - x₀ ≠ 0` for `z` in the upper half-plane and real `x₀`. -/
theorem sub_ofReal_ne_zero_of_im_pos {x₀ : ℝ} {z : ℂ} (hz : 0 < z.im) : z - x₀ ≠ 0 := fun h ↦ by
  have := congrArg Complex.im h
  simp at this
  linarith

/-- `z - x₀ + 2i ≠ 0` for `z` in the closed upper half-plane and real `x₀`. -/
theorem sub_ofReal_add_two_mul_I_ne_zero {x₀ : ℝ} {z : ℂ} (hz : 0 ≤ z.im) :
    z - x₀ + 2 * I ≠ 0 := fun h ↦ by
  have := congrArg Complex.im h
  simp at this
  linarith

theorem harmonicOnNhd_logNormRatio (x₀ : ℝ) :
    HarmonicOnNhd (logNormRatio x₀) {z | 0 < z.im} := by
  intro z hz
  have hz' : (0 : ℝ) < z.im := hz
  have h₁ : z - x₀ ≠ 0 := sub_ofReal_ne_zero_of_im_pos hz'
  have h₂ : z - x₀ + 2 * I ≠ 0 := sub_ofReal_add_two_mul_I_ne_zero hz'.le
  have hf : AnalyticAt ℂ (fun w : ℂ ↦ (w - x₀) / (w - x₀ + 2 * I)) z := by
    fun_prop (disch := exact h₂)
  exact hf.harmonicAt_log_norm (div_ne_zero h₁ h₂)

/-- `‖w‖ ≤ ‖w + 2i‖` for `Im w ≥ 0`, as `‖w + 2i‖² = ‖w‖² + 4 Im w + 4`. -/
theorem norm_le_norm_add_two_mul_I {w : ℂ} (hw : 0 ≤ w.im) : ‖w‖ ≤ ‖w + 2 * I‖ := by
  rw [norm_def, norm_def]
  refine Real.sqrt_le_sqrt ?_
  simp only [normSq_apply, add_re, add_im, mul_re, mul_im, I_re, I_im, re_ofNat, im_ofNat]
  nlinarith

theorem logNormRatio_nonpos {x₀ : ℝ} {z : ℂ} (hz : 0 ≤ z.im) : logNormRatio x₀ z ≤ 0 := by
  refine Real.log_nonpos (norm_nonneg _) ?_
  rw [norm_div]
  exact div_le_one_of_le₀ (norm_le_norm_add_two_mul_I (by simpa using hz)) (norm_nonneg _)

/-- `logNormRatio x₀ z → -∞` as `z → x₀` within the upper half-plane. -/
theorem tendsto_logNormRatio_atBot (x₀ : ℝ) :
    Tendsto (logNormRatio x₀) (𝓝[{z | 0 < z.im}] (x₀ : ℂ)) atBot := by
  refine Real.tendsto_log_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
  · have hc : ContinuousAt (fun w : ℂ ↦ ‖(w - x₀) / (w - x₀ + 2 * I)‖) x₀ := by
      have h₂ : (x₀ : ℂ) - x₀ + 2 * I ≠ 0 := sub_ofReal_add_two_mul_I_ne_zero (by simp)
      fun_prop (disch := exact h₂)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact norm_pos_iff.2 (div_ne_zero (sub_ofReal_ne_zero_of_im_pos hz)
      (sub_ofReal_add_two_mul_I_ne_zero (le_of_lt hz)))

theorem harmonicOnNhd_negLogNormAddI : HarmonicOnNhd negLogNormAddI {z | 0 < z.im} := by
  intro z hz
  have hz' : (0 : ℝ) < z.im := hz
  have h : z + I ≠ 0 := fun h ↦ by
    have := congrArg Complex.im h
    simp at this
    linarith
  exact ((analyticAt_id.add analyticAt_const).harmonicAt_log_norm h).neg

theorem negLogNormAddI_nonpos {z : ℂ} (hz : 0 ≤ z.im) : negLogNormAddI z ≤ 0 := by
  refine neg_nonpos.2 (Real.log_nonneg ?_)
  have := im_le_norm (z + I)
  rw [add_im, I_im] at this
  linarith

/-- `-log ‖z + i‖ ≤ -log (R - 1)` for `‖z‖ ≥ R > 1`. -/
theorem negLogNormAddI_le {z : ℂ} {R : ℝ} (hR : 1 < R) (hz : R ≤ ‖z‖) :
    negLogNormAddI z ≤ -Real.log (R - 1) := by
  refine neg_le_neg (Real.log_le_log (by linarith) ?_)
  have := norm_sub_le (z + I) I
  rw [add_sub_cancel_right, norm_I] at this
  linarith

/-- A boundary point `ζ` of the half-disc `{‖z‖ < R} ∩ ℍ` lies in the closed upper half-plane,
and it is either real or of modulus at least `R`. -/
theorem frontier_ball_inter_halfPlane_subset (R : ℝ) :
    frontier (ball (0 : ℂ) R ∩ {z | 0 < z.im}) ⊆ {ζ | 0 ≤ ζ.im ∧ (ζ.im = 0 ∨ R ≤ ‖ζ‖)} := by
  intro ζ hζ
  rw [(isOpen_ball.inter UpperHalfPlane.isOpen_upperHalfPlaneSet).frontier_eq] at hζ
  obtain ⟨hcl, hnot⟩ := hζ
  have hcl' : ζ ∈ closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im} :=
    closure_minimal (inter_subset_inter ball_subset_closedBall fun z hz ↦ le_of_lt hz)
      (isClosed_closedBall.inter (isClosed_le continuous_const continuous_im)) hcl
  refine ⟨hcl'.2, ?_⟩
  by_contra! h
  exact hnot ⟨mem_ball_zero_iff.2 h.2, lt_of_le_of_ne hcl'.2 (Ne.symm h.1)⟩

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

Proof (Phragmén–Lindelöf): for `ε > 0`, the harmonic function
`h z = ∑ x₀ ∈ E, log ‖(z - x₀) / (z - x₀ + 2i)‖ - log ‖z + i‖` is nonpositive on the closed upper
half-plane, tends to `-∞` at the points of `E`, and satisfies `h z ≤ -log (‖z‖ - 1)`. Hence
`u + ε h ≤ 0` on the half-disc `Ω_R = {‖z‖ < R} ∩ ℍ` by the weak maximum principle, once
`R` is so large that `M - ε log (R - 2) ≤ 0`: at real boundary points outside `E` the boundary
condition holds since `ε h ≤ 0`, at points of `E` since `u ≤ M` and `ε h → -∞`, and at boundary
points of modulus `R` since `u + ε h ≤ M - ε log (R - 2)` near them. Thus `u z ≤ -ε h z` for every
`z ∈ ℍ` and every `ε > 0`; let `ε → 0`. -/
theorem le_zero_of_halfPlane {E : Finset ℝ} {M : ℝ}
    (hu : SubharmonicOn u {z | 0 < z.im}) (hM : ∀ z : ℂ, 0 < z.im → u z ≤ M)
    (hbdry : ∀ x : ℝ, x ∉ E → limsup u (𝓝[{z | 0 < z.im}] (x : ℂ)) ≤ 0) :
    ∀ z : ℂ, 0 < z.im → u z ≤ 0 := by
  intro z hz
  set h : ℂ → ℝ := fun w ↦ ∑ x₀ ∈ E, logNormRatio x₀ w + negLogNormAddI w with hh
  have hharm : HarmonicOnNhd h {w | 0 < w.im} :=
    (HarmonicOnNhd.sum fun x₀ _ ↦ harmonicOnNhd_logNormRatio x₀).add harmonicOnNhd_negLogNormAddI
  have hle : ∀ w : ℂ, 0 ≤ w.im → h w ≤ negLogNormAddI w := fun w hw ↦ by
    have := Finset.sum_nonpos fun x₀ (_ : x₀ ∈ E) ↦ logNormRatio_nonpos (x₀ := x₀) hw
    simp only [hh]
    linarith
  have hneg : ∀ w : ℂ, 0 ≤ w.im → h w ≤ 0 := fun w hw ↦
    (hle w hw).trans (negLogNormAddI_nonpos hw)
  -- for every `ε > 0`, `u z ≤ -ε h z`
  have key : ∀ ε : ℝ, 0 < ε → u z ≤ ((-(ε * h z) : ℝ) : EReal) := by
    intro ε hε
    obtain ⟨R, hR₂, hRz, hRlog⟩ : ∃ R : ℝ, 2 < R ∧ ‖z‖ < R ∧ M / ε ≤ Real.log (R - 1 - 1) := by
      refine ⟨Real.exp (M / ε) + 2 + ‖z‖, ?_, ?_, ?_⟩
      · linarith [Real.exp_pos (M / ε), norm_nonneg z]
      · linarith [Real.exp_pos (M / ε)]
      · calc M / ε = Real.log (Real.exp (M / ε)) := (Real.log_exp _).symm
          _ ≤ _ := Real.log_le_log (Real.exp_pos _) (by linarith [norm_nonneg z])
    -- the values `u w + ε h w` are nonpositive wherever `h w ≤ -M / ε`
    have hbound : ∀ w : ℂ, 0 < w.im → h w ≤ -(M / ε) → u w + ((ε * h w : ℝ) : EReal) ≤ 0 := by
      intro w hw hhw
      have h₁ : ε * h w ≤ -M := by
        have := mul_le_mul_of_nonneg_left hhw hε.le
        have : ε * (M / ε) = M := by field_simp
        linarith
      calc u w + ((ε * h w : ℝ) : EReal) ≤ (M : EReal) + ((ε * h w : ℝ) : EReal) :=
            add_le_add_left (hM w hw) _
        _ = ((M + ε * h w : ℝ) : EReal) := (EReal.coe_add _ _).symm
        _ ≤ 0 := by rw [← EReal.coe_zero, EReal.coe_le_coe_iff]; linarith
    -- the weak maximum principle on the half-disc `Ω`
    set Ω : Set ℂ := ball 0 R ∩ {w | 0 < w.im} with hΩ
    have hΩsub : Ω ⊆ {w | 0 < w.im} := inter_subset_right
    have hw : SubharmonicOn (fun w ↦ u w + ((ε * h w : ℝ) : EReal)) Ω :=
      (hu.add_harmonic UpperHalfPlane.isOpen_upperHalfPlaneSet
        (hharm.const_smul (c := ε))).mono hΩsub
    have hfr : ∀ ζ ∈ frontier Ω, limsup (fun w ↦ u w + ((ε * h w : ℝ) : EReal)) (𝓝[Ω] ζ) ≤ 0 := by
      intro ζ hζ
      obtain ⟨hζim, hζ'⟩ := frontier_ball_inter_halfPlane_subset R hζ
      rcases hζ' with him | hnorm
      · -- a real boundary point `x = ζ.re`
        have hζx : ((ζ.re : ℝ) : ℂ) = ζ := Complex.ext (by simp) (by simp [him])
        rw [← hζx]
        by_cases hE : ζ.re ∈ E
        · -- `x ∈ E`: `u ≤ M` and `ε h → -∞`
          refine limsup_le_of_le (by isBoundedDefault) ?_
          have h₁ : ∀ᶠ w in 𝓝[{w | 0 < w.im}] (ζ.re : ℂ), logNormRatio ζ.re w ≤ -(M / ε) :=
            (tendsto_logNormRatio_atBot ζ.re).eventually (eventually_le_atBot _)
          filter_upwards [nhdsWithin_mono _ hΩsub h₁, self_mem_nhdsWithin] with w hw₁ hwΩ
          have hwim : 0 < w.im := hΩsub hwΩ
          refine hbound w hwim (le_trans ?_ hw₁)
          have h₂ := Finset.sum_nonpos fun x₀ (_ : x₀ ∈ E.erase ζ.re) ↦
            logNormRatio_nonpos (x₀ := x₀) hwim.le
          have h₃ := negLogNormAddI_nonpos hwim.le
          simp only [hh]
          rw [← Finset.add_sum_erase E _ hE]
          linarith
        · -- `x ∉ E`: the boundary condition, as `ε h ≤ 0`
          calc limsup (fun w ↦ u w + ((ε * h w : ℝ) : EReal)) (𝓝[Ω] (ζ.re : ℂ))
              ≤ limsup u (𝓝[Ω] (ζ.re : ℂ)) := by
                refine limsup_le_limsup (eventually_nhdsWithin_of_forall fun w hw ↦ ?_)
                exact add_le_of_nonpos_right (EReal.coe_nonpos.2
                  (mul_nonpos_of_nonneg_of_nonpos hε.le (hneg w (hΩsub hw).le)))
            _ ≤ limsup u (𝓝[{w | 0 < w.im}] (ζ.re : ℂ)) :=
                limsup_le_limsup_of_le (nhdsWithin_mono _ hΩsub)
            _ ≤ 0 := hbdry ζ.re hE
      · -- a boundary point of modulus `R`: `u + ε h ≤ 0` nearby
        refine limsup_le_of_le (by isBoundedDefault) ?_
        have h₁ : ∀ᶠ w in 𝓝 ζ, R - 1 < ‖w‖ :=
          (continuous_norm.tendsto ζ).eventually (lt_mem_nhds (by linarith))
        filter_upwards [eventually_nhdsWithin_of_eventually_nhds h₁, self_mem_nhdsWithin]
          with w hw₁ hwΩ
        have hwim : 0 < w.im := hΩsub hwΩ
        refine hbound w hwim ?_
        have h₂ := negLogNormAddI_le (R := R - 1) (by linarith) hw₁.le
        linarith [hle w hwim.le]
    have hΩz : z ∈ Ω := ⟨mem_ball_zero_iff.2 hRz, hz⟩
    have hz₀ := hw.le_zero_of_limsup_frontier
      (isOpen_ball.inter UpperHalfPlane.isOpen_upperHalfPlaneSet)
      (isBounded_ball.subset inter_subset_left)
      ((convex_ball 0 R).inter (convex_halfSpace_im_gt 0)).isPreconnected hfr z hΩz
    have := (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))).2 hz₀
    rwa [zero_sub, ← EReal.coe_neg] at this
  -- let `ε → 0`
  have hlim : Tendsto (fun ε : ℝ ↦ ((-(ε * h z) : ℝ) : EReal)) (𝓝[>] 0) (𝓝 0) := by
    rw [← EReal.coe_zero]
    refine EReal.tendsto_coe.2 ?_
    have : Tendsto (fun ε : ℝ ↦ -(ε * h z)) (𝓝 0) (𝓝 (-(0 * h z))) :=
      ((continuous_id.mul continuous_const).neg).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
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
    set P : ℂ → ℝ := poissonIntegralHalfPlane fun x ↦ max (b x) (-(n : ℝ)) with hP
    have hPge : ∀ w : ℂ, 0 < w.im → -(n : ℝ) ≤ P w := fun w hw ↦
      le_poissonIntegralHalfPlane_of_le hbn (fun x ↦ le_max_right _ _) hw
    have hv : SubharmonicOn (fun w ↦ u w - (P w : EReal)) {z | 0 < z.im} :=
      hu.sub_harmonic UpperHalfPlane.isOpen_upperHalfPlaneSet
        (harmonicOnNhd_poissonIntegralHalfPlane hbn)
    have hvM : ∀ w : ℂ, 0 < w.im → u w - (P w : EReal) ≤ ((M + n : ℝ) : EReal) := fun w hw ↦ by
      calc u w - (P w : EReal) ≤ (M : EReal) - ((-(n : ℝ) : ℝ) : EReal) :=
            EReal.sub_le_sub (hM w hw) (EReal.coe_le_coe_iff.2 (hPge w hw))
        _ = ((M + n : ℝ) : EReal) := by rw [← EReal.coe_sub, sub_neg_eq_add]
    have hvb : ∀ x : ℝ, x ∉ E →
        limsup (fun w ↦ u w - (P w : EReal)) (𝓝[{z | 0 < z.im}] (x : ℂ)) ≤ 0 := by
      intro x hx
      have hPt : Tendsto P (𝓝[{z | 0 < z.im}] (x : ℂ)) (𝓝 (max (b x) (-(n : ℝ)))) :=
        tendsto_poissonIntegralHalfPlane_of_continuousAt hbn ((hbc x hx).max continuousAt_const)
      refine EReal.le_of_forall_lt_iff_le.1 fun δ hδ ↦ ?_
      have hδ' : 0 < δ := EReal.coe_pos.1 hδ
      refine limsup_le_of_le (by isBoundedDefault) ?_
      have h₁ : ∀ᶠ w in 𝓝[{z | 0 < z.im}] (x : ℂ), u w < ((b x + δ / 2 : ℝ) : EReal) :=
        eventually_lt_of_limsup_lt
          ((hbdry x hx).trans_lt (EReal.coe_lt_coe_iff.2 (by linarith)))
      have h₂ : ∀ᶠ w in 𝓝[{z | 0 < z.im}] (x : ℂ), b x - δ / 2 < P w :=
        hPt.eventually (lt_mem_nhds (by linarith [le_max_left (b x) (-(n : ℝ))]))
      filter_upwards [h₁, h₂] with w hw₁ hw₂
      calc u w - (P w : EReal) ≤ ((b x + δ / 2 : ℝ) : EReal) - (P w : EReal) :=
            EReal.sub_le_sub hw₁.le le_rfl
        _ = ((b x + δ / 2 - P w : ℝ) : EReal) := (EReal.coe_sub _ _).symm
        _ ≤ (δ : EReal) := EReal.coe_le_coe_iff.2 (by linarith)
    exact EReal.sub_nonpos.1 (hv.le_zero_of_halfPlane hvM hvb z hz)
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
    · exact bot_le
    · exact EReal.coe_le_coe_iff.2
        (Real.log_le_log (norm_pos_iff.2 hfw) ((hK w hw).trans (le_max_left _ _)))
  have h := (hf.subharmonicOn_log_norm UpperHalfPlane.isOpen_upperHalfPlaneSet)
    |>.le_poissonIntegralHalfPlane hM hb hbc hbdry z hz
  by_cases hfz : f z = 0
  · rw [hfz, norm_zero]
    exact (Real.exp_pos _).le
  · rw [ite_eq_right hfz, EReal.coe_le_coe_iff] at h
    exact (Real.log_le_iff_le_exp (norm_pos_iff.2 hfz)).1 h

end SubharmonicOn
