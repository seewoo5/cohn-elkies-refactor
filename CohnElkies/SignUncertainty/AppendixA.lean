import CohnElkies.SignUncertainty.TailIntegral
import CohnElkies.SignUncertainty.OriginCorrection
import CohnElkies.SignUncertainty.Finiteness
import CohnElkiesForMathlib.Analysis.Fourier.EigenfunctionConcentration
import CohnElkiesForMathlib.Analysis.InnerProductSpace.WeakSequentialCompactness

/-! # Appendix A of the report: Proposition A.1 and `A₊(d) < A₋(d)`

**Proposition A.1.** For a radial `g ∈ E₋(d)`, `d ≥ 1`, the tail integral `T_d g` of report (87) is
a self-Fourier sign eigenfunction `T_d g ∈ E₊(d)` (`SignEigenfunction.tailIntegral`): continuous,
integrable, `𝓕 (T_d g) = T_d g`, `T_d g (0) = 0` (`CohnElkies.SignUncertainty.TailIntegral`), and
nonzero (differentiating the small-scale representation along a ray recovers `g`). If `g ≥ 0`
outside the ball of radius `R`, then `T_d g > 0` outside that ball: `T_d g (x) ≥ 0` by (87), and
`T_d g (x) = 0` would force `g`, hence `𝓕 g = -g`, to vanish outside the ball of radius `‖x‖`,
contradicting Fourier analyticity (`fourier_eq_zero_of_eq_zero_outside`). Hence `r(T_d g) ≤ r(g)`
and, when `r(g) < ∞`, `r(T_d g) < r(g)` (`SignEigenfunction.signRadius_tailIntegral_lt`).

**Existence of extremizers.** Theorem 1.4 of Cohn–Gonçalves, *An optimal uncertainty principle in
twelve dimensions via modular forms* (Invent. Math. 2019), in its existence part (their §3.2): for
every `d ≥ 1` the infimum `A₋(d) = inf {r(g) : g ∈ 𝓔₋(d)}` of report (6) is attained
(`exists_signRadius_eq_signUncertaintyConstant_neg_one`). Applied to Proposition A.1, this gives
the comparison `A₊(d) < A₋(d)` of the sign-uncertainty constants
(`signUncertaintyConstant_one_lt_neg_one`), and `0 < A_ς(d) < ∞` for both signs
(`signUncertaintyConstant_pos_lt_top`).

Write `A = A₋(d)`, `0 < A < ∞` (`CohnElkies.SignUncertainty.Finiteness`), `a = A.toReal`. The
existence proof follows Cohn–Gonçalves, with their quantitative input (Nazarov's uncertainty
principle) replaced by the qualitative compactness statement of
`CohnElkiesForMathlib.Analysis.Fourier.EigenfunctionConcentration`.

1. *Minimizing sequence* (`IsMinimizingSequence`, `exists_isMinimizingSequence`): `L¹`-normalized
   `f n ∈ 𝓔₋(d)` with `r(f n) ≤ a + 1/(n+1)`; then `|f n| ≤ 1`, `∫ f n = 0`, and `f n ≥ 0` outside
   the ball of radius `a + 1/(m+1)` for `n ≥ m`.
2. *No concentration* (`IsMinimizingSequence.exists_setIntegral_closedBall_le`): the `L¹` mass of
   `f n` outside the ball `B` of radius `a + 1` is at least some `κ > 0` independent of `n`, so
   `∫_B f n ≤ -κ` since `∫ f n = 0` and `f n ≥ 0` outside `B`.
3. *Weak limit* (`IsMinimizingSequence.exists_tendsto_integral_mul`): `‖f n‖₂ ≤ 1`, so a
   subsequence converges weakly in `L²` to some `g`: `∫ z f n → ∫ z g` for every `z ∈ L²`.
4. *Properties of `g`*: testing against bounded functions of compact support, `g` is integrable
   (`integrable_of_tendsto_integral_mul`), `∫_B g ≤ -κ` (so `g ≠ 0`), `∫ g ≤ 0`
   (`integral_nonpos_of_tendsto_integral_mul`) and `g ≥ 0` a.e. outside the ball of radius `a`
   (`ae_nonneg_of_tendsto_integral_mul`).
5. *Eigen-equation* (`fourier_ae_eq_neg_of_tendsto_integral_mul`): testing against smooth compactly
   supported `ϕ` and using `∫ (𝓕 f) ϕ = ∫ f (𝓕 ϕ)`, `𝓕 g = -g` almost everywhere.
6. *Continuous representative* (`IsMinimizingSequence.exists_signRadius_le`): `G = -Re 𝓕 g` is
   continuous, integrable, `𝓕 G = -G` everywhere, `G ≠ 0`, `G(0) = -∫ g ≥ 0` and `G ≥ 0` outside
   the ball of radius `a`; the origin correction of Cohn–Gonçalves (Lemma 3.1,
   `CohnElkies.SignUncertainty.OriginCorrection`) turns `G` into `h ∈ 𝓔₋(d)` with `r(h) ≤ a`.
7. Hence `r(h) = A₋(d)`, and `A₊(d) ≤ r(T_d ℛh) < r(ℛh) = A₋(d)` for the rotational average `ℛh`. -/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal FourierTransform Topology InnerProductSpace RealInnerProductSpace
  SchwartzMap

variable {d : ℕ}

/-! ### Sign radii -/

/-- A sign eigenfunction nonnegative outside the ball of radius `R` has `R > 0`: otherwise `g ≥ 0`
everywhere and `∫ g = 0` would force `g = 0` (report, proof of Proposition A.1). -/
theorem SignEigenfunction.pos_of_nonneg_outside {ς : ℤˣ} (g : SignEigenfunction d ς) {R : ℝ}
    (hR : ∀ x : Euclidean d, R ≤ ‖x‖ → 0 ≤ g x) : 0 < R := by
  by_contra! hR0
  have hnn : ∀ x, 0 ≤ g x := fun x ↦ hR x (hR0.trans (norm_nonneg x))
  have h := (integral_eq_zero_iff_of_nonneg hnn g.integrable).1 g.integral_eq_zero
  exact g.ne_zero ((g.continuous.ae_eq_iff_eq volume continuous_const).1 h)

/-- A continuous function on `ℝ^d` (`d ≥ 1`) nonnegative outside the closed ball of radius `R` is
nonnegative on its boundary sphere as well. -/
theorem nonneg_of_forall_lt_norm (hd : 0 < d) {g : Euclidean d → ℝ} (hg : Continuous g) {R : ℝ}
    (h : ∀ x : Euclidean d, R < ‖x‖ → 0 ≤ g x) (x : Euclidean d) (hx : R ≤ ‖x‖) : 0 ≤ g x := by
  rcases hx.lt_or_eq with hlt | heq
  · exact h x hlt
  by_cases hx0 : x = 0
  · subst hx0
    rw [norm_zero] at heq
    set e := radialUnitDirection hd
    have hlim : Tendsto (fun t : ℝ ↦ g (t • e)) (𝓝[>] 0) (𝓝 (g 0)) := by
      have hc : Continuous fun t : ℝ ↦ g (t • e) := hg.comp (continuous_id.smul continuous_const)
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    refine ge_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    refine h _ ?_
    rw [norm_smul, norm_radialUnitDirection hd, mul_one, Real.norm_of_nonneg (le_of_lt ht), heq]
    exact ht
  · have hlim : Tendsto (fun t : ℝ ↦ g (t • x)) (𝓝[>] 1) (𝓝 (g x)) := by
      have hc : Continuous fun t : ℝ ↦ g (t • x) := hg.comp (continuous_id.smul continuous_const)
      have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Ioi 1))
      simpa using this
    refine ge_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    refine h _ ?_
    rw [norm_smul, Real.norm_of_nonneg (zero_le_one.trans (le_of_lt ht)), heq]
    exact lt_mul_of_one_lt_left (norm_pos_iff.2 hx0) ht

/-- The last-sign radius `r(g)` of a continuous function with `r(g) < ⊤` is itself a sign radius
(`d ≥ 1`). -/
theorem nonneg_of_toReal_signRadius_le (hd : 0 < d) {g : Euclidean d → ℝ} (hg : Continuous g)
    (hfin : signRadius g < ⊤) (x : Euclidean d) (hx : (signRadius g).toReal ≤ ‖x‖) : 0 ≤ g x := by
  refine nonneg_of_forall_lt_norm hd hg (R := (signRadius g).toReal) (fun y hy ↦ ?_) x hx
  by_contra hneg
  have h := le_signRadius_of_not_nonneg_outside (g := g) (R := ‖y‖) fun hall ↦ hneg (hall y le_rfl)
  rw [ENNReal.ofReal_le_iff_le_toReal hfin.ne] at h
  exact hy.not_ge h

namespace SignEigenfunction

variable (hd : 0 < d) (g : SignEigenfunction d (-1)) (hg : IsRadial (g : Euclidean d → ℝ))
include hd hg

/-! ### Positivity of `T_d g` outside a sign radius of `g` -/

/-- Report, proof of Proposition A.1: if `g ≥ 0` outside the ball of radius `R`, then `T_d g > 0`
outside that ball. Nonnegativity is (87); if `T_d g (x) = 0`, then `g` vanishes on the ray beyond
`x`, hence (radiality) outside the ball of radius `‖x‖`, and so does `𝓕 g = -g`, which forces
`g = 0` by Fourier analyticity. -/
theorem tailIntegral_pos {R : ℝ} (hR : ∀ x : Euclidean d, R ≤ ‖x‖ → 0 ≤ g x) {x : Euclidean d}
    (hx : R ≤ ‖x‖) : 0 < tailIntegral d g x := by
  have hR0 : 0 < R := g.pos_of_nonneg_outside hR
  have hx' : 0 < ‖x‖ := hR0.trans_le hx
  have hx0 : x ≠ 0 := norm_pos_iff.1 hx'
  set Φ : ℝ → ℝ := fun t ↦ t ^ ((d / 2 : ℝ) - 1) * g (t • x) with hΦ
  have hΦnn : ∀ t ∈ Ioi (1 : ℝ), 0 ≤ Φ t := fun t ht ↦ by
    have ht0 : 0 < t := zero_lt_one.trans ht
    refine mul_nonneg (Real.rpow_nonneg ht0.le _) (hR _ ?_)
    rw [norm_smul, Real.norm_of_nonneg ht0.le]
    exact hx.trans (le_mul_of_one_le_left (norm_nonneg x) (le_of_lt ht))
  have hint : IntegrableOn Φ (Ioi 1) :=
    (g.integrableOn_rpow_mul_smul hd hg hx0).mono_set (Ioi_subset_Ioi zero_le_one)
  have hnn : 0 ≤ ∫ t in Ioi (1 : ℝ), Φ t := setIntegral_nonneg measurableSet_Ioi hΦnn
  rw [tailIntegral_of_ne_zero _ hx0]
  refine mul_pos (by positivity) (lt_of_le_of_ne hnn fun h0 ↦ ?_)
  have hae : Φ =ᵐ[volume.restrict (Ioi 1)] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae (ae_restrict_of_forall_mem measurableSet_Ioi hΦnn)
      hint).1 h0.symm
  have hcont : ContinuousOn Φ (Ioi 1) :=
    (continuousOn_id.rpow_const fun t ht ↦ Or.inl (zero_lt_one.trans ht).ne').mul
      (g.continuous.comp (continuous_id.smul continuous_const :
        Continuous fun t : ℝ ↦ t • x)).continuousOn
  have hzero : ∀ t ∈ Ioi (1 : ℝ), Φ t = 0 := fun t ht ↦ by
    simpa using Measure.eqOn_open_of_ae_eq hae isOpen_Ioi hcont continuousOn_const ht
  have hvan : ∀ y : Euclidean d, ‖x‖ < ‖y‖ → g y = 0 := by
    intro y hy
    have ht : 1 < ‖y‖ / ‖x‖ := (one_lt_div hx').2 hy
    have hΦt := hzero _ ht
    simp only [hΦ] at hΦt
    have hgy : g y = g ((‖y‖ / ‖x‖) • x) := hg _ _ (by
      rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ hx'.ne'])
    rw [hgy]
    exact (mul_eq_zero.1 hΦt).resolve_left (Real.rpow_pos_of_pos (zero_lt_one.trans ht) _).ne'
  have hsupp : ∀ y : Euclidean d, ‖x‖ < ‖y‖ → g.toComplex y = 0 := fun y hy ↦ by
    simp [hvan y hy]
  have hfour : ∀ y : Euclidean d, ‖x‖ < ‖y‖ → 𝓕 g.toComplex y = 0 := fun y hy ↦ by
    rw [g.fourier_toComplex, hvan y hy]
    simp
  have hzero' := fourier_eq_zero_of_eq_zero_outside hd g.integrable_toComplex hsupp hfour
  exact g.ne_zero (funext fun y ↦ by simpa [congrFun hzero' y] using g.coe_eq_fourier y)

/-! ### Nonvanishing of `T_d g` -/

/-- If all the small-scale integrals `∫_0^1 s^{λ-1} g(s x) ds` vanish, then `g = 0`: the profile
`F(R) = ∫_0^R r^{λ-1} g(r e₁) dr` vanishes for all `R > 0`, so its derivative `R^{λ-1} g(R e₁)`
vanishes too (this is `(x·∇ + λ) T_d g = -λ g/2` of the report, integrated along rays). -/
theorem eq_zero_of_forall_integral_Ioo_eq_zero
    (h : ∀ x : Euclidean d, ∫ s in Ioo (0 : ℝ) 1, s ^ ((d / 2 : ℝ) - 1) * g (s • x) = 0) :
    (g : Euclidean d → ℝ) = 0 := by
  set e := radialUnitDirection hd with he
  set f : ℝ → ℝ := fun r ↦ r ^ ((d / 2 : ℝ) - 1) * g (r • e) with hf
  have hF : ∀ R : ℝ, 0 < R → ∫ r in (0 : ℝ)..R, f r = 0 := by
    intro R hR
    have h1 := h (R • e)
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at h1
    have h2 : ∫ s in (0 : ℝ)..1, s ^ ((d / 2 : ℝ) - 1) * g (s • R • e) =
        (R ^ ((d / 2 : ℝ) - 1))⁻¹ * ∫ s in (0 : ℝ)..1, f (R * s) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s hs ↦ ?_
      have hs0 : 0 ≤ s := by
        rw [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at hs
        exact hs.1
      simp only [hf, smul_smul, Real.mul_rpow hR.le hs0]
      field_simp
    rw [h2, intervalIntegral.integral_comp_mul_left (f := f) hR.ne', mul_zero, mul_one,
      smul_eq_mul] at h1
    simpa [hR.ne', (Real.rpow_pos_of_pos hR _).ne'] using h1
  have hderiv : ∀ R : ℝ, 0 < R → f R = 0 := by
    intro R hR
    have hfint : IntervalIntegrable f volume 0 R := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le]
      exact (g.integrableOn_rpow_mul_profile hd hg).mono_set Ioc_subset_Ioi_self
    have hcont : ContinuousAt f R :=
      (Real.continuousAt_rpow_const R _ (Or.inl hR.ne')).mul
        (g.continuous.comp (continuous_id.smul continuous_const :
          Continuous fun r : ℝ ↦ r • e)).continuousAt
    have hmeas : StronglyMeasurableAtFilter f (𝓝 R) :=
      ((measurable_id.pow_const _).mul (g.continuous.measurable.comp
        (measurable_id.smul_const e))).aestronglyMeasurable.stronglyMeasurableAtFilter
    have hD := intervalIntegral.integral_hasDerivAt_right hfint hmeas hcont
    have hD0 : HasDerivAt (fun u ↦ ∫ r in (0 : ℝ)..u, f r) 0 R := by
      refine (hasDerivAt_const R (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hR] with u hu
      exact hF u hu
    exact hD.unique hD0
  funext x
  by_cases hx : x = 0
  · simp [hx, g.zero]
  · have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hfx := hderiv ‖x‖ hx'
    simp only [hf] at hfx
    rw [Pi.zero_apply, hg x (‖x‖ • e) (by simp [norm_smul, he, norm_radialUnitDirection hd])]
    exact (mul_eq_zero.1 hfx).resolve_left (Real.rpow_pos_of_pos hx' _).ne'

/-- `T_d g ≠ 0` (Proposition A.1). -/
theorem tailIntegral_ne_zero : tailIntegral d g ≠ 0 := fun h ↦
  g.ne_zero (g.eq_zero_of_forall_integral_Ioo_eq_zero hd hg fun x ↦ by
    have hx := congrFun h x
    rw [g.tailIntegral_eq_neg_integral_Ioo hd hg x, Pi.zero_apply, neg_mul, neg_eq_zero,
      mul_eq_zero] at hx
    exact hx.resolve_left (by positivity))

/-! ### Proposition A.1 -/

/-- `r(T_d g) ≤ r(g)`: `T_d g ≥ 0` outside every ball outside which `g ≥ 0`. -/
theorem signRadius_tailIntegral_le : signRadius (tailIntegral d g) ≤ signRadius g :=
  signRadius_le_signRadius fun _ hR _ hx ↦ (g.tailIntegral_pos hd hg hR hx).le

/-- Proposition A.1: if `r(g) < ∞` then `r(T_d g) < r(g)`. Indeed `r(g) > 0`, `T_d g > 0` on the
sphere of radius `r(g)`, and the (radial, continuous) function `T_d g` stays positive on a slightly
smaller sphere. -/
theorem signRadius_tailIntegral_lt (hfin : signRadius (g : Euclidean d → ℝ) < ⊤) :
    signRadius (tailIntegral d g) < signRadius g := by
  set R := (signRadius (g : Euclidean d → ℝ)).toReal with hRdef
  have hR : ∀ y : Euclidean d, R ≤ ‖y‖ → 0 ≤ g y :=
    nonneg_of_toReal_signRadius_le hd g.continuous hfin
  have hR0 : 0 < R := g.pos_of_nonneg_outside hR
  set e := radialUnitDirection hd with he
  have hpos : 0 < tailIntegral d g (R • e) := g.tailIntegral_pos hd hg hR
    (by simp [norm_smul, he, norm_radialUnitDirection hd, abs_of_pos hR0])
  have hcont : ContinuousAt (fun r : ℝ ↦ tailIntegral d g (r • e)) R :=
    ((g.continuous_tailIntegral hd hg).comp (continuous_id.smul continuous_const :
      Continuous fun r : ℝ ↦ r • e)).continuousAt
  obtain ⟨δ, hδ, hδpos⟩ : ∃ δ > 0, ∀ r : ℝ, |r - R| < δ → 0 < tailIntegral d g (r • e) := by
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 (hcont.eventually (lt_mem_nhds hpos))
    exact ⟨δ, hδ, fun r hr ↦ hδ' (by rwa [Real.dist_eq])⟩
  have hsign : ∀ y : Euclidean d, R - δ / 2 ≤ ‖y‖ → 0 ≤ tailIntegral d g y := by
    intro y hy
    rcases le_or_gt R ‖y‖ with h | h
    · exact (g.tailIntegral_pos hd hg hR h).le
    · have h' := hδpos ‖y‖ (by rw [abs_sub_lt_iff]; constructor <;> linarith)
      rw [hg.tailIntegral (‖y‖ • e) y (by simp [norm_smul, he, norm_radialUnitDirection hd])]
        at h'
      exact h'.le
  calc signRadius (tailIntegral d g) ≤ ENNReal.ofReal (R - δ / 2) :=
        signRadius_le (R := Real.toNNReal (R - δ / 2)) fun y hy ↦
          hsign y ((Real.le_coe_toNNReal _).trans hy)
    _ < ENNReal.ofReal R := (ENNReal.ofReal_lt_ofReal_iff hR0).2 (by linarith)
    _ = signRadius g := ENNReal.ofReal_toReal hfin.ne

end SignEigenfunction

/-- Proposition A.1 of the report (Appendix A): for a radial `g ∈ E₋(d)`, `d ≥ 1`, the tail
integral `T_d g` of (87) is a self-Fourier sign eigenfunction, `T_d g ∈ E₊(d)`: it is continuous
and integrable, `𝓕 (T_d g) = T_d g`, `T_d g (0) = 0` and `T_d g ≠ 0`. Moreover `‖T_d g‖₁ ≤ ½ ‖g‖₁`
(`SignEigenfunction.integral_norm_tailIntegral_le`), `r(T_d g) ≤ r(g)`
(`SignEigenfunction.signRadius_tailIntegral_le`) and `r(T_d g) < r(g)` when `r(g) < ∞`
(`SignEigenfunction.signRadius_tailIntegral_lt`). -/
def SignEigenfunction.tailIntegral (hd : 0 < d) (g : SignEigenfunction d (-1))
    (hg : IsRadial (g : Euclidean d → ℝ)) : SignEigenfunction d 1 where
  toFun := _root_.CohnElkies.tailIntegral d g
  integrable := g.integrable_tailIntegral hd hg
  fourier_eq ξ := by
    rw [g.fourier_tailIntegral hd hg ξ]
    simp
  ne_zero := g.tailIntegral_ne_zero hd hg
  zero := tailIntegral_zero _

@[simp] theorem SignEigenfunction.tailIntegral_apply (hd : 0 < d) (g : SignEigenfunction d (-1))
    (hg : IsRadial (g : Euclidean d → ℝ)) (x : Euclidean d) :
    g.tailIntegral hd hg x = _root_.CohnElkies.tailIntegral d g x :=
  rfl

/-! ## Existence of extremizers (Cohn–Gonçalves, Theorem 1.4)

### Step 1: minimizing sequences -/

/-- A minimizing sequence for `A₋(d)` at level `a` (Cohn–Gonçalves 2019, §3.2): `L¹`-normalized
integrable `f n` with `𝓕 (f n) = -f n` pointwise, `|f n| ≤ 1`, `∫ f n = 0`, and `f n ≥ 0` outside
the ball of radius `a + 1/(m+1)` for all `n ≥ m`. -/
structure IsMinimizingSequence (a : ℝ) (f : ℕ → Euclidean d → ℝ) : Prop where
  integrable : ∀ n, Integrable (f n)
  fourier_eq : ∀ n (ξ : Euclidean d), 𝓕 (fun x ↦ (f n x : ℂ)) ξ = -(f n ξ : ℂ)
  integral_norm : ∀ n, ∫ x, ‖f n x‖ = 1
  norm_le : ∀ n x, ‖f n x‖ ≤ 1
  integral_eq_zero : ∀ n, ∫ x, f n x = 0
  nonneg : ∀ m n : ℕ, m ≤ n → ∀ x : Euclidean d, a + ((m : ℝ) + 1)⁻¹ ≤ ‖x‖ → 0 ≤ f n x

namespace IsMinimizingSequence

variable {a : ℝ} {f : ℕ → Euclidean d → ℝ}

/-- A subsequence of a minimizing sequence is a minimizing sequence. -/
theorem comp (hf : IsMinimizingSequence a f) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    IsMinimizingSequence a (f ∘ φ) where
  integrable n := hf.integrable (φ n)
  fourier_eq n := hf.fourier_eq (φ n)
  integral_norm n := hf.integral_norm (φ n)
  norm_le n := hf.norm_le (φ n)
  integral_eq_zero n := hf.integral_eq_zero (φ n)
  nonneg m n hmn := hf.nonneg m (φ n) (hmn.trans (hφ.id_le n))

/-- `f n ≥ 0` outside the ball of radius `a + 1` (the case `m = 0`). -/
theorem nonneg_of_add_one_le (hf : IsMinimizingSequence a f) (n : ℕ) (x : Euclidean d)
    (hx : a + 1 ≤ ‖x‖) : 0 ≤ f n x :=
  hf.nonneg 0 n (Nat.zero_le n) x (by simpa using hx)

end IsMinimizingSequence

/-- Step 1: since `A₋(d) < ∞`, for each `n` there is `g n ∈ 𝓔₋(d)` with
`r(g n) < A₋(d) + 1/(n+1)`; its `L¹`-normalization `f n = g n / ‖g n‖₁` has the same last-sign
radius, `‖f n‖₁ = 1`, `|f n| ≤ ‖f n‖₁ = 1`, `∫ f n = 0`, and `f n ≥ 0` outside the ball of radius
`r(f n) ≤ a + 1/(n+1) ≤ a + 1/(m+1)` for `n ≥ m`, where `a = A₋(d).toReal`. -/
theorem exists_isMinimizingSequence (hd : 0 < d) :
    ∃ f : ℕ → Euclidean d → ℝ,
      IsMinimizingSequence (signUncertaintyConstant (-1) d).toReal f := by
  have hfin := signUncertaintyConstant_neg_one_lt_top hd
  have hlt : ∀ n : ℕ, ∃ g : SignEigenfunction d (-1), signRadius (g : Euclidean d → ℝ) <
      signUncertaintyConstant (-1) d + ((n : ℝ≥0∞) + 1)⁻¹ :=
    fun n ↦ iInf_lt_iff.1 (ENNReal.lt_add_right hfin.ne (by simp))
  choose g hg using hlt
  refine ⟨fun n ↦ (g n).normalize, fun n ↦ (g n).normalize.integrable, fun n ξ ↦ ?_,
    fun n ↦ (g n).integral_norm_normalize,
    fun n x ↦ ((g n).normalize.norm_apply_le x).trans_eq (g n).integral_norm_normalize,
    fun n ↦ (g n).normalize.integral_eq_zero, fun m n hmn x hx ↦ ?_⟩
  · refine ((g n).normalize.fourier_toComplex ξ).trans ?_
    simp
  · have hlt := hg n
    rw [← (g n).signRadius_normalize] at hlt
    have hfin' : signRadius ((g n).normalize : Euclidean d → ℝ) < ⊤ :=
      hlt.trans (ENNReal.add_lt_top.2 ⟨hfin, ENNReal.inv_lt_top.2 (by positivity)⟩)
    refine nonneg_of_toReal_signRadius_le hd (g n).normalize.continuous hfin' x (le_trans ?_ hx)
    calc (signRadius ((g n).normalize : Euclidean d → ℝ)).toReal
        ≤ (signUncertaintyConstant (-1) d + ((n : ℝ≥0∞) + 1)⁻¹).toReal :=
          ENNReal.toReal_mono (by finiteness) hlt.le
      _ = (signUncertaintyConstant (-1) d).toReal + ((n : ℝ) + 1)⁻¹ := by
          rw [ENNReal.toReal_add hfin.ne (by finiteness)]
          simp [ENNReal.toReal_add]
      _ ≤ (signUncertaintyConstant (-1) d).toReal + ((m : ℝ) + 1)⁻¹ := by
          have : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hmn
          exact add_le_add_right (inv_anti₀ (by positivity) this) _

/-! ### Step 2: no concentration inside the ball of radius `a + 1` -/

/-- Step 2: for a minimizing sequence, the negative mass inside the ball `B` of radius `a + 1` is
bounded away from zero, `∫_B f n ≤ -κ` for some `κ > 0` and all `n`. Indeed the eigenfunctions
`f n` (eigenvalue `-1`, `‖f n‖₁ = 1`) have `L¹` mass at least `κ` outside `B`
(`Real.exists_pos_le_setIntegral_norm_compl_closedBall_of_fourier_eq_mul`), where `f n ≥ 0`, and
`∫ f n = 0`. -/
theorem IsMinimizingSequence.exists_setIntegral_closedBall_le (hd : 0 < d) {a : ℝ}
    {f : ℕ → Euclidean d → ℝ} (hf : IsMinimizingSequence a f) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ n, ∫ x in Metric.closedBall (0 : Euclidean d) (a + 1), f n x ≤ -κ := by
  have := nontrivial_euclidean hd
  obtain ⟨κ, hκ, hκf⟩ := Real.exists_pos_le_setIntegral_norm_compl_closedBall_of_fourier_eq_mul
    (V := Euclidean d) (c := -1) (by norm_num) (a + 1)
  refine ⟨κ, hκ, fun n ↦ ?_⟩
  set B := Metric.closedBall (0 : Euclidean d) (a + 1) with hB
  have hBm : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  have hnn : ∀ x ∈ Bᶜ, 0 ≤ f n x := fun x hx ↦ by
    have hx' : a + 1 < ‖x‖ := by simpa [hB, mem_closedBall_zero_iff] using hx
    exact hf.nonneg_of_add_one_le n x hx'.le
  have h1 : κ ≤ ∫ x in Bᶜ, ‖(f n x : ℂ)‖ :=
    hκf _ (hf.integrable n).ofReal (fun ξ ↦ by rw [hf.fourier_eq n ξ, neg_one_mul])
      (by simpa using hf.integral_norm n)
  have h2 : ∫ x in Bᶜ, ‖(f n x : ℂ)‖ = ∫ x in Bᶜ, f n x :=
    setIntegral_congr_fun hBm.compl fun x hx ↦ by
      rw [Complex.norm_real, Real.norm_of_nonneg (hnn x hx)]
  have h3 : (∫ x in B, f n x) + ∫ x in Bᶜ, f n x = 0 := by
    rw [integral_add_compl hBm (hf.integrable n), hf.integral_eq_zero n]
  linarith

/-! ### Step 3: the `L²` bound and the weak limit -/

/-- A minimizing sequence lies in `L²`: `|f n|² ≤ |f n|` since `|f n| ≤ 1`. -/
theorem IsMinimizingSequence.memLp_two {a : ℝ} {f : ℕ → Euclidean d → ℝ}
    (hf : IsMinimizingSequence a f) (n : ℕ) : MemLp (f n) 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm (hf.integrable n).aestronglyMeasurable).2 ?_
  refine (hf.integrable n).norm.mono' ((hf.integrable n).aestronglyMeasurable.norm.pow 2)
    (.of_forall fun x ↦ ?_)
  rw [norm_pow, norm_norm]
  exact pow_le_of_le_one (norm_nonneg _) (hf.norm_le n x) two_ne_zero

/-- `‖f n‖₂ ≤ 1`: `∫ |f n|² ≤ ∫ |f n| = 1`. -/
theorem IsMinimizingSequence.norm_toLp_le {a : ℝ} {f : ℕ → Euclidean d → ℝ}
    (hf : IsMinimizingSequence a f) (n : ℕ) : ‖(hf.memLp_two n).toLp (f n)‖ ≤ 1 := by
  rw [Lp.norm_toLp, (hf.memLp_two n).eLpNorm_eq_integral_rpow_norm two_ne_zero
    ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun x ↦ by positivity) _)]
  refine Real.rpow_le_one (integral_nonneg fun x ↦ by positivity) ?_ (by norm_num)
  calc ∫ x, ‖f n x‖ ^ (2 : ℝ) ≤ ∫ x, ‖f n x‖ :=
        integral_mono_of_nonneg (.of_forall fun x ↦ by positivity) (hf.integrable n).norm
          (.of_forall fun x ↦
            Real.rpow_le_self_of_le_one (norm_nonneg _) (hf.norm_le n x) one_le_two)
    _ = 1 := hf.integral_norm n

/-- Step 3 (weak compactness): a minimizing sequence has a subsequence `f ∘ φ` converging weakly
in `L²` to a strongly measurable `g ∈ L²`: `∫ z · f (φ n) → ∫ z · g` for every `z ∈ L²`
(`InnerProductSpace.tendsto_subseq_inner_left_of_norm_le` in the separable Hilbert space
`L²(ℝ^d)`). -/
theorem IsMinimizingSequence.exists_tendsto_integral_mul {a : ℝ} {f : ℕ → Euclidean d → ℝ}
    (hf : IsMinimizingSequence a f) :
    ∃ (φ : ℕ → ℕ) (g : Euclidean d → ℝ), StrictMono φ ∧ StronglyMeasurable g ∧
      MemLp g 2 volume ∧ ∀ z : Euclidean d → ℝ, MemLp z 2 volume →
        Tendsto (fun n ↦ ∫ x, z x * f (φ n) x) atTop (𝓝 (∫ x, z x * g x)) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩
  obtain ⟨φ, G, hφ, -, hG⟩ := InnerProductSpace.tendsto_subseq_inner_left_of_norm_le ℝ
    (x := fun n ↦ (hf.memLp_two n).toLp (f n)) hf.norm_toLp_le
  refine ⟨φ, G, hφ, Lp.stronglyMeasurable G, Lp.memLp G, fun z hz ↦ ?_⟩
  have key : ∀ w : Lp ℝ 2 (volume : Measure (Euclidean d)),
      ⟪w, hz.toLp z⟫_ℝ = ∫ x, z x * w x := by
    intro w
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hz.coeFn_toLp] with x hx
    rw [hx, Real.inner_apply, mul_comm]
  have h := hG (hz.toLp z)
  simp_rw [key] at h
  refine h.congr fun n ↦ integral_congr_ae ?_
  filter_upwards [(hf.memLp_two (φ n)).coeFn_toLp] with x hx
  rw [hx]

/-! ### Step 4: properties of the weak limit

Throughout, `f` is a minimizing sequence, `g` is strongly measurable, and
`∫ z · f n → ∫ z · g` for every `z ∈ L²`; the test functions are bounded and supported in sets of
finite measure. -/

section WeakLimit

variable {a : ℝ} {f : ℕ → Euclidean d → ℝ} {g : Euclidean d → ℝ}

/-- Testing the weak convergence against the indicator of a set `s` of finite measure:
`∫_s f n → ∫_s g`. -/
theorem tendsto_setIntegral_of_tendsto_integral_mul
    (hW : ∀ z : Euclidean d → ℝ, MemLp z 2 volume →
      Tendsto (fun n ↦ ∫ x, z x * f n x) atTop (𝓝 (∫ x, z x * g x)))
    {s : Set (Euclidean d)} (hs : MeasurableSet s) (hμs : volume s ≠ ∞) :
    Tendsto (fun n ↦ ∫ x in s, f n x) atTop (𝓝 (∫ x in s, g x)) := by
  have hz : MemLp (s.indicator fun _ ↦ (1 : ℝ)) 2 volume :=
    memLp_indicator_const 2 hs 1 (Or.inr hμs)
  have e : ∀ w : Euclidean d → ℝ, ∫ x, s.indicator (fun _ ↦ (1 : ℝ)) x * w x = ∫ x in s, w x := by
    intro w
    rw [← integral_indicator hs]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ s <;> simp [hx]
  simpa only [e] using hW _ hz

/-- Step 4(a): `∫_s |g| ≤ 1` for every measurable `s` of finite measure, by testing against
`s.indicator (sign g)` and `∫_s |f n| ≤ ‖f n‖₁ = 1`. -/
theorem setIntegral_norm_le_one_of_tendsto_integral_mul (hf : IsMinimizingSequence a f)
    (hg : StronglyMeasurable g)
    (hW : ∀ z : Euclidean d → ℝ, MemLp z 2 volume →
      Tendsto (fun n ↦ ∫ x, z x * f n x) atTop (𝓝 (∫ x, z x * g x)))
    {s : Set (Euclidean d)} (hs : MeasurableSet s) (hμs : volume s ≠ ∞) :
    ∫ x in s, ‖g x‖ ≤ 1 := by
  set σ : Euclidean d → ℝ := fun x ↦ if 0 ≤ g x then 1 else -1 with hσ
  have hσm : Measurable σ :=
    Measurable.ite (measurableSet_le measurable_const hg.measurable) measurable_const
      measurable_const
  have hσ1 : ∀ x, ‖σ x‖ ≤ 1 := fun x ↦ by
    simp only [hσ]
    split_ifs <;> simp
  have hz : MemLp (s.indicator σ) 2 volume :=
    memLp_indicator_of_ae_norm_le hs hμs hσm.aestronglyMeasurable (.of_forall hσ1)
  have e1 : ∫ x, s.indicator σ x * g x = ∫ x in s, ‖g x‖ := by
    rw [← integral_indicator hs]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ s
    · simp only [indicator_of_mem hx, hσ, Real.norm_eq_abs]
      split_ifs with h0
      · rw [one_mul, abs_of_nonneg h0]
      · rw [neg_one_mul, abs_of_neg (not_le.1 h0)]
    · simp [indicator_of_notMem hx]
  have h := hW _ hz
  rw [e1] at h
  refine le_of_tendsto' h fun n ↦ ?_
  calc ∫ x, s.indicator σ x * f n x ≤ ‖∫ x, s.indicator σ x * f n x‖ := Real.le_norm_self _
    _ ≤ ∫ x, ‖s.indicator σ x * f n x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖f n x‖ :=
        integral_mono_of_nonneg (.of_forall fun x ↦ norm_nonneg _) (hf.integrable n).norm
          (.of_forall fun x ↦ by
            dsimp only
            rw [norm_mul]
            exact mul_le_of_le_one_left (norm_nonneg _)
              (le_trans (norm_indicator_le_norm_self σ x) (hσ1 x)))
    _ = 1 := hf.integral_norm n

/-- Step 4(a): the weak limit `g` is integrable, with `∫ |g| ≤ 1`, since `∫_s |g| ≤ 1` for every
measurable `s` of finite measure. -/
theorem integrable_of_tendsto_integral_mul (hf : IsMinimizingSequence a f)
    (hg : StronglyMeasurable g) (hg2 : MemLp g 2 volume)
    (hW : ∀ z : Euclidean d → ℝ, MemLp z 2 volume →
      Tendsto (fun n ↦ ∫ x, z x * f n x) atTop (𝓝 (∫ x, z x * g x))) :
    Integrable g := by
  refine integrable_of_forall_fin_meas_le 1 ENNReal.one_lt_top hg.aestronglyMeasurable
    fun s hs hμs ↦ ?_
  have hint : IntegrableOn g s := by
    have : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.2 hμs
    exact (hg2.restrict s).integrable one_le_two
  rw [← ofReal_integral_norm_eq_lintegral_enorm hint]
  exact ENNReal.ofReal_le_one.2 (setIntegral_norm_le_one_of_tendsto_integral_mul hf hg hW hs hμs)

/-- Step 4(c): `∫ g ≤ 0`. For the balls `K m` of radius `a + 1 + m`, `∫_{K m} f n ≤ 0` (as
`∫ f n = 0` and `f n ≥ 0` outside `K m`), hence `∫_{K m} g ≤ 0`, and `∫_{K m} g → ∫ g`. -/
theorem integral_nonpos_of_tendsto_integral_mul (hf : IsMinimizingSequence a f)
    (hgint : Integrable g)
    (hW : ∀ z : Euclidean d → ℝ, MemLp z 2 volume →
      Tendsto (fun n ↦ ∫ x, z x * f n x) atTop (𝓝 (∫ x, z x * g x))) :
    ∫ x, g x ≤ 0 := by
  set K : ℕ → Set (Euclidean d) := fun m ↦ Metric.closedBall 0 (a + 1 + m) with hK
  have hKm : ∀ m, MeasurableSet (K m) := fun m ↦ Metric.isClosed_closedBall.measurableSet
  have hKμ : ∀ m, volume (K m) ≠ ∞ := fun m ↦ measure_closedBall_lt_top.ne
  have hmono : Monotone K := fun m m' h ↦ Metric.closedBall_subset_closedBall (by
    have : (m : ℝ) ≤ m' := by exact_mod_cast h
    linarith)
  have hunion : ⋃ m, K m = univ := by
    refine eq_univ_of_forall fun x ↦ mem_iUnion.2 ⟨⌈‖x‖ - (a + 1)⌉₊, ?_⟩
    simp only [hK, mem_closedBall_zero_iff]
    linarith [Nat.le_ceil (‖x‖ - (a + 1))]
  have hle : ∀ m, ∫ x in K m, g x ≤ 0 := fun m ↦ by
    refine le_of_tendsto' (tendsto_setIntegral_of_tendsto_integral_mul hW (hKm m) (hKμ m))
      fun n ↦ ?_
    have h1 : (∫ x in K m, f n x) + ∫ x in (K m)ᶜ, f n x = 0 := by
      rw [integral_add_compl (hKm m) (hf.integrable n), hf.integral_eq_zero n]
    have h2 : 0 ≤ ∫ x in (K m)ᶜ, f n x := by
      refine setIntegral_nonneg (hKm m).compl fun x hx ↦ hf.nonneg_of_add_one_le n x ?_
      have hx' : a + 1 + m < ‖x‖ := by simpa [hK, mem_closedBall_zero_iff] using hx
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    linarith
  have hlim := tendsto_setIntegral_of_monotone hKm hmono hgint.integrableOn
  rw [hunion, Measure.restrict_univ] at hlim
  exact le_of_tendsto' hlim hle

/-- Step 4(d): `g ≥ 0` almost everywhere outside the ball of radius `a`. On the finite-measure
annulus `S m = {a + 1/(m+1) ≤ ‖x‖ ≤ m + 1}` we have `f n ≥ 0` for `n ≥ m`, so testing against the
indicator of `S m ∩ {g < 0}` gives `∫_{S m ∩ {g < 0}} g ≥ 0`, forcing `S m ∩ {g < 0}` to be null;
these sets exhaust `{a < ‖x‖} ∩ {g < 0}`. -/
theorem ae_nonneg_of_tendsto_integral_mul (hf : IsMinimizingSequence a f)
    (hg : StronglyMeasurable g) (hg2 : MemLp g 2 volume)
    (hW : ∀ z : Euclidean d → ℝ, MemLp z 2 volume →
      Tendsto (fun n ↦ ∫ x, z x * f n x) atTop (𝓝 (∫ x, z x * g x))) :
    ∀ᵐ x, a < ‖x‖ → 0 ≤ g x := by
  set N : Set (Euclidean d) := {x | g x < 0}
  have hNm : MeasurableSet N := measurableSet_lt hg.measurable measurable_const
  set S : ℕ → Set (Euclidean d) :=
    fun m ↦ {x | a + ((m : ℝ) + 1)⁻¹ ≤ ‖x‖ ∧ ‖x‖ ≤ (m : ℝ) + 1} ∩ N
  have hSm : ∀ m, MeasurableSet (S m) := fun m ↦
    ((measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)).inter hNm
  have hSμ : ∀ m, volume (S m) ≠ ∞ := fun m ↦
    ((measure_mono fun x hx ↦ mem_closedBall_zero_iff.2 hx.1.2).trans_lt
      (measure_closedBall_lt_top (x := (0 : Euclidean d)) (r := (m : ℝ) + 1))).ne
  have hnull : ∀ m, volume (S m) = 0 := by
    intro m
    have hlim := tendsto_setIntegral_of_tendsto_integral_mul hW (hSm m) (hSμ m)
    have hge : 0 ≤ ∫ x in S m, g x := by
      refine ge_of_tendsto hlim ?_
      filter_upwards [eventually_ge_atTop m] with n hn
      exact setIntegral_nonneg (hSm m) fun x hx ↦ hf.nonneg m n hn x hx.1.1
    have hint : IntegrableOn g (S m) := by
      have : IsFiniteMeasure (volume.restrict (S m)) := isFiniteMeasure_restrict.2 (hSμ m)
      exact (hg2.restrict _).integrable one_le_two
    have hle : ∫ x in S m, g x ≤ 0 := setIntegral_nonpos (hSm m) fun x hx ↦ hx.2.le
    have h0 : ∫ x in S m, -g x = 0 := by rw [integral_neg, hle.antisymm hge, neg_zero]
    rw [integral_eq_zero_iff_of_nonneg_ae
      (ae_restrict_of_forall_mem (hSm m) fun x hx ↦ neg_nonneg.2 hx.2.le) hint.neg,
      Filter.EventuallyEq, ae_restrict_iff' (hSm m)] at h0
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h0] with x hx hxS
    have := hx hxS
    simp only [Pi.zero_apply, neg_eq_zero] at this
    exact hxS.2.ne this
  have hsub : {x : Euclidean d | ¬ (a < ‖x‖ → 0 ≤ g x)} ⊆ ⋃ m, S m := by
    intro x hx
    simp only [mem_ofPred_eq, Classical.not_imp, not_le] at hx
    obtain ⟨hax, hgx⟩ := hx
    obtain ⟨m₁, hm₁⟩ := exists_nat_one_div_lt (sub_pos.2 hax)
    refine mem_iUnion.2 ⟨max m₁ ⌈‖x‖⌉₊, ⟨⟨?_, ?_⟩, hgx⟩⟩
    · have h1 : (((max m₁ ⌈‖x‖⌉₊ : ℕ) : ℝ) + 1)⁻¹ ≤ ((m₁ : ℝ) + 1)⁻¹ := by
        refine inv_anti₀ (by positivity) ?_
        have : (m₁ : ℝ) ≤ ((max m₁ ⌈‖x‖⌉₊ : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
        linarith
      rw [one_div] at hm₁
      linarith
    · have h2 : ((⌈‖x‖⌉₊ : ℕ) : ℝ) ≤ ((max m₁ ⌈‖x‖⌉₊ : ℕ) : ℝ) := by
        exact_mod_cast le_max_right _ _
      linarith [Nat.le_ceil ‖x‖]
  rw [ae_iff]
  exact measure_mono_null hsub (measure_iUnion_null hnull)

/-! ### Step 5: the eigen-equation of the weak limit -/

/-- The complex form of the weak convergence: `∫ z · f n → ∫ z · g` for every complex `z ∈ L²`
(split `z` into real and imaginary parts). -/
theorem tendsto_integral_mul_ofReal_of_tendsto_integral_mul (hf : IsMinimizingSequence a f)
    (hg2 : MemLp g 2 volume)
    (hW : ∀ z : Euclidean d → ℝ, MemLp z 2 volume →
      Tendsto (fun n ↦ ∫ x, z x * f n x) atTop (𝓝 (∫ x, z x * g x)))
    {z : Euclidean d → ℂ} (hz : MemLp z 2 volume) :
    Tendsto (fun n ↦ ∫ x, z x * (f n x : ℂ)) atTop (𝓝 (∫ x, z x * (g x : ℂ))) := by
  have hre := hW _ hz.re
  have him := hW _ hz.im
  simp only [RCLike.re_to_complex, RCLike.im_to_complex] at hre him
  have e : ∀ w : Euclidean d → ℝ, MemLp w 2 volume → ∫ x, z x * (w x : ℂ) =
      ((∫ x, (z x).re * w x : ℝ) : ℂ) + ((∫ x, (z x).im * w x : ℝ) : ℂ) * I := by
    intro w hw
    have h1 : Integrable fun x ↦ (((z x).re * w x : ℝ) : ℂ) := by
      have := hz.re.integrable_mul hw
      simp only [RCLike.re_to_complex, Pi.mul_def] at this
      exact this.ofReal
    have h2 : Integrable fun x ↦ (((z x).im * w x : ℝ) : ℂ) * I := by
      have := hz.im.integrable_mul hw
      simp only [RCLike.im_to_complex, Pi.mul_def] at this
      exact this.ofReal.mul_const I
    rw [← integral_complex_ofReal, ← integral_complex_ofReal, ← integral_mul_const,
      ← integral_add h1 h2]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    dsimp only
    apply Complex.ext <;> simp
  simp_rw [e _ (hf.memLp_two _), e _ hg2]
  exact ((Complex.continuous_ofReal.tendsto _).comp hre).add
    (((Complex.continuous_ofReal.tendsto _).comp him).mul_const I)

/-- Step 5: the weak limit satisfies `𝓕 g = -g` almost everywhere. For a real smooth compactly
supported `ϕ` (a Schwartz function `Φ`), Fubini (`∫ (𝓕 u) Φ = ∫ u (𝓕 Φ)` for integrable `u`) and
the weak convergence give
`∫ (𝓕 g) Φ = ∫ g (𝓕 Φ) = lim ∫ f n (𝓕 Φ) = lim ∫ (𝓕 f n) Φ = -lim ∫ f n Φ = -∫ g Φ`,
so `∫ ϕ • (𝓕 g + g) = 0` for all such `ϕ`, and `𝓕 g + g = 0` a.e. -/
theorem fourier_ae_eq_neg_of_tendsto_integral_mul (hf : IsMinimizingSequence a f)
    (hgint : Integrable g)
    (hWc : ∀ z : Euclidean d → ℂ, MemLp z 2 volume →
      Tendsto (fun n ↦ ∫ x, z x * (f n x : ℂ)) atTop (𝓝 (∫ x, z x * (g x : ℂ)))) :
    ∀ᵐ x, 𝓕 (fun y ↦ (g y : ℂ)) x = -(g x : ℂ) := by
  set gℂ : Euclidean d → ℂ := fun y ↦ (g y : ℂ) with hgℂ
  have hgℂi : Integrable gℂ := hgint.ofReal
  have hcont : Continuous (𝓕 gℂ) := hgℂi.continuous_fourier
  have hloc : LocallyIntegrable (𝓕 gℂ + gℂ) :=
    hcont.locallyIntegrable.add hgℂi.locallyIntegrable
  have hae : ∀ᵐ x, (𝓕 gℂ + gℂ) x = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun ϕ hϕ hϕs ↦ ?_
    have hΦs : HasCompactSupport (Complex.ofRealCLM ∘ ϕ) := hϕs.comp_left rfl
    set Φ : 𝓢(Euclidean d, ℂ) := hΦs.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hϕ)
    have hΦx : ∀ x, Φ x = (ϕ x : ℂ) := fun x ↦ rfl
    have hΦi : Integrable (Φ : Euclidean d → ℂ) := Φ.integrable
    -- Fubini for `g` and for the `f n`.
    have h1 : ∫ ξ, 𝓕 gℂ ξ * Φ ξ = ∫ x, gℂ x * 𝓕 (Φ : Euclidean d → ℂ) x := by
      have := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ (Euclidean d))
        Real.continuous_fourierChar continuous_inner hgℂi hΦi
      simp only [flip_innerₗ, smul_eq_mul] at this
      exact this
    have h2 : ∀ n, ∫ ξ, 𝓕 (fun y ↦ (f n y : ℂ)) ξ * Φ ξ =
        ∫ x, (f n x : ℂ) * 𝓕 (Φ : Euclidean d → ℂ) x := fun n ↦ by
      have := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ (Euclidean d))
        Real.continuous_fourierChar continuous_inner (hf.integrable n).ofReal hΦi
      simp only [flip_innerₗ, smul_eq_mul] at this
      exact this
    have hΦ2 : MemLp (Φ : Euclidean d → ℂ) 2 volume := Φ.memLp 2
    have hFΦ2 : MemLp (𝓕 (Φ : Euclidean d → ℂ)) 2 volume := by
      rw [← SchwartzMap.fourier_coe]
      exact (𝓕 Φ).memLp 2
    -- The two limits.
    have hlim1 : Tendsto (fun n ↦ ∫ x, (f n x : ℂ) * 𝓕 (Φ : Euclidean d → ℂ) x) atTop
        (𝓝 (∫ x, gℂ x * 𝓕 (Φ : Euclidean d → ℂ) x)) := by
      simp_rw [mul_comm _ (𝓕 (Φ : Euclidean d → ℂ) _)]
      exact hWc _ hFΦ2
    have hlim2 : Tendsto (fun n ↦ ∫ x, (f n x : ℂ) * 𝓕 (Φ : Euclidean d → ℂ) x) atTop
        (𝓝 (-∫ x, Φ x * gℂ x)) := by
      have e : ∀ n, ∫ x, (f n x : ℂ) * 𝓕 (Φ : Euclidean d → ℂ) x =
          -∫ x, Φ x * (f n x : ℂ) := fun n ↦ by
        rw [← h2, ← integral_neg]
        refine integral_congr_ae (.of_forall fun ξ ↦ ?_)
        dsimp only
        rw [hf.fourier_eq n ξ]
        ring
      simp_rw [e]
      exact (hWc _ hΦ2).neg
    have heq : ∫ x, gℂ x * 𝓕 (Φ : Euclidean d → ℂ) x = -∫ x, Φ x * gℂ x :=
      tendsto_nhds_unique hlim1 hlim2
    -- Conclusion.
    have hi1 : Integrable fun x ↦ Φ x * 𝓕 gℂ x :=
      hΦi.mul_of_top_left (memLp_top_of_bound hcont.aestronglyMeasurable _
        (.of_forall (Real.norm_fourier_le_integral_norm gℂ)))
    have hi2 : Integrable fun x ↦ Φ x * gℂ x := hgℂi.mul_of_top_right (Φ.memLp_top volume)
    have e1 : ∫ x, Φ x * 𝓕 gℂ x = ∫ ξ, 𝓕 gℂ ξ * Φ ξ :=
      integral_congr_ae (.of_forall fun x ↦ mul_comm _ _)
    calc ∫ x, ϕ x • (𝓕 gℂ + gℂ) x = ∫ x, (Φ x * 𝓕 gℂ x + Φ x * gℂ x) := by
          refine integral_congr_ae (.of_forall fun x ↦ ?_)
          dsimp only
          rw [hΦx, Pi.add_apply, Complex.real_smul, mul_add]
      _ = (∫ x, Φ x * 𝓕 gℂ x) + ∫ x, Φ x * gℂ x := integral_add hi1 hi2
      _ = 0 := by rw [e1, h1, heq, neg_add_cancel]
  filter_upwards [hae] with x hx
  rw [Pi.add_apply] at hx
  exact eq_neg_of_add_eq_zero_left hx

/-! ### Step 6: the continuous representative and the origin correction -/

/-- Steps 4–6 combined: a minimizing sequence at level `a > 0` produces `h ∈ 𝓔₋(d)` with
`r(h) ≤ a`. The weak limit `g` of a subsequence has the continuous representative
`G = -Re 𝓕 g` (`𝓕 g = -g` a.e.), which is integrable with `𝓕 G = -G` everywhere, nonzero
(`∫_B G = ∫_B g ≤ -κ < 0`), nonnegative at the origin (`G(0) = -∫ g ≥ 0`) and nonnegative outside
the ball of radius `a` (a.e. on the open set `{a < ‖x‖}`, hence everywhere there by continuity,
and on the sphere by `nonneg_of_forall_lt_norm`); the origin correction of Cohn–Gonçalves
(`originCorrection`) makes it vanish at the origin without losing these properties. -/
theorem IsMinimizingSequence.exists_signRadius_le (hd : 0 < d) {a : ℝ} (ha : 0 < a)
    {f : ℕ → Euclidean d → ℝ} (hf : IsMinimizingSequence a f) :
    ∃ h : SignEigenfunction d (-1), signRadius (h : Euclidean d → ℝ) ≤ ENNReal.ofReal a := by
  obtain ⟨κ, hκ, hκf⟩ := hf.exists_setIntegral_closedBall_le hd
  obtain ⟨φ, g, hφ, hg, hg2, hW⟩ := hf.exists_tendsto_integral_mul
  replace hf := hf.comp hφ
  set B := Metric.closedBall (0 : Euclidean d) (a + 1)
  have hBm : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  have hBμ : volume B ≠ ∞ := measure_closedBall_lt_top.ne
  have hgint : Integrable g := integrable_of_tendsto_integral_mul hf hg hg2 hW
  have hBg : ∫ x in B, g x ≤ -κ :=
    le_of_tendsto' (tendsto_setIntegral_of_tendsto_integral_mul hW hBm hBμ) fun n ↦ hκf (φ n)
  have hg0 : ∫ x, g x ≤ 0 := integral_nonpos_of_tendsto_integral_mul hf hgint hW
  have hgnn : ∀ᵐ x, a < ‖x‖ → 0 ≤ g x := ae_nonneg_of_tendsto_integral_mul hf hg hg2 hW
  have hfour : ∀ᵐ x, 𝓕 (fun y ↦ (g y : ℂ)) x = -(g x : ℂ) :=
    fourier_ae_eq_neg_of_tendsto_integral_mul hf hgint
      fun z hz ↦ tendsto_integral_mul_ofReal_of_tendsto_integral_mul hf hg2 hW hz
  -- The continuous representative `G = -Re 𝓕 g`.
  set gℂ : Euclidean d → ℂ := fun y ↦ (g y : ℂ) with hgℂ
  have hcont : Continuous (𝓕 gℂ) := hgint.ofReal.continuous_fourier
  set G : Euclidean d → ℝ := fun x ↦ -(𝓕 gℂ x).re with hGdef
  have hGc : Continuous G := (Complex.continuous_re.comp hcont).neg
  have hGg : G =ᵐ[volume] g := by
    filter_upwards [hfour] with x hx
    simp [hGdef, hx]
  have hGint : Integrable G := hgint.congr hGg.symm
  have him : ∀ x, (𝓕 gℂ x).im = 0 := by
    have hae : (fun x ↦ (𝓕 gℂ x).im) =ᵐ[volume] fun _ ↦ (0 : ℝ) := by
      filter_upwards [hfour] with x hx
      simp [hx]
    exact fun x ↦ congrFun
      (((Complex.continuous_im.comp hcont).ae_eq_iff_eq volume continuous_const).1 hae) x
  have hGℂ : (fun x ↦ (G x : ℂ)) =ᵐ[volume] gℂ := by
    filter_upwards [hGg] with x hx
    simp only [hgℂ, hx]
  have hGfour : ∀ ξ, 𝓕 (fun x ↦ (G x : ℂ)) ξ = -(G ξ : ℂ) := fun ξ ↦ by
    rw [Real.fourier_congr_ae hGℂ]
    apply Complex.ext <;> simp [hGdef, him]
  have hGne : G ≠ 0 := fun h0 ↦ by
    have : ∫ x in B, G x = ∫ x in B, g x := integral_congr_ae (ae_restrict_of_ae hGg)
    rw [h0] at this
    simp only [Pi.zero_apply, integral_zero] at this
    linarith
  have hG0 : 0 ≤ G 0 := by
    have : G 0 = -∫ x, g x := by
      simp only [hGdef, fourier_zero_eq_integral, hgℂ, integral_complex_ofReal, Complex.ofReal_re]
    rw [this]
    linarith
  have hGnn : ∀ x : Euclidean d, a ≤ ‖x‖ → 0 ≤ G x := by
    have hU : IsOpen {x : Euclidean d | a < ‖x‖} := isOpen_lt continuous_const continuous_norm
    have hae : (fun x ↦ min (G x) 0) =ᵐ[volume.restrict {x | a < ‖x‖}] fun _ ↦ (0 : ℝ) := by
      rw [Filter.EventuallyEq, ae_restrict_iff' hU.measurableSet]
      filter_upwards [hgnn, hGg] with x hx hGx hxU
      rw [hGx]
      exact min_eq_right (hx hxU)
    have hEq := Measure.eqOn_open_of_ae_eq hae hU (hGc.min continuous_const).continuousOn
      continuousOn_const
    exact nonneg_of_forall_lt_norm hd hGc fun x hx ↦ min_eq_right_iff.1 (hEq hx)
  exact ⟨originCorrection hd G hGint hGfour hGne ha hGnn hG0,
    signRadius_originCorrection_le hd G hGint hGfour hGne ha hGnn hG0⟩

end WeakLimit

/-! ### Step 7: the extremizer and the strict inequality `A₊(d) < A₋(d)` -/

/-- Cohn–Gonçalves 2019, Theorem 1.4 (existence): `A₋(d)` is attained by some `g ∈ 𝓔₋(d)`. -/
theorem exists_signRadius_eq_signUncertaintyConstant_neg_one (hd : 0 < d) :
    ∃ g : SignEigenfunction d (-1),
      signRadius (g : Euclidean d → ℝ) = signUncertaintyConstant (-1) d := by
  have hfin := signUncertaintyConstant_neg_one_lt_top hd
  have hpos := signUncertaintyConstant_pos hd (-1)
  obtain ⟨f, hf⟩ := exists_isMinimizingSequence hd
  obtain ⟨g, hg⟩ := hf.exists_signRadius_le hd (ENNReal.toReal_pos hpos.ne' hfin.ne)
  exact ⟨g, le_antisymm (hg.trans_eq (ENNReal.ofReal_toReal hfin.ne))
    (signUncertaintyConstant_le g)⟩

/-- Appendix A of the report: `A₊(d) < A₋(d)` for every `d ≥ 1`. Let `g ∈ 𝓔₋(d)` attain
`A₋(d) < ∞` and let `h = ℛg` be its rotational average, a radial element of `𝓔₋(d)` with
`r(h) = A₋(d)`; then `T_d h ∈ 𝓔₊(d)` (Proposition A.1) has `r(T_d h) < r(h)`, so
`A₊(d) ≤ r(T_d h) < A₋(d)`. -/
theorem signUncertaintyConstant_one_lt_neg_one (hd : 0 < d) :
    signUncertaintyConstant 1 d < signUncertaintyConstant (-1) d := by
  have hfin := signUncertaintyConstant_neg_one_lt_top hd
  obtain ⟨g, hg⟩ := exists_signRadius_eq_signUncertaintyConstant_neg_one hd
  obtain ⟨R, hR⟩ := exists_nonneg_outside_of_signRadius_lt_top (hg ▸ hfin)
  have hrad : IsRadial (g.radialize hd hR : Euclidean d → ℝ) := g.radialize_eq_of_norm_eq hd hR
  have heq : signRadius (g.radialize hd hR : Euclidean d → ℝ) = signUncertaintyConstant (-1) d :=
    le_antisymm ((g.signRadius_radialize_le hd hR).trans hg.le)
      (signUncertaintyConstant_le (g.radialize hd hR))
  calc signUncertaintyConstant 1 d
      ≤ signRadius ((g.radialize hd hR).tailIntegral hd hrad : Euclidean d → ℝ) :=
        signUncertaintyConstant_le _
    _ < signRadius (g.radialize hd hR : Euclidean d → ℝ) :=
        (g.radialize hd hR).signRadius_tailIntegral_lt hd hrad (heq ▸ hfin)
    _ = signUncertaintyConstant (-1) d := heq

/-- `A_ς(d) < ∞` for `d ≥ 1` and both signs: `A₊(d) < A₋(d) < ∞`. -/
theorem signUncertaintyConstant_lt_top (hd : 0 < d) (ς : ℤˣ) :
    signUncertaintyConstant ς d < ⊤ := by
  rcases Int.units_eq_one_or ς with rfl | rfl
  · exact (signUncertaintyConstant_one_lt_neg_one hd).trans
      (signUncertaintyConstant_neg_one_lt_top hd)
  · exact signUncertaintyConstant_neg_one_lt_top hd

/-- `0 < A_ς(d) < ∞` for `d ≥ 1` and both signs. -/
theorem signUncertaintyConstant_pos_lt_top (hd : 0 < d) (ς : ℤˣ) :
    0 < signUncertaintyConstant ς d ∧ signUncertaintyConstant ς d < ⊤ :=
  ⟨signUncertaintyConstant_pos hd ς, signUncertaintyConstant_lt_top hd ς⟩

end

end CohnElkies
