import CohnElkies.SignUncertainty.TailIntegral

/-! # Appendix A of the report: Proposition A.1 and `A₊(d) ≤ A₋(d)`

For a radial `g ∈ E₋(d)`, `d ≥ 1`, the tail integral `T_d g` of report (87) is a self-Fourier sign
eigenfunction `T_d g ∈ E₊(d)` (`SignEigenfunction.tailIntegral`, Proposition A.1): continuous,
integrable, `𝓕 (T_d g) = T_d g`, `T_d g (0) = 0` (`CohnElkies.SignUncertainty.TailIntegral`), and
nonzero (differentiating the small-scale representation along a ray recovers `g`). If `g ≥ 0`
outside the ball of radius `R`, then `T_d g > 0` outside that ball: `T_d g (x) ≥ 0` by (87), and
`T_d g (x) = 0` would force `g`, hence `𝓕 g = -g`, to vanish outside the ball of radius `‖x‖`,
contradicting Fourier analyticity (`fourier_eq_zero_of_eq_zero_outside`). Hence `r(T_d g) ≤ r(g)`
and, when `r(g) < ∞`, `r(T_d g) < r(g)` (`SignEigenfunction.signRadius_tailIntegral_lt`).

Combined with the radial reduction `signUncertaintyConstant_eq_radial`, this gives the comparison
`A₊(d) ≤ A₋(d)` of the sign-uncertainty constants (`signUncertaintyConstant_one_le_neg_one`). The
strict inequality `A₊(d) < A₋(d)` of the report needs an extremizer attaining `A₋(d)`
(Cohn–Gonçalves 2019, Theorem 1.4) and is not formalized. -/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform Topology

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

/-! ### The comparison `A₊(d) ≤ A₋(d)` -/

/-- Appendix A of the report: `A₊(d) ≤ A₋(d)` for `d ≥ 1`. Every radial `g ∈ E₋(d)` yields
`T_d g ∈ E₊(d)` with `r(T_d g) ≤ r(g)` (Proposition A.1), and the infimum defining `A₋(d)` may
be taken over radial eigenfunctions (`signUncertaintyConstant_eq_radial`). The strict inequality
`A₊(d) < A₋(d)` stated in the report needs an extremizer attaining `A₋(d)` (Cohn–Gonçalves 2019,
Theorem 1.4, not proved in the report) and is not formalized. -/
theorem signUncertaintyConstant_one_le_neg_one (hd : 0 < d) :
    signUncertaintyConstant 1 d ≤ signUncertaintyConstant (-1) d := by
  rw [signUncertaintyConstant_eq_radial hd (-1)]
  exact le_iInf₂ fun g hg ↦ (signUncertaintyConstant_le (g.tailIntegral hd hg)).trans
    (g.signRadius_tailIntegral_le hd hg)

/-- The strict inequality `A₊(d) < A₋(d)` of Appendix A, conditional on the existence of an
extremizer: if some `g ∈ 𝓔₋(d)` attains `A₋(d) < ∞`, then `A₊(d) < A₋(d)`. The existence of such
an extremizer is Theorem 1.4 of Cohn–Gonçalves (2019), whose proof (weak `L²` compactness, Mazur's
lemma, Fatou, and a uniform negative-mass bound from Jaming's form of Nazarov's uncertainty
principle) is not part of the report and is not formalized here, so it enters as a hypothesis. -/
theorem signUncertaintyConstant_one_lt_neg_one (hd : 0 < d)
    (hfin : signUncertaintyConstant (-1) d < ⊤)
    (hext : ∃ g : SignEigenfunction d (-1),
      signRadius (g : Euclidean d → ℝ) = signUncertaintyConstant (-1) d) :
    signUncertaintyConstant 1 d < signUncertaintyConstant (-1) d := by
  obtain ⟨g, hg⟩ := hext
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

end

end CohnElkies
