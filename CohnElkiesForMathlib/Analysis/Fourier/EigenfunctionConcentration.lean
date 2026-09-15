import CohnElkiesForMathlib.Analysis.Fourier.CompactSupport
import CohnElkiesForMathlib.Analysis.InnerProductSpace.WeakSequentialCompactness

/-!
# Eigenfunctions of the Fourier transform do not concentrate on a ball

Let `V` be a nontrivial finite-dimensional real inner product space and `c ≠ 0` a complex number.
We show that the `L¹`-normalized integrable eigenfunctions of the Fourier transform with
eigenvalue `c` (`𝓕 f ξ = c * f ξ` for all `ξ`, `∫ ‖f‖ = 1`) have `L¹` mass outside any given ball
`Metric.closedBall 0 R` bounded below by a positive constant `κ = κ (c, R)`
(`Real.exists_pos_le_setIntegral_norm_compl_closedBall_of_fourier_eq_mul`). This is the uniform
"no concentration" estimate needed to produce extremizers for the sign uncertainty principle of
Cohn and Gonçalves, who deduce a quantitative version from Nazarov's uncertainty principle; we
obtain the qualitative version by compactness.

The proof is by contradiction. Given normalized eigenfunctions `f n` whose mass outside the ball
`B` tends to zero, the truncations `B.indicator (f n)` are bounded in `L²` (an eigenfunction is
bounded by `‖c‖⁻¹ * ∫ ‖f‖`), hence have a weakly convergent subsequence
(`InnerProductSpace.tendsto_subseq_inner_right_of_norm_le`). Testing the weak convergence against
the truncated Fourier kernels `B.indicator (𝐞 ⟪·, ξ⟫)` shows that the Fourier transforms of the
truncations converge pointwise (`Real.inner_toLp_indicator_fourierChar_toLp`), hence
`f n = c⁻¹ * 𝓕 (f n)` converges pointwise to a continuous limit `G`
(`Real.tendsto_of_tendsto_fourier_indicator`). Dominated convergence on `B` and Fatou's lemma on
`Bᶜ` show that `G` has mass one, vanishes outside `B` and satisfies `𝓕 G = c • G`; thus `G` and
`𝓕 G` both have compact support, contradicting
`Real.eq_zero_of_hasCompactSupport_fourierIntegral`
(`Real.not_tendsto_setIntegral_norm_compl_closedBall_of_fourier_eq_mul`).

## Main results

* `MeasureTheory.memLp_indicator_of_ae_norm_le`: a bounded measurable function vanishing outside a
  set of finite measure lies in every `Lᵖ`.
* `Real.continuous_of_fourier_eq_mul`, `Real.norm_le_of_fourier_eq_mul`: an integrable
  eigenfunction of the Fourier transform with nonzero eigenvalue `c` is continuous and bounded by
  `‖c‖⁻¹ * ∫ ‖f‖`.
* `Real.norm_fourier_sub_fourier_indicator_le`: truncating an integrable function to a set `s`
  changes its Fourier transform by at most its `L¹` mass outside `s`.
* `Real.exists_pos_le_setIntegral_norm_compl_closedBall_of_fourier_eq_mul`: eigenfunctions of the
  Fourier transform do not concentrate on a ball.
-/

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform InnerProductSpace RealInnerProductSpace Topology

noncomputable section

namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E] {p : ℝ≥0∞}
  {s : Set α} {f : α → E} {M : ℝ}

/-- The `Lᵖ` seminorm of the restriction of a function bounded by `M` to a measurable set `s` is
at most `μ s ^ (1 / p) * M`. -/
theorem eLpNorm_indicator_le_of_ae_norm_le (hs : MeasurableSet s) (hM : ∀ᵐ x ∂μ, ‖f x‖ ≤ M) :
    eLpNorm (s.indicator f) p μ ≤ μ s ^ p.toReal⁻¹ * ENNReal.ofReal M := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs, ← Measure.restrict_apply_univ s]
  exact eLpNorm_le_of_ae_bound (ae_restrict_of_ae hM)

/-- A bounded measurable function vanishing outside a set of finite measure lies in every `Lᵖ`. -/
theorem memLp_indicator_of_ae_norm_le (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (hf : AEStronglyMeasurable f μ) (hM : ∀ᵐ x ∂μ, ‖f x‖ ≤ M) : MemLp (s.indicator f) p μ :=
  ⟨hf.indicator hs, (eLpNorm_indicator_le_of_ae_norm_le hs hM).trans_lt
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) hμs)
      ENNReal.ofReal_lt_top)⟩

end MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The Fourier transform of an integrable function is continuous. -/
theorem MeasureTheory.Integrable.continuous_fourier {f : V → E} (hf : Integrable f) :
    Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf

namespace Real

/-- The Fourier transform is bounded by the `L¹` norm: `‖𝓕 f ξ‖ ≤ ∫ ‖f‖`. -/
theorem norm_fourier_le_integral_norm (f : V → E) (ξ : V) : ‖𝓕 f ξ‖ ≤ ∫ x, ‖f x‖ := by
  rw [fourier_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp_rw [Circle.norm_smul]

/-- The Fourier transform of `s.indicator f` is the Fourier integral of `f` over `s`. -/
theorem fourier_indicator_eq_setIntegral {s : Set V} (hs : MeasurableSet s) (f : V → E) (ξ : V) :
    𝓕 (s.indicator f) ξ = ∫ v in s, 𝐞 (-⟪v, ξ⟫) • f v := by
  rw [fourier_eq, ← integral_indicator hs]
  refine integral_congr_ae (.of_forall fun v ↦ ?_)
  by_cases hv : v ∈ s <;> simp [hv]

/-- Truncating an integrable function to a measurable set `s` changes its Fourier transform by at
most the `L¹` mass of the function outside `s`. -/
theorem norm_fourier_sub_fourier_indicator_le {f : V → E} (hf : Integrable f) {s : Set V}
    (hs : MeasurableSet s) (ξ : V) : ‖𝓕 f ξ - 𝓕 (s.indicator f) ξ‖ ≤ ∫ x in sᶜ, ‖f x‖ := by
  rw [fourier_indicator_eq_setIntegral hs, fourier_eq,
    ← integral_add_compl hs ((fourierIntegral_convergent_iff ξ).2 hf), add_sub_cancel_left]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp_rw [Circle.norm_smul]

section Eigenfunction

variable {c : ℂ} {f : V → ℂ}

/-- An integrable eigenfunction of the Fourier transform with nonzero eigenvalue is continuous. -/
theorem continuous_of_fourier_eq_mul (hc : c ≠ 0) (hf : Integrable f)
    (h : ∀ ξ, 𝓕 f ξ = c * f ξ) : Continuous f := by
  have : f = fun ξ ↦ c⁻¹ * 𝓕 f ξ := funext fun ξ ↦ by rw [h ξ, inv_mul_cancel_left₀ hc]
  rw [this]
  exact continuous_const.mul hf.continuous_fourier

/-- An eigenfunction of the Fourier transform with nonzero eigenvalue `c` is bounded by
`‖c‖⁻¹ * ∫ ‖f‖`. -/
theorem norm_le_of_fourier_eq_mul (hc : c ≠ 0) (h : ∀ ξ, 𝓕 f ξ = c * f ξ) (ξ : V) :
    ‖f ξ‖ ≤ ‖c‖⁻¹ * ∫ x, ‖f x‖ := by
  rw [← inv_mul_cancel_left₀ hc (f ξ), ← h ξ, norm_mul, norm_inv]
  gcongr
  exact norm_fourier_le_integral_norm f ξ

end Eigenfunction

/-- The `L²` pairing of the truncated Fourier kernel `s.indicator (𝐞 ⟪·, ξ⟫)` with `w` is the
Fourier transform of the truncation `s.indicator w` at `ξ`. -/
theorem inner_toLp_indicator_fourierChar_toLp {s : Set V} (hs : MeasurableSet s) {ξ : V}
    (hz : MemLp (s.indicator fun x ↦ (𝐞 ⟪x, ξ⟫ : ℂ)) 2 volume) {w : V → ℂ}
    (hw : MemLp w 2 volume) : ⟪hz.toLp _, hw.toLp w⟫_ℂ = 𝓕 (s.indicator w) ξ := by
  rw [L2.inner_def, fourier_indicator_eq_setIntegral hs, ← integral_indicator hs]
  refine integral_congr_ae ?_
  filter_upwards [hz.coeFn_toLp, hw.coeFn_toLp] with a ha hb
  rw [ha, hb, RCLike.inner_apply']
  by_cases has : a ∈ s
  · simp only [indicator_of_mem has, Circle.smul_def, smul_eq_mul, AddChar.map_neg_eq_inv,
      Circle.coe_inv_eq_conj]
  · simp [indicator_of_notMem has]

/-- If the `L¹` mass of the Fourier eigenfunctions `f n` outside `s` tends to zero and the Fourier
transforms of the truncations `s.indicator (f n)` converge pointwise to `𝓕 g`, then `f n`
converges pointwise to `c⁻¹ * 𝓕 g`. -/
theorem tendsto_of_tendsto_fourier_indicator {c : ℂ} (hc : c ≠ 0) {f : ℕ → V → ℂ}
    (hf : ∀ n, Integrable (f n)) (heig : ∀ n ξ, 𝓕 (f n) ξ = c * f n ξ) {s : Set V}
    (hs : MeasurableSet s) (hδ : Tendsto (fun n ↦ ∫ x in sᶜ, ‖f n x‖) atTop (𝓝 0)) {g : V → ℂ}
    (hlim : ∀ ξ, Tendsto (fun n ↦ 𝓕 (s.indicator (f n)) ξ) atTop (𝓝 (𝓕 g ξ))) (ξ : V) :
    Tendsto (fun n ↦ f n ξ) atTop (𝓝 (c⁻¹ * 𝓕 g ξ)) := by
  have h1 : Tendsto (fun n ↦ 𝓕 (f n) ξ - 𝓕 (s.indicator (f n)) ξ) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n ↦ norm_fourier_sub_fourier_indicator_le (hf n) hs ξ) hδ
  have h2 : Tendsto (fun n ↦ 𝓕 (f n) ξ) atTop (𝓝 (𝓕 g ξ)) := by
    simpa using h1.add (hlim ξ)
  refine (h2.const_mul c⁻¹).congr fun n ↦ ?_
  rw [heig n ξ, inv_mul_cancel_left₀ hc]

/-- Normalized eigenfunctions of the Fourier transform converging pointwise to a continuous
function cannot have `L¹` mass outside a fixed ball tending to zero: the limit would be a
compactly supported eigenfunction of `L¹` norm one, whose Fourier transform is compactly supported
as well. -/
theorem not_tendsto_setIntegral_norm_compl_closedBall_of_fourier_eq_mul [Nontrivial V] {c : ℂ}
    (hc : c ≠ 0) {f : ℕ → V → ℂ} (hf : ∀ n, Integrable (f n))
    (heig : ∀ n ξ, 𝓕 (f n) ξ = c * f n ξ) (hone : ∀ n, ∫ x, ‖f n x‖ = 1) {G : V → ℂ}
    (hG : Continuous G) (hlim : ∀ x, Tendsto (fun n ↦ f n x) atTop (𝓝 (G x))) (R : ℝ) :
    ¬ Tendsto (fun n ↦ ∫ x in (Metric.closedBall (0 : V) R)ᶜ, ‖f n x‖) atTop (𝓝 0) := by
  intro hδ
  set B := Metric.closedBall (0 : V) R
  have hBm : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  have : IsFiniteMeasure (volume.restrict B) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  have hcont : ∀ n, Continuous (f n) := fun n ↦ continuous_of_fourier_eq_mul hc (hf n) (heig n)
  have hbdd : ∀ n x, ‖f n x‖ ≤ ‖c‖⁻¹ := fun n x ↦ by
    simpa [hone n] using norm_le_of_fourier_eq_mul hc (heig n) x
  -- `G` has `L¹` mass one on `B` (dominated convergence).
  have h4 : ∫ x in B, ‖G x‖ = 1 := by
    refine tendsto_nhds_unique (tendsto_integral_filter_of_norm_le_const
      (.of_forall fun n ↦ (hcont n).norm.aestronglyMeasurable)
      ⟨‖c‖⁻¹, .of_forall fun n ↦ .of_forall fun x ↦ by simpa using hbdd n x⟩
      (.of_forall fun x ↦ (hlim x).norm)) ?_
    have : ∀ n, ∫ x in B, ‖f n x‖ = 1 - ∫ x in Bᶜ, ‖f n x‖ := fun n ↦ by
      rw [← hone n, ← integral_add_compl hBm (hf n).norm, add_sub_cancel_right]
    simp_rw [this]
    simpa using tendsto_const_nhds.sub hδ
  -- `G` vanishes outside `B` (Fatou's lemma and continuity).
  have h5 : ∀ x, x ∉ B → G x = 0 := by
    have hae : G =ᵐ[volume.restrict Bᶜ] 0 := by
      have hfatou := lintegral_liminf_le (μ := volume.restrict Bᶜ) (u := atTop)
        fun n ↦ (hcont n).measurable.enorm
      have hzero : Tendsto (fun n ↦ ∫⁻ x in Bᶜ, ‖f n x‖ₑ) atTop (𝓝 0) := by
        have : ∀ n, ∫⁻ x in Bᶜ, ‖f n x‖ₑ = ENNReal.ofReal (∫ x in Bᶜ, ‖f n x‖) := fun n ↦
          (ofReal_integral_norm_eq_lintegral_enorm (hf n).integrableOn).symm
        simp_rw [this]
        simpa using ENNReal.tendsto_ofReal hδ
      simp_rw [show ∀ x, liminf (fun n ↦ ‖f n x‖ₑ) atTop = ‖G x‖ₑ from
        fun x ↦ (hlim x).enorm.liminf_eq, hzero.liminf_eq, nonpos_iff_eq_zero,
        lintegral_eq_zero_iff' hG.measurable.enorm.aemeasurable] at hfatou
      filter_upwards [hfatou] with x hx
      simpa using hx
    exact fun x hx ↦ Measure.eqOn_open_of_ae_eq hae
      (isOpen_compl_iff.2 Metric.isClosed_closedBall) hG.continuousOn continuousOn_const hx
  have hGsupp : HasCompactSupport G := HasCompactSupport.intro (isCompact_closedBall 0 R) h5
  -- `𝓕 G = c • G` (dominated convergence on `B`).
  have h6 : ∀ ξ, 𝓕 G ξ = c * G ξ := by
    intro ξ
    have hBG : B.indicator G = G := indicator_eq_self.2 fun x hx ↦ by_contra fun h ↦ hx (h5 x h)
    have hlim6 : Tendsto (fun n ↦ 𝓕 (B.indicator (f n)) ξ) atTop (𝓝 (𝓕 G ξ)) := by
      rw [show 𝓕 G ξ = 𝓕 (B.indicator G) ξ by rw [hBG]]
      simp_rw [fourier_indicator_eq_setIntegral hBm]
      refine tendsto_integral_filter_of_norm_le_const
        (.of_forall fun n ↦
          ((fourierIntegral_convergent_iff ξ).2 (hf n)).aestronglyMeasurable.restrict)
        ⟨‖c‖⁻¹, .of_forall fun n ↦ .of_forall fun x ↦ ?_⟩
        (.of_forall fun x ↦ (hlim x).const_smul _)
      rw [Circle.norm_smul]
      exact hbdd n x
    have hlim6' : Tendsto (fun n ↦ 𝓕 (B.indicator (f n)) ξ) atTop (𝓝 (c * G ξ)) := by
      have h1 : Tendsto (fun n ↦ 𝓕 (f n) ξ - 𝓕 (B.indicator (f n)) ξ) atTop (𝓝 0) :=
        squeeze_zero_norm (fun n ↦ norm_fourier_sub_fourier_indicator_le (hf n) hBm ξ) hδ
      have h2 : Tendsto (fun n ↦ 𝓕 (f n) ξ) atTop (𝓝 (c * G ξ)) := by
        simp_rw [heig]
        exact (hlim ξ).const_mul c
      simpa using h2.sub h1
    exact tendsto_nhds_unique hlim6 hlim6'
  have hGfourier : HasCompactSupport (𝓕 G) :=
    HasCompactSupport.intro (isCompact_closedBall 0 R) fun x hx ↦ by rw [h6 x, h5 x hx, mul_zero]
  have hG0 := eq_zero_of_hasCompactSupport_fourierIntegral hG
    (hG.integrable_of_hasCompactSupport hGsupp) hGsupp hGfourier
  rw [hG0] at h4
  simp at h4

/-- **Eigenfunctions of the Fourier transform do not concentrate on a ball**: for `c ≠ 0` and
`R : ℝ` there is `κ > 0` such that every integrable `f : V → ℂ` with `𝓕 f ξ = c * f ξ` for all
`ξ` and `∫ ‖f‖ = 1` has `L¹` mass at least `κ` outside the closed ball of radius `R`. -/
theorem exists_pos_le_setIntegral_norm_compl_closedBall_of_fourier_eq_mul [Nontrivial V] {c : ℂ}
    (hc : c ≠ 0) (R : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ f : V → ℂ, Integrable f → (∀ ξ, 𝓕 f ξ = c * f ξ) → ∫ x, ‖f x‖ = 1 →
      κ ≤ ∫ x in (Metric.closedBall (0 : V) R)ᶜ, ‖f x‖ := by
  by_contra! h
  choose f hf heig hone hlt using fun n : ℕ ↦ h (1 / ((n : ℝ) + 1)) (by positivity)
  set B := Metric.closedBall (0 : V) R
  have hBm : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  have hBμ : volume B ≠ ∞ := measure_closedBall_lt_top.ne
  have hδ : Tendsto (fun n ↦ ∫ x in Bᶜ, ‖f n x‖) atTop (𝓝 0) :=
    squeeze_zero (fun n ↦ integral_nonneg fun x ↦ norm_nonneg _) (fun n ↦ (hlt n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hbdd : ∀ n x, ‖f n x‖ ≤ ‖c‖⁻¹ := fun n x ↦ by
    simpa [hone n] using norm_le_of_fourier_eq_mul hc (heig n) x
  -- The truncations `B.indicator (f n)` are bounded in `L²`: extract a weakly convergent
  -- subsequence.
  have hmem : ∀ n, MemLp (B.indicator (f n)) 2 volume := fun n ↦
    memLp_indicator_of_ae_norm_le hBm hBμ (hf n).aestronglyMeasurable (.of_forall (hbdd n))
  have hnorm : ∀ n, ‖(hmem n).toLp _‖ ≤
      (volume B ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal ‖c‖⁻¹).toReal := fun n ↦ by
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top
      (ENNReal.rpow_lt_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) hBμ).ne
      ENNReal.ofReal_ne_top) (eLpNorm_indicator_le_of_ae_norm_le hBm (.of_forall (hbdd n)))
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩
  obtain ⟨φ, g, hφ, -, hg⟩ := InnerProductSpace.tendsto_subseq_inner_right_of_norm_le ℂ hnorm
  -- Identify the weak limit through the truncated Fourier kernels.
  have hg' : Integrable (B.indicator (g : V → ℂ)) := by
    rw [integrable_indicator_iff hBm]
    have : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.2 hBμ
    exact ((Lp.memLp g).restrict B).integrable one_le_two
  have hlim : ∀ ξ, Tendsto (fun n ↦ 𝓕 (B.indicator (f (φ n))) ξ) atTop
      (𝓝 (𝓕 (B.indicator (g : V → ℂ)) ξ)) := by
    intro ξ
    have hz : MemLp (B.indicator fun x ↦ (𝐞 ⟪x, ξ⟫ : ℂ)) 2 volume :=
      memLp_indicator_of_ae_norm_le hBm hBμ
        (by fun_prop : Continuous fun x : V ↦ (𝐞 ⟪x, ξ⟫ : ℂ)).aestronglyMeasurable
        (.of_forall fun x ↦ (Circle.norm_coe _).le)
    have := hg (hz.toLp _)
    rw [← Lp.toLp_coeFn g (Lp.memLp g), inner_toLp_indicator_fourierChar_toLp hBm hz] at this
    refine this.congr fun n ↦ ?_
    rw [inner_toLp_indicator_fourierChar_toLp hBm hz, indicator_indicator, inter_self]
  exact not_tendsto_setIntegral_norm_compl_closedBall_of_fourier_eq_mul hc (fun n ↦ hf (φ n))
    (fun n ↦ heig (φ n)) (fun n ↦ hone (φ n))
    (G := fun ξ ↦ c⁻¹ * 𝓕 (B.indicator (g : V → ℂ)) ξ) (continuous_const.mul hg'.continuous_fourier)
    (tendsto_of_tendsto_fourier_indicator hc (fun n ↦ hf (φ n)) (fun n ↦ heig (φ n)) hBm
      (hδ.comp hφ.tendsto_atTop) hlim) R (hδ.comp hφ.tendsto_atTop)

end Real

end
