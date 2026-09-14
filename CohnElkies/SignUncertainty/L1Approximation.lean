import CohnElkies.SignUncertainty.Basic

/-! # `L¹` approximation lemmas (for the Schwartz approximation of report §2.1)

Generic facts on `ℝ^d` used to approximate an `L¹` Fourier eigenfunction by Schwartz functions:
* continuity of translation in `L¹`: `y ↦ ∫ ‖f(x - y) - f(x)‖ dx` is continuous;
* the `L¹` bound `‖f ⋆ k‖₁ ≤ ‖f‖₁ ‖k‖₁`;
* approximate identities: `‖f ⋆ k_n - f‖₁ → 0` for `k_n(x) = n^d k(n x)` with `∫ k = 1`;
* multipliers: `‖m_n f - f‖₁ → 0` for `|m_n| ≤ 1`, `m_n → 1` pointwise;
* the two combination lemmas needed for `q_n = (η_n g) ⋆ φ_n` and `𝓕 q_n = ς (κ_n ⋆ g) 𝓕 φ_n`. -/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform Topology Convolution

variable {d : ℕ}

/-! ### Continuity of translation in `L¹` -/

/-- `T_f(y) = ∫ ‖f(x - y) - f(x)‖ dx`, the `L¹` distance between `f` and its translate by `y`. -/
def translationDefect (f : Euclidean d → ℂ) (y : Euclidean d) : ℝ := ∫ x, ‖f (x - y) - f x‖

@[simp] theorem translationDefect_zero (f : Euclidean d → ℂ) : translationDefect f 0 = 0 := by
  simp [translationDefect]

theorem translationDefect_nonneg (f : Euclidean d → ℂ) (y : Euclidean d) :
    0 ≤ translationDefect f y :=
  integral_nonneg fun _ ↦ norm_nonneg _

theorem translationDefect_le {f : Euclidean d → ℂ} (hf : Integrable f) (y : Euclidean d) :
    translationDefect f y ≤ 2 * ∫ x, ‖f x‖ := by
  unfold translationDefect
  calc ∫ x, ‖f (x - y) - f x‖ ≤ ∫ x, (‖f (x - y)‖ + ‖f x‖) :=
        integral_mono_of_nonneg (.of_forall fun _ ↦ norm_nonneg _)
          ((hf.comp_sub_right y).norm.add hf.norm) (.of_forall fun x ↦ norm_sub_le _ _)
    _ = 2 * ∫ x, ‖f x‖ := by
        rw [integral_add (hf.comp_sub_right y).norm hf.norm,
          integral_sub_right_eq_self (fun x ↦ ‖f x‖) y]
        ring

/-- Translation is continuous in `L¹`: `y ↦ ‖f(· - y) - f‖₁` is continuous (via the continuity
of `MeasureTheory.Lp.compMeasurePreserving`). -/
theorem continuous_translationDefect {f : Euclidean d → ℂ} (hf : Integrable f) :
    Continuous (translationDefect f) := by
  let τ : Euclidean d → C(Euclidean d, Euclidean d) := fun y ↦ ⟨fun x ↦ x - y, by fun_prop⟩
  have hτ : Continuous τ := by
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    exact (by fun_prop : Continuous (Function.uncurry fun (y x : Euclidean d) ↦ x - y))
  have hmp : ∀ y, MeasurePreserving (τ y) volume volume := fun y ↦
    measurePreserving_sub_right volume y
  have hcont : Continuous fun y ↦
      ‖Lp.compMeasurePreserving (τ y) (hmp y) (hf.toL1 f) - hf.toL1 f‖ :=
    ((continuous_const.compMeasurePreservingLp hτ hmp ENNReal.one_ne_top).sub
      continuous_const).norm
  refine hcont.congr fun y ↦ ?_
  rw [L1.norm_eq_integral_norm]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (Lp.compMeasurePreserving (τ y) (hmp y) (hf.toL1 f)) (hf.toL1 f),
    Lp.coeFn_compMeasurePreserving (hf.toL1 f) (hmp y),
    (hmp y).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toL1, hf.coeFn_toL1] with x h1 h2 h3 h4
  simp only [Function.comp_apply] at h2 h3
  rw [h1, Pi.sub_apply, h2, h3, h4]
  rfl

/-! ### Young's inequality in `L¹` -/

/-- `‖f ⋆ k‖₁ ≤ ‖f‖₁ ‖k‖₁`. -/
theorem integral_norm_convolution_le {f k : Euclidean d → ℂ} (hf : Integrable f)
    (hk : Integrable k) :
    ∫ x, ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ] k) x‖ ≤ (∫ x, ‖f x‖) * ∫ x, ‖k x‖ := by
  have hint : Integrable (fun p : Euclidean d × Euclidean d ↦ ‖f p.2‖ * ‖k (p.1 - p.2)‖)
      (volume.prod volume) := by
    simpa using hf.norm.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hk.norm
  calc ∫ x, ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ] k) x‖
      ≤ ∫ x, ∫ t, ‖f t‖ * ‖k (x - t)‖ := by
        refine integral_mono_of_nonneg (.of_forall fun _ ↦ norm_nonneg _) hint.integral_prod_left
          (.of_forall fun x ↦ ?_)
        dsimp only
        rw [convolution_def]
        refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
        simp
    _ = ∫ t, ∫ x, ‖f t‖ * ‖k (x - t)‖ :=
        integral_integral_swap (f := fun x t ↦ ‖f t‖ * ‖k (x - t)‖) hint
    _ = ∫ t, ‖f t‖ * ∫ x, ‖k (x - t)‖ := by simp_rw [integral_const_mul]
    _ = ∫ t, ‖f t‖ * ∫ x, ‖k x‖ := by simp_rw [integral_sub_right_eq_self (fun x ↦ ‖k x‖)]
    _ = (∫ t, ‖f t‖) * ∫ x, ‖k x‖ := integral_mul_const _ _

theorem integral_norm_mul_le {f m : Euclidean d → ℂ} (hf : Integrable f)
    (hbound : ∀ x, ‖m x‖ ≤ 1) : ∫ x, ‖m x * f x‖ ≤ ∫ x, ‖f x‖ :=
  integral_mono_of_nonneg (.of_forall fun _ ↦ norm_nonneg _) hf.norm (.of_forall fun x ↦ by
    dsimp only
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hbound x))

/-- Linearity of the convolution in the left argument, where the convolution integrals exist. -/
theorem sub_convolution_apply {f g k : Euclidean d → ℂ} {x : Euclidean d}
    (hf : ConvolutionExistsAt f k x (ContinuousLinearMap.mul ℂ ℂ))
    (hg : ConvolutionExistsAt g k x (ContinuousLinearMap.mul ℂ ℂ)) :
    ((f - g) ⋆[ContinuousLinearMap.mul ℂ ℂ] k) x =
      (f ⋆[ContinuousLinearMap.mul ℂ ℂ] k) x - (g ⋆[ContinuousLinearMap.mul ℂ ℂ] k) x := by
  simp only [convolution_def, ContinuousLinearMap.mul_apply', Pi.sub_apply, sub_mul]
  simpa [ContinuousLinearMap.mul_apply'] using integral_sub hf.integrable hg.integrable

/-! ### Approximate identities -/

/-- The rescaled kernel `k_n(x) = n^d k(n x)`. -/
def scaledKernel (k : Euclidean d → ℂ) (n : ℕ) (x : Euclidean d) : ℂ :=
  (n : ℂ) ^ d * k ((n : ℝ) • x)

theorem integrable_scaledKernel {k : Euclidean d → ℂ} (hk : Integrable k) {n : ℕ} (hn : 0 < n) :
    Integrable (scaledKernel k n) :=
  (hk.comp_smul (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0)).const_mul _

/-- The change of variables `x ↦ n x` on `ℝ^d`. -/
theorem smul_integral_comp_natCast_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : Euclidean d → F) {n : ℕ} (hn : 0 < n) :
    ((n : ℝ) ^ d) • ∫ x, Φ ((n : ℝ) • x) = ∫ x, Φ x := by
  rw [Measure.integral_comp_smul_of_nonneg (μ := volume) Φ (n : ℝ) (hR := n.cast_nonneg),
    finrank_euclideanSpace_fin, smul_smul,
    mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast hn.ne')), one_smul]

theorem integral_scaledKernel (k : Euclidean d → ℂ) {n : ℕ} (hn : 0 < n) :
    ∫ x, scaledKernel k n x = ∫ x, k x := by
  unfold scaledKernel
  rw [integral_const_mul, show (n : ℂ) ^ d = (((n : ℝ) ^ d : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.real_smul, smul_integral_comp_natCast_smul k hn]

theorem integral_norm_scaledKernel (k : Euclidean d → ℂ) {n : ℕ} (hn : 0 < n) :
    ∫ x, ‖scaledKernel k n x‖ = ∫ x, ‖k x‖ := by
  unfold scaledKernel
  simp only [norm_mul, norm_pow, Complex.norm_natCast]
  rw [integral_const_mul, ← smul_eq_mul, smul_integral_comp_natCast_smul (fun x ↦ ‖k x‖) hn]

/-- `(f ⋆ k) x - f x = ∫ (f (x - t) - f x) k(t) dt` for a.e. `x`, when `∫ k = 1`. -/
private theorem ae_convolution_sub_eq_integral {f k : Euclidean d → ℂ} (hf : Integrable f)
    (hk : Integrable k) (hk1 : ∫ t, k t = 1) :
    ∀ᵐ x ∂volume, (f ⋆[ContinuousLinearMap.mul ℂ ℂ] k) x - f x =
      ∫ t, (f (x - t) - f x) * k t := by
  filter_upwards [hf.ae_convolution_exists (ContinuousLinearMap.mul ℂ ℂ) hk] with x hx
  have h1 : Integrable fun t ↦ f (x - t) * k t := by simpa using hx.integrable_swap
  have h2 : Integrable fun t ↦ f x * k t := hk.const_mul _
  calc (f ⋆[ContinuousLinearMap.mul ℂ ℂ] k) x - f x
      = (∫ t, f (x - t) * k t) - ∫ t, f x * k t := by
        rw [convolution_mul_swap, integral_const_mul, hk1, mul_one]
    _ = ∫ t, (f (x - t) - f x) * k t := by
        rw [← integral_sub h1 h2]
        simp_rw [sub_mul]

/-- The basic estimate for approximate identities:
`‖f ⋆ k_n - f‖₁ ≤ ∫ ‖k(s)‖ ‖f(· - s/n) - f‖₁ ds` (report §2.1, `q_n → g`). -/
theorem integral_norm_convolution_scaledKernel_sub_le {f k : Euclidean d → ℂ} (hf : Integrable f)
    (hk : Integrable k) (hk1 : ∫ x, k x = 1) {n : ℕ} (hn : 0 < n) :
    ∫ x, ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ] scaledKernel k n) x - f x‖ ≤
      ∫ s, ‖k s‖ * translationDefect f ((n : ℝ)⁻¹ • s) := by
  set kn := scaledKernel k n with hkn
  have hkn_int : Integrable kn := integrable_scaledKernel hk hn
  have hkn1 : ∫ t, kn t = 1 := by rw [hkn, integral_scaledKernel k hn, hk1]
  have hΨ₁ : Integrable (fun p : Euclidean d × Euclidean d ↦ f (p.1 - p.2) * kn p.2)
      (volume.prod volume) := by
    simpa [mul_comm] using hkn_int.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ).flip hf
  have hΨ₂ : Integrable (fun p : Euclidean d × Euclidean d ↦ f p.1 * kn p.2)
      (volume.prod volume) := hf.mul_prod hkn_int
  have hΨ : Integrable (fun p : Euclidean d × Euclidean d ↦ ‖(f (p.1 - p.2) - f p.1) * kn p.2‖)
      (volume.prod volume) := by
    simpa [sub_mul] using (hΨ₁.sub hΨ₂).norm
  calc ∫ x, ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ] kn) x - f x‖
      ≤ ∫ x, ∫ t, ‖(f (x - t) - f x) * kn t‖ := by
        refine integral_mono_of_nonneg (.of_forall fun _ ↦ norm_nonneg _) hΨ.integral_prod_left ?_
        filter_upwards [ae_convolution_sub_eq_integral hf hkn_int hkn1] with x hx
        rw [hx]
        exact norm_integral_le_integral_norm _
    _ = ∫ t, ∫ x, ‖(f (x - t) - f x) * kn t‖ :=
        integral_integral_swap (f := fun x t ↦ ‖(f (x - t) - f x) * kn t‖) hΨ
    _ = ∫ t, ‖kn t‖ * translationDefect f t := by
        refine integral_congr_ae (.of_forall fun t ↦ ?_)
        simp_rw [norm_mul]
        rw [integral_mul_const, mul_comm]
        rfl
    _ = ∫ s, ‖k s‖ * translationDefect f ((n : ℝ)⁻¹ • s) := by
        have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        set Φ : Euclidean d → ℝ := fun s ↦ ‖k s‖ * translationDefect f ((n : ℝ)⁻¹ • s) with hΦ
        have h : ∀ t, ‖kn t‖ * translationDefect f t = (n : ℝ) ^ d * Φ ((n : ℝ) • t) := fun t ↦ by
          simp only [hkn, hΦ, scaledKernel, norm_mul, norm_pow, Complex.norm_natCast, smul_smul,
            inv_mul_cancel₀ hn'.ne', one_smul]
          ring
        rw [integral_congr_ae (.of_forall h), integral_const_mul, ← smul_eq_mul,
          smul_integral_comp_natCast_smul Φ hn]

/-- Approximate identity in `L¹`: `‖f ⋆ k_n - f‖₁ → 0` for `k_n(x) = n^d k(n x)`, `∫ k = 1`. -/
theorem tendsto_integral_norm_convolution_scaledKernel_sub {f k : Euclidean d → ℂ}
    (hf : Integrable f) (hk : Integrable k) (hk1 : ∫ x, k x = 1) :
    Tendsto (fun n ↦ ∫ x, ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ] scaledKernel k n) x - f x‖) atTop
      (𝓝 0) := by
  have hT := continuous_translationDefect hf
  set Φ : ℕ → Euclidean d → ℝ := fun n s ↦ ‖k s‖ * translationDefect f ((n : ℝ)⁻¹ • s) with hΦ
  have hmeas : ∀ n, AEStronglyMeasurable (Φ n) volume := fun n ↦ by
    have hc : Continuous fun s : Euclidean d ↦ translationDefect f ((n : ℝ)⁻¹ • s) :=
      hT.comp (continuous_const_smul ((n : ℝ)⁻¹))
    exact hk.norm.aestronglyMeasurable.mul hc.aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ s ∂volume, ‖Φ n s‖ ≤ ‖k s‖ * (2 * ∫ x, ‖f x‖) := fun n ↦
    .of_forall fun s ↦ by
      simp only [hΦ]
      rw [norm_mul, norm_norm, Real.norm_of_nonneg (translationDefect_nonneg _ _)]
      gcongr
      exact translationDefect_le hf _
  have hpt : ∀ s, Tendsto (fun n ↦ Φ n s) atTop (𝓝 (‖k s‖ * translationDefect f 0)) := fun s ↦ by
    have h1 : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹ • s) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const s
    exact ((hT.tendsto 0).comp h1).const_mul _
  have hlim := tendsto_integral_of_dominated_convergence _ hmeas (hk.norm.mul_const _) hbound
    (.of_forall hpt)
  simp only [translationDefect_zero, mul_zero, integral_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (.of_forall fun n ↦ integral_nonneg fun _ ↦ norm_nonneg _) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact integral_norm_convolution_scaledKernel_sub_le hf hk hk1 hn

/-! ### Multipliers -/

/-- `‖m_n f - f‖₁ → 0` for multipliers `|m_n| ≤ 1` with `m_n → 1` pointwise (dominated
convergence). -/
theorem tendsto_integral_norm_mul_sub {f : Euclidean d → ℂ} (hf : Integrable f)
    {m : ℕ → Euclidean d → ℂ} (hm : ∀ n, AEStronglyMeasurable (m n) volume)
    (hbound : ∀ n x, ‖m n x‖ ≤ 1) (hlim : ∀ x, Tendsto (fun n ↦ m n x) atTop (𝓝 1)) :
    Tendsto (fun n ↦ ∫ x, ‖m n x * f x - f x‖) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (fun x ↦ 2 * ‖f x‖)
    (F := fun n x ↦ ‖m n x * f x - f x‖) (f := fun _ ↦ 0)
    (fun n ↦ (((hm n).mul hf.aestronglyMeasurable).sub hf.aestronglyMeasurable).norm)
    (hf.norm.const_mul 2) (fun n ↦ .of_forall fun x ↦ ?_) (.of_forall fun x ↦ ?_)
  · simpa using h
  · rw [norm_norm]
    calc ‖m n x * f x - f x‖ ≤ ‖m n x * f x‖ + ‖f x‖ := norm_sub_le _ _
      _ = ‖m n x‖ * ‖f x‖ + ‖f x‖ := by rw [norm_mul]
      _ ≤ 1 * ‖f x‖ + ‖f x‖ := by gcongr; exact hbound n x
      _ = 2 * ‖f x‖ := by ring
  · simpa using (((hlim x).mul_const (f x)).sub_const (f x)).norm

/-! ### The two combination lemmas -/

/-- If `H_n → G` in `L¹` and `G ⋆ φ_n → G` in `L¹` for kernels with `‖φ_n‖₁ = 1`, then
`H_n ⋆ φ_n → G` in `L¹`. -/
theorem tendsto_integral_norm_convolution_sub_of_tendsto {G : Euclidean d → ℂ}
    {H φ : ℕ → Euclidean d → ℂ} (hG : Integrable G) (hH : ∀ n, Integrable (H n))
    (hφ : ∀ n, Integrable (φ n)) (hφ1 : ∀ n, ∫ x, ‖φ n x‖ = 1)
    (hHG : Tendsto (fun n ↦ ∫ x, ‖H n x - G x‖) atTop (𝓝 0))
    (hGφ : Tendsto (fun n ↦ ∫ x, ‖(G ⋆[ContinuousLinearMap.mul ℂ ℂ] φ n) x - G x‖) atTop
      (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, ‖(H n ⋆[ContinuousLinearMap.mul ℂ ℂ] φ n) x - G x‖) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n ↦ (∫ x, ‖H n x - G x‖) * 1 +
      ∫ x, ‖(G ⋆[ContinuousLinearMap.mul ℂ ℂ] φ n) x - G x‖) atTop (𝓝 0) := by
    simpa using (hHG.mul_const 1).add hGφ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n ↦ integral_nonneg fun _ ↦ norm_nonneg _) fun n ↦ ?_
  have h1 : Integrable ((H n - G) ⋆[ContinuousLinearMap.mul ℂ ℂ] φ n) :=
    ((hH n).sub hG).integrable_convolution _ (hφ n)
  have h2 : Integrable fun x ↦ (G ⋆[ContinuousLinearMap.mul ℂ ℂ] φ n) x - G x :=
    (hG.integrable_convolution _ (hφ n)).sub hG
  calc ∫ x, ‖(H n ⋆[ContinuousLinearMap.mul ℂ ℂ] φ n) x - G x‖
      ≤ ∫ x, (‖((H n - G) ⋆[ContinuousLinearMap.mul ℂ ℂ] φ n) x‖ +
          ‖(G ⋆[ContinuousLinearMap.mul ℂ ℂ] φ n) x - G x‖) := by
        refine integral_mono_of_nonneg (.of_forall fun _ ↦ norm_nonneg _) (h1.norm.add h2.norm) ?_
        filter_upwards [(hH n).ae_convolution_exists (ContinuousLinearMap.mul ℂ ℂ) (hφ n),
          hG.ae_convolution_exists (ContinuousLinearMap.mul ℂ ℂ) (hφ n)] with x hx hx'
        rw [sub_convolution_apply hx hx']
        have h : (H n ⋆[ContinuousLinearMap.mul ℂ ℂ] φ n) x - G x =
            ((H n ⋆[ContinuousLinearMap.mul ℂ ℂ] φ n) x - (G ⋆[ContinuousLinearMap.mul ℂ ℂ] φ n) x)
              + ((G ⋆[ContinuousLinearMap.mul ℂ ℂ] φ n) x - G x) := by ring
        rw [h]
        exact norm_add_le _ _
    _ = (∫ x, ‖((H n - G) ⋆[ContinuousLinearMap.mul ℂ ℂ] φ n) x‖) +
          ∫ x, ‖(G ⋆[ContinuousLinearMap.mul ℂ ℂ] φ n) x - G x‖ :=
        integral_add h1.norm h2.norm
    _ ≤ (∫ x, ‖H n x - G x‖) * 1 +
          ∫ x, ‖(G ⋆[ContinuousLinearMap.mul ℂ ℂ] φ n) x - G x‖ := by
        have key : ∫ x, ‖((H n - G) ⋆[ContinuousLinearMap.mul ℂ ℂ] φ n) x‖ ≤
            (∫ x, ‖H n x - G x‖) * 1 := by
          rw [← hφ1 n]
          exact integral_norm_convolution_le ((hH n).sub hG) (hφ n)
        exact add_le_add key le_rfl

/-- If `A_n → G` in `L¹` and `m_n` are multipliers with `|m_n| ≤ 1`, `m_n → 1` pointwise, then
`A_n m_n → G` in `L¹`. -/
theorem tendsto_integral_norm_mul_sub_of_tendsto {G : Euclidean d → ℂ}
    {A m : ℕ → Euclidean d → ℂ} (hG : Integrable G) (hA : ∀ n, Integrable (A n))
    (hm : ∀ n, AEStronglyMeasurable (m n) volume) (hbound : ∀ n x, ‖m n x‖ ≤ 1)
    (hlim : ∀ x, Tendsto (fun n ↦ m n x) atTop (𝓝 1))
    (hAG : Tendsto (fun n ↦ ∫ x, ‖A n x - G x‖) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, ‖A n x * m n x - G x‖) atTop (𝓝 0) := by
  have hlim' : Tendsto (fun n ↦ (∫ x, ‖A n x - G x‖) + ∫ x, ‖m n x * G x - G x‖) atTop
      (𝓝 0) := by
    simpa using hAG.add (tendsto_integral_norm_mul_sub hG hm hbound hlim)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim'
    (fun n ↦ integral_nonneg fun _ ↦ norm_nonneg _) fun n ↦ ?_
  have h1 : Integrable fun x ↦ m n x * (A n x - G x) :=
    ((hA n).sub hG).bdd_mul (c := 1) (hm n) (.of_forall fun x ↦ hbound n x)
  have h2 : Integrable fun x ↦ m n x * G x - G x :=
    (hG.bdd_mul (c := 1) (hm n) (.of_forall fun x ↦ hbound n x)).sub hG
  calc ∫ x, ‖A n x * m n x - G x‖
      ≤ ∫ x, (‖m n x * (A n x - G x)‖ + ‖m n x * G x - G x‖) := by
        refine integral_mono_of_nonneg (.of_forall fun _ ↦ norm_nonneg _) (h1.norm.add h2.norm)
          (.of_forall fun x ↦ ?_)
        have hx : A n x * m n x - G x = m n x * (A n x - G x) + (m n x * G x - G x) := by ring
        dsimp only
        rw [hx]
        exact norm_add_le _ _
    _ = (∫ x, ‖m n x * (A n x - G x)‖) + ∫ x, ‖m n x * G x - G x‖ :=
        integral_add h1.norm h2.norm
    _ ≤ (∫ x, ‖A n x - G x‖) + ∫ x, ‖m n x * G x - G x‖ :=
        add_le_add (integral_norm_mul_le ((hA n).sub hG) (hbound n)) le_rfl

end

end CohnElkies
