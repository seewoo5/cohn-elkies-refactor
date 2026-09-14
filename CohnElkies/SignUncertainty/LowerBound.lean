import CohnElkies.SignUncertainty.SchwartzApproximation
import CohnElkies.SignUncertainty.Radialization
import CohnElkies.LowerBound.Main

/-! # The lower bound of Theorem 1.2 (report Proposition 3.7, `L¹` case)

For `0 < c < 1/π`, in all sufficiently large dimensions `d`, no sign eigenfunction
`g : SignEigenfunction d ς` (report (6): `0 ≠ g ∈ L¹`, `𝓕 g = ς g`, `g(0) = 0`) is nonnegative
outside the ball of radius `c √d`; hence `A_ς(d) ≥ c √d` and `1/π ≤ liminf A_ς(d)/√d`.

Proof (report, proof of Proposition 3.7): replace `g` by its rotational average `h = Rg ≠ 0`
(`CohnElkies.SignUncertainty.Radialization`), approximate `h` in `L¹` by real radial test functions
`q_n` with `𝓕 q_n = ς q_n`, `q_n(0) = 0` (`CohnElkies.SignUncertainty.SchwartzApproximation`); since
`∫ q_n = 0`, half of `‖q_n‖₁` is negative mass, which lies inside the ball up to `‖q_n - h‖₁`, so
`½ ‖q_n‖₁ ≤ C e^{-γ d} ‖q_n‖₁ + ‖q_n - h‖₁` by Proposition 3.1 (`exists_interior_mass_bound`);
letting `n → ∞` gives `½ ‖h‖₁ ≤ C e^{-γ d} ‖h‖₁`, impossible for large `d`. -/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform Topology

variable {d : ℕ}

/-- Pointwise negative-mass estimate: `½ (|u| - u) ≤ 1_{‖x‖ < R} |u| + |u - h|` whenever `h ≥ 0`
outside the ball of radius `R`. -/
private theorem half_abs_sub_le {u h : Euclidean d → ℝ} {R : ℝ}
    (hR : ∀ x : Euclidean d, R ≤ ‖x‖ → 0 ≤ h x) (x : Euclidean d) :
    2⁻¹ * (|u x| - u x) ≤
      (Metric.ball (0 : Euclidean d) R).indicator (fun x ↦ |u x|) x + |u x - h x| := by
  by_cases hx : x ∈ Metric.ball (0 : Euclidean d) R
  · rw [Set.indicator_of_mem hx]
    linarith [abs_nonneg (u x - h x), neg_abs_le (u x)]
  · rw [Set.indicator_of_notMem hx]
    have hh0 := hR x (by simpa [Metric.mem_ball, not_lt] using hx)
    rcases abs_cases (u x) with ⟨h1, -⟩ | ⟨h1, -⟩ <;>
      linarith [neg_le_abs (u x - h x), abs_nonneg (u x - h x)]

/-- The negative-mass estimate of the proof of Proposition 3.7: for a real test function `q` with
`∫ q = 0`, `½ ‖q‖₁ = ∫ q₋ ≤ ∫_{‖x‖ < R} |q| + ‖q - h‖₁` whenever `h ≥ 0` outside the ball of
radius `R`. -/
theorem half_integral_norm_le (q : TestFunction d) (hq : IsRealValued q) (hint : ∫ x, q x = 0)
    {h : Euclidean d → ℝ} (hh : Integrable h) {R : ℝ}
    (hR : ∀ x : Euclidean d, R ≤ ‖x‖ → 0 ≤ h x) :
    2⁻¹ * ∫ x, ‖q x‖ ≤
      (∫ x in Metric.ball (0 : Euclidean d) R, ‖q x‖) + ∫ x, ‖q x - (h x : ℂ)‖ := by
  set u : Euclidean d → ℝ := fun x ↦ (q x).re with hu
  have hui : Integrable u := q.integrable.re
  have hqu : ∀ x, q x = (u x : ℂ) := fun x ↦ Complex.ext rfl (by simp [hu, hq x])
  have hnorm : ∀ x, ‖q x‖ = |u x| := fun x ↦ by
    rw [hqu x, Complex.norm_real, Real.norm_eq_abs]
  have hint' : ∫ x, u x = 0 := by
    have h2 : ∫ x, u x = (∫ x, q x).re := integral_re q.integrable
    rw [h2, hint, Complex.zero_re]
  have h1 : ∫ x, ‖q x‖ = ∫ x, (|u x| - u x) := by
    simp_rw [hnorm]
    rw [integral_sub hui.abs hui, hint', sub_zero]
  have hi1 : Integrable ((Metric.ball (0 : Euclidean d) R).indicator fun x ↦ |u x|) :=
    hui.abs.indicator measurableSet_ball
  have hi2 : Integrable fun x ↦ |u x - h x| := (hui.sub hh).abs
  calc 2⁻¹ * ∫ x, ‖q x‖ = ∫ x, 2⁻¹ * (|u x| - u x) := by rw [h1, integral_const_mul]
    _ ≤ ∫ x, ((Metric.ball (0 : Euclidean d) R).indicator (fun x ↦ |u x|) x + |u x - h x|) :=
        integral_mono_of_nonneg
          (.of_forall fun x ↦ mul_nonneg (by norm_num) (by linarith [le_abs_self (u x)]))
          (hi1.add hi2) (.of_forall (half_abs_sub_le hR))
    _ = (∫ x in Metric.ball (0 : Euclidean d) R, |u x|) + ∫ x, |u x - h x| := by
        rw [integral_add hi1 hi2, integral_indicator measurableSet_ball]
    _ = (∫ x in Metric.ball (0 : Euclidean d) R, ‖q x‖) + ∫ x, ‖q x - (h x : ℂ)‖ := by
        congr 1
        · exact setIntegral_congr_fun measurableSet_ball fun x _ ↦ (hnorm x).symm
        · refine integral_congr_ae (.of_forall fun x ↦ ?_)
          dsimp only
          rw [hqu x, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- `∫ q = 𝓕 q (0) = ς q(0) = 0` for a test function with `𝓕 q = ς q` and `q 0 = 0`. -/
theorem integral_eq_zero_of_fourier_eq {ς : ℤˣ} (q : TestFunction d)
    (hfour : (𝓕 q : TestFunction d) = ((ς : ℤ) : ℂ) • q) (hzero : q 0 = 0) : ∫ x, q x = 0 := by
  have h := congrFun (SchwartzMap.fourier_coe q) 0
  rw [hfour, smul_apply, hzero, smul_zero, fourier_zero_eq_integral] at h
  exact h.symm

/-- `L¹` convergence implies convergence of the `L¹` norms. -/
private theorem tendsto_integral_norm_of_tendsto_integral_norm_sub {F : ℕ → Euclidean d → ℂ}
    {G : Euclidean d → ℂ} (hF : ∀ n, Integrable (F n)) (hG : Integrable G)
    (hlim : Tendsto (fun n ↦ ∫ x, ‖F n x - G x‖) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, ‖F n x‖) atTop (𝓝 (∫ x, ‖G x‖)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) hlim
  rw [← integral_sub (hF n).norm hG.norm]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (.of_forall fun _ ↦ norm_nonneg _) ((hF n).sub hG).norm (.of_forall fun x ↦ ?_))
  dsimp only
  rw [Real.norm_eq_abs]
  exact abs_norm_sub_norm_le _ _

/-- Proposition 3.7 of the report, `L¹` case: for `0 < c < 1/π`, in all sufficiently large
dimensions `d` no sign eigenfunction `g` (`0 ≠ g ∈ L¹(ℝ^d;ℝ)`, `𝓕 g = ς g`, `g(0) = 0`; report (6))
is nonnegative outside the ball of radius `c √d`. The proof follows the module docstring: radial
reduction, Schwartz approximation, the negative-mass estimate for each `q_n`, and `n → ∞`. -/
theorem eventually_not_nonneg_outside_signEigenfunction {c : ℝ} (hc : 0 < c) (hcπ : c < π⁻¹) :
    ∀ᶠ d : ℕ in atTop, ∀ (ς : ℤˣ) (g : SignEigenfunction d ς),
      ¬ ∀ x : Euclidean d, c * √d ≤ ‖x‖ → 0 ≤ g x := by
  obtain ⟨C, γ, -, hγ, hbound⟩ := exists_interior_mass_bound hc hcπ
  have hsmall : ∀ᶠ d : ℕ in atTop, C * Real.exp (-γ * d) < 2⁻¹ := by
    have hexp : Tendsto (fun d : ℕ ↦ Real.exp (-γ * (d : ℝ))) atTop (𝓝 0) := by
      simpa [Function.comp_def, neg_mul] using Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hγ))
    have h := hexp.const_mul C
    rw [mul_zero] at h
    exact h.eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [eventually_gt_atTop 0, hbound, hsmall] with d hd hbd hsm ς g hsign
  set h : SignEigenfunction d ς := g.radialize hd hsign with hh
  have hrad : IsRadial h := g.radialize_eq_of_norm_eq hd hsign
  have hnonneg : ∀ x : Euclidean d, c * √d ≤ ‖x‖ → 0 ≤ h x := fun x hx ↦
    g.radialize_nonneg hd hsign hx
  obtain ⟨q, hq, hlim⟩ := exists_schwartz_approximation hd h hrad
  set N : ℝ := ∫ x, ‖h x‖ with hN
  have hNpos : 0 < N := h.integral_norm_pos
  have key : ∀ n, 2⁻¹ * ∫ x, ‖q n x‖ ≤
      C * Real.exp (-γ * d) * (∫ x, ‖q n x‖) + ∫ x, ‖q n x - (h x : ℂ)‖ := by
    intro n
    obtain ⟨hreal, hradial, hfour, hzero⟩ := hq n
    have hhalf := half_integral_norm_le (q n) hreal
      (integral_eq_zero_of_fourier_eq (q n) hfour hzero) h.integrable hnonneg
    by_cases hq0 : q n = 0
    · have h0 : ∫ x, ‖q n x‖ = 0 := by simp [hq0]
      rw [h0]
      simpa using integral_nonneg fun x ↦ norm_nonneg (q n x - (h x : ℂ))
    · have hmass := hbd ς ⟨q n, hreal, hradial, hq0, hfour, hzero⟩
      linarith
  have hNn : Tendsto (fun n ↦ ∫ x, ‖q n x‖) atTop (𝓝 N) := by
    simpa [hN] using tendsto_integral_norm_of_tendsto_integral_norm_sub
      (fun n ↦ (q n).integrable) h.integrable_toComplex hlim
  have hfinal : 2⁻¹ * N ≤ C * Real.exp (-γ * d) * N + 0 :=
    le_of_tendsto_of_tendsto' (hNn.const_mul _) ((hNn.const_mul _).add hlim) key
  nlinarith [mul_lt_mul_of_pos_right hsm hNpos]

/-- Proposition 3.7 for the sign-uncertainty constants: `A_ς(d) ≥ c √d` for every `c < 1/π` in all
sufficiently large dimensions `d` (the lower bound of Theorem 1.2). -/
theorem eventually_ofReal_le_signUncertaintyConstant {c : ℝ} (hc : 0 < c) (hcπ : c < π⁻¹)
    (ς : ℤˣ) :
    ∀ᶠ d : ℕ in atTop, ENNReal.ofReal (c * √d) ≤ signUncertaintyConstant ς d := by
  filter_upwards [eventually_not_nonneg_outside_signEigenfunction hc hcπ] with d hd
  exact le_signUncertaintyConstant fun g ↦ hd ς g

/-- `c ≤ A_ς(d)/√d` eventually, for every `0 < c < 1/π` (in `ℝ≥0∞`). -/
theorem eventually_ofReal_le_signUncertaintyConstant_div_sqrt {c : ℝ} (hc : 0 < c)
    (hcπ : c < π⁻¹) (ς : ℤˣ) :
    ∀ᶠ d : ℕ in atTop,
      ENNReal.ofReal c ≤ signUncertaintyConstant ς d / ENNReal.ofReal (Real.sqrt d) := by
  filter_upwards [eventually_ofReal_le_signUncertaintyConstant hc hcπ ς, eventually_gt_atTop 0]
    with d hd hd0
  have hsq : 0 < √(d : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hd0)
  rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hsq).ne')
    (Or.inl ENNReal.ofReal_ne_top), ← ENNReal.ofReal_mul hc.le]
  exact hd

/-- The lower bound of Theorem 1.2 in `liminf` form: `1/π ≤ liminf_{d → ∞} A_ς(d)/√d`
(in `ℝ≥0∞`). -/
theorem le_liminf_signUncertaintyConstant_div_sqrt (ς : ℤˣ) :
    ENNReal.ofReal (Real.pi⁻¹) ≤
      liminf (fun d : ℕ ↦ signUncertaintyConstant ς d / ENNReal.ofReal (Real.sqrt d)) atTop := by
  refine le_of_forall_lt fun a ha ↦ ?_
  have ha' : a ≠ ⊤ := ne_top_of_lt ha
  have hπ : 0 < π⁻¹ := inv_pos.2 Real.pi_pos
  have hat : a.toReal < π⁻¹ := by
    rwa [← ENNReal.ofReal_lt_ofReal_iff hπ, ENNReal.ofReal_toReal ha']
  set c : ℝ := (a.toReal + π⁻¹) / 2 with hc
  have hc0 : 0 < c := by positivity
  have hcπ : c < π⁻¹ := by
    rw [hc]
    linarith
  have hac : a < ENNReal.ofReal c := by
    rw [← ENNReal.ofReal_toReal ha', ENNReal.ofReal_lt_ofReal_iff hc0, hc]
    linarith
  exact hac.trans_le (le_liminf_of_le
    (h := eventually_ofReal_le_signUncertaintyConstant_div_sqrt hc0 hcπ ς))

end

end CohnElkies
