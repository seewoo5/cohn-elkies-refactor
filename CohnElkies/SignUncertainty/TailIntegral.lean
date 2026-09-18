import CohnElkies.SignUncertainty.MellinCancellation

/-! # The tail-integration operator `T_d` (report Appendix A, (87) and (89))

`T_d g (x) = (λ/2) ∫_1^∞ t^{λ-1} g(t x) dt` (`tailIntegral`, report (87)), `λ = d/2`, for a radial
`g ∈ E₋(d)`. By the central Mellin cancellation along rays
(`SignEigenfunction.integral_rpow_mul_smul_eq_zero`) it has the small-scale representation
`T_d g (x) = -(λ/2) ∫_0^1 s^{λ-1} g(s x) ds` (report (89)), valid also at `x = 0`; hence `T_d g` is
continuous (dominated convergence). Tonelli on the large-scale representation gives integrability
and `‖T_d g‖₁ ≤ ½ ‖g‖₁`, and Fubini, Fourier scaling and the substitution `s = 1/t` give the
self-Fourier property `𝓕 (T_d g) = T_d g` (report (89)). -/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform Topology RealInnerProductSpace

variable {d : ℕ}

/-- The tail-integration operator `T_d g (x) = (λ/2) ∫_1^∞ t^{λ-1} g(t x) dt` of report (87),
`λ = d/2`, with `T_d g (0) = 0`. -/
def tailIntegral (d : ℕ) (g : Euclidean d → ℝ) (x : Euclidean d) : ℝ :=
  if x = 0 then 0 else (d / 2 : ℝ) / 2 * ∫ t in Ioi (1 : ℝ), t ^ ((d / 2 : ℝ) - 1) * g (t • x)

@[simp] theorem tailIntegral_zero (g : Euclidean d → ℝ) : tailIntegral d g 0 = 0 := ite_eq_left rfl

theorem tailIntegral_of_ne_zero (g : Euclidean d → ℝ) {x : Euclidean d} (hx : x ≠ 0) :
    tailIntegral d g x = (d / 2 : ℝ) / 2 * ∫ t in Ioi (1 : ℝ), t ^ ((d / 2 : ℝ) - 1) * g (t • x) :=
  ite_eq_right hx

/-- For `g(0) = 0` the large-scale formula (87) also holds at `x = 0`. -/
theorem tailIntegral_eq_of_zero (g : Euclidean d → ℝ) (hg : g 0 = 0) (x : Euclidean d) :
    tailIntegral d g x =
      (d / 2 : ℝ) / 2 * ∫ t in Ioi (1 : ℝ), t ^ ((d / 2 : ℝ) - 1) * g (t • x) := by
  by_cases hx : x = 0
  · simp [hx, hg]
  · exact tailIntegral_of_ne_zero g hx

/-- `T_d g` is radial when `g` is. -/
theorem IsRadial.tailIntegral {g : Euclidean d → ℝ} (hg : IsRadial g) :
    IsRadial (tailIntegral d g) := by
  intro x y hxy
  by_cases hx : x = 0
  · have hy : y = 0 := norm_eq_zero.1 (by rw [← hxy, hx, norm_zero])
    simp [hx, hy]
  · have hy : y ≠ 0 := fun h ↦ hx (norm_eq_zero.1 (by rw [hxy, h, norm_zero]))
    rw [tailIntegral_of_ne_zero g hx, tailIntegral_of_ne_zero g hy]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
    rw [hg (t • x) (t • y) (by simp [norm_smul, hxy])]

namespace SignEigenfunction

variable (hd : 0 < d) (g : SignEigenfunction d (-1)) (hg : IsRadial (g : Euclidean d → ℝ))
include hd hg

/-! ### The small-scale representation and continuity -/

/-- The small-scale representation of report (89): `T_d g (x) = -(λ/2) ∫_0^1 s^{λ-1} g(s x) ds`,
for every `x` (both sides vanish at `x = 0`); from the central Mellin cancellation along the ray
through `x`. -/
theorem tailIntegral_eq_neg_integral_Ioo (x : Euclidean d) :
    tailIntegral d g x =
      -((d / 2 : ℝ) / 2) * ∫ s in Ioo (0 : ℝ) 1, s ^ ((d / 2 : ℝ) - 1) * g (s • x) := by
  by_cases hx : x = 0
  · simp [hx, g.zero]
  · rw [tailIntegral_of_ne_zero _ hx, neg_mul, ← mul_neg]
    congr 1
    have hint := g.integrableOn_rpow_mul_smul hd hg hx
    have h0 := g.integral_rpow_mul_smul_eq_zero hd hg hx
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi (hint.mono_set Ioc_subset_Ioi_self)
      (hint.mono_set (Ioi_subset_Ioi zero_le_one)), integral_Ioc_eq_integral_Ioo] at h0
    linarith

/-- `T_d g` is continuous (dominated convergence on the small-scale representation, `g` being
bounded and continuous and `s^{λ-1}` integrable on `(0, 1)`). -/
theorem continuous_tailIntegral : Continuous (tailIntegral d g) := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.2 hd
  have hrepr : tailIntegral d g = fun x ↦
      -((d / 2 : ℝ) / 2) * ∫ s in Ioo (0 : ℝ) 1, s ^ ((d / 2 : ℝ) - 1) * g (s • x) :=
    funext (g.tailIntegral_eq_neg_integral_Ioo hd hg)
  rw [hrepr]
  refine continuous_const.mul (continuous_of_dominated
    (bound := fun s ↦ s ^ ((d / 2 : ℝ) - 1) * ∫ y, ‖g y‖) ?_ ?_ ?_ ?_)
  · intro x
    exact ((measurable_id.pow_const _).mul (g.continuous.comp
      (continuous_id.smul continuous_const : Continuous fun s : ℝ ↦ s • x)).measurable
      ).aestronglyMeasurable
  · intro x
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hs.1.le _)]
    exact mul_le_mul_of_nonneg_left (g.norm_apply_le _) (Real.rpow_nonneg hs.1.le _)
  · exact ((intervalIntegral.integrableOn_Ioo_rpow_iff one_pos).2 (by linarith)).mul_const _
  · exact .of_forall fun s ↦ continuous_const.mul (g.continuous.comp (continuous_const_smul s))

/-! ### Integrability and the `L¹` bound `‖T_d g‖₁ ≤ ½ ‖g‖₁` -/

omit hd hg in
/-- `∫ |t^{λ-1} g(t x)| dx = t^{-λ-1} ‖g‖₁` for `t > 0` (the substitution `y = t x`, `d = 2λ`). -/
theorem integral_norm_rpow_mul_smul {t : ℝ} (ht : 0 < t) :
    ∫ x, ‖t ^ ((d / 2 : ℝ) - 1) * g (t • x)‖ = t ^ (-(d / 2 : ℝ) - 1) * ∫ x, ‖g x‖ := by
  simp_rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]
  rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg (volume : Measure (Euclidean d))
    (fun x ↦ ‖g x‖) t (hR := ht.le), finrank_euclideanSpace_fin, smul_eq_mul, ← mul_assoc,
    ← Real.rpow_natCast, ← Real.rpow_neg ht.le, ← Real.rpow_add ht]
  congr 2
  ring

omit hg in
/-- The integrand `(x, t) ↦ t^{λ-1} g(t x)` of (87) is absolutely integrable on `ℝ^d × (1, ∞)`
(Tonelli: `∫ |g(t x)| dx = t^{-d} ‖g‖₁` and `∫_1^∞ t^{λ-1-d} dt < ∞`). -/
theorem integrable_tailIntegral_kernel :
    Integrable (fun p : Euclidean d × ℝ ↦ p.2 ^ ((d / 2 : ℝ) - 1) * g (p.2 • p.1))
      (volume.prod (volume.restrict (Ioi 1))) := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.2 hd
  have hmeas : AEStronglyMeasurable
      (fun p : Euclidean d × ℝ ↦ p.2 ^ ((d / 2 : ℝ) - 1) * g (p.2 • p.1))
      (volume.prod (volume.restrict (Ioi 1))) :=
    ((measurable_snd.pow_const _).mul (g.continuous.measurable.comp
      (continuous_snd.smul continuous_fst).measurable)).aestronglyMeasurable
  rw [integrable_prod_iff' hmeas]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (g.integrable.comp_smul (zero_lt_one.trans ht).ne').const_mul _
  · refine IntegrableOn.congr_fun ((integrableOn_Ioi_rpow_of_lt (a := -(d / 2 : ℝ) - 1)
      (by linarith) one_pos).mul_const (∫ x, ‖g x‖)) (fun t ht ↦ ?_) measurableSet_Ioi
    exact (g.integral_norm_rpow_mul_smul (zero_lt_one.trans ht)).symm

omit hg in
theorem integrable_integral_norm_tailIntegral_kernel :
    Integrable fun x ↦ ∫ t in Ioi (1 : ℝ), ‖t ^ ((d / 2 : ℝ) - 1) * g (t • x)‖ :=
  (g.integrable_tailIntegral_kernel hd).norm.integral_prod_left

omit hg in
/-- `∫ ∫_1^∞ t^{λ-1} |g(t x)| dt dx = ‖g‖₁ / λ` (Tonelli and `∫_1^∞ t^{-λ-1} dt = 1/λ`). -/
theorem integral_integral_norm_tailIntegral_kernel :
    ∫ x, ∫ t in Ioi (1 : ℝ), ‖t ^ ((d / 2 : ℝ) - 1) * g (t • x)‖ = (d / 2 : ℝ)⁻¹ * ∫ x, ‖g x‖ := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.2 hd
  rw [integral_integral_swap (f := fun (x : Euclidean d) (t : ℝ) ↦
      ‖t ^ ((d / 2 : ℝ) - 1) * g (t • x)‖) (g.integrable_tailIntegral_kernel hd).norm,
    setIntegral_congr_fun measurableSet_Ioi fun t ht ↦
      g.integral_norm_rpow_mul_smul (zero_lt_one.trans ht),
    integral_mul_const, integral_Ioi_rpow_of_lt (a := -(d / 2 : ℝ) - 1) (by linarith) one_pos,
    Real.one_rpow]
  congr 1
  rw [show -(d / 2 : ℝ) - 1 + 1 = -(d / 2) by ring, div_neg, neg_div, neg_neg, one_div]

omit hd hg in
/-- `|T_d g (x)| ≤ (λ/2) ∫_1^∞ t^{λ-1} |g(t x)| dt`. -/
theorem norm_tailIntegral_le (x : Euclidean d) :
    ‖tailIntegral d g x‖ ≤
      (d / 2 : ℝ) / 2 * ∫ t in Ioi (1 : ℝ), ‖t ^ ((d / 2 : ℝ) - 1) * g (t • x)‖ := by
  rw [tailIntegral_eq_of_zero _ g.zero, norm_mul, Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)

/-- `T_d g` is integrable. -/
theorem integrable_tailIntegral : Integrable (tailIntegral d g) :=
  ((g.integrable_integral_norm_tailIntegral_kernel hd).const_mul ((d / 2 : ℝ) / 2)).mono'
    (g.continuous_tailIntegral hd hg).aestronglyMeasurable (.of_forall g.norm_tailIntegral_le)

/-- `‖T_d g‖₁ ≤ ½ ‖g‖₁` (report, proof of Proposition A.1). -/
theorem integral_norm_tailIntegral_le : ∫ x, ‖tailIntegral d g x‖ ≤ 1 / 2 * ∫ x, ‖g x‖ := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.2 hd
  calc ∫ x, ‖tailIntegral d g x‖
      ≤ ∫ x, (d / 2 : ℝ) / 2 * ∫ t in Ioi (1 : ℝ), ‖t ^ ((d / 2 : ℝ) - 1) * g (t • x)‖ :=
        integral_mono (g.integrable_tailIntegral hd hg).norm
          ((g.integrable_integral_norm_tailIntegral_kernel hd).const_mul _) g.norm_tailIntegral_le
    _ = (d / 2 : ℝ) / 2 * ((d / 2 : ℝ)⁻¹ * ∫ x, ‖g x‖) := by
        rw [integral_const_mul, g.integral_integral_norm_tailIntegral_kernel hd]
    _ = 1 / 2 * ∫ x, ‖g x‖ := by
        field_simp

/-! ### The self-Fourier property `𝓕 (T_d g) = T_d g` -/

end SignEigenfunction

/-- Fourier scaling for plain functions: `𝓕 (f (t ·)) (ξ) = t^{-d} 𝓕 f (ξ / t)` for `t > 0`. -/
theorem fourier_comp_smul (f : Euclidean d → ℂ) {t : ℝ} (ht : 0 < t) (ξ : Euclidean d) :
    𝓕 (fun x ↦ f (t • x)) ξ = ((t ^ d)⁻¹ : ℝ) • 𝓕 f (t⁻¹ • ξ) := by
  have h := Measure.integral_comp_smul_of_nonneg (volume : Measure (Euclidean d))
    (fun y ↦ Complex.exp (↑(-2 * π * ⟪y, t⁻¹ • ξ⟫) * I) • f y) t (hR := ht.le)
  rw [Real.fourier_eq', Real.fourier_eq']
  simp only [finrank_euclideanSpace_fin, real_inner_smul_left, real_inner_smul_right,
    inv_mul_cancel_left₀ ht.ne'] at h ⊢
  exact h

theorem rpow_sub_one_mul_inv_pow {t : ℝ} (ht : 0 < t) (d : ℕ) :
    t ^ ((d / 2 : ℝ) - 1) * (t ^ d)⁻¹ = t ^ (-(d / 2 : ℝ) - 1) := by
  rw [← Real.rpow_natCast, ← Real.rpow_neg ht.le, ← Real.rpow_add ht]
  congr 1
  ring

namespace SignEigenfunction

variable (hd : 0 < d) (g : SignEigenfunction d (-1)) (hg : IsRadial (g : Euclidean d → ℝ))
include hd hg

omit hd hg in
/-- The substitution `s = 1/t` in the large-scale integral:
`∫_1^∞ t^{-λ-1} g(ξ/t) dt = ∫_0^1 s^{λ-1} g(s ξ) ds`. -/
theorem integral_rpow_mul_inv_smul (ξ : Euclidean d) :
    ∫ t in Ioi (1 : ℝ), t ^ (-(d / 2 : ℝ) - 1) * g (t⁻¹ • ξ) =
      ∫ s in Ioo (0 : ℝ) 1, s ^ ((d / 2 : ℝ) - 1) * g (s • ξ) := by
  rw [← integral_inv_sq_smul_comp_inv_Ioi_one fun s ↦ s ^ ((d / 2 : ℝ) - 1) * g (s • ξ)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
  have ht0 : 0 < t := zero_lt_one.trans ht
  simp only [smul_eq_mul]
  rw [← mul_assoc, Real.inv_rpow ht0.le, ← Real.rpow_neg ht0.le, ← Real.rpow_two,
    ← Real.rpow_neg ht0.le, ← Real.rpow_add ht0]
  congr 2
  ring

/-- The self-Fourier property `𝓕 (T_d g) = T_d g` of report (89): Fubini on the large-scale
representation, Fourier scaling `𝓕(g(t ·))(ξ) = t^{-d} 𝓕 g (ξ/t) = -t^{-d} g(ξ/t)`, the
substitution `s = 1/t`, and the small-scale representation. -/
theorem fourier_tailIntegral (ξ : Euclidean d) :
    𝓕 (fun x ↦ (tailIntegral d g x : ℂ)) ξ = tailIntegral d g ξ := by
  set e : Euclidean d → ℂ := fun x ↦ Complex.exp (↑(-2 * π * ⟪x, ξ⟫) * I) with he
  have he1 : ∀ x, ‖e x‖ = 1 := fun x ↦ Complex.norm_exp_ofReal_mul_I _
  have hK : Integrable
      (fun p : Euclidean d × ℝ ↦ e p.1 * ((p.2 ^ ((d / 2 : ℝ) - 1) * g (p.2 • p.1) : ℝ) : ℂ))
      (volume.prod (volume.restrict (Ioi 1))) :=
    (g.integrable_tailIntegral_kernel hd).ofReal.bdd_mul (c := 1)
      ((by fun_prop : Continuous fun p : Euclidean d × ℝ ↦ e p.1).aestronglyMeasurable)
      (.of_forall fun p ↦ (he1 p.1).le)
  have hinner : ∀ t ∈ Ioi (1 : ℝ),
      ∫ x, e x * ((t ^ ((d / 2 : ℝ) - 1) * g (t • x) : ℝ) : ℂ) =
        -((t ^ (-(d / 2 : ℝ) - 1) * g (t⁻¹ • ξ) : ℝ) : ℂ) := by
    intro t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    have h1 : ∫ x, e x * ((t ^ ((d / 2 : ℝ) - 1) * g (t • x) : ℝ) : ℂ) =
        ((t ^ ((d / 2 : ℝ) - 1) : ℝ) : ℂ) * 𝓕 (fun x ↦ g.toComplex (t • x)) ξ := by
      rw [Real.fourier_eq', ← integral_const_mul]
      refine integral_congr_ae (.of_forall fun x ↦ ?_)
      simp only [he, toComplex_apply, smul_eq_mul]
      push_cast
      ring
    rw [h1, fourier_comp_smul g.toComplex ht0 ξ, g.fourier_toComplex, Complex.real_smul,
      ← rpow_sub_one_mul_inv_pow ht0 d]
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
    push_cast
    ring
  calc 𝓕 (fun x ↦ (tailIntegral d g x : ℂ)) ξ
      = ∫ x, e x • (tailIntegral d g x : ℂ) := Real.fourier_eq' _ _
    _ = ∫ x, (((d / 2 : ℝ) / 2 : ℝ) : ℂ) *
          ∫ t in Ioi (1 : ℝ), e x * ((t ^ ((d / 2 : ℝ) - 1) * g (t • x) : ℝ) : ℂ) := by
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        dsimp only
        rw [tailIntegral_eq_of_zero _ g.zero, integral_const_mul, integral_complex_ofReal,
          smul_eq_mul]
        push_cast
        ring
    _ = (((d / 2 : ℝ) / 2 : ℝ) : ℂ) *
          ∫ t in Ioi (1 : ℝ), ∫ x, e x * ((t ^ ((d / 2 : ℝ) - 1) * g (t • x) : ℝ) : ℂ) := by
        rw [integral_const_mul, integral_integral_swap (f := fun (x : Euclidean d) (t : ℝ) ↦
          e x * ((t ^ ((d / 2 : ℝ) - 1) * g (t • x) : ℝ) : ℂ)) hK]
    _ = (((d / 2 : ℝ) / 2 : ℝ) : ℂ) *
          -((∫ t in Ioi (1 : ℝ), t ^ (-(d / 2 : ℝ) - 1) * g (t⁻¹ • ξ) : ℝ) : ℂ) := by
        rw [setIntegral_congr_fun measurableSet_Ioi hinner, integral_neg, integral_complex_ofReal]
    _ = tailIntegral d g ξ := by
        rw [g.integral_rpow_mul_inv_smul ξ, g.tailIntegral_eq_neg_integral_Ioo hd hg ξ]
        push_cast
        ring

end SignEigenfunction

end

end CohnElkies
