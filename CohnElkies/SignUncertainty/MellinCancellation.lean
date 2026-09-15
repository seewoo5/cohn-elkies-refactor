import CohnElkies.SignUncertainty.Mollifiers
import CohnElkies.SignUncertainty.Radialization

/-! # The central Mellin cancellation (report Appendix A, equation (88))

For an anti-self-Fourier sign eigenfunction `g ∈ E₋(d)` (report (5)–(6)) the central Mellin moment
vanishes: `∫ g(x) ‖x‖^{-λ} dx = 0`, `λ = d/2` (`SignEigenfunction.integral_mul_norm_rpow_eq_zero`).
Following the report, the Gaussian moment `J(t) = ∫ g(x) e^{-πt‖x‖²} dx` satisfies the Gaussian
duality `J(t) = -t^{-λ} J(1/t)` (the pairing `∫ 𝓕g · φ = ∫ g · 𝓕φ`, `𝓕 g = -g`, and the Fourier
transform of the Gaussian), so that `∫_0^∞ t^{λ/2-1} J(t) dt` is its own negative under the
substitution `t ↦ 1/t`; on the other hand Fubini and the Gamma integral evaluate this integral to
`Γ(λ/2) π^{-λ/2} ∫ g(x) ‖x‖^{-λ} dx`, which therefore vanishes. For radial `g`, polar coordinates
turn this into the vanishing of the profile moment `∫_0^∞ r^{λ-1} g(r e₁) dr` (report (88)) and,
along every ray, of `∫_0^∞ s^{λ-1} g(s x) ds` (`x ≠ 0`), the integrals converging absolutely. -/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform Topology

variable {d : ℕ}

/-! ### The substitution `t ↦ 1/t` -/

/-- The change of variables `t ↦ t⁻¹` on a measurable set of nonzero reals. -/
theorem integral_inv_sq_smul_comp_inv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : ℝ → E) {s : Set ℝ} (hs : MeasurableSet s) (h0 : (0 : ℝ) ∉ s) :
    ∫ t in s, (t ^ 2)⁻¹ • G t⁻¹ = ∫ u in s⁻¹, G u := by
  rw [← Set.image_inv_eq_inv, integral_image_eq_integral_abs_deriv_smul hs
    (f' := fun t ↦ -(t ^ 2)⁻¹)
    (fun t ht ↦ (hasDerivAt_inv (ne_of_mem_of_not_mem ht h0)).hasDerivWithinAt)
    inv_injective.injOn G]
  refine setIntegral_congr_fun hs fun t _ ↦ ?_
  simp [abs_of_nonneg (sq_nonneg t)]

theorem integral_inv_sq_smul_comp_inv_Ioi_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (G : ℝ → E) :
    ∫ t in Ioi (0 : ℝ), (t ^ 2)⁻¹ • G t⁻¹ = ∫ u in Ioi (0 : ℝ), G u := by
  have h : (Ioi (0 : ℝ))⁻¹ = Ioi 0 := by
    ext u
    simp
  rw [integral_inv_sq_smul_comp_inv G measurableSet_Ioi (by simp), h]

theorem integral_inv_sq_smul_comp_inv_Ioi_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (G : ℝ → E) :
    ∫ t in Ioi (1 : ℝ), (t ^ 2)⁻¹ • G t⁻¹ = ∫ u in Ioo (0 : ℝ) 1, G u := by
  rw [integral_inv_sq_smul_comp_inv G measurableSet_Ioi (by simp), Set.inv_Ioi₀ one_pos, inv_one]

/-! ### Gaussian duality for the Gaussian moment `J(t)` -/

/-- The Gaussian moment `J(t) = ∫ g(x) e^{-πt‖x‖²} dx` of report Appendix A (proof of
Proposition A.1). -/
def gaussianMoment (g : Euclidean d → ℝ) (t : ℝ) : ℝ := ∫ x, g x * gaussianReal t x

/-- The Fourier transform is self-adjoint: `∫ 𝓕 f · φ = ∫ f · 𝓕 φ` for integrable `f`, `φ`. -/
theorem integral_fourier_mul_eq_integral_mul_fourier {f φ : Euclidean d → ℂ} (hf : Integrable f)
    (hφ : Integrable φ) : ∫ ξ, 𝓕 f ξ * φ ξ = ∫ x, f x * 𝓕 φ x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ (Euclidean d))
    Real.continuous_fourierChar continuous_inner hf hφ
  simp only [flip_innerₗ, smul_eq_mul] at h
  exact h

/-- Gaussian duality for `g ∈ E₋(d)`: `J(t) = -t^{-λ} J(1/t)`, `λ = d/2` (report, proof of
Proposition A.1). -/
theorem SignEigenfunction.gaussianMoment_eq (g : SignEigenfunction d (-1)) {t : ℝ} (ht : 0 < t) :
    gaussianMoment g t = -(t ^ (d / 2 : ℝ))⁻¹ * gaussianMoment g t⁻¹ := by
  have h := integral_fourier_mul_eq_integral_mul_fourier g.integrable_toComplex
    (integrable_ofReal_gaussianReal (d := d) ht)
  simp only [g.fourier_toComplex, fourier_gaussianReal ht, SignEigenfunction.toComplex_apply,
    Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul, integral_neg,
    mul_left_comm _ ((((t ^ (d / 2 : ℝ))⁻¹ : ℝ) : ℂ)), integral_const_mul] at h
  simp only [← Complex.ofReal_mul, integral_complex_ofReal] at h
  push_cast at h
  apply Complex.ofReal_injective
  simp only [gaussianMoment]
  push_cast
  linear_combination -h

/-! ### Fubini and the Gamma integral -/

/-- `∫ |g(x)| ‖x‖^{-λ} dx < ∞` for a bounded integrable `g` on `ℝ^d`, since `λ = d/2 < d`. -/
theorem integrable_mul_norm_rpow_neg_half (hd : 0 < d) {g : Euclidean d → ℝ} (hg : Integrable g)
    {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) :
    Integrable fun x : Euclidean d ↦ g x * ‖x‖ ^ (-(d / 2 : ℝ)) := by
  have hmeas : AEStronglyMeasurable (fun x : Euclidean d ↦ g x * ‖x‖ ^ (-(d / 2 : ℝ))) volume :=
    hg.aestronglyMeasurable.mul (measurable_norm.pow_const (-(d / 2 : ℝ)) :
      Measurable fun x : Euclidean d ↦ ‖x‖ ^ (-(d / 2 : ℝ))).aestronglyMeasurable
  have hd' : (0 : ℝ) < d := Nat.cast_pos.2 hd
  rw [← integrableOn_univ, ← Set.union_compl_self (Metric.ball (0 : Euclidean d) 1)]
  refine IntegrableOn.union ?_ ?_
  · refine integrableOn_ball_of_norm_le_rpow (μ := volume) (C := C) (α := d / 2)
      (by rw [finrank_euclideanSpace_fin]; exact hd)
      (by rw [finrank_euclideanSpace_fin]; linarith) (.of_forall fun x ↦ ?_) hmeas
    rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]
    exact mul_le_mul_of_nonneg_right (hC x) (Real.rpow_nonneg (norm_nonneg x) _)
  · refine hg.norm.integrableOn.mono' hmeas.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with x hx
    rw [norm_mul]
    refine mul_le_of_le_one_right (norm_nonneg (g x)) ?_
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by simpa using hx) (by linarith)

/-- The Gamma integral: `∫_0^∞ t^{a-1} e^{-πt‖x‖²} dt = Γ(a) π^{-a} ‖x‖^{-2a}` for `x ≠ 0`. -/
theorem integral_rpow_mul_gaussianReal {a : ℝ} (ha : 0 < a) {x : Euclidean d} (hx : x ≠ 0) :
    ∫ t in Ioi (0 : ℝ), t ^ (a - 1) * gaussianReal t x =
      Real.Gamma a * π ^ (-a) * ‖x‖ ^ (-(2 * a)) := by
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hπ : 0 < π * ‖x‖ ^ 2 := by positivity
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi ha hπ
  have e : ∀ t : ℝ, gaussianReal t x = Real.exp (-(π * ‖x‖ ^ 2 * t)) := fun t ↦ by
    simp only [gaussianReal]
    ring_nf
  simp_rw [e]
  rw [h, one_div, Real.inv_rpow hπ.le, Real.mul_rpow Real.pi_pos.le (by positivity),
    ← Real.rpow_natCast ‖x‖ 2, ← Real.rpow_mul (norm_nonneg x), mul_inv, ← Real.rpow_neg
    Real.pi_pos.le, ← Real.rpow_neg (norm_nonneg x)]
  push_cast
  ring

/-- Absolute convergence of the double integral `∫_0^∞ ∫ t^{λ/2-1} g(x) e^{-πt‖x‖²} dx dt`. -/
theorem SignEigenfunction.integrable_gaussianMoment_kernel (hd : 0 < d) {ς : ℤˣ}
    (g : SignEigenfunction d ς) :
    Integrable (fun p : ℝ × Euclidean d ↦ p.1 ^ ((d / 4 : ℝ) - 1) * (g p.2 * gaussianReal p.1 p.2))
      ((volume.restrict (Ioi 0)).prod volume) := by
  have ha : (0 : ℝ) < d / 4 := by positivity
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × Euclidean d ↦ p.1 ^ ((d / 4 : ℝ) - 1) * (g p.2 * gaussianReal p.1 p.2))
      ((volume.restrict (Ioi 0)).prod volume) :=
    ((measurable_fst.pow_const _).mul ((g.continuous.measurable.comp measurable_snd).mul
      (by unfold gaussianReal; fun_prop :
        Continuous fun p : ℝ × Euclidean d ↦ gaussianReal p.1 p.2).measurable)).aestronglyMeasurable
  rw [integrable_prod_iff' hmeas]
  refine ⟨.of_forall fun x ↦ ?_, ?_⟩
  · by_cases hx : x = 0
    · simp [hx, g.zero]
    · have hπ : 0 < π * ‖x‖ ^ 2 := by positivity
      refine IntegrableOn.congr_fun ((integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1)
        (s := d / 4 - 1) (by linarith) one_pos hπ).const_mul (g x)) (fun t _ ↦ ?_) measurableSet_Ioi
      simp only [gaussianReal, Real.rpow_one]
      ring_nf
  · have key : ∀ x : Euclidean d,
        ∫ t in Ioi (0 : ℝ), ‖t ^ ((d / 4 : ℝ) - 1) * (g x * gaussianReal t x)‖ =
          ‖g x‖ * (Real.Gamma (d / 4) * π ^ (-(d / 4 : ℝ)) * ‖x‖ ^ (-(d / 2 : ℝ))) := by
      intro x
      by_cases hx : x = 0
      · simp [hx, g.zero]
      · have h := integral_rpow_mul_gaussianReal (d := d) ha hx
        rw [show (2 : ℝ) * (d / 4) = d / 2 by ring] at h
        rw [← h, ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
        rw [norm_mul, norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (le_of_lt ht) _),
          Real.norm_of_nonneg (gaussianReal_pos t x).le]
        ring
    simp_rw [key]
    have hint := integrable_mul_norm_rpow_neg_half hd g.integrable.norm
      (C := ∫ y, ‖g y‖) fun x ↦ by simpa using g.norm_apply_le x
    refine (hint.const_mul (Real.Gamma (d / 4) * π ^ (-(d / 4 : ℝ)))).congr (.of_forall fun x ↦ ?_)
    ring

/-- `∫_0^∞ t^{λ/2-1} J(t) dt = Γ(λ/2) π^{-λ/2} ∫ g(x) ‖x‖^{-λ} dx`, `λ = d/2` (Fubini and the Gamma
integral). -/
theorem SignEigenfunction.integral_rpow_mul_gaussianMoment (hd : 0 < d) {ς : ℤˣ}
    (g : SignEigenfunction d ς) :
    ∫ t in Ioi (0 : ℝ), t ^ ((d / 4 : ℝ) - 1) * gaussianMoment g t =
      Real.Gamma (d / 4) * π ^ (-(d / 4 : ℝ)) * ∫ x, g x * ‖x‖ ^ (-(d / 2 : ℝ)) := by
  have ha : (0 : ℝ) < d / 4 := by positivity
  have h := integral_integral_swap (μ := volume.restrict (Ioi 0)) (ν := volume)
    (f := fun (t : ℝ) (x : Euclidean d) ↦ t ^ ((d / 4 : ℝ) - 1) * (g x * gaussianReal t x))
    (g.integrable_gaussianMoment_kernel hd)
  simp only [integral_const_mul] at h
  simp only [gaussianMoment]
  rw [h, ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  simp only
  by_cases hx : x = 0
  · simp [hx, g.zero]
  · have h := integral_rpow_mul_gaussianReal (d := d) ha hx
    rw [show (2 : ℝ) * (d / 4) = d / 2 by ring] at h
    simp_rw [mul_left_comm _ (g x)]
    rw [integral_const_mul, h]

/-! ### The central Mellin cancellation -/

theorem rpow_sub_one_mul_rpow_neg_two_mul {t : ℝ} (ht : 0 < t) (a : ℝ) :
    t ^ (a - 1) * (t ^ (2 * a))⁻¹ = (t ^ 2)⁻¹ * t⁻¹ ^ (a - 1) := by
  rw [Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, ← Real.rpow_neg ht.le, ← Real.rpow_add ht,
    ← Real.rpow_two, ← Real.rpow_neg ht.le, ← Real.rpow_add ht]
  congr 1
  ring

/-- The central Mellin cancellation for `g ∈ E₋(d)`: `∫ g(x) ‖x‖^{-λ} dx = 0`, `λ = d/2` (report,
proof of Proposition A.1: Gaussian duality makes `∫_0^∞ t^{λ/2-1} J(t) dt` its own negative). -/
theorem SignEigenfunction.integral_mul_norm_rpow_eq_zero (hd : 0 < d)
    (g : SignEigenfunction d (-1)) : ∫ x, g x * ‖x‖ ^ (-(d / 2 : ℝ)) = 0 := by
  have ha : (0 : ℝ) < d / 4 := by positivity
  have hsub : ∫ t in Ioi (0 : ℝ), t ^ ((d / 4 : ℝ) - 1) * gaussianMoment g t =
      -∫ t in Ioi (0 : ℝ), t ^ ((d / 4 : ℝ) - 1) * gaussianMoment g t := by
    conv_rhs => rw [← integral_inv_sq_smul_comp_inv_Ioi_zero
      (fun u ↦ u ^ ((d / 4 : ℝ) - 1) * gaussianMoment g u)]
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    rw [g.gaussianMoment_eq ht, show (d / 2 : ℝ) = 2 * (d / 4) by ring, smul_eq_mul]
    have := rpow_sub_one_mul_rpow_neg_two_mul ht (d / 4)
    linear_combination (-gaussianMoment g t⁻¹) * this
  have h0 : ∫ t in Ioi (0 : ℝ), t ^ ((d / 4 : ℝ) - 1) * gaussianMoment g t = 0 := by
    linarith
  rw [g.integral_rpow_mul_gaussianMoment hd] at h0
  exact (mul_eq_zero.1 h0).resolve_left (by positivity)

/-! ### Polar coordinates and the radial forms of the cancellation -/

/-- Polar coordinates for a radial function on `ℝ^d`: `∫ F(x) dx = S_d ∫_0^∞ r^{d-1} F(r e₁) dr`
(Mathlib's `integral_fun_norm_addHaar`). -/
theorem integral_eq_sphereArea_mul_of_radial (hd : 0 < d) {F : Euclidean d → ℝ}
    (hF : IsRadial F) :
    ∫ x, F x = sphereArea d * ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * F (r • radialUnitDirection hd) := by
  have := nontrivial_euclidean hd
  have hrad : ∀ x, F x = F (‖x‖ • radialUnitDirection hd) := fun x ↦
    hF _ _ (by simp [norm_smul, norm_radialUnitDirection hd])
  calc ∫ x, F x = ∫ x, (fun r : ℝ ↦ F (r • radialUnitDirection hd)) ‖x‖ :=
        integral_congr_ae (.of_forall hrad)
    _ = _ := by
        rw [integral_fun_norm_addHaar volume (fun r : ℝ ↦ F (r • radialUnitDirection hd)),
          finrank_euclideanSpace_fin, volume_real_unitBall hd]
        simp [sphereArea, mul_assoc]

/-- Integrability of a radial function on `ℝ^d` in polar coordinates. -/
theorem integrable_iff_of_radial (hd : 0 < d) {F : Euclidean d → ℝ} (hF : IsRadial F) :
    Integrable F ↔
      IntegrableOn (fun r : ℝ ↦ r ^ (d - 1) * F (r • radialUnitDirection hd)) (Ioi 0) := by
  have := nontrivial_euclidean hd
  have hrad : F = fun x ↦ (fun r : ℝ ↦ F (r • radialUnitDirection hd)) ‖x‖ := funext fun x ↦
    hF _ _ (by simp [norm_smul, norm_radialUnitDirection hd])
  conv_lhs => rw [hrad]
  rw [integrable_fun_norm_addHaar volume (f := fun r : ℝ ↦ F (r • radialUnitDirection hd)),
    finrank_euclideanSpace_fin]
  exact Iff.rfl

theorem rpow_sub_one_mul_rpow_neg_half (hd : 0 < d) {r : ℝ} (hr : 0 < r) :
    r ^ (d - 1) * r ^ (-(d / 2 : ℝ)) = r ^ ((d / 2 : ℝ) - 1) := by
  rw [← Real.rpow_natCast, Nat.cast_pred hd, ← Real.rpow_add hr]
  congr 1
  ring

namespace SignEigenfunction

variable (hd : 0 < d) (g : SignEigenfunction d (-1)) (hg : IsRadial (g : Euclidean d → ℝ))
include hd hg

/-- The profile moment `∫_0^∞ r^{λ-1} g(r e₁) dr` of a radial `g ∈ E₋(d)` converges
absolutely. -/
theorem integrableOn_rpow_mul_profile :
    IntegrableOn (fun r : ℝ ↦ r ^ ((d / 2 : ℝ) - 1) * g (r • radialUnitDirection hd)) (Ioi 0) := by
  have hrad : IsRadial fun x : Euclidean d ↦ g x * ‖x‖ ^ (-(d / 2 : ℝ)) := fun x y hxy ↦ by
    simp only [hg x y hxy, hxy]
  have hint := (integrable_iff_of_radial hd hrad).1 (integrable_mul_norm_rpow_neg_half hd
    g.integrable (C := ∫ y, ‖g y‖) fun x ↦ g.norm_apply_le x)
  refine hint.congr_fun (fun r hr ↦ ?_) measurableSet_Ioi
  simp only [norm_smul, norm_radialUnitDirection hd, mul_one,
    Real.norm_of_nonneg (mem_Ioi.1 hr).le]
  rw [← mul_assoc, mul_right_comm, rpow_sub_one_mul_rpow_neg_half hd hr]

/-- The central Mellin cancellation, report (88): `∫_0^∞ r^{λ-1} g(r e₁) dr = 0` for a radial
`g ∈ E₋(d)`. -/
theorem integral_rpow_mul_profile :
    ∫ r in Ioi (0 : ℝ), r ^ ((d / 2 : ℝ) - 1) * g (r • radialUnitDirection hd) = 0 := by
  have hrad : IsRadial fun x : Euclidean d ↦ g x * ‖x‖ ^ (-(d / 2 : ℝ)) := fun x y hxy ↦ by
    simp only [hg x y hxy, hxy]
  have h := g.integral_mul_norm_rpow_eq_zero hd
  rw [integral_eq_sphereArea_mul_of_radial hd hrad] at h
  refine Eq.trans ?_ ((mul_eq_zero.1 h).resolve_left (radialSurfaceArea_pos hd).ne')
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
  simp only [norm_smul, norm_radialUnitDirection hd, mul_one,
    Real.norm_of_nonneg (mem_Ioi.1 hr).le]
  rw [← mul_assoc, mul_right_comm, rpow_sub_one_mul_rpow_neg_half hd hr]

variable {x : Euclidean d} (hx : x ≠ 0)
include hx

theorem rpow_mul_smul_eq (s : ℝ) (hs : 0 < s) :
    s ^ ((d / 2 : ℝ) - 1) * g (s • x) = (‖x‖ ^ ((d / 2 : ℝ) - 1))⁻¹ *
      ((‖x‖ * s) ^ ((d / 2 : ℝ) - 1) * g ((‖x‖ * s) • radialUnitDirection hd)) := by
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [hg (s • x) ((‖x‖ * s) • radialUnitDirection hd) (by
    simp [norm_smul, norm_radialUnitDirection hd, abs_of_pos hs, mul_comm]),
    Real.mul_rpow hx'.le hs.le, ← mul_assoc, ← mul_assoc,
    inv_mul_cancel₀ (Real.rpow_pos_of_pos hx' _).ne', one_mul]

/-- Absolute convergence along rays: `∫_0^∞ s^{λ-1} |g(s x)| ds < ∞` for radial `g ∈ E₋(d)` and
`x ≠ 0`. -/
theorem integrableOn_rpow_mul_smul :
    IntegrableOn (fun s : ℝ ↦ s ^ ((d / 2 : ℝ) - 1) * g (s • x)) (Ioi 0) := by
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  have h := (integrableOn_Ioi_comp_mul_left_iff
    (fun r : ℝ ↦ r ^ ((d / 2 : ℝ) - 1) * g (r • radialUnitDirection hd)) 0 hx').2
    (by simpa using g.integrableOn_rpow_mul_profile hd hg)
  exact IntegrableOn.congr_fun (h.const_mul (‖x‖ ^ ((d / 2 : ℝ) - 1))⁻¹)
    (fun s hs ↦ (g.rpow_mul_smul_eq hd hg hx s hs).symm) measurableSet_Ioi

/-- The central Mellin cancellation along rays: `∫_0^∞ s^{λ-1} g(s x) ds = 0` for radial
`g ∈ E₋(d)` and `x ≠ 0` (report (88)). -/
theorem integral_rpow_mul_smul_eq_zero :
    ∫ s in Ioi (0 : ℝ), s ^ ((d / 2 : ℝ) - 1) * g (s • x) = 0 := by
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [setIntegral_congr_fun measurableSet_Ioi fun s hs ↦ g.rpow_mul_smul_eq hd hg hx s hs,
    integral_const_mul, integral_comp_mul_left_Ioi
    (fun r : ℝ ↦ r ^ ((d / 2 : ℝ) - 1) * g (r • radialUnitDirection hd)) 0 hx', mul_zero,
    g.integral_rpow_mul_profile hd hg, smul_zero, mul_zero]

end SignEigenfunction

end

end CohnElkies
