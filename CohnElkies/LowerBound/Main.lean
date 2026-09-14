import CohnElkies.LowerBound.CenteredMax

/-!
# The lower bound of Theorem 1.1 (report §3, Propositions 3.1 and 3.7)

Proposition 3.1 (`exists_interior_mass_bound`): for `c < 1/π` and all large `d`, a radial
eigenfunction has at most `C e^{-γ d}` of its `L¹` mass inside the ball of radius `c √d`;
hence (`eventually_not_nonneg_outside`) no radial eigenfunction vanishing at the origin is
nonnegative outside that ball, which is Proposition 3.7 in the form `uniformAntiFourierSignRadius`.
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory Real Set
open scoped ENNReal Topology

theorem lowerInverseQuadraticMass_pos : 0 < lowerInverseQuadraticMass :=
  integral_pos_of_integrable_nonneg_nonzero (x := 0)
    (continuous_const.div₀ (by fun_prop) fun S ↦ by positivity) inverseQuadraticAbs_integrable
    (fun S ↦ by positivity) (by norm_num)

/-- Proposition 3.1 of the report: for `0 < c < 1/π` there are `C, γ > 0` such that in every
large dimension `d`, every nonzero real radial Schwartz `g` with `𝓕 g = ±g` and `g(0) = 0` has
exponentially small mass inside the ball of radius `c√d`: `∫_{‖x‖ < c√d} |g| ≤ C e^{-γd} ‖g‖₁`.
The constants come from the Cauchy-type majorant of Lemma 3.6 and depend only on `c`. -/
theorem exists_interior_mass_bound {c : ℝ} (hc : 0 < c) (hcπ : c < π⁻¹) :
    ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧ ∀ᶠ d : ℕ in atTop, ∀ (ς : ℤˣ) (g : RadialEigenfunction d ς),
      ∫ x in Metric.ball (0 : Euclidean d) (c * √d), ‖g.toFun x‖ ≤
        C * exp (-γ * d) * ∫ x, ‖g.toFun x‖ := by
  obtain ⟨σ, γ, C, hσpos, hσone, hγ, hC, hmajor⟩ :=
    exists_lowerStripPoissonMajorant_integrable_majorant hc hcπ
  have hσbelow : (-1 : ℝ) < σ := by linarith
  have hσ' : (0 : ℝ) < 1 - σ := sub_pos.mpr hσone
  have hM := lowerInverseQuadraticMass_pos
  refine ⟨(2 * π)⁻¹ * (C * lowerInverseQuadraticMass) / (1 - σ), γ / 2, by positivity,
    by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop 0, hmajor] with d hd hmaj ς g
  have hR : 0 < c * √(d : ℝ) := mul_pos hc (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd))
  have hℓ : (0 : ℝ) < (d : ℝ) / 2 := by positivity
  have hL1 := integral_norm_Z_g_le_of_majorant hd g hR hσbelow hσone
    (norm_Z_g_le_exp_H_σ hd g hR hσbelow hσone) hmaj
  refine (g.setIntegral_ball_norm_le hd hR hσbelow hσone).trans ?_
  calc ((2 * π)⁻¹ * ∫ s : ℝ, ‖Z_g hd g.toFun (c * √d)
          ((s : ℂ) + I * (σ * ((d : ℂ) / 2)))‖) / ((1 - σ) * ((d : ℝ) / 2)) *
        L1norm g.toFun
      ≤ (2 * π)⁻¹ * (C * lowerInverseQuadraticMass * ((d : ℝ) / 2) *
          exp (-γ * ((d : ℝ) / 2))) / ((1 - σ) * ((d : ℝ) / 2)) * L1norm g.toFun := by
        gcongr
        exact g.L1norm_pos.le
    _ = (2 * π)⁻¹ * (C * lowerInverseQuadraticMass) / (1 - σ) * exp (-(γ / 2) * d) *
          L1norm g.toFun := by
        rw [show -(γ / 2) * (d : ℝ) = -γ * ((d : ℝ) / 2) by ring]
        field_simp

/-- Proposition 3.7 of the report, Schwartz case: for `0 < c < 1/π`, in every large dimension no
nonzero real radial Schwartz `g` with `𝓕 g = ±g` and `g(0) = 0` is nonnegative outside the ball
of radius `c√d`. Indeed `∫ g = 𝓕 g (0) = 0` forces half of `‖g‖₁` to be negative mass, which by
Proposition 3.1 cannot fit inside the ball. -/
theorem eventually_not_nonneg_outside {c : ℝ} (hc : 0 < c) (hcπ : c < π⁻¹) :
    ∀ᶠ d : ℕ in atTop, ∀ (ς : ℤˣ) (g : RadialEigenfunction d ς),
      ¬ ∀ x : Euclidean d, c * √d ≤ ‖x‖ → 0 ≤ (g.toFun x).re := by
  obtain ⟨C, γ, -, hγ, hbound⟩ := exists_interior_mass_bound hc hcπ
  have hsmall : ∀ᶠ d : ℕ in atTop, C * exp (-γ * d) < 1 / 2 := by
    have hexp : Tendsto (fun d : ℕ ↦ exp (-γ * (d : ℝ))) atTop (𝓝 0) := by
      simpa [Function.comp_def, neg_mul] using Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hγ))
    exact (hexp.const_mul C).eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [eventually_gt_atTop 0, hbound, hsmall] with d hd hbd hsm ς g hsign
  have hR : 0 < c * √(d : ℝ) := mul_pos hc (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd))
  have hhalf := half_le_setIntegral_Iic_abs (g.integrable_logProfile hd hR)
    (g.integral_logProfile hd hR) (g.integral_abs_logProfile hd hR)
    fun v hv ↦ logProfile_nonneg_of_exterior hd g.toFun g.ne_zero hR hsign hv
  rw [g.setIntegral_Iic_abs_logProfile hd hR, le_div_iff₀ g.L1norm_pos] at hhalf
  have hbd' : (∫ x in Metric.ball (0 : Euclidean d) (c * √d), ‖g.toFun x‖) ≤
      C * exp (-γ * d) * L1norm g.toFun := hbd ς g
  nlinarith [mul_lt_mul_of_pos_right hsm g.L1norm_pos]

/-- Report Proposition 3.7 in the form used by Theorem 3.8: below the critical radius `1/π`
there is no anti-self-Fourier witness of radius `c√d` in all large dimensions. -/
theorem uniformAntiFourierSignRadius : UniformAntiFourierSignRadius := fun c hc hcπ ↦ by
  filter_upwards [eventually_not_nonneg_outside hc hcπ] with d hd
  exact ⟨fun w ↦ hd (-1) w.toRadialEigenfunction w.eventually_nonneg⟩

end

end CohnElkies
