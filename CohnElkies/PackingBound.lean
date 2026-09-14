import CohnElkies.SpherePacking.CohnElkiesBound
import CohnElkies.Asymptotics.Manuscript

/-!
# The sphere packing bound and Theorem 1.1 (report §1)

The Cohn–Elkies bound `Δ_d ≤ (v_d/2^d) f(0)/𝓕f(0)` for every admissible `f ∈ 𝒜_d`
(`PackingBounds.PackingBridge.sphere_packing_le_admissible`), hence `Δ_d ≤ LP_d`, equation (4)
of the report (`sphere_packing_le_linear_program`), the sharp asymptotic upper bound
`Δ_d ≤ (√(e/(2π)) + o(1))^d` (`sphere_packing_sharp_asymptotic_upper`), and Theorem 1.1 in the
two forms of the comparator challenge (`PackingBounds.FullMain.exact_limit`,
`exact_binary_exponent`). The linear program `LP_d = PackingBounds.fullLinearProgram d` is the
one of equation (3), over all of `𝒜_d`.
-/

open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory Metric
open scoped ENNReal FourierTransform SchwartzMap Topology

namespace PackingBounds.PackingBridge

/-- The ball of radius `1/2` in `ℝ^d` has volume `v_d / 2^d`. -/
theorem volume_half_ball {d : ℕ} (hd : 0 < d) :
    volume (ball (0 : CohnElkies.Euclidean d) (1 / 2 : ℝ)) =
      ENNReal.ofReal (CohnElkies.unitBallVolume d / (2 : ℝ) ^ d) := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, CohnElkies.sqrt_pi_pow_eq_rpow]
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp [CohnElkies.unitBallVolume]
  ring

/-- The Cohn–Elkies bound: each admissible `f ∈ 𝒜_d` bounds the sphere packing constant by
`2^{-d} v_d · f(0)/𝓕f(0)`. -/
theorem sphere_packing_le_admissible {d : ℕ} (hd : 0 < d) (f : CohnElkies.Admissible d) :
    SpherePackingConstant d ≤
      ENNReal.ofReal (CohnElkies.unitBallVolume d / (2 : ℝ) ^ d * CohnElkies.quotient f) := by
  have hfne : f.function ≠ 0 := fun hf ↦ by simpa [hf] using f.fourier_zero_pos
  have h := LinearProgrammingBound hfne (fun x ↦ Complex.ext (by simp) (by simp [f.real x]))
    (fun x ↦ Complex.ext (by simp) (by simp [f.fourier_real x])) f.outside_nonpos
    f.fourier_nonneg hd
  rw [volume_half_ball hd] at h
  have hratio : ((f.function (0 : CohnElkies.Euclidean d)).re.toNNReal : ENNReal) /
      (((𝓕 f.function : CohnElkies.TestFunction d)
        (0 : CohnElkies.Euclidean d)).re.toNNReal : ENNReal) =
      ENNReal.ofReal (CohnElkies.quotient f) := by
    rw [← ENNReal.coe_div (Real.toNNReal_pos.mpr f.fourier_zero_pos).ne']
    simp only [CohnElkies.quotient, fullQuotient, ENNReal.ofReal,
      Real.toNNReal_div (CohnElkies.admissible_zero_pos f).le]
  change SpherePackingConstant d ≤
    ((f.function (0 : CohnElkies.Euclidean d)).re.toNNReal : ENNReal) /
      (((𝓕 f.function : CohnElkies.TestFunction d)
        (0 : CohnElkies.Euclidean d)).re.toNNReal : ENNReal) *
      ENNReal.ofReal (CohnElkies.unitBallVolume d / (2 : ℝ) ^ d) at h
  rw [hratio, ← ENNReal.ofReal_mul (CohnElkies.quotient_pos f).le,
    mul_comm (CohnElkies.quotient f)] at h
  exact h

/-- The Cohn–Elkies bound `Δ_d ≤ LP_d`, equation (4) of the report. -/
theorem sphere_packing_le_linear_program (d : ℕ) (hd : 0 < d) :
    SpherePackingConstant d ≤ ENNReal.ofReal (PackingBounds.fullLinearProgram d) := by
  have hfactor := CohnElkies.geometricFactor_pos d
  have hfinite : SpherePackingConstant d ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (iSup_le fun P ↦ SpherePacking.upper_packing_density_le_one P)
  refine (ENNReal.le_ofReal_iff_toReal_le hfinite (CohnElkies.linearProgram_nonneg d)).2 ?_
  have hbound : (SpherePackingConstant d).toReal / (CohnElkies.unitBallVolume d / (2 : ℝ) ^ d) ≤
      sInf (CohnElkies.quotientSet d) := by
    refine le_csInf (CohnElkies.quotientSet_nonempty d) ?_
    rintro _ ⟨f, rfl⟩
    refine (div_le_iff₀ hfactor).2 ?_
    simpa [mul_comm] using ENNReal.toReal_le_of_le_ofReal
      (mul_nonneg hfactor.le (CohnElkies.quotient_pos f).le) (sphere_packing_le_admissible hd f)
  have h := (div_le_iff₀ hfactor).1 hbound
  rw [mul_comm] at h
  exact h

/-- Sharp asymptotic upper bound: `Δ_d ≤ (√(e/(2π)) + o(1))^d`. -/
theorem sphere_packing_sharp_asymptotic_upper : ∃ e : ℕ → ℝ,
      Asymptotics.IsLittleO atTop e (fun _ : ℕ ↦ (1 : ℝ)) ∧
      ∀ d : ℕ, 0 < d → SpherePackingConstant d ≤ ENNReal.ofReal
            ((√(Real.exp 1 / (2 * π)) + e d) ^ d) := by
  obtain ⟨e, he, hformula⟩ := CohnElkies.exists_manuscriptPackingIsLittleO
  refine ⟨e, he, fun d hd ↦ ?_⟩
  change SpherePackingConstant d ≤ ENNReal.ofReal ((CohnElkies.criticalPackingBase + e d) ^ d)
  rw [← hformula d hd]
  exact sphere_packing_le_linear_program d hd

end PackingBounds.PackingBridge

namespace PackingBounds.FullMain

/-- Theorem 1.1 of the report: `LP_d^{1/d} → √(e / (2π))`. -/
theorem exact_limit : Tendsto (fun d : ℕ ↦ fullLinearProgram d ^ ((d : ℝ)⁻¹)) atTop
      (nhds (√(Real.exp 1 / (2 * π)))) := by
  simpa [CohnElkies.SharpPackingRootAsymptotic, CohnElkies.criticalPackingBase] using
    CohnElkies.sharpPackingRootAsymptotic

/-- Theorem 1.1 in base-2 form: `log₂ LP_d / d → -½ log₂(2π/e) = -0.6044…`. -/
theorem exact_binary_exponent : Tendsto (fun d : ℕ ↦ Real.logb 2 (fullLinearProgram d) / (d : ℝ))
      atTop
      (nhds (-(1 / 2 : ℝ) * Real.logb 2 (2 * π / Real.exp 1))) := by
  simpa [CohnElkies.SharpBinaryLogAsymptotic, CohnElkies.criticalBinaryExponent] using
    CohnElkies.sharpBinaryLogAsymptotic

end PackingBounds.FullMain

end
