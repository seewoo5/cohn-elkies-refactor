import CohnElkies.LowerBound.MellinStrip
import CohnElkies.LowerBound.PoissonKernel
import CohnElkiesForMathlib.Analysis.SpecialFunctions.Gamma.Basic
import CohnElkiesForMathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The Gamma boundary function `h_λ` on the lower edge of the strip (report §3.2, Lemma 3.3)

The bound `|Z(x - id/2)| ≤ e^{h_λ(x)}` on the lower edge of the strip with
`h_λ(x) = log |Γ((d/2 - ix)/2)/Γ((d/2 + ix)/2)|`-type boundary function of report (7) and (17), its
explicit forms in even and odd dimensions via the Gamma recurrences (7), the correction
`½ log coth (π|Y|/2)` in odd dimensions, monotonicity and integrability properties, the negativity
of the rescaled boundary function, and the Riemann-sum comparison `f_T(x) = log sqrt(1 + x²)`
with its midpoint/left error terms and endpoint phase (report, proof of Lemma 3.3).
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Real

/-! ### The Gamma recurrences of report (7) -/

/-- The gamma recurrence at `z = iy/2` (report (7), even dimensions). -/
theorem integer_gamma_product (k : ℕ) {y : ℝ} (hy : y ≠ 0) :
    Complex.Gamma (k + I * y / 2) =
      Complex.Gamma (I * y / 2) * ∏ j ∈ Finset.range k, (j + I * y / 2) := by
  have hz (j : ℕ) : I * y / 2 + j ≠ 0 := fun h ↦ hy (by simpa using congrArg Complex.im h)
  simpa [add_comm] using Complex.Gamma_add_nat_eq_mul_prod _ hz k

/-- The gamma recurrence at `z = 1/2 + iy/2` (report (7), odd dimensions). -/
theorem half_integer_gamma_product (k : ℕ) (y : ℝ) :
    Complex.Gamma (k + 1 / 2 + I * y / 2) =
      Complex.Gamma (1 / 2 + I * y / 2) * ∏ j ∈ Finset.range k, (j + 1 / 2 + I * y / 2) := by
  have hz (j : ℕ) : 1 / 2 + I * y / 2 + j ≠ 0 := fun h ↦ by
    have := congrArg Complex.re h
    norm_num at this
    linarith [j.cast_nonneg (α := ℝ)]
  simpa [add_comm, add_left_comm, add_assoc] using Complex.Gamma_add_nat_eq_mul_prod _ hz k

end

noncomputable section

open Filter MeasureTheory Real Set
open scoped FourierTransform Interval RealInnerProductSpace Topology

/-- A normalized profile (unit mass, zero mean, nonnegative on `[0, ∞)`) carries at least half
of its mass on `(-∞, 0]`; report (13). -/
theorem half_le_setIntegral_Iic_abs {φ : ℝ → ℝ} (hφ : Integrable φ)
    (hmean : (∫ v : ℝ, φ v) = 0) (hmass : (∫ v : ℝ, |φ v|) = 1)
    (hsign : ∀ v : ℝ, 0 ≤ v → 0 ≤ φ v) :
    (1 / 2 : ℝ) ≤ ∫ v in Iic (0 : ℝ), |φ v| := by
  have hneg : Integrable (fun v : ℝ ↦ max (-φ v) 0) := hφ.neg.sup (integrable_zero ℝ ℝ volume)
  have hpoint : ∀ v : ℝ, |φ v| - φ v = 2 * max (-φ v) 0 := fun v ↦ by
    rcases le_total 0 (φ v) with h | h
    · rw [abs_of_nonneg h, max_eq_right (by linarith)]; ring
    · rw [abs_of_nonpos h, max_eq_left (by linarith)]; ring
  have hhalf : (∫ v : ℝ, max (-φ v) 0) = 1 / 2 := by
    have h : (∫ v : ℝ, (|φ v| - φ v)) = 1 := by
      rw [integral_sub hφ.abs hφ, hmass, hmean]
      norm_num
    rw [integral_congr_ae (.of_forall hpoint), integral_const_mul] at h
    linarith
  calc (1 / 2 : ℝ) = ∫ v in Iic (0 : ℝ), max (-φ v) 0 := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero, hhalf]
        intro v hv
        exact max_eq_right (by linarith [hsign v (by simpa using hv : (0 : ℝ) < v).le])
    _ ≤ ∫ v in Iic (0 : ℝ), |φ v| :=
        setIntegral_mono_on hneg.integrableOn hφ.abs.integrableOn measurableSet_Iic
          fun v _ ↦ max_le (neg_le_abs _) (abs_nonneg _)

/-- If a profile is recovered from a strip trace `Z` by Fourier inversion at height `a`, its
`L¹` mass on `(-∞, 0]` is at most `(2π)⁻¹‖Z‖₁ / a`. -/
theorem negativeHalfline_le_of_fourierInversion {φ : ℝ → ℝ} (hφ : Integrable φ) {a : ℝ}
    (ha : 0 < a) (Z : ℝ → ℂ)
    (hinversion : ∀ v : ℝ, (φ v : ℂ) =
      (exp (a * v) : ℂ) * ((𝓕⁻ (fun ξ : ℝ ↦ Z (2 * π * ξ)) : ℝ → ℂ) v)) :
    (∫ v in Iic (0 : ℝ), |φ v|) ≤ ((2 * π)⁻¹ * ∫ s : ℝ, ‖Z s‖) / a := by
  have hfourier : ∀ v : ℝ, ‖(𝓕⁻ (fun ξ : ℝ ↦ Z (2 * π * ξ)) : ℝ → ℂ) v‖ ≤
      (2 * π)⁻¹ * ∫ s : ℝ, ‖Z s‖ := fun v ↦ by
    refine (VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
      (-innerₗ ℝ) (fun ξ : ℝ ↦ Z (2 * π * ξ)) v).trans_eq ?_
    rw [Measure.integral_comp_mul_left (fun s : ℝ ↦ ‖Z s‖) (2 * π)]
    change |(2 * π)⁻¹| * (∫ s : ℝ, ‖Z s‖) = (2 * π)⁻¹ * (∫ s : ℝ, ‖Z s‖)
    rw [abs_of_pos (inv_pos.mpr (by positivity))]
  have hbound : ∀ v : ℝ, v ≤ 0 → |φ v| ≤ ((2 * π)⁻¹ * ∫ s : ℝ, ‖Z s‖) * exp (a * v) := by
    intro v _
    rw [show |φ v| = ‖(φ v : ℂ)‖ by simp, hinversion v, norm_mul,
      Complex.norm_of_nonneg (exp_pos _).le, mul_comm]
    exact mul_le_mul_of_nonneg_right (hfourier v) (exp_pos _).le
  calc (∫ v in Iic (0 : ℝ), |φ v|)
      ≤ ∫ v in Iic (0 : ℝ), ((2 * π)⁻¹ * ∫ s : ℝ, ‖Z s‖) * exp (a * v) :=
        setIntegral_mono_on hφ.abs.integrableOn
          ((integrableOn_exp_mul_Iic ha 0).const_mul _) measurableSet_Iic hbound
    _ = ((2 * π)⁻¹ * ∫ s : ℝ, ‖Z s‖) / a := by
        rw [integral_const_mul, integral_exp_mul_Iic ha 0]
        simp [div_eq_mul_inv]

namespace RadialEigenfunction

variable {d : ℕ} {ς : ℤˣ}

theorem diffContOnCl_Z_g (hd : 0 < d) (g : RadialEigenfunction d ς) (R : ℝ) :
    DiffContOnCl ℂ (Z_g hd g.toFun R) (Complex.im ⁻¹' Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2)) :=
  normalizedRadialMellinStrip_diffContOnCl hd g.toFun g.radial g.zero R

/-- Report (16): `|Z(y + iλ)| ≤ 1` on the top edge of the strip. -/
theorem norm_Z_g_top_le_one (hd : 0 < d) (g : RadialEigenfunction d ς) (R y : ℝ) :
    ‖Z_g hd g.toFun R ((y : ℂ) + I * ((d : ℂ) / 2))‖ ≤ 1 :=
  normalizedRadialMellinStrip_top_norm_le_one hd g.toFun g.radial g.ne_zero R y

theorem exists_norm_Z_g_le (hd : 0 < d) (g : RadialEigenfunction d ς) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, -((d : ℝ) / 2) ≤ z.im → z.im ≤ (d : ℝ) / 2 →
      ‖Z_g hd g.toFun R z‖ ≤ C :=
  normalizedRadialMellinStrip_uniform_bound hd g.toFun g.radial g.zero R

theorem integrable_Z_g_shifted (hd : 0 < d) (g : RadialEigenfunction d ς) {R : ℝ} (hR : 0 < R)
    {a : ℝ} (ha : a < (d : ℝ)) :
    Integrable (fun t : ℝ ↦ Z_g hd g.toFun R ((t : ℂ) + I * ((d : ℂ) / 2 - a))) :=
  normalizedRadialMellinStrip_shifted_integrable hd g.toFun g.real hR ha

/-- Lemmas 3.2 and 3.6 of the report combined: the mass of a radial eigenfunction `g` in the
ball of radius `R` is controlled by the `L¹` norm of `Z` on the interior line `Im z = σλ`:
`∫_{‖x‖<R} |g| ≤ ((2π)⁻¹ ‖Z(· + iσλ)‖₁ / ((1 - σ) λ)) ‖g‖₁`. -/
theorem setIntegral_ball_norm_le (hd : 0 < d) (g : RadialEigenfunction d ς) {R σ : ℝ}
    (hR : 0 < R) (hσbelow : -1 < σ) (hσabove : σ < 1) :
    (∫ x in Metric.ball (0 : Euclidean d) R, ‖g.toFun x‖) ≤
      ((2 * π)⁻¹ * ∫ s : ℝ, ‖Z_g hd g.toFun R ((s : ℂ) + I * (σ * ((d : ℂ) / 2)))‖) /
        ((1 - σ) * ((d : ℝ) / 2)) * L1norm g.toFun := by
  have hℓ : 0 < (d : ℝ) / 2 := half_pos (Nat.cast_pos.mpr hd)
  have ha : 0 < (1 - σ) * ((d : ℝ) / 2) := mul_pos (sub_pos.mpr hσabove) hℓ
  have haless : (1 - σ) * ((d : ℝ) / 2) < (d : ℝ) := by
    nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 + σ) hℓ]
  have hupper := negativeHalfline_le_of_fourierInversion (g.integrable_logProfile hd hR) ha
    (fun s : ℝ ↦ Z_g hd g.toFun R
      ((s : ℂ) + I * ((d : ℂ) / 2 - ((1 - σ) * ((d : ℝ) / 2) : ℝ))))
    (fun v ↦ by
      simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using
        normalizedRadialMellinStrip_shifted_fourier_inversion hd g.toFun g.radial g.real g.zero
          hR haless v)
  rwa [show (d : ℂ) / 2 - ((1 - σ) * ((d : ℝ) / 2) : ℝ) = σ * ((d : ℂ) / 2) by push_cast; ring,
    g.setIntegral_Iic_abs_logProfile hd hR, div_le_iff₀ g.L1norm_pos] at hupper

end RadialEigenfunction

/-- The lower-boundary majorant `h_λ(y) = λ log(πR²) + log|Γ(-iy/2)| - log|Γ(λ + iy/2)|`;
report (14). -/
def h_ℓ (ℓ R y : ℝ) : ℝ := ℓ * log (π * R ^ 2) + log ‖Complex.Gamma (-I * (y : ℂ) / 2)‖ -
    log ‖Complex.Gamma ((ℓ : ℂ) + I * (y : ℂ) / 2)‖

theorem lowerGammaBoundaryLog_continuousOn {ℓ : ℝ} (hℓ : 0 < ℓ) (R : ℝ) {S : Set ℝ}
    (hS : ∀ y ∈ S, y ≠ 0) : ContinuousOn (h_ℓ ℓ R) S := by
  have key : ∀ f : ℝ → ℂ, Continuous f → (∀ y ∈ S, ∀ m : ℕ, f y ≠ -(m : ℂ)) →
      ContinuousOn (fun y : ℝ ↦ log ‖Complex.Gamma (f y)‖) S := by
    intro f hf hpole
    have hcomp : ContinuousOn (fun y : ℝ ↦ Complex.Gamma (f y)) S := fun y hy ↦ by
      simpa [Function.comp_def] using
        ((Complex.continuousAt_Gamma (f y) (hpole y hy)).comp hf.continuousAt).continuousWithinAt
    exact hcomp.norm.log fun y hy ↦ norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero (hpole y hy))
  have hnumPole : ∀ y ∈ S, ∀ m : ℕ, -I * (y : ℂ) / 2 ≠ -(m : ℂ) := by
    intro y hy m hm
    have him := congrArg Complex.im hm
    norm_num at him
    exact hS y hy (by linarith)
  have hdenPole : ∀ y : ℝ, ∀ m : ℕ, (ℓ : ℂ) + I * (y : ℂ) / 2 ≠ -(m : ℂ) := by
    intro y m hm
    have hre := congrArg Complex.re hm
    norm_num at hre
    linarith [Nat.cast_nonneg (α := ℝ) m]
  change ContinuousOn (fun y : ℝ ↦ ℓ * log (π * R ^ 2) +
    log ‖Complex.Gamma (-I * (y : ℂ) / 2)‖ - log ‖Complex.Gamma ((ℓ : ℂ) + I * (y : ℂ) / 2)‖) S
  exact (continuousOn_const.add
      (key (fun y : ℝ ↦ -I * (y : ℂ) / 2) (by fun_prop) hnumPole)).sub
    (key (fun y : ℝ ↦ (ℓ : ℂ) + I * (y : ℂ) / 2) (by fun_prop) fun y _ ↦ hdenPole y)

theorem lowerGammaBoundaryLog_measurable {ℓ : ℝ} (hℓ : 0 < ℓ) (R : ℝ) : Measurable (h_ℓ ℓ R) :=
  measurable_of_continuousOn_compl_singleton (0 : ℝ)
    (lowerGammaBoundaryLog_continuousOn hℓ R fun y hy ↦ by simpa using hy)

/-- Lemma 3.2 of the report: `log |Z(y - iλ)| ≤ h_λ(y)` on the bottom edge of the strip. -/
theorem RadialEigenfunction.norm_Z_g_bottom_le_exp_h_ℓ {d : ℕ} {ς : ℤˣ} (hd : 0 < d)
    (g : RadialEigenfunction d ς) {R : ℝ} (hR : 0 < R) (y : ℝ) (hy : y ≠ 0) :
    ‖Z_g hd g.toFun R ((y : ℂ) - I * ((d : ℂ) / 2))‖ ≤ exp (h_ℓ ((d : ℝ) / 2) R y) := by
  simpa [h_ℓ] using normalizedRadialMellinStrip_bottom_norm_le_gamma hd g.toFun g.radial g.zero
    g.fourier_eq g.ne_zero R hR y hy

/-- The Poisson extension `H_σ(s) = ∫ P_σ(T) h_λ(s - λT) dT` of the lower-boundary
majorant; report (18). -/
def H_σ (ℓ R σ s : ℝ) : ℝ := ∫ T : ℝ, P_σ σ T * h_ℓ ℓ R (s - ℓ * T)

/-- The substitution `T = (s - y)/ℓ` in the strip Poisson integral; report (18). -/
theorem stripPoisson_integral_changeVariables {ℓ : ℝ} (hℓ : 0 < ℓ) (σ s : ℝ) (h : ℝ → ℝ) :
    (∫ y : ℝ, P_σ σ ((s - y) / ℓ) / ℓ * h y) = ∫ T : ℝ, P_σ σ T * h (s - ℓ * T) := by
  let G : ℝ → ℝ := fun y ↦ P_σ σ ((s - y) / ℓ) / ℓ * h y
  have hscale : (∫ T : ℝ, G (s - ℓ * T)) = ℓ⁻¹ * ∫ y : ℝ, G y := by
    have hraw := Measure.integral_comp_mul_left (fun u : ℝ ↦ G (s + u)) (-ℓ)
    rw [integral_add_left_eq_self G s] at hraw
    simpa [sub_eq_add_neg, neg_mul, inv_neg, abs_neg, abs_of_pos (inv_pos.mpr hℓ),
      smul_eq_mul] using hraw
  have hrewrite : (∫ T : ℝ, G (s - ℓ * T)) = ℓ⁻¹ * ∫ T : ℝ, P_σ σ T * h (s - ℓ * T) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun T ↦ ?_)
    have hargument : (s - (s - ℓ * T)) / ℓ = T := by
      field_simp
      ring
    change P_σ σ ((s - (s - ℓ * T)) / ℓ) / ℓ * h (s - ℓ * T) = ℓ⁻¹ * (P_σ σ T * h (s - ℓ * T))
    rw [hargument]
    ring
  change (∫ y : ℝ, G y) = ∫ T : ℝ, P_σ σ T * h (s - ℓ * T)
  exact mul_left_cancel₀ (inv_ne_zero hℓ.ne') (hscale.symm.trans hrewrite)

theorem norm_integerGammaFactor (j : ℕ) (y : ℝ) :
    ‖(j : ℂ) + I * (y : ℂ) / 2‖ = √((j : ℝ) ^ 2 + (y / 2) ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp
  ring

theorem integerGammaFactor_ne_zero (j : ℕ) {y : ℝ} (hy : y ≠ 0) :
    (j : ℂ) + I * (y : ℂ) / 2 ≠ 0 := fun hz ↦ by
  have him := congrArg Complex.im hz
  norm_num at him
  exact hy (by linarith)

theorem gamma_imaginary_ne_zero {y : ℝ} (hy : y ≠ 0) : Complex.Gamma (I * (y : ℂ) / 2) ≠ 0 := by
  refine Complex.Gamma_ne_zero fun j hj ↦ ?_
  have him := congrArg Complex.im hj
  norm_num at him
  exact hy (by linarith)

theorem norm_gamma_neg_imaginary (y : ℝ) :
    ‖Complex.Gamma (-I * (y : ℂ) / 2)‖ = ‖Complex.Gamma (I * (y : ℂ) / 2)‖ := by
  rw [show -I * (y : ℂ) / 2 = starRingEnd ℂ (I * (y : ℂ) / 2) by
      simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.conj_ofNat],
    Complex.Gamma_conj, RCLike.norm_conj]

/-- Even dimensions: the gamma recurrence (7) turns `h_n` into a Riemann sum; report, proof of
Lemma 3.3. -/
theorem lowerGammaBoundaryLog_integer (k : ℕ) (R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    h_ℓ (k : ℝ) R y = (k : ℝ) * log (π * R ^ 2) -
      ∑ j ∈ Finset.range k, log (√((j : ℝ) ^ 2 + (y / 2) ^ 2)) := by
  have hbase : ‖Complex.Gamma (I * (y : ℂ) / 2)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (gamma_imaginary_ne_zero hy)
  have hproductnorm : ‖∏ j ∈ Finset.range k, ((j : ℂ) + I * (y : ℂ) / 2)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Finset.prod_ne_zero_iff.mpr fun j _ ↦ integerGammaFactor_ne_zero j hy)
  have hlogproduct : log ‖∏ j ∈ Finset.range k, ((j : ℂ) + I * (y : ℂ) / 2)‖ =
      ∑ j ∈ Finset.range k, log (√((j : ℝ) ^ 2 + (y / 2) ^ 2)) := by
    rw [Complex.norm_prod, Real.log_prod]
    · exact Finset.sum_congr rfl fun j _ ↦ by rw [norm_integerGammaFactor]
    · exact fun j _ ↦ norm_ne_zero_iff.mpr (integerGammaFactor_ne_zero j hy)
  unfold h_ℓ
  rw [Complex.ofReal_natCast, integer_gamma_product k hy, norm_mul,
    Real.log_mul hbase hproductnorm, norm_gamma_neg_imaginary, hlogproduct]
  ring

theorem lower_sqrtFactor_ge_abs_half (c y : ℝ) : |y| / 2 ≤ √(c ^ 2 + (y / 2) ^ 2) := by
  refine (Real.le_sqrt (by positivity) (by positivity)).2 ?_
  nlinarith [sq_nonneg c, sq_abs y]

theorem lowerGammaBoundaryLog_integer_log_tail (k : ℕ) {R y : ℝ} (hR : 0 < R) (hy : y ≠ 0) :
    h_ℓ (k : ℝ) R y ≤ (k : ℝ) * log (2 * π * R ^ 2 / |y|) := by
  have hyhalf : 0 < |y| / 2 := by positivity
  have hsum : (k : ℝ) * log (|y| / 2) ≤
      ∑ j ∈ Finset.range k, log (√((j : ℝ) ^ 2 + (y / 2) ^ 2)) := by
    rw [show (k : ℝ) * log (|y| / 2) = ∑ _j ∈ Finset.range k, log (|y| / 2) by simp]
    exact Finset.sum_le_sum fun j _ ↦
      Real.log_le_log hyhalf (lower_sqrtFactor_ge_abs_half (j : ℝ) y)
  have hlogratio : log (π * R ^ 2) - log (|y| / 2) = log (2 * π * R ^ 2 / |y|) := by
    rw [← Real.log_div (mul_ne_zero pi_ne_zero (pow_ne_zero 2 hR.ne')) hyhalf.ne']
    congr 1
    field_simp [abs_ne_zero.mpr hy]
  rw [lowerGammaBoundaryLog_integer k R hy, ← hlogratio]
  nlinarith [hsum]

theorem lower_abs_log_sqrtFactor_le {c y : ℝ} (hc : 0 ≤ c) (hy : 0 < y) :
    |log (√(c ^ 2 + (y / 2) ^ 2))| ≤ c + y / 2 + |log (y / 2)| := by
  have ht : 0 < y / 2 := by positivity
  have hinside : 0 < c ^ 2 + (y / 2) ^ 2 := by positivity
  have hsqrt : 0 < √(c ^ 2 + (y / 2) ^ 2) := Real.sqrt_pos.2 hinside
  have hlower : y / 2 ≤ √(c ^ 2 + (y / 2) ^ 2) := by
    refine (Real.le_sqrt ht.le hinside.le).2 ?_
    nlinarith [sq_nonneg c]
  have hupper : √(c ^ 2 + (y / 2) ^ 2) ≤ c + y / 2 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [mul_nonneg hc ht.le]⟩
  rcases le_total 1 (√(c ^ 2 + (y / 2) ^ 2)) with hlarge | hsmall
  · rw [abs_of_nonneg (Real.log_nonneg hlarge)]
    linarith [Real.log_le_sub_one_of_pos hsqrt, abs_nonneg (log (y / 2))]
  · rw [abs_of_nonpos (Real.log_nonpos hsqrt.le hsmall)]
    have hnonneg : 0 ≤ c + y / 2 := by positivity
    linarith [Real.log_le_log ht hlower, neg_le_abs (log (y / 2))]

theorem lower_exp_log_sqrtFactor_integrableOn_Ioi {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) :
    IntegrableOn (fun y : ℝ ↦ exp ((-a) * y) * log (√(c ^ 2 + (y / 2) ^ 2))) (Ioi (0 : ℝ)) := by
  have hlinear : IntegrableOn (fun y : ℝ ↦ y * exp ((-a) * y)) (Ioi (0 : ℝ)) := by
    simpa [rpow_one] using integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (1 : ℝ))
      (b := a) (by norm_num) (by norm_num) ha
  have hmajorant : IntegrableOn (fun y : ℝ ↦ c * exp ((-a) * y) +
      (1 / 2 : ℝ) * (y * exp ((-a) * y)) + exp ((-a) * y) * |log (y / 2)|) (Ioi (0 : ℝ)) :=
    (((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) 0).const_mul c).add
      (hlinear.const_mul (1 / 2))).add (integrableOn_exp_neg_mul_mul_abs_log_div_two_Ioi ha)
  have hcontinuous : ContinuousOn (fun y : ℝ ↦ exp ((-a) * y) * log (√(c ^ 2 + (y / 2) ^ 2)))
      (Ioi (0 : ℝ)) := by
    refine ContinuousOn.mul (by fun_prop) (ContinuousOn.log (by fun_prop) fun y hy ↦ ?_)
    refine (Real.sqrt_pos.2 ?_).ne'
    have ht : 0 < y / 2 := half_pos (mem_Ioi.mp hy)
    positivity
  refine hmajorant.mono' (hcontinuous.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  calc ‖exp ((-a) * y) * log (√(c ^ 2 + (y / 2) ^ 2))‖
      = exp ((-a) * y) * |log (√(c ^ 2 + (y / 2) ^ 2))| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
    _ ≤ exp ((-a) * y) * (c + y / 2 + |log (y / 2)|) :=
        mul_le_mul_of_nonneg_left (lower_abs_log_sqrtFactor_le hc (mem_Ioi.mp hy))
          (exp_pos _).le
    _ = c * exp ((-a) * y) + (1 / 2 : ℝ) * (y * exp ((-a) * y)) +
        exp ((-a) * y) * |log (y / 2)| := by ring

theorem lower_exp_log_sqrtFactor_integrable {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) :
    Integrable (fun y : ℝ ↦ exp ((-a) * |y|) * log (√(c ^ 2 + (y / 2) ^ 2))) := by
  refine integrable_of_even (fun y ↦ by rw [abs_neg, show (-y / 2) ^ 2 = (y / 2) ^ 2 by ring]) ?_
  refine (lower_exp_log_sqrtFactor_integrableOn_Ioi ha hc).congr_fun (fun y hy ↦ ?_)
    measurableSet_Ioi
  simp only [abs_of_pos (mem_Ioi.mp hy)]

theorem lowerGammaBoundaryLog_integer_exp_integrable {a : ℝ} (ha : 0 < a) (k : ℕ) (R : ℝ) :
    Integrable (fun y : ℝ ↦ exp ((-a) * |y|) * h_ℓ (k : ℝ) R y) := by
  have hconstant : Integrable (fun y : ℝ ↦ ((k : ℝ) * log (π * R ^ 2)) * exp ((-a) * |y|)) :=
    (integrable_exp_neg_mul_abs ha).const_mul ((k : ℝ) * log (π * R ^ 2))
  have hsum : Integrable (fun y : ℝ ↦ ∑ j ∈ Finset.range k,
      exp ((-a) * |y|) * log (√((j : ℝ) ^ 2 + (y / 2) ^ 2))) :=
    integrable_finsetSum (Finset.range k)
      fun j _ ↦ lower_exp_log_sqrtFactor_integrable ha (Nat.cast_nonneg j)
  have hmodel : Integrable (fun y : ℝ ↦ exp ((-a) * |y|) * ((k : ℝ) * log (π * R ^ 2) -
      ∑ j ∈ Finset.range k, log (√((j : ℝ) ^ 2 + (y / 2) ^ 2)))) := by
    simpa only [mul_sub, Finset.mul_sum, mul_comm] using! hconstant.sub hsum
  refine hmodel.congr ?_
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with y hy
  rw [lowerGammaBoundaryLog_integer k R hy]

/-- Integrability of `K̃_λ(z, ·) h_λ` on one half-line `S`, given the kernel bound with sign `u`
(`u = 1` on `(0, ∞)`, `u = -1` on `(-∞, 0)`). -/
private theorem integrableOn_K'_ℓ_mul_h_ℓ {ℓ R : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hgammaabs : Integrable fun y : ℝ ↦ exp (-(π / (2 * ℓ)) * |y|) * |h_ℓ ℓ R y|)
    (S : Set ℝ) (u : ℝ) (hS : MeasurableSet S) (hne : ∀ y ∈ S, y ≠ 0)
    (hcont : ContinuousOn (fun y : ℝ ↦ K'_ℓ ℓ z y) S)
    (hbound : ∀ y ∈ S, ‖K'_ℓ ℓ z y‖ ≤ exp (u * (π * (z.re - y) / (2 * ℓ))) /
      (2 * ℓ * sin (π * (z.im + ℓ) / (2 * ℓ))))
    (habs : ∀ y ∈ S, -(u * (π / (2 * ℓ))) * y = -(π / (2 * ℓ)) * |y|) :
    IntegrableOn (fun y : ℝ ↦ K'_ℓ ℓ z y * (h_ℓ ℓ R y : ℂ)) S := by
  have hcast : ContinuousOn (fun y : ℝ ↦ (h_ℓ ℓ R y : ℂ)) S := by
    simpa [Function.comp_def] using Complex.continuous_ofReal.comp_continuousOn
      (lowerGammaBoundaryLog_continuousOn hℓ R hne)
  refine (hgammaabs.integrableOn.const_mul (exp (u * (π * z.re / (2 * ℓ))) /
    (2 * ℓ * sin (π * (z.im + ℓ) / (2 * ℓ))))).mono'
    ((hcont.mul hcast).aestronglyMeasurable hS) ?_
  filter_upwards [ae_restrict_mem hS] with y hy
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc ‖K'_ℓ ℓ z y‖ * |h_ℓ ℓ R y| ≤
        exp (u * (π * (z.re - y) / (2 * ℓ))) /
          (2 * ℓ * sin (π * (z.im + ℓ) / (2 * ℓ))) * |h_ℓ ℓ R y| :=
        mul_le_mul_of_nonneg_right (hbound y hy) (abs_nonneg _)
    _ = _ := by
        rw [show u * (π * (z.re - y) / (2 * ℓ)) =
          u * (π * z.re / (2 * ℓ)) + -(u * (π / (2 * ℓ))) * y by ring, exp_add, habs y hy]
        ring

/-- The regularized strip kernel times the boundary majorant is integrable on the boundary
line; report, proof of Lemma 3.2. -/
theorem lowerStripGammaOuter_integrable_of_exp_integrable {ℓ R : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ)
    (hgamma : Integrable (fun y : ℝ ↦ exp (-(π / (2 * ℓ)) * |y|) * h_ℓ ℓ R y)) :
    Integrable (fun y : ℝ ↦ K'_ℓ ℓ z y * (h_ℓ ℓ R y : ℂ)) := by
  have hgammaabs : Integrable (fun y : ℝ ↦ exp (-(π / (2 * ℓ)) * |y|) * |h_ℓ ℓ R y|) := by
    simpa [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)] using hgamma.norm
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  exact ⟨integrableOn_K'_ℓ_mul_h_ℓ hℓ hgammaabs _ (-1) measurableSet_Iio
      (fun y hy ↦ (mem_Iio.mp hy).ne)
      (stripRegularizedHolomorphicPoissonKernel_continuousOn_Iio hℓ hz)
      (fun y hy ↦ by
        simpa using norm_stripRegularizedHolomorphicPoissonKernel_of_neg hℓ hz (mem_Iio.mp hy))
      (fun y hy ↦ by rw [abs_of_neg (mem_Iio.mp hy)]; ring),
    integrableOn_K'_ℓ_mul_h_ℓ hℓ hgammaabs _ 1 measurableSet_Ioi (fun y hy ↦ (mem_Ioi.mp hy).ne')
      (stripRegularizedHolomorphicPoissonKernel_continuousOn_Ioi hℓ hz)
      (fun y hy ↦ by
        simpa using
          norm_stripRegularizedHolomorphicPoissonKernel_of_nonneg hℓ hz (mem_Ioi.mp hy).le)
      (fun y hy ↦ by rw [abs_of_pos (mem_Ioi.mp hy)]; ring)⟩

theorem norm_halfIntegerGammaFactor (j : ℕ) (y : ℝ) :
    ‖(j : ℂ) + (1 / 2 : ℂ) + I * (y : ℂ) / 2‖ = √(((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp
  ring

theorem halfIntegerGammaFactor_ne_zero (j : ℕ) (y : ℝ) :
    (j : ℂ) + (1 / 2 : ℂ) + I * (y : ℂ) / 2 ≠ 0 := fun hz ↦ by
  have hre := congrArg Complex.re hz
  norm_num at hre
  linarith [Nat.cast_nonneg (α := ℝ) j]

/-- Odd dimensions: the gamma identities (7) split `h_λ` into a midpoint Riemann sum and a
boundary correction; report, proof of Lemma 3.3. -/
theorem lowerGammaBoundaryLog_halfInteger_factorized (k : ℕ) (R : ℝ) {y : ℝ} (_hy : y ≠ 0) :
    h_ℓ ((k : ℝ) + 1 / 2) R y = ((k : ℝ) + 1 / 2) * log (π * R ^ 2) -
      ∑ j ∈ Finset.range k, log (√(((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2)) +
      (log ‖Complex.Gamma (I * (y : ℂ) / 2)‖ -
        log ‖Complex.Gamma ((1 / 2 : ℂ) + I * (y : ℂ) / 2)‖) := by
  have hbasenorm : ‖Complex.Gamma ((1 / 2 : ℂ) + I * (y : ℂ) / 2)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
  have hproductnorm : ‖∏ j ∈ Finset.range k, ((j : ℂ) + (1 / 2 : ℂ) + I * (y : ℂ) / 2)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Finset.prod_ne_zero_iff.mpr fun j _ ↦ halfIntegerGammaFactor_ne_zero j y)
  have hlogproduct : log ‖∏ j ∈ Finset.range k, ((j : ℂ) + (1 / 2 : ℂ) + I * (y : ℂ) / 2)‖ =
      ∑ j ∈ Finset.range k, log (√(((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2)) := by
    rw [Complex.norm_prod, Real.log_prod]
    · exact Finset.sum_congr rfl fun j _ ↦ by rw [norm_halfIntegerGammaFactor]
    · exact fun j _ ↦ norm_ne_zero_iff.mpr (halfIntegerGammaFactor_ne_zero j y)
  unfold h_ℓ
  rw [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat, half_integer_gamma_product k y, norm_mul,
    Real.log_mul hbasenorm hproductnorm,
    norm_gamma_neg_imaginary, hlogproduct]
  ring

end

noncomputable section
open Filter MeasureTheory Real Set
open scoped FourierTransform Interval RealInnerProductSpace Topology

/-- Half of a natural number is either an integer or an integer plus `1 / 2`. -/
theorem natCast_div_two_cases (d : ℕ) :
    (∃ k : ℕ, (d : ℝ) / 2 = k) ∨ ∃ k : ℕ, (d : ℝ) / 2 = (k : ℝ) + 1 / 2 := by
  rcases d.even_or_odd with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact Or.inl ⟨k, by push_cast; ring⟩
  · exact Or.inr ⟨k, by push_cast; ring⟩

theorem lowerGammaBoundaryLog_halfInteger (k : ℕ) (R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    h_ℓ ((k : ℝ) + 1 / 2) R y = ((k : ℝ) + 1 / 2) * log (π * R ^ 2) -
        ∑ j ∈ Finset.range k, log (√(((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2)) +
        1 / 2 * log (coth (π * |y| / 2) / (|y| / 2)) := by
  rw [lowerGammaBoundaryLog_halfInteger_factorized k R hy]
  congr 1
  simpa [abs_div, mul_div_assoc] using
    Complex.log_norm_Gamma_I_mul_sub_log_norm_Gamma_one_half_add_I_mul
      (x := y / 2) (div_ne_zero hy two_ne_zero)

theorem lowerGammaBoundaryLog_halfInteger_log_tail (k : ℕ) {R y : ℝ} (hR : 0 < R) (hy : y ≠ 0) :
    h_ℓ ((k : ℝ) + 1 / 2) R y ≤ ((k : ℝ) + 1 / 2) * log (2 * π * R ^ 2 / |y|) +
      1 / 2 * log (coth (π * |y| / 2)) := by
  have hyhalf : 0 < |y| / 2 := by positivity
  have hsum : (k : ℝ) * log (|y| / 2) ≤
      ∑ j ∈ Finset.range k, log (√(((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2)) := by
    calc (k : ℝ) * log (|y| / 2) = ∑ _j ∈ Finset.range k, log (|y| / 2) := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _ ↦
          Real.log_le_log hyhalf (lower_sqrtFactor_ge_abs_half ((j : ℝ) + 1 / 2) y)
  have hlogratio : log (π * R ^ 2) - log (|y| / 2) = log (2 * π * R ^ 2 / |y|) := by
    rw [← Real.log_div (mul_ne_zero Real.pi_ne_zero (pow_ne_zero 2 hR.ne')) hyhalf.ne']
    congr 1
    field_simp [abs_ne_zero.mpr hy]
  rw [lowerGammaBoundaryLog_halfInteger k R hy,
    Real.log_div (coth_pos (by positivity)).ne' hyhalf.ne', ← hlogratio]
  linarith

theorem lowerGammaBoundaryLog_dimension_log_tail {d : ℕ} (_hd : 0 < d) {R y : ℝ} (hR : 0 < R)
    (hy : y ≠ 0) :
    h_ℓ ((d : ℝ) / 2) R y ≤ (d : ℝ) / 2 * log (2 * π * R ^ 2 / |y|) +
      1 / 2 * log (coth (π * |y| / 2)) := by
  have hcoth : 0 ≤ log (coth (π * |y| / 2)) := log_coth_nonneg (by positivity)
  obtain ⟨k, hk⟩ | ⟨k, hk⟩ := natCast_div_two_cases d <;> rw [hk]
  · linarith [lowerGammaBoundaryLog_integer_log_tail k hR hy]
  · exact lowerGammaBoundaryLog_halfInteger_log_tail k hR hy

theorem lowerGammaBoundaryLog_dimension_scaled_log_tail {d : ℕ} (hd : 0 < d) {c Y : ℝ}
    (hc : 0 < c) (hY : Y ≠ 0) :
    h_ℓ ((d : ℝ) / 2) (c * √d) ((d : ℝ) / 2 * Y) ≤ (d : ℝ) / 2 * log (4 * π * c ^ 2 / |Y|) +
      1 / 2 * log (coth (π * |(d : ℝ) / 2 * Y| / 2)) := by
  have hdreal : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hℓ : 0 < (d : ℝ) / 2 := half_pos hdreal
  have hratio : 2 * π * (c * √d) ^ 2 / |(d : ℝ) / 2 * Y| = 4 * π * c ^ 2 / |Y| := by
    rw [abs_mul, abs_of_pos hℓ, mul_pow, Real.sq_sqrt hdreal.le]
    field_simp [hℓ.ne', abs_ne_zero.mpr hY, hdreal.ne']
    ring
  have htail := lowerGammaBoundaryLog_dimension_log_tail hd (mul_pos hc (Real.sqrt_pos.2 hdreal))
    (mul_ne_zero hℓ.ne' hY)
  rwa [hratio] at htail

theorem lowerGammaBoundaryLog_dimension_scaled_log_tail_uniform {d : ℕ} (hd : 2 ≤ d) {c Y : ℝ}
    (hc : 0 < c) (hY : Y ≠ 0) :
    h_ℓ ((d : ℝ) / 2) (c * √d) ((d : ℝ) / 2 * Y) ≤ (d : ℝ) / 2 * log (4 * π * c ^ 2 / |Y|) +
      1 / 2 * log (coth (π * |Y| / 2)) := by
  have hdpos : 0 < d := by omega
  have hℓ : 1 ≤ (d : ℝ) / 2 := (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by exact_mod_cast hd)
  have hcompare : π * |Y| / 2 ≤ π * |(d : ℝ) / 2 * Y| / 2 := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (d : ℝ) / 2)]
    nlinarith [mul_nonneg Real.pi_pos.le (abs_nonneg Y)]
  have hcoth := antitoneOn_log_coth (by positivity : (0 : ℝ) < π * |Y| / 2)
    (by positivity : (0 : ℝ) < π * |(d : ℝ) / 2 * Y| / 2) hcompare
  linarith [lowerGammaBoundaryLog_dimension_scaled_log_tail hdpos hc hY]

/-- The positive part `(log (A / |y|))⁺` is integrable for every `A > 0`. -/
theorem lower_positiveLogRatio_integrable {A : ℝ} (hA : 0 < A) :
    Integrable fun y : ℝ ↦ max (log (A / |y|)) 0 := by
  have hB : (0 : ℝ) ≤ max 1 A := le_trans zero_le_one (le_max_left 1 A)
  have hmaj : Integrable fun y : ℝ ↦ exp (max 1 A) * (|log A| * exp ((-1 : ℝ) * |y|) +
      exp ((-1 : ℝ) * |y|) * |log (|y|)|) :=
    (((integrable_exp_neg_mul_abs (by norm_num : (0 : ℝ) < 1)).const_mul |log A|).add
      (integrable_exp_neg_mul_abs_mul_abs_log_abs (by norm_num : (0 : ℝ) < 1))).const_mul
        (exp (max 1 A))
  refine hmaj.mono'
    (by fun_prop : Measurable fun y : ℝ ↦ max (log (A / |y|)) 0).aestronglyMeasurable ?_
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  rcases eq_or_ne y 0 with rfl | hy
  · simp only [abs_zero, div_zero, log_zero, max_self, mul_zero, exp_zero, mul_one, add_zero]
    positivity
  rcases le_or_gt (|y|) (max 1 A) with hsmall | hlarge
  · have hpoly : (0 : ℝ) ≤ |log A| + |log (|y|)| := by positivity
    have habs : log (A / |y|) ≤ |log A| + |log (|y|)| := by
      rw [Real.log_div hA.ne' (abs_ne_zero.mpr hy)]
      linarith [le_abs_self (log A), neg_le_abs (log |y|)]
    have hfactor : 1 ≤ exp (max 1 A) * exp ((-1 : ℝ) * |y|) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.2 (by linarith)
    calc max (log (A / |y|)) 0 ≤ |log A| + |log (|y|)| := max_le habs hpoly
      _ ≤ exp (max 1 A) * exp ((-1 : ℝ) * |y|) * (|log A| + |log (|y|)|) :=
          le_mul_of_one_le_left hpoly hfactor
      _ = exp (max 1 A) * (|log A| * exp ((-1 : ℝ) * |y|) +
            exp ((-1 : ℝ) * |y|) * |log (|y|)|) := by ring
  · rw [max_eq_right (Real.log_nonpos (by positivity)
      ((div_le_one (abs_pos.mpr hy)).2 ((le_max_right 1 A).trans hlarge.le)))]
    positivity

/-- Positive part of the boundary log-profile at radius `c√d`, rescaled by `ℓ = d / 2`. -/
def lowerGammaScaledPositivePart (d : ℕ) (c Y : ℝ) : ℝ :=
  max (h_ℓ ((d : ℝ) / 2) (c * √d) ((d : ℝ) / 2 * Y)) 0

theorem lowerGammaScaledPositivePart_le {d : ℕ} (hd : 2 ≤ d) {c Y : ℝ} (hc : 0 < c) (hY : Y ≠ 0) :
    lowerGammaScaledPositivePart d c Y ≤ (d : ℝ) / 2 * max (log (4 * π * c ^ 2 / |Y|)) 0 +
      1 / 2 * log (coth (π * |Y| / 2)) := by
  have hcoth : 0 ≤ log (coth (π * |Y| / 2)) := log_coth_nonneg (by positivity)
  have hlog : (d : ℝ) / 2 * log (4 * π * c ^ 2 / |Y|) ≤
      (d : ℝ) / 2 * max (log (4 * π * c ^ 2 / |Y|)) 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
  unfold lowerGammaScaledPositivePart
  refine max_le ?_ (by positivity)
  linarith [lowerGammaBoundaryLog_dimension_scaled_log_tail_uniform hd hc hY]

theorem lowerGammaScaledPositivePart_integrable {d : ℕ} (hd : 2 ≤ d) {c : ℝ} (hc : 0 < c) :
    Integrable (lowerGammaScaledPositivePart d c) := by
  have hdpos : 0 < d := by omega
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  refine (((lower_positiveLogRatio_integrable (by positivity : (0 : ℝ) < 4 * π * c ^ 2)).const_mul
    ((d : ℝ) / 2)).add (integrable_log_coth_pi_mul_abs_div_two.const_mul (1 / 2))).mono'
    ((((lowerGammaBoundaryLog_measurable hℓ (c * √d)).comp
      (by fun_prop : Measurable fun Y : ℝ ↦ (d : ℝ) / 2 * Y)).max
        measurable_const).aestronglyMeasurable) ?_
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with Y hY
  rw [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ lowerGammaScaledPositivePart d c Y from
    le_max_right _ _)]
  exact lowerGammaScaledPositivePart_le hd hc hY

theorem lowerGammaScaledPositivePart_integral_le {d : ℕ} (hd : 2 ≤ d) {c : ℝ} (hc : 0 < c) :
    (∫ Y : ℝ, lowerGammaScaledPositivePart d c Y) ≤
      (d : ℝ) / 2 * (∫ Y : ℝ, max (log (4 * π * c ^ 2 / |Y|)) 0) +
        1 / 2 * ∫ Y : ℝ, log (coth (π * |Y| / 2)) := by
  have hpositive := lower_positiveLogRatio_integrable (by positivity : (0 : ℝ) < 4 * π * c ^ 2)
  have hcoth := integrable_log_coth_pi_mul_abs_div_two
  calc (∫ Y : ℝ, lowerGammaScaledPositivePart d c Y)
      ≤ ∫ Y : ℝ, ((d : ℝ) / 2 * max (log (4 * π * c ^ 2 / |Y|)) 0 +
          1 / 2 * log (coth (π * |Y| / 2))) := by
        refine integral_mono_ae (lowerGammaScaledPositivePart_integrable hd hc)
          ((hpositive.const_mul _).add (hcoth.const_mul _)) ?_
        filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with Y hY
        exact lowerGammaScaledPositivePart_le hd hc hY
    _ = _ := by
        rw [integral_add (hpositive.const_mul _) (hcoth.const_mul _), integral_const_mul,
          integral_const_mul]

theorem lowerGammaBoundaryLog_dimension_scaled_nonpos_of_large {d : ℕ} (hd : 2 ≤ d) {c Y : ℝ}
    (hc : 0 < c) (hlarge : max 1 (8 * π * c ^ 2) ≤ |Y|) :
    h_ℓ ((d : ℝ) / 2) (c * √d) ((d : ℝ) / 2 * Y) ≤ 0 := by
  have hyone : 1 ≤ |Y| := (le_max_left 1 _).trans hlarge
  have hY : Y ≠ 0 := by rintro rfl; norm_num at hyone
  have hlogtwo : (1 / 2 : ℝ) ≤ log 2 := by linarith [Real.log_two_gt_d9]
  have hℓ : 1 ≤ (d : ℝ) / 2 := (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by exact_mod_cast hd)
  have hlogratio : log (4 * π * c ^ 2 / |Y|) ≤ -log 2 := by
    have hhalf : -log 2 = log (1 / 2 : ℝ) := by rw [one_div, Real.log_inv]
    rw [hhalf]
    refine Real.log_le_log (by positivity) ((div_le_iff₀ (by linarith)).2 ?_)
    linarith [(le_max_right 1 (8 * π * c ^ 2)).trans hlarge]
  have hpiabs : 3 ≤ π * |Y| := by
    nlinarith [Real.pi_gt_three, mul_nonneg (by linarith [Real.pi_gt_three] : (0 : ℝ) ≤ π - 3)
      (sub_nonneg.mpr hyone)]
  have hcorrection : 1 / 2 * log (coth (π * |Y| / 2)) ≤ 1 / 2 := by
    have hcoth := log_coth_le_four_mul_exp_neg_two_mul (by linarith : (1 : ℝ) ≤ π * |Y| / 2)
    have hexp : exp (-2 * (π * |Y| / 2)) ≤ 1 / 4 := by
      calc exp (-2 * (π * |Y| / 2)) ≤ exp (-3 : ℝ) := Real.exp_le_exp.2 (by linarith)
        _ = (exp 3)⁻¹ := Real.exp_neg 3
        _ ≤ 1 / 4 := by
            rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
            nlinarith [Real.add_one_le_exp (3 : ℝ)]
    linarith
  have hmain : (d : ℝ) / 2 * log (4 * π * c ^ 2 / |Y|) ≤ -log 2 := by
    linarith [mul_le_mul_of_nonneg_left hlogratio (by positivity : (0 : ℝ) ≤ (d : ℝ) / 2),
      mul_nonneg (sub_nonneg.mpr hℓ) (by linarith : (0 : ℝ) ≤ log 2)]
  linarith [lowerGammaBoundaryLog_dimension_scaled_log_tail_uniform hd hc hY]

theorem lowerGammaScaledPositivePart_support {d : ℕ} (hd : 2 ≤ d) {c : ℝ} (hc : 0 < c) :
    Function.support (lowerGammaScaledPositivePart d c) ⊆
      Icc (-(max 1 (8 * π * c ^ 2))) (max 1 (8 * π * c ^ 2)) := by
  intro Y hY
  have hsmall : |Y| < max 1 (8 * π * c ^ 2) := by
    by_contra! hnot
    exact hY (max_eq_right (lowerGammaBoundaryLog_dimension_scaled_nonpos_of_large hd hc hnot))
  exact abs_le.1 hsmall.le

theorem exists_lowerGammaScaledPositivePart_uniform_bound {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d → Function.support (lowerGammaScaledPositivePart d c) ⊆
            Icc (-C) C ∧
          (∫ Y : ℝ, lowerGammaScaledPositivePart d c Y) ≤ C * ((d : ℝ) / 2) := by
  obtain ⟨J, K, hK, hbound⟩ : ∃ J K : ℝ, 0 ≤ K ∧ ∀ d : ℕ, 2 ≤ d →
      (∫ Y : ℝ, lowerGammaScaledPositivePart d c Y) ≤ (d : ℝ) / 2 * J + 1 / 2 * K := by
    refine ⟨_, _, ?_, fun d hd ↦ lowerGammaScaledPositivePart_integral_le hd hc⟩
    refine integral_nonneg fun Y ↦ ?_
    rcases eq_or_ne Y 0 with rfl | hY
    · simp [Real.coth]
    · exact log_coth_nonneg (by positivity)
  refine ⟨max (max 1 (8 * π * c ^ 2)) (J + 1 / 2 * K), lt_of_lt_of_le zero_lt_one
    ((le_max_left 1 _).trans (le_max_left _ _)), fun d hd ↦ ⟨fun Y hY ↦ ?_, ?_⟩⟩
  · exact Icc_subset_Icc (neg_le_neg (le_max_left _ _)) (le_max_left _ _)
      (lowerGammaScaledPositivePart_support hd hc hY)
  · have hℓ : 1 ≤ (d : ℝ) / 2 := (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by exact_mod_cast hd)
    have h2 : (d : ℝ) / 2 * J + 1 / 2 * K ≤ (d : ℝ) / 2 * (J + 1 / 2 * K) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hℓ) hK]
    linarith [hbound d hd, mul_le_mul_of_nonneg_left
      (le_max_right (max 1 (8 * π * c ^ 2)) (J + 1 / 2 * K)) (by linarith : (0 : ℝ) ≤ (d : ℝ) / 2)]

theorem lowerGammaBoundaryLog_dimension_neg {d : ℕ} (R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    h_ℓ ((d : ℝ) / 2) R (-y) = h_ℓ ((d : ℝ) / 2) R y := by
  obtain ⟨k, hk⟩ | ⟨k, hk⟩ := natCast_div_two_cases d <;> rw [hk]
  · rw [lowerGammaBoundaryLog_integer k R (neg_ne_zero.mpr hy),
      lowerGammaBoundaryLog_integer k R hy]
    simp [div_pow]
  · rw [lowerGammaBoundaryLog_halfInteger k R (neg_ne_zero.mpr hy),
      lowerGammaBoundaryLog_halfInteger k R hy]
    simp [div_pow]

/-- The factors `log √(c² + (y/2)²)` of the boundary profile increase in `y > 0`. -/
theorem lower_log_sqrtFactor_mono (c : ℝ) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    log (√(c ^ 2 + (x / 2) ^ 2)) ≤ log (√(c ^ 2 + (y / 2) ^ 2)) :=
  Real.log_le_log (Real.sqrt_pos.2 (by positivity)) (Real.sqrt_le_sqrt (by nlinarith))

theorem lowerGammaBoundaryLog_integer_antitoneOn (k : ℕ) (R : ℝ) :
    AntitoneOn (h_ℓ (k : ℝ) R) (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  have hx' : 0 < x := hx
  have hy' : 0 < y := hy
  rw [lowerGammaBoundaryLog_integer k R hy'.ne', lowerGammaBoundaryLog_integer k R hx'.ne']
  linarith [Finset.sum_le_sum fun j (_ : j ∈ Finset.range k) ↦
    lower_log_sqrtFactor_mono (j : ℝ) hx' hxy]

theorem lowerGammaBoundaryLog_halfInteger_antitoneOn (k : ℕ) (R : ℝ) :
    AntitoneOn (h_ℓ ((k : ℝ) + 1 / 2) R) (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  have hx' : 0 < x := hx
  have hy' : 0 < y := hy
  have hratio : coth (π * y / 2) / (y / 2) ≤ coth (π * x / 2) / (x / 2) :=
    (div_le_div_of_nonneg_right (antitoneOn_coth (by positivity : (0 : ℝ) < π * x / 2)
      (by positivity : (0 : ℝ) < π * y / 2) (by gcongr)) (half_pos hy').le).trans
      (div_le_div_of_nonneg_left (coth_pos (by positivity)).le (half_pos hx') (by linarith))
  have hcoth := Real.log_le_log (div_pos (coth_pos (by positivity)) (half_pos hy')) hratio
  rw [lowerGammaBoundaryLog_halfInteger k R hy'.ne', lowerGammaBoundaryLog_halfInteger k R hx'.ne',
    abs_of_pos hx', abs_of_pos hy']
  linarith [Finset.sum_le_sum fun j (_ : j ∈ Finset.range k) ↦
    lower_log_sqrtFactor_mono ((j : ℝ) + 1 / 2) hx' hxy]

theorem lowerGammaBoundaryLog_dimension_antitoneOn {d : ℕ} (R : ℝ) :
    AntitoneOn (h_ℓ ((d : ℝ) / 2) R) (Ioi (0 : ℝ)) := by
  obtain ⟨k, hk⟩ | ⟨k, hk⟩ := natCast_div_two_cases d <;> rw [hk]
  · exact lowerGammaBoundaryLog_integer_antitoneOn k R
  · exact lowerGammaBoundaryLog_halfInteger_antitoneOn k R

/-- An even function that is antitone on `[0, ∞)` and compactly supported has intervals
`(-r, r) ⊆ {f > t} ⊆ [-r, r]` as superlevel sets. -/
theorem even_antitone_superlevel_interval {f : ℝ → ℝ} {B t : ℝ} (heven : ∀ x : ℝ, f (-x) = f x)
    (hanti : AntitoneOn f (Ici (0 : ℝ))) (hsupport : Function.support f ⊆ Icc (-B) B)
    (ht : 0 < t) :
    ∃ r : ℝ, 0 ≤ r ∧ Ioo (-r) r ⊆ {x : ℝ | t < f x} ∧
        {x : ℝ | t < f x} ⊆ Icc (-r) r := by
  have habs (x : ℝ) : f |x| = f x := by
    rcases abs_choice x with h | h <;> rw [h]
    exact heven x
  let S : Set ℝ := {u : ℝ | 0 ≤ u ∧ t < f u}
  have hmem : ∀ u ∈ S, 0 ≤ u ∧ t < f u := fun _ hu ↦ hu
  by_cases hne : S.Nonempty
  · have hbdd : BddAbove S := ⟨B, fun u hu ↦ (hsupport fun h ↦ by
      have := (hmem u hu).2; rw [h] at this; linarith).2⟩
    refine ⟨sSup S, ?_, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
    · obtain ⟨u, hu⟩ := hne
      exact (hmem u hu).1.trans (le_csSup hbdd hu)
    · obtain ⟨u, hu, hxu⟩ := exists_lt_of_lt_csSup hne (abs_lt.mpr hx)
      have hlt : t < f |x| :=
        (hmem u hu).2.trans_le (hanti (abs_nonneg x) (hmem u hu).1 hxu.le)
      rwa [habs] at hlt
    · exact abs_le.1 (le_csSup hbdd (show |x| ∈ S from ⟨abs_nonneg x, by rw [habs]; exact hx⟩))
  · exact ⟨0, le_rfl, by simp, fun x hx ↦
      absurd ⟨|x|, abs_nonneg x, by rw [habs]; exact hx⟩ hne⟩

theorem lowerGammaBoundaryLog_halfInteger_exp_integrable {a : ℝ} (ha : 0 < a) (k : ℕ) (R : ℝ) :
    Integrable fun y : ℝ ↦ exp ((-a) * |y|) * h_ℓ ((k : ℝ) + 1 / 2) R y := by
  have hsum : Integrable fun y : ℝ ↦ ∑ j ∈ Finset.range k,
      exp ((-a) * |y|) * log (√(((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2)) :=
    integrable_finsetSum _ fun j _ ↦ lower_exp_log_sqrtFactor_integrable ha (by positivity)
  have hbase : Integrable fun y : ℝ ↦ ((k : ℝ) + 1 / 2) * log (π * R ^ 2) * exp ((-a) * |y|) -
      (∑ j ∈ Finset.range k, exp ((-a) * |y|) * log (√(((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2))) +
      1 / 2 * (exp ((-a) * |y|) * log (coth (π * |y| / 2) / (|y| / 2))) :=
    (((integrable_exp_neg_mul_abs ha).const_mul (((k : ℝ) + 1 / 2) * log (π * R ^ 2))).sub hsum).add
      ((integrable_exp_neg_mul_abs_mul_log_coth_div ha).const_mul (1 / 2))
  refine hbase.congr ?_
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with y hy
  simp only [lowerGammaBoundaryLog_halfInteger k R hy, mul_add, mul_sub, Finset.mul_sum]
  ring

theorem lowerGammaBoundaryLog_dimension_exp_integrable {d : ℕ} (_hd : 0 < d) {a : ℝ} (ha : 0 < a)
    (R : ℝ) : Integrable fun y : ℝ ↦ exp ((-a) * |y|) * h_ℓ ((d : ℝ) / 2) R y := by
  obtain ⟨k, hk⟩ | ⟨k, hk⟩ := natCast_div_two_cases d <;> rw [hk]
  · exact lowerGammaBoundaryLog_integer_exp_integrable ha k R
  · exact lowerGammaBoundaryLog_halfInteger_exp_integrable ha k R

theorem lowerStripGammaOuter_integrable_dimension {d : ℕ} (hd : 0 < d) {R : ℝ} {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2)) :
    Integrable fun y : ℝ ↦ K'_ℓ ((d : ℝ) / 2) z y * (h_ℓ ((d : ℝ) / 2) R y : ℂ) := by
  have hℓ : 0 < (d : ℝ) / 2 := by positivity
  exact lowerStripGammaOuter_integrable_of_exp_integrable hℓ hz
    (lowerGammaBoundaryLog_dimension_exp_integrable hd (by positivity) R)

/-- `f_T T x = log √(x² + T²/4)`, the integrand of the Riemann sum of report Lemma 3.3. -/
def f_T (T x : ℝ) : ℝ := log (√(x ^ 2 + T ^ 2 / 4))

theorem lowerRiemannLog_monotoneOn {T : ℝ} (hT : T ≠ 0) : MonotoneOn (f_T T) (Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  have hx' : (0 : ℝ) ≤ x := hx
  have hy' : (0 : ℝ) ≤ y := hy
  exact Real.log_le_log (Real.sqrt_pos.2 (by positivity))
    (Real.sqrt_le_sqrt (by nlinarith [(sq_le_sq₀ hx' hy').2 hxy]))

/-- For `f` monotone on `[0, k]` the left and right Riemann sums bracket `∫₀ᵏ f`, and the two
sums differ by `f k - f 0`. -/
theorem monotone_riemann_bracket {f : ℝ → ℝ} {k : ℕ} (hf : MonotoneOn f (Icc (0 : ℝ) (k : ℝ))) :
    (∑ j ∈ Finset.range k, f j) ≤ (∫ x in (0 : ℝ)..(k : ℝ), f x) ∧
      (∫ x in (0 : ℝ)..(k : ℝ), f x) ≤ ∑ j ∈ Finset.range k, f ((j : ℝ) + 1) ∧
        (∑ j ∈ Finset.range k, f ((j : ℝ) + 1)) - ∑ j ∈ Finset.range k, f j = f k - f 0 := by
  have hf' : MonotoneOn f (Icc (0 : ℝ) (0 + (k : ℝ))) := by simpa using hf
  refine ⟨by simpa using hf'.sum_le_integral,
    by simpa [Nat.cast_add, Nat.cast_one] using hf'.integral_le_sum, ?_⟩
  rw [← Finset.sum_sub_distrib]
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] using
    Finset.sum_range_sub (fun j : ℕ ↦ f (j : ℝ)) k

theorem monotone_leftRiemann_error (f : ℝ → ℝ) {k : ℕ} (hk : 0 < k)
    (hf : MonotoneOn f (Icc (0 : ℝ) 1)) :
    0 ≤ (k : ℝ) * (∫ x in (0 : ℝ)..1, f x) - ∑ j ∈ Finset.range k, f ((j : ℝ) / (k : ℝ)) ∧
      (k : ℝ) * (∫ x in (0 : ℝ)..1, f x) - ∑ j ∈ Finset.range k, f ((j : ℝ) / (k : ℝ)) ≤
        f 1 - f 0 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hscaled : MonotoneOn (fun x : ℝ ↦ f (x / (k : ℝ))) (Icc (0 : ℝ) (k : ℝ)) :=
    fun x hx y hy hxy ↦ hf ⟨div_nonneg hx.1 hkpos.le, (div_le_one hkpos).2 hx.2⟩
      ⟨div_nonneg hy.1 hkpos.le, (div_le_one hkpos).2 hy.2⟩
      (div_le_div_of_nonneg_right hxy hkpos.le)
  obtain ⟨hleft, hright, hshift⟩ := monotone_riemann_bracket hscaled
  have hintegral : (∫ x in (0 : ℝ)..(k : ℝ), f (x / (k : ℝ))) =
      (k : ℝ) * ∫ x in (0 : ℝ)..1, f x := by simp [hkpos.ne']
  rw [hintegral] at hleft hright
  rw [div_self hkpos.ne', zero_div] at hshift
  exact ⟨by linarith, by linarith⟩

theorem lower_integer_leftRiemann_error {T : ℝ} (hT : T ≠ 0) {k : ℕ} (hk : 0 < k) :
    0 ≤ (k : ℝ) * (∫ x in (0 : ℝ)..1, f_T T x) - ∑ j ∈ Finset.range k,
            f_T T ((j : ℝ) / (k : ℝ)) ∧
      (k : ℝ) * (∫ x in (0 : ℝ)..1, f_T T x) - ∑ j ∈ Finset.range k,
            f_T T ((j : ℝ) / (k : ℝ)) ≤
        f_T T 1 - f_T T 0 :=
  monotone_leftRiemann_error (f_T T) hk ((lowerRiemannLog_monotoneOn hT).mono fun _ hx ↦ hx.1)

theorem monotone_midpointIntegral_error (f : ℝ → ℝ) (k : ℕ)
    (hf : MonotoneOn f (Icc (0 : ℝ) (k : ℝ))) :
    |(∫ x in (0 : ℝ)..(k : ℝ), f x) - ∑ j ∈ Finset.range k, f ((j : ℝ) + 1 / 2)| ≤
      f (k : ℝ) - f 0 := by
  obtain ⟨hleft, hright, hshift⟩ := monotone_riemann_bracket hf
  have key : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      (∑ j ∈ Finset.range k, f ((j : ℝ) + a)) ≤ ∑ j ∈ Finset.range k, f ((j : ℝ) + b) := by
    refine fun a b ha hab hb ↦ Finset.sum_le_sum fun j hj ↦ ?_
    have hj1 : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast Finset.mem_range.1 hj
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := j.cast_nonneg
    exact hf ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
  have h1 := key 0 (1 / 2) le_rfl (by norm_num) (by norm_num)
  have h2 := key (1 / 2) 1 (by norm_num) (by norm_num) le_rfl
  simp only [add_zero] at h1
  exact abs_le.2 ⟨by linarith, by linarith⟩

theorem lower_halfInteger_midpointRiemann_error {T : ℝ} (hT : T ≠ 0) {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) :
    |ℓ * (∫ x in (0 : ℝ)..((k : ℝ) / ℓ), f_T T x) -
        ∑ j ∈ Finset.range k, f_T T (((j : ℝ) + 1 / 2) / ℓ)| ≤
      f_T T ((k : ℝ) / ℓ) - f_T T 0 := by
  have hscaled : MonotoneOn (fun x : ℝ ↦ f_T T (x / ℓ)) (Icc (0 : ℝ) (k : ℝ)) :=
    fun x hx y hy hxy ↦ lowerRiemannLog_monotoneOn hT (div_nonneg hx.1 hℓ.le)
      (div_nonneg hy.1 hℓ.le) (div_le_div_of_nonneg_right hxy hℓ.le)
  have hmid := monotone_midpointIntegral_error (fun x : ℝ ↦ f_T T (x / ℓ)) k hscaled
  have hscale : (∫ x in (0 : ℝ)..(k : ℝ), f_T T (x / ℓ)) =
      ℓ * ∫ x in (0 : ℝ)..((k : ℝ) / ℓ), f_T T x := by
    simpa using intervalIntegral.integral_comp_div (a := (0 : ℝ)) (b := (k : ℝ)) (f_T T) hℓ.ne'
  rw [hscale] at hmid
  simpa using hmid

/-- The endpoint phase `-π|T|/4 - ½ log (1 + T²/4) + (|T|/2) arctan (|T|/2)` of Lemma 3.3. -/
def lowerEndpointPhase (T : ℝ) : ℝ :=
  -π * |T| / 4 - 1 / 2 * log (1 + T ^ 2 / 4) + |T| / 2 * arctan (|T| / 2)

/-- A primitive of `f_T T`. -/
def lowerRiemannLogPrimitive (T x : ℝ) : ℝ :=
  x / 2 * log (x ^ 2 + T ^ 2 / 4) - x + |T| / 2 * arctan (x / (|T| / 2))

theorem lowerRiemannLogPrimitive_hasDerivAt {T : ℝ} (hT : T ≠ 0) (x : ℝ) :
    HasDerivAt (lowerRiemannLogPrimitive T) (f_T T x) x := by
  have hrad : 0 < x ^ 2 + T ^ 2 / 4 := by positivity
  have ha : 0 < |T| / 2 := half_pos (abs_pos.mpr hT)
  have hquad : HasDerivAt (fun u : ℝ ↦ u ^ 2 + T ^ 2 / 4) (2 * x) x := by
    convert! ((hasDerivAt_id x).pow 2).add_const (T ^ 2 / 4) using 1
    simp [id_eq]
  have hfirst := ((hasDerivAt_id x).div_const 2).mul (hquad.log hrad.ne')
  have hatan := (Real.hasDerivAt_arctan (x / (|T| / 2))).comp x
    ((hasDerivAt_id x).div_const (|T| / 2))
  convert! (hfirst.sub (hasDerivAt_id x)).add (hatan.const_mul (|T| / 2)) using 1
  unfold f_T
  simp only [id_eq]
  rw [Real.log_sqrt hrad.le]
  field_simp [hrad.ne', ha.ne']
  nlinarith [sq_abs T]

/-- The Riemann-sum integral of Lemma 3.3, evaluated by the primitive above. -/
theorem integral_lowerRiemannLog {T : ℝ} (hT : T ≠ 0) :
    -(∫ x in (0 : ℝ)..1, f_T T x) = 1 + lowerEndpointPhase T := by
  have hmono : MonotoneOn (f_T T) ([[0, 1]] : Set ℝ) := by
    simpa using (lowerRiemannLog_monotoneOn hT).mono fun _ hx ↦ hx.1
  have ha : 0 < |T| / 2 := half_pos (abs_pos.mpr hT)
  have hatan : arctan (1 / (|T| / 2)) = π / 2 - arctan (|T| / 2) := by
    simpa [one_div] using Real.arctan_inv_of_pos ha
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ ↦ lowerRiemannLogPrimitive_hasDerivAt hT x) hmono.intervalIntegrable]
  unfold lowerRiemannLogPrimitive lowerEndpointPhase
  simp only [one_pow, zero_pow (by norm_num : 2 ≠ 0), zero_add, zero_div, zero_mul, sub_zero,
    Real.arctan_zero]
  rw [hatan]
  ring

end

end CohnElkies
