import CohnElkies.Basic

/-!
# Radial test functions and their profiles (report §2.2)

The volume `v_d` of the unit ball (`v_{2k} = π^k/k!`), the radial profile `r ↦ f(r e₁)` of a
test function, polar integration `∫ f(x) |x|^{s-d} dx = S_d · M g(s)` with the surface area
`S_d = d v_d`, the Mellin transform `X_g(t) = M g(ℓ - it)` of a profile on the line `Re z = ℓ`
(report (8)) and its expression as a Fourier transform, and the radial profile of a test function
as a Schwartz function on `ℝ` (smoothness, decay, Mellin convergence for `Re s > -2` when
`f(0) = 0`).
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open MeasureTheory Metric Real
open scoped ENNReal

theorem sqrt_pi_pow_eq_rpow (d : ℕ) : √π ^ d = π ^ (d / 2 : ℝ) := by
  rw [sqrt_eq_rpow, ← rpow_natCast, ← rpow_mul pi_nonneg]
  congr 1
  ring

/-- The unit ball of `ℝ^d` has volume `v_d`. -/
theorem volume_real_unitBall {d : ℕ} (hd : 0 < d) :
    volume.real (ball (0 : Euclidean d) 1) = unitBallVolume d := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have h : volume (ball (0 : Euclidean d) 1) = ENNReal.ofReal (unitBallVolume d) := by
    simpa [unitBallVolume, sqrt_pi_pow_eq_rpow] using
      EuclideanSpace.volume_ball (Fin d) (0 : Euclidean d) 1
  rw [measureReal_def, h, ENNReal.toReal_ofReal (unitBallVolume_pos d).le]

/-- `v_{2k} = π^k / k!`. -/
theorem unitBallVolume_even (k : ℕ) : unitBallVolume (2 * k) = π ^ k / (k.factorial : ℝ) := by
  rw [unitBallVolume]
  push_cast
  rw [show 2 * (k : ℝ) / 2 = k by ring, rpow_natCast, Gamma_nat_eq_factorial]

end

noncomputable section

open Filter MeasureTheory Metric Real Set
open scoped FourierTransform SchwartzMap Topology ENNReal

/-- The first standard basis vector `e₁` of `ℝ^d`, `d > 0`. -/
def radialUnitDirection {d : ℕ} (hd : 0 < d) : Euclidean d :=
  EuclideanSpace.basisFun (Fin d) ℝ ⟨0, hd⟩

theorem norm_radialUnitDirection {d : ℕ} (hd : 0 < d) : ‖radialUnitDirection hd‖ = 1 :=
  (EuclideanSpace.basisFun (Fin d) ℝ).norm_eq_one _

/-- The radial profile `r ↦ f(r e₁)` of a test function `f` (the function `g(r)` of report
§2.2). -/
def radialProfile {d : ℕ} (hd : 0 < d) (f : TestFunction d) (r : ℝ) : ℂ :=
  f (r • radialUnitDirection hd)

theorem radialProfile_norm {d : ℕ} (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (x : Euclidean d) : radialProfile hd f ‖x‖ = f x :=
  hf _ _ (by simp [norm_smul, norm_radialUnitDirection hd])

theorem radialProfile_neg {d : ℕ} (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f) (r : ℝ) :
    radialProfile hd f (-r) = radialProfile hd f r :=
  hf _ _ (by simp [norm_smul, norm_radialUnitDirection hd])

theorem radialProfile_continuous {d : ℕ} (hd : 0 < d) (f : TestFunction d) :
    Continuous (radialProfile hd f) :=
  f.continuous.comp (continuous_id.smul continuous_const)

@[simp] theorem radialProfile_zero {d : ℕ} (hd : 0 < d) (f : TestFunction d) :
    radialProfile hd f 0 = f 0 := by
  simp [radialProfile]

theorem radialProfile_real {d : ℕ} (hd : 0 < d) (f : TestFunction d) (hf : IsRealValued f)
    (r : ℝ) : (radialProfile hd f r).im = 0 :=
  hf _

/-- The surface area `S_d = d v_d` of the unit sphere of `ℝ^d`. -/
def sphereArea (d : ℕ) : ℝ := d * unitBallVolume d

theorem radialSurfaceArea_pos {d : ℕ} (hd : 0 < d) : 0 < sphereArea d :=
  mul_pos (Nat.cast_pos.2 hd) (unitBallVolume_pos d)

/-- Polar integration for radial `f` with profile `g`: `∫ f(x) |x|^{s-d} dx = S_d · M g(s)`
(report §2.2). -/
theorem integral_radialProfile_cpow {d : ℕ} (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (s : ℂ) :
    ∫ x : Euclidean d, f x * (‖x‖ : ℂ) ^ (s - d) =
      sphereArea d • mellin (radialProfile hd f) s := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  calc ∫ x : Euclidean d, f x * (‖x‖ : ℂ) ^ (s - d)
      = ∫ x : Euclidean d, radialProfile hd f ‖x‖ * (‖x‖ : ℂ) ^ (s - d) :=
        integral_congr_ae (.of_forall fun x ↦ by simp only [radialProfile_norm hd f hf])
    _ = sphereArea d • ∫ r in Ioi (0 : ℝ), (r ^ (d - 1) : ℝ) •
          (radialProfile hd f r * (r : ℂ) ^ (s - d)) := by
        rw [integral_fun_norm_addHaar volume fun r : ℝ ↦ radialProfile hd f r * (r : ℂ) ^ (s - d),
          finrank_euclideanSpace_fin, volume_real_unitBall hd]
        simp [sphereArea, mul_smul]
    _ = sphereArea d • mellin (radialProfile hd f) s := by
        unfold mellin
        congr 1
        refine setIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
        rw [Complex.real_smul, Complex.ofReal_pow, ← Complex.cpow_natCast, smul_eq_mul,
          mul_left_comm, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 hr.ne'), Nat.cast_pred hd,
          show (d : ℂ) - 1 + (s - d) = s - 1 by ring, mul_comm]

/-- `X_f(t) = M g(λ - it)`: the Mellin transform of the radial profile `g` of `f` on the critical
line `Re z = λ = d/2` (report (8)). -/
def X_fℝ {d : ℕ} (hd : 0 < d) (f : TestFunction d) (t : ℝ) : ℂ :=
  mellin (radialProfile hd f) ((d / 2 : ℝ) - I * t)

/-- `X_f` is the Fourier transform of `v ↦ e^{-λ v} g(e^{-v})`. -/
theorem radialMellinFrequency_eq_fourier {d : ℕ} (hd : 0 < d) (f : TestFunction d) (t : ℝ) :
    X_fℝ hd f t =
      𝓕 (fun u : ℝ ↦ exp (-(d / 2) * u) • radialProfile hd f (exp (-u))) (-t / (2 * π)) := by
  unfold X_fℝ
  simpa using mellin_eq_fourier (radialProfile hd f) (s := (d / 2 : ℝ) - I * t)

end

noncomputable section

open Asymptotics Filter Function MeasureTheory Metric Real Set
open scoped FourierTransform SchwartzMap Topology

/-! ### The radial profile as a Schwartz function on the line -/

/-- The isometry `r ↦ r e₁` of the real line into `ℝ^d`. -/
def radialLineIsometry {d : ℕ} (hd : 0 < d) : ℝ →ₗᵢ[ℝ] Euclidean d :=
  LinearIsometry.toSpanSingleton ℝ (Euclidean d) (norm_radialUnitDirection hd)

/-- The radial profile `r ↦ f(r e₁)` of a test function, as a Schwartz function on `ℝ`. -/
def radialSchwartzProfile {d : ℕ} (hd : 0 < d) (f : TestFunction d) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (radialLineIsometry hd).toContinuousLinearMap.hasTemperateGrowth
    (radialLineIsometry hd).isometry.antilipschitzWith f

@[simp] theorem radialSchwartzProfile_apply {d : ℕ} (hd : 0 < d) (f : TestFunction d) (r : ℝ) :
    radialSchwartzProfile hd f r = radialProfile hd f r := rfl

theorem radialProfile_smooth {d : ℕ} (hd : 0 < d) (f : TestFunction d) (n : ℕ∞) :
    ContDiff ℝ n (radialProfile hd f) := (radialSchwartzProfile hd f).smooth n

theorem radialProfile_deriv_zero {d : ℕ} (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f) :
    deriv (radialProfile hd f) 0 = 0 := by
  have heven : (fun r : ℝ ↦ radialProfile hd f (-r)) = radialProfile hd f :=
    funext (radialProfile_neg hd f hf)
  have hderiv := congrArg (fun h : ℝ → ℂ ↦ deriv h 0) heven
  rw [deriv_comp_neg] at hderiv
  simp only [neg_zero] at hderiv
  linear_combination -hderiv / 2

/-- A radial test function vanishing at the origin has a profile of size `O(r²)` near `0`. -/
theorem radialProfile_quadratic_bound {d : ℕ} (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0) :
    ∃ C : ℝ, ∀ r : ℝ, 0 ≤ r → r ≤ 1 → ‖radialProfile hd f r‖ ≤ C * r ^ 2 := by
  have hsmooth : ContDiffOn ℝ (2 : ℕ∞) (radialProfile hd f) (Icc (0 : ℝ) 1) :=
    (radialProfile_smooth hd f 2).contDiffOn
  obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound (f := radialProfile hd f) (a := (0 : ℝ))
    (b := (1 : ℝ)) (n := 1) zero_le_one hsmooth
  refine ⟨C, fun r hr hrone ↦ ?_⟩
  have hderivWithin : derivWithin (radialProfile hd f) (Icc (0 : ℝ) 1) 0 = 0 := by
    rw [DifferentiableAt.derivWithin ((radialProfile_smooth hd f 1).differentiable one_ne_zero 0)
      (uniqueDiffOn_Icc_zero_one 0 (by simp))]
    exact radialProfile_deriv_zero hd f hf
  have htaylor : taylorWithinEval (radialProfile hd f) 1 (Icc (0 : ℝ) 1) 0 r = 0 := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, taylorWithinEval_succ]
    simp [radialProfile_zero, hzero, iteratedDerivWithin_one, hderivWithin]
  simpa only [htaylor, sub_zero, Nat.reduceAdd] using hC r ⟨hr, hrone⟩

theorem radialProfile_isBigO_rpow_two_zero {d : ℕ} (hd : 0 < d) (f : TestFunction d)
    (hf : IsRadial f) (hzero : f (0 : Euclidean d) = 0) :
    radialProfile hd f =O[𝓝[>] (0 : ℝ)] fun r : ℝ ↦ r ^ (2 : ℝ) := by
  obtain ⟨C, hC⟩ := radialProfile_quadratic_bound hd f hf hzero
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_mem_nhdsWithin, (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
    |>.filter_mono nhdsWithin_le_nhds] with r hr hrone
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hr.le 2), Real.rpow_two]
  exact hC r hr.le hrone.le

theorem radialProfile_isBigO_rpow_atTop {d : ℕ} (hd : 0 < d) (f : TestFunction d) (a : ℝ) :
    radialProfile hd f =O[atTop] fun r : ℝ ↦ r ^ (-a) := by
  refine (((radialSchwartzProfile hd f).isBigO_cocompact_rpow (-a)).mono atTop_le_cocompact).congr'
    (.of_forall fun r ↦ radialSchwartzProfile_apply hd f r) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  simp [Real.norm_eq_abs, abs_of_pos hr]

theorem radialProfile_locallyIntegrableOn {d : ℕ} (hd : 0 < d) (f : TestFunction d) :
    LocallyIntegrableOn (radialProfile hd f) (Ioi (0 : ℝ)) :=
  (radialProfile_continuous hd f).locallyIntegrable.locallyIntegrableOn _

theorem radialProfile_mellinConvergent {d : ℕ} (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0) (s : ℂ) (hs : -2 < s.re) :
    MellinConvergent (radialProfile hd f) s :=
  mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := (-2 : ℝ))
    (radialProfile_locallyIntegrableOn hd f) (radialProfile_isBigO_rpow_atTop hd f (s.re + 1))
    (by linarith) (by simpa using radialProfile_isBigO_rpow_two_zero hd f hf hzero) hs

theorem radialProfile_mellin_differentiableAt {d : ℕ} (hd : 0 < d) (f : TestFunction d)
    (hf : IsRadial f) (hzero : f (0 : Euclidean d) = 0) (s : ℂ) (hs : -2 < s.re) :
    DifferentiableAt ℂ (mellin (radialProfile hd f)) s :=
  mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := (-2 : ℝ))
    (radialProfile_locallyIntegrableOn hd f) (radialProfile_isBigO_rpow_atTop hd f (s.re + 1))
    (by linarith) (by simpa using radialProfile_isBigO_rpow_two_zero hd f hf hzero) hs

end

end CohnElkies
