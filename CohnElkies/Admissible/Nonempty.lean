import CohnElkies.SchwartzTools

/-!
# The admissible class is nonempty

The flat bump `φ` (a radial nonnegative compactly supported test function with `∫ φ > 0`) and its
autocorrelation `φ ⋆ φ`, whose Fourier transform `(𝓕 φ)² ≥ 0` is positive at the origin, give a
radial admissible function in every dimension (`autocorrelationAdmissible`, so `𝒜_d^rad ≠ ∅` and
`𝒜_d ≠ ∅`, `admissible_nonempty`), so the quotient set of the Cohn–Elkies program is nonempty.
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter Function MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology RealInnerProductSpace Pointwise ContDiff

/-- The flat bump `x ↦ expNegInvGlue (1 - 4‖x‖²)`, supported in the ball of radius `1/2`. -/
def bumpReal (d : ℕ) (x : Euclidean d) : ℝ := expNegInvGlue (1 - 4 * ‖x‖ ^ 2)

/-- The flat bump, viewed as a complex-valued function. -/
def bumpFun (d : ℕ) (x : Euclidean d) : ℂ := (bumpReal d x : ℂ)

theorem support_bumpReal (d : ℕ) :
    support (bumpReal d) = Metric.ball (0 : Euclidean d) (1 / 2) := by
  ext x
  simp only [mem_support, bumpReal, Metric.mem_ball, dist_zero_right]
  refine ⟨fun hx ↦ ?_, fun hx ↦ (expNegInvGlue.pos_of_pos (by nlinarith [norm_nonneg x])).ne'⟩
  have hpos : 0 < 1 - 4 * ‖x‖ ^ 2 := lt_of_not_ge fun h ↦ hx (expNegInvGlue.zero_of_nonpos h)
  nlinarith [norm_nonneg x]

theorem support_bumpFun (d : ℕ) :
    support (bumpFun d) = Metric.ball (0 : Euclidean d) (1 / 2) := by
  rw [← support_bumpReal d]; ext x; simp [bumpFun]

theorem contDiff_bumpFun (d : ℕ) : ContDiff ℝ ∞ (bumpFun d) :=
  Complex.ofRealCLM.contDiff.comp
    (expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_const.mul (contDiff_norm_sq ℝ))))

theorem hasCompactSupport_bumpFun (d : ℕ) : HasCompactSupport (bumpFun d) :=
  .of_support_subset_isCompact (isCompact_closedBall (0 : Euclidean d) (1 / 2))
    (by rw [support_bumpFun]; exact Metric.ball_subset_closedBall)

/-- The flat bump as a test function on `ℝ^d`. -/
def bump (d : ℕ) : TestFunction d :=
  (hasCompactSupport_bumpFun d).toSchwartzMap (contDiff_bumpFun d)

@[simp] theorem bump_apply (d : ℕ) (x : Euclidean d) : bump d x = (bumpReal d x : ℂ) := rfl

theorem support_bump (d : ℕ) :
    support (bump d : Euclidean d → ℂ) = Metric.ball (0 : Euclidean d) (1 / 2) :=
  support_bumpFun d

theorem bump_real (d : ℕ) : IsRealValued (bump d) := fun x ↦ by simp

theorem bump_radial (d : ℕ) : IsRadial (bump d) := fun x y hxy ↦ by simp [bumpReal, hxy]

theorem integral_bumpReal_pos (d : ℕ) : 0 < ∫ x : Euclidean d, bumpReal d x := by
  have hint : Integrable (bumpReal d) (volume : Measure (Euclidean d)) := by
    simpa using ((bump d).integrable (μ := volume)).re
  have hzero : 0 < bumpReal d (0 : Euclidean d) := by
    unfold bumpReal
    simpa using expNegInvGlue.pos_of_pos (by norm_num : (0 : ℝ) < 1)
  exact integral_pos_of_integrable_nonneg_nonzero (by unfold bumpReal; fun_prop) hint
    (fun _ ↦ expNegInvGlue.nonneg _) hzero.ne'

/-- The autocorrelation `φ ⋆ φ` of the flat bump: the witness for `𝒜_d ≠ ∅`. -/
def autocorrelation (d : ℕ) : TestFunction d :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (bump d) (bump d)

theorem fourier_autocorrelation_apply (d : ℕ) (ξ : Euclidean d) :
    ((𝓕 (autocorrelation d) : TestFunction d) ξ) = ((𝓕 (bump d) : TestFunction d) ξ) ^ 2 := by
  rw [autocorrelation, SchwartzMap.fourier_convolution]
  simp [pow_two]

theorem fourier_bump_real (d : ℕ) : IsRealValued (𝓕 (bump d) : TestFunction d) :=
  (bump_real d).fourier_of_radial (bump_radial d)

theorem fourier_bump_zero (d : ℕ) : ((𝓕 (bump d) : TestFunction d) (0 : Euclidean d)) =
    (↑(∫ x : Euclidean d, bumpReal d x) : ℂ) := by
  change (𝓕 (bump d : Euclidean d → ℂ)) 0 = _
  rw [Real.fourier_eq']
  simpa using integral_ofReal (𝕜 := ℂ) (f := bumpReal d) (μ := (volume : Measure (Euclidean d)))

theorem autocorrelation_eq_zero (d : ℕ) {x : Euclidean d} (hx : 1 ≤ ‖x‖) :
    autocorrelation d x = 0 := by
  have hconv : (autocorrelation d : Euclidean d → ℂ) = MeasureTheory.convolution
      (bump d : Euclidean d → ℂ) (bump d : Euclidean d → ℂ) (ContinuousLinearMap.mul ℂ ℂ) volume :=
    funext (SchwartzMap.convolution_apply (ContinuousLinearMap.mul ℂ ℂ) (bump d) (bump d))
  have hsub : support (autocorrelation d : Euclidean d → ℂ) ⊆ Metric.ball (0 : Euclidean d) 1 := by
    rw [hconv]
    refine (MeasureTheory.support_convolution_subset (ContinuousLinearMap.mul ℂ ℂ)).trans ?_
    rw [support_bump, ball_add_ball (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)]
    norm_num
  by_contra hne
  have hball := hsub hne
  rw [Metric.mem_ball, dist_zero_right] at hball
  linarith

theorem autocorrelation_real (d : ℕ) : IsRealValued (autocorrelation d) := by
  intro x
  rw [autocorrelation, SchwartzMap.convolution_apply, MeasureTheory.convolution_def]
  change (∫ t : Euclidean d, (bumpReal d t : ℂ) * (bumpReal d (x - t) : ℂ)).im = 0
  simp_rw [← Complex.ofReal_mul]
  rw [show (∫ t : Euclidean d, ((bumpReal d t * bumpReal d (x - t) : ℝ) : ℂ))
      = ((∫ t : Euclidean d, bumpReal d t * bumpReal d (x - t) : ℝ) : ℂ) from
    integral_ofReal (𝕜 := ℂ)]
  simp

theorem autocorrelation_radial (d : ℕ) : IsRadial (autocorrelation d) := by
  have hfourier : IsRadial (𝓕 (autocorrelation d) : TestFunction d) := fun x y hxy ↦ by
    rw [fourier_autocorrelation_apply, fourier_autocorrelation_apply,
      (bump_radial d).fourier x y hxy]
  intro x y hxy
  simpa [fourier_sq_apply] using hfourier.fourier (-x) (-y) (by simpa using hxy)

/-- The autocorrelation of the flat bump is a radial admissible function. -/
def autocorrelationAdmissible (d : ℕ) : RadialAdmissible d where
  function := autocorrelation d
  real := autocorrelation_real d
  radial := autocorrelation_radial d
  fourier_real := fun ξ ↦ by
    rw [fourier_autocorrelation_apply]
    simp [pow_two, Complex.mul_im, fourier_bump_real d ξ]
  fourier_nonneg := fun ξ ↦ by
    rw [fourier_autocorrelation_apply]
    simp only [pow_two, Complex.mul_re, fourier_bump_real d ξ, mul_zero, sub_zero]
    exact mul_self_nonneg _
  fourier_zero_pos := by
    rw [fourier_autocorrelation_apply, fourier_bump_zero]
    simpa [pow_two, Complex.mul_re] using
      mul_pos (integral_bumpReal_pos d) (integral_bumpReal_pos d)
  outside_nonpos := fun x hx ↦ by rw [autocorrelation_eq_zero d hx]; simp

theorem admissible_nonempty (d : ℕ) : Nonempty (Admissible d) :=
  ⟨(autocorrelationAdmissible d).toAdmissible⟩

theorem quotientSet_nonempty (d : ℕ) : (quotientSet d).Nonempty :=
  ⟨_, (autocorrelationAdmissible d).toAdmissible, rfl⟩

end

end CohnElkies
