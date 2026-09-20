import Mathlib

/-!
# The Poisson kernel and the Poisson integral of the upper half-plane

We define the Poisson kernel `P(z, x) = π⁻¹ Im z / ((x - Re z)² + (Im z)²)` of the upper
half-plane `ℍ = {z | 0 < Im z}` and the Poisson integral `P[b](z) = ∫ P(z, x) b(x) dx` of a
boundary datum `b : ℝ → ℝ` with `b(x) / (1 + x²)` integrable, and prove the basic facts:
positivity, total mass `∫ P(z, x) dx = 1`, harmonicity in `z`, monotonicity and boundedness of
`P[b]`, harmonicity of `P[b]` on `ℍ` (it is the imaginary part of the holomorphic Nevanlinna
integral `π⁻¹ ∫ ((x - z)⁻¹ - x / (1 + x²)) b(x) dx`), the boundary behaviour
`P[b](z) → b(x₀)` as `z → x₀` at continuity points of `b`, and the monotone convergence of
the truncations `P[max b (-n)] → P[b]`.
-/

open Filter InnerProductSpace MeasureTheory Metric Set
open scoped Real Topology

/-- The elementary inequality `1 + x² ≤ (2 + (1 + 2 A²) / η²) ((x - a)² + h²)` for `|a| ≤ A` and
`0 < η ≤ h`; it compares `(x - a)² + h²`, the squared distance from `x ∈ ℝ` to `a + i h`, with
`1 + x²`, uniformly for `a + i h` in a compact subset of the upper half-plane. -/
theorem one_add_sq_le_mul_sub_sq_add_sq {A η a h x : ℝ} (hη : 0 < η) (ha : |a| ≤ A)
    (hh : η ≤ h) : 1 + x ^ 2 ≤ (2 + (1 + 2 * A ^ 2) / η ^ 2) * ((x - a) ^ 2 + h ^ 2) := by
  have h3 : 1 + 2 * A ^ 2 ≤ (1 + 2 * A ^ 2) / η ^ 2 * h ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [pow_le_pow_left₀ hη.le hh 2]
  have h4 : 0 ≤ (1 + 2 * A ^ 2) / η ^ 2 * (x - a) ^ 2 := by positivity
  nlinarith [sq_nonneg (x - 2 * a), abs_nonneg a, sq_abs a]

/-- Truncating from below does not increase the absolute value: `|max a (-c)| ≤ |a|` for
`0 ≤ c`. -/
theorem abs_max_neg_le_abs {a c : ℝ} (hc : 0 ≤ c) : |max a (-c)| ≤ |a| :=
  abs_le.2 ⟨(neg_abs_le a).trans (le_max_left _ _),
    max_le (le_abs_self a) ((neg_nonpos.2 hc).trans (abs_nonneg a))⟩

namespace Complex

/-- The Poisson kernel `P(z, x) = π⁻¹ Im z / ((x - Re z)² + (Im z)²)` of the upper half-plane. -/
noncomputable def poissonKernelHalfPlane (z : ℂ) (x : ℝ) : ℝ :=
  π⁻¹ * z.im / ((x - z.re) ^ 2 + z.im ^ 2)

theorem poissonKernelHalfPlane_pos {z : ℂ} (hz : 0 < z.im) (x : ℝ) :
    0 < poissonKernelHalfPlane z x :=
  div_pos (by positivity) (by positivity)

/-- The Poisson kernel is the imaginary part of the holomorphic function `π⁻¹ (x - z)⁻¹`. -/
theorem poissonKernelHalfPlane_eq_im (z : ℂ) (x : ℝ) :
    poissonKernelHalfPlane z x = (π⁻¹ * ((x : ℂ) - z)⁻¹).im := by
  simp [poissonKernelHalfPlane, normSq_apply, mul_div_assoc, sq]

theorem measurable_poissonKernelHalfPlane (z : ℂ) : Measurable (poissonKernelHalfPlane z) := by
  fun_prop [poissonKernelHalfPlane]

theorem continuous_poissonKernelHalfPlane {z : ℂ} (hz : z.im ≠ 0) :
    Continuous (poissonKernelHalfPlane z) :=
  continuous_const.div (by fun_prop) fun x ↦ by positivity

/-- For `x ≠ z` the Poisson kernel is continuous in `z`. -/
theorem continuousAt_poissonKernelHalfPlane {z : ℂ} {x : ℝ} (h : (x : ℂ) ≠ z) :
    ContinuousAt (fun w ↦ poissonKernelHalfPlane w x) z := by
  refine (continuousAt_const.mul continuous_im.continuousAt).div (by fun_prop) ?_
  simpa [normSq_apply, sq] using (normSq_pos.2 (sub_ne_zero.2 h)).ne'

/-- The Poisson kernel in the form `π⁻¹ (Im z)⁻¹ (1 + ((Im z)⁻¹ (x - Re z))²)⁻¹` adapted to the
substitution `x = Re z + Im z · t`. -/
theorem poissonKernelHalfPlane_eq_inv_one_add_sq {z : ℂ} (hz : z.im ≠ 0) (x : ℝ) :
    poissonKernelHalfPlane z x = π⁻¹ * z.im⁻¹ * (1 + (z.im⁻¹ * (x - z.re)) ^ 2)⁻¹ := by
  unfold poissonKernelHalfPlane
  field_simp
  ring

theorem integrable_poissonKernelHalfPlane {z : ℂ} (hz : 0 < z.im) :
    Integrable (poissonKernelHalfPlane z) :=
  (((integrable_inv_one_add_mul_sq (inv_ne_zero hz.ne')).comp_sub_right z.re).const_mul
    (π⁻¹ * z.im⁻¹)).congr (Eventually.of_forall fun x ↦
      (poissonKernelHalfPlane_eq_inv_one_add_sq hz.ne' x).symm)

/-- The Poisson kernel has total mass one: `∫ P(z, x) dx = 1` for `z ∈ ℍ`. -/
theorem integral_poissonKernelHalfPlane {z : ℂ} (hz : 0 < z.im) :
    ∫ x, poissonKernelHalfPlane z x = 1 := by
  simp_rw [poissonKernelHalfPlane_eq_inv_one_add_sq hz.ne']
  rw [integral_const_mul, integral_sub_right_eq_self (fun x ↦ (1 + (z.im⁻¹ * x) ^ 2)⁻¹) z.re,
    integral_univ_inv_one_add_mul_sq, abs_inv, abs_of_pos hz]
  field_simp

/-- Harmonicity of the Poisson kernel in `z` away from `x`: it is the imaginary part of the
holomorphic function `π⁻¹ (x - z)⁻¹`. -/
theorem harmonicAt_poissonKernelHalfPlane {z : ℂ} {x : ℝ} (h : (x : ℂ) ≠ z) :
    HarmonicAt (fun w ↦ poissonKernelHalfPlane w x) z := by
  simp only [poissonKernelHalfPlane_eq_im]
  exact (analyticAt_const.mul
    ((analyticAt_const.sub analyticAt_id).inv (sub_ne_zero.2 h))).harmonicAt_im

/-!
### Comparison with the Cauchy density `(1 + x²)⁻¹`

For `z` in a compact subset of `ℍ` the Poisson kernel `P(z, x)` and the derivative of the
holomorphic kernel are bounded by a constant times `(1 + x²)⁻¹`, uniformly in `z`; this is the
elementary inequality `1 + x² ≤ (2 + (1 + 2A²)/η²) ((x - a)² + h²)` for `|a| ≤ A`, `0 < η ≤ h`.
-/

/-- Uniform comparison of the Poisson kernel with the Cauchy density: for `|Re z| ≤ A` and
`η ≤ Im z`, `P(z, x) ≤ π⁻¹ Im z (2 + (1 + 2A²)/η²) / (1 + x²)`. -/
theorem poissonKernelHalfPlane_le_div_one_add_sq {z : ℂ} {A η : ℝ} (hη : 0 < η)
    (hA : |z.re| ≤ A) (hz : η ≤ z.im) (x : ℝ) :
    poissonKernelHalfPlane z x ≤ π⁻¹ * z.im * (2 + (1 + 2 * A ^ 2) / η ^ 2) / (1 + x ^ 2) := by
  have hzim : 0 < z.im := hη.trans_le hz
  rw [poissonKernelHalfPlane, div_le_div_iff₀ (by positivity) (by positivity)]
  exact (mul_le_mul_of_nonneg_left (one_add_sq_le_mul_sub_sq_add_sq hη hA hz)
    (by positivity)).trans_eq (by ring)

theorem integrable_const_div_one_add_sq (c : ℝ) : Integrable fun x : ℝ ↦ c / (1 + x ^ 2) := by
  simpa [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul c

/-- A boundary datum `b` with `b(x) / (1 + x²)` integrable is a.e.-strongly measurable. -/
theorem aestronglyMeasurable_of_integrable_div_one_add_sq {b : ℝ → ℝ}
    (hb : Integrable fun x ↦ b x / (1 + x ^ 2)) : AEStronglyMeasurable b volume :=
  (hb.aestronglyMeasurable.mul
    (by fun_prop : Continuous fun x : ℝ ↦ 1 + x ^ 2).aestronglyMeasurable).congr
    (Eventually.of_forall fun x ↦ div_mul_cancel₀ _ (by positivity))

/-!
### The Poisson integral
-/

/-- The Poisson integral `P[b](z) = ∫ P(z, x) b(x) dx` of a boundary datum `b : ℝ → ℝ`. -/
noncomputable def poissonIntegralHalfPlane (b : ℝ → ℝ) (z : ℂ) : ℝ :=
  ∫ x, poissonKernelHalfPlane z x * b x

/-- For `z ∈ ℍ` and `b(x) / (1 + x²)` integrable the Poisson integrand `P(z, x) b(x)` is
integrable. -/
theorem integrable_poissonKernelHalfPlane_mul {b : ℝ → ℝ}
    (hb : Integrable fun x ↦ b x / (1 + x ^ 2)) {z : ℂ} (hz : 0 < z.im) :
    Integrable fun x ↦ poissonKernelHalfPlane z x * b x := by
  refine (hb.norm.const_mul (π⁻¹ * z.im * (2 + (1 + 2 * |z.re| ^ 2) / z.im ^ 2))).mono'
    ((continuous_poissonKernelHalfPlane hz.ne').aestronglyMeasurable.mul
      (aestronglyMeasurable_of_integrable_div_one_add_sq hb)) (Eventually.of_forall fun x ↦ ?_)
  simp only [norm_mul, Real.norm_eq_abs, abs_div, abs_of_pos (poissonKernelHalfPlane_pos hz x),
    abs_of_pos (by positivity : (0 : ℝ) < 1 + x ^ 2)]
  exact (mul_le_mul_of_nonneg_right (poissonKernelHalfPlane_le_div_one_add_sq hz le_rfl le_rfl x)
    (abs_nonneg _)).trans_eq (by ring)

theorem poissonIntegralHalfPlane_const {z : ℂ} (hz : 0 < z.im) (c : ℝ) :
    poissonIntegralHalfPlane (fun _ ↦ c) z = c := by
  simp [poissonIntegralHalfPlane, integral_mul_const, integral_poissonKernelHalfPlane hz]

theorem poissonIntegralHalfPlane_add {b₁ b₂ : ℝ → ℝ} (hb₁ : Integrable fun x ↦ b₁ x / (1 + x ^ 2))
    (hb₂ : Integrable fun x ↦ b₂ x / (1 + x ^ 2)) {z : ℂ} (hz : 0 < z.im) :
    poissonIntegralHalfPlane (b₁ + b₂) z =
      poissonIntegralHalfPlane b₁ z + poissonIntegralHalfPlane b₂ z := by
  simpa [poissonIntegralHalfPlane, mul_add] using integral_add
    (integrable_poissonKernelHalfPlane_mul hb₁ hz) (integrable_poissonKernelHalfPlane_mul hb₂ hz)

/-- The Poisson integral is monotone in the boundary datum. -/
theorem poissonIntegralHalfPlane_mono {b₁ b₂ : ℝ → ℝ} (hb₁ : Integrable fun x ↦ b₁ x / (1 + x ^ 2))
    (hb₂ : Integrable fun x ↦ b₂ x / (1 + x ^ 2)) (h : b₁ ≤ b₂) {z : ℂ} (hz : 0 < z.im) :
    poissonIntegralHalfPlane b₁ z ≤ poissonIntegralHalfPlane b₂ z :=
  integral_mono (integrable_poissonKernelHalfPlane_mul hb₁ hz)
    (integrable_poissonKernelHalfPlane_mul hb₂ hz) fun x ↦
    mul_le_mul_of_nonneg_left (h x) (poissonKernelHalfPlane_pos hz x).le

/-- If `b ≤ M` then `P[b] ≤ M` on `ℍ`. -/
theorem poissonIntegralHalfPlane_le_of_le {b : ℝ → ℝ} (hb : Integrable fun x ↦ b x / (1 + x ^ 2))
    {M : ℝ} (h : ∀ x, b x ≤ M) {z : ℂ} (hz : 0 < z.im) : poissonIntegralHalfPlane b z ≤ M :=
  (poissonIntegralHalfPlane_mono hb (integrable_const_div_one_add_sq M) h hz).trans_eq
    (poissonIntegralHalfPlane_const hz M)

/-- If `M ≤ b` then `M ≤ P[b]` on `ℍ`. -/
theorem le_poissonIntegralHalfPlane_of_le {b : ℝ → ℝ} (hb : Integrable fun x ↦ b x / (1 + x ^ 2))
    {M : ℝ} (h : ∀ x, M ≤ b x) {z : ℂ} (hz : 0 < z.im) : M ≤ poissonIntegralHalfPlane b z :=
  (poissonIntegralHalfPlane_const hz M).symm.trans_le
    (poissonIntegralHalfPlane_mono (integrable_const_div_one_add_sq M) hb h hz)

/-!
### The holomorphic Nevanlinna integral and harmonicity of the Poisson integral

The kernel `(x - z)⁻¹ - x / (1 + x²)` is holomorphic in `z ∈ ℍ`, is `O(x⁻²)` as `x → ±∞` (the
regularizing term `x / (1 + x²)` is real and does not affect the imaginary part), and its
imaginary part is `π P(z, x)`. Hence `π⁻¹ ∫ ((x - z)⁻¹ - x / (1 + x²)) b(x) dx` is holomorphic on
`ℍ` (differentiation under the integral sign) with imaginary part `P[b]`, and `P[b]` is harmonic.
-/

/-- The kernel `(x - z)⁻¹ - x / (1 + x²)` of the Nevanlinna representation of the upper
half-plane. -/
noncomputable def nevanlinnaKernelHalfPlane (z : ℂ) (x : ℝ) : ℂ :=
  ((x : ℂ) - z)⁻¹ - ((x / (1 + x ^ 2) : ℝ) : ℂ)

/-- The imaginary part of the Nevanlinna kernel is `π P(z, x)`. -/
theorem im_nevanlinnaKernelHalfPlane (z : ℂ) (x : ℝ) :
    (nevanlinnaKernelHalfPlane z x).im = π * poissonKernelHalfPlane z x := by
  rw [poissonKernelHalfPlane_eq_im, nevanlinnaKernelHalfPlane, sub_im, ofReal_im, sub_zero,
    im_ofReal_mul, mul_inv_cancel_left₀ Real.pi_ne_zero]

theorem measurable_nevanlinnaKernelHalfPlane (z : ℂ) :
    Measurable (nevanlinnaKernelHalfPlane z) := by
  fun_prop [nevanlinnaKernelHalfPlane]

/-- The closed form `(x - z)⁻¹ - x / (1 + x²) = (z + (1 + z²) / (x - z)) / (1 + x²)`. -/
theorem nevanlinnaKernelHalfPlane_eq {z : ℂ} {x : ℝ} (h : (x : ℂ) ≠ z) :
    nevanlinnaKernelHalfPlane z x = (z + (1 + z ^ 2) / ((x : ℂ) - z)) / (1 + x ^ 2) := by
  have h2 : (1 + (x : ℂ) ^ 2) ≠ 0 := by exact_mod_cast (by positivity : (1 + x ^ 2 : ℝ) ≠ 0)
  unfold nevanlinnaKernelHalfPlane
  push_cast
  field_simp [sub_ne_zero.2 h]
  ring

/-- The bound `‖(x - z)⁻¹ - x / (1 + x²)‖ ≤ (‖z‖ + ‖1 + z²‖ / Im z) / (1 + x²)` for `z ∈ ℍ`. -/
theorem norm_nevanlinnaKernelHalfPlane_le {z : ℂ} (hz : 0 < z.im) (x : ℝ) :
    ‖nevanlinnaKernelHalfPlane z x‖ ≤ (‖z‖ + ‖1 + z ^ 2‖ / z.im) / (1 + x ^ 2) := by
  have hxz : (x : ℂ) ≠ z := fun h ↦ by simp [← h] at hz
  have him : z.im ≤ ‖(x : ℂ) - z‖ := by simpa [abs_of_pos hz] using abs_im_le_norm ((x : ℂ) - z)
  have hn : ‖(1 + (x : ℂ) ^ 2)‖ = 1 + x ^ 2 := by
    exact_mod_cast Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + x ^ 2)
  rw [nevanlinnaKernelHalfPlane_eq hxz, norm_div, hn]
  gcongr
  exact (norm_add_le _ _).trans (by rw [norm_div]; gcongr)

/-- The `z`-derivative of the Nevanlinna kernel is `(x - z)⁻²`. -/
theorem hasDerivAt_nevanlinnaKernelHalfPlane {z : ℂ} {x : ℝ} (h : (x : ℂ) ≠ z) :
    HasDerivAt (fun w ↦ nevanlinnaKernelHalfPlane w x) (((x : ℂ) - z) ^ 2)⁻¹ z :=
  ((((hasDerivAt_id z).const_sub (x : ℂ)).inv (sub_ne_zero.2 h)).sub_const _).congr_deriv
    (by simp)

/-- `‖(x - w)⁻²‖ = ((x - Re w)² + (Im w)²)⁻¹` for real `x`. -/
theorem norm_inv_sq_ofReal_sub (w : ℂ) (x : ℝ) :
    ‖(((x : ℂ) - w) ^ 2)⁻¹‖ = ((x - w.re) ^ 2 + w.im ^ 2)⁻¹ := by
  simp [Complex.sq_norm, normSq_apply, ← sq]

/-- The holomorphic Nevanlinna integral `π⁻¹ ∫ ((x - z)⁻¹ - x / (1 + x²)) b(x) dx`; its
imaginary part on `ℍ` is the Poisson integral of `b`. -/
noncomputable def nevanlinnaIntegralHalfPlane (b : ℝ → ℝ) (z : ℂ) : ℂ :=
  π⁻¹ * ∫ x, nevanlinnaKernelHalfPlane z x * b x

/-- For `z ∈ ℍ` and `b(x) / (1 + x²)` integrable the Nevanlinna integrand is integrable. -/
theorem integrable_nevanlinnaKernelHalfPlane_mul {b : ℝ → ℝ}
    (hb : Integrable fun x ↦ b x / (1 + x ^ 2)) {z : ℂ} (hz : 0 < z.im) :
    Integrable fun x ↦ nevanlinnaKernelHalfPlane z x * (b x : ℂ) := by
  refine (hb.norm.const_mul (‖z‖ + ‖1 + z ^ 2‖ / z.im)).mono'
    ((measurable_nevanlinnaKernelHalfPlane z).aestronglyMeasurable.mul
      (continuous_ofReal.comp_aestronglyMeasurable
        (aestronglyMeasurable_of_integrable_div_one_add_sq hb))) (Eventually.of_forall fun x ↦ ?_)
  rw [norm_mul, norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < 1 + x ^ 2)]
  exact (mul_le_mul_of_nonneg_right (norm_nevanlinnaKernelHalfPlane_le hz x)
    (abs_nonneg _)).trans_eq (by ring)

/-- On `ℍ` the imaginary part of the Nevanlinna integral is the Poisson integral. -/
theorem im_nevanlinnaIntegralHalfPlane {b : ℝ → ℝ} (hb : Integrable fun x ↦ b x / (1 + x ^ 2))
    {z : ℂ} (hz : 0 < z.im) :
    (nevanlinnaIntegralHalfPlane b z).im = poissonIntegralHalfPlane b z := by
  unfold nevanlinnaIntegralHalfPlane poissonIntegralHalfPlane
  rw [im_ofReal_mul, ← RCLike.im_to_complex,
    ← integral_im (integrable_nevanlinnaKernelHalfPlane_mul hb hz)]
  simp [im_nevanlinnaKernelHalfPlane, mul_assoc, integral_const_mul, Real.pi_ne_zero]

/-- The Nevanlinna integral is holomorphic on `ℍ` (differentiation under the integral sign). -/
theorem differentiableAt_nevanlinnaIntegralHalfPlane {b : ℝ → ℝ}
    (hb : Integrable fun x ↦ b x / (1 + x ^ 2)) {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ (nevanlinnaIntegralHalfPlane b) z := by
  set r := z.im / 2 with hr
  have hr0 : 0 < r := by positivity
  set A := |z.re| + r with hA
  set K := 2 + (1 + 2 * A ^ 2) / r ^ 2
  have hball : ∀ w ∈ ball z r, |w.re| ≤ A ∧ r ≤ w.im := fun w hw ↦ by
    have h1 : |w.re - z.re| ≤ ‖w - z‖ := by simpa using abs_re_le_norm (w - z)
    have h2 : |w.im - z.im| ≤ ‖w - z‖ := by simpa using abs_im_le_norm (w - z)
    have hw' : ‖w - z‖ < r := mem_ball_iff_norm.1 hw
    exact ⟨by linarith [abs_sub_abs_le_abs_sub w.re z.re], by linarith [(abs_le.1 h2).1]⟩
  have hmeasb : AEStronglyMeasurable (fun x ↦ (b x : ℂ)) volume :=
    continuous_ofReal.comp_aestronglyMeasurable
      (aestronglyMeasurable_of_integrable_div_one_add_sq hb)
  have hne : ∀ w ∈ ball z r, ∀ x : ℝ, (x : ℂ) ≠ w := fun w hw x h ↦ by
    simpa [← h] using hr0.trans_le (hball w hw).2
  refine DifferentiableAt.const_mul ?_ _
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (𝕜 := ℂ)
    (F' := fun w x ↦ (((x : ℂ) - w) ^ 2)⁻¹ * (b x : ℂ))
    (ball_mem_nhds z hr0) (Eventually.of_forall fun w ↦
      (measurable_nevanlinnaKernelHalfPlane w).aestronglyMeasurable.mul hmeasb)
    (integrable_nevanlinnaKernelHalfPlane_mul hb hz)
    ((by fun_prop : Measurable fun x : ℝ ↦ (((x : ℂ) - z) ^ 2)⁻¹).aestronglyMeasurable.mul hmeasb)
    (Eventually.of_forall fun x w hw ↦ ?_) (hb.norm.const_mul K)
    (Eventually.of_forall fun x w hw ↦
      (hasDerivAt_nevanlinnaKernelHalfPlane (hne w hw x)).mul_const _)).2.differentiableAt
  have hwim : 0 < w.im := hr0.trans_le (hball w hw).2
  rw [norm_mul, norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < 1 + x ^ 2), norm_inv_sq_ofReal_sub, ← mul_div_assoc,
    mul_div_right_comm]
  gcongr
  rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  exact one_add_sq_le_mul_sub_sq_add_sq hr0 (hball w hw).1 (hball w hw).2

/-- The Nevanlinna integral is holomorphic on the upper half-plane. -/
theorem differentiableOn_nevanlinnaIntegralHalfPlane {b : ℝ → ℝ}
    (hb : Integrable fun x ↦ b x / (1 + x ^ 2)) :
    DifferentiableOn ℂ (nevanlinnaIntegralHalfPlane b) {z | 0 < z.im} := fun _ hz ↦
  (differentiableAt_nevanlinnaIntegralHalfPlane hb hz).differentiableWithinAt

/-- **Harmonicity of the Poisson integral**: for `b(x) / (1 + x²)` integrable, `P[b]` is harmonic
on the upper half-plane. -/
theorem harmonicOnNhd_poissonIntegralHalfPlane {b : ℝ → ℝ}
    (hb : Integrable fun x ↦ b x / (1 + x ^ 2)) :
    HarmonicOnNhd (poissonIntegralHalfPlane b) {z | 0 < z.im} := by
  intro z hz
  have hnhds : {z : ℂ | 0 < z.im} ∈ 𝓝 z := UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz
  refine (harmonicAt_congr_nhds ?_).1
    ((differentiableOn_nevanlinnaIntegralHalfPlane hb).analyticAt hnhds).harmonicAt_im
  filter_upwards [hnhds] with w hw using im_nevanlinnaIntegralHalfPlane hb hw

/-!
### Boundary behaviour

At a continuity point `x₀` of `b` the Poisson integral tends to `b(x₀)` as `z → x₀` within `ℍ`
(the Poisson kernel is an approximate identity): the part of `∫ P(z, x) |b(x) - b(x₀)| dx` over
`|x - x₀| < δ` is at most `sup_{|x - x₀| < δ} |b(x) - b(x₀)|` since the kernel has mass one, and
on `|x - x₀| ≥ δ` the kernel is bounded by `4 π⁻¹ Im z (2 + (1 + 2x₀²)/δ²) / (1 + x²)` once
`|Re z - x₀| ≤ δ/2`, so the far part tends to `0` by dominated convergence.
-/

/-- The far-field bound: for `|x - x₀| ≥ δ` and `|Re z - x₀| ≤ δ / 2`,
`P(z, x) ≤ 4 π⁻¹ Im z (2 + (1 + 2 x₀²) / δ²) / (1 + x²)`. -/
theorem poissonKernelHalfPlane_le_of_le_abs_sub {z : ℂ} (hz : 0 < z.im) {x₀ δ x : ℝ}
    (hδ : 0 < δ) (hzre : |z.re - x₀| ≤ δ / 2) (hx : δ ≤ |x - x₀|) :
    poissonKernelHalfPlane z x ≤
      4 * π⁻¹ * z.im * (2 + (1 + 2 * x₀ ^ 2) / δ ^ 2) / (1 + x ^ 2) := by
  have hδ2 : δ ^ 2 ≤ (x - x₀) ^ 2 := by simpa [sq_abs] using pow_le_pow_left₀ hδ.le hx 2
  have h1 : (x - x₀) ^ 2 ≤ 4 * (x - z.re) ^ 2 := by
    have h2 : |x - x₀| ≤ 2 * |x - z.re| := by linarith [abs_sub_le x z.re x₀]
    nlinarith [sq_abs (x - x₀), sq_abs (x - z.re), abs_nonneg (x - x₀), abs_nonneg (x - z.re)]
  have key : 1 + x ^ 2 ≤ 4 * (2 + (1 + 2 * x₀ ^ 2) / δ ^ 2) * ((x - z.re) ^ 2 + z.im ^ 2) := by
    nlinarith [sq_nonneg (x - 2 * x₀), sq_nonneg z.im,
      div_mul_cancel₀ (1 + 2 * x₀ ^ 2) (by positivity : δ ^ 2 ≠ 0),
      div_nonneg (by positivity : (0 : ℝ) ≤ 1 + 2 * x₀ ^ 2) (sq_nonneg δ)]
  rw [poissonKernelHalfPlane, div_le_div_iff₀ (by positivity) (by positivity)]
  exact (mul_le_mul_of_nonneg_left key (by positivity)).trans_eq (by ring)

/-- The Poisson kernel `P(z, x)` tends to `0` as `z → x₀` for `x ≠ x₀`. -/
theorem tendsto_poissonKernelHalfPlane_nhds_ofReal {x₀ x : ℝ} (h : x ≠ x₀) :
    Tendsto (fun z ↦ poissonKernelHalfPlane z x) (𝓝 (x₀ : ℂ)) (𝓝 0) := by
  simpa [poissonKernelHalfPlane] using
    (continuousAt_poissonKernelHalfPlane (ofReal_injective.ne h)).tendsto

/-- **Boundary behaviour of the Poisson integral**: at a continuity point `x₀` of `b`,
`P[b](z) → b(x₀)` as `z → x₀` within the upper half-plane. -/
theorem tendsto_poissonIntegralHalfPlane_of_continuousAt {b : ℝ → ℝ}
    (hb : Integrable fun x ↦ b x / (1 + x ^ 2)) {x₀ : ℝ} (hcont : ContinuousAt b x₀) :
    Tendsto (poissonIntegralHalfPlane b) (𝓝[{z | 0 < z.im}] (x₀ : ℂ)) (𝓝 (b x₀)) := by
  set l := 𝓝[{z : ℂ | 0 < z.im}] (x₀ : ℂ)
  have habs : Integrable fun x ↦ |b x - b x₀| / (1 + x ^ 2) :=
    (hb.sub (integrable_const_div_one_add_sq (b x₀))).abs.congr (Eventually.of_forall fun x ↦ by
      simp [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 1 + x ^ 2), ← sub_div])
  have hmem : ∀ᶠ z in l, 0 < z.im := self_mem_nhdsWithin
  -- the deviation `|P[b](z) - b(x₀)|` is at most `∫ P(z, x) |b(x) - b(x₀)| dx`
  have hle : ∀ z : ℂ, 0 < z.im → |poissonIntegralHalfPlane b z - b x₀| ≤
      ∫ x, poissonKernelHalfPlane z x * |b x - b x₀| := fun z hz ↦ by
    have e : ∫ x, poissonKernelHalfPlane z x * (b x - b x₀) =
        poissonIntegralHalfPlane b z - b x₀ := by
      simp [mul_sub, integral_sub (integrable_poissonKernelHalfPlane_mul hb hz)
        ((integrable_poissonKernelHalfPlane hz).mul_const _), integral_mul_const,
        integral_poissonKernelHalfPlane hz, poissonIntegralHalfPlane]
    rw [← e]
    exact abs_integral_le_integral_abs.trans (integral_congr_ae (Eventually.of_forall fun x ↦ by
      simp [abs_of_pos (poissonKernelHalfPlane_pos hz x)])).le
  -- the deviation tends to `0`
  have hE : Tendsto (fun z ↦ ∫ x, poissonKernelHalfPlane z x * |b x - b x₀|) l (𝓝 0) := by
    rw [tendsto_order]
    refine ⟨fun a ha ↦ hmem.mono fun z hz ↦ ha.trans_le (integral_nonneg fun x ↦
      mul_nonneg (poissonKernelHalfPlane_pos hz x).le (abs_nonneg _)), fun ε hε ↦ ?_⟩
    obtain ⟨δ, hδ, hδb⟩ := Metric.continuousAt_iff.1 hcont (ε / 2) (by positivity)
    set K := 4 * π⁻¹ * (2 + (1 + 2 * x₀ ^ 2) / δ ^ 2)
    have hnear : ∀ᶠ z in l, |z.re - x₀| ≤ δ / 2 ∧ z.im ≤ 1 := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds
        (ball_mem_nhds (x₀ : ℂ) (lt_min (half_pos hδ) one_pos))] with z hz
      have h1 : |z.re - x₀| ≤ ‖z - x₀‖ := by simpa using abs_re_le_norm (z - x₀)
      have h2 : |z.im| ≤ ‖z - x₀‖ := by simpa using abs_im_le_norm (z - x₀)
      obtain ⟨hz1, hz2⟩ := lt_min_iff.1 (mem_ball_iff_norm.1 hz)
      exact ⟨h1.trans hz1.le, (le_abs_self _).trans (h2.trans hz2.le)⟩
    -- the far part tends to `0` by dominated convergence
    have hfar : Tendsto (fun z ↦ ∫ x in (ball x₀ δ)ᶜ, poissonKernelHalfPlane z x * |b x - b x₀|) l
        (𝓝 0) := by
      refine (tendsto_integral_filter_of_dominated_convergence
        (F := fun z x ↦ poissonKernelHalfPlane z x * |b x - b x₀|) (f := fun _ ↦ 0)
        (fun x ↦ K * (|b x - b x₀| / (1 + x ^ 2))) (Eventually.of_forall fun z ↦
          ((measurable_poissonKernelHalfPlane z).aestronglyMeasurable.mul
            ((aestronglyMeasurable_of_integrable_div_one_add_sq hb).sub
              aestronglyMeasurable_const).norm).restrict)
        ?_ (habs.const_mul K).integrableOn ?_).mono_right (by simp)
      · filter_upwards [hmem, hnear] with z hz hz'
        filter_upwards [ae_restrict_mem measurableSet_ball.compl] with x hx
        have hx' : δ ≤ |x - x₀| := by simpa [Real.dist_eq] using hx
        have hP : poissonKernelHalfPlane z x ≤ K / (1 + x ^ 2) :=
          (poissonKernelHalfPlane_le_of_le_abs_sub hz hδ hz'.1 hx').trans
            (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_of_le_one_right (by positivity) hz'.2) (by positivity)) (by positivity))
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (poissonKernelHalfPlane_pos hz x), abs_abs]
        exact (mul_le_mul_of_nonneg_right hP (abs_nonneg _)).trans_eq (by ring)
      · filter_upwards [ae_restrict_mem measurableSet_ball.compl] with x hx
        have hx' : x ≠ x₀ := fun h ↦ hx (by simp [h, hδ])
        simpa using ((tendsto_poissonKernelHalfPlane_nhds_ofReal hx').mono_left
          nhdsWithin_le_nhds).mul_const |b x - b x₀|
    filter_upwards [hmem, (tendsto_order.1 hfar).2 (ε / 2) (by positivity)] with z hz hfarz
    have hint : Integrable fun x ↦ poissonKernelHalfPlane z x * |b x - b x₀| :=
      integrable_poissonKernelHalfPlane_mul habs hz
    have hnear : ∫ x in ball x₀ δ, poissonKernelHalfPlane z x * |b x - b x₀| ≤ ε / 2 := by
      calc ∫ x in ball x₀ δ, poissonKernelHalfPlane z x * |b x - b x₀|
          ≤ ∫ x in ball x₀ δ, poissonKernelHalfPlane z x * (ε / 2) :=
            setIntegral_mono_on hint.integrableOn
              ((integrable_poissonKernelHalfPlane hz).mul_const _).integrableOn measurableSet_ball
              fun x hx ↦ mul_le_mul_of_nonneg_left
                (by simpa [Real.dist_eq] using (hδb (mem_ball.1 hx)).le)
                (poissonKernelHalfPlane_pos hz x).le
        _ ≤ ∫ x, poissonKernelHalfPlane z x * (ε / 2) :=
            setIntegral_le_integral ((integrable_poissonKernelHalfPlane hz).mul_const _)
              (Eventually.of_forall fun x ↦
                (mul_pos (poissonKernelHalfPlane_pos hz x) (by positivity)).le)
        _ = ε / 2 := by rw [integral_mul_const, integral_poissonKernelHalfPlane hz, one_mul]
    rw [← integral_add_compl (measurableSet_ball (x := x₀) (ε := δ)) hint]
    linarith
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun z ↦ norm_nonneg _)
    (hmem.mono fun z hz ↦ (Real.norm_eq_abs _).trans_le (hle z hz)) hE

/-!
### Truncation from below

For boundary data bounded above but not below one truncates to `max b (-n)`; the Poisson
integrals of the truncations converge to `P[b]` (dominated convergence with the majorant
`P(z, x) |b(x)|`, since `|max (b x) (-n)| ≤ |b x|`).
-/

/-- The truncations `max b (-c)` of an admissible boundary datum are admissible. -/
theorem integrable_max_neg_div_one_add_sq {b : ℝ → ℝ} (hb : Integrable fun x ↦ b x / (1 + x ^ 2))
    (c : ℝ) : Integrable fun x ↦ max (b x) (-c) / (1 + x ^ 2) :=
  (hb.sup (integrable_const_div_one_add_sq (-c))).congr
    (Eventually.of_forall fun x ↦ max_div_div_right (by positivity) _ _)

/-- **Monotone limit of the truncations**: `P[max b (-n)](z) → P[b](z)` as `n → ∞` for `z ∈ ℍ`. -/
theorem tendsto_poissonIntegralHalfPlane_max {b : ℝ → ℝ}
    (hb : Integrable fun x ↦ b x / (1 + x ^ 2)) {z : ℂ} (hz : 0 < z.im) :
    Tendsto (fun n : ℕ ↦ poissonIntegralHalfPlane (fun x ↦ max (b x) (-(n : ℝ))) z) atTop
      (𝓝 (poissonIntegralHalfPlane b z)) := by
  refine tendsto_integral_of_dominated_convergence (fun x ↦ ‖poissonKernelHalfPlane z x * b x‖)
    (fun n ↦ (integrable_poissonKernelHalfPlane_mul
      (integrable_max_neg_div_one_add_sq hb n) hz).aestronglyMeasurable)
    (integrable_poissonKernelHalfPlane_mul hb hz).norm
    (fun n ↦ Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall fun x ↦ ?_)
  · simp only [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_max_neg_le_abs n.cast_nonneg) (abs_nonneg _)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (-b x)] with n hn
    rw [max_eq_left (by linarith)]

end Complex
