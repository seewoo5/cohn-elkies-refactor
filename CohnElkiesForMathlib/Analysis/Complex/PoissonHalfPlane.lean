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
  have h1 : 1 + x ^ 2 ≤ 2 * (x - a) ^ 2 + (1 + 2 * a ^ 2) := by nlinarith [sq_nonneg (x - 2 * a)]
  have h2 : a ^ 2 ≤ A ^ 2 := by simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg a) ha 2
  have h3 : 1 + 2 * A ^ 2 ≤ (1 + 2 * A ^ 2) / η ^ 2 * h ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have : η ^ 2 ≤ h ^ 2 := pow_le_pow_left₀ hη.le hh 2
    nlinarith
  have h4 : 0 ≤ (1 + 2 * A ^ 2) / η ^ 2 * (x - a) ^ 2 := by positivity
  nlinarith

/-- Truncating from below does not increase the absolute value: `|max a (-c)| ≤ |a|` for
`0 ≤ c`. -/
theorem abs_max_neg_le_abs {a c : ℝ} (hc : 0 ≤ c) : |max a (-c)| ≤ |a| := by
  rcases le_total (-c) a with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h, abs_neg, abs_of_nonneg hc, abs_of_nonpos (h.trans (by linarith))]
    linarith

namespace Complex

/-- The Poisson kernel `P(z, x) = π⁻¹ Im z / ((x - Re z)² + (Im z)²)` of the upper half-plane. -/
noncomputable def poissonKernelHalfPlane (z : ℂ) (x : ℝ) : ℝ :=
  π⁻¹ * z.im / ((x - z.re) ^ 2 + z.im ^ 2)

theorem poissonKernelHalfPlane_pos {z : ℂ} (hz : 0 < z.im) (x : ℝ) :
    0 < poissonKernelHalfPlane z x := by
  unfold poissonKernelHalfPlane
  positivity

theorem poissonKernelHalfPlane_nonneg {z : ℂ} (hz : 0 ≤ z.im) (x : ℝ) :
    0 ≤ poissonKernelHalfPlane z x := by
  unfold poissonKernelHalfPlane
  positivity

/-- The Poisson kernel is the imaginary part of the holomorphic function `π⁻¹ (x - z)⁻¹`. -/
theorem poissonKernelHalfPlane_eq_im (z : ℂ) (x : ℝ) :
    poissonKernelHalfPlane z x = (π⁻¹ * ((x : ℂ) - z)⁻¹).im := by
  simp [poissonKernelHalfPlane, normSq_apply, mul_div_assoc, sq]

/-- The uniform bound `P(z, x) ≤ π⁻¹ / Im z`. -/
theorem poissonKernelHalfPlane_le {z : ℂ} (hz : 0 < z.im) (x : ℝ) :
    poissonKernelHalfPlane z x ≤ π⁻¹ * z.im⁻¹ := by
  unfold poissonKernelHalfPlane
  calc π⁻¹ * z.im / ((x - z.re) ^ 2 + z.im ^ 2) ≤ π⁻¹ * z.im / z.im ^ 2 := by
        gcongr
        exact le_add_of_nonneg_left (sq_nonneg _)
    _ = π⁻¹ * z.im⁻¹ := by field_simp

theorem measurable_poissonKernelHalfPlane (z : ℂ) : Measurable (poissonKernelHalfPlane z) := by
  unfold poissonKernelHalfPlane
  fun_prop

theorem continuous_poissonKernelHalfPlane {z : ℂ} (hz : z.im ≠ 0) :
    Continuous (poissonKernelHalfPlane z) := by
  unfold poissonKernelHalfPlane
  exact continuous_const.div (by fun_prop) fun x ↦ by positivity

/-- For `x ≠ z` the Poisson kernel is continuous in `z`. -/
theorem continuousAt_poissonKernelHalfPlane {z : ℂ} {x : ℝ} (h : (x : ℂ) ≠ z) :
    ContinuousAt (fun w ↦ poissonKernelHalfPlane w x) z := by
  have hne : (x - z.re) ^ 2 + z.im ^ 2 ≠ 0 := by
    intro h0
    apply h
    have hre : x - z.re = 0 := by nlinarith [sq_nonneg (x - z.re), sq_nonneg z.im]
    have him : z.im = 0 := by nlinarith [sq_nonneg (x - z.re), sq_nonneg z.im]
    exact Complex.ext (by simpa using sub_eq_zero.1 hre) (by simpa using him.symm)
  unfold poissonKernelHalfPlane
  exact (continuousAt_const.mul continuous_im.continuousAt).div (by fun_prop) hne

/-- The Poisson kernel in the form `π⁻¹ (Im z)⁻¹ (1 + ((Im z)⁻¹ (x - Re z))²)⁻¹` adapted to the
substitution `x = Re z + Im z · t`. -/
theorem poissonKernelHalfPlane_eq_inv_one_add_sq {z : ℂ} (hz : z.im ≠ 0) (x : ℝ) :
    poissonKernelHalfPlane z x = π⁻¹ * z.im⁻¹ * (1 + (z.im⁻¹ * (x - z.re)) ^ 2)⁻¹ := by
  unfold poissonKernelHalfPlane
  field_simp
  ring

theorem integrable_poissonKernelHalfPlane {z : ℂ} (hz : 0 < z.im) :
    Integrable (poissonKernelHalfPlane z) := by
  have h := ((integrable_inv_one_add_mul_sq (inv_ne_zero hz.ne')).comp_sub_right z.re).const_mul
    (π⁻¹ * z.im⁻¹)
  exact h.congr (Eventually.of_forall fun x ↦
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
  have ha : AnalyticAt ℂ (fun w : ℂ ↦ π⁻¹ * ((x : ℂ) - w)⁻¹) z :=
    analyticAt_const.mul ((analyticAt_const.sub analyticAt_id).inv (sub_ne_zero.2 h))
  have e : (fun w ↦ poissonKernelHalfPlane w x) = fun w ↦ (π⁻¹ * ((x : ℂ) - w)⁻¹).im :=
    funext fun w ↦ poissonKernelHalfPlane_eq_im w x
  rw [e]
  exact ha.harmonicAt_im

theorem harmonicOnNhd_poissonKernelHalfPlane (x : ℝ) :
    HarmonicOnNhd (fun w ↦ poissonKernelHalfPlane w x) {z | 0 < z.im} := fun z hz ↦
  harmonicAt_poissonKernelHalfPlane fun h ↦ by
    have : (0 : ℝ) < z.im := hz
    rw [← h] at this
    simp at this

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
  unfold poissonKernelHalfPlane
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc π⁻¹ * z.im * (1 + x ^ 2)
      ≤ π⁻¹ * z.im * ((2 + (1 + 2 * A ^ 2) / η ^ 2) * ((x - z.re) ^ 2 + z.im ^ 2)) := by
        gcongr
        exact one_add_sq_le_mul_sub_sq_add_sq hη hA hz
    _ = _ := by ring

theorem integrable_const_div_one_add_sq (c : ℝ) : Integrable fun x : ℝ ↦ c / (1 + x ^ 2) := by
  simpa [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul c

/-- A boundary datum `b` with `b(x) / (1 + x²)` integrable is a.e.-strongly measurable. -/
theorem aestronglyMeasurable_of_integrable_div_one_add_sq {b : ℝ → ℝ}
    (hb : Integrable fun x ↦ b x / (1 + x ^ 2)) : AEStronglyMeasurable b volume := by
  have := hb.aestronglyMeasurable.mul
    (by fun_prop : Continuous fun x : ℝ ↦ 1 + x ^ 2).aestronglyMeasurable
  refine this.congr (Eventually.of_forall fun x ↦ ?_)
  change b x / (1 + x ^ 2) * (1 + x ^ 2) = b x
  field_simp

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
  set C := π⁻¹ * z.im * (2 + (1 + 2 * |z.re| ^ 2) / z.im ^ 2) with hC
  refine (hb.norm.const_mul C).mono'
    ((continuous_poissonKernelHalfPlane hz.ne').aestronglyMeasurable.mul
      (aestronglyMeasurable_of_integrable_div_one_add_sq hb)) (Eventually.of_forall fun x ↦ ?_)
  simp only [norm_mul, Real.norm_eq_abs, abs_div, abs_of_pos (poissonKernelHalfPlane_pos hz x),
    abs_of_pos (by positivity : (0 : ℝ) < 1 + x ^ 2)]
  rw [← mul_div_assoc, mul_div_right_comm]
  gcongr
  exact poissonKernelHalfPlane_le_div_one_add_sq hz le_rfl le_rfl x

theorem poissonIntegralHalfPlane_const {z : ℂ} (hz : 0 < z.im) (c : ℝ) :
    poissonIntegralHalfPlane (fun _ ↦ c) z = c := by
  simp [poissonIntegralHalfPlane, integral_mul_const, integral_poissonKernelHalfPlane hz]

theorem poissonIntegralHalfPlane_add {b₁ b₂ : ℝ → ℝ} (hb₁ : Integrable fun x ↦ b₁ x / (1 + x ^ 2))
    (hb₂ : Integrable fun x ↦ b₂ x / (1 + x ^ 2)) {z : ℂ} (hz : 0 < z.im) :
    poissonIntegralHalfPlane (b₁ + b₂) z =
      poissonIntegralHalfPlane b₁ z + poissonIntegralHalfPlane b₂ z := by
  simp only [poissonIntegralHalfPlane, Pi.add_apply, mul_add]
  exact integral_add (integrable_poissonKernelHalfPlane_mul hb₁ hz)
    (integrable_poissonKernelHalfPlane_mul hb₂ hz)

theorem poissonIntegralHalfPlane_neg (b : ℝ → ℝ) (z : ℂ) :
    poissonIntegralHalfPlane (-b) z = -poissonIntegralHalfPlane b z := by
  simp [poissonIntegralHalfPlane, integral_neg]

theorem poissonIntegralHalfPlane_sub {b₁ b₂ : ℝ → ℝ} (hb₁ : Integrable fun x ↦ b₁ x / (1 + x ^ 2))
    (hb₂ : Integrable fun x ↦ b₂ x / (1 + x ^ 2)) {z : ℂ} (hz : 0 < z.im) :
    poissonIntegralHalfPlane (b₁ - b₂) z =
      poissonIntegralHalfPlane b₁ z - poissonIntegralHalfPlane b₂ z := by
  simp only [poissonIntegralHalfPlane, Pi.sub_apply, mul_sub]
  exact integral_sub (integrable_poissonKernelHalfPlane_mul hb₁ hz)
    (integrable_poissonKernelHalfPlane_mul hb₂ hz)

theorem poissonIntegralHalfPlane_const_mul (c : ℝ) (b : ℝ → ℝ) (z : ℂ) :
    poissonIntegralHalfPlane (fun x ↦ c * b x) z = c * poissonIntegralHalfPlane b z := by
  simp [poissonIntegralHalfPlane, ← integral_const_mul, mul_left_comm]

/-- The Poisson integral is monotone in the boundary datum. -/
theorem poissonIntegralHalfPlane_mono {b₁ b₂ : ℝ → ℝ} (hb₁ : Integrable fun x ↦ b₁ x / (1 + x ^ 2))
    (hb₂ : Integrable fun x ↦ b₂ x / (1 + x ^ 2)) (h : b₁ ≤ b₂) {z : ℂ} (hz : 0 < z.im) :
    poissonIntegralHalfPlane b₁ z ≤ poissonIntegralHalfPlane b₂ z :=
  integral_mono (integrable_poissonKernelHalfPlane_mul hb₁ hz)
    (integrable_poissonKernelHalfPlane_mul hb₂ hz) fun x ↦
    mul_le_mul_of_nonneg_left (h x) (poissonKernelHalfPlane_pos hz x).le

/-- If `b ≤ M` then `P[b] ≤ M` on `ℍ`. -/
theorem poissonIntegralHalfPlane_le_of_le {b : ℝ → ℝ} (hb : Integrable fun x ↦ b x / (1 + x ^ 2))
    {M : ℝ} (h : ∀ x, b x ≤ M) {z : ℂ} (hz : 0 < z.im) : poissonIntegralHalfPlane b z ≤ M := by
  simpa [poissonIntegralHalfPlane_const hz] using
    poissonIntegralHalfPlane_mono hb (integrable_const_div_one_add_sq M) h hz

/-- If `M ≤ b` then `M ≤ P[b]` on `ℍ`. -/
theorem le_poissonIntegralHalfPlane_of_le {b : ℝ → ℝ} (hb : Integrable fun x ↦ b x / (1 + x ^ 2))
    {M : ℝ} (h : ∀ x, M ≤ b x) {z : ℂ} (hz : 0 < z.im) : M ≤ poissonIntegralHalfPlane b z := by
  simpa [poissonIntegralHalfPlane_const hz] using
    poissonIntegralHalfPlane_mono (integrable_const_div_one_add_sq M) hb h hz

/-- If `|b| ≤ M` then `|P[b]| ≤ M` on `ℍ`. -/
theorem abs_poissonIntegralHalfPlane_le {b : ℝ → ℝ} (hb : Integrable fun x ↦ b x / (1 + x ^ 2))
    {M : ℝ} (h : ∀ x, |b x| ≤ M) {z : ℂ} (hz : 0 < z.im) :
    |poissonIntegralHalfPlane b z| ≤ M :=
  abs_le.2 ⟨le_poissonIntegralHalfPlane_of_le hb (fun x ↦ (abs_le.1 (h x)).1) hz,
    poissonIntegralHalfPlane_le_of_le hb (fun x ↦ (abs_le.1 (h x)).2) hz⟩

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

theorem im_nevanlinnaKernelHalfPlane (z : ℂ) (x : ℝ) :
    (nevanlinnaKernelHalfPlane z x).im = π * poissonKernelHalfPlane z x := by
  rw [poissonKernelHalfPlane_eq_im, nevanlinnaKernelHalfPlane, sub_im, ofReal_im, sub_zero,
    im_ofReal_mul, mul_inv_cancel_left₀ Real.pi_ne_zero]

theorem measurable_nevanlinnaKernelHalfPlane (z : ℂ) :
    Measurable (nevanlinnaKernelHalfPlane z) := by
  unfold nevanlinnaKernelHalfPlane
  fun_prop

/-- The closed form `(x - z)⁻¹ - x / (1 + x²) = (z + (1 + z²) / (x - z)) / (1 + x²)`. -/
theorem nevanlinnaKernelHalfPlane_eq {z : ℂ} {x : ℝ} (h : (x : ℂ) ≠ z) :
    nevanlinnaKernelHalfPlane z x = (z + (1 + z ^ 2) / ((x : ℂ) - z)) / (1 + x ^ 2) := by
  have h' : (x : ℂ) - z ≠ 0 := sub_ne_zero.2 h
  have h2 : (1 + (x : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast (by positivity : (1 + x ^ 2 : ℝ) ≠ 0)
  unfold nevanlinnaKernelHalfPlane
  push_cast
  field_simp
  ring

/-- The bound `‖(x - z)⁻¹ - x / (1 + x²)‖ ≤ (‖z‖ + ‖1 + z²‖ / Im z) / (1 + x²)` for `z ∈ ℍ`. -/
theorem norm_nevanlinnaKernelHalfPlane_le {z : ℂ} (hz : 0 < z.im) (x : ℝ) :
    ‖nevanlinnaKernelHalfPlane z x‖ ≤ (‖z‖ + ‖1 + z ^ 2‖ / z.im) / (1 + x ^ 2) := by
  have hxz : (x : ℂ) ≠ z := fun h ↦ by rw [← h] at hz; simp at hz
  have him : z.im ≤ ‖(x : ℂ) - z‖ := by
    simpa [abs_of_pos hz] using abs_im_le_norm ((x : ℂ) - z)
  have hn : ‖(1 + (x : ℂ) ^ 2)‖ = 1 + x ^ 2 := by
    rw [show (1 + (x : ℂ) ^ 2) = ((1 + x ^ 2 : ℝ) : ℂ) by push_cast; rfl, norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [nevanlinnaKernelHalfPlane_eq hxz, norm_div, hn]
  gcongr
  calc ‖z + (1 + z ^ 2) / ((x : ℂ) - z)‖ ≤ ‖z‖ + ‖(1 + z ^ 2) / ((x : ℂ) - z)‖ := norm_add_le _ _
    _ = ‖z‖ + ‖1 + z ^ 2‖ / ‖(x : ℂ) - z‖ := by rw [norm_div]
    _ ≤ ‖z‖ + ‖1 + z ^ 2‖ / z.im := by gcongr

/-- The `z`-derivative of the Nevanlinna kernel is `(x - z)⁻²`. -/
theorem hasDerivAt_nevanlinnaKernelHalfPlane {z : ℂ} {x : ℝ} (h : (x : ℂ) ≠ z) :
    HasDerivAt (fun w ↦ nevanlinnaKernelHalfPlane w x) (((x : ℂ) - z) ^ 2)⁻¹ z := by
  have h1 : HasDerivAt (fun w : ℂ ↦ ((x : ℂ) - w)⁻¹) (-(-1) / ((x : ℂ) - z) ^ 2) z :=
    ((hasDerivAt_id z).const_sub (x : ℂ)).inv (sub_ne_zero.2 h)
  have h2 := h1.sub_const ((x / (1 + x ^ 2) : ℝ) : ℂ)
  rw [neg_neg, one_div] at h2
  exact h2

/-- `‖(x - w)⁻²‖ = ((x - Re w)² + (Im w)²)⁻¹` for real `x`. -/
theorem norm_inv_sq_ofReal_sub (w : ℂ) (x : ℝ) :
    ‖(((x : ℂ) - w) ^ 2)⁻¹‖ = ((x - w.re) ^ 2 + w.im ^ 2)⁻¹ := by
  rw [norm_inv, norm_pow, Complex.sq_norm, normSq_apply]
  simp [sq]

/-- The holomorphic Nevanlinna integral `π⁻¹ ∫ ((x - z)⁻¹ - x / (1 + x²)) b(x) dx`; its
imaginary part on `ℍ` is the Poisson integral of `b`. -/
noncomputable def nevanlinnaIntegralHalfPlane (b : ℝ → ℝ) (z : ℂ) : ℂ :=
  π⁻¹ * ∫ x, nevanlinnaKernelHalfPlane z x * b x

theorem integrable_nevanlinnaKernelHalfPlane_mul {b : ℝ → ℝ}
    (hb : Integrable fun x ↦ b x / (1 + x ^ 2)) {z : ℂ} (hz : 0 < z.im) :
    Integrable fun x ↦ nevanlinnaKernelHalfPlane z x * (b x : ℂ) := by
  refine (hb.norm.const_mul (‖z‖ + ‖1 + z ^ 2‖ / z.im)).mono'
    ((measurable_nevanlinnaKernelHalfPlane z).aestronglyMeasurable.mul
      (continuous_ofReal.comp_aestronglyMeasurable
        (aestronglyMeasurable_of_integrable_div_one_add_sq hb))) (Eventually.of_forall fun x ↦ ?_)
  rw [norm_mul, norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < 1 + x ^ 2), ← mul_div_assoc, mul_div_right_comm]
  gcongr
  exact norm_nevanlinnaKernelHalfPlane_le hz x

/-- On `ℍ` the imaginary part of the Nevanlinna integral is the Poisson integral. -/
theorem im_nevanlinnaIntegralHalfPlane {b : ℝ → ℝ} (hb : Integrable fun x ↦ b x / (1 + x ^ 2))
    {z : ℂ} (hz : 0 < z.im) :
    (nevanlinnaIntegralHalfPlane b z).im = poissonIntegralHalfPlane b z := by
  have h := integral_im (integrable_nevanlinnaKernelHalfPlane_mul hb hz)
  change ∫ x, (nevanlinnaKernelHalfPlane z x * (b x : ℂ)).im =
    (∫ x, nevanlinnaKernelHalfPlane z x * (b x : ℂ)).im at h
  unfold nevanlinnaIntegralHalfPlane poissonIntegralHalfPlane
  rw [im_ofReal_mul, ← h]
  simp_rw [mul_im, ofReal_re, ofReal_im, mul_zero, zero_add, im_nevanlinnaKernelHalfPlane,
    mul_assoc, integral_const_mul, inv_mul_cancel_left₀ Real.pi_ne_zero]

/-- The Nevanlinna integral is holomorphic on `ℍ` (differentiation under the integral sign). -/
theorem differentiableAt_nevanlinnaIntegralHalfPlane {b : ℝ → ℝ}
    (hb : Integrable fun x ↦ b x / (1 + x ^ 2)) {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ (nevanlinnaIntegralHalfPlane b) z := by
  set r := z.im / 2 with hr
  have hr0 : 0 < r := by positivity
  set A := |z.re| + r with hA
  set K := 2 + (1 + 2 * A ^ 2) / r ^ 2 with hK
  have hball : ∀ w ∈ ball z r, |w.re| ≤ A ∧ r ≤ w.im := fun w hw ↦ by
    have h1 : |w.re - z.re| ≤ ‖w - z‖ := by simpa using abs_re_le_norm (w - z)
    have h2 : |w.im - z.im| ≤ ‖w - z‖ := by simpa using abs_im_le_norm (w - z)
    have hw' : ‖w - z‖ < r := mem_ball_iff_norm.1 hw
    constructor
    · calc |w.re| ≤ |z.re| + |w.re - z.re| := by
            simpa using abs_add_le z.re (w.re - z.re)
        _ ≤ A := by rw [hA]; linarith
    · have := (abs_le.1 (h2.trans hw'.le)).1
      rw [hr] at this ⊢
      linarith
  have hmeasb : AEStronglyMeasurable (fun x ↦ (b x : ℂ)) volume :=
    continuous_ofReal.comp_aestronglyMeasurable
      (aestronglyMeasurable_of_integrable_div_one_add_sq hb)
  have hne : ∀ w ∈ ball z r, ∀ x : ℝ, (x : ℂ) ≠ w := fun w hw x h ↦ by
    have := (hball w hw).2
    rw [← h] at this
    simp at this
    linarith
  unfold nevanlinnaIntegralHalfPlane
  refine DifferentiableAt.const_mul ?_ _
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (𝕜 := ℂ)
    (F := fun w x ↦ nevanlinnaKernelHalfPlane w x * (b x : ℂ))
    (F' := fun w x ↦ (((x : ℂ) - w) ^ 2)⁻¹ * (b x : ℂ))
    (bound := fun x ↦ K * (|b x| / (1 + x ^ 2)))
    (ball_mem_nhds z hr0) (Eventually.of_forall fun w ↦
      (measurable_nevanlinnaKernelHalfPlane w).aestronglyMeasurable.mul hmeasb)
    (integrable_nevanlinnaKernelHalfPlane_mul hb hz)
    ((by fun_prop : Measurable fun x : ℝ ↦ (((x : ℂ) - z) ^ 2)⁻¹).aestronglyMeasurable.mul hmeasb)
    (Eventually.of_forall fun x w hw ↦ ?_) ?_
    (Eventually.of_forall fun x w hw ↦
      (hasDerivAt_nevanlinnaKernelHalfPlane (hne w hw x)).mul_const _)).2.differentiableAt
  · have hwim : 0 < w.im := hr0.trans_le (hball w hw).2
    rw [norm_mul, norm_real, Real.norm_eq_abs, norm_inv_sq_ofReal_sub, ← mul_div_assoc,
      mul_div_right_comm]
    gcongr
    rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    exact one_add_sq_le_mul_sub_sq_add_sq hr0 (hball w hw).1 (hball w hw).2
  · have := hb.norm.const_mul K
    refine this.congr (Eventually.of_forall fun x ↦ ?_)
    simp only [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 1 + x ^ 2)]

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
  have ha : AnalyticAt ℂ (nevanlinnaIntegralHalfPlane b) z :=
    (differentiableOn_nevanlinnaIntegralHalfPlane hb).analyticAt hnhds
  refine (harmonicAt_congr_nhds ?_).1 ha.harmonicAt_im
  filter_upwards [hnhds] with w hw
  exact im_nevanlinnaIntegralHalfPlane hb hw

theorem continuousOn_poissonIntegralHalfPlane {b : ℝ → ℝ}
    (hb : Integrable fun x ↦ b x / (1 + x ^ 2)) :
    ContinuousOn (poissonIntegralHalfPlane b) {z | 0 < z.im} :=
  (harmonicOnNhd_poissonIntegralHalfPlane hb).continuousOn

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
  set K := 2 + (1 + 2 * x₀ ^ 2) / δ ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have h1 : (x - x₀) ^ 2 ≤ 4 * (x - z.re) ^ 2 := by
    have h2 : |x - x₀| ≤ 2 * |x - z.re| := by linarith [abs_sub_le x z.re x₀]
    nlinarith [sq_abs (x - x₀), sq_abs (x - z.re), abs_nonneg (x - x₀), abs_nonneg (x - z.re)]
  have h3 : 1 + x ^ 2 ≤ K * (x - x₀) ^ 2 := by
    have hδ2 : δ ^ 2 ≤ (x - x₀) ^ 2 := by simpa [sq_abs] using pow_le_pow_left₀ hδ.le hx 2
    have e1 : 1 + x ^ 2 ≤ 2 * (x - x₀) ^ 2 + (1 + 2 * x₀ ^ 2) := by
      nlinarith [sq_nonneg (x - 2 * x₀)]
    have e2 : 1 + 2 * x₀ ^ 2 ≤ (1 + 2 * x₀ ^ 2) / δ ^ 2 * (x - x₀) ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    rw [hK]
    nlinarith
  unfold poissonKernelHalfPlane
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc π⁻¹ * z.im * (1 + x ^ 2) ≤ π⁻¹ * z.im * (K * (4 * (x - z.re) ^ 2)) := by
        gcongr
        exact h3.trans (mul_le_mul_of_nonneg_left h1 hK0)
    _ ≤ π⁻¹ * z.im * (K * (4 * ((x - z.re) ^ 2 + z.im ^ 2))) := by
        gcongr
        linarith [sq_nonneg z.im]
    _ = 4 * π⁻¹ * z.im * K * ((x - z.re) ^ 2 + z.im ^ 2) := by ring

/-- The Poisson kernel `P(z, x)` tends to `0` as `z → x₀` for `x ≠ x₀`. -/
theorem tendsto_poissonKernelHalfPlane_nhds_ofReal {x₀ x : ℝ} (h : x ≠ x₀) :
    Tendsto (fun z ↦ poissonKernelHalfPlane z x) (𝓝 (x₀ : ℂ)) (𝓝 0) := by
  have h' : (x : ℂ) ≠ (x₀ : ℂ) := by exact_mod_cast h
  have := (continuousAt_poissonKernelHalfPlane h').tendsto
  simpa [poissonKernelHalfPlane] using this

/-- **Boundary behaviour of the Poisson integral**: at a continuity point `x₀` of `b`,
`P[b](z) → b(x₀)` as `z → x₀` within the upper half-plane. -/
theorem tendsto_poissonIntegralHalfPlane_of_continuousAt {b : ℝ → ℝ}
    (hb : Integrable fun x ↦ b x / (1 + x ^ 2)) {x₀ : ℝ} (hcont : ContinuousAt b x₀) :
    Tendsto (poissonIntegralHalfPlane b) (𝓝[{z | 0 < z.im}] (x₀ : ℂ)) (𝓝 (b x₀)) := by
  set l := 𝓝[{z : ℂ | 0 < z.im}] (x₀ : ℂ) with hl
  have hbmeas := aestronglyMeasurable_of_integrable_div_one_add_sq hb
  have habs : Integrable fun x ↦ |b x - b x₀| / (1 + x ^ 2) := by
    have := (hb.sub (integrable_const_div_one_add_sq (b x₀))).norm
    refine this.congr (Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.sub_apply, Real.norm_eq_abs, ← sub_div, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < 1 + x ^ 2)]
  have hmem : ∀ᶠ z in l, 0 < z.im := self_mem_nhdsWithin
  -- the deviation `|P[b](z) - b(x₀)|` is at most `∫ P(z, x) |b(x) - b(x₀)| dx`
  have hle : ∀ z : ℂ, 0 < z.im → |poissonIntegralHalfPlane b z - b x₀| ≤
      ∫ x, poissonKernelHalfPlane z x * |b x - b x₀| := fun z hz ↦ by
    have hint := integrable_poissonKernelHalfPlane_mul hb hz
    have hint' := integrable_poissonKernelHalfPlane_mul
      (integrable_const_div_one_add_sq (b x₀)) hz
    have e : ∫ x, poissonKernelHalfPlane z x * (b x - b x₀) =
        poissonIntegralHalfPlane b z - b x₀ := by
      simp_rw [mul_sub]
      rw [integral_sub hint hint', integral_mul_const, integral_poissonKernelHalfPlane hz, one_mul,
        poissonIntegralHalfPlane]
    rw [← e]
    refine abs_integral_le_integral_abs.trans (le_of_eq (integral_congr_ae
      (Eventually.of_forall fun x ↦ ?_)))
    simp only [abs_mul, abs_of_pos (poissonKernelHalfPlane_pos hz x)]
  -- the deviation tends to `0`
  have hE : Tendsto (fun z ↦ ∫ x, poissonKernelHalfPlane z x * |b x - b x₀|) l (𝓝 0) := by
    rw [tendsto_order]
    refine ⟨fun a ha ↦ ?_, fun ε hε ↦ ?_⟩
    · filter_upwards [hmem] with z hz
      exact ha.trans_le (integral_nonneg fun x ↦
        mul_nonneg (poissonKernelHalfPlane_pos hz x).le (abs_nonneg _))
    obtain ⟨δ, hδ, hδb⟩ := Metric.continuousAt_iff.1 hcont (ε / 2) (by positivity)
    set K := 4 * π⁻¹ * (2 + (1 + 2 * x₀ ^ 2) / δ ^ 2) with hK
    have hnear : ∀ᶠ z in l, |z.re - x₀| ≤ δ / 2 ∧ z.im ≤ 1 := by
      have : ball (x₀ : ℂ) (min (δ / 2) 1) ∈ l :=
        mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ (by positivity))
      filter_upwards [this] with z hz
      have hz' : ‖z - x₀‖ < min (δ / 2) 1 := mem_ball_iff_norm.1 hz
      have h1 : |z.re - x₀| ≤ ‖z - x₀‖ := by simpa using abs_re_le_norm (z - x₀)
      have h2 : |z.im| ≤ ‖z - x₀‖ := by simpa using abs_im_le_norm (z - x₀)
      exact ⟨h1.trans (hz'.le.trans (min_le_left _ _)),
        (le_abs_self _).trans (h2.trans (hz'.le.trans (min_le_right _ _)))⟩
    -- the far part tends to `0` by dominated convergence
    have hfar : Tendsto (fun z ↦ ∫ x in (ball x₀ δ)ᶜ, poissonKernelHalfPlane z x * |b x - b x₀|) l
        (𝓝 0) := by
      have := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (ball x₀ δ)ᶜ)
        (l := l) (F := fun z x ↦ poissonKernelHalfPlane z x * |b x - b x₀|) (f := fun _ ↦ 0)
        (fun x ↦ K * (|b x - b x₀| / (1 + x ^ 2))) (Eventually.of_forall fun z ↦
          ((measurable_poissonKernelHalfPlane z).aestronglyMeasurable.mul
            (hbmeas.sub aestronglyMeasurable_const).norm).restrict) ?_
        (habs.const_mul K).integrableOn ?_
      · simpa using this
      · filter_upwards [hmem, hnear] with z hz hz'
        filter_upwards [ae_restrict_mem measurableSet_ball.compl] with x hx
        have hx' : δ ≤ |x - x₀| := by simpa [Real.dist_eq] using hx
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (poissonKernelHalfPlane_pos hz x), abs_abs,
          ← mul_div_assoc, mul_div_right_comm]
        gcongr
        refine (poissonKernelHalfPlane_le_of_le_abs_sub hz hδ hz'.1 hx').trans ?_
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        calc 4 * π⁻¹ * z.im * (2 + (1 + 2 * x₀ ^ 2) / δ ^ 2)
            ≤ 4 * π⁻¹ * 1 * (2 + (1 + 2 * x₀ ^ 2) / δ ^ 2) := by gcongr; exact hz'.2
          _ = K := by rw [hK]; ring
      · filter_upwards [ae_restrict_mem measurableSet_ball.compl] with x hx
        have hx' : x ≠ x₀ := fun h ↦ hx (by simp [h, hδ])
        simpa using ((tendsto_poissonKernelHalfPlane_nhds_ofReal hx').mono_left
          nhdsWithin_le_nhds).mul_const |b x - b x₀|
    filter_upwards [hmem, (tendsto_order.1 hfar).2 (ε / 2) (by positivity)] with z hz hfarz
    have hint : Integrable fun x ↦ poissonKernelHalfPlane z x * |b x - b x₀| :=
      integrable_poissonKernelHalfPlane_mul habs hz
    have hsplit := (integral_add_compl (measurableSet_ball (x := x₀) (ε := δ)) hint).symm
    have hnear : ∫ x in ball x₀ δ, poissonKernelHalfPlane z x * |b x - b x₀| ≤ ε / 2 := by
      calc ∫ x in ball x₀ δ, poissonKernelHalfPlane z x * |b x - b x₀|
          ≤ ∫ x in ball x₀ δ, poissonKernelHalfPlane z x * (ε / 2) := by
            refine setIntegral_mono_on hint.integrableOn
              ((integrable_poissonKernelHalfPlane hz).mul_const _).integrableOn measurableSet_ball
              fun x hx ↦ mul_le_mul_of_nonneg_left ?_ (poissonKernelHalfPlane_pos hz x).le
            simpa [Real.dist_eq] using (hδb (mem_ball.1 hx)).le
        _ ≤ ∫ x, poissonKernelHalfPlane z x * (ε / 2) :=
            setIntegral_le_integral ((integrable_poissonKernelHalfPlane hz).mul_const _)
              (Eventually.of_forall fun x ↦ by
                have := poissonKernelHalfPlane_pos hz x
                positivity)
        _ = ε / 2 := by rw [integral_mul_const, integral_poissonKernelHalfPlane hz, one_mul]
    rw [hsplit]
    linarith
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun z ↦ norm_nonneg _) ?_ hE
  filter_upwards [hmem] with z hz
  rw [Real.norm_eq_abs]
  exact hle z hz

/-!
### Truncation from below

For boundary data bounded above but not below one truncates to `max b (-n)`; the Poisson
integrals of the truncations decrease to `P[b]` (dominated convergence with the majorant
`P(z, x) |b(x)|`, since `|max (b x) (-n)| ≤ |b x|`).
-/

theorem integrable_max_neg_div_one_add_sq {b : ℝ → ℝ} (hb : Integrable fun x ↦ b x / (1 + x ^ 2))
    (c : ℝ) : Integrable fun x ↦ max (b x) (-c) / (1 + x ^ 2) := by
  refine (hb.sup (integrable_const_div_one_add_sq (-c))).congr (Eventually.of_forall fun x ↦ ?_)
  simp only [Pi.sup_apply]
  rw [max_div_div_right (by positivity)]

/-- The Poisson integrals of the truncations `max b (-n)` decrease in `n`. -/
theorem antitone_poissonIntegralHalfPlane_max {b : ℝ → ℝ}
    (hb : Integrable fun x ↦ b x / (1 + x ^ 2)) {z : ℂ} (hz : 0 < z.im) :
    Antitone fun n : ℕ ↦ poissonIntegralHalfPlane (fun x ↦ max (b x) (-(n : ℝ))) z :=
  fun m n hmn ↦ poissonIntegralHalfPlane_mono
    (integrable_max_neg_div_one_add_sq hb n) (integrable_max_neg_div_one_add_sq hb m)
    (fun _ ↦ max_le_max le_rfl (neg_le_neg (Nat.cast_le.2 hmn))) hz

/-- **Monotone limit of the truncations**: `P[max b (-n)](z) → P[b](z)` as `n → ∞` for `z ∈ ℍ`. -/
theorem tendsto_poissonIntegralHalfPlane_max {b : ℝ → ℝ}
    (hb : Integrable fun x ↦ b x / (1 + x ^ 2)) {z : ℂ} (hz : 0 < z.im) :
    Tendsto (fun n : ℕ ↦ poissonIntegralHalfPlane (fun x ↦ max (b x) (-(n : ℝ))) z) atTop
      (𝓝 (poissonIntegralHalfPlane b z)) := by
  unfold poissonIntegralHalfPlane
  refine tendsto_integral_of_dominated_convergence (fun x ↦ poissonKernelHalfPlane z x * |b x|)
    (fun n ↦ (integrable_poissonKernelHalfPlane_mul
      (integrable_max_neg_div_one_add_sq hb n) hz).aestronglyMeasurable) ?_
    (fun n ↦ Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall fun x ↦ ?_)
  · refine (integrable_poissonKernelHalfPlane_mul hb hz).norm.congr
      (Eventually.of_forall fun x ↦ ?_)
    simp [Real.norm_eq_abs, abs_of_pos (poissonKernelHalfPlane_pos hz x)]
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (poissonKernelHalfPlane_pos hz x)]
    exact mul_le_mul_of_nonneg_left (abs_max_neg_le_abs n.cast_nonneg)
      (poissonKernelHalfPlane_pos hz x).le
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (-b x)] with n hn
    rw [max_eq_left (by linarith)]

end Complex
