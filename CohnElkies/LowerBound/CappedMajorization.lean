import CohnElkies.LowerBound.StripToHalfPlane
import CohnElkies.LowerBound.CappedMajorant
import CohnElkiesForMathlib.Analysis.Complex.Subharmonic.HalfPlane

/-!
# The Poisson principle in the strip and the majorization of `Z` (report §3.2, Lemma 3.2)

**Poisson principle for a horizontal strip** (`norm_le_exp_integral_P_σ_of_strip`): if `Z` is
holomorphic and bounded on the strip `|Im z| < ℓ` and continuous on its closure, with
`‖Z‖ ≤ e^{b}` on the bottom edge for a continuous, linearly bounded profile `b` and `‖Z‖ ≤ 1` on
the top edge, then `‖Z(s + iσℓ)‖ ≤ exp (∫ P_σ(T) b(s − ℓT) dT)` at every interior point. The proof
is the report's: the conformal map `Φ(t) = exp(π(t + iℓ)/(2ℓ))` sends the strip onto the upper
half-plane `ℍ` (`CohnElkies.LowerBound.StripToHalfPlane`), `log ‖Z ∘ Φ⁻¹‖` is subharmonic and
bounded above on `ℍ`, and its boundary values are at most the transported datum
`b((2ℓ/π) log x)` on `(0, ∞)`, the image of the bottom edge, and `0` on `(-∞, 0)`, the image of
the top edge. The Poisson principle for the upper half-plane
(`AnalyticOnNhd.log_norm_le_poissonIntegralHalfPlane`, with the single exceptional boundary
point `0`) bounds `log ‖Z ∘ Φ⁻¹‖` by the half-plane Poisson integral of this datum, which at
`Φ(s + iσℓ)` is the strip Poisson integral `∫ P_σ(T) b(s − ℓT) dT`: the harmonic-measure
identity `poissonIntegralHalfPlane_halfPlaneDatum`.

Applied to the normalized Mellin transform `Z_g` and the capped boundary profile `h_{λ,D}` this is
Lemma 3.2 of the report: `‖Z(s + iσλ)‖ ≤ exp (∫ P_σ(T) h_{λ,D}(s − λT) dT)` for every large enough
cap `D` (`norm_Z_g_le_exp_integral_of_cap`, `exists_capped_poisson_majorization`). The module also
proves the linear bound on `h_{λ,D}`. An alternative proof of the principle, by the
Phragmén–Lindelöf principle in the strip, is in
`CohnElkies.LowerBound.PhragmenLindelofMajorization`.
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology

/-! ### The linear bound on the capped profile -/
theorem abs_log_half_le_half {x : ℝ} (hx : 2 ≤ x) : |Real.log (x / 2)| ≤ x / 2 := by
  rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
  linarith [Real.log_le_sub_one_of_pos (show 0 < x / 2 by linarith)]

theorem abs_log_sqrtFactor_le_add {c x : ℝ} (hc : 0 ≤ c) (hx : 2 ≤ x) :
    |Real.log (√(c ^ 2 + (x / 2) ^ 2))| ≤ c + x := by
  linarith [lower_abs_log_sqrtFactor_le hc (show 0 < x by linarith), abs_log_half_le_half hx]

/-- The Riemann sum of the factors `log √(cⱼ² + (x/2)²)` of `h_λ` is linearly bounded. -/
theorem abs_sum_log_sqrtFactor_le {k : ℕ} {c : ℕ → ℝ} (hc : ∀ j, 0 ≤ c j) {x : ℝ} (hx : 2 ≤ x) :
    |∑ j ∈ Finset.range k, Real.log (√(c j ^ 2 + (x / 2) ^ 2))| ≤
      (∑ j ∈ Finset.range k, c j) + k * x := by
  calc |∑ j ∈ Finset.range k, Real.log (√(c j ^ 2 + (x / 2) ^ 2))|
      ≤ ∑ j ∈ Finset.range k, |Real.log (√(c j ^ 2 + (x / 2) ^ 2))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range k, (c j + x) :=
        Finset.sum_le_sum fun j _ ↦ abs_log_sqrtFactor_le_add (hc j) hx
    _ = (∑ j ∈ Finset.range k, c j) + k * x := by simp [Finset.sum_add_distrib]

/-- Even dimensions: `h_k` grows at most linearly away from the pole at `0`. -/
theorem exists_abs_h_ℓ_le_natCast (k : ℕ) (R : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x : ℝ, 2 ≤ x → |h_ℓ (k : ℝ) R x| ≤ A * (1 + x) := by
  have hL : (0 : ℝ) ≤ |(k : ℝ) * Real.log (π * R ^ 2)| := abs_nonneg _
  have hS : (0 : ℝ) ≤ ∑ j ∈ Finset.range k, (j : ℝ) := by positivity
  refine ⟨|(k : ℝ) * Real.log (π * R ^ 2)| + (∑ j ∈ Finset.range k, (j : ℝ)) + k,
    by positivity, fun x hx ↦ ?_⟩
  have hx0 : (0 : ℝ) ≤ x := by linarith
  rw [lowerGammaBoundaryLog_integer k R (show (0 : ℝ) < x by linarith).ne']
  have hsum := abs_sum_log_sqrtFactor_le (k := k) (c := fun j : ℕ ↦ (j : ℝ))
    (fun j ↦ Nat.cast_nonneg j) hx
  have habs := abs_sub ((k : ℝ) * Real.log (π * R ^ 2))
    (∑ j ∈ Finset.range k, Real.log (√((j : ℝ) ^ 2 + (x / 2) ^ 2)))
  nlinarith [mul_nonneg hL hx0, mul_nonneg hS hx0, mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hx0]

/-- Odd dimensions: `h_{k+1/2}` grows at most linearly away from the pole at `0`; the extra
`coth` correction contributes the terms `π x + |log π|`. -/
theorem exists_abs_h_ℓ_le_natCast_add_half (k : ℕ) (R : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x : ℝ, 2 ≤ x → |h_ℓ ((k : ℝ) + 1 / 2) R x| ≤ A * (1 + x) := by
  have hL : (0 : ℝ) ≤ |((k : ℝ) + 1 / 2) * Real.log (π * R ^ 2)| := abs_nonneg _
  have hQ : (0 : ℝ) ≤ |Real.log π| := abs_nonneg _
  have hS : (0 : ℝ) ≤ ∑ j ∈ Finset.range k, ((j : ℝ) + 1 / 2) := by positivity
  refine ⟨|((k : ℝ) + 1 / 2) * Real.log (π * R ^ 2)| +
    (∑ j ∈ Finset.range k, ((j : ℝ) + 1 / 2)) + k + π + |Real.log π| + 1, by positivity,
    fun x hx ↦ ?_⟩
  have hx0 : (0 : ℝ) < x := by linarith
  have hsum := abs_sum_log_sqrtFactor_le (k := k) (c := fun j : ℕ ↦ (j : ℝ) + 1 / 2)
    (fun j ↦ by positivity) hx
  have hcorr : |1 / 2 * Real.log (Real.coth (π * (x / 2)) / (x / 2))| ≤
      (π * x + |Real.log π| + x) / 2 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    linarith [Real.abs_log_coth_div_le (show 0 < x / 2 by linarith), abs_log_half_le_half hx]
  rw [lowerGammaBoundaryLog_halfInteger k R hx0.ne', abs_of_pos hx0,
    show π * x / 2 = π * (x / 2) by ring]
  have hmain := abs_sub (((k : ℝ) + 1 / 2) * Real.log (π * R ^ 2))
    (∑ j ∈ Finset.range k, Real.log (√(((j : ℝ) + 1 / 2) ^ 2 + (x / 2) ^ 2)))
  have htotal := abs_add_le (((k : ℝ) + 1 / 2) * Real.log (π * R ^ 2) -
      ∑ j ∈ Finset.range k, Real.log (√(((j : ℝ) + 1 / 2) ^ 2 + (x / 2) ^ 2)))
    (1 / 2 * Real.log (Real.coth (π * (x / 2)) / (x / 2)))
  nlinarith [mul_nonneg hL hx0.le, mul_nonneg hS hx0.le, mul_nonneg hQ hx0.le,
    mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hx0.le, mul_nonneg Real.pi_pos.le hx0.le]

/-- `h_λ` is even for `λ = d/2`. -/
theorem h_ℓ_eq_abs {d : ℕ} (R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    h_ℓ ((d : ℝ) / 2) R y = h_ℓ ((d : ℝ) / 2) R |y| := by
  rcases abs_choice y with h | h <;> rw [h]
  exact (lowerGammaBoundaryLog_dimension_neg R hy).symm

/-- Report Lemma 3.2: away from the pole the boundary profile `h_{d/2}` is linearly bounded. -/
theorem exists_abs_h_ℓ_le (d : ℕ) (R : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ y : ℝ, 2 ≤ |y| → |h_ℓ ((d : ℝ) / 2) R y| ≤ A * (1 + |y|) := by
  obtain ⟨A, hA, htail⟩ : ∃ A : ℝ, 0 ≤ A ∧
      ∀ x : ℝ, 2 ≤ x → |h_ℓ ((d : ℝ) / 2) R x| ≤ A * (1 + x) := by
    rcases d.even_or_odd with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [show ((k + k : ℕ) : ℝ) / 2 = (k : ℝ) by push_cast; ring]
      exact exists_abs_h_ℓ_le_natCast k R
    · rw [show ((2 * k + 1 : ℕ) : ℝ) / 2 = (k : ℝ) + 1 / 2 by push_cast; ring]
      exact exists_abs_h_ℓ_le_natCast_add_half k R
  refine ⟨A, hA, fun y hy ↦ ?_⟩
  rw [h_ℓ_eq_abs R (by rintro rfl; norm_num at hy)]
  exact htail _ hy

/-- Report Lemma 3.2: the capped profile `h_{d/2,D}` is linearly bounded on all of `ℝ`; near the
pole the cap `D` takes over and continuity bounds the compact part `|y| ≤ 2`. -/
theorem exists_abs_h_ℓD_le {d : ℕ} (hd : 0 < d) (R D : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ y : ℝ, |h_ℓD ((d : ℝ) / 2) R D y| ≤ A * (1 + |y|) := by
  have hℓ : 0 < (d : ℝ) / 2 := half_pos (Nat.cast_pos.mpr hd)
  obtain ⟨A₀, hA₀, htail⟩ := exists_abs_h_ℓ_le d R
  obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact (Icc (-2 : ℝ) 2)).exists_bound_of_continuousOn
    (lowerGammaBoundaryCapped_continuous hℓ R D).continuousOn
  obtain ⟨A, hA, hKA, hDA, hA₀A⟩ : ∃ A : ℝ, 0 ≤ A ∧ K ≤ A ∧ |D| ≤ A ∧ A₀ ≤ A :=
    ⟨max 0 (max K (max |D| A₀)), le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)),
      (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))⟩
  refine ⟨A, hA, fun y ↦ ?_⟩
  have hfactor : A ≤ A * (1 + |y|) := by nlinarith [abs_nonneg y]
  rcases lt_or_ge |y| 2 with hy | hy
  · calc |h_ℓD ((d : ℝ) / 2) R D y| ≤ K := by simpa using hK y (abs_le.mp hy.le)
      _ ≤ A := hKA
      _ ≤ A * (1 + |y|) := hfactor
  · rw [h_ℓD, ite_eq_right (show y ≠ 0 by rintro rfl; norm_num at hy)]
    rcases le_total (h_ℓ ((d : ℝ) / 2) R y) D with hmin | hmin
    · rw [min_eq_left hmin]
      exact (htail y hy).trans (mul_le_mul_of_nonneg_right hA₀A (by positivity))
    · rw [min_eq_right hmin]
      exact hDA.trans hfactor

/-! ### The Poisson principle for the strip via the upper half-plane -/

/-- The bottom edge `y - iℓ` lies in the closure of the strip `|Im z| < ℓ`. -/
theorem ofReal_sub_I_mul_mem_closure_strip {ℓ : ℝ} (hℓ : 0 < ℓ) (y : ℝ) :
    (y : ℂ) - I * (ℓ : ℂ) ∈ closure (Complex.im ⁻¹' Ioo (-ℓ) ℓ) := by
  rw [Complex.closure_preimage_im, closure_Ioo (by linarith : (-ℓ) ≠ ℓ)]
  simp only [mem_preimage, mem_Icc, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add, zero_sub]
  constructor <;> linarith

/-- The top edge `y + iℓ` lies in the closure of the strip `|Im z| < ℓ`. -/
theorem ofReal_add_I_mul_mem_closure_strip {ℓ : ℝ} (hℓ : 0 < ℓ) (y : ℝ) :
    (y : ℂ) + I * (ℓ : ℂ) ∈ closure (Complex.im ⁻¹' Ioo (-ℓ) ℓ) := by
  rw [Complex.closure_preimage_im, closure_Ioo (by linarith : (-ℓ) ≠ ℓ)]
  simp only [mem_preimage, mem_Icc, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add]
  constructor <;> linarith

/-- **The Poisson principle for the strip** (the report's proof of Lemma 3.2, through the upper
half-plane). Let `Z` be holomorphic and bounded on the open strip `|Im z| < ℓ` and continuous on
its closure, let `b` be continuous with `|b y| ≤ A (1 + |y|)`, and assume `‖Z(y − iℓ)‖ ≤ e^{b y}`
on the bottom edge and `‖Z(y + iℓ)‖ ≤ 1` on the top edge. Then at every interior point
`s + iσℓ`, `-1 < σ < 1`, `‖Z(s + iσℓ)‖ ≤ exp (∫ P_σ(T) b(s − ℓT) dT)`, the exponential of the
Poisson integral of `b`.

Proof: `F = Z ∘ Φ⁻¹` is analytic and bounded on `ℍ`, where `Φ⁻¹(w) = (2ℓ/π) log w − iℓ`. As
`w → x` within `ℍ`, `F w → Z((2ℓ/π) log x − iℓ)` for `x > 0` and `F w → Z((2ℓ/π) log(−x) + iℓ)`
for `x < 0`, so `limsup log ‖F‖ ≤ b((2ℓ/π) log x)` on `(0, ∞)` and `≤ 0` on `(−∞, 0)`: this is
the datum `halfPlaneDatum ℓ b`, continuous off `0`. The Poisson principle for the half-plane,
with the exceptional point `0`, gives `‖F‖ ≤ exp P[halfPlaneDatum ℓ b]` on `ℍ`, and at
`w = Φ(s + iσℓ)` the Poisson integral is `∫ P_σ(T) b(s − ℓT) dT`
(`poissonIntegralHalfPlane_halfPlaneDatum`). -/
theorem norm_le_exp_integral_P_σ_of_strip {ℓ : ℝ} (hℓ : 0 < ℓ) {Z : ℂ → ℂ}
    (hZ : DiffContOnCl ℂ Z (Complex.im ⁻¹' Ioo (-ℓ) ℓ)) {K : ℝ}
    (hK : ∀ z : ℂ, z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ → ‖Z z‖ ≤ K)
    {b : ℝ → ℝ} (hb : Continuous b) {A : ℝ} (hbound : ∀ y : ℝ, |b y| ≤ A * (1 + |y|))
    (hbottom : ∀ y : ℝ, ‖Z ((y : ℂ) - I * (ℓ : ℂ))‖ ≤ Real.exp (b y))
    (htop : ∀ y : ℝ, ‖Z ((y : ℂ) + I * (ℓ : ℂ))‖ ≤ 1)
    {σ : ℝ} (hσbelow : -1 < σ) (hσabove : σ < 1) (s : ℝ) :
    ‖Z ((s : ℂ) + I * (σ * ℓ : ℂ))‖ ≤ Real.exp (∫ T : ℝ, P_σ σ T * b (s - ℓ * T)) := by
  have hstrip : IsOpen (Complex.im ⁻¹' Ioo (-ℓ) ℓ) := isOpen_Ioo.preimage Complex.continuous_im
  -- the transplanted function `F = Z ∘ Φ⁻¹` is analytic and bounded on the half-plane
  have hF : AnalyticOnNhd ℂ (Z ∘ halfPlaneToStrip ℓ) {w : ℂ | 0 < w.im} := fun w hw ↦
    (hZ.differentiableOn.analyticOnNhd hstrip _ (halfPlaneToStrip_mem_strip hℓ hw)).comp
      (halfPlaneToStrip_analyticAt ℓ hw)
  have hFK : ∀ w : ℂ, 0 < w.im → ‖(Z ∘ halfPlaneToStrip ℓ) w‖ ≤ K := fun w hw ↦
    hK _ (halfPlaneToStrip_mem_strip hℓ hw)
  -- boundary values of `F` at the real points `x ≠ 0`
  have hlim : ∀ {x : ℝ} {t : ℂ}, t ∈ closure (Complex.im ⁻¹' Ioo (-ℓ) ℓ) →
      Tendsto (halfPlaneToStrip ℓ) (𝓝[{w : ℂ | 0 < w.im}] (x : ℂ)) (𝓝 t) →
      Tendsto (Z ∘ halfPlaneToStrip ℓ) (𝓝[{w : ℂ | 0 < w.im}] (x : ℂ)) (𝓝 (Z t)) :=
    fun ht htend ↦ (hZ.continuousOn _ ht).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨htend, eventually_mem_nhdsWithin.mono fun w hw ↦
        subset_closure (halfPlaneToStrip_mem_strip hℓ hw)⟩)
  have hbdry : ∀ x : ℝ, x ∉ ({0} : Finset ℝ) →
      limsup (fun w ↦ if (Z ∘ halfPlaneToStrip ℓ) w = 0 then ⊥ else
        ((Real.log ‖(Z ∘ halfPlaneToStrip ℓ) w‖ : ℝ) : EReal))
        (𝓝[{w : ℂ | 0 < w.im}] (x : ℂ)) ≤ (halfPlaneDatum ℓ b x : EReal) := by
    intro x hx
    rcases (show x ≠ 0 by simpa using hx).lt_or_gt with hx | hx
    · rw [halfPlaneDatum_of_nonpos hx.le]
      exact (hlim (ofReal_add_I_mul_mem_closure_strip hℓ _)
        (tendsto_halfPlaneToStrip_ofReal_of_neg ℓ hx)).limsup_log_norm_le
        ((htop _).trans_eq Real.exp_zero.symm)
    · rw [halfPlaneDatum_of_pos hx]
      exact (hlim (ofReal_sub_I_mul_mem_closure_strip hℓ _)
        (tendsto_halfPlaneToStrip_ofReal_of_pos ℓ hx)).limsup_log_norm_le (hbottom _)
  -- the half-plane Poisson principle, evaluated at `Φ(s + iσℓ)`
  have hmem := ofReal_add_I_mul_mul_mem_strip hℓ hσbelow hσabove s
  have h := hF.log_norm_le_poissonIntegralHalfPlane hFK
    (integrable_halfPlaneDatum_div_one_add_sq hℓ hb hbound)
    (fun x hx ↦ halfPlaneDatum_continuousAt hb (by simpa using hx)) hbdry _
    (stripToHalfPlane_im_pos hℓ hmem)
  rwa [Function.comp_apply, halfPlaneToStrip_stripToHalfPlane hℓ hmem,
    poissonIntegralHalfPlane_halfPlaneDatum hℓ hσbelow hσabove s b] at h

/-! ### Lemma 3.2: the capped Poisson majorization of `Z_g` -/


/-- Report Lemma 3.2: for `D` large enough the capped profile majorizes the bottom-edge values of
`Z_g`; away from the pole this is the Gamma bound, near it the global bound `C` and the cap. -/
theorem exists_norm_Z_g_bottom_le_exp_h_ℓD {d : ℕ} {ς : ℤˣ} (hd : 0 < d)
    (g : RadialEigenfunction d ς) {R : ℝ} (hR : 0 < R) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∀ y : ℝ,
      ‖Z_g hd g.toFun R ((y : ℂ) - I * ((d : ℂ) / 2))‖ ≤
        Real.exp (h_ℓD ((d : ℝ) / 2) R D y) := by
  obtain ⟨C, hC, hglobal⟩ := g.exists_norm_Z_g_le hd R
  refine ⟨Real.log (C + 1), fun D hD y ↦ ?_⟩
  have hbounded := hglobal ((y : ℂ) - I * ((d : ℂ) / 2)) (by simp)
    (by simp; linarith [Nat.cast_nonneg (α := ℝ) d])
  have hexp : ‖Z_g hd g.toFun R ((y : ℂ) - I * ((d : ℂ) / 2))‖ ≤ Real.exp D :=
    calc ‖Z_g hd g.toFun R ((y : ℂ) - I * ((d : ℂ) / 2))‖ ≤ C + 1 := by linarith
      _ = Real.exp (Real.log (C + 1)) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp D := Real.exp_le_exp.mpr hD
  rcases eq_or_ne y 0 with rfl | hy
  · simpa [h_ℓD] using hexp
  · rw [h_ℓD, ite_eq_right hy]
    rcases le_total (h_ℓ ((d : ℝ) / 2) R y) D with hmin | hmin
    · rw [min_eq_left hmin]
      exact g.norm_Z_g_bottom_le_exp_h_ℓ hd hR y hy
    · rw [min_eq_right hmin]
      exact hexp

/-- Report Lemma 3.2: `|Z(s + iσλ)| ≤ exp(∫ P_σ(T) h_{λ,D}(s − λT) dT)`, the Poisson principle
`norm_le_exp_integral_P_σ_of_strip` for the bounded function `Z_g` on the strip `|Im z| < λ = d/2`
with the capped profile `b = h_{λ,D}`, which is continuous and linearly bounded; the top-edge
bound is (16). -/
theorem norm_Z_g_le_exp_integral_of_cap {d : ℕ} {ς : ℤˣ} (hd : 0 < d)
    (g : RadialEigenfunction d ς) (R D : ℝ)
    (hcap : ∀ y : ℝ, ‖Z_g hd g.toFun R ((y : ℂ) - I * ((d : ℂ) / 2))‖ ≤
      Real.exp (h_ℓD ((d : ℝ) / 2) R D y))
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) (s : ℝ) :
    ‖Z_g hd g.toFun R ((s : ℂ) + I * (σ * ((d : ℂ) / 2)))‖ ≤
      Real.exp (∫ T : ℝ, P_σ σ T * h_ℓD ((d : ℝ) / 2) R D (s - (d : ℝ) / 2 * T)) := by
  have hℓ : 0 < (d : ℝ) / 2 := half_pos (Nat.cast_pos.mpr hd)
  have hcast : ((d : ℂ) / 2) = (((d : ℝ) / 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat]
  obtain ⟨A, -, hbound⟩ := exists_abs_h_ℓD_le hd R D
  obtain ⟨K, -, hK⟩ := g.exists_norm_Z_g_le hd R
  rw [hcast] at hcap ⊢
  exact norm_le_exp_integral_P_σ_of_strip hℓ (g.diffContOnCl_Z_g hd R)
    (fun z hz ↦ hK z hz.1.le hz.2.le) (lowerGammaBoundaryCapped_continuous hℓ R D) hbound hcap
    (fun y ↦ by rw [← hcast]; exact g.norm_Z_g_top_le_one hd R y) hbelow habove s

/-- Report Lemma 3.2: for every large enough cap `D`, the normalized Mellin transform of a
radial eigenfunction is majorized on the strip by the Poisson extension of `h_{λ,D}`. -/
theorem exists_capped_poisson_majorization {d : ℕ} {ς : ℤˣ} (hd : 0 < d)
    (g : RadialEigenfunction d ς) {R : ℝ} (hR : 0 < R) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∀ {σ : ℝ}, -1 < σ → σ < 1 → ∀ s : ℝ,
      ‖Z_g hd g.toFun R ((s : ℂ) + I * (σ * ((d : ℂ) / 2)))‖ ≤
        Real.exp (∫ T : ℝ, P_σ σ T * h_ℓD ((d : ℝ) / 2) R D (s - (d : ℝ) / 2 * T)) := by
  obtain ⟨D₀, hbottom⟩ := exists_norm_Z_g_bottom_le_exp_h_ℓD hd g hR
  refine ⟨D₀, fun D hD ↦ ?_⟩
  intro σ hbelow habove s
  exact norm_Z_g_le_exp_integral_of_cap hd g R D (hbottom D hD) hbelow habove s

end

end CohnElkies
