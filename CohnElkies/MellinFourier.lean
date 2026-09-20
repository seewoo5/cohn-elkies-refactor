import CohnElkies.Radial

/-!
# The Mellin–Fourier functional equation (report §2.2, (9)–(10))

The Mellin multiplier `m_ℓ(t) = π^{it} Γ((ℓ - it)/2) / Γ((ℓ + it)/2)` of the radial Fourier
transform, the Gaussian pairing `Φ_f(a) = ∫ f(x) e^{-a|x|²} dx` and the functional equation
`X_{𝓕f}(t) = m_ℓ(t) X_f(t)` relating the Mellin transforms of the radial profiles of `f` and `𝓕 f`
on the critical line `Re z = d/2` (`radialMellinMultiplier`), together with the strip version used
by the lower bound (`radial_fourier_mellin_strip`).
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory Real Set
open scoped FourierTransform SchwartzMap Topology RealInnerProductSpace

/-- The Mellin multiplier `m_ℓ(t) = π^{it} Γ((ℓ - it)/2) / Γ((ℓ + it)/2)` of the radial Fourier
transform on the line `Re z = ℓ` (report (10)). -/
def m_ℓ (ℓ t : ℝ) : ℂ :=
  Complex.exp (I * t * log π) * Complex.Gamma ((ℓ - I * t) / 2) / Complex.Gamma ((ℓ + I * t) / 2)

theorem mellinMultiplier_denominator_ne_zero {ℓ : ℝ} (hℓ : 0 < ℓ) (t : ℝ) :
    Complex.Gamma ((ℓ + I * t) / 2) ≠ 0 :=
  Complex.Gamma_ne_zero_of_re_pos (by simpa using half_pos hℓ)

/-! ### Preliminaries -/

/-- The Fourier transform of a radial test function is radial. -/
theorem gaussianMellin_fourier_radial {d : ℕ} {f : TestFunction d} (hf : IsRadial f) :
    IsRadial (𝓕 f : TestFunction d) := fun x y hxy ↦ by
  let A : Euclidean d ≃ₗᵢ[ℝ] Euclidean d := Submodule.reflection (ℝ ∙ (x - y))ᗮ
  have hA : (f : Euclidean d → ℂ) ∘ A = f := funext fun z ↦ hf _ _ (A.norm_map z)
  have hAx : A x = y := Submodule.reflection_sub hxy
  rw [SchwartzMap.fourier_coe, ← hAx, ← Real.fourier_comp_linearIsometry, hA]

/-- `f(x) |x|^z` is integrable for a Schwartz function `f` and `-d < Re z ≤ 0`. -/
theorem schwartz_mul_norm_cpow_integrable {d : ℕ} (hd : 0 < d) (f : TestFunction d) (z : ℂ)
    (hlower : -(d : ℝ) < z.re) (hupper : z.re ≤ 0) :
    Integrable (fun x : Euclidean d ↦ f x * (‖x‖ : ℂ) ^ z) (volume : Measure (Euclidean d)) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hmeas : AEStronglyMeasurable (fun x : Euclidean d ↦ f x * (‖x‖ : ℂ) ^ z) volume :=
    (f.continuous.measurable.mul
      ((Complex.measurable_ofReal.comp measurable_norm).pow_const z)).aestronglyMeasurable
  have hinner : IntegrableOn (fun x : Euclidean d ↦ f x * (‖x‖ : ℂ) ^ z) (Metric.ball 0 1) := by
    refine integrableOn_ball_of_norm_le_rpow (C := SchwartzMap.seminorm ℝ 0 0 f) (α := -z.re)
      (by rw [finrank_euclideanSpace_fin]; exact hd)
      (by rw [finrank_euclideanSpace_fin]; linarith) ?_ hmeas
    filter_upwards [ae_restrict_of_ae ((volume : Measure (Euclidean d)).ae_ne 0)] with x hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_iff.2 hx), neg_neg]
    exact mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℝ f x)
      (Real.rpow_nonneg (norm_nonneg x) _)
  have houter : IntegrableOn (fun x : Euclidean d ↦ f x * (‖x‖ : ℂ) ^ z)
      (Metric.ball (0 : Euclidean d) 1)ᶜ := by
    refine f.integrable.norm.restrict.mono' hmeas.restrict ?_
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet.compl] with x hx
    have hx1 : 1 ≤ ‖x‖ := by simpa using hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hx1)]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (Real.rpow_le_one_of_one_le_of_nonpos hx1 hupper)
  simpa using hinner.union houter

/-! ### The Gaussian pairing `Φ_f(a) = ∫ f(x) e^{-a|x|²} dx` -/

/-- The Gaussian pairing `Φ_f(a) = ∫ f(x) e^{-a|x|²} dx` of a test function. -/
def gaussianPairing {d : ℕ} (f : TestFunction d) (a : ℝ) : ℂ :=
  ∫ x, f x * Complex.exp (-(a * (‖x‖ : ℂ) ^ 2))

/-- Parseval against a Gaussian: `Φ_{𝓕 f}(a) = (π/a)^{d/2} Φ_f(π²/a)`. -/
theorem gaussianPairing_fourier {d : ℕ} (f : TestFunction d) {a : ℝ} (ha : 0 < a) :
    gaussianPairing (𝓕 f) a = (π / a : ℂ) ^ (d / 2 : ℂ) * gaussianPairing f (π ^ 2 / a) := by
  have ha' : 0 < (a : ℂ).re := by simpa using ha
  have hw : Integrable fun x : Euclidean d ↦ Complex.exp (-(a * (‖x‖ : ℂ) ^ 2)) := by
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Euclidean d) ha' 0 0
  have hflip : (innerₗ (Euclidean d)).flip = innerₗ (Euclidean d) := by
    ext x y
    exact real_inner_comm x y
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ (Euclidean d))
    (μ := volume) (ν := volume) (f := (f : Euclidean d → ℂ)) Real.continuous_fourierChar
    continuous_inner f.integrable hw
  rw [hflip] at h
  unfold gaussianPairing
  rw [SchwartzMap.fourier_coe, ← integral_const_mul]
  refine h.trans (integral_congr_ae (.of_forall fun x ↦ ?_))
  have hg := fourier_gaussian_innerProductSpace (V := Euclidean d) ha' x
  simp only [finrank_euclideanSpace_fin, neg_mul] at hg
  change f x * 𝓕 (fun v : Euclidean d ↦ Complex.exp (-(a * (‖v‖ : ℂ) ^ 2))) x = _
  rw [hg]
  push_cast
  ring_nf

/-- `M Φ_f(b) = Γ(b) ∫ f(x) |x|^{-2b} dx` for `0 < Re b < d/2` (Fubini and the Gamma integral). -/
theorem mellin_gaussianPairing {d : ℕ} (hd : 0 < d) (f : TestFunction d) {b : ℂ} (hb : 0 < b.re)
    (hbd : 2 * b.re < d) :
    mellin (gaussianPairing f) b = Complex.Gamma b * ∫ x, f x * (‖x‖ : ℂ) ^ (-(2 * b)) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  set F : Euclidean d → ℝ → ℂ := fun x a ↦
    f x * ((a : ℂ) ^ (b - 1) * Complex.exp (-((‖x‖ : ℂ) ^ 2 * a))) with hF
  have hslice (r : ℝ) (hr : 0 < r) :
      IntegrableOn (fun a : ℝ ↦ (a : ℂ) ^ (b - 1) * Complex.exp (-(r * a))) (Ioi 0) := by
    have hmeas : AEStronglyMeasurable (fun a : ℝ ↦ (a : ℂ) ^ (b - 1) * Complex.exp (-(r * a)))
        (volume.restrict (Ioi 0)) :=
      ((Complex.measurable_ofReal.pow_const _).mul (by fun_prop)).aestronglyMeasurable
    refine (integrable_norm_iff hmeas).1 ((integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1)
      (s := b.re - 1) (by linarith) one_pos hr).congr_fun (fun a ha ↦ ?_) measurableSet_Ioi)
    simp [Complex.norm_cpow_eq_rpow_re_of_pos ha, Complex.norm_exp]
  have hnorm (r : ℝ) (hr : 0 < r) :
      ∫ a : ℝ in Ioi 0, ‖(a : ℂ) ^ (b - 1) * Complex.exp (-(r * a))‖ =
        (1 / r) ^ b.re * Gamma b.re := by
    rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi hb hr]
    refine setIntegral_congr_fun measurableSet_Ioi fun a ha ↦ ?_
    simp [Complex.norm_cpow_eq_rpow_re_of_pos ha, Complex.norm_exp]
  have hint : Integrable (Function.uncurry F) (volume.prod (volume.restrict (Ioi 0))) := by
    have hmeas : AEStronglyMeasurable (Function.uncurry F)
        (volume.prod (volume.restrict (Ioi 0))) := by
      change AEStronglyMeasurable (fun p : Euclidean d × ℝ ↦
        f p.1 * ((p.2 : ℂ) ^ (b - 1) * Complex.exp (-((‖p.1‖ : ℂ) ^ 2 * p.2)))) _
      exact ((f.continuous.measurable.comp measurable_fst).mul
        (((Complex.measurable_ofReal.comp measurable_snd).pow_const _).mul
          (by fun_prop))).aestronglyMeasurable
    refine (integrable_prod_iff hmeas).2 ⟨?_, ?_⟩
    · filter_upwards [(volume : Measure (Euclidean d)).ae_ne 0] with x hx
      simpa only [Function.uncurry_apply_pair, hF, Complex.ofReal_pow] using
        (hslice _ (pow_pos (norm_pos_iff.2 hx) 2)).const_mul (f x)
    · have hz : (-(2 * b.re) : ℂ).re = -(2 * b.re) := by simp
      refine ((schwartz_mul_norm_cpow_integrable hd f (-(2 * b.re)) (by rw [hz]; linarith)
        (by rw [hz]; linarith)).norm.mul_const (Gamma b.re)).congr ?_
      filter_upwards [(volume : Measure (Euclidean d)).ae_ne 0] with x hx
      have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
      have hpow : (1 / ‖x‖ ^ 2) ^ b.re = ‖x‖ ^ (-(2 * b.re)) := by
        rw [one_div, Real.inv_rpow (sq_nonneg _), ← Real.rpow_natCast_mul hx0.le,
          ← Real.rpow_neg hx0.le]
        norm_num
      simp only [Function.uncurry_apply_pair, hF, norm_mul (f x), integral_const_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos hx0, hz]
      rw [← Complex.ofReal_pow, hnorm _ (pow_pos hx0 2), hpow]
      ring
  calc mellin (gaussianPairing f) b
      = ∫ a in Ioi 0, ∫ x, F x a := by
        unfold mellin
        refine setIntegral_congr_fun measurableSet_Ioi fun a _ ↦ ?_
        simp only [gaussianPairing, smul_eq_mul, hF, ← integral_const_mul]
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        push_cast
        ring_nf
    _ = ∫ x, ∫ a in Ioi 0, F x a := (integral_integral_swap hint).symm
    _ = ∫ x, f x * ((‖x‖ : ℂ) ^ (-(2 * b)) * Complex.Gamma b) := by
        refine integral_congr_ae ?_
        filter_upwards [(volume : Measure (Euclidean d)).ae_ne 0] with x hx
        have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
        simp only [hF, integral_const_mul]
        rw [← Complex.ofReal_pow, Complex.integral_cpow_mul_exp_neg_mul_Ioi hb (pow_pos hx0 2)]
        congr 2
        rw [one_div, ← Complex.ofReal_inv, ← Real.rpow_two, ← Real.rpow_neg hx0.le,
          ← Complex.cpow_mul_ofReal_nonneg hx0.le]
        congr 1
        push_cast
        ring
    _ = Complex.Gamma b * ∫ x, f x * (‖x‖ : ℂ) ^ (-(2 * b)) := by
        rw [← integral_const_mul]
        exact integral_congr_ae (.of_forall fun x ↦ by ring)

/-- The Mellin reflection identity `M Φ_{𝓕 f}(b) = π^{d/2} (π²)^{b - d/2} M Φ_f(d/2 - b)`. -/
theorem mellin_gaussianPairing_fourier {d : ℕ} (f : TestFunction d) (b : ℂ) :
    mellin (gaussianPairing (𝓕 f)) b = (π : ℂ) ^ (d / 2 : ℂ) *
      (((π : ℂ) ^ 2) ^ (b - d / 2) * mellin (gaussianPairing f) (d / 2 - b)) := by
  have h : mellin (gaussianPairing (𝓕 f)) b = mellin (fun a : ℝ ↦ (π : ℂ) ^ (d / 2 : ℂ) •
      ((a : ℂ) ^ (-(d / 2 : ℂ)) • gaussianPairing f (π ^ 2 * a⁻¹))) b := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun a ha ↦ ?_
    have harg : (a : ℂ).arg ≠ π := by
      rw [Complex.arg_ofReal_of_nonneg ha.le]
      exact pi_pos.ne
    simp only [smul_eq_mul]
    rw [gaussianPairing_fourier f ha, div_eq_mul_inv (π : ℂ), div_eq_mul_inv (π ^ 2),
      ← Complex.ofReal_inv,
      Complex.mul_cpow_ofReal_nonneg pi_pos.le (inv_nonneg.2 ha.le), Complex.ofReal_inv,
      Complex.inv_cpow _ _ harg, ← Complex.cpow_neg, mul_assoc]
  rw [h, mellin_const_smul, mellin_cpow_smul,
    mellin_comp_inv (fun a : ℝ ↦ gaussianPairing f (π ^ 2 * a)),
    mellin_comp_mul_left _ _ (by positivity : (0 : ℝ) < π ^ 2)]
  simp only [smul_eq_mul, ← sub_eq_add_neg, neg_sub, Complex.ofReal_pow]

/-- The Riesz pairing identity on the strip `0 < Re s < d` (report §2.2):
`Γ((d-s)/2) ∫ 𝓕f(ξ) |ξ|^{s-d} dξ = π^{d/2 - s} Γ(s/2) ∫ f(x) |x|^{-s} dx`. -/
theorem fourier_riesz_pairing {d : ℕ} (hd : 0 < d) (f : TestFunction d) {s : ℂ} (hs : 0 < s.re)
    (hsd : s.re < d) :
    Complex.Gamma ((d - s) / 2) * ∫ ξ, (𝓕 f : TestFunction d) ξ * (‖ξ‖ : ℂ) ^ (s - d) =
      (π : ℂ) ^ (d / 2 - s) * (Complex.Gamma (s / 2) * ∫ x, f x * (‖x‖ : ℂ) ^ (-s)) := by
  set b : ℂ := (d - s) / 2 with hb
  have hre : b.re = (d - s.re) / 2 := by simp [hb]
  have hre' : (d / 2 - b : ℂ).re = s.re / 2 := by
    simp [hb]
    ring
  have h := mellin_gaussianPairing_fourier f b
  rwa [mellin_gaussianPairing hd (𝓕 f) (b := b) (by rw [hre]; linarith) (by rw [hre]; linarith),
    mellin_gaussianPairing hd f (b := d / 2 - b) (by rw [hre']; linarith)
      (by rw [hre']; linarith),
    show -(2 * b) = s - d by rw [hb]; ring, show (d / 2 - b : ℂ) = s / 2 by rw [hb]; ring,
    show -(2 * (s / 2)) = -s by ring, ← mul_assoc, ← Complex.ofReal_pow, ← Real.rpow_two,
    ← Complex.cpow_mul_ofReal_nonneg pi_pos.le,
    ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 pi_pos.ne'), Complex.ofReal_ofNat,
    show (d / 2 + 2 * (b - d / 2) : ℂ) = d / 2 - s by rw [hb]; ring] at h

/-! ### The Mellin–Fourier functional equation (report (9) and (10)) -/

/-- The Mellin–Hankel functional equation (9) of the report, for `0 < Re s < d`:
`M ĝ(s) = π^{λ - s} Γ(s/2) / Γ((d-s)/2) · M g(d - s)` for the radial profile `g` of `f`. -/
theorem radial_fourier_mellin_strip {d : ℕ} (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (s : ℂ) (hs : 0 < s.re) (hsd : s.re < (d : ℝ)) :
    mellin (radialProfile hd (𝓕 f : TestFunction d)) s = ((π : ℂ) ^ ((d : ℂ) / 2 - s) *
        Complex.Gamma (s / 2) / Complex.Gamma (((d : ℂ) - s) / 2)) *
            mellin (radialProfile hd f) ((d : ℂ) - s) := by
  have hΓ : Complex.Gamma ((d - s) / 2) ≠ 0 := by
    refine Complex.Gamma_ne_zero_of_re_pos ?_
    simp
    linarith
  have hS : (sphereArea d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (radialSurfaceArea_pos hd).ne'
  have h := fourier_riesz_pairing hd f hs hsd
  rw [integral_radialProfile_cpow hd _ (gaussianMellin_fourier_radial hf),
    show -s = (d - s) - d by ring, integral_radialProfile_cpow hd f hf, Complex.real_smul,
    Complex.real_smul] at h
  rw [div_mul_eq_mul_div, eq_div_iff hΓ]
  refine mul_left_cancel₀ hS ?_
  linear_combination h

/-- The Mellin multiplier identity (10) of the report: `X_{𝓕 f}(t) = m_λ(t) X_f(-t)`. -/
theorem radialMellinMultiplier {d : ℕ} (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (t : ℝ) : X_fℝ hd (𝓕 f : TestFunction d) t = m_ℓ ((d : ℝ) / 2) t * X_fℝ hd f (-t) := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.2 hd
  have hre : (d / 2 - I * t : ℂ).re = d / 2 := by simp
  have h := radial_fourier_mellin_strip hd f hf (d / 2 - I * t) (by rw [hre]; linarith)
    (by rw [hre]; linarith)
  have hphase : (π : ℂ) ^ (d / 2 - (d / 2 - I * t) : ℂ) = Complex.exp (I * t * log π) := by
    rw [sub_sub_cancel, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 pi_pos.ne'),
      ← Complex.ofReal_log pi_pos.le]
    congr 1
    ring
  rw [hphase, show (d : ℂ) - (d / 2 - I * t) = d / 2 + I * t by ring] at h
  unfold X_fℝ m_ℓ
  simpa [mul_neg, sub_neg_eq_add] using h

end

end CohnElkies
