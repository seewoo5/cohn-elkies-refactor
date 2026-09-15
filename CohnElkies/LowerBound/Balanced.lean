import CohnElkies.SchwartzTools
import CohnElkiesForMathlib.Analysis.Fourier.CompactSupport

/-!
# The balanced function and the anti-self-Fourier witness (report §3, (29)–(30))

For a radial admissible `F ∈ 𝒜_d^rad` the dilation `h(x) = F(a x)` with `a = (𝓕F(0)/F(0))^{1/d}`
is balanced (`𝓕 h (0) = h (0)`); nonnegative compactly supported self-Fourier functions vanish (via
the complex moment generating function of `h ≥ 0`), so `g = 𝓕 h - h` is a nonzero anti-self-Fourier
witness of radius `a`. Hence the normalized cost of `F` is at least `c` whenever no
anti-self-Fourier witness of radius `c √d` exists (`normalizedCost_ge_of_no_antiFourierWitness`),
the reduction of the lower bound of Theorem 1.1 to Proposition 3.7 (for general `F ∈ 𝒜_d`, first
replace `F` by its rotational average, `Admissible.radialize`, in `CohnElkies.Asymptotics.Main`).
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology RealInnerProductSpace ENNReal NNReal

/-! ### The balanced function `h(x) = F(a x)` (report (29)) -/

/-- The balancing scale `a = (𝓕F(0) / F(0))^{1/d}` of a radial admissible function `F`. -/
def balancingScale {d : ℕ} (f : RadialAdmissible d) : ℝ :=
  (((𝓕 f.function) 0).re / (f.function 0).re) ^ (d : ℝ)⁻¹

theorem balancingScale_pos {d : ℕ} (f : RadialAdmissible d) : 0 < balancingScale f :=
  Real.rpow_pos_of_pos (div_pos f.fourier_zero_pos (admissible_zero_pos f.toAdmissible)) _

theorem balancingScale_pow {d : ℕ} (f : RadialAdmissible d) (hd : 0 < d) :
    balancingScale f ^ d = ((𝓕 f.function) 0).re / (f.function 0).re :=
  Real.rpow_inv_natCast_pow
    (div_pos f.fourier_zero_pos (admissible_zero_pos f.toAdmissible)).le hd.ne'

/-- `1 / a = normalizedCost F · √d`. -/
theorem balancingScale_inv {d : ℕ} (f : RadialAdmissible d) (hd : 0 < d) :
    (balancingScale f)⁻¹ = normalizedCost f.toAdmissible * √d := by
  rw [balancingScale, normalizedCost, quotient, PackingBounds.fullQuotient,
    ← Real.inv_rpow (div_pos f.fourier_zero_pos (admissible_zero_pos f.toAdmissible)).le, inv_div,
    div_mul_cancel₀ _ (Real.sqrt_pos.2 (Nat.cast_pos.2 hd)).ne']

/-- The balanced function `h(x) = F(a x)`; it satisfies `𝓕 h (0) = h (0)`. -/
def balanced {d : ℕ} (f : RadialAdmissible d) : TestFunction d :=
  dilate f.function (balancingScale f) (balancingScale_pos f)

theorem balanced_real {d : ℕ} (f : RadialAdmissible d) : IsRealValued (balanced f) :=
  IsRealValued.dilate f.real _ _

theorem balanced_radial {d : ℕ} (f : RadialAdmissible d) : IsRadial (balanced f) :=
  f.radial.dilate _ _

theorem balanced_fourier_real {d : ℕ} (f : RadialAdmissible d) :
    IsRealValued (𝓕 (balanced f) : TestFunction d) := fun ξ ↦ by
  rw [balanced, fourier_dilate_apply, Complex.smul_im, f.fourier_real, smul_zero]

theorem balanced_fourier_nonneg {d : ℕ} (f : RadialAdmissible d) (ξ : Euclidean d) :
    0 ≤ ((𝓕 (balanced f) : TestFunction d) ξ).re := by
  rw [balanced, fourier_dilate_apply, Complex.smul_re]
  exact mul_nonneg (inv_nonneg.2 (pow_nonneg (balancingScale_pos f).le _)) (f.fourier_nonneg _)

theorem balanced_fourier_zero {d : ℕ} (f : RadialAdmissible d) (hd : 0 < d) :
    (𝓕 (balanced f) : TestFunction d) 0 = balanced f 0 := by
  rw [balanced, fourier_dilate_zero, balancingScale_pow f hd, dilate_zero]
  refine Complex.ext ?_ (by simp [f.fourier_real 0, f.real 0])
  simp only [Complex.smul_re, smul_eq_mul, inv_div]
  exact div_mul_cancel₀ _ f.fourier_zero_pos.ne'

theorem balanced_outside_nonpos {d : ℕ} (f : RadialAdmissible d) (x : Euclidean d)
    (hx : (balancingScale f)⁻¹ ≤ ‖x‖) : (balanced f x).re ≤ 0 :=
  f.outside_nonpos (balancingScale f • x) (by
    rw [norm_smul, Real.norm_of_nonneg (balancingScale_pos f).le, mul_comm]
    exact (inv_le_iff_one_le_mul₀ (balancingScale_pos f)).1 hx)

/-- If `𝓕 h = h`, the balanced function `h` vanishes outside the ball of radius `1 / a`. -/
theorem balanced_hasCompactSupport {d : ℕ} (f : RadialAdmissible d)
    (hself : (𝓕 (balanced f) : TestFunction d) = balanced f) :
    HasCompactSupport (balanced f : Euclidean d → ℂ) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Euclidean d) (balancingScale f)⁻¹) fun x hx ↦ ?_
  rw [mem_closedBall_zero_iff]
  by_contra! h
  have h0 := balanced_fourier_nonneg f x
  rw [hself] at h0
  exact hx (Complex.ext (le_antisymm (balanced_outside_nonpos f x h.le) h0) (balanced_real f x))

/-! ### Nonnegative compactly supported self-Fourier functions vanish -/

/-- The density `x ↦ Re g(x)` of a nonnegative test function, as an `ℝ≥0`-valued function. -/
def nnDensity {d : ℕ} (g : TestFunction d) (hg : ∀ x, 0 ≤ (g x).re) (x : Euclidean d) : ℝ≥0 :=
  ⟨(g x).re, hg x⟩

theorem nnDensity_measurable {d : ℕ} (g : TestFunction d) (hg : ∀ x, 0 ≤ (g x).re) :
    Measurable (nnDensity g hg) :=
  ((Complex.continuous_re.comp g.continuous).subtype_mk hg).measurable

/-- The finite measure `Re g(x) dx` of a nonnegative test function. -/
def nnMeasure {d : ℕ} (g : TestFunction d) (hg : ∀ x, 0 ≤ (g x).re) : Measure (Euclidean d) :=
  volume.withDensity fun x ↦ (nnDensity g hg x : ℝ≥0∞)

/-- For compactly supported `g`, the complex moment generating function of `X` under
`Re g(x) dx` is entire. -/
theorem analyticOnNhd_complexMGF_nnMeasure {d : ℕ} (g : TestFunction d)
    (hg : ∀ x, 0 ≤ (g x).re) (hcompact : HasCompactSupport (g : Euclidean d → ℂ))
    (X : Euclidean d → ℝ) (hX : Continuous X) :
    AnalyticOnNhd ℂ (ProbabilityTheory.complexMGF X (nnMeasure g hg)) univ := by
  have h : ProbabilityTheory.integrableExpSet X (nnMeasure g hg) = univ := by
    refine eq_univ_of_forall fun t ↦ ?_
    change Integrable _ (volume.withDensity _)
    rw [integrable_withDensity_iff_integrable_smul (nnDensity_measurable g hg)]
    simp only [nnDensity]
    have hcont : Continuous fun x : Euclidean d ↦ (g x).re * Real.exp (t * X x) :=
      (Complex.continuous_re.comp g.continuous).mul
        (Real.continuous_exp.comp (continuous_const.mul hX))
    exact hcont.integrable_of_hasCompactSupport (hcompact.comp_left Complex.zero_re).mul_right
  simpa [h] using ProbabilityTheory.analyticOnNhd_complexMGF (X := X) (μ := nnMeasure g hg)

/-- On the imaginary axis, the complex moment generating function of `x ↦ -2π ⟪x, e⟫` under
`Re g(x) dx` is the Fourier transform of `g` along `e`. -/
theorem complexMGF_nnMeasure {d : ℕ} (g : TestFunction d) (hreal : IsRealValued g)
    (hg : ∀ x, 0 ≤ (g x).re) (e : Euclidean d) (t : ℝ) :
    ProbabilityTheory.complexMGF (fun x ↦ -2 * π * ⟪x, e⟫) (nnMeasure g hg) (t * I) =
      (𝓕 g : TestFunction d) (t • e) := by
  rw [ProbabilityTheory.complexMGF, nnMeasure,
    integral_withDensity_eq_integral_smul (nnDensity_measurable g hg), SchwartzMap.fourier_coe,
    Real.fourier_eq']
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  have hx : ((nnDensity g hg x : ℝ) : ℂ) = g x := Complex.ext rfl (hreal x).symm
  simp only [NNReal.smul_def, Complex.real_smul, hx, real_inner_smul_right, smul_eq_mul,
    mul_comm (g x)]
  congr 2
  push_cast
  ring

/-- A nonnegative real compactly supported test function with `𝓕 g = g` vanishes (Fourier
analyticity; report, proof of Theorem 3.8). -/
theorem eq_zero_of_fourier_eq_self {d : ℕ} (hd : 0 < d) (g : TestFunction d)
    (hreal : IsRealValued g) (hg : ∀ x, 0 ≤ (g x).re)
    (hcompact : HasCompactSupport (g : Euclidean d → ℂ)) (hfixed : (𝓕 g : TestFunction d) = g) :
    g = 0 := by
  set e : Euclidean d := EuclideanSpace.single ⟨0, hd⟩ 1
  have he : ‖e‖ = 1 := by simp [e]
  obtain ⟨R, hR⟩ := hcompact.isBounded.subset_closedBall (0 : Euclidean d)
  have hvanish (t : ℝ) (ht : max R 0 < t) :
      ProbabilityTheory.complexMGF (fun x ↦ -2 * π * ⟪x, e⟫) (nnMeasure g hg) (t * I) = 0 := by
    rw [complexMGF_nnMeasure g hreal hg e t, hfixed]
    by_contra hne
    have hball := mem_closedBall_zero_iff.1 (hR (subset_tsupport _ hne))
    rw [norm_smul, he, mul_one, Real.norm_of_nonneg ((le_max_right R 0).trans ht.le)] at hball
    linarith [le_max_left R 0]
  have hzero := (analyticOnNhd_complexMGF_nnMeasure g hg hcompact _
    (by fun_prop)).eq_zero_of_forall_ofReal_mul_I_eq_zero _ hvanish
  have hg0 : ∫ x, g x = 0 := by
    simpa [SchwartzMap.fourier_coe, Real.fourier_eq'] using
      (complexMGF_nnMeasure g hreal hg e 0).symm.trans (congrFun hzero _)
  have hint : ∫ x, (g x).re = 0 := (integral_re g.integrable).trans (by rw [hg0]; rfl)
  have hre : (fun x ↦ (g x).re) = 0 :=
    ((Complex.continuous_re.comp g.continuous).ae_eq_iff_eq volume continuous_const).1
      ((integral_eq_zero_iff_of_nonneg hg g.integrable.re).1 hint)
  exact SchwartzMap.ext fun x ↦ Complex.ext (congrFun hre x) (hreal x)

/-! ### The anti-self-Fourier witness `g = 𝓕 h - h` (report (30)) -/

/-- The balanced anti-self-Fourier part `g = 𝓕 h - h` is nonzero: otherwise `h` would be a
nonzero nonnegative compactly supported self-Fourier function. -/
theorem antiFourierPart_balanced_ne_zero {d : ℕ} (f : RadialAdmissible d) (hd : 0 < d) :
    antiFourierPart (balanced f) ≠ 0 := fun hzero ↦ by
  have hself : (𝓕 (balanced f) : TestFunction d) = balanced f := sub_eq_zero.1 hzero
  have hnonneg (x : Euclidean d) : 0 ≤ (balanced f x).re := hself ▸ balanced_fourier_nonneg f x
  have h := eq_zero_of_fourier_eq_self hd _ (balanced_real f) hnonneg
    (balanced_hasCompactSupport f hself) hself
  exact (admissible_zero_pos f.toAdmissible).ne'
    (by simpa [balanced] using congrArg (fun g : TestFunction d ↦ (g 0).re) h)

/-- The scaling step of Theorem 3.8 of the report: if no anti-self-Fourier witness of radius
`c √d` exists, then every radial admissible function has normalized cost at least `c`. -/
theorem normalizedCost_ge_of_no_antiFourierWitness {d : ℕ} (f : RadialAdmissible d) (hd : 0 < d)
    (c : ℝ) (hno : IsEmpty (AntiSelfFourierWitness d (c * √d))) :
    c ≤ normalizedCost f.toAdmissible := by
  by_contra! hlt
  have hradius : (balancingScale f)⁻¹ ≤ c * √d := by
    rw [balancingScale_inv f hd]
    exact mul_le_mul_of_nonneg_right hlt.le (Real.sqrt_nonneg _)
  exact hno.false
    { toFun := antiFourierPart (balanced f)
      real := fun x ↦ by
        change (𝓕 (balanced f) x - balanced f x).im = 0
        rw [Complex.sub_im, balanced_fourier_real f x, balanced_real f x, sub_zero]
      radial := fun x y hxy ↦ by
        change 𝓕 (balanced f) x - balanced f x = 𝓕 (balanced f) y - balanced f y
        rw [IsRadial.fourier (balanced_radial f) x y hxy, balanced_radial f x y hxy]
      ne_zero := antiFourierPart_balanced_ne_zero f hd
      fourier_eq := by simpa using fourier_antiFourierPart _ (balanced_radial f)
      zero := antiFourierPart_zero _ (balanced_fourier_zero f hd)
      eventually_nonneg := fun x hx ↦ antiFourierPart_nonneg_of_signs _ _
        (balanced_fourier_nonneg f) (balanced_outside_nonpos f) x (hradius.trans hx) }

end

end CohnElkies
