import CohnElkies.UpperBound.ShellEstimates

/-!
# The damping exponents and saddle moments on the contour (report §4.3, (45)–(49))

The gamma damping `D_γ` and the saddle variance and third moment of report (45)–(48), the damping
exponent `D(u, T) = D_γ + D_B - D_s` of the contour `z = λ(1 + u) - iλT` (report (46)) with its
first-branch lower bound `D ≥ 2ε D_γ` (report (49)), and the identity for the shell phase on the
shifted contour.
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section
open Filter MeasureTheory Real Set
open scoped Topology

/-! ### The gamma damping `D_γ` and the saddle moments of report (45)–(48) -/

theorem upperGammaMeasureDensity_pos {ℓ η a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a) : 0 < μ_ℓ ℓ η a := by
  have hx : 0 < 2 * a / ℓ := by positivity
  unfold μ_ℓ
  exact div_pos (exp_pos _) (mul_pos ha (sub_pos.2 (exp_lt_one_iff.2 (by linarith))))

/-- The quadratic lower bound `x²/4 ≤ 1 - cos x` on `|x| ≤ 1`. -/
theorem upper_one_sub_cos_quadratic_lower {x : ℝ} (hx : |x| ≤ 1) : x ^ 2 / 4 ≤ 1 - cos x := by
  have h4 : |x| ^ 4 = x ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  have hquartic := cos_le_quartic (abs_nonneg x) hx
  rw [cos_abs, sq_abs, h4] at hquartic
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
  nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.2 hx2)]

/-- The integrand `(1 - cos (aT)) μ_{λ,η}(a)` of the gamma damping, report (45). -/
def upperGammaDampingIntegrand (ℓ η T a : ℝ) : ℝ := (1 - Real.cos (a * T)) * μ_ℓ ℓ η a

/-- `D_γ(T) = ∫₀^∞ (1 - cos (aT)) μ_{λ,η}(a) da`, the gamma damping of report (45). -/
def D_γ (ℓ η T : ℝ) : ℝ := ∫ a : ℝ in Ioi 0, upperGammaDampingIntegrand ℓ η T a

theorem upperGammaDampingIntegrand_integrable {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) (T : ℝ) :
    IntegrableOn (upperGammaDampingIntegrand ℓ η T) (Ioi 0) := by
  have hmeas : Measurable (upperGammaDampingIntegrand ℓ η T) := by
    unfold upperGammaDampingIntegrand μ_ℓ
    fun_prop
  refine ((upperGammaVarianceDensity_integrable hℓ hη).const_mul (T ^ 2 / 2)).mono'
    hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  have hdensity := (upperGammaMeasureDensity_pos (η := η) hℓ ha).le
  have hcos : 0 ≤ 1 - cos (a * T) := sub_nonneg.2 (cos_le_one _)
  have hquad : 1 - cos (a * T) ≤ (a * T) ^ 2 / 2 := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := a * T)]
  unfold upperGammaDampingIntegrand
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hcos hdensity)]
  calc
    (1 - cos (a * T)) * μ_ℓ ℓ η a ≤ (a * T) ^ 2 / 2 * μ_ℓ ℓ η a :=
      mul_le_mul_of_nonneg_right hquad hdensity
    _ = T ^ 2 / 2 * (a ^ 2 * μ_ℓ ℓ η a) := by ring

theorem upperGammaDamping_nonneg {ℓ η : ℝ} (hℓ : 0 < ℓ) (T : ℝ) : 0 ≤ D_γ ℓ η T := by
  unfold D_γ
  refine setIntegral_nonneg measurableSet_Ioi fun a ha ↦ ?_
  exact mul_nonneg (sub_nonneg.2 (cos_le_one _)) (upperGammaMeasureDensity_pos (η := η) hℓ ha).le

/-- On the window `0 < a ≤ min (η⁻¹, |T|⁻¹)` the gamma integrand is at least `λT²/(8e)`. -/
theorem upperGammaDampingIntegrand_lower_on_window {ℓ η T a : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η)
    (ha : 0 < a) (haη : a ≤ η⁻¹) (haT : a ≤ |T|⁻¹) (hT : T ≠ 0) :
    ℓ / (8 * exp 1) * T ^ 2 ≤ upperGammaDampingIntegrand ℓ η T a := by
  have hTa : |a * T| ≤ 1 := by
    rw [abs_mul, abs_of_pos ha]
    calc
      a * |T| ≤ |T|⁻¹ * |T| := by gcongr
      _ = 1 := inv_mul_cancel₀ (abs_ne_zero.2 hT)
  have heta : η * a ≤ 1 := by
    calc
      η * a ≤ η * η⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hη.ne'
  have hexp : (exp 1)⁻¹ ≤ exp (-η * a) := by
    rw [← exp_neg]
    exact exp_le_exp.2 (by linarith)
  unfold upperGammaDampingIntegrand
  calc
    ℓ / (8 * exp 1) * T ^ 2 = T ^ 2 / 4 * (ℓ / 2 * (exp 1)⁻¹) := by
      field_simp [(exp_pos 1).ne']
      ring
    _ ≤ T ^ 2 / 4 * (ℓ / 2 * exp (-η * a)) := by gcongr
    _ ≤ T ^ 2 / 4 * (a ^ 2 * μ_ℓ ℓ η a) :=
      mul_le_mul_of_nonneg_left (upperGammaVarianceDensity_pointwise_bounds (η := η) hℓ ha).1
        (by positivity)
    _ = (a * T) ^ 2 / 4 * μ_ℓ ℓ η a := by ring
    _ ≤ (1 - cos (a * T)) * μ_ℓ ℓ η a :=
      mul_le_mul_of_nonneg_right (upper_one_sub_cos_quadratic_lower hTa)
        (upperGammaMeasureDensity_pos (η := η) hℓ ha).le

/-- Report (45): `λ/(8e) · min (T²/η, |T|) ≤ D_γ(T)`. -/
theorem upperGammaDamping_lower_bound {ℓ η : ℝ} (hℓ : 0 < ℓ) (hη : 0 < η) (T : ℝ) :
    ℓ / (8 * exp 1) * min (T ^ 2 / η) |T| ≤ D_γ ℓ η T := by
  rcases eq_or_ne T 0 with rfl | hT
  · simp [D_γ, upperGammaDampingIntegrand]
  set q : ℝ := min η⁻¹ |T|⁻¹ with hq
  set c : ℝ := ℓ / (8 * exp 1) * T ^ 2 with hc
  have hqpos : 0 < q := lt_min (inv_pos.2 hη) (inv_pos.2 (abs_pos.2 hT))
  have hsubset : Ioc (0 : ℝ) q ⊆ Ioi 0 := fun a ha ↦ ha.1
  have hfull := upperGammaDampingIntegrand_integrable hℓ hη T
  have hconstant : IntegrableOn (fun _ : ℝ ↦ c) (Ioc 0 q) :=
    integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hmono := setIntegral_mono_on hconstant (hfull.mono_set hsubset) measurableSet_Ioc
    fun a ha ↦ upperGammaDampingIntegrand_lower_on_window hℓ hη ha.1
      (ha.2.trans (min_le_left _ _)) (ha.2.trans (min_le_right _ _)) hT
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] upperGammaDampingIntegrand ℓ η T := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    exact mul_nonneg (sub_nonneg.2 (cos_le_one _))
      (upperGammaMeasureDensity_pos (η := η) hℓ ha).le
  have hrestrict := setIntegral_mono_set hfull hnonneg
    (Filter.Eventually.of_forall fun a ha ↦ hsubset ha)
  have hconstint : (∫ _a : ℝ in Ioc (0 : ℝ) q, c) = q * c := by
    have hmeasure : (volume : Measure ℝ).real (Ioc (0 : ℝ) q) = q := by
      change ((volume : Measure ℝ) (Ioc (0 : ℝ) q)).toReal = q
      rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
      simp
    rw [setIntegral_const, hmeasure]
    rfl
  have hmin : q * T ^ 2 = min (T ^ 2 / η) |T| := by
    rw [hq, min_mul_of_nonneg _ _ (sq_nonneg T)]
    congr 1
    · rw [div_eq_mul_inv, mul_comm]
    · calc
        |T|⁻¹ * T ^ 2 = |T|⁻¹ * |T| ^ 2 := by rw [sq_abs]
        _ = |T| := by field_simp
  calc
    ℓ / (8 * exp 1) * min (T ^ 2 / η) |T| = q * c := by rw [hc, ← hmin]; ring
    _ = ∫ _a : ℝ in Ioc (0 : ℝ) q, c := hconstint.symm
    _ ≤ ∫ a : ℝ in Ioc (0 : ℝ) q, upperGammaDampingIntegrand ℓ η T a := hmono
    _ ≤ ∫ a : ℝ in Ioi 0, upperGammaDampingIntegrand ℓ η T a := hrestrict
    _ = D_γ ℓ η T := rfl

/-- The total damping `D_u = D_γ + D_B - D_s` of report (47). -/
def D_u (ε ℓ δ T : ℝ) : ℝ := D_γ ℓ (2 + δ) T + D_B ε ℓ δ T - D_s ε ℓ δ T

/-- The saddle variance `V_γ + (V_B - V_s)` of report (48). -/
def upperSaddleVariance (ε ℓ δ : ℝ) : ℝ := V_γ ℓ (2 + δ) + upperNetShellVariance ε δ

/-- The saddle third moment `M₃_γ + (M₃_B - M₃_s)` of report (48). -/
def M₃ (ε ℓ δ : ℝ) : ℝ := M₃_γ ℓ (2 + δ) + upperNetShellThirdMoment ε δ

theorem eventually_upperSaddleDamping_gamma_add_shell :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ ℓ : ℝ, 0 < ℓ → ∀ δ : ℝ, ε / 2 ≤ δ → ∀ T : ℝ,
      D_γ ℓ (2 + δ) T + 99 / 100 * D_B ε ℓ δ T ≤ D_u ε ℓ δ T := by
  filter_upwards [eventually_upper_shortShell_domination] with ε hdom ℓ hℓ δ hδ T
  unfold D_u
  linarith [hdom ℓ hℓ.le δ hδ T]

theorem eventually_upperSaddleVariance_bounds :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ ℓ : ℝ, 0 < ℓ → ∀ δ : ℝ, ε / 2 ≤ δ →
      1 / (2 * (2 + δ)) + 99 / 100 * V_B ε δ ≤ upperSaddleVariance ε ℓ δ ∧
        upperSaddleVariance ε ℓ δ ≤ (1 / (2 * (2 + δ)) + 1 / (ℓ * (2 + δ) ^ 2)) + V_B ε δ := by
  filter_upwards [self_mem_nhdsWithin, eventually_upper_netShellVariance_bounds]
    with ε hε hnet ℓ hℓ δ hδ
  change 0 < ε at hε
  obtain ⟨hγlow, hγhigh⟩ := upperGammaVariance_bounds hℓ (show (0 : ℝ) < 2 + δ by nlinarith)
  obtain ⟨hslow, hshigh⟩ := hnet δ hδ
  exact ⟨add_le_add hγlow hslow, add_le_add hγhigh hshigh⟩

theorem upperPositiveShellVariance_pos {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) : 0 < V_B ε δ := by
  have hB : 0 < Bε ε := by unfold Bε; positivity
  refine lt_of_lt_of_le ?_ (upperPositiveShellVariance_bounds hε hδ).1
  exact mul_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hB)) (shellWeight_pos ε))
    (exp_pos _)

theorem eventually_upperSaddleVariance_pos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ ℓ : ℝ, 0 < ℓ →
    ∀ δ : ℝ, ε / 2 ≤ δ → 0 < upperSaddleVariance ε ℓ δ := by
  filter_upwards [self_mem_nhdsWithin, eventually_upperSaddleVariance_bounds]
    with ε hε hbound ℓ hℓ δ hδ
  change 0 < ε at hε
  have hδ0 : (0 : ℝ) ≤ δ := by nlinarith
  have hshell := upperPositiveShellVariance_pos hε hδ0
  have hpositive : 0 < 1 / (2 * (2 + δ)) + 99 / 100 * V_B ε δ := by positivity
  exact hpositive.trans_le (hbound ℓ hℓ δ hδ).1

/-- The constant `B + 1 + A/100` comparing the shell third moment to the shell variance. -/
def upperSaddleShellThirdCoefficient (ε : ℝ) : ℝ := Bε ε + 1 + Aε ε / 100

/-- Report (48): the saddle third moment is dominated by the saddle variance. -/
theorem eventually_upperSaddleThirdMoment_le_variance : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ ℓ : ℝ, 1 ≤ ℓ →
    ∀ δ : ℝ, ε / 2 ≤ δ → M₃ ε ℓ δ ≤
      (2 + (100 / 99 : ℝ) * upperSaddleShellThirdCoefficient ε) * upperSaddleVariance ε ℓ δ := by
  filter_upwards [self_mem_nhdsWithin, eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_upper_netShellVariance_bounds, eventually_upper_netShellThirdMoment_bound]
    with ε hε horder hnet hthird ℓ hℓ δ hδ
  change 0 < ε at hε
  have hℓpos : 0 < ℓ := by linarith
  have hδ0 : 0 ≤ δ := by nlinarith
  have hηpos : (0 : ℝ) < 2 + δ := by linarith
  obtain ⟨hnetlower, hnetupper⟩ := hnet δ hδ
  have hpositiveShell := upperPositiveShellVariance_pos hε hδ0
  have hnetnonneg : 0 ≤ upperNetShellVariance ε δ := by linarith
  have hgammavariance : 0 ≤ V_γ ℓ (2 + δ) :=
    le_trans (by positivity : (0 : ℝ) ≤ 1 / (2 * (2 + δ)))
      (upperGammaVariance_bounds hℓpos hηpos).1
  have hgamma : M₃_γ ℓ (2 + δ) ≤ 2 * V_γ ℓ (2 + δ) := by
    have hsquare : (4 : ℝ) ≤ ℓ * (2 + δ) ^ 2 := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ ℓ - 1 by linarith) (sq_nonneg (2 + δ))]
    have hfirst : 1 / (2 * (2 + δ) ^ 2) ≤ 1 / (2 * (2 + δ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hsecond : 2 / (ℓ * (2 + δ) ^ 3) ≤ 1 / (2 * (2 + δ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hsquare hηpos.le]
    linarith [(upperGammaThirdMoment_bounds hℓpos hηpos).2,
      (upperGammaVariance_bounds hℓpos hηpos).1]
  have hC : 0 ≤ upperSaddleShellThirdCoefficient ε := by
    have hB : 0 ≤ Bε ε := by unfold Bε; positivity
    have hA : 0 ≤ Aε ε := ((show 0 < a₀ε ε by unfold a₀ε; positivity).trans_le horder).le
    unfold upperSaddleShellThirdCoefficient
    linarith
  have htransfer : V_B ε δ ≤ (100 / 99 : ℝ) * upperNetShellVariance ε δ := by linarith
  have hthirdshell : upperNetShellThirdMoment ε δ ≤ (100 / 99 : ℝ) *
      upperSaddleShellThirdCoefficient ε * upperNetShellVariance ε δ := by
    have h : upperNetShellThirdMoment ε δ ≤ upperSaddleShellThirdCoefficient ε * V_B ε δ :=
      hthird δ hδ
    nlinarith [mul_le_mul_of_nonneg_left htransfer hC]
  unfold M₃ upperSaddleVariance
  nlinarith [mul_nonneg hC hgammavariance, mul_nonneg hC hnetnonneg]

/-! ### The first-branch saddle damping of report (49) -/

/-- The short-shell margin factor `b(a) e^{εa}` is at most its value `1 - 2ε` at `a = 0`. -/
theorem shortMargin_mul_exp_le {ε a : ℝ} (hε : 0 < ε) (ha : 0 ≤ a) :
    bε ε a * exp (ε * a) ≤ 1 - 2 * ε := by
  have hderiv (x : ℝ) : HasDerivAt (fun t : ℝ ↦ bε ε t * exp (ε * t))
      (ε * exp (ε * x) * (bε ε x - 2)) x := by
    have hmargin : HasDerivAt (fun t : ℝ ↦ bε ε t) (-(2 * ε)) x := by
      convert! (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_const x (2 * ε)).mul
        ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x))) using 1
      simp [Pi.add_apply, id]
    have hexp : HasDerivAt (fun t : ℝ ↦ exp (ε * t)) (exp (ε * x) * ε) x := by
      convert! ((hasDerivAt_id x).const_mul ε).exp using 1; simp [id]
    convert! hmargin.mul hexp using 1; simp; ring
  have hanti : AntitoneOn (fun t : ℝ ↦ bε ε t * exp (ε * t)) (Ici (0 : ℝ)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (by unfold bε; fun_prop : Continuous fun t : ℝ ↦ bε ε t * exp (ε * t)).continuousOn
      (fun x _ ↦ (hderiv x).differentiableAt.differentiableWithinAt) fun x hx ↦ ?_
    rw [(hderiv x).deriv]
    have hx0 : 0 ≤ x := interior_subset hx
    have hmargin : bε ε x ≤ 1 := by
      unfold bε; nlinarith [mul_nonneg hε.le (show (0 : ℝ) ≤ 1 + x by linarith)]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hε.le (exp_pos _).le) (by linarith)
  simpa [bε] using hanti (show (0 : ℝ) ∈ Ici 0 by simp) ha ha

/-- Report (49): on the first branch `u ≤ 1 + ε/2` the short-shell ratio is at most `1 - 2ε`. -/
theorem upperFirstBranch_shortRatio_le {ε u a : ℝ} (hε : 0 < ε) (ha : 0 ≤ a)
    (hulower : -1 ≤ u) (huupper : u ≤ 1 + ε / 2) (hmargin : 0 ≤ bε ε a) :
    bε ε a * exp ((u - 1) * a) * (cosh (u * a) / cosh a) ≤ 1 - 2 * ε := by
  have hupper : bε ε a ≤ 1 - 2 * ε := by unfold bε; nlinarith [mul_nonneg hε.le ha]
  by_cases hu : u ≤ 1
  · have hexp : exp ((u - 1) * a) ≤ 1 :=
      exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hu) ha)
    have hratio : cosh (u * a) / cosh a ≤ 1 := by
      refine (div_le_one (cosh_pos a)).2 (cosh_le_cosh.2 ?_)
      rw [abs_mul, abs_of_nonneg ha]
      exact (mul_le_mul_of_nonneg_right (abs_le.2 ⟨hulower, hu⟩) ha).trans (by simp)
    calc
      bε ε a * exp ((u - 1) * a) * (cosh (u * a) / cosh a) ≤ bε ε a * 1 * 1 := by gcongr
      _ = bε ε a := by ring
      _ ≤ 1 - 2 * ε := by linarith
  · replace hu : 1 ≤ u := le_of_not_ge hu
    have hdouble : exp (2 * (u - 1) * a) ≤ exp (ε * a) :=
      exp_le_exp.2 (by nlinarith [mul_nonneg (show (0 : ℝ) ≤ ε - 2 * (u - 1) by linarith) ha])
    have hratio : cosh (u * a) / cosh a ≤ exp ((u - 1) * a) := by
      convert cosh_ratio_upper ha (show (0 : ℝ) ≤ u - 1 by linarith) using 1; ring_nf
    calc
      bε ε a * exp ((u - 1) * a) * (cosh (u * a) / cosh a) ≤
          bε ε a * exp ((u - 1) * a) * exp ((u - 1) * a) := by gcongr
      _ = bε ε a * exp (2 * (u - 1) * a) := by
        rw [mul_assoc, ← exp_add]
        congr 1
        ring_nf
      _ ≤ bε ε a * exp (ε * a) := mul_le_mul_of_nonneg_left hdouble hmargin
      _ ≤ 1 - 2 * ε := shortMargin_mul_exp_le hε ha
      _ ≤ 1 - 2 * ε := by linarith

/-- Report (49): pointwise, the short shell is dominated by `(1 - 2ε)` times the gamma density. -/
theorem upperFirstBranch_shortMeasure_pointwise {ε ℓ u a : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (ha : 0 < a) (hulower : -1 ≤ u) (huupper : u ≤ 1 + ε / 2) (hmargin : 0 ≤ bε ε a) :
    ℓ * (-w_s ε a) * cosh (u * a) ≤ (1 - 2 * ε) * μ_ℓ ℓ (1 + u) a := by
  have hbase : ℓ / 2 * exp (-(1 + u) * a) / a ^ 2 ≤ μ_ℓ ℓ (1 + u) a := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [(upperGammaVarianceDensity_pointwise_bounds (η := 1 + u) hℓ ha).1]
  have hidentity : ℓ * (-w_s ε a) * cosh (u * a) =
      bε ε a * exp ((u - 1) * a) * (cosh (u * a) / cosh a) *
        (ℓ / 2 * exp (-(1 + u) * a) / a ^ 2) := by
    have hexp : exp (a * (u - 1)) * exp (-(a * (1 + u))) = exp (-(2 * a)) := by
      rw [← exp_add]
      congr 1
      ring
    unfold w_s
    field_simp [ha.ne', (cosh_pos a).ne']
    rw [← hexp]
    ring
  rw [hidentity]
  calc
    _ ≤ (1 - 2 * ε) * (ℓ / 2 * exp (-(1 + u) * a) / a ^ 2) :=
      mul_le_mul_of_nonneg_right (upperFirstBranch_shortRatio_le hε ha.le hulower huupper hmargin)
        (by positivity)
    _ ≤ (1 - 2 * ε) * μ_ℓ ℓ (1 + u) a := mul_le_mul_of_nonneg_left hbase (by linarith)

theorem positiveShellDamping_nonneg {ε ℓ δ T : ℝ} (hℓ : 0 ≤ ℓ) : 0 ≤ D_B ε ℓ δ T := by
  unfold D_B
  refine mul_nonneg hℓ (intervalIntegral.integral_nonneg (by linarith) fun a ha ↦ ?_)
  unfold w_B
  exact mul_nonneg (mul_nonneg (div_nonneg (shellWeight_pos ε).le (cosh_pos a).le)
    (cosh_pos _).le) (sub_nonneg.2 (cos_le_one _))

/-- The damping exponent `D(u, T) = D_γ + D_B - D_s` of the contour `z = λ(1 + u) - iλT`,
report (46) and (49). -/
def saddleSourceContourDamping (ε ℓ u T : ℝ) : ℝ :=
  D_γ ℓ (1 + u) T + D_B ε ℓ (u - 1) T - D_s ε ℓ (u - 1) T

/-- Report (49): on the first branch the saddle damping dominates `2ε D_γ`. -/
theorem upperFirstBranchSaddleDamping_lower_bound {ε ℓ u : ℝ} (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (hulower : -1 < u) (huupper : u ≤ 1 + ε / 2) (horder : a₀ε ε ≤ Aε ε)
    (hmargin : ∀ a ∈ Icc (a₀ε ε) (Aε ε), 0 ≤ bε ε a) (T : ℝ) :
    2 * ε * D_γ ℓ (1 + u) T ≤ saddleSourceContourDamping ε ℓ u T := by
  have hη : (0 : ℝ) < 1 + u := by linarith
  have ha₀ : 0 < a₀ε ε := by unfold a₀ε; positivity
  have hsubset : Ioc (a₀ε ε) (Aε ε) ⊆ Ioi (0 : ℝ) := fun a ha ↦ ha₀.trans ha.1
  have hgamma := upperGammaDampingIntegrand_integrable hℓ hη T
  have hshortOn : IntegrableOn (fun a : ℝ ↦ ℓ * (-w_s ε a) * cosh (u * a) *
      (1 - cos (a * T))) (Ioc (a₀ε ε) (Aε ε)) := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le horder).mp ?_
    exact ((((shortShellDensity_intervalIntegrable hε horder).neg.const_mul ℓ).mul_continuousOn
        (by fun_prop : Continuous fun a : ℝ ↦ cosh (u * a)).continuousOn).mul_continuousOn
      (by fun_prop : Continuous fun a : ℝ ↦ 1 - cos (a * T)).continuousOn)
  have hmono := setIntegral_mono_on hshortOn ((hgamma.mono_set hsubset).const_mul (1 - 2 * ε))
    measurableSet_Ioc fun a ha ↦ by
      simpa [upperGammaDampingIntegrand, mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right (upperFirstBranch_shortMeasure_pointwise hε hεsmall hℓ
          (ha₀.trans ha.1) hulower.le huupper (hmargin a ⟨ha.1.le, ha.2⟩))
          (sub_nonneg.2 (cos_le_one (a * T)))
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] upperGammaDampingIntegrand ℓ (1 + u) T := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    exact mul_nonneg (sub_nonneg.2 (cos_le_one _)) (upperGammaMeasureDensity_pos hℓ ha).le
  have hrestrict := mul_le_mul_of_nonneg_left (setIntegral_mono_set hgamma hnonneg
    (Filter.Eventually.of_forall fun a ha ↦ hsubset ha)) (show (0 : ℝ) ≤ 1 - 2 * ε by linarith)
  have hshort : D_s ε ℓ (u - 1) T ≤ (1 - 2 * ε) * D_γ ℓ (1 + u) T := by
    calc
      D_s ε ℓ (u - 1) T = ∫ a : ℝ in Ioc (a₀ε ε) (Aε ε),
          ℓ * (-w_s ε a) * cosh (u * a) * (1 - cos (a * T)) := by
        unfold D_s
        rw [show 1 + (u - 1) = u by ring, ← intervalIntegral.integral_const_mul,
          intervalIntegral.integral_of_le horder]
        exact setIntegral_congr_fun measurableSet_Ioc fun a ha ↦ by ring
      _ ≤ ∫ a : ℝ in Ioc (a₀ε ε) (Aε ε),
          (1 - 2 * ε) * upperGammaDampingIntegrand ℓ (1 + u) T a := hmono
      _ = (1 - 2 * ε) * ∫ a : ℝ in Ioc (a₀ε ε) (Aε ε),
          upperGammaDampingIntegrand ℓ (1 + u) T a := integral_const_mul _ _
      _ ≤ (1 - 2 * ε) * ∫ a : ℝ in Ioi 0, upperGammaDampingIntegrand ℓ (1 + u) T a := hrestrict
      _ = (1 - 2 * ε) * D_γ ℓ (1 + u) T := rfl
  unfold saddleSourceContourDamping
  nlinarith [positiveShellDamping_nonneg (ε := ε) (δ := u - 1) (T := T) hℓ.le]

/-! ### The shell phase on the shifted contour (report (49)) -/

/-- The real part of the shell integral of `cos(x(T + iu)) - 1`. -/
theorem saddle_complexShellInterval_re (w : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hw : ContinuousOn w (Icc a b)) (T u : ℝ) :
    (∫ x in a..b, (w x : ℂ) * (Complex.cos ((x : ℂ) * ((T : ℂ) + I * (u : ℂ))) - 1)).re =
      ∫ x in a..b, w x * (cos (x * T) * cosh (x * u) - 1) := by
  have hcosre (x : ℝ) : (Complex.cos ((x : ℂ) * ((T : ℂ) + I * (u : ℂ)))).re =
      cos (x * T) * cosh (x * u) := by
    rw [show (x : ℂ) * ((T : ℂ) + I * (u : ℂ)) = (x : ℂ) * (T : ℂ) + (x : ℂ) * (u : ℂ) * I by
        ring,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.cos_add, Complex.cos_mul_I,
      Complex.sin_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin,
      ← Complex.ofReal_sinh]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, mul_one]
  have hF : IntervalIntegrable (fun x : ℝ ↦ (w x : ℂ) *
      (Complex.cos ((x : ℂ) * ((T : ℂ) + I * (u : ℂ))) - 1)) volume a b :=
    ((Complex.ofRealCLM.continuous.comp_continuousOn hw).mul (by fun_prop :
      Continuous fun x : ℝ ↦
        Complex.cos ((x : ℂ) * ((T : ℂ) + I * (u : ℂ))) - 1).continuousOn).intervalIntegrable_of_Icc
      hab
  calc
    (∫ x in a..b, (w x : ℂ) * (Complex.cos ((x : ℂ) * ((T : ℂ) + I * (u : ℂ))) - 1)).re =
        ∫ x in a..b, ((w x : ℂ) *
          (Complex.cos ((x : ℂ) * ((T : ℂ) + I * (u : ℂ))) - 1)).re :=
      (Complex.reCLM.intervalIntegral_comp_comm hF).symm
    _ = ∫ x in a..b, w x * (cos (x * T) * cosh (x * u) - 1) := by
      refine intervalIntegral.integral_congr fun x hx ↦ ?_
      rw [Complex.mul_re, Complex.sub_re, hcosre]
      simp

theorem shortShellDensity_continuousOn_support {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (w_s ε) (Icc (a₀ε ε) (Aε ε)) := by
  have hn : Continuous fun a : ℝ ↦ bε ε a * exp (-2 * a) := by unfold bε; fun_prop
  have hd : Continuous fun a : ℝ ↦ 2 * a ^ 2 * cosh a := by fun_prop
  unfold w_s
  refine (hn.continuousOn.div hd.continuousOn fun a ha ↦ ?_).neg
  have ha0 : 0 < a := (show 0 < a₀ε ε by unfold a₀ε; positivity).trans_le ha.1
  positivity

/-- Splitting a shell integral into its hyperbolic and its oscillatory part. -/
theorem saddle_shellInterval_hyperbolic_sub_oscillatory (w : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hw : ContinuousOn w (Icc a b)) (T u : ℝ) :
    (∫ x in a..b, w x * (cosh (x * u) - 1)) -
        ∫ x in a..b, w x * (cos (x * T) * cosh (x * u) - 1) =
      ∫ x in a..b, w x * cosh (u * x) * (1 - cos (x * T)) := by
  have hhyper : ContinuousOn (fun x : ℝ ↦ w x * (cosh (x * u) - 1)) (Icc a b) :=
    hw.mul (by fun_prop : Continuous fun x : ℝ ↦ cosh (x * u) - 1).continuousOn
  have hosc : ContinuousOn (fun x : ℝ ↦ w x * (cos (x * T) * cosh (x * u) - 1)) (Icc a b) :=
    hw.mul (by fun_prop : Continuous fun x : ℝ ↦ cos (x * T) * cosh (x * u) - 1).continuousOn
  rw [← intervalIntegral.integral_sub (hhyper.intervalIntegrable_of_Icc hab)
    (hosc.intervalIntegrable_of_Icc hab)]
  refine intervalIntegral.integral_congr fun x hx ↦ ?_
  rw [mul_comm u x]
  ring

/-- Report (49): `λ (h_ε(iu) - Re h_ε(T + iu)) = D_B(T) - D_s(T)`. -/
theorem saddleShellPhase_damping_identity {ε : ℝ} (hε : 0 < ε) (horder : a₀ε ε ≤ Aε ε)
    (ℓ T u : ℝ) : ℓ * (h_εI ε u - (h_ε ε ((T : ℂ) + I * (u : ℂ))).re) =
      D_B ε ℓ (u - 1) T - D_s ε ℓ (u - 1) T := by
  have hB : Bε ε ≤ Bε ε + 1 := by linarith
  have hshort := saddle_shellInterval_hyperbolic_sub_oscillatory (w_s ε) horder
    (shortShellDensity_continuousOn_support hε) T u
  have hpos := saddle_shellInterval_hyperbolic_sub_oscillatory (w_B ε) hB
    (positiveShellDensity_continuous ε).continuousOn T u
  have hre : (h_ε ε ((T : ℂ) + I * (u : ℂ))).re =
      (∫ a in a₀ε ε..Aε ε, w_s ε a * (cos (a * T) * cosh (a * u) - 1)) +
        ∫ a in Bε ε..Bε ε + 1, w_B ε a * (cos (a * T) * cosh (a * u) - 1) := by
    unfold h_ε
    rw [Complex.add_re]
    congr 1
    · exact saddle_complexShellInterval_re (w_s ε) horder
        (shortShellDensity_continuousOn_support hε) T u
    · exact saddle_complexShellInterval_re (w_B ε) hB
        (positiveShellDensity_continuous ε).continuousOn T u
  have hneg : (∫ a in a₀ε ε..Aε ε, -w_s ε a * cosh (u * a) * (1 - cos (a * T))) =
      -∫ a in a₀ε ε..Aε ε, w_s ε a * cosh (u * a) * (1 - cos (a * T)) := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun a ha ↦ by ring
  rw [hre]
  unfold h_εI D_B D_s
  rw [show 1 + (u - 1) = u by ring, hneg]
  linear_combination ℓ * hshort + ℓ * hpos

end

end CohnElkies
