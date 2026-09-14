import CohnElkies.UpperBound.GaussianError
import CohnElkies.UpperBound.Coverage
import CohnElkies.Asymptotics.Framework

/-!
# The signs of `f₊` and `f₋` (report §4.3, Theorem 4.1)

The saddle-source construction as an ordered `ε`-construction (`saddleOrderedUpperConstruction`),
the sign of a profile `f_P` at its saddle points on both branches (from the Gaussian approximation
and the range bounds on `P`), and the sign pattern of the pair: `Re f₊ ≥ 0` everywhere (small radii
by `SmallRadius`, large radii by the saddle points) and `Re f₋ ≤ 0` beyond the radius `R_{ε,d}`
(`saddleSourceEventualSigns`).
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section

open Filter MeasureTheory Set
open scoped FourierTransform SchwartzMap Topology

/-! ### The saddle-source construction as an ordered `ε`-construction -/

/-- The saddle-point pair `f_ε^±` is realized by Schwartz functions in every dimension. -/
def SaddleSourceSchwartzRealization : Prop := ∀ ε : ℝ, 0 < ε → a₀ε ε ≤ Aε ε → ∀ d : ℕ, 0 < d →
  ∃ fminus fplus : TestFunction d, (∀ x : Euclidean d, fminus x = fMinusFun ε d x) ∧
    (∀ x : Euclidean d, fplus x = fPlusFun ε d x)

/-- For small `ε` and large `d` the saddle-point pair has the sign pattern required by the
Cohn–Elkies conditions: `f_ε^+ ≥ 0` everywhere and `f_ε^- ≤ 0` outside the radius `R_ε`. -/
def SaddleSourceEventualSigns : Prop := ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ᶠ d : ℕ in atTop,
  (∀ x : Euclidean d, 0 ≤ (fPlusFun ε d x).re) ∧
    (∀ x : Euclidean d, R_ε ε d ≤ ‖x‖ → (fMinusFun ε d x).re ≤ 0)

/-- The ordered `ε`-construction built from the saddle-point pair, with normalized radius
`R_ε ε d / √d` and limiting radius `α_ε`. -/
def saddleOrderedUpperConstruction (hschwartz : SaddleSourceSchwartzRealization)
    (hsigns : SaddleSourceEventualSigns) : OrderedEpsilonUpperConstruction :=
  let hex := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (eventually_upper_shortCutoff_le_shortEndpoint.and hsigns)
  { epsilonBound := hex.choose
    epsilonBound_pos := hex.choose_spec.1
    normalizedRadius := fun ε d ↦ R_ε ε d / √(d : ℝ)
    limitingRadius := α_ε
    limitingRadius_tendsto := tendsto_limitingSaddleRadius
    normalizedRadius_tendsto := fun _ hε _ ↦ tendsto_saddleSourceRadius_normalized hε
    admissibleWitness := fun ε hε hsmall ↦ by
      obtain ⟨horder, hsignε⟩ := hex.choose_spec.2 ⟨hε, hsmall⟩
      filter_upwards [hsignε, eventually_gt_atTop 0] with d hsign hd
      obtain ⟨fminus, fplus, hminus, hplus⟩ := hschwartz ε hε horder d hd
      exact ⟨_, (saddleSourceAdmissible_normalizedCost hε hd horder (saddleSourceRadius_pos ε d)
        fminus fplus hminus hplus hsign.1 hsign.2).le⟩ }

end

noncomputable section

open Filter MeasureTheory Real Set
open scoped FourierTransform SchwartzMap Topology

/-- Beyond the small-radius ordinate `u_*` the saddle scale dominates `(log ℓ)/4`. -/
theorem scale_le_of_star_le {d : ℕ} (hd : 0 < d) (ε : ℝ) {u : ℝ} (hu : u_star ε d ≤ u) :
    log ((d : ℝ) / 2) / 4 ≤ (d : ℝ) / 2 * (1 + u) := by
  have hℓ : (0 : ℝ) < (d : ℝ) / 2 := by positivity
  have hstar : (d : ℝ) / 2 * (1 + u_star ε d) = log ((d : ℝ) / 2) / 4 := by
    rw [u_star]
    field_simp
    ring
  rw [← hstar]
  exact mul_le_mul_of_nonneg_left (by linarith) hℓ.le

theorem scale_le_of_one_le {ℓ u : ℝ} (hℓ : 0 < ℓ) (hu : 1 ≤ u) : log ℓ / 4 ≤ ℓ * (1 + u) := by
  nlinarith [log_le_sub_one_of_pos hℓ, mul_nonneg hℓ.le (sub_nonneg.mpr hu)]

/-- For `u₀ > -1` the saddle scale `ℓ(1 + u)`, `u ≥ u₀`, eventually dominates `(log ℓ)/4`. -/
theorem eventually_scale_le_of_le {u₀ : ℝ} (hu₀ : -1 < u₀) :
    ∀ᶠ ℓ : ℝ in atTop, ∀ u : ℝ, u₀ ≤ u → log ℓ / 4 ≤ ℓ * (1 + u) := by
  have hη : 0 < 4 * (1 + u₀) := by linarith
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    (tendsto_log_pow_div_atTop 1).eventually (Iio_mem_nhds hη)] with ℓ hℓ h u hu
  simp only [pow_one] at h
  rw [div_lt_iff₀ hℓ] at h
  nlinarith [mul_le_mul_of_nonneg_left (by linarith : 1 + u₀ ≤ 1 + u) hℓ.le]

/-! ### The sign of a profile at its saddle points (report §4.3) -/

/-- Report §4.3, first branch: at the saddle point of height `u` (`-1 < u ≤ 1 + ε/2`, with
`log λ / 4 ≤ λ(1 + u)`) the profile `f_P` of a saddle polynomial with range bounds on `u ≥ u₀`
has the sign of `P(iu)`, whatever its origin value `c`. -/
theorem eventually_mellinProfile_re_mul_pos_firstBranch : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    ∀ (P : ℂ → ℂ) (u₀ : ℝ), IsSaddlePolynomial ε P → SaddleRangeBounds P u₀ →
      ∀ᶠ d : ℕ in atTop, ∀ (c u : ℝ), -1 < u → u ≤ 1 + ε / 2 →
        log ((d : ℝ) / 2) / 4 ≤ (d : ℝ) / 2 * (1 + u) → u₀ ≤ u →
        0 < (P (I * (u : ℂ))).re *
          (mellinProfile ε ((d : ℝ) / 2) P c (exp (logRadius ε d u))).re := by
  filter_upwards [self_mem_nhdsWithin, eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_firstBranch_fullGaussianError] with ε hε horder hfull
  intro P u₀ hP hrange
  filter_upwards [tendsto_saddleResidue_dimension_half.eventually (hfull P u₀ hP hrange),
    eventually_gt_atTop 0] with d hdimen hd c u hu hupper hscale hu₀
  have hℓ : (0 : ℝ) < (d : ℝ) / 2 := by positivity
  rw [← saddleSourceStationaryLogRadius_eq_saddleLogRadius]
  exact mellinProfile_exp_re_mul_pos_of_gaussian_error hε hℓ hu horder hP c
    (hdimen u hu hupper hscale hu₀)

/-- Report §4.3, second branch: at the saddle point of height `u ≥ 1 + ε/2` the profile `f_P` of
a saddle polynomial with range bounds on `u ≥ u₀` has the sign of `P(iu)`. -/
theorem eventually_mellinProfile_re_mul_pos_secondBranch : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    ∀ (P : ℂ → ℂ) (u₀ : ℝ), IsSaddlePolynomial ε P → SaddleRangeBounds P u₀ →
      ∀ᶠ d : ℕ in atTop, ∀ (c u : ℝ), 1 + ε / 2 ≤ u → u₀ ≤ u →
        0 < (P (I * (u : ℂ))).re *
          (mellinProfile ε ((d : ℝ) / 2) P c (exp (logRadius ε d u))).re := by
  filter_upwards [self_mem_nhdsWithin, eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_secondBranch_fullGaussianError] with ε hε horder hfull
  intro P u₀ hP hrange
  filter_upwards [tendsto_saddleResidue_dimension_half.eventually (hfull P u₀ hP hrange),
    eventually_gt_atTop 0] with d hdimen hd c u hu hu₀
  change 0 < ε at hε
  have hδ : ε / 2 ≤ u - 1 := by linarith
  have hidentity : 1 + (u - 1) = u := by ring
  have hulower : -1 < u := by linarith
  have hℓ : (0 : ℝ) < (d : ℝ) / 2 := by positivity
  rw [← saddleSourceStationaryLogRadius_eq_saddleLogRadius]
  refine mellinProfile_exp_re_mul_pos_of_gaussian_error hε hℓ hulower horder hP c ?_
  simpa only [hidentity] using hdimen (u - 1) hδ (by rwa [hidentity])

/-- Report §4.3 with Corollary 4.9: for a saddle polynomial `P` with range bounds on `u ≥ u₀`
(`u₀ > -1`) whose values `P(iu)`, `u ≥ u₀`, have the sign `s`, the profile `f_P` has the sign
`s` at every radius `r ≥ e^{v(u₀)}`, for small `ε` and large `d`. -/
theorem eventually_mellinProfile_re_mul_pos_of_radius : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    ∀ (P : ℂ → ℂ) (u₀ s : ℝ), IsSaddlePolynomial ε P → SaddleRangeBounds P u₀ → -1 < u₀ →
      (∀ u : ℝ, u₀ ≤ u → 0 < s * (P (I * (u : ℂ))).re) →
      ∀ᶠ d : ℕ in atTop, ∀ (c r : ℝ), exp (logRadius ε d u₀) ≤ r →
        0 < s * (mellinProfile ε ((d : ℝ) / 2) P c r).re := by
  filter_upwards [eventually_saddleLogRadius_covers_Ici,
    eventually_mellinProfile_re_mul_pos_firstBranch,
    eventually_mellinProfile_re_mul_pos_secondBranch] with ε hcoverage hfirst hsecond
  intro P u₀ s hP hrange hu₀ hs
  filter_upwards [hfirst P u₀ hP hrange, hsecond P u₀ hP hrange, eventually_gt_atTop 0,
    tendsto_saddleResidue_dimension_half.eventually (eventually_scale_le_of_le hu₀)]
    with d hfirst_d hsecond_d hd hscale c r hr
  obtain ⟨u, hu, hlog⟩ := hcoverage d hd u₀ hu₀ r hr
  rw [← show exp (logRadius ε d u) = r by rw [hlog, exp_log ((exp_pos _).trans_le hr)]]
  have hmul : 0 < (P (I * (u : ℂ))).re *
      (mellinProfile ε ((d : ℝ) / 2) P c (exp (logRadius ε d u))).re := by
    rcases le_or_gt u (1 + ε / 2) with hbranch | hbranch
    · exact hfirst_d c u (by linarith) hbranch (hscale u hu) hu
    · exact hsecond_d c u hbranch.le hu
  nlinarith [mul_pos hmul (hs u hu), sq_nonneg (P (I * (u : ℂ))).re]

/-! ### The signs of `f₊` and `f₋` -/

/-- `Re f₊ > 0` at the saddles of the first branch `u_* ≤ u ≤ 1 + ε/2`. -/
theorem eventually_fPlus_re_pos_firstBranch : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ᶠ d : ℕ in atTop,
    ∀ u : ℝ, u_star ε d ≤ u → u ≤ 1 + ε / 2 →
      0 < (fPlus ε ((d : ℝ) / 2) (exp (logRadius ε d u))).re := by
  filter_upwards [self_mem_nhdsWithin, eventually_mellinProfile_re_mul_pos_firstBranch]
    with ε hε hfirst
  filter_upwards [hfirst (PPlus ε) (-1) (isSaddlePolynomial_PPlus ε) (saddleRangeBounds_PPlus hε),
    eventually_saddleSmallRadiusStarOrdinate_gt_neg_one ε, eventually_gt_atTop 0]
    with d hfirst_d hstar hd u hu hupper
  have hulower : -1 < u := hstar.trans_le hu
  rw [fPlus_eq_mellinProfile]
  exact (pos_iff_pos_of_mul_pos (hfirst_d (originValue ε ((d : ℝ) / 2)) u hulower hupper
    (scale_le_of_star_le hd ε hu) hulower.le)).mp (plusPolynomial_imaginary_re_pos hε hulower)

/-- `Re f₊ > 0` at the saddles of the second branch `1 + ε/2 ≤ u`. -/
theorem eventually_fPlus_re_pos_secondBranch : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ᶠ d : ℕ in atTop,
    ∀ u : ℝ, 1 + ε / 2 ≤ u → 0 < (fPlus ε ((d : ℝ) / 2) (exp (logRadius ε d u))).re := by
  filter_upwards [self_mem_nhdsWithin, eventually_mellinProfile_re_mul_pos_secondBranch]
    with ε hε hsecond
  filter_upwards [hsecond (PPlus ε) (-1) (isSaddlePolynomial_PPlus ε)
    (saddleRangeBounds_PPlus hε)] with d hsecond_d u hu
  change 0 < ε at hε
  have hulower : -1 < u := by linarith
  rw [fPlus_eq_mellinProfile]
  exact (pos_iff_pos_of_mul_pos (hsecond_d (originValue ε ((d : ℝ) / 2)) u hu hulower.le)).mp
    (plusPolynomial_imaginary_re_pos hε hulower)

/-- `Re f₊ ≥ 0` beyond the small radius `r_*`, covering both saddle branches. -/
theorem eventually_fPlus_nonneg_of_star : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ᶠ d : ℕ in atTop,
    ∀ r : ℝ, r_star ε d ≤ r → 0 ≤ (fPlus ε ((d : ℝ) / 2) r).re := by
  filter_upwards [eventually_saddleSmallRadiusStar_log_coverage,
    eventually_fPlus_re_pos_firstBranch, eventually_fPlus_re_pos_secondBranch]
    with ε hcoverage hfirst hsecond
  filter_upwards [hcoverage, hfirst, hsecond] with d hcov hfirst_d hsecond_d r hr
  obtain ⟨u, hu, hlog⟩ := hcov r hr
  rw [← show exp (logRadius ε d u) = r by
    rw [hlog, exp_log ((saddleSmallRadiusStar_pos ε d).trans_le hr)]]
  rcases le_or_gt u (1 + ε / 2) with hbranch | hbranch
  · exact (hfirst_d u hu hbranch).le
  · exact (hsecond_d u hbranch.le).le

/-- Report §4.3: `Re f₋ < 0` beyond the source radius `R_ε`, covering both saddle branches. -/
theorem eventually_fMinus_re_neg_of_radius : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ᶠ d : ℕ in atTop,
    ∀ r : ℝ, R_ε ε d ≤ r → (fMinus ε ((d : ℝ) / 2) r).re < 0 := by
  filter_upwards [self_mem_nhdsWithin, eventually_mellinProfile_re_mul_pos_of_radius]
    with ε hε hradius
  change 0 < ε at hε
  have hsign : ∀ u : ℝ, 1 + ε / 4 ≤ u → 0 < (-1 : ℝ) * (PMinus ε (I * (u : ℂ))).re :=
    fun u hu ↦ by linarith [minusPolynomial_imaginary_re_neg hε hu]
  filter_upwards [hradius (PMinus ε) (1 + ε / 4) (-1) (isSaddlePolynomial_PMinus ε)
    (saddleRangeBounds_PMinus hε) (by linarith) hsign] with d hd r hr
  rw [fMinus_eq_mellinProfile]
  linarith [hd (originValue ε ((d : ℝ) / 2)) r hr]

/-- `Re f₋ ≤ 0` beyond the source radius `R_ε`. -/
theorem eventually_fMinus_nonpos_of_radius : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ᶠ d : ℕ in atTop,
    ∀ r : ℝ, R_ε ε d ≤ r → (fMinus ε ((d : ℝ) / 2) r).re ≤ 0 := by
  filter_upwards [eventually_fMinus_re_neg_of_radius] with ε h
  filter_upwards [h] with d hd r hr
  exact (hd r hr).le

/-- Report §4: for small `ε` and large `d` the pair `f_ε^±` has the Cohn–Elkies sign pattern. -/
theorem saddleSourceEventualSigns : SaddleSourceEventualSigns := by
  unfold SaddleSourceEventualSigns
  filter_upwards [eventually_plusSaddleProfile_re_pos_on_star, eventually_fPlus_nonneg_of_star,
    eventually_fMinus_nonpos_of_radius] with ε hsmall hlarge hminus
  filter_upwards [hsmall, hlarge, hminus] with d hsmall_d hlarge_d hminus_d
  refine ⟨fun x ↦ ?_, fun x hx ↦ hminus_d ‖x‖ hx⟩
  change 0 ≤ (fPlus ε ((d : ℝ) / 2) ‖x‖).re
  rcases le_total ‖x‖ (r_star ε d) with hx | hx
  · exact (hsmall_d ‖x‖ (norm_nonneg x) hx).le
  · exact hlarge_d ‖x‖ hx

end

end CohnElkies
