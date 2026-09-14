import CohnElkies.UpperBound.Envelope
import CohnElkies.MellinFourier

/-!
# The radial profiles `f_P` as inverse Mellin transforms (report §4.1–4.2, Lemma 4.3)

The inverse Mellin kernel `r^{-z}`, the Gaussian pole representatives and the subtraction of
finitely many poles, the profile `f_P(r) = (1/2π) ∫ M_P(λ - it) r^{-λ + it} dt` on the critical
line (`mellinProfile`), the pair `f₊`, `f₋` (`fPlus`, `fMinus`), polynomial bounds on the Gamma
factor and the shell phase on shifted lines and horizontal strips, the integrability of the
weighted data, the rectangular contour shift, and the Fourier representation of the profiles:
`f_P` is the Fourier transform of an explicit `L¹` function, is real valued, and its Mellin data
satisfies the multiplier identity `m_λ X_P = X_{P(-·)}` behind `𝓕 f₋ = f₊` (report (40)).
-/

namespace CohnElkies
open scoped Real
open Complex (I)

noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace Topology
open Real

/-! ### The inverse Mellin kernel and the Gaussian pole representatives -/

/-- The inverse Mellin kernel `r ^ (-z)`. -/
def saddleMellinInversePower (r : ℝ) (z : ℂ) : ℂ := (r : ℂ) ^ (-z)

theorem saddleMellinInversePower_differentiable {r : ℝ} (hr : 0 < r) :
    Differentiable ℂ (saddleMellinInversePower r) := by
  have hform : saddleMellinInversePower r = fun z : ℂ ↦ Complex.exp (Complex.log r * -z) :=
    funext fun z ↦ Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') (-z)
  rw [hform]
  fun_prop

/-- The entire function `(exp (z ^ 2) - 1) / z`, i.e. the slope of `exp (z ^ 2)` at the origin. -/
def saddleGaussianPoleSlope (z : ℂ) : ℂ := dslope (fun w : ℂ ↦ Complex.exp (w ^ 2)) 0 z

theorem saddleGaussianPoleSlope_differentiable : Differentiable ℂ saddleGaussianPoleSlope :=
  differentiableOn_univ.mp ((Complex.differentiableOn_dslope (s := univ) (c := (0 : ℂ))
    univ_mem).mpr (Differentiable.differentiableOn (by fun_prop)))

theorem saddleGaussianPoleSlope_eq_of_ne {z : ℂ} (hz : z ≠ 0) :
    saddleGaussianPoleSlope z = (Complex.exp (z ^ 2) - 1) / z := by
  have h : (z - 0) • dslope (fun w : ℂ ↦ Complex.exp (w ^ 2)) 0 z =
      Complex.exp (z ^ 2) - Complex.exp ((0 : ℂ) ^ 2) :=
    sub_smul_dslope (fun w : ℂ ↦ Complex.exp (w ^ 2)) 0 z
  rw [smul_eq_mul, sub_zero, show ((0 : ℂ) ^ 2) = 0 by norm_num, Complex.exp_zero] at h
  unfold saddleGaussianPoleSlope
  rw [eq_div_iff hz]
  linear_combination h

/-- `exp ((z + 2n) ^ 2) / (z + 2n)`: a rapidly decaying stand-in for the polar part at `z = -2n`,
with the same residue. -/
def saddleGaussianPoleRepresentative (n : ℕ) (z : ℂ) : ℂ :=
  Complex.exp ((z + (2 * n : ℂ)) ^ 2) / (z + (2 * n : ℂ))

/-! ### Pole subtraction (Lemma 4.3)

The Mellin data `M₊`, `M₋` are meromorphic with simple poles at `z = -2n`, `n : ℕ`.  All the work
is done once for an abstract datum `M` with residues `ρ` and then specialised. -/

/-- `M` is meromorphic with at most simple poles at the points `z = -2n` (`n : ℕ`), the pole at
`-2n` having residue `ρ n`; the hypothesis of Lemma 4.3 of the report. -/
structure IsPoleDatum (M : ℂ → ℂ) (ρ : ℕ → ℂ) : Prop where
  meromorphic : Meromorphic M
  differentiableAt : ∀ z : ℂ, (∀ n : ℕ, z ≠ -(2 * n : ℂ)) → DifferentiableAt ℂ M z
  decomposition : ∀ n : ℕ, ∃ R : ℂ → ℂ, DifferentiableOn ℂ R (saddlePoleStrip n) ∧
    ∀ z ∈ saddlePoleStrip n, z ≠ -(2 * n : ℂ) → M z = ρ n / (z + (2 * n : ℂ)) + R z

/-- Lemma 4.3: the Mellin data `M_P` of an entire polynomial factor `P` is a pole datum with
residues `poleResidue ε ℓ P`. -/
theorem isPoleDatum_mellinData {ε : ℝ} (hε : 0 < ε) (horder : a₀ε ε ≤ Aε ε) (ℓ : ℝ)
    {P : ℂ → ℂ} (hP : Differentiable ℂ P) :
    IsPoleDatum (mellinData ε ℓ P) (poleResidue ε ℓ P) where
  meromorphic := mellinData_meromorphic hε horder ℓ hP
  differentiableAt _ hz := mellinData_differentiableAt_of_not_pole hε horder ℓ hP hz
  decomposition n := ⟨nthPoleRegularPart ε ℓ P n,
    nthPoleRegularPart_differentiableOn hε horder ℓ hP n,
    fun _ hz hne ↦ mellinData_nthPole_decomposition ε ℓ P hz hne⟩

/-- The Mellin datum `M` with the polar parts of its first `N + 1` poles subtracted. -/
def finitePoleSubtraction (M : ℂ → ℂ) (ρ : ℕ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  M z - ∑ n ∈ Finset.range (N + 1), ρ n / (z + (2 * n : ℂ))

/-- `finitePoleSubtraction` in meromorphic normal form: the removable singularities left at the
subtracted poles are filled in, so this is analytic on `{Re z > -2 (N + 1)}`. -/
def finitePoleRegularPart (M : ℂ → ℂ) (ρ : ℕ → ℂ) (N : ℕ) : ℂ → ℂ :=
  toMeromorphicNFOn (finitePoleSubtraction M ρ N) (saddleFinitePoleHalfPlane N)

/-- The regular part of Lemma 4.3: the Gaussian representatives are subtracted instead of the bare
polar parts, which keeps the difference rapidly decaying on horizontal lines. -/
def rapidPoleRegularPart (M : ℂ → ℂ) (ρ : ℕ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  finitePoleRegularPart M ρ N z -
    ∑ n ∈ Finset.range (N + 1), ρ n * saddleGaussianPoleSlope (z + (2 * n : ℂ))

section PoleDatum

variable {M : ℂ → ℂ} {ρ : ℕ → ℂ} {N : ℕ} {z : ℂ}

theorem poleCoordinate_ne_zero (hz : ∀ n : ℕ, z ≠ -(2 * n : ℂ)) (n : ℕ) :
    z + (2 * n : ℂ) ≠ 0 := fun h ↦ hz n (by linear_combination h)

theorem poleCoordinate_ne_zero_of_ne {m n : ℕ} (hmn : m ≠ n) :
    -(2 * n : ℂ) + (2 * m : ℂ) ≠ 0 := fun h ↦ by
  have h2 : 2 * n = 2 * m := by exact_mod_cast neg_add_eq_zero.mp h
  lia

theorem differentiableAt_polePart {s : Finset ℕ} (hs : ∀ n ∈ s, z + (2 * n : ℂ) ≠ 0) :
    DifferentiableAt ℂ (fun w : ℂ ↦ ∑ n ∈ s, ρ n / (w + (2 * n : ℂ))) z :=
  DifferentiableAt.fun_sum fun n hn ↦ (differentiableAt_const _).div (by fun_prop) (hs n hn)

theorem meromorphic_finitePoleSubtraction (hM : Meromorphic M) (ρ : ℕ → ℂ) (N : ℕ) :
    Meromorphic (finitePoleSubtraction M ρ N) :=
  hM.sub fun _ ↦ MeromorphicAt.fun_sum fun _ _ ↦ by fun_prop

theorem finitePoleRegularPart_eventuallyEq (hM : Meromorphic M) (ρ : ℕ → ℂ)
    (hz : z ∈ saddleFinitePoleHalfPlane N) :
    finitePoleRegularPart M ρ N =ᶠ[𝓝[≠] z] finitePoleSubtraction M ρ N :=
  (meromorphic_finitePoleSubtraction hM ρ N).meromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE hz

theorem exists_tendsto_finitePoleSubtraction (hM : IsPoleDatum M ρ)
    (hz : z ∈ saddleFinitePoleHalfPlane N) :
    ∃ c : ℂ, Tendsto (finitePoleSubtraction M ρ N) (𝓝[≠] z) (𝓝 c) := by
  by_cases hpole : ∃ n : ℕ, z = -(2 * n : ℂ)
  · obtain ⟨n, rfl⟩ := hpole
    obtain ⟨R, hRdiff, hRdec⟩ := hM.decomposition n
    have hmem : n ∈ Finset.range (N + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le ((saddlePole_mem_finiteHalfPlane_iff N n).mp hz))
    have hnhds : saddlePoleStrip n ∈ 𝓝 (-(2 * n : ℂ)) :=
      (isOpen_saddlePoleStrip n).mem_nhds (saddlePole_mem_strip n)
    have hother : DifferentiableAt ℂ (fun w : ℂ ↦
        ∑ m ∈ (Finset.range (N + 1)).erase n, ρ m / (w + (2 * m : ℂ)))
          (-(2 * n : ℂ)) :=
      differentiableAt_polePart fun m hm ↦ poleCoordinate_ne_zero_of_ne (Finset.mem_erase.mp hm).1
    have hreg : DifferentiableAt ℂ (fun w : ℂ ↦ R w -
        ∑ m ∈ (Finset.range (N + 1)).erase n, ρ m / (w + (2 * m : ℂ)))
          (-(2 * n : ℂ)) := (hRdiff.differentiableAt hnhds).sub hother
    refine ⟨_, Tendsto.congr' ?_
      (hreg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)⟩
    filter_upwards [nhdsWithin_le_nhds hnhds, self_mem_nhdsWithin] with w hw hne
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hne
    unfold finitePoleSubtraction
    rw [hRdec w hw hne,
      ← (Finset.range (N + 1)).sum_erase_add (fun m : ℕ ↦ ρ m / (w + (2 * m : ℂ))) hmem]
    ring
  · simp only [not_exists] at hpole
    have hdiff : DifferentiableAt ℂ (finitePoleSubtraction M ρ N) z :=
      (hM.differentiableAt z hpole).sub
        (differentiableAt_polePart fun n _ ↦ poleCoordinate_ne_zero hpole n)
    exact ⟨_, hdiff.continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩

theorem analyticOnNhd_finitePoleRegularPart (hM : IsPoleDatum M ρ) (N : ℕ) :
    AnalyticOnNhd ℂ (finitePoleRegularPart M ρ N) (saddleFinitePoleHalfPlane N) := by
  intro z hz
  have hnf := meromorphicNFOn_toMeromorphicNFOn (finitePoleSubtraction M ρ N)
    (saddleFinitePoleHalfPlane N) hz
  obtain ⟨c, hc⟩ := exists_tendsto_finitePoleSubtraction hM hz
  have hlim : Tendsto (finitePoleRegularPart M ρ N) (𝓝[≠] z) (𝓝 c) :=
    hc.congr' (finitePoleRegularPart_eventuallyEq hM.meromorphic ρ hz).symm
  exact hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp
    ((tendsto_nhds_iff_meromorphicOrderAt_nonneg hnf.meromorphicAt).mp ⟨c, hlim⟩)

theorem finitePoleRegularPart_eq_of_not_pole (hM : IsPoleDatum M ρ)
    (hz : z ∈ saddleFinitePoleHalfPlane N) (hpole : ∀ n : ℕ, z ≠ -(2 * n : ℂ)) :
    finitePoleRegularPart M ρ N z = finitePoleSubtraction M ρ N z := by
  have hsub : ContinuousAt (finitePoleSubtraction M ρ N) z :=
    ((hM.differentiableAt z hpole).sub
      (differentiableAt_polePart fun n _ ↦ poleCoordinate_ne_zero hpole n)).continuousAt
  have hreg := (analyticOnNhd_finitePoleRegularPart hM N z hz).continuousAt
  exact ((hreg.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hsub).mp
    (finitePoleRegularPart_eventuallyEq hM.meromorphic ρ hz)).eq_of_nhds

theorem differentiableOn_rapidPoleRegularPart (hM : IsPoleDatum M ρ) (N : ℕ) :
    DifferentiableOn ℂ (rapidPoleRegularPart M ρ N) (saddleFinitePoleHalfPlane N) := by
  unfold rapidPoleRegularPart
  refine (analyticOnNhd_finitePoleRegularPart hM N).differentiableOn.sub
    (DifferentiableOn.fun_sum fun n _ ↦ (differentiableOn_const _).mul ?_)
  exact (saddleGaussianPoleSlope_differentiable.comp (by fun_prop)).differentiableOn

theorem rapidPoleRegularPart_eq_of_not_pole (hM : IsPoleDatum M ρ)
    (hz : z ∈ saddleFinitePoleHalfPlane N) (hpole : ∀ n : ℕ, z ≠ -(2 * n : ℂ)) :
    rapidPoleRegularPart M ρ N z =
      M z - ∑ n ∈ Finset.range (N + 1), ρ n * saddleGaussianPoleRepresentative n z := by
  have hsum : (∑ n ∈ Finset.range (N + 1), ρ n / (z + (2 * n : ℂ))) +
      ∑ n ∈ Finset.range (N + 1), ρ n * saddleGaussianPoleSlope (z + (2 * n : ℂ)) =
      ∑ n ∈ Finset.range (N + 1), ρ n * saddleGaussianPoleRepresentative n z := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ ↦ ?_
    have hne := poleCoordinate_ne_zero hpole n
    rw [saddleGaussianPoleSlope_eq_of_ne hne]
    unfold saddleGaussianPoleRepresentative
    field_simp
    ring
  unfold rapidPoleRegularPart
  rw [finitePoleRegularPart_eq_of_not_pole hM hz hpole]
  unfold finitePoleSubtraction
  linear_combination -hsum

end PoleDatum

/-! ### The rectangular contour shift -/

/-- The integrand `r ^ (-z) · (regular part)` of the contour shift of Lemma 4.3. -/
def rapidContourIntegrand (M : ℂ → ℂ) (ρ : ℕ → ℂ) (N : ℕ) (r : ℝ) (z : ℂ) : ℂ :=
  saddleMellinInversePower r z * rapidPoleRegularPart M ρ N z

theorem saddleFinitePoleHalfPlane_reProdIm_subset {N : ℕ} {z w : ℂ}
    (hz : z ∈ saddleFinitePoleHalfPlane N) (hw : w ∈ saddleFinitePoleHalfPlane N) :
    ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) ⊆ saddleFinitePoleHalfPlane N := by
  intro u hu
  simp only [saddleFinitePoleHalfPlane, Set.mem_ofPred_eq] at hz hw ⊢
  rcases Set.mem_uIcc.mp (Complex.mem_reProdIm.mp hu).1 with h | h
  exacts [hz.trans_le h.1, hw.trans_le h.1]

/-- Cauchy's theorem for the contour integrand on rectangles inside `Re z > -2(N+1)`. -/
theorem rapidContourIntegrand_boundary_rectangle {M : ℂ → ℂ} {ρ : ℕ → ℂ} (hM : IsPoleDatum M ρ)
    (N : ℕ) {r : ℝ} (hr : 0 < r) (z w : ℂ) (hz : z ∈ saddleFinitePoleHalfPlane N)
    (hw : w ∈ saddleFinitePoleHalfPlane N) :
    (∫ x : ℝ in z.re..w.re, rapidContourIntegrand M ρ N r (x + z.im * I)) -
    (∫ x : ℝ in z.re..w.re, rapidContourIntegrand M ρ N r (x + w.im * I)) +
    I • (∫ y : ℝ in z.im..w.im, rapidContourIntegrand M ρ N r (w.re + y * I)) -
    I • (∫ y : ℝ in z.im..w.im, rapidContourIntegrand M ρ N r (z.re + y * I)) = 0 :=
  Complex.integral_boundary_rect_eq_zero_of_differentiableOn _ z w
    (((saddleMellinInversePower_differentiable hr).differentiableOn.mul
      (differentiableOn_rapidPoleRegularPart hM N)).mono
        (saddleFinitePoleHalfPlane_reProdIm_subset hz hw))

/-! ### The vertical line `z = ℓ - i t` and the functions `f₊`, `f₋` -/

theorem mellinShellArgument_vertical (ℓ t : ℝ) :
    I * (((ℓ : ℂ) - I * (t : ℂ)) - (ℓ : ℂ)) / (ℓ : ℂ) = (t : ℂ) / (ℓ : ℂ) := by
  rw [show I * (((ℓ : ℂ) - I * (t : ℂ)) - (ℓ : ℂ)) = (t : ℂ) by
    linear_combination (-(t : ℂ)) * Complex.I_sq]

theorem mellinEnvelope_vertical (ε ℓ t : ℝ) :
    mellinEnvelope ε ℓ ((ℓ : ℂ) - I * (t : ℂ)) = E ε ℓ t := by
  unfold mellinEnvelope E
  rw [mellinShellArgument_vertical,
    show (ℓ : ℂ) - ((ℓ : ℂ) - I * (t : ℂ)) = I * (t : ℂ) by ring]

/-- On the critical line `z = λ - it` the Mellin data is the spectrum: `M_P(λ - it) = X_P(t)`. -/
theorem mellinData_vertical (ε ℓ : ℝ) (P : ℂ → ℂ) (t : ℝ) :
    mellinData ε ℓ P ((ℓ : ℂ) - I * (t : ℂ)) = spectrum ε ℓ P t := by
  unfold mellinData spectrum
  rw [mellinEnvelope_vertical, mellinShellArgument_vertical]

/-- The radial profile `f_P` of a Mellin datum `M_P`: its inverse Mellin transform for `r ≠ 0`,
with the prescribed real value `c` at the origin. The profiles `f₊`, `f₋`, `f₀` of the report
are the cases `P = P₊, P₋, P₀` (with `c = f_P(0)` given by `poleResidue_zero`). -/
def mellinProfile (ε ℓ : ℝ) (P : ℂ → ℂ) (c r : ℝ) : ℂ :=
  if r = 0 then (c : ℂ) else mellinInv ℓ (mellinData ε ℓ P) r

/-- The radial function `x ↦ f_P(‖x‖)` on `ℝ ^ d`. -/
def mellinProfileFun (ε : ℝ) (d : ℕ) (P : ℂ → ℂ) (c : ℝ) (x : Euclidean d) : ℂ :=
  mellinProfile ε (d / 2 : ℝ) P c ‖x‖

theorem mellinProfile_zero (ε ℓ : ℝ) (P : ℂ → ℂ) (c : ℝ) : mellinProfile ε ℓ P c 0 = c := by
  simp [mellinProfile]

theorem mellinProfile_of_ne_zero (ε ℓ : ℝ) (P : ℂ → ℂ) (c : ℝ) {r : ℝ} (hr : r ≠ 0) :
    mellinProfile ε ℓ P c r = mellinInv ℓ (mellinData ε ℓ P) r := by
  simp [mellinProfile, hr]

theorem mellinProfileFun_radial (ε : ℝ) (d : ℕ) (P : ℂ → ℂ) (c : ℝ) :
    IsRadial (mellinProfileFun ε d P c) := fun _ _ hxy ↦ by simp only [mellinProfileFun, hxy]

@[simp] theorem mellinProfileFun_zero (ε : ℝ) (d : ℕ) (P : ℂ → ℂ) (c : ℝ) :
    mellinProfileFun ε d P c (0 : Euclidean d) = c := by
  simp [mellinProfileFun, mellinProfile]

/-- The radial profile `f₊` of the report, the inverse Mellin transform of `M₊`; definitionally
`mellinProfile ε ℓ (PPlus ε) (originValue ε ℓ)`. -/
def fPlus (ε ℓ r : ℝ) : ℂ := if r = 0 then (originValue ε ℓ : ℂ) else mellinInv ℓ (MPlus ε ℓ) r

/-- The radial profile `f₋` of the report, the inverse Mellin transform of `M₋`; definitionally
`mellinProfile ε ℓ (PMinus ε) (originValue ε ℓ)`. -/
def fMinus (ε ℓ r : ℝ) : ℂ := if r = 0 then (originValue ε ℓ : ℂ) else mellinInv ℓ (MMinus ε ℓ) r

/-- The radial function `x ↦ f₊(‖x‖)` on `ℝ ^ d`. -/
def fPlusFun (ε : ℝ) (d : ℕ) (x : Euclidean d) : ℂ := fPlus ε (d / 2 : ℝ) ‖x‖

/-- The radial function `x ↦ f₋(‖x‖)` on `ℝ ^ d`. -/
def fMinusFun (ε : ℝ) (d : ℕ) (x : Euclidean d) : ℂ := fMinus ε (d / 2 : ℝ) ‖x‖

@[simp] theorem plusSaddleFunction_zero (ε : ℝ) (d : ℕ) :
    fPlusFun ε d (0 : Euclidean d) = (originValue ε (d / 2 : ℝ) : ℂ) := by simp [fPlusFun, fPlus]

@[simp] theorem minusSaddleFunction_zero (ε : ℝ) (d : ℕ) :
    fMinusFun ε d (0 : Euclidean d) = (originValue ε (d / 2 : ℝ) : ℂ) := by simp [fMinusFun, fMinus]

theorem saddleFunction_zero_pos {ε : ℝ} (hε : 0 < ε) (d : ℕ) :
    0 < (fPlusFun ε d (0 : Euclidean d)).re ∧ 0 < (fMinusFun ε d (0 : Euclidean d)).re :=
  ⟨by simpa using saddleOriginValue_pos hε (d / 2 : ℝ),
    by simpa using saddleOriginValue_pos hε (d / 2 : ℝ)⟩

theorem fPlus_eq_mellinProfile (ε ℓ : ℝ) :
    fPlus ε ℓ = mellinProfile ε ℓ (PPlus ε) (originValue ε ℓ) := rfl

theorem fMinus_eq_mellinProfile (ε ℓ : ℝ) :
    fMinus ε ℓ = mellinProfile ε ℓ (PMinus ε) (originValue ε ℓ) := rfl

theorem fPlusFun_eq_mellinProfileFun (ε : ℝ) (d : ℕ) :
    fPlusFun ε d = mellinProfileFun ε d (PPlus ε) (originValue ε (d / 2 : ℝ)) := rfl

theorem fMinusFun_eq_mellinProfileFun (ε : ℝ) (d : ℕ) :
    fMinusFun ε d = mellinProfileFun ε d (PMinus ε) (originValue ε (d / 2 : ℝ)) := rfl

/-! ### Gamma factors on vertical and horizontal lines -/

theorem gamma_shiftedLine_polynomial_bound (a : ℝ) {t : ℝ} (ht : 1 ≤ |t|) (k m : ℕ)
    (hshift : 0 < a / 2 + (k : ℝ)) :
    |t| ^ m * ‖Complex.Gamma (((a : ℂ) + (t : ℂ) * I) / 2)‖ ≤
      (2 : ℝ) ^ (k + m) * Gamma (a / 2 + (k + m : ℝ)) := by
  have ht0 : t ≠ 0 := by rintro rfl; norm_num at ht
  have harg : ((a : ℂ) + (t : ℂ) * I) / 2 = (a / 2 : ℂ) + (t / 2 : ℂ) * I := by ring
  have hre : ((a / 2 : ℂ) + (t / 2 : ℂ) * I).re = a / 2 := by simp
  have him : ((a / 2 : ℂ) + (t / 2 : ℂ) * I).im = t / 2 := by simp
  have hpos : 0 < a / 2 + (k + m : ℝ) := by
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hne : ∀ j : ℕ, (a / 2 : ℂ) + (t / 2 : ℂ) * I + (j : ℂ) ≠ 0 := fun j hj ↦ by
    have him' : ((a / 2 : ℂ) + (t / 2 : ℂ) * I + (j : ℂ)).im = t / 2 := by simp
    rw [hj] at him'
    exact ht0 (by simpa using him'.symm)
  have hgamma : (|t| / 2) ^ (k + m) * ‖Complex.Gamma (((a : ℂ) + (t : ℂ) * I) / 2)‖ ≤
      Gamma (a / 2 + (k + m : ℝ)) := by
    have hbound :=
      Complex.abs_im_pow_mul_norm_Gamma_le hne (k + m) (by rw [hre]; push_cast; exact hpos)
    rw [hre, him] at hbound
    rw [harg]
    simpa [abs_div] using hbound
  calc |t| ^ m * ‖Complex.Gamma (((a : ℂ) + (t : ℂ) * I) / 2)‖
      ≤ |t| ^ (k + m) * ‖Complex.Gamma (((a : ℂ) + (t : ℂ) * I) / 2)‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ht (Nat.le_add_left m k)) (norm_nonneg _)
    _ = (2 : ℝ) ^ (k + m) *
          ((|t| / 2) ^ (k + m) * ‖Complex.Gamma (((a : ℂ) + (t : ℂ) * I) / 2)‖) := by
        rw [div_pow]
        field_simp
    _ ≤ (2 : ℝ) ^ (k + m) * Gamma (a / 2 + (k + m : ℝ)) := by gcongr

/-! ### The shell phase on horizontal strips -/

theorem norm_complexCos_le_cosh_im (z : ℂ) : ‖Complex.cos z‖ ≤ cosh z.im := by
  change ‖(Complex.exp (z * I) + Complex.exp (-z * I)) / 2‖ ≤ cosh z.im
  calc ‖(Complex.exp (z * I) + Complex.exp (-z * I)) / 2‖
      = ‖Complex.exp (z * I) + Complex.exp (-z * I)‖ / 2 := by
        rw [norm_div]
        norm_num
    _ ≤ (‖Complex.exp (z * I)‖ + ‖Complex.exp (-z * I)‖) / 2 := by
        gcongr
        exact norm_add_le _ _
    _ = cosh z.im := by
        rw [Complex.norm_exp, Complex.norm_exp, Real.cosh_eq]
        simp [Complex.mul_re, add_comm]

/-- The variation `∫ |w| (cosh (a H) + 1)` of the shell densities; it majorises `‖h_ε‖` on the
horizontal strip `|Im z| ≤ H`. -/
def horizontalShellVariation (ε H : ℝ) : ℝ :=
  (∫ a in a₀ε ε..Aε ε, |w_s ε a| * (cosh (a * H) + 1)) +
    ∫ a in Bε ε..Bε ε + 1, |w_B ε a| * (cosh (a * H) + 1)

theorem integral_abs_mul_cosh_mono {w : ℝ → ℝ} {p q H K : ℝ} (hpq : p ≤ q)
    (hw : IntervalIntegrable w volume p q) (hH : 0 ≤ H) (hHK : H ≤ K) :
    (∫ a in p..q, |w a| * (cosh (a * H) + 1)) ≤ ∫ a in p..q, |w a| * (cosh (a * K) + 1) := by
  refine intervalIntegral.integral_mono_on hpq (hw.abs.mul_continuousOn (by fun_prop))
    (hw.abs.mul_continuousOn (by fun_prop)) fun a _ ↦ ?_
  gcongr
  refine Real.cosh_le_cosh.mpr ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hH, abs_of_nonneg (hH.trans hHK)]
  exact mul_le_mul_of_nonneg_left hHK (abs_nonneg a)

theorem horizontalShellVariation_mono {ε : ℝ} (hε : 0 < ε) (horder : a₀ε ε ≤ Aε ε)
    {H K : ℝ} (hH : 0 ≤ H) (hHK : H ≤ K) :
    horizontalShellVariation ε H ≤ horizontalShellVariation ε K :=
  add_le_add
    (integral_abs_mul_cosh_mono horder (shortShellDensity_intervalIntegrable hε horder) hH hHK)
    (integral_abs_mul_cosh_mono (by linarith)
      ((positiveShellDensity_continuous ε).intervalIntegrable _ _) hH hHK)

theorem norm_integral_shellPhase_le {w : ℝ → ℝ} {p q H : ℝ} (hpq : p ≤ q) (hp : 0 ≤ p)
    (hw : IntervalIntegrable w volume p q) {z : ℂ} (hz : |z.im| ≤ H) :
    ‖∫ a in p..q, (w a : ℂ) * (Complex.cos ((a : ℂ) * z) - 1)‖ ≤
      ∫ a in p..q, |w a| * (cosh (a * H) + 1) := by
  have hH : 0 ≤ H := (abs_nonneg z.im).trans hz
  refine intervalIntegral.norm_integral_le_of_norm_le hpq (.of_forall fun a ha ↦ ?_)
    (hw.abs.mul_continuousOn (by fun_prop))
  have ha0 : 0 ≤ a := hp.trans ha.1.le
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg (w a))
  calc ‖Complex.cos ((a : ℂ) * z) - 1‖ ≤ cosh ((a : ℂ) * z).im + 1 := by
        refine (norm_sub_le _ _).trans ?_
        simpa using norm_complexCos_le_cosh_im ((a : ℂ) * z)
    _ ≤ cosh (a * H) + 1 := by
        gcongr
        refine Real.cosh_le_cosh.mpr ?_
        simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
          abs_mul, abs_of_nonneg ha0, abs_of_nonneg hH]
        exact mul_le_mul_of_nonneg_left hz ha0

theorem norm_mellinShellPhase_le {ε : ℝ} (hε : 0 < ε) (horder : a₀ε ε ≤ Aε ε)
    {z : ℂ} {H : ℝ} (hstrip : |z.im| ≤ H) : ‖h_ε ε z‖ ≤ horizontalShellVariation ε H := by
  have hcutoff : 0 < a₀ε ε := by unfold a₀ε; positivity
  have hlocation : 0 < Bε ε := by unfold Bε; positivity
  unfold h_ε horizontalShellVariation
  refine (norm_add_le _ _).trans (add_le_add
    (norm_integral_shellPhase_le horder hcutoff.le
      (shortShellDensity_intervalIntegrable hε horder) hstrip)
    (norm_integral_shellPhase_le (by linarith) hlocation.le
      ((positiveShellDensity_continuous ε).intervalIntegrable _ _) hstrip))

/-! ### Polynomial bounds on the shifted lines `Re z = a` -/

theorem mellinShellArgument_shiftedLine (ℓ a t : ℝ) :
    I * (((a : ℂ) + (t : ℂ) * I) - (ℓ : ℂ)) / (ℓ : ℂ) =
      ((-t / ℓ : ℝ) : ℂ) + I * (((a - ℓ) / ℓ : ℝ) : ℂ) := by
  have key : I * (((a : ℂ) + (t : ℂ) * I) - (ℓ : ℂ)) = ((-t : ℝ) : ℂ) + I * ((a - ℓ : ℝ) : ℂ) := by
    push_cast
    linear_combination (t : ℂ) * Complex.I_sq
  rw [key]
  push_cast
  ring

theorem norm_mellinPiFactor_shiftedLine (ℓ a t : ℝ) :
    ‖Complex.exp (((ℓ : ℂ) - ((a : ℂ) + (t : ℂ) * I)) * (log π : ℂ) / 2)‖ =
      exp ((ℓ - a) * log π / 2) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem norm_shellExponential_shiftedLine_le {ε ℓ : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : a₀ε ε ≤ Aε ε) (a t : ℝ) :
    ‖Complex.exp ((ℓ : ℂ) * h_ε ε (I * (((a : ℂ) + (t : ℂ) * I) - (ℓ : ℂ)) / (ℓ : ℂ)))‖ ≤
      exp (ℓ * horizontalShellVariation ε |(a - ℓ) / ℓ|) := by
  have him : |(I * (((a : ℂ) + (t : ℂ) * I) - (ℓ : ℂ)) / (ℓ : ℂ)).im| = |(a - ℓ) / ℓ| := by
    rw [mellinShellArgument_shiftedLine ℓ a t]
    simp [Complex.mul_im]
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  calc ((ℓ : ℂ) * h_ε ε (I * (((a : ℂ) + (t : ℂ) * I) - (ℓ : ℂ)) / (ℓ : ℂ))).re
      ≤ ‖(ℓ : ℂ) * h_ε ε (I * (((a : ℂ) + (t : ℂ) * I) - (ℓ : ℂ)) / (ℓ : ℂ))‖ :=
        Complex.re_le_norm _
    _ = ℓ * ‖h_ε ε (I * (((a : ℂ) + (t : ℂ) * I) - (ℓ : ℂ)) / (ℓ : ℂ))‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hℓ]
    _ ≤ ℓ * horizontalShellVariation ε |(a - ℓ) / ℓ| :=
        mul_le_mul_of_nonneg_left (norm_mellinShellPhase_le hε horder him.le) hℓ.le

theorem mellinShellArgument_shiftedLine_le {ℓ : ℝ} (hℓ : 0 < ℓ) (a : ℝ) {t : ℝ} (ht : 1 ≤ |t|) :
    1 + ‖I * (((a : ℂ) + (t : ℂ) * I) - (ℓ : ℂ)) / (ℓ : ℂ)‖ ≤
      (1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) * |t| := by
  have hnorm : ‖I * (((a : ℂ) + (t : ℂ) * I) - (ℓ : ℂ)) / (ℓ : ℂ)‖ ≤ |t| / ℓ + |(a - ℓ) / ℓ| := by
    rw [mellinShellArgument_shiftedLine ℓ a t]
    refine (norm_add_le _ _).trans_eq ?_
    simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, one_mul]
    rw [show (-t / ℓ : ℝ) = -(t / ℓ) by ring, abs_neg, abs_div, abs_of_pos hℓ]
  have hoffset := mul_le_mul_of_nonneg_left ht (abs_nonneg ((a - ℓ) / ℓ))
  rw [mul_one] at hoffset
  calc 1 + ‖I * (((a : ℂ) + (t : ℂ) * I) - (ℓ : ℂ)) / (ℓ : ℂ)‖
      ≤ 1 + (|t| / ℓ + |(a - ℓ) / ℓ|) := by gcongr
    _ ≤ |t| + |t| / ℓ + |(a - ℓ) / ℓ| * |t| := by linarith
    _ = (1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) * |t| := by
        rw [div_eq_mul_inv]
        ring

/-- The majorant of `|t| ^ m ‖M (a + i t)‖` on the vertical line `Re z = a` (Lemma 4.3). -/
def saddleShiftedLineMajorant (ε ℓ a : ℝ) (k m : ℕ) : ℝ :=
  (1 + |β ε|) * (1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) ^ 3 *
      ((2 : ℝ) ^ (k + (m + 3)) * Gamma (a / 2 + (k + (m + 3) : ℝ))) *
    exp ((ℓ - a) * log π / 2) * exp (ℓ * horizontalShellVariation ε |(a - ℓ) / ℓ|)

theorem gammaShift_pos {a : ℝ} {k : ℕ} (m : ℕ) (hshift : 0 < a / 2 + (k : ℝ)) :
    0 < a / 2 + (k + (m + 3) : ℝ) := by
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

theorem saddleShiftedLineMajorant_nonneg {ε ℓ a : ℝ} (hℓ : 0 < ℓ) (k m : ℕ)
    (hshift : 0 < a / 2 + (k : ℝ)) : 0 ≤ saddleShiftedLineMajorant ε ℓ a k m := by
  unfold saddleShiftedLineMajorant
  positivity [Real.Gamma_pos_of_pos (gammaShift_pos m hshift)]

/-- Lemma 4.3: on the line `Re z = a` the Mellin datum `M_P` decays faster than any polynomial,
with the explicit majorant `saddleShiftedLineMajorant`. -/
theorem mellinData_shiftedLine_polynomial_bound {ε ℓ : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : a₀ε ε ≤ Aε ε) {P : ℂ → ℂ} (hP : ∀ z : ℂ, ‖P z‖ ≤ (1 + |β ε|) * (1 + ‖z‖) ^ 3)
    (a : ℝ) {t : ℝ} (ht : 1 ≤ |t|) (k m : ℕ) (hshift : 0 < a / 2 + (k : ℝ)) :
    |t| ^ m * ‖mellinData ε ℓ P ((a : ℂ) + (t : ℂ) * I)‖ ≤ saddleShiftedLineMajorant ε ℓ a k m := by
  unfold mellinData
  have hC : (0 : ℝ) ≤ (1 + |β ε|) * (1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) ^ 3 := by positivity
  have hG : (0 : ℝ) ≤ (2 : ℝ) ^ (k + (m + 3)) * Gamma (a / 2 + (k + (m + 3) : ℝ)) := by
    positivity [Real.Gamma_pos_of_pos (gammaShift_pos m hshift)]
  have hgamma := gamma_shiftedLine_polynomial_bound a ht k (m + 3) hshift
  push_cast at hgamma
  have hpoly : ‖P (I * (((a : ℂ) + (t : ℂ) * I) - (ℓ : ℂ)) / (ℓ : ℂ))‖ ≤
      (1 + |β ε|) * (1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) ^ 3 * |t| ^ 3 := by
    calc _ ≤ (1 + |β ε|) * (1 + ‖I * (((a : ℂ) + (t : ℂ) * I) - (ℓ : ℂ)) / (ℓ : ℂ)‖) ^ 3 := hP _
      _ ≤ (1 + |β ε|) * ((1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) * |t|) ^ 3 := by
          gcongr
          exact mellinShellArgument_shiftedLine_le hℓ a ht
      _ = _ := by
          rw [mul_pow]
          ring
  unfold saddleShiftedLineMajorant
  calc |t| ^ m * ‖mellinEnvelope ε ℓ ((a : ℂ) + (t : ℂ) * I) *
          P (I * (((a : ℂ) + (t : ℂ) * I) - (ℓ : ℂ)) / (ℓ : ℂ))‖
      = |t| ^ m * ‖Complex.Gamma (((a : ℂ) + (t : ℂ) * I) / 2)‖ *
          ‖Complex.exp (((ℓ : ℂ) - ((a : ℂ) + (t : ℂ) * I)) * (log π : ℂ) / 2)‖ *
          ‖Complex.exp ((ℓ : ℂ) * h_ε ε (I * (((a : ℂ) + (t : ℂ) * I) - (ℓ : ℂ)) / (ℓ : ℂ)))‖ *
          ‖P (I * (((a : ℂ) + (t : ℂ) * I) - (ℓ : ℂ)) / (ℓ : ℂ))‖ := by
        unfold mellinEnvelope
        rw [norm_mul, norm_mul, norm_mul]
        ring
    _ ≤ |t| ^ m * ‖Complex.Gamma (((a : ℂ) + (t : ℂ) * I) / 2)‖ *
          ‖Complex.exp (((ℓ : ℂ) - ((a : ℂ) + (t : ℂ) * I)) * (log π : ℂ) / 2)‖ *
          ‖Complex.exp ((ℓ : ℂ) * h_ε ε (I * (((a : ℂ) + (t : ℂ) * I) - (ℓ : ℂ)) / (ℓ : ℂ)))‖ *
          ((1 + |β ε|) * (1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) ^ 3 * |t| ^ 3) :=
        mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ = (1 + |β ε|) * (1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) ^ 3 *
          (|t| ^ (m + 3) * ‖Complex.Gamma (((a : ℂ) + (t : ℂ) * I) / 2)‖) *
          ‖Complex.exp (((ℓ : ℂ) - ((a : ℂ) + (t : ℂ) * I)) * (log π : ℂ) / 2)‖ *
          ‖Complex.exp ((ℓ : ℂ) * h_ε ε (I * (((a : ℂ) + (t : ℂ) * I) - (ℓ : ℂ)) / (ℓ : ℂ)))‖ := by
        rw [pow_add]
        ring
    _ ≤ (1 + |β ε|) * (1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) ^ 3 *
          ((2 : ℝ) ^ (k + (m + 3)) * Gamma (a / 2 + (k + (m + 3) : ℝ))) *
          ‖Complex.exp (((ℓ : ℂ) - ((a : ℂ) + (t : ℂ) * I)) * (log π : ℂ) / 2)‖ *
          ‖Complex.exp ((ℓ : ℂ) * h_ε ε (I * (((a : ℂ) + (t : ℂ) * I) - (ℓ : ℂ)) / (ℓ : ℂ)))‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hgamma hC) (norm_nonneg _)) (norm_nonneg _)
    _ = (1 + |β ε|) * (1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) ^ 3 *
          ((2 : ℝ) ^ (k + (m + 3)) * Gamma (a / 2 + (k + (m + 3) : ℝ))) *
          exp ((ℓ - a) * log π / 2) *
          ‖Complex.exp ((ℓ : ℂ) * h_ε ε (I * (((a : ℂ) + (t : ℂ) * I) - (ℓ : ℂ)) / (ℓ : ℂ)))‖ := by
        rw [norm_mellinPiFactor_shiftedLine]
    _ ≤ _ := mul_le_mul_of_nonneg_left
        (norm_shellExponential_shiftedLine_le hε hℓ horder a t)
        (mul_nonneg (mul_nonneg hC hG) (Real.exp_pos _).le)

/-! ### Uniform bounds on horizontal strips -/

/-- The height of the strip swept out by `z ↦ I (z - ℓ) / ℓ` as `Re z` runs over `[A, B]`. -/
def horizontalStripHeight (ℓ A B : ℝ) : ℝ := max |(A - ℓ) / ℓ| |(B - ℓ) / ℓ|

theorem horizontalStripHeight_bound {ℓ A B x : ℝ} (hℓ : 0 < ℓ) (hx : x ∈ Set.Icc A B) :
    |(x - ℓ) / ℓ| ≤ horizontalStripHeight ℓ A B := by
  have hA : (A - ℓ) / ℓ ≤ (x - ℓ) / ℓ := (div_le_div_iff_of_pos_right hℓ).2 (by linarith [hx.1])
  have hB : (x - ℓ) / ℓ ≤ (B - ℓ) / ℓ := (div_le_div_iff_of_pos_right hℓ).2 (by linarith [hx.2])
  unfold horizontalStripHeight
  rw [abs_le]
  constructor
  · linarith [neg_abs_le ((A - ℓ) / ℓ), le_max_left |(A - ℓ) / ℓ| |(B - ℓ) / ℓ|]
  · linarith [le_abs_self ((B - ℓ) / ℓ), le_max_right |(A - ℓ) / ℓ| |(B - ℓ) / ℓ|]

/-- `saddleShiftedLineMajorant` with the shell variation frozen at the height of the strip. -/
def fixedStripMajorant (ε ℓ H a : ℝ) (k m : ℕ) : ℝ :=
  (1 + |β ε|) * (1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) ^ 3 *
      ((2 : ℝ) ^ (k + (m + 3)) * Gamma (a / 2 + (k + (m + 3) : ℝ))) *
    exp ((ℓ - a) * log π / 2) * exp (ℓ * horizontalShellVariation ε H)

theorem fixedStripMajorant_nonneg {ε ℓ H a : ℝ} (hℓ : 0 < ℓ) {k : ℕ} (m : ℕ)
    (hshift : 0 < a / 2 + (k : ℝ)) : 0 ≤ fixedStripMajorant ε ℓ H a k m := by
  unfold fixedStripMajorant
  positivity [Real.Gamma_pos_of_pos (gammaShift_pos m hshift)]

theorem shiftedLineMajorant_le_fixedStrip {ε ℓ a H : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : a₀ε ε ≤ Aε ε) (hH : |(a - ℓ) / ℓ| ≤ H) (k m : ℕ)
    (hshift : 0 < a / 2 + (k : ℝ)) :
    saddleShiftedLineMajorant ε ℓ a k m ≤ fixedStripMajorant ε ℓ H a k m := by
  have hgamma : 0 ≤ Gamma (a / 2 + (k + (m + 3) : ℝ)) :=
    (Real.Gamma_pos_of_pos (gammaShift_pos m hshift)).le
  have hC : (0 : ℝ) ≤ (1 + |β ε|) * (1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) ^ 3 := by positivity
  unfold saddleShiftedLineMajorant fixedStripMajorant
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
    (mul_nonneg (mul_nonneg hC (by positivity)) (Real.exp_pos _).le)
  exact mul_le_mul_of_nonneg_left
    (horizontalShellVariation_mono hε horder (abs_nonneg _) hH) hℓ.le

theorem fixedStripMajorant_continuousOn {A B : ℝ} (ε ℓ H : ℝ) {k : ℕ} (m : ℕ)
    (hshift : 0 < A / 2 + (k : ℝ)) :
    ContinuousOn (fun a : ℝ ↦ fixedStripMajorant ε ℓ H a k m) (Set.Icc A B) := by
  have harg : ContinuousOn (fun a : ℝ ↦ a / 2 + (k + (m + 3) : ℝ)) (Set.Icc A B) := by
    fun_prop
  have hgamma : ContinuousOn (fun a : ℝ ↦ Gamma (a / 2 + (k + (m + 3) : ℝ)))
      (Set.Icc A B) := by
    apply Real.differentiableOn_Gamma_Ioi.continuousOn.comp harg
    intro a ha
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    rw [Set.mem_Ioi]
    linarith [ha.1]
  unfold fixedStripMajorant
  exact ((((by fun_prop : ContinuousOn (fun a : ℝ ↦ (1 + |β ε|) *
    (1 + ℓ⁻¹ + |(a - ℓ) / ℓ|) ^ 3) (Set.Icc A B))).mul
      (continuousOn_const.mul hgamma)).mul (by fun_prop)).mul continuousOn_const

theorem exists_horizontalStrip_polynomial_bound {ε ℓ : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : a₀ε ε ≤ Aε ε) {F : ℂ → ℂ}
    (hF : ∀ a t : ℝ, 1 ≤ |t| → ∀ k m : ℕ, 0 < a / 2 + (k : ℝ) →
      |t| ^ m * ‖F ((a : ℂ) + (t : ℂ) * I)‖ ≤ saddleShiftedLineMajorant ε ℓ a k m)
    {A B : ℝ} (hAB : A ≤ B) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ Set.Icc A B, ∀ t : ℝ, 1 ≤ |t| →
      |t| ^ m * ‖F ((a : ℂ) + (t : ℂ) * I)‖ ≤ C := by
  obtain ⟨k, hk⟩ := exists_nat_gt (-(A / 2))
  have hshiftA : 0 < A / 2 + (k : ℝ) := by linarith
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image
    (fixedStripMajorant_continuousOn (A := A) (B := B) ε ℓ (horizontalStripHeight ℓ A B) m hshiftA)
  refine ⟨C, (fixedStripMajorant_nonneg (H := horizontalStripHeight ℓ A B) hℓ m hshiftA).trans
    (hC (Set.mem_image_of_mem _ ⟨le_rfl, hAB⟩)), fun a ha t ht ↦ ?_⟩
  have hshifta : 0 < a / 2 + (k : ℝ) := by linarith [ha.1]
  exact ((hF a t ht k m hshifta).trans (shiftedLineMajorant_le_fixedStrip hε hℓ horder
    (horizontalStripHeight_bound hℓ ha) k m hshifta)).trans (hC (Set.mem_image_of_mem _ ha))

/-- Lemma 4.3: uniform polynomial decay of `M_P` on horizontal strips. -/
theorem mellinData_horizontalStrip_polynomial_bound {ε ℓ : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : a₀ε ε ≤ Aε ε) {P : ℂ → ℂ} (hP : IsSaddlePolynomial ε P) {A B : ℝ} (hAB : A ≤ B)
    (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ Set.Icc A B, ∀ t : ℝ, 1 ≤ |t| →
      |t| ^ m * ‖mellinData ε ℓ P ((a : ℂ) + (t : ℂ) * I)‖ ≤ C :=
  exists_horizontalStrip_polynomial_bound hε hℓ horder
    (fun a _ ht k m hs ↦
      mellinData_shiftedLine_polynomial_bound hε hℓ horder hP.norm_le a ht k m hs) hAB m

/-! ### The envelope `E` on the critical line -/

theorem saddleEnvelope_conj (ε ℓ t : ℝ) : starRingEnd ℂ (E ε ℓ t) = E ε ℓ (-t) := by
  have hphase : starRingEnd ℂ (h_ε ε ((t : ℂ) / (ℓ : ℂ))) = h_ε ε (-((t : ℂ) / (ℓ : ℂ))) := by
    rw [← Complex.ofReal_div, mellinShellPhase_real_conj, mellinShellPhase_neg]
  unfold E
  simp only [map_mul, ← Complex.exp_conj, ← Complex.Gamma_conj, map_div₀, map_sub,
    Complex.conj_ofReal, Complex.conj_I, map_ofNat, Complex.ofReal_neg, neg_div]
  rw [hphase]
  congr 2 <;> congr 1 <;> ring

theorem norm_shellExponential_le {ε ℓ : ℝ} (hε : 0 < ε) (horder : a₀ε ε ≤ Aε ε) (t : ℝ) :
    ‖Complex.exp ((ℓ : ℂ) * h_ε ε ((t : ℂ) / (ℓ : ℂ)))‖ ≤
      exp (2 * |ℓ| * saddleShellTotalVariation ε) := by
  rw [← Complex.ofReal_div, mellinShellPhase_ofReal, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  refine Real.exp_le_exp.mpr ?_
  calc ℓ * realOscillatoryShellPhase ε (t / ℓ)
      ≤ |ℓ| * |realOscillatoryShellPhase ε (t / ℓ)| := by
        rw [← abs_mul]
        exact le_abs_self _
    _ ≤ |ℓ| * (2 * saddleShellTotalVariation ε) := by
        gcongr
        exact abs_realOscillatoryShellPhase_le hε horder (t / ℓ)
    _ = 2 * |ℓ| * saddleShellTotalVariation ε := by ring

theorem saddleEnvelope_vertical_polynomial_bound {ε ℓ : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : a₀ε ε ≤ Aε ε) (t : ℝ) (k : ℕ) :
    |t| ^ k * ‖E ε ℓ t‖ ≤
      (2 : ℝ) ^ k * Gamma (ℓ / 2 + k) * exp (2 * |ℓ| * saddleShellTotalVariation ε) := by
  have hz : 0 < (((ℓ : ℂ) - I * (t : ℂ)) / 2).re := by simpa using half_pos hℓ
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hgamma : (|t| / 2) ^ k * ‖Complex.Gamma (((ℓ : ℂ) - I * (t : ℂ)) / 2)‖ ≤
      Gamma (ℓ / 2 + k) := by
    simpa [abs_div] using Complex.abs_im_pow_mul_norm_Gamma_le
      (fun j ↦ Complex.add_natCast_ne_zero_of_re_pos hz j) k (by linarith)
  have hscaled : |t| ^ k * ‖Complex.Gamma (((ℓ : ℂ) - I * (t : ℂ)) / 2)‖ ≤
      (2 : ℝ) ^ k * Gamma (ℓ / 2 + k) := by
    calc |t| ^ k * ‖Complex.Gamma (((ℓ : ℂ) - I * (t : ℂ)) / 2)‖
        = (2 : ℝ) ^ k * ((|t| / 2) ^ k * ‖Complex.Gamma (((ℓ : ℂ) - I * (t : ℂ)) / 2)‖) := by
          rw [div_pow]
          field_simp
      _ ≤ (2 : ℝ) ^ k * Gamma (ℓ / 2 + k) := by gcongr
  have hunit : ‖Complex.exp (I * (t : ℂ) * (log π : ℂ) / 2)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  calc |t| ^ k * ‖E ε ℓ t‖
      = |t| ^ k * ‖Complex.Gamma (((ℓ : ℂ) - I * (t : ℂ)) / 2)‖ *
          ‖Complex.exp ((ℓ : ℂ) * h_ε ε ((t : ℂ) / (ℓ : ℂ)))‖ := by
        unfold E
        rw [norm_mul, norm_mul, hunit]
        ring
    _ ≤ (2 : ℝ) ^ k * Gamma (ℓ / 2 + k) * exp (2 * |ℓ| * saddleShellTotalVariation ε) := by
        gcongr
        exact norm_shellExponential_le hε horder t

end

noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace Topology
open Real

/-! ### Integrability from faster-than-polynomial decay -/

/-- A continuous function decaying faster than any polynomial has integrable moments. -/
theorem integrable_of_continuous_polynomial_decay {F : ℝ → ℂ} (hF : Continuous F)
    (hdecay : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ |t| → |t| ^ j * ‖F t‖ ≤ C) (k : ℕ) :
    Integrable fun t : ℝ ↦ (t : ℂ) ^ k * F t := by
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).bddAbove_image
    hF.norm.continuousOn
  obtain ⟨C, hC, htail⟩ := hdecay (k + 2)
  have hbnd : ∀ t ∈ Icc (-1 : ℝ) 1, ‖F t‖ ≤ M := fun t ht ↦ hM (mem_image_of_mem _ ht)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hbnd 0 (by norm_num))
  refine (integrable_inv_one_add_sq.const_mul (2 * (M + C))).mono' (by fun_prop)
    (.of_forall fun t ↦ ?_)
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : (0 : ℝ) < 1 + t ^ 2), norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs]
  have hX : 0 ≤ |t| ^ k * ‖F t‖ := by positivity
  by_cases ht : |t| ≤ 1
  · have h1 : |t| ^ k * ‖F t‖ ≤ M :=
      (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (abs_nonneg t) ht)).trans
        (hbnd t ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩)
    have h2 : t ^ 2 ≤ 1 := by rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg t) ht
    nlinarith
  · replace ht : 1 ≤ |t| := (not_le.1 ht).le
    have h1 : (1 : ℝ) ≤ t ^ 2 := by rw [← sq_abs]; exact one_le_pow₀ ht
    have h2 : |t| ^ k * ‖F t‖ * t ^ 2 ≤ C := by
      rw [show |t| ^ k * ‖F t‖ * t ^ 2 = |t| ^ (k + 2) * ‖F t‖ by rw [pow_add, sq_abs]; ring]
      exact htail t ht
    nlinarith

/-! ### The Mellin data on a vertical line avoiding the poles -/

/-- A vertical line `Re z = a` with `a ≠ -2n` for all `n` misses every pole `z = -2n`. -/
theorem saddleShiftedLine_ne_pole {a : ℝ} (hpole : ∀ n : ℕ, a ≠ -(2 * n : ℝ)) (t : ℝ)
    (n : ℕ) : (a : ℂ) + (t : ℂ) * I ≠ -(2 * n : ℂ) :=
  fun heq ↦ hpole n (by simpa using congrArg Complex.re heq)

/-- Lemma 4.3: every moment of a Mellin datum that is holomorphic off the poles and dominated by
`saddleShiftedLineMajorant` is integrable on a pole-free vertical line. -/
theorem shiftedLine_moment_integrable {M : ℂ → ℂ} {ε ℓ a : ℝ} (hℓ : 0 < ℓ)
    (hdiff : ∀ z : ℂ, (∀ n : ℕ, z ≠ -(2 * n : ℂ)) → DifferentiableAt ℂ M z)
    (hbound : ∀ {t : ℝ}, 1 ≤ |t| → ∀ k m : ℕ, 0 < a / 2 + (k : ℝ) →
      |t| ^ m * ‖M ((a : ℂ) + (t : ℂ) * I)‖ ≤ saddleShiftedLineMajorant ε ℓ a k m)
    (hpole : ∀ n : ℕ, a ≠ -(2 * n : ℝ)) (j : ℕ) :
    Integrable fun t : ℝ ↦ (t : ℂ) ^ j * M ((a : ℂ) + (t : ℂ) * I) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (-(a / 2))
  have hshift : 0 < a / 2 + (k : ℝ) := by linarith
  refine integrable_of_continuous_polynomial_decay (continuous_iff_continuousAt.2 fun t ↦ ?_)
    (fun m ↦ ⟨saddleShiftedLineMajorant ε ℓ a k m, saddleShiftedLineMajorant_nonneg hℓ k m hshift,
      fun t ht ↦ hbound ht k m hshift⟩) j
  have hline : ContinuousAt (fun u : ℝ ↦ (a : ℂ) + (u : ℂ) * I) t := by fun_prop
  simpa [Function.comp_def] using
    (hdiff _ (saddleShiftedLine_ne_pole hpole t)).continuousAt.comp_of_eq hline rfl

/-- Lemma 4.3: every moment of `M_P` is integrable on a pole-free vertical line. -/
theorem mellinData_shiftedLine_moment_integrable {ε ℓ a : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : a₀ε ε ≤ Aε ε) {P : ℂ → ℂ} (hP : IsSaddlePolynomial ε P)
    (hpole : ∀ n : ℕ, a ≠ -(2 * n : ℝ)) (j : ℕ) :
    Integrable fun t : ℝ ↦ (t : ℂ) ^ j * mellinData ε ℓ P ((a : ℂ) + (t : ℂ) * I) :=
  shiftedLine_moment_integrable hℓ
    (fun _ hz ↦ mellinData_differentiableAt_of_not_pole hε horder ℓ hP.differentiable hz)
    (fun ht k m hs ↦ mellinData_shiftedLine_polynomial_bound hε hℓ horder hP.norm_le a ht k m hs)
    hpole j

theorem plusSaddleMellinData_shiftedLine_moment_integrable {ε ℓ a : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : a₀ε ε ≤ Aε ε) (hpole : ∀ n : ℕ, a ≠ -(2 * n : ℝ)) (j : ℕ) :
    Integrable fun t : ℝ ↦ (t : ℂ) ^ j * MPlus ε ℓ ((a : ℂ) + (t : ℂ) * I) :=
  mellinData_shiftedLine_moment_integrable hε hℓ horder (isSaddlePolynomial_PPlus ε) hpole j

/-! ### The inverse Mellin weight `r ^ (-z)` -/

/-- `‖r ^ (-z)‖ = r ^ (-Re z)`. -/
theorem saddleMellinInversePower_shiftedLine_norm {r : ℝ} (hr : 0 < r) (a t : ℝ) :
    ‖saddleMellinInversePower r ((a : ℂ) + (t : ℂ) * I)‖ = r ^ (-a) := by
  unfold saddleMellinInversePower
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]; simp

/-- Multiplying by the weight `r ^ (-z)` preserves integrability along a vertical line. -/
theorem integrable_inversePower_mul {a r : ℝ} (hr : 0 < r) {G : ℝ → ℂ} (hG : Integrable G) :
    Integrable fun t : ℝ ↦ saddleMellinInversePower r ((a : ℂ) + (t : ℂ) * I) * G t := by
  have hweight : Continuous fun t : ℝ ↦ saddleMellinInversePower r ((a : ℂ) + (t : ℂ) * I) :=
    (saddleMellinInversePower_differentiable hr).continuous.comp (by fun_prop)
  refine (hG.norm.const_mul (r ^ (-a))).mono'
    (hweight.aestronglyMeasurable.mul hG.aestronglyMeasurable) (.of_forall fun t ↦ ?_)
  rw [norm_mul, saddleMellinInversePower_shiftedLine_norm hr]

theorem mellinData_shiftedLine_weighted_integrable {ε ℓ a r : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : a₀ε ε ≤ Aε ε) {P : ℂ → ℂ} (hP : IsSaddlePolynomial ε P)
    (hpole : ∀ n : ℕ, a ≠ -(2 * n : ℝ)) (hr : 0 < r) :
    Integrable fun t : ℝ ↦ saddleMellinInversePower r ((a : ℂ) + (t : ℂ) * I) *
      mellinData ε ℓ P ((a : ℂ) + (t : ℂ) * I) :=
  integrable_inversePower_mul hr
    (by simpa using mellinData_shiftedLine_moment_integrable hε hℓ horder hP hpole 0)

/-! ### The Gaussian pole representatives on a vertical line -/

theorem saddleGaussianPoleRepresentative_shiftedLine_norm (a t : ℝ) (n : ℕ) :
    ‖saddleGaussianPoleRepresentative n ((a : ℂ) + (t : ℂ) * I)‖ =
      exp ((a + (2 * n : ℝ)) ^ 2 - t ^ 2) /
        ‖(a : ℂ) + (t : ℂ) * I + (2 * n : ℂ)‖ := by
  unfold saddleGaussianPoleRepresentative
  rw [norm_div, Complex.norm_exp]
  congr 1
  simp [pow_two, Complex.mul_re, Complex.mul_im]

theorem saddleGaussianPoleRepresentative_shiftedLine_continuous {a : ℝ} (n : ℕ)
    (ha : a ≠ -(2 * n : ℝ)) :
    Continuous fun t : ℝ ↦ saddleGaussianPoleRepresentative n ((a : ℂ) + (t : ℂ) * I) := by
  have hline : Continuous fun t : ℝ ↦ (a : ℂ) + (t : ℂ) * I + (2 * n : ℂ) := by fun_prop
  have hnz : ∀ t : ℝ, (a : ℂ) + (t : ℂ) * I + (2 * n : ℂ) ≠ 0 := fun t hzero ↦ ha (by
    have hre := congrArg Complex.re hzero
    norm_num [Complex.mul_re] at hre
    linarith)
  unfold saddleGaussianPoleRepresentative
  exact (Complex.continuous_exp.comp (hline.pow 2)).div hline hnz

theorem saddleGaussianPoleRepresentative_shiftedLine_integrable {a : ℝ} (n : ℕ)
    (ha : a ≠ -(2 * n : ℝ)) :
    Integrable fun t : ℝ ↦ saddleGaussianPoleRepresentative n ((a : ℂ) + (t : ℂ) * I) := by
  have hgaussian : Integrable fun t : ℝ ↦ exp (-t ^ 2) := by
    simpa using integrable_exp_neg_mul_sq (b := (1 : ℝ)) one_pos
  have habs : 0 < |a + (2 * n : ℝ)| := abs_pos.2 fun h ↦ ha (by linarith)
  refine (hgaussian.const_mul (exp ((a + (2 * n : ℝ)) ^ 2) / |a + (2 * n : ℝ)|)).mono'
    (saddleGaussianPoleRepresentative_shiftedLine_continuous n ha).aestronglyMeasurable
    (.of_forall fun t ↦ ?_)
  have hden : |a + (2 * n : ℝ)| ≤ ‖(a : ℂ) + (t : ℂ) * I + (2 * n : ℂ)‖ := by
    simpa [Complex.mul_re] using
      Complex.abs_re_le_norm ((a : ℂ) + (t : ℂ) * I + (2 * n : ℂ))
  rw [saddleGaussianPoleRepresentative_shiftedLine_norm, sub_eq_add_neg, Real.exp_add]
  calc exp ((a + (2 * n : ℝ)) ^ 2) * exp (-t ^ 2) /
        ‖(a : ℂ) + (t : ℂ) * I + (2 * n : ℂ)‖
      ≤ exp ((a + (2 * n : ℝ)) ^ 2) * exp (-t ^ 2) / |a + (2 * n : ℝ)| := by gcongr
    _ = exp ((a + (2 * n : ℝ)) ^ 2) / |a + (2 * n : ℝ)| * exp (-t ^ 2) := by ring

theorem saddleGaussianPoleRepresentative_shiftedLine_weighted_integrable {a r : ℝ} (n : ℕ)
    (ha : a ≠ -(2 * n : ℝ)) (hr : 0 < r) :
    Integrable fun t : ℝ ↦ saddleMellinInversePower r ((a : ℂ) + (t : ℂ) * I) *
      saddleGaussianPoleRepresentative n ((a : ℂ) + (t : ℂ) * I) :=
  integrable_inversePower_mul hr (saddleGaussianPoleRepresentative_shiftedLine_integrable n ha)

/-! ### Uniform decay of the weighted data on a horizontal strip -/

/-- Multiplying by `r ^ (-z)` preserves uniform polynomial decay on a horizontal strip. -/
theorem weighted_horizontalStrip_bound {r A B : ℝ} (hr : 0 < r) (hAB : A ≤ B) {F : ℂ → ℂ}
    {m : ℕ} (hF : ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ Icc A B, ∀ t : ℝ, 1 ≤ |t| →
      |t| ^ m * ‖F ((a : ℂ) + (t : ℂ) * I)‖ ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ Icc A B, ∀ t : ℝ, 1 ≤ |t| →
      |t| ^ m * ‖saddleMellinInversePower r ((a : ℂ) + (t : ℂ) * I) *
        F ((a : ℂ) + (t : ℂ) * I)‖ ≤ C := by
  obtain ⟨C, hC, hF⟩ := hF
  have hpow : Continuous fun a : ℝ ↦ r ^ (-a) :=
    (Real.continuous_const_rpow hr.ne').comp continuous_neg
  obtain ⟨R, hR⟩ := (isCompact_Icc : IsCompact (Icc A B)).bddAbove_image hpow.continuousOn
  have hR0 : 0 ≤ R := (Real.rpow_nonneg hr.le (-A)).trans (hR (mem_image_of_mem _ ⟨le_rfl, hAB⟩))
  refine ⟨R * C, mul_nonneg hR0 hC, fun a ha t ht ↦ ?_⟩
  calc |t| ^ m * ‖saddleMellinInversePower r ((a : ℂ) + (t : ℂ) * I) * F ((a : ℂ) + (t : ℂ) * I)‖
      = r ^ (-a) * (|t| ^ m * ‖F ((a : ℂ) + (t : ℂ) * I)‖) := by
        rw [norm_mul, saddleMellinInversePower_shiftedLine_norm hr]; ring
    _ ≤ R * C := mul_le_mul (hR (mem_image_of_mem _ ha)) (hF a ha t ht) (by positivity) hR0

/-- Lemma 4.3: the integral over a horizontal segment vanishes in the limit when the integrand
decays like `1 / |t|` uniformly on the strip. -/
theorem saddleHorizontalIntegral_tendsto_zero {F : ℂ → ℂ} {A B C : ℝ} (hAB : A ≤ B)
    (hdecay : ∀ a ∈ Icc A B, ∀ t : ℝ, 1 ≤ |t| → |t| * ‖F ((a : ℂ) + (t : ℂ) * I)‖ ≤ C)
    (s : ℝ) (hs : |s| = 1) :
    Tendsto (fun T : ℝ ↦ ∫ a in A..B, F ((a : ℂ) + (s * T : ℂ) * I)) atTop (𝓝 0) := by
  have hmajor : Tendsto (fun T : ℝ ↦ C / T * |B - A|) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop tendsto_id).mul_const |B - A|
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun a ha ↦ ?_
  rw [uIoc_of_le hAB] at ha
  have habs : |s * T| = T := by rw [abs_mul, hs, one_mul, abs_of_nonneg hTpos.le]
  have htail := hdecay a ⟨ha.1.le, ha.2⟩ (s * T) (by rw [habs]; exact hT)
  rw [habs, Complex.ofReal_mul] at htail
  exact (le_div_iff₀ hTpos).2 (by linarith)

theorem mellinData_weighted_horizontalIntegral_tendsto_zero {ε ℓ r : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : a₀ε ε ≤ Aε ε) {P : ℂ → ℂ} (hP : IsSaddlePolynomial ε P) (hr : 0 < r) {A B : ℝ}
    (hAB : A ≤ B) (s : ℝ) (hs : |s| = 1) :
    Tendsto (fun T : ℝ ↦ ∫ a in A..B,
        saddleMellinInversePower r ((a : ℂ) + (s * T : ℂ) * I) *
          mellinData ε ℓ P ((a : ℂ) + (s * T : ℂ) * I)) atTop (𝓝 0) := by
  obtain ⟨C, -, hbound⟩ := weighted_horizontalStrip_bound hr hAB
    (mellinData_horizontalStrip_polynomial_bound hε hℓ horder hP hAB 1)
  exact saddleHorizontalIntegral_tendsto_zero
    (F := fun z ↦ saddleMellinInversePower r z * mellinData ε ℓ P z) hAB (by simpa using hbound)
    s hs

/-- On a horizontal strip the weighted Gaussian representative decays like `1 / |t|`. -/
theorem saddleGaussianPoleRepresentative_weighted_horizontalStrip_bound {r A B : ℝ} (hr : 0 < r)
    (hAB : A ≤ B) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ Icc A B, ∀ t : ℝ, 1 ≤ |t| →
      |t| * ‖saddleMellinInversePower r ((a : ℂ) + (t : ℂ) * I) *
        saddleGaussianPoleRepresentative n ((a : ℂ) + (t : ℂ) * I)‖ ≤ C := by
  have hcoef : Continuous fun a : ℝ ↦ r ^ (-a) * exp ((a + (2 * n : ℝ)) ^ 2) :=
    ((Real.continuous_const_rpow hr.ne').comp continuous_neg).mul (by fun_prop)
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc A B)).bddAbove_image hcoef.continuousOn
  refine ⟨C, le_trans (by positivity) (hC (mem_image_of_mem _ ⟨le_rfl, hAB⟩)), fun a ha t ht ↦ ?_⟩
  have hden : |t| ≤ ‖(a : ℂ) + (t : ℂ) * I + (2 * n : ℂ)‖ := by
    simpa [Complex.mul_im] using
      Complex.abs_im_le_norm ((a : ℂ) + (t : ℂ) * I + (2 * n : ℂ))
  have hdenpos : 0 < ‖(a : ℂ) + (t : ℂ) * I + (2 * n : ℂ)‖ :=
    (zero_lt_one.trans_le ht).trans_le hden
  rw [norm_mul, saddleMellinInversePower_shiftedLine_norm hr,
    saddleGaussianPoleRepresentative_shiftedLine_norm, sub_eq_add_neg, Real.exp_add]
  calc |t| * (r ^ (-a) * (exp ((a + (2 * n : ℝ)) ^ 2) * exp (-t ^ 2) /
        ‖(a : ℂ) + (t : ℂ) * I + (2 * n : ℂ)‖))
      = r ^ (-a) * exp ((a + (2 * n : ℝ)) ^ 2) *
          (exp (-t ^ 2) * (|t| / ‖(a : ℂ) + (t : ℂ) * I + (2 * n : ℂ)‖)) := by ring
    _ ≤ r ^ (-a) * exp ((a + (2 * n : ℝ)) ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left (mul_le_one₀ (Real.exp_le_one_iff.2 (neg_nonpos.2 (sq_nonneg t)))
          (by positivity) ((div_le_one hdenpos).2 hden)) (by positivity)
    _ = r ^ (-a) * exp ((a + (2 * n : ℝ)) ^ 2) := mul_one _
    _ ≤ C := hC (mem_image_of_mem _ ha)

/-- The same bound for a finite linear combination of Gaussian representatives. -/
theorem saddleFiniteGaussianPoleWeighted_horizontalStrip_bound {r A B : ℝ} (hr : 0 < r)
    (hAB : A ≤ B) (c : ℕ → ℂ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ Icc A B, ∀ t : ℝ, 1 ≤ |t| →
      |t| * ‖saddleMellinInversePower r ((a : ℂ) + (t : ℂ) * I) *
        ∑ n ∈ Finset.range (N + 1),
          c n * saddleGaussianPoleRepresentative n ((a : ℂ) + (t : ℂ) * I)‖ ≤ C := by
  choose G hG hbound using fun n : ℕ ↦
    saddleGaussianPoleRepresentative_weighted_horizontalStrip_bound hr hAB n
  refine ⟨∑ n ∈ Finset.range (N + 1), ‖c n‖ * G n,
    Finset.sum_nonneg fun n _ ↦ mul_nonneg (norm_nonneg _) (hG n), fun a ha t ht ↦ ?_⟩
  set z : ℂ := (a : ℂ) + (t : ℂ) * I with hzdef
  calc |t| * ‖saddleMellinInversePower r z *
        ∑ n ∈ Finset.range (N + 1), c n * saddleGaussianPoleRepresentative n z‖
      ≤ |t| * ∑ n ∈ Finset.range (N + 1),
          ‖saddleMellinInversePower r z * (c n * saddleGaussianPoleRepresentative n z)‖ := by
        rw [Finset.mul_sum]
        gcongr
        exact norm_sum_le _ _
    _ = ∑ n ∈ Finset.range (N + 1), ‖c n‖ *
          (|t| * ‖saddleMellinInversePower r z * saddleGaussianPoleRepresentative n z‖) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun n _ ↦ by rw [norm_mul, norm_mul, norm_mul]; ring
    _ ≤ ∑ n ∈ Finset.range (N + 1), ‖c n‖ * G n :=
        Finset.sum_le_sum fun n _ ↦
          mul_le_mul_of_nonneg_left (by rw [hzdef]; exact hbound n a ha t ht) (norm_nonneg _)

/-! ### The contour integrand of Lemma 4.3

All the work is done once for an abstract integrand `F` that agrees off the poles with
`r ^ (-z) M(z)` minus the weighted Gaussian representatives of the residues `ρ`. -/

section ContourIntegrand

variable {F M : ℂ → ℂ} {ρ : ℕ → ℂ} {N : ℕ} {r : ℝ}

/-- The defining property of the contour integrand of Lemma 4.3, off the poles. -/
abbrev IsRapidContourIntegrand (F M : ℂ → ℂ) (ρ : ℕ → ℂ) (N : ℕ) (r : ℝ) : Prop :=
  ∀ z ∈ saddleFinitePoleHalfPlane N, (∀ n : ℕ, z ≠ -(2 * n : ℂ)) →
    F z = saddleMellinInversePower r z * M z - saddleMellinInversePower r z *
      ∑ n ∈ Finset.range (N + 1), ρ n * saddleGaussianPoleRepresentative n z

/-- The contour integrand is integrable on a pole-free vertical line of the half-plane. -/
theorem contourIntegrand_shiftedLine_integrable {a : ℝ} (hr : 0 < r)
    (hhalf : -(2 * ((N : ℝ) + 1)) < a) (hpole : ∀ n : ℕ, a ≠ -(2 * n : ℝ))
    (hdata : Integrable fun t : ℝ ↦ M ((a : ℂ) + (t : ℂ) * I))
    (hF : IsRapidContourIntegrand F M ρ N r) :
    Integrable fun t : ℝ ↦ F ((a : ℂ) + (t : ℂ) * I) := by
  have hsum : Integrable fun t : ℝ ↦ saddleMellinInversePower r ((a : ℂ) + (t : ℂ) * I) *
      ∑ n ∈ Finset.range (N + 1),
        ρ n * saddleGaussianPoleRepresentative n ((a : ℂ) + (t : ℂ) * I) :=
    integrable_inversePower_mul hr (integrable_finsetSum _ fun n _ ↦
      (saddleGaussianPoleRepresentative_shiftedLine_integrable n (hpole n)).const_mul (ρ n))
  refine ((integrable_inversePower_mul (a := a) hr hdata).sub hsum).congr (.of_forall fun t ↦ ?_)
  refine (hF _ ?_ (saddleShiftedLine_ne_pole hpole t)).symm
  change -(2 * ((N : ℝ) + 1)) < ((a : ℂ) + (t : ℂ) * I).re
  simpa [Complex.mul_re] using hhalf

/-- Lemma 4.3: the contour integrand decays like `1 / |t|` uniformly on a horizontal strip. -/
theorem contourIntegrand_horizontalStrip_bound {A B : ℝ} (hr : 0 < r)
    (hhalf : -(2 * ((N : ℝ) + 1)) < A) (hAB : A ≤ B)
    (hstrip : ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ Icc A B, ∀ t : ℝ, 1 ≤ |t| →
      |t| ^ 1 * ‖M ((a : ℂ) + (t : ℂ) * I)‖ ≤ C)
    (hF : IsRapidContourIntegrand F M ρ N r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ Icc A B, ∀ t : ℝ, 1 ≤ |t| →
      |t| * ‖F ((a : ℂ) + (t : ℂ) * I)‖ ≤ C := by
  obtain ⟨D, hD, hdata⟩ := weighted_horizontalStrip_bound hr hAB hstrip
  obtain ⟨G, hG, hgauss⟩ := saddleFiniteGaussianPoleWeighted_horizontalStrip_bound hr hAB ρ N
  refine ⟨D + G, add_nonneg hD hG, fun a ha t ht ↦ ?_⟩
  have htne : t ≠ 0 := fun h ↦ by rw [h] at ht; norm_num at ht
  have hz : (a : ℂ) + (t : ℂ) * I ∈ saddleFinitePoleHalfPlane N := by
    change -(2 * ((N : ℝ) + 1)) < ((a : ℂ) + (t : ℂ) * I).re
    simpa [Complex.mul_re] using hhalf.trans_le ha.1
  rw [hF _ hz fun n heq ↦ htne (by simpa [Complex.mul_im] using congrArg Complex.im heq)]
  have h1 := mul_le_mul_of_nonneg_left (norm_sub_le
    (saddleMellinInversePower r ((a : ℂ) + (t : ℂ) * I) * M ((a : ℂ) + (t : ℂ) * I))
    (saddleMellinInversePower r ((a : ℂ) + (t : ℂ) * I) * ∑ n ∈ Finset.range (N + 1),
      ρ n * saddleGaussianPoleRepresentative n ((a : ℂ) + (t : ℂ) * I))) (abs_nonneg t)
  have h2 := hdata a ha t ht
  rw [pow_one] at h2
  linarith [hgauss a ha t ht]

end ContourIntegrand

/-! ### The rectangular contour shift -/

/-- `∫_{-T}^{T} (a + it)⁻¹ dt = 2 arctan (T / a)`. -/
theorem saddleCauchyPole_symmetric_intervalIntegral {a : ℝ} (ha : a ≠ 0) (T : ℝ) :
    (∫ t in -T..T, ((a : ℂ) + (t : ℂ) * I)⁻¹) = ((2 * arctan (T / a) : ℝ) : ℂ) := by
  have hnz : ∀ t : ℝ, (a : ℂ) + (t : ℂ) * I ≠ 0 := fun t hzero ↦
    ha (by simpa [Complex.mul_re] using congrArg Complex.re hzero)
  have hden : ∀ t : ℝ, a ^ 2 + t ^ 2 ≠ 0 := fun t ↦ by positivity
  have hderiv : ∀ t : ℝ, HasDerivAt (fun u : ℝ ↦ (arctan (u / a) : ℂ) -
      ((log (a ^ 2 + u ^ 2) / 2 : ℝ) : ℂ) * I) (((a : ℂ) + (t : ℂ) * I)⁻¹) t := fun t ↦ by
    have hatan : HasDerivAt (fun u : ℝ ↦ arctan (u / a)) (a / (a ^ 2 + t ^ 2)) t := by
      refine ((Real.hasDerivAt_arctan (t / a)).comp t
        ((hasDerivAt_id t).div_const a)).congr_deriv ?_
      field_simp [ha, hden t]
    have hlog : HasDerivAt (fun u : ℝ ↦ log (a ^ 2 + u ^ 2) / 2) (t / (a ^ 2 + t ^ 2)) t := by
      have hquad : HasDerivAt (fun u : ℝ ↦ a ^ 2 + u ^ 2) (2 * t) t := by
        simpa using ((hasDerivAt_id t).pow 2).const_add (a ^ 2)
      refine (((Real.hasDerivAt_log (hden t)).comp t hquad).div_const 2).congr_deriv ?_
      field_simp [hden t]
    have hvalue : ((a / (a ^ 2 + t ^ 2) : ℝ) : ℂ) - ((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * I =
        ((a : ℂ) + (t : ℂ) * I)⁻¹ := by
      have hcden : (a : ℂ) ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by
        simpa using Complex.ofReal_ne_zero.2 (hden t)
      apply (mul_eq_one_iff_eq_inv₀ (hnz t)).mp
      push_cast
      field_simp [hcden, Complex.I_sq]
      ring_nf
      simp [Complex.I_sq]
    exact hvalue ▸ hatan.ofReal_comp.sub (hlog.ofReal_comp.mul_const I)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hderiv t)
    (((by fun_prop : Continuous fun t : ℝ ↦ (a : ℂ) + (t : ℂ) * I).inv₀
      hnz).intervalIntegrable _ _)]
  simp [neg_div, Real.arctan_neg, pow_two]
  ring

/-- If the horizontal sides of the rectangles vanish in the limit, the vertical integrals of `F`
over the lines `Re z = A` and `Re z = B` agree. -/
theorem saddleInfiniteRectangle_vertical_integral_eq {F : ℂ → ℂ} {A B : ℝ}
    (hA : Integrable fun t : ℝ ↦ F ((A : ℂ) + (t : ℂ) * I))
    (hB : Integrable fun t : ℝ ↦ F ((B : ℂ) + (t : ℂ) * I))
    (hlower : Tendsto (fun T : ℝ ↦ ∫ a in A..B, F ((a : ℂ) + (-T : ℂ) * I)) atTop (𝓝 0))
    (hupper : Tendsto (fun T : ℝ ↦ ∫ a in A..B, F ((a : ℂ) + (T : ℂ) * I)) atTop (𝓝 0))
    (hrectangle : ∀ T : ℝ, (∫ a in A..B, F ((a : ℂ) + (-T : ℂ) * I)) -
      (∫ a in A..B, F ((a : ℂ) + (T : ℂ) * I)) +
      I * (∫ t in -T..T, F ((B : ℂ) + (t : ℂ) * I)) -
      I * (∫ t in -T..T, F ((A : ℂ) + (t : ℂ) * I)) = 0) :
    (∫ t : ℝ, F ((B : ℂ) + (t : ℂ) * I)) = ∫ t : ℝ, F ((A : ℂ) + (t : ℂ) * I) := by
  have hright := intervalIntegral_tendsto_integral hB tendsto_neg_atTop_atBot tendsto_id
  have hleft := intervalIntegral_tendsto_integral hA tendsto_neg_atTop_atBot tendsto_id
  have key := tendsto_nhds_unique
    (((hlower.sub hupper).add (tendsto_const_nhds.mul hright)).sub (tendsto_const_nhds.mul hleft))
    (tendsto_const_nhds.congr fun T ↦ (hrectangle T).symm)
  have hidentity : I * ((∫ t : ℝ, F ((B : ℂ) + (t : ℂ) * I)) -
      ∫ t : ℝ, F ((A : ℂ) + (t : ℂ) * I)) = 0 := by simpa [mul_sub] using key
  exact sub_eq_zero.mp ((mul_eq_zero.mp hidentity).resolve_left Complex.I_ne_zero)

/-- Lemma 4.3: the vertical integrals of the contour integrand over two pole-free lines of the
half-plane `Re z > -2 (N + 1)` agree. -/
theorem contourIntegrand_vertical_integral_eq {F M : ℂ → ℂ} {ρ : ℕ → ℂ} {N : ℕ} {r A B : ℝ}
    (hr : 0 < r) (hhalf : -(2 * ((N : ℝ) + 1)) < A) (hAB : A ≤ B)
    (hApole : ∀ n : ℕ, A ≠ -(2 * n : ℝ)) (hBpole : ∀ n : ℕ, B ≠ -(2 * n : ℝ))
    (hAint : Integrable fun t : ℝ ↦ M ((A : ℂ) + (t : ℂ) * I))
    (hBint : Integrable fun t : ℝ ↦ M ((B : ℂ) + (t : ℂ) * I))
    (hstrip : ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ Icc A B, ∀ t : ℝ, 1 ≤ |t| →
      |t| ^ 1 * ‖M ((a : ℂ) + (t : ℂ) * I)‖ ≤ C)
    (hF : IsRapidContourIntegrand F M ρ N r)
    (hrect : ∀ z w : ℂ, z ∈ saddleFinitePoleHalfPlane N → w ∈ saddleFinitePoleHalfPlane N →
      (∫ x : ℝ in z.re..w.re, F (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, F (x + w.im * I)) +
        I • (∫ y : ℝ in z.im..w.im, F (w.re + y * I)) -
        I • (∫ y : ℝ in z.im..w.im, F (z.re + y * I)) = 0) :
    (∫ t : ℝ, F ((B : ℂ) + (t : ℂ) * I)) = ∫ t : ℝ, F ((A : ℂ) + (t : ℂ) * I) := by
  obtain ⟨C, -, hbound⟩ := contourIntegrand_horizontalStrip_bound hr hhalf hAB hstrip hF
  refine saddleInfiniteRectangle_vertical_integral_eq
    (contourIntegrand_shiftedLine_integrable hr hhalf hApole hAint hF)
    (contourIntegrand_shiftedLine_integrable hr (hhalf.trans_le hAB) hBpole hBint hF)
    (by simpa using saddleHorizontalIntegral_tendsto_zero hAB hbound (-1) (by norm_num))
    (by simpa using saddleHorizontalIntegral_tendsto_zero hAB hbound 1 (by norm_num)) fun T ↦ ?_
  have hz : (A : ℂ) + (-T : ℂ) * I ∈ saddleFinitePoleHalfPlane N := by
    change -(2 * ((N : ℝ) + 1)) < _
    simpa [Complex.mul_re] using hhalf
  have hw : (B : ℂ) + (T : ℂ) * I ∈ saddleFinitePoleHalfPlane N := by
    change -(2 * ((N : ℝ) + 1)) < _
    simpa [Complex.mul_re] using hhalf.trans_le hAB
  simpa [Complex.mul_re, Complex.mul_im, smul_eq_mul] using hrect _ _ hz hw

/-- Off the poles the contour integrand is the weighted Mellin datum minus the weighted Gaussian
representatives of its first `N + 1` residues. -/
theorem rapidContourIntegrand_isRapid {M : ℂ → ℂ} {ρ : ℕ → ℂ} (hM : IsPoleDatum M ρ) (N : ℕ)
    (r : ℝ) : IsRapidContourIntegrand (rapidContourIntegrand M ρ N r) M ρ N r :=
  fun z hz hpole ↦ by
    unfold rapidContourIntegrand
    rw [rapidPoleRegularPart_eq_of_not_pole hM hz hpole, mul_sub]

/-- Lemma 4.3 for the Mellin data `M_P`: the vertical integrals of its contour integrand over two
pole-free lines of the half-plane `Re z > -2 (N + 1)` agree. -/
theorem mellinData_rapidContourIntegrand_vertical_integral_eq {ε ℓ r A B : ℝ} (hε : 0 < ε)
    (hℓ : 0 < ℓ) (horder : a₀ε ε ≤ Aε ε) {P : ℂ → ℂ} (hP : IsSaddlePolynomial ε P) (hr : 0 < r)
    (N : ℕ) (hhalf : -(2 * ((N : ℝ) + 1)) < A) (hAB : A ≤ B)
    (hApole : ∀ n : ℕ, A ≠ -(2 * n : ℝ)) (hBpole : ∀ n : ℕ, B ≠ -(2 * n : ℝ)) :
    (∫ t : ℝ, rapidContourIntegrand (mellinData ε ℓ P) (poleResidue ε ℓ P) N r
        ((B : ℂ) + (t : ℂ) * I)) =
      ∫ t : ℝ, rapidContourIntegrand (mellinData ε ℓ P) (poleResidue ε ℓ P) N r
        ((A : ℂ) + (t : ℂ) * I) :=
  have hM := isPoleDatum_mellinData hε horder ℓ hP.differentiable
  contourIntegrand_vertical_integral_eq hr hhalf hAB hApole hBpole
    (by simpa using mellinData_shiftedLine_moment_integrable hε hℓ horder hP hApole 0)
    (by simpa using mellinData_shiftedLine_moment_integrable hε hℓ horder hP hBpole 0)
    (mellinData_horizontalStrip_polynomial_bound hε hℓ horder hP hAB 1)
    (rapidContourIntegrand_isRapid hM N r) (rapidContourIntegrand_boundary_rectangle hM N hr)

/-! ### The spectrum on the critical line and its Fourier transform -/

/-- Lemma 4.3: all moments `|t| ^ k ‖X_P(t)‖` of a spectrum `X_P(t) = E_λ(t) P(t/λ)` are
integrable. -/
theorem spectrum_norm_moment_integrable {ε ℓ : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : a₀ε ε ≤ Aε ε) {P : ℂ → ℂ} (hP : IsSaddlePolynomial ε P) (k : ℕ) :
    Integrable fun t : ℝ ↦ |t| ^ k * ‖spectrum ε ℓ P t‖ := by
  have hdecay : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ |t| →
      |t| ^ j * ‖spectrum ε ℓ P t‖ ≤ C := fun j ↦ by
    refine ⟨(1 + |β ε|) * (1 + ℓ⁻¹) ^ 3 * ((2 : ℝ) ^ (j + 3) * Gamma (ℓ / 2 + (j + 3)) *
      exp (2 * |ℓ| * saddleShellTotalVariation ε)), ?_, fun t ht ↦ ?_⟩
    · have hpos : 0 < Gamma (ℓ / 2 + ((j : ℝ) + 3)) := Real.Gamma_pos_of_pos (by positivity)
      positivity
    · have hpoly : ‖P ((t : ℂ) / (ℓ : ℂ))‖ ≤ (1 + |β ε|) * (1 + ℓ⁻¹) ^ 3 * |t| ^ 3 := by
        have hnorm : ‖(t : ℂ) / (ℓ : ℂ)‖ = |t| / ℓ := by rw [norm_div]; simp [abs_of_pos hℓ]
        calc ‖P ((t : ℂ) / (ℓ : ℂ))‖ ≤ (1 + |β ε|) * (1 + ‖(t : ℂ) / (ℓ : ℂ)‖) ^ 3 :=
            hP.norm_le _
          _ = (1 + |β ε|) * (1 + |t| / ℓ) ^ 3 := by rw [hnorm]
          _ ≤ (1 + |β ε|) * ((1 + ℓ⁻¹) * |t|) ^ 3 := by
              gcongr
              rw [inv_eq_one_div]
              field_simp [hℓ.ne']
              nlinarith
          _ = (1 + |β ε|) * (1 + ℓ⁻¹) ^ 3 * |t| ^ 3 := by ring
      unfold spectrum
      calc |t| ^ j * ‖E ε ℓ t * P ((t : ℂ) / (ℓ : ℂ))‖
          = |t| ^ j * ‖E ε ℓ t‖ * ‖P ((t : ℂ) / (ℓ : ℂ))‖ := by rw [norm_mul]; ring
        _ ≤ |t| ^ j * ‖E ε ℓ t‖ * ((1 + |β ε|) * (1 + ℓ⁻¹) ^ 3 * |t| ^ 3) := by gcongr
        _ = (1 + |β ε|) * (1 + ℓ⁻¹) ^ 3 * (|t| ^ (j + 3) * ‖E ε ℓ t‖) := by rw [pow_add]; ring
        _ ≤ _ := by
            simpa only [Nat.cast_add, Nat.cast_ofNat] using mul_le_mul_of_nonneg_left
              (saddleEnvelope_vertical_polynomial_bound hε hℓ horder t (j + 3))
              (by positivity : (0 : ℝ) ≤ (1 + |β ε|) * (1 + ℓ⁻¹) ^ 3)
  simpa [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs] using
    (integrable_of_continuous_polynomial_decay (spectrum_continuous hε hℓ horder hP.continuous)
      hdecay k).norm

/-- If all moments of a continuous `F` are integrable, so are all moments of `y ↦ F(-2πy)`. -/
theorem integrable_norm_moment_comp_neg_two_pi {F : ℝ → ℂ} (hF : Continuous F)
    (hmom : ∀ j : ℕ, Integrable fun t : ℝ ↦ |t| ^ j * ‖F t‖) (k : ℕ) :
    Integrable fun y : ℝ ↦ ‖y‖ ^ k * ‖F (-(2 * π * y))‖ := by
  have hc : (1 : ℝ) ≤ |(-(2 * π) : ℝ)| := by
    rw [abs_neg, abs_of_pos (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hc0 : (-(2 * π) : ℝ) ≠ 0 := fun h ↦ by rw [h] at hc; norm_num at hc
  have key : Integrable fun y : ℝ ↦ |y| ^ k * ‖F (-(2 * π) * y)‖ := by
    refine ((hmom k).comp_mul_left' hc0).mono'
      (((continuous_abs.pow k).mul (hF.comp (by fun_prop)).norm).aestronglyMeasurable)
      (.of_forall fun y ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    gcongr
    exact le_mul_of_one_le_left (abs_nonneg y) hc
  simpa [neg_mul, mul_assoc] using key

/-- The Fourier data `y ↦ X_P(-2πy)` of report (40). -/
def fourierData (ε ℓ : ℝ) (P : ℂ → ℂ) (y : ℝ) : ℂ := spectrum ε ℓ P (-(2 * π * y))

theorem fourierData_norm_moment_integrable {ε ℓ : ℝ} (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : a₀ε ε ≤ Aε ε) {P : ℂ → ℂ} (hP : IsSaddlePolynomial ε P) (k : ℕ) :
    Integrable fun y : ℝ ↦ ‖y‖ ^ k * ‖fourierData ε ℓ P y‖ :=
  integrable_norm_moment_comp_neg_two_pi (spectrum_continuous hε hℓ horder hP.continuous)
    (fun j ↦ spectrum_norm_moment_integrable hε hℓ horder hP j) k

/-! ### The profiles `f_±` as Fourier transforms -/

/-- The inverse Mellin transform on the line `Re z = σ` is a Fourier transform. -/
theorem mellinInv_eq_fourier (σ : ℝ) (F : ℂ → ℂ) {r : ℝ} (hr : 0 < r) :
    mellinInv σ F r =
      (r ^ (-σ) : ℝ) * 𝓕 (fun y : ℝ ↦ F ((σ : ℂ) + 2 * (π : ℂ) * (y : ℂ) * I)) (log r) := by
  rw [mellinInv_eq_fourierInv σ F hr, Real.fourierInv_eq_fourier_neg, neg_neg, smul_eq_mul]
  congr 1
  simpa using (Complex.ofReal_cpow hr.le (-σ)).symm

/-- Report (40): `f_P(r) = r^{-λ} 𝓕(X_P(-2π ·))(log r)` for `r > 0`. -/
theorem mellinProfile_eq_fourier (ε ℓ : ℝ) (P : ℂ → ℂ) (c : ℝ) {r : ℝ} (hr : 0 < r) :
    mellinProfile ε ℓ P c r = (r ^ (-ℓ) : ℝ) * (𝓕 (fourierData ε ℓ P)) (log r) := by
  have hline : (fun y : ℝ ↦ mellinData ε ℓ P ((ℓ : ℂ) + 2 * (π : ℂ) * (y : ℂ) * I)) =
      fourierData ε ℓ P := funext fun y ↦ by
    rw [show ((ℓ : ℂ) + 2 * (π : ℂ) * (y : ℂ) * I) = (ℓ : ℂ) - I * ((-(2 * π * y) : ℝ) : ℂ) by
      push_cast; ring]
    exact mellinData_vertical ε ℓ P _
  rw [mellinProfile_of_ne_zero ε ℓ P c hr.ne', mellinInv_eq_fourier ℓ (mellinData ε ℓ P) hr,
    hline]

/-- A profile of the shape `r ↦ r ^ (-λ) · G (log r)` with `G` smooth is smooth on `(0, ∞)`. -/
theorem contDiffOn_profile {ℓ : ℝ} {f G : ℝ → ℂ} (hG : ContDiff ℝ ∞ G)
    (hf : ∀ r ∈ Ioi (0 : ℝ), f r = (r ^ (-ℓ) : ℝ) * G (log r)) : ContDiffOn ℝ ∞ f (Ioi 0) := by
  have hpow : ContDiffOn ℝ ∞ (fun r : ℝ ↦ ((r ^ (-ℓ) : ℝ) : ℂ)) (Ioi 0) :=
    Complex.ofRealCLM.contDiff.fun_comp_contDiffOn
      (contDiff_id.contDiffOn.rpow_const_of_ne fun r hr ↦ (show (0 : ℝ) < r from hr).ne')
  have hlog : ContDiffOn ℝ ∞ log (Ioi 0) :=
    contDiff_id.contDiffOn.log fun r hr ↦ (show (0 : ℝ) < r from hr).ne'
  exact (hpow.mul (hG.fun_comp_contDiffOn hlog)).congr hf

/-- A radial function is smooth away from the origin as soon as its profile is smooth on
`(0, ∞)`. -/
theorem contDiffOn_comp_norm {d : ℕ} {f : ℝ → ℂ} (hf : ContDiffOn ℝ ∞ f (Ioi 0)) :
    ContDiffOn ℝ ∞ (fun x : Euclidean d ↦ f ‖x‖) ({0}ᶜ : Set (Euclidean d)) := by
  have hnorm : ContDiffOn ℝ ∞ (fun x : Euclidean d ↦ ‖x‖) ({0}ᶜ : Set (Euclidean d)) :=
    ContDiffOn.norm ℝ contDiff_id.contDiffOn fun x hx ↦ hx
  simpa only [Function.comp_def] using hf.comp hnorm fun x hx ↦ norm_pos_iff.2 hx

/-- Lemma 4.3: `x ↦ f_P(‖x‖)` is smooth away from the origin. -/
theorem mellinProfileFun_contDiffOn {ε : ℝ} (hε : 0 < ε) {d : ℕ} (hd : 0 < d)
    (horder : a₀ε ε ≤ Aε ε) {P : ℂ → ℂ} (hP : IsSaddlePolynomial ε P) (c : ℝ) :
    ContDiffOn ℝ ∞ (mellinProfileFun ε d P c) ({0}ᶜ : Set (Euclidean d)) :=
  contDiffOn_comp_norm (contDiffOn_profile
    (Real.contDiff_fourier (N := ⊤) fun n _ ↦ fourierData_norm_moment_integrable hε
      (div_pos (by exact_mod_cast hd) two_pos) horder hP n)
    fun r hr ↦ mellinProfile_eq_fourier ε _ P c hr)

/-! ### Real-valuedness of the profiles -/

/-- Conjugate symmetry of the spectrum of a saddle polynomial: `conj X_P(t) = X_P(-t)`. -/
theorem spectrum_conj {ε : ℝ} {P : ℂ → ℂ} (hP : IsSaddlePolynomial ε P) (ℓ t : ℝ) :
    starRingEnd ℂ (spectrum ε ℓ P t) = spectrum ε ℓ P (-t) := by
  unfold spectrum
  rw [map_mul, saddleEnvelope_conj, hP.conj_eq, map_div₀, Complex.conj_ofReal,
    Complex.conj_ofReal, Complex.ofReal_neg, neg_div]

/-- Conjugate symmetry of a Mellin datum on the critical line, from that of its spectrum. -/
theorem mellinData_conj_vertical {ℓ : ℝ} {M : ℂ → ℂ} {X : ℝ → ℂ}
    (hvert : ∀ t : ℝ, M ((ℓ : ℂ) - I * (t : ℂ)) = X t)
    (hconj : ∀ t : ℝ, starRingEnd ℂ (X t) = X (-t)) (t : ℝ) :
    starRingEnd ℂ (M ((ℓ : ℂ) + (t : ℂ) * I)) = M ((ℓ : ℂ) + (-t : ℂ) * I) := by
  have hneg : M ((ℓ : ℂ) + (t : ℂ) * I) = X (-t) := by
    have h := hvert (-t)
    rw [Complex.ofReal_neg] at h
    rw [← h]
    congr 1
    ring
  have hpos : M ((ℓ : ℂ) + (-t : ℂ) * I) = X t := by
    rw [← hvert t]
    congr 1
    ring
  rw [hneg, hpos, hconj, neg_neg]

/-- Lemma 4.3: a Hermitian Mellin datum has a real inverse Mellin transform. -/
theorem mellinInv_real_of_hermitian (σ : ℝ) (F : ℂ → ℂ)
    (hF : ∀ t : ℝ, starRingEnd ℂ (F ((σ : ℂ) + (t : ℂ) * I)) =
      F ((σ : ℂ) + (-t : ℂ) * I)) {r : ℝ} (hr : 0 < r) : (mellinInv σ F r).im = 0 := by
  have hpow : ∀ t : ℝ, starRingEnd ℂ ((r : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) =
      (r : ℂ) ^ (-((σ : ℂ) + (-t : ℂ) * I)) := fun t ↦ by
    have harg : (r : ℂ).arg ≠ π := by
      rw [Complex.arg_ofReal_of_nonneg hr.le]; exact Real.pi_ne_zero.symm
    simpa [map_neg, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I] using
      (Complex.cpow_conj (r : ℂ) (-((σ : ℂ) + (t : ℂ) * I)) harg).symm
  set g : ℝ → ℂ := fun t ↦
    (r : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) * F ((σ : ℂ) + (t : ℂ) * I) with hgdef
  have hsym : ∀ t : ℝ, starRingEnd ℂ (g t) = g (-t) := fun t ↦ by
    simp only [hgdef, map_mul, hpow t, hF t, Complex.ofReal_neg]
  have hint : starRingEnd ℂ (∫ t : ℝ, g t) = ∫ t : ℝ, g t :=
    calc starRingEnd ℂ (∫ t : ℝ, g t)
        = ∫ t : ℝ, starRingEnd ℂ (g t) := (integral_conj (f := g)).symm
      _ = ∫ t : ℝ, g (-t) := integral_congr_ae (.of_forall hsym)
      _ = ∫ t : ℝ, g t := by rw [integral_neg_eq_self]
  have hrewrite : mellinInv σ F r = (1 / (2 * π) : ℝ) • ∫ t : ℝ, g t := by
    unfold mellinInv
    simp only [hgdef, smul_eq_mul]
  apply Complex.conj_eq_iff_im.mp
  rw [hrewrite]
  simp only [Complex.real_smul, map_mul, Complex.conj_ofReal, hint]

/-- Lemma 4.3: the profile `f_P` of a saddle polynomial is real on `[0, ∞)`. -/
theorem mellinProfile_im {ε : ℝ} {P : ℂ → ℂ} (hP : IsSaddlePolynomial ε P) (ℓ c : ℝ) {r : ℝ}
    (hr : 0 ≤ r) : (mellinProfile ε ℓ P c r).im = 0 := by
  unfold mellinProfile
  split_ifs with h
  · simp
  · exact mellinInv_real_of_hermitian _ _
      (mellinData_conj_vertical (mellinData_vertical ε ℓ P) (spectrum_conj hP ℓ)) (hr.lt_of_ne' h)

/-- Lemma 4.3: `x ↦ f_P(‖x‖)` is real valued. -/
theorem mellinProfileFun_im {ε : ℝ} {P : ℂ → ℂ} (hP : IsSaddlePolynomial ε P) (d : ℕ) (c : ℝ) :
    IsRealValued (mellinProfileFun ε d P c) := fun x ↦ mellinProfile_im hP _ c (norm_nonneg x)

/-! ### The multiplier identity -/

/-- The multiplier identity `m_λ(t) E_λ(-t) = E_λ(t)` for the envelope. -/
theorem mellinMultiplier_mul_E_neg {ε ℓ : ℝ} (hℓ : 0 < ℓ) (t : ℝ) :
    m_ℓ ℓ t * E ε ℓ (-t) = E ε ℓ t := by
  have hphase : Complex.exp (I * (t : ℂ) * (log π : ℂ)) *
      Complex.exp (I * (-t : ℂ) * (log π : ℂ) / 2) =
        Complex.exp (I * (t : ℂ) * (log π : ℂ) / 2) := by
    rw [← Complex.exp_add]; congr 1; ring
  unfold m_ℓ E
  rw [Complex.ofReal_neg, neg_div, mellinShellPhase_neg,
    show ((ℓ : ℂ) - I * (-t : ℂ)) / 2 = ((ℓ : ℂ) + I * (t : ℂ)) / 2 by ring]
  calc _ = Complex.exp (I * (t : ℂ) * (log π : ℂ)) *
        Complex.exp (I * (-t : ℂ) * (log π : ℂ) / 2) *
        Complex.Gamma (((ℓ : ℂ) - I * (t : ℂ)) / 2) *
        Complex.exp ((ℓ : ℂ) * h_ε ε ((t : ℂ) / (ℓ : ℂ))) := by
          field_simp [mellinMultiplier_denominator_ne_zero hℓ t]
    _ = _ := by rw [hphase]

/-- The multiplier identity `m_λ(t) X_P(-t) = X_Q(t)` of report (40) whenever `P(-ζ) = Q(ζ)`;
the cases `(P, Q) = (P₋, P₊)` and `(P₀, P₀)` give `f̂₋ = f₊` and `f̂₀ = f₀`. -/
theorem mellinMultiplier_mul_spectrum_neg {ε ℓ : ℝ} (hℓ : 0 < ℓ) {P Q : ℂ → ℂ}
    (hPQ : ∀ z : ℂ, P (-z) = Q z) (t : ℝ) :
    m_ℓ ℓ t * spectrum ε ℓ P (-t) = spectrum ε ℓ Q t := by
  unfold spectrum
  rw [Complex.ofReal_neg, neg_div, hPQ, ← mul_assoc, mellinMultiplier_mul_E_neg hℓ]

end

end CohnElkies
