import Mathlib

/-!
# Complements on the complex Gamma function

The recurrence `Γ(z + k) = Γ(z) ∏_{j < k} (z + j)`, `‖Γ(z + 1)‖ = ‖z‖ ‖Γ(z)‖`, the bound
`‖Γ(z)‖ ≤ Γ(Re z)` for `Re z > 0` and its consequence `|Im z|^k ‖Γ(z)‖ ≤ Γ(Re z + k)`, the
residues `Res_{z = -n} Γ = (-1)^n / n!` and `Res_{z = -2n} Γ(z/2) = 2 (-1)^n / n!` (as limits of
`(z + n) Γ(z)`), and the meromorphy of `z ↦ Γ(z / 2)`.
-/

open Filter MeasureTheory Real Set
open scoped Topology

/-- The gamma recurrence `Γ(z + k) = Γ(z) ∏_{j < k} (z + j)`. -/
theorem Complex.Gamma_add_nat_eq_mul_prod (z : ℂ) (hz : ∀ j : ℕ, z + j ≠ 0) (k : ℕ) :
    Complex.Gamma (z + k) = Complex.Gamma z * ∏ j ∈ Finset.range k, (z + j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ (hz k), ih, Finset.prod_range_succ]
    ring

theorem Complex.norm_Gamma_add_one {z : ℂ} (hz : z ≠ 0) :
    ‖Complex.Gamma (z + 1)‖ = ‖z‖ * ‖Complex.Gamma z‖ := by
  rw [Complex.Gamma_add_one z hz, norm_mul]

theorem Complex.norm_Gamma_le_Gamma_re {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral, Real.Gamma_eq_integral hz]
  calc ‖∫ x in Ioi (0 : ℝ), (Real.exp (-x) : ℂ) * (x : ℂ) ^ (z - 1)‖
      ≤ ∫ x in Ioi (0 : ℝ), ‖(Real.exp (-x) : ℂ) * (x : ℂ) ^ (z - 1)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ (z.re - 1) :=
        setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ by
          rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos (-x)).le,
            Complex.norm_cpow_eq_rpow_re_of_pos hx]
          simp

theorem Complex.add_natCast_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) (j : ℕ) :
    z + (j : ℂ) ≠ 0 :=
  Complex.ne_zero_of_re_pos (by rw [Complex.add_re, Complex.natCast_re]; positivity)

/-- `|Im z| ^ k ‖Γ z‖ ≤ Γ (Re z + k)`: the Gamma factor decays faster than any polynomial along
vertical lines. -/
theorem Complex.abs_im_pow_mul_norm_Gamma_le {z : ℂ} (hz : ∀ j : ℕ, z + (j : ℂ) ≠ 0) (k : ℕ)
    (hshift : 0 < z.re + k) : |z.im| ^ k * ‖Complex.Gamma z‖ ≤ Real.Gamma (z.re + k) := by
  have hprod : |z.im| ^ k ≤ ∏ j ∈ Finset.range k, ‖z + (j : ℂ)‖ := by
    simpa using Finset.prod_le_prod (s := Finset.range k) (f := fun _ : ℕ ↦ |z.im|)
      (g := fun j : ℕ ↦ ‖z + (j : ℂ)‖) (fun _ _ ↦ abs_nonneg _)
      (fun j _ ↦ by simpa using Complex.abs_im_le_norm (z + (j : ℂ)))
  calc |z.im| ^ k * ‖Complex.Gamma z‖
      ≤ (∏ j ∈ Finset.range k, ‖z + (j : ℂ)‖) * ‖Complex.Gamma z‖ := by gcongr
    _ = ‖Complex.Gamma (z + (k : ℂ))‖ := by
        rw [Complex.Gamma_add_nat_eq_mul_prod z hz k, norm_mul, norm_prod]
        ring
    _ ≤ Real.Gamma (z.re + k) := by
        simpa using Complex.norm_Gamma_le_Gamma_re (z := z + (k : ℂ)) (by simpa using hshift)

/-- `z ↦ Γ(z/2)` is meromorphic on `ℂ`. -/
theorem Complex.meromorphic_Gamma_div_two : Meromorphic fun z : ℂ ↦ Complex.Gamma (z / 2) := by
  intro z
  simpa [Function.comp_def] using
    MeromorphicAt.comp_analyticAt (g := fun u : ℂ ↦ u / 2) (x := z) (Meromorphic.Gamma (z / 2))
      (by fun_prop)

/-- `Res_{z = -n} Γ = (-1)^n / n!`, report (41). -/
theorem Complex.tendsto_add_natCast_mul_Gamma_nhdsNE (n : ℕ) :
    Tendsto (fun z : ℂ ↦ (z + (n : ℂ)) * Complex.Gamma z) (𝓝[≠] (-(n : ℂ)))
      (𝓝 ((-1 : ℂ) ^ n / (n.factorial : ℂ))) := by
  induction n with
  | zero => simpa using Complex.tendsto_self_mul_Gamma_nhds_zero
  | succ n ih =>
    rw [Nat.cast_succ]
    have hnonzero : -((n : ℂ) + 1) ≠ 0 := neg_ne_zero.2 (by exact_mod_cast n.succ_ne_zero)
    have hshift : Tendsto (fun z : ℂ ↦ z + 1) (𝓝[≠] (-((n : ℂ) + 1))) (𝓝[≠] (-(n : ℂ))) := by
      refine tendsto_nhdsWithin_iff.2 ⟨((continuous_add_right (1 : ℂ)).tendsto' _ _
        (by show -((n : ℂ) + 1) + 1 = -(n : ℂ); ring)).mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
      intro heq
      exact hz (by linear_combination heq)
    have hden : Tendsto (fun z : ℂ ↦ z) (𝓝[≠] (-((n : ℂ) + 1))) (𝓝 (-((n : ℂ) + 1))) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hne : ∀ᶠ z in 𝓝[≠] (-((n : ℂ) + 1)), z ≠ (0 : ℂ) := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds
        (eventually_ne_nhds hnonzero)] with z _ hz using hz
    have htarget : ((-1 : ℂ) ^ n / (n.factorial : ℂ)) / (-((n : ℂ) + 1)) =
        (-1 : ℂ) ^ (n + 1) / ((n + 1).factorial : ℂ) := by
      have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
      have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ]
      field_simp [hn, hf]
    rw [← htarget]
    refine ((ih.comp hshift).div hden hnonzero).congr' ?_
    filter_upwards [hne] with z hz
    change (z + 1 + (n : ℂ)) * Complex.Gamma (z + 1) / z = (z + ((n : ℂ) + 1)) * Complex.Gamma z
    rw [Complex.Gamma_add_one z hz]
    field_simp [hz]
    ring

/-- `Res_{z = -2n} Γ(z/2) = 2(-1)^n / n!`, report (41). -/
theorem Complex.tendsto_add_two_mul_natCast_mul_Gamma_div_two_nhdsNE (n : ℕ) :
    Tendsto (fun z : ℂ ↦ (z + 2 * n) * Complex.Gamma (z / 2)) (𝓝[≠] (-(2 * n : ℂ)))
      (𝓝 (2 * (-1 : ℂ) ^ n / (n.factorial : ℂ))) := by
  have hscale : Tendsto (fun z : ℂ ↦ z / 2) (𝓝[≠] (-(2 * n : ℂ))) (𝓝[≠] (-(n : ℂ))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨((continuous_id.div_const (2 : ℂ)).tendsto' _ _
      (by show -(2 * (n : ℂ)) / 2 = -(n : ℂ); ring)).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
    intro heq
    exact hz (by linear_combination 2 * heq)
  convert! ((Complex.tendsto_add_natCast_mul_Gamma_nhdsNE n).comp hscale).const_mul (2 : ℂ) using 1
  · funext z
    change (z + 2 * (n : ℂ)) * Complex.Gamma (z / 2) =
      2 * ((z / 2 + (n : ℂ)) * Complex.Gamma (z / 2))
    ring
  · ring_nf
