import Mathlib

/-!
# Phragmén–Lindelöf in a horizontal strip for a function whose modulus extends continuously

`Complex.norm_extension_le_of_forall_mem_frontier_le` is the maximum modulus principle on a bounded
preconnected open set for a continuous function `N` on the closure that agrees with `‖f‖` inside
(only the modulus of `f`, not `f` itself, extends to the closure), and
`PhragmenLindelof.horizontal_strip_norm_extension` is the corresponding Phragmén–Lindelöf principle
in a horizontal strip `{z | a < im z < b}`; it strengthens `PhragmenLindelof.horizontal_strip`,
which requires `f` to extend continuously.
-/

open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter Real Topology

/-- **Maximum modulus principle** for a continuous extension of the modulus.

If `f` is differentiable on a bounded preconnected open set `U` and `N` is a continuous function
on `closure U` that agrees with `‖f‖` on `U`, then any bound `N ≤ C` on `frontier U` propagates
to all of `closure U`.  Compared with `Complex.norm_le_of_forall_mem_frontier_norm_le` only the
modulus of `f`, not `f` itself, is required to extend continuously to the closure.

Proof: `N` attains its maximum on the compact set `closure U` at some `w`; if `w ∈ U`, then `‖f‖`
attains an interior maximum, so `N` is constant on `U`, hence on `closure U`, and the bound on the
(nonempty) frontier propagates. -/
theorem Complex.norm_extension_le_of_forall_mem_frontier_le {U : Set ℂ} (hopen : IsOpen U)
    (hconnected : IsPreconnected U) (hbounded : IsBounded U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) {N : ℂ → ℝ}
    (hN : ContinuousOn N (closure U)) (hinterior : ∀ z ∈ U, N z = ‖f z‖) {C : ℝ}
    (hfrontier : ∀ z ∈ frontier U, N z ≤ C) {z : ℂ} (hz : z ∈ closure U) : N z ≤ C := by
  rcases U.eq_empty_or_nonempty with rfl | hnonempty
  · simp at hz
  obtain ⟨w, hwclosure, hwmax⟩ := hbounded.isCompact_closure.exists_isMaxOn hnonempty.closure hN
  refine (hwmax hz).trans ?_
  rw [closure_eq_interior_union_frontier, hopen.interior_eq, mem_union] at hwclosure
  rcases hwclosure with hw | hw
  · have hmax : IsMaxOn (norm ∘ f) U w := fun x hx ↦ by
      change ‖f x‖ ≤ ‖f w‖
      rw [← hinterior x hx, ← hinterior w hw]
      exact hwmax (subset_closure hx)
    have hconst : EqOn N (Function.const ℂ (N w)) U := fun x hx ↦ by
      change N x = N w
      rw [hinterior x hx, hinterior w hw]
      simpa [Function.comp_def] using
        Complex.norm_eqOn_of_isPreconnected_of_isMaxOn hconnected hopen hf hw hmax hx
    obtain ⟨t, ht⟩ := nonempty_frontier_iff.mpr
      ⟨hnonempty, fun hu ↦ NormedSpace.unbounded_univ ℂ ℂ (hu ▸ hbounded)⟩
    exact (hconst.of_subset_closure hN continuousOn_const subset_closure Subset.rfl
      (frontier_subset_closure ht)).symm.trans_le (hfrontier t ht)
  · exact hfrontier w hw

/-- The damping factor `exp (ε (e^{q(w - mi)} + e^{-q(w - mi)}))`, `ε < 0`, has modulus at most
`exp (ε cos (qr) e^{q |re w|})` on the closed strip `|im w - m| ≤ r` when `qr ≤ π / 2`. -/
private theorem norm_damp_le {ε q r m : ℝ} (hε : ε < 0) (hq : 0 < q) (hqr : q * r ≤ π / 2)
    {w : ℂ} (hw : w.im ∈ Icc (m - r) (m + r)) :
    ‖Complex.exp (ε * (Complex.exp (q * (w - m * I)) + Complex.exp (-(q * (w - m * I)))))‖ ≤
      Real.exp (ε * Real.cos (q * r) * Real.exp (q * |w.re|)) := by
  have hwaff : |(q * (w - m * I) : ℂ).im| ≤ q * r := by
    rw [← Real.closedBall_eq_Icc, mem_closedBall, Real.dist_eq] at hw
    rw [Complex.im_ofReal_mul, Complex.sub_im, Complex.mul_I_im, Complex.ofReal_re, abs_mul,
      abs_of_pos hq]
    gcongr
  simpa only [Complex.re_ofReal_mul, abs_mul, abs_of_pos hq, Complex.sub_re, Complex.mul_I_re,
    Complex.ofReal_im, zero_mul, neg_zero, sub_zero] using
    norm_exp_mul_exp_add_exp_neg_le_of_abs_im_le hε.le hwaff hqr

/-- If `f = O(exp (B e^{c |re w|}))` in the strip `a < im w < b` and `‖g w‖ ≤ exp (δ e^{q |re w|})`
on the closed strip with `δ < 0` and `c < q`, then `‖g • f‖ ≤ C` on the vertical sides
`|re w| = R` of some rectangle containing `z`. -/
private theorem exists_norm_smul_le_of_isBigO {a b c q δ B C : ℝ} (hC : 0 < C) (hδ : δ < 0)
    (hq : 0 < q) (hcq : c < q) {f g : ℂ → ℂ}
    (hO : f =O[comap (fun w : ℂ ↦ |w.re|) atTop ⊓ 𝓟 (Complex.im ⁻¹' Ioo a b)]
      fun w : ℂ ↦ Real.exp (B * Real.exp (c * |w.re|)))
    (hg : ∀ ⦃w : ℂ⦄, w.im ∈ Icc a b → ‖g w‖ ≤ Real.exp (δ * Real.exp (q * |w.re|))) (z : ℂ) :
    ∃ R : ℝ, |z.re| < R ∧ ∀ w : ℂ, |w.re| = R → w.im ∈ Ioo a b → ‖g w • f w‖ ≤ C := by
  refine ((eventually_gt_atTop |z.re|).and ?_).exists
  obtain ⟨A, hA, hAmajor⟩ := hO.exists_pos
  simp only [isBigOWith_iff, eventually_inf_principal, eventually_comap, mem_Ioo, mem_preimage,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hAmajor
  suffices hlimit : Tendsto (fun R : ℝ ↦
      Real.exp (δ * Real.exp (q * R) + B * Real.exp (c * R) + Real.log A)) atTop (𝓝 (0 : ℝ)) by
    filter_upwards [hlimit.eventually (ge_mem_nhds hC), hAmajor] with R hRC hbound w hwre hwim
    calc
      ‖g w • f w‖ ≤ Real.exp (δ * Real.exp (q * R) + B * Real.exp (c * R) + Real.log A) := by
        rw [norm_smul, Real.exp_add, ← hwre, Real.exp_add, Real.exp_log hA, mul_assoc,
          mul_comm _ A]
        gcongr
        exacts [hg (Ioo_subset_Icc_self hwim), hbound w hwre hwim]
      _ ≤ C := hRC
  refine Real.tendsto_exp_atBot.comp ?_
  suffices haux : Tendsto (fun R : ℝ ↦ δ + B * (Real.exp ((q - c) * R))⁻¹) atTop
      (𝓝 (δ + B * 0)) by
    rw [mul_zero, add_zero] at haux
    refine Tendsto.atBot_add ?_ tendsto_const_nhds
    simpa only [id, Function.comp_apply, add_mul, mul_assoc, ← div_eq_inv_mul, ← Real.exp_sub,
      ← sub_mul, sub_sub_cancel] using haux.neg_mul_atTop hδ
        (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hq))
  exact tendsto_const_nhds.add (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (sub_pos.mpr hcq)))))

/-- **Phragmén–Lindelöf principle** in a horizontal strip `{z | a < im z < b}` for a function
whose *modulus* extends continuously to the closed strip.

Let `f` be differentiable on the open strip and let `N` be continuous and nonnegative on the
closed strip with `N = ‖f‖` on the open strip.  Assume `N ≤ C` on the two boundary lines
`im z = a` and `im z = b`, and that `f z = O(exp (B * exp (c * |re z|)))` as `|re z| → ∞` inside
the strip, for some `c < π / (b - a)`.  Then `N ≤ C` on the whole closed strip.

This strengthens `PhragmenLindelof.horizontal_strip`, which requires `f` itself to be continuous
on the closed strip (`DiffContOnCl`); here only `‖f‖` is assumed to extend.

Proof: recenter the strip as `|im z - m| < r`, choose `c < q < π / (2r)` and, for `ε < 0`, damp
`f` by `exp (ε (e^{q(z - mi)} + e^{-q(z - mi)}))`, whose modulus is at most `1` on the boundary
lines and at most `exp (ε cos (qr) e^{q |re z|})` in the strip, so that the damped function is
bounded by `C` on the vertical sides of a wide rectangle by the growth assumption; the maximum
principle on that rectangle bounds the damped function at `z`, and `ε → 0⁻` concludes. -/
theorem PhragmenLindelof.horizontal_strip_norm_extension
    {a b C : ℝ} (hab : a < b) (hC : 0 < C)
    (f : ℂ → ℂ) (N : ℂ → ℝ)
    (hf : DifferentiableOn ℂ f (Complex.im ⁻¹' Ioo a b))
    (hN : ContinuousOn N (Complex.im ⁻¹' Icc a b))
    (hNnonneg : ∀ w : ℂ, w.im ∈ Icc a b → 0 ≤ N w)
    (hinterior : ∀ w : ℂ, w.im ∈ Ioo a b → N w = ‖f w‖)
    (hbottom : ∀ w : ℂ, w.im = a → N w ≤ C)
    (htop : ∀ w : ℂ, w.im = b → N w ≤ C)
    (hgrowth : ∃ c < π / (b - a), ∃ B : ℝ, Asymptotics.IsBigO
          (Filter.comap (fun w : ℂ ↦ |w.re|) Filter.atTop ⊓ Filter.principal
              (Complex.im ⁻¹' Ioo a b))
          f
          (fun w : ℂ ↦ Real.exp (B * Real.exp (c * |w.re|))))
    {z : ℂ} (hza : a ≤ z.im) (hzb : z.im ≤ b) :
    N z ≤ C := by
  rw [le_iff_eq_or_lt] at hza hzb
  rcases hza with hza | hza
  · exact hbottom z hza.symm
  rcases hzb with hzb | hzb
  · exact htop z hzb
  obtain ⟨m, r, rfl, rfl⟩ : ∃ m r : ℝ, a = m - r ∧ b = m + r :=
    ⟨(a + b) / 2, (b - a) / 2, by ring, by ring⟩
  have hr : 0 < r := by linarith
  have hwidth : m - r < m + r := by linarith
  rw [add_sub_sub_cancel, ← two_mul, div_mul_eq_div_div] at hgrowth
  obtain ⟨c, hc, B, hO⟩ := hgrowth
  obtain ⟨q, ⟨hcq, hq⟩, hqr⟩ : ∃ q : ℝ, (c < q ∧ 0 < q) ∧ q < π / 2 / r := by
    simpa only [max_lt_iff] using exists_between (max_lt hc (div_pos Real.pi_div_two_pos hr))
  have hqr' : q * r < π / 2 := (lt_div_iff₀ hr).mp hqr
  set aff : ℂ → ℂ := fun w ↦ q * (w - m * I) with haff
  set damp : ℝ → ℂ → ℂ :=
    fun ε w ↦ Complex.exp (ε * (Complex.exp (aff w) + Complex.exp (-aff w))) with hdamp
  suffices hevent : ∀ᶠ ε : ℝ in 𝓝[<] (0 : ℝ), ‖damp ε z • f z‖ ≤ C by
    rw [hinterior z ⟨hza, hzb⟩]
    refine le_of_tendsto (Tendsto.mono_left ?_ nhdsWithin_le_nhds) hevent
    apply ((Complex.continuous_ofReal.mul continuous_const).cexp.smul
      continuous_const).norm.tendsto'
    simp
  filter_upwards [self_mem_nhdsWithin] with ε (hε : ε < 0)
  have hedge : ∀ w : ℂ, w.im = m - r ∨ w.im = m + r → w.im ∈ Icc (m - r) (m + r) := fun w hw ↦
    hw.by_cases (fun h ↦ h.symm ▸ left_mem_Icc.mpr hwidth.le)
      fun h ↦ h.symm ▸ right_mem_Icc.mpr hwidth.le
  obtain ⟨δ, hδ, hδbound⟩ : ∃ δ < (0 : ℝ), ∀ ⦃w : ℂ⦄, w.im ∈ Icc (m - r) (m + r) →
      ‖damp ε w‖ ≤ Real.exp (δ * Real.exp (q * |w.re|)) :=
    ⟨ε * Real.cos (q * r), mul_neg_of_neg_of_pos hε (Real.cos_pos_of_mem_Ioo
      (abs_lt.mp ((abs_of_pos (mul_pos hq hr)).symm ▸ hqr'))),
      fun w hw ↦ norm_damp_le hε hq hqr'.le hw⟩
  have hdampedge : ∀ w : ℂ, w.im = m - r ∨ w.im = m + r → ‖damp ε w‖ ≤ 1 := fun w hw ↦
    (hδbound (hedge w hw)).trans
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hδ.le (Real.exp_pos _).le))
  obtain ⟨R, hzR, hR⟩ := exists_norm_smul_le_of_isBigO hC hδ hq hcq hO hδbound z
  have hRpos : 0 < R := (abs_nonneg z.re).trans_lt hzR
  have hclosure : closure (Ioo (-R) R ×ℂ Ioo (m - r) (m + r)) ⊆
      Complex.im ⁻¹' Icc (m - r) (m + r) := fun w hw ↦ by
    rw [Complex.closure_reProdIm, closure_Ioo (neg_lt_self hRpos).ne, closure_Ioo hwidth.ne] at hw
    exact hw.2
  have hzU : z ∈ Ioo (-R) R ×ℂ Ioo (m - r) (m + r) := ⟨abs_lt.mp hzR, hza, hzb⟩
  have hdampdiff : Differentiable ℂ (damp ε) :=
    ((((differentiable_id.sub_const _).const_mul _).cexp.add
      ((differentiable_id.sub_const _).const_mul _).neg.cexp).const_mul _).cexp
  have hNext : ∀ w ∈ Ioo (-R) R ×ℂ Ioo (m - r) (m + r),
      ‖damp ε w‖ * N w = ‖damp ε w • f w‖ := fun w hw ↦ by
    rw [hinterior w hw.2, norm_smul]
  rw [← hNext z hzU]
  refine Complex.norm_extension_le_of_forall_mem_frontier_le (isOpen_Ioo.reProdIm isOpen_Ioo)
    (((convex_Ioo _ _).linear_preimage Complex.reLm).inter
      ((convex_Ioo _ _).linear_preimage Complex.imLm)).isPreconnected
    ((isBounded_Ioo _ _).reProdIm (isBounded_Ioo _ _))
    ((hdampdiff.differentiableOn.smul hf).mono inter_subset_right)
    (hdampdiff.continuous.norm.continuousOn.mul (hN.mono hclosure)) hNext ?_ (subset_closure hzU)
  intro w hw
  change ‖damp ε w‖ * N w ≤ C
  rw [Complex.frontier_reProdIm, closure_Ioo (neg_lt_self hRpos).ne, frontier_Ioo hwidth,
    closure_Ioo hwidth.ne, frontier_Ioo (neg_lt_self hRpos)] at hw
  by_cases him : w.im = m - r ∨ w.im = m + r
  · exact (mul_le_of_le_one_left (hNnonneg w (hedge w him)) (hdampedge w him)).trans
      (him.by_cases (hbottom w) (htop w))
  · have hvert : w ∈ ({-R, R} : Set ℝ) ×ℂ Icc (m - r) (m + r) := hw.resolve_left fun h ↦ him h.2
    have himinterior : w.im ∈ Ioo (m - r) (m + r) :=
      (or_assoc.mpr (eq_endpoints_or_mem_Ioo_of_mem_Icc hvert.2)).resolve_left him
    rw [hinterior w himinterior, ← norm_smul]
    exact hR w ((abs_eq hRpos.le).mpr hvert.1.symm) himinterior
