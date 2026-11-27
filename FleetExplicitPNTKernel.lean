import ContourShift
import ExplicitFormula
import ZetaGrowth

/-!
# The truncated Perron kernel and the truncated Perron formula with explicit error

Port, with adaptations, of the kernel and truncated-Perron part of kerr-lean
`Kerr/Zeta/ExplicitFormula.lean` (James C. Kerr, Apache-2.0): `kernel`, `norm_hseg_le`,
`norm_vseg_le`, `kernel_gt_one`, `kernel_lt_one`, `perronTruncated_eq_tsum`,
`halfint_log_bound`, `norm_term_error_halfint`, `integral_inv_one_add_abs`. The two rectangle
identities (`kernel_rect_gt_one`, `kernel_rect_lt_one`) are re-proved here with hp-proof's own
residue theorem `ContourShift.rectBoundaryIntegral_eq_of_extension` and Mathlib's rectangle
Cauchy theorem instead of the PrimeNumberTheoremAnd rectangle library used in kerr-lean.
The half-integer error is stated at abscissa `c = 3/2` (kerr-lean: `c = 2`).

* `kernel y c T = (2π)⁻¹ ∫_{-T}^{T} y^{c+it}/(c+it) dt`.
* `kernel_gt_one`: `‖K(y,c,T) − 1‖ ≤ y^c/(π T |log y|)` for `y > 1`.
* `kernel_lt_one`: `‖K(y,c,T)‖ ≤ y^c/(π T |log y|)` for `0 < y < 1`.
* `perron_integral_eq_tsum`: `∫_{-T}^{T} (−ζ'/ζ)(c+it) x^{c+it}/(c+it) dt = 2π ∑ Λ(n) K(x/n,c,T)`.
* `S32_le`: `∑ Λ(n) n^{-3/2} ≤ 20`.
* `perron_error_halfint`: at `x = N + 1/2`, `‖ψ(x) − ∑ Λ(n) K(x/n,3/2,T)‖ ≤ 80 x^{5/2}/(π T)`.
* `perron_small`: `‖∑ Λ(n) K((1/x)/n,3/2,T)‖ ≤ 20/(π T log x)` for `x > 1`.
-/

noncomputable section
open Complex Filter Topology MeasureTheory Set
open scoped Real Interval ArithmeticFunction.vonMangoldt

namespace FleetExplicitPNTKernel

/-! ## The kernel -/

/-- The truncated Perron kernel `(1/2π) ∫_{-T}^{T} y^{c+it}/(c+it) dt`. -/
def kernel (y c T : ℝ) : ℂ :=
  ((2 * π : ℝ) : ℂ)⁻¹ * ∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)

/-- Horizontal segment bound: `‖∫_a^b y^{σ+iT}/(σ+iT) dσ‖ ≤ (y^b − y^a)/(|T| log y)`. -/
lemma norm_hseg_le {y a b T : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) (hab : a ≤ b) (hT : T ≠ 0) :
    ‖∫ σ in a..b, (y : ℂ) ^ ((σ : ℂ) + T * I) / ((σ : ℂ) + T * I)‖ ≤
      (y ^ b - y ^ a) / (|T| * Real.log y) := by
  have hT' : 0 < |T| := abs_pos.mpr hT
  have hlog : Real.log y ≠ 0 := by
    intro h
    rcases Real.log_eq_zero.mp h with h | h | h <;> [linarith; exact hy1 h; linarith]
  have hderiv : ∀ σ : ℝ, HasDerivAt (fun σ : ℝ => y ^ σ / Real.log y / |T|) (y ^ σ / |T|) σ := by
    intro σ
    have := (Real.hasStrictDerivAt_const_rpow hy σ).hasDerivAt
    convert (this.div_const (Real.log y)).div_const |T| using 1
    field_simp
  have hcont : Continuous (fun σ : ℝ => y ^ σ / |T|) := by
    exact (continuous_const.rpow continuous_id fun _ => Or.inl hy.ne').div_const _
  calc ‖∫ σ in a..b, (y : ℂ) ^ ((σ : ℂ) + T * I) / ((σ : ℂ) + T * I)‖
      ≤ ∫ σ in a..b, y ^ σ / |T| := by
        apply intervalIntegral.norm_integral_le_of_norm_le hab
        · refine Eventually.of_forall (fun σ _ => ?_)
          rw [norm_div, norm_cpow_eq_rpow_re_of_pos hy]
          have hre : ((σ : ℂ) + T * I).re = σ := by simp
          have him : |T| ≤ ‖(σ : ℂ) + T * I‖ := by
            have := abs_im_le_norm ((σ : ℂ) + T * I); simpa using this
          rw [hre]
          exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le _) hT' him
        · exact hcont.intervalIntegrable _ _
    _ = (y ^ b - y ^ a) / (|T| * Real.log y) := by
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun σ _ => hderiv σ)
          (hcont.intervalIntegrable _ _)]
        field_simp

/-- Vertical segment bound. -/
lemma norm_vseg_le {y σ T : ℝ} (hy : 0 < y) (hσ : σ ≠ 0) (hT : 0 ≤ T) :
    ‖∫ t in (-T)..T, (y : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I)‖ ≤
      y ^ σ / |σ| * (2 * T) := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -T) (b := T)
    (C := y ^ σ / |σ|)
    (f := fun t : ℝ => (y : ℂ) ^ ((σ : ℂ) + t * I) / ((σ : ℂ) + t * I)) (fun t _ => by
      rw [norm_div, norm_cpow_eq_rpow_re_of_pos hy]
      have hre : ((σ : ℂ) + t * I).re = σ := by simp
      have hle : |σ| ≤ ‖(σ : ℂ) + t * I‖ := by
        have := abs_re_le_norm ((σ : ℂ) + t * I); simpa using this
      rw [hre]
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le _) (abs_pos.mpr hσ) hle)
  rwa [show |T - -T| = 2 * T by rw [sub_neg_eq_add, ← two_mul, abs_of_nonneg (by linarith)] ]
    at this

lemma differentiable_const_cpow {y : ℝ} (hy : 0 < y) :
    Differentiable ℂ (fun s : ℂ => (y : ℂ) ^ s) :=
  fun s => (differentiableAt_id).const_cpow (Or.inl (by exact_mod_cast hy.ne'))

/-- `s ↦ y^s/s` is continuous along any real-parametrized line avoiding `0`. -/
lemma continuous_cpow_div_line {y : ℝ} (hy : 0 < y) {L : ℝ → ℂ} (hL : Continuous L)
    (hL0 : ∀ u, L u ≠ 0) : Continuous fun u => (y : ℂ) ^ (L u) / L u :=
  ((differentiable_const_cpow hy).continuous.comp hL).div hL hL0

/-- Rectangle identity for `y > 1` (one simple pole at `0`, residue `1`). -/
lemma kernel_rect_gt_one {y c T U : ℝ} (hy : 1 < y) (hc : 0 < c) (hT : 0 < T) (hU : 0 < U) :
    (∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) =
      2 * π + ((∫ σ in (-U)..c, (y : ℂ) ^ ((σ : ℂ) + T * I) / ((σ : ℂ) + T * I)) -
        (∫ σ in (-U)..c, (y : ℂ) ^ ((σ : ℂ) + (-T : ℝ) * I) / ((σ : ℂ) + (-T : ℝ) * I))) * (-I) +
        ∫ t in (-T)..T, (y : ℂ) ^ (((-U : ℝ) : ℂ) + t * I) / (((-U : ℝ) : ℂ) + t * I) := by
  have hy0 : 0 < y := by linarith
  set f : ℂ → ℂ := fun s => (y : ℂ) ^ s / s with hf
  set z : ℂ := (-U : ℝ) + (-T : ℝ) * I with hz
  set w : ℂ := (c : ℝ) + (T : ℝ) * I with hw
  have hz1 : z.re = -U := by simp [hz]
  have hz2 : z.im = -T := by simp [hz]
  have hw1 : w.re = c := by simp [hw]
  have hw2 : w.im = T := by simp [hw]
  set P : Finset Residue.SimplePole := {⟨0, 1⟩} with hP
  have hres := ContourShift.rectBoundaryIntegral_eq_of_extension f
    (dslope (fun s : ℂ => (y : ℂ) ^ s) 0) z w (by rw [hz1, hw1]; linarith)
    (by rw [hz2, hw2]; linarith) P
    (by
      intro p hp
      rw [hP, Finset.mem_singleton] at hp
      subst hp
      simp only [zero_re, zero_im, hz1, hz2, hw1, hw2]
      exact ⟨by linarith, hc, by linarith, hT⟩)
    (((differentiableOn_dslope Filter.univ_mem).2
        (differentiable_const_cpow hy0).differentiableOn).mono (subset_univ _))
    (by
      intro s _ hsP
      have hs0 : s ≠ 0 := hsP ⟨0, 1⟩ (by rw [hP]; exact Finset.mem_singleton_self _)
      simp only [hf, Residue.principalPart, hP, Finset.sum_singleton, sub_zero]
      rw [dslope_of_ne _ hs0, slope_def_field, cpow_zero]
      field_simp
      ring)
    (by
      refine ⟨?_, ?_, ?_, ?_⟩
      · refine (continuous_cpow_div_line hy0 (by fun_prop) fun u h => ?_).intervalIntegrable _ _
        have := congrArg Complex.im h; simp [hz2] at this; linarith
      · refine (continuous_cpow_div_line hy0 (by fun_prop) fun u h => ?_).intervalIntegrable _ _
        have := congrArg Complex.im h; simp [hw2] at this; linarith
      · refine (continuous_cpow_div_line hy0 (by fun_prop) fun u h => ?_).intervalIntegrable _ _
        have := congrArg Complex.re h; simp [hw1] at this; linarith
      · refine (continuous_cpow_div_line hy0 (by fun_prop) fun u h => ?_).intervalIntegrable _ _
        have := congrArg Complex.re h; simp [hz1] at this; linarith)
  simp only [Residue.rectBoundaryIntegral, hz1, hz2, hw1, hw2, hP, Finset.sum_singleton,
    hf] at hres
  have h2pi : (2 * (π : ℂ) * I) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [this, I_ne_zero]
  linear_combination (-I) * hres + ((∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))
    - 2 * π - ∫ t in (-T)..T, (y : ℂ) ^ (((-U : ℝ) : ℂ) + t * I) / (((-U : ℝ) : ℂ) + t * I)) * I_sq

/-- Rectangle identity for `0 < y < 1` (no pole to the right of `Re s = c > 0`). -/
lemma kernel_rect_lt_one {y c T U : ℝ} (hy : 0 < y) (hc : 0 < c) (_hT : 0 < T) (hcU : c ≤ U) :
    (∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) =
      (∫ t in (-T)..T, (y : ℂ) ^ ((U : ℂ) + t * I) / ((U : ℂ) + t * I)) +
      ((∫ σ in c..U, (y : ℂ) ^ ((σ : ℂ) + (-T : ℝ) * I) / ((σ : ℂ) + (-T : ℝ) * I)) -
        (∫ σ in c..U, (y : ℂ) ^ ((σ : ℂ) + T * I) / ((σ : ℂ) + T * I))) * (-I) := by
  set f : ℂ → ℂ := fun s => (y : ℂ) ^ s / s with hf
  set z : ℂ := (c : ℝ) + (-T : ℝ) * I with hz
  set w : ℂ := (U : ℝ) + (T : ℝ) * I with hw
  have hz1 : z.re = c := by simp [hz]
  have hz2 : z.im = -T := by simp [hz]
  have hw1 : w.re = U := by simp [hw]
  have hw2 : w.im = T := by simp [hw]
  have hres := Residue.rectBoundaryIntegral_eq_zero_of_differentiableOn f z w (by
    intro s hs
    have h1 : s.re ∈ [[z.re, w.re]] := hs.1
    rw [hz1, hw1, uIcc_of_le hcU] at h1
    have hs0 : s ≠ 0 := by intro h; rw [h] at h1; simp at h1; linarith [h1.1]
    exact ((differentiable_const_cpow hy) s).div differentiableAt_id hs0
      |>.differentiableWithinAt)
  simp only [Residue.rectBoundaryIntegral, hz1, hz2, hw1, hw2, hf] at hres
  linear_combination I * hres + ((∫ t in (-T)..T, (y : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))
    - ∫ t in (-T)..T, (y : ℂ) ^ ((U : ℂ) + t * I) / ((U : ℂ) + t * I)) * I_sq

lemma le_of_forall_le_add_div {a b K : ℝ} (h : ∀ U : ℝ, 1 ≤ U → a ≤ b + K / U) : a ≤ b := by
  have ht : Tendsto (fun U : ℝ => b + K / U) atTop (𝓝 (b + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
  rw [add_zero] at ht
  exact ge_of_tendsto ht (eventually_atTop.2 ⟨1, h⟩)

lemma norm_two_pi_inv : ‖(((2 * π : ℝ) : ℂ))⁻¹‖ = (2 * π)⁻¹ := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.two_pi_pos]

/-- **Truncated Perron kernel, `y > 1`**: `‖K(y,c,T) − 1‖ ≤ y^c / (π T |log y|)`. -/
theorem kernel_gt_one {y c T : ℝ} (hy : 1 < y) (hc : 0 < c) (hT : 0 < T) :
    ‖kernel y c T - 1‖ ≤ y ^ c / (π * T * |Real.log y|) := by
  have hy0 : 0 < y := by linarith
  have hlog : 0 < Real.log y := Real.log_pos hy
  rw [abs_of_pos hlog]
  apply le_of_forall_le_add_div (K := T / π)
  intro U hU
  have hU0 : 0 < U := by linarith
  rw [kernel, kernel_rect_gt_one hy hc hT hU0]
  set Ht := ∫ σ in (-U)..c, (y : ℂ) ^ ((σ : ℂ) + T * I) / ((σ : ℂ) + T * I)
  set Hb := ∫ σ in (-U)..c, (y : ℂ) ^ ((σ : ℂ) + (-T : ℝ) * I) / ((σ : ℂ) + (-T : ℝ) * I)
  set VL := ∫ t in (-T)..T, (y : ℂ) ^ (((-U : ℝ) : ℂ) + t * I) / (((-U : ℝ) : ℂ) + t * I)
  have hpi : ((2 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  have e : ((2 * π : ℝ) : ℂ)⁻¹ * (2 * π + (Ht - Hb) * (-I) + VL) - 1 =
      ((2 * π : ℝ) : ℂ)⁻¹ * ((Ht - Hb) * (-I) + VL) := by
    field_simp; push_cast; ring
  rw [e, norm_mul, norm_two_pi_inv]
  have hHt : ‖Ht‖ ≤ y ^ c / (T * Real.log y) := by
    refine (norm_hseg_le hy0 hy.ne' (by linarith) hT.ne').trans ?_
    rw [abs_of_pos hT]
    gcongr
    linarith [Real.rpow_nonneg hy0.le (-U)]
  have hHb : ‖Hb‖ ≤ y ^ c / (T * Real.log y) := by
    refine (norm_hseg_le hy0 hy.ne' (by linarith) (by simpa using hT.ne')).trans ?_
    rw [abs_neg, abs_of_pos hT]
    gcongr
    linarith [Real.rpow_nonneg hy0.le (-U)]
  have hVL : ‖VL‖ ≤ 2 * T / U := by
    refine (norm_vseg_le hy0 (by linarith : (-U : ℝ) ≠ 0) hT.le).trans ?_
    rw [abs_neg, abs_of_pos hU0]
    have : y ^ (-U) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy.le (by linarith)
    calc y ^ (-U) / U * (2 * T) ≤ 1 / U * (2 * T) := by gcongr
      _ = 2 * T / U := by ring
  have hsum : ‖(Ht - Hb) * (-I) + VL‖ ≤ 2 * (y ^ c / (T * Real.log y)) + 2 * T / U := by
    calc ‖(Ht - Hb) * (-I) + VL‖ ≤ ‖Ht - Hb‖ * ‖-I‖ + ‖VL‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul]
      _ ≤ (‖Ht‖ + ‖Hb‖) * 1 + ‖VL‖ := by
          rw [norm_neg, norm_I]; gcongr; exact norm_sub_le _ _
      _ ≤ _ := by linarith
  calc (2 * π)⁻¹ * ‖(Ht - Hb) * (-I) + VL‖
      ≤ (2 * π)⁻¹ * (2 * (y ^ c / (T * Real.log y)) + 2 * T / U) := by
        gcongr
    _ = y ^ c / (π * T * Real.log y) + T / π / U := by
        field_simp

/-- **Truncated Perron kernel, `0 < y < 1`**: `‖K(y,c,T)‖ ≤ y^c / (π T |log y|)`. -/
theorem kernel_lt_one {y c T : ℝ} (hy0 : 0 < y) (hy : y < 1) (hc : 0 < c) (hT : 0 < T) :
    ‖kernel y c T‖ ≤ y ^ c / (π * T * |Real.log y|) := by
  have hlog : Real.log y < 0 := Real.log_neg hy0 hy
  rw [abs_of_neg hlog]
  apply le_of_forall_le_add_div (K := T / π)
  intro U' hU'
  set U := max U' c with hUdef
  have hcU : c ≤ U := le_max_right _ _
  have hU'U : U' ≤ U := le_max_left _ _
  have hU0 : 0 < U := by linarith
  rw [kernel, kernel_rect_lt_one hy0 hc hT hcU]
  set Ht := ∫ σ in c..U, (y : ℂ) ^ ((σ : ℂ) + T * I) / ((σ : ℂ) + T * I)
  set Hb := ∫ σ in c..U, (y : ℂ) ^ ((σ : ℂ) + (-T : ℝ) * I) / ((σ : ℂ) + (-T : ℝ) * I)
  set VR := ∫ t in (-T)..T, (y : ℂ) ^ ((U : ℂ) + t * I) / ((U : ℂ) + t * I)
  rw [norm_mul, norm_two_pi_inv]
  have key : ∀ T' : ℝ, |T'| = T → ‖∫ σ in c..U, (y : ℂ) ^ ((σ : ℂ) + T' * I) / ((σ : ℂ) + T' * I)‖
      ≤ y ^ c / (T * -Real.log y) := by
    intro T' hT'
    have hT'0 : T' ≠ 0 := by intro h; rw [h, abs_zero] at hT'; linarith
    refine (norm_hseg_le hy0 hy.ne hcU hT'0).trans ?_
    have hden : 0 < T * -Real.log y := mul_pos hT (neg_pos.2 hlog)
    rw [hT', ← neg_div_neg_eq, neg_sub, ← mul_neg]
    exact div_le_div_of_nonneg_right (by linarith [Real.rpow_nonneg hy0.le U]) hden.le
  have hHt : ‖Ht‖ ≤ y ^ c / (T * -Real.log y) := key T (abs_of_pos hT)
  have hHb : ‖Hb‖ ≤ y ^ c / (T * -Real.log y) := key (-T) (by rw [abs_neg, abs_of_pos hT])
  have hVR : ‖VR‖ ≤ 2 * T / U' := by
    refine (norm_vseg_le hy0 hU0.ne' hT.le).trans ?_
    rw [abs_of_pos hU0]
    have : y ^ U ≤ 1 := Real.rpow_le_one hy0.le hy.le hU0.le
    calc y ^ U / U * (2 * T) ≤ 1 / U' * (2 * T) := by
          gcongr
      _ = 2 * T / U' := by ring
  have hsum : ‖VR + (Hb - Ht) * (-I)‖ ≤ 2 * (y ^ c / (T * -Real.log y)) + 2 * T / U' := by
    calc ‖VR + (Hb - Ht) * (-I)‖ ≤ ‖VR‖ + ‖Hb - Ht‖ * ‖-I‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul]
      _ ≤ ‖VR‖ + (‖Hb‖ + ‖Ht‖) * 1 := by
          rw [norm_neg, norm_I]; gcongr; exact norm_sub_le _ _
      _ ≤ _ := by linarith
  calc (2 * π)⁻¹ * ‖VR + (Hb - Ht) * (-I)‖
      ≤ (2 * π)⁻¹ * (2 * (y ^ c / (T * -Real.log y)) + 2 * T / U') := by gcongr
    _ = y ^ c / (π * T * -Real.log y) + T / π / U' := by
        field_simp

/-! ## The truncated Perron integral as a series of kernels -/

/-- `−ζ'/ζ(s) = ∑ Λ(n)/n^s` on `Re s > 1` (Mathlib `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`). -/
lemma neg_logDeriv_eq_tsum {s : ℂ} (hs : 1 < s.re) :
    -(deriv riemannZeta s) / riemannZeta s = ∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ s := by
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, LSeries]
  refine tsum_congr fun n => ?_
  rw [LSeries.term_def]
  split_ifs with h
  · subst h; simp
  · rfl

lemma vonMangoldt_term_eq {x : ℝ} (hx : 0 < x) (n : ℕ) (s : ℂ) :
    (Λ n : ℂ) / (n : ℂ) ^ s * ((x : ℂ) ^ s / s) = (Λ n : ℂ) * (((x / n : ℝ) : ℂ) ^ s / s) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have hn : (0 : ℝ) < n := by exact_mod_cast h
    rw [ofReal_div, div_cpow_ofReal_nonneg hx.le hn.le, ofReal_natCast]
    have : (n : ℂ) ^ s ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]; push Not; intro h'; exact absurd h' (by exact_mod_cast h.ne')
    field_simp

lemma norm_vonMangoldt_term_le {x c : ℝ} (hx : 0 < x) (hc : 0 < c) (n : ℕ) (t : ℝ) :
    ‖(Λ n : ℂ) * (((x / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))‖ ≤
      x ^ c / c * ExplicitFormula.coeff c n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [ExplicitFormula.coeff_zero]
  · have hn : (0 : ℝ) < n := by exact_mod_cast h
    have hxn : 0 < x / n := div_pos hx hn
    rw [norm_mul, norm_div, norm_cpow_eq_rpow_re_of_pos hxn, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero]
    have hcn : c ≤ ‖(c : ℂ) + t * I‖ := by
      have := abs_re_le_norm ((c : ℂ) + t * I); simp at this; linarith [le_abs_self c]
    rw [Real.div_rpow hx.le hn.le, ExplicitFormula.coeff, Real.rpow_neg hn.le]
    have hΛ := (ArithmeticFunction.vonMangoldt_nonneg (n := n))
    have hnc : 0 < (n : ℝ) ^ c := Real.rpow_pos_of_pos hn c
    have hxc : 0 ≤ x ^ c := Real.rpow_nonneg hx.le c
    calc Λ n * (x ^ c / (n : ℝ) ^ c / ‖(c : ℂ) + t * I‖)
        ≤ Λ n * (x ^ c / (n : ℝ) ^ c / c) := by gcongr
      _ = x ^ c / c * (Λ n * ((n : ℝ) ^ c)⁻¹) := by field_simp

/-- **Truncated Perron integral as a series of kernels**: for `x > 0`, `c > 1`, `T ≥ 0`,
`∫_{-T}^{T} (−ζ'/ζ)(c+it) · x^{c+it}/(c+it) dt = 2π ∑ Λ(n) K(x/n, c, T)`. -/
theorem perron_integral_eq_tsum {x c T : ℝ} (hx : 0 < x) (hc : 1 < c) (hT : 0 ≤ T) :
    (∫ t in (-T)..T, (-(deriv riemannZeta ((c : ℂ) + t * I))) / riemannZeta ((c : ℂ) + t * I) *
      ((x : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))) =
      2 * π * ∑' n : ℕ, (Λ n : ℂ) * kernel (x / n) c T := by
  have hc0 : 0 < c := by linarith
  set F : ℕ → ℝ → ℂ := fun n t =>
    (Λ n : ℂ) * (((x / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) with hF
  have hs0 : ∀ t : ℝ, (c : ℂ) + t * I ≠ 0 := by
    intro t h; have := congrArg Complex.re h; simp at this; linarith
  have hpt : ∀ t : ℝ, (-(deriv riemannZeta ((c : ℂ) + t * I))) / riemannZeta ((c : ℂ) + t * I) *
      ((x : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) = ∑' n, F n t := by
    intro t
    rw [neg_logDeriv_eq_tsum (by simpa using hc), ← tsum_mul_right]
    exact tsum_congr fun n => vonMangoldt_term_eq hx n _
  have hcont : ∀ n, Continuous (F n) := by
    intro n
    refine continuous_const.mul (Continuous.div ?_ (by fun_prop) hs0)
    exact (by fun_prop : Continuous fun t : ℝ => (c : ℂ) + t * I).const_cpow (Or.inr hs0)
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioc (-T) T)) :=
    fun n => (hcont n).integrableOn_Ioc
  have hsum : Summable fun n => ∫ t, ‖F n t‖ ∂(volume.restrict (Ioc (-T) T)) := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_)
      ((ExplicitFormula.coeff_summable hc).mul_left (x ^ c / c * (2 * T)))
    calc ∫ t, ‖F n t‖ ∂(volume.restrict (Ioc (-T) T))
        ≤ ∫ t, x ^ c / c * ExplicitFormula.coeff c n ∂(volume.restrict (Ioc (-T) T)) :=
          integral_mono (hint n).norm (integrable_const _)
            (fun t => norm_vonMangoldt_term_le hx hc0 n t)
      _ = x ^ c / c * (2 * T) * ExplicitFormula.coeff c n := by
          rw [integral_const, smul_eq_mul, measureReal_restrict_apply_univ, Real.volume_real_Ioc,
            show T - -T = 2 * T by ring, max_eq_left (by linarith)]
          ring
  unfold kernel
  simp_rw [hpt]
  rw [intervalIntegral.integral_of_le (by linarith),
    ← integral_tsum_of_summable_integral_norm hint hsum, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [intervalIntegral.integral_of_le (by linarith), hF]
  simp only
  rw [integral_const_mul]
  have h2 : (2 * (π : ℂ)) * (((2 * π : ℝ) : ℂ))⁻¹ = 1 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast; field_simp
  rw [show ∀ a b J : ℂ, 2 * (π : ℂ) * (a * (b * J)) = a * ((2 * π * b) * J) from
    fun a b J => by ring, h2, one_mul]

/-- The kernel series is (absolutely) summable. -/
lemma summable_kernel_terms {x c T : ℝ} (hx : 0 < x) (hc : 1 < c) (hT : 0 ≤ T) :
    Summable fun n : ℕ => (Λ n : ℂ) * kernel (x / n) c T := by
  have hc0 : 0 < c := by linarith
  refine Summable.of_norm_bounded
    ((ExplicitFormula.coeff_summable hc).mul_left ((2 * π)⁻¹ * (x ^ c / c * (2 * T)))) fun n => ?_
  have hb : ‖∫ t in (-T)..T, (((x / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))‖ *
      Λ n ≤ x ^ c / c * (2 * T) * ExplicitFormula.coeff c n := by
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := -T) (b := T)
      (C := x ^ c / c * ExplicitFormula.coeff c n)
      (f := fun t : ℝ => (Λ n : ℂ) * (((x / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)))
      (fun t _ => norm_vonMangoldt_term_le hx hc0 n t)
    rw [intervalIntegral.integral_const_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      show |T - -T| = 2 * T by rw [sub_neg_eq_add, ← two_mul, abs_of_nonneg (by linarith)] ] at h1
    linarith
  rw [kernel, norm_mul, norm_mul, norm_two_pi_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have h2 : 0 ≤ (2 * π)⁻¹ := by positivity
  calc Λ n * ((2 * π)⁻¹ * ‖∫ t in (-T)..T, (((x / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) /
        ((c : ℂ) + t * I))‖)
      = (2 * π)⁻¹ * (‖∫ t in (-T)..T, (((x / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) /
        ((c : ℂ) + t * I))‖ * Λ n) := by ring
    _ ≤ (2 * π)⁻¹ * (x ^ c / c * (2 * T) * ExplicitFormula.coeff c n) := by gcongr
    _ = _ := by ring

/-! ## `∑ Λ(n) n^{-3/2} ≤ 20` -/

/-- `∑ Λ(n) n^{-3/2} ≤ 20`: `Λ(n) ≤ log n ≤ 4 n^{1/4}` and `∑ (n+1)^{-5/4} ≤ 5`. -/
theorem S32_le : ∑' n : ℕ, ExplicitFormula.coeff (3 / 2) n ≤ 20 := by
  have hs := ExplicitFormula.coeff_summable (c := 3 / 2) (by norm_num)
  rw [hs.tsum_eq_zero_add, ExplicitFormula.coeff_zero, zero_add]
  have hsum := ZetaGrowth.summable_add_one_rpow (a := -(1 + 1 / 4)) (by norm_num)
  have hb := ZetaGrowth.tsum_add_one_rpow_le (p := 1 / 4) (by norm_num)
  have hle : ∀ n : ℕ, ExplicitFormula.coeff (3 / 2) (n + 1) ≤ 4 * ((n : ℝ) + 1) ^ (-(1 + 1 / 4) : ℝ) := by
    intro n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [ExplicitFormula.coeff]
    push_cast
    have h1 : Λ (n + 1) ≤ Real.log ((n : ℝ) + 1) := by
      have := ArithmeticFunction.vonMangoldt_le_log (n := n + 1); push_cast at this; exact this
    have h2 := Real.log_le_rpow_div hn.le (by norm_num : (0 : ℝ) < 1 / 4)
    have h3 : Λ (n + 1) ≤ 4 * ((n : ℝ) + 1) ^ (1 / 4 : ℝ) := by
      have : ((n : ℝ) + 1) ^ (1 / 4 : ℝ) / (1 / 4) = 4 * ((n : ℝ) + 1) ^ (1 / 4 : ℝ) := by ring
      linarith
    have hp : 0 < ((n : ℝ) + 1) ^ (-(3 / 2) : ℝ) := Real.rpow_pos_of_pos hn _
    calc Λ (n + 1) * ((n : ℝ) + 1) ^ (-(3 / 2) : ℝ)
        ≤ 4 * ((n : ℝ) + 1) ^ (1 / 4 : ℝ) * ((n : ℝ) + 1) ^ (-(3 / 2) : ℝ) := by gcongr
      _ = 4 * ((n : ℝ) + 1) ^ (-(1 + 1 / 4) : ℝ) := by
          rw [mul_assoc, ← Real.rpow_add hn]; norm_num
  have hs' : Summable fun n : ℕ => ExplicitFormula.coeff (3 / 2) (n + 1) :=
    (summable_nat_add_iff 1).mpr hs
  calc ∑' n : ℕ, ExplicitFormula.coeff (3 / 2) (n + 1)
      ≤ ∑' n : ℕ, 4 * ((n : ℝ) + 1) ^ (-(1 + 1 / 4) : ℝ) :=
        hs'.tsum_le_tsum hle (hsum.mul_left 4)
    _ = 4 * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + 1 / 4) : ℝ) := tsum_mul_left
    _ ≤ 4 * (1 + 1 / (1 / 4)) := by gcongr
    _ = 20 := by norm_num

/-! ## Truncated Perron with an explicit error at half-integers -/

/-- At a half-integer `x = N + 1/2`, `|log (x/n)| ≥ 1/(4x)` for every `n ≥ 1`. -/
lemma halfint_log_bound {N n : ℕ} (hN : 1 ≤ N) (hn : 1 ≤ n) :
    1 / (4 * ((N : ℝ) + 1 / 2)) ≤ |Real.log (((N : ℝ) + 1 / 2) / n)| := by
  set x : ℝ := (N : ℝ) + 1 / 2 with hx
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : 0 < x := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  rcases le_or_gt (n : ℝ) N with h | h
  · have hxn : 1 < x / n := (one_lt_div hn0).2 (by linarith)
    rw [abs_of_pos (Real.log_pos hxn)]
    have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hx0 hn0)
    rw [inv_div] at h1
    have h2 : 1 / (4 * x) ≤ 1 - n / x := by
      rw [div_le_iff₀ (by positivity), sub_mul, div_mul_eq_mul_div, mul_comm (n : ℝ) (4 * x),
        mul_div_assoc, show (4 * x * ((n : ℝ) / x)) = 4 * n by field_simp]
      linarith
    linarith
  · have hNn : (N : ℝ) + 1 ≤ n := by exact_mod_cast (show N + 1 ≤ n by exact_mod_cast h)
    have hxn : x / n < 1 := (div_lt_one hn0).2 (by linarith)
    rw [abs_of_neg (Real.log_neg (div_pos hx0 hn0) hxn)]
    have h1 := Real.log_le_sub_one_of_pos (div_pos hx0 hn0)
    have h2 : 1 / (4 * x) ≤ 1 - x / n := by
      rw [show 1 - x / n = (n - x) / n by field_simp, div_le_div_iff₀ (by positivity) hn0]
      nlinarith
    linarith

/-- The indicator `n ≤ N`. -/
def ind (N n : ℕ) : ℂ := if n ≤ N then 1 else 0

/-- Termwise Perron error at a half-integer. -/
lemma norm_term_error_halfint {N n : ℕ} (hN : 1 ≤ N) {c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    ‖(Λ n : ℂ) * (ind N n - kernel (((N : ℝ) + 1 / 2) / n) c T)‖ ≤
      4 * ((N : ℝ) + 1 / 2) ^ (c + 1) / (π * T) * ExplicitFormula.coeff c n := by
  set x : ℝ := (N : ℝ) + 1 / 2 with hx
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0; simp [ExplicitFormula.coeff_zero]
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : 0 < x := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hy0 : 0 < x / n := div_pos hx0 hn0
  have hlog := halfint_log_bound hN hn
  rw [← hx] at hlog
  have hK : ‖ind N n - kernel (x / n) c T‖ ≤ (x / n) ^ c / (π * T * |Real.log (x / n)|) := by
    rcases le_or_gt n N with h | h
    · have hgt : 1 < x / n := (one_lt_div hn0).2 (by
        have : (n : ℝ) ≤ N := by exact_mod_cast h
        linarith)
      rw [show ind N n = 1 by simp [ind, h], norm_sub_rev]; exact kernel_gt_one hgt hc hT
    · have hlt : x / n < 1 := (div_lt_one hn0).2 (by
        have : (N : ℝ) + 1 ≤ n := by exact_mod_cast h
        linarith)
      rw [show ind N n = 0 by simp [ind, not_le.mpr h], zero_sub, norm_neg]
      exact kernel_lt_one hy0 hlt hc hT
  have hK' : ‖ind N n - kernel (x / n) c T‖ ≤ (x / n) ^ c * (4 * x) / (π * T) := by
    refine hK.trans ?_
    have hlp : 0 < |Real.log (x / n)| := lt_of_lt_of_le (by
      have : 0 < 4 * x := by linarith
      positivity) hlog
    rw [div_le_div_iff₀ (mul_pos (mul_pos Real.pi_pos hT) hlp) (mul_pos Real.pi_pos hT)]
    have h4 : 1 ≤ 4 * x * |Real.log (x / n)| := by
      have := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ 4 * x)
      rwa [mul_one_div_cancel (mul_pos (by norm_num : (0:ℝ) < 4) hx0).ne'] at this
    have hy2 : 0 ≤ (x / n) ^ c := Real.rpow_nonneg hy0.le c
    have hpT : 0 < π * T := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h4 (mul_nonneg hy2 hpT.le)]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hΛ := (ArithmeticFunction.vonMangoldt_nonneg (n := n))
  calc Λ n * ‖ind N n - kernel (x / n) c T‖
      ≤ Λ n * ((x / n) ^ c * (4 * x) / (π * T)) := by gcongr
    _ = 4 * x ^ (c + 1) / (π * T) * ExplicitFormula.coeff c n := by
        rw [Real.div_rpow hx0.le hn0.le, Real.rpow_add_one hx0.ne', ExplicitFormula.coeff,
          Real.rpow_neg hn0.le]
        field_simp

/-- `ψ(N + 1/2) = ∑ Λ(n)·[n ≤ N]`. -/
lemma psi_halfint_eq_tsum (N : ℕ) :
    ((Chebyshev.psi ((N : ℝ) + 1 / 2) : ℝ) : ℂ) = ∑' n : ℕ, (Λ n : ℂ) * ind N n := by
  have hfl : ⌊(N : ℝ) + 1 / 2⌋₊ = N := by
    rw [Nat.floor_eq_iff (by positivity)]; constructor <;> linarith
  rw [tsum_eq_sum (s := Finset.range (N + 1)) (fun n hn => by
    rw [Finset.mem_range, not_lt] at hn
    simp [ind, show ¬ n ≤ N by omega])]
  rw [Chebyshev.psi_eq_sum_Icc, hfl]
  push_cast
  have hI : Finset.Icc 0 N = Finset.range (N + 1) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_range, zero_le, true_and]; omega
  rw [hI]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_range] at hn
  simp [ind, show n ≤ N by omega]

/-- **Truncated Perron formula with explicit error at half-integers** (`c = 3/2`): for
`x = N + 1/2`, `N ≥ 1`, `T > 0`, `‖ψ(x) − ∑ Λ(n) K(x/n, 3/2, T)‖ ≤ 80 x^{5/2}/(π T)`. -/
theorem perron_error_halfint {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hT : 0 < T) :
    ‖((Chebyshev.psi ((N : ℝ) + 1 / 2) : ℝ) : ℂ) -
        ∑' n : ℕ, (Λ n : ℂ) * kernel (((N : ℝ) + 1 / 2) / n) (3 / 2) T‖ ≤
      80 * ((N : ℝ) + 1 / 2) ^ (5 / 2 : ℝ) / (π * T) := by
  set x : ℝ := (N : ℝ) + 1 / 2 with hx
  have hx0 : 0 < x := by positivity
  have hsumK := summable_kernel_terms (x := x) (c := 3 / 2) (T := T) hx0 (by norm_num) hT.le
  have hsumI : Summable fun n : ℕ => (Λ n : ℂ) * ind N n := by
    apply summable_of_ne_finset_zero (s := Finset.range (N + 1))
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    simp [ind, show ¬ n ≤ N by omega]
  set B : ℝ := 4 * x ^ ((3 / 2 : ℝ) + 1) / (π * T) with hB
  have hsumB : Summable fun n : ℕ => B * ExplicitFormula.coeff (3 / 2) n :=
    (ExplicitFormula.coeff_summable (by norm_num)).mul_left B
  have hterm : ∀ n : ℕ, ‖(Λ n : ℂ) * ind N n - (Λ n : ℂ) * kernel (x / n) (3 / 2) T‖ ≤
      B * ExplicitFormula.coeff (3 / 2) n := by
    intro n
    rw [← mul_sub]
    exact norm_term_error_halfint hN (by norm_num) hT
  have hsplit : ((Chebyshev.psi x : ℝ) : ℂ) - ∑' n : ℕ, (Λ n : ℂ) * kernel (x / n) (3 / 2) T =
      ∑' n : ℕ, ((Λ n : ℂ) * ind N n - (Λ n : ℂ) * kernel (x / n) (3 / 2) T) := by
    rw [psi_halfint_eq_tsum, hsumI.tsum_sub hsumK]
  rw [hsplit]
  have hsE : Summable fun n : ℕ =>
      ‖(Λ n : ℂ) * ind N n - (Λ n : ℂ) * kernel (x / n) (3 / 2) T‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsumB
  refine (norm_tsum_le_tsum_norm hsE).trans ?_
  refine (hsE.tsum_le_tsum hterm hsumB).trans ?_
  rw [tsum_mul_left]
  have hB0 : 0 ≤ B := by positivity
  calc B * ∑' n : ℕ, ExplicitFormula.coeff (3 / 2) n ≤ B * 20 := by gcongr; exact S32_le
    _ = 80 * x ^ (5 / 2 : ℝ) / (π * T) := by rw [hB]; norm_num; ring

/-- **The reflected Perron sum is small**: for `x > 1`, `T > 0`,
`‖∑ Λ(n) K((1/x)/n, 3/2, T)‖ ≤ 20/(π T log x)`. -/
theorem perron_small {x T : ℝ} (hx : 1 < x) (hT : 0 < T) :
    ‖∑' n : ℕ, (Λ n : ℂ) * kernel ((1 / x) / n) (3 / 2) T‖ ≤ 20 / (π * T * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hsumK := summable_kernel_terms (x := 1 / x) (c := 3 / 2) (T := T) (by positivity)
    (by norm_num) hT.le
  set B : ℝ := 1 / (π * T * Real.log x) with hB
  have hterm : ∀ n : ℕ, ‖(Λ n : ℂ) * kernel ((1 / x) / n) (3 / 2) T‖ ≤
      B * ExplicitFormula.coeff (3 / 2) n := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · subst h0; simp [ExplicitFormula.coeff_zero]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hy0 : 0 < 1 / x / n := by positivity
    have hy1 : 1 / x / n < 1 := by
      rw [div_div, div_lt_one (by positivity)]; nlinarith
    have hK := kernel_lt_one hy0 hy1 (by norm_num : (0 : ℝ) < 3 / 2) hT
    have hlog : Real.log x ≤ |Real.log (1 / x / n)| := by
      rw [div_div, one_div, Real.log_inv, abs_neg, Real.log_mul hx0.ne' hn0.ne',
        abs_of_nonneg (by have := Real.log_nonneg hn1; linarith)]
      linarith [Real.log_nonneg hn1]
    have hpow : (1 / x / n) ^ (3 / 2 : ℝ) ≤ (n : ℝ) ^ (-(3 / 2) : ℝ) := by
      rw [div_div, Real.rpow_neg hn0.le, one_div, Real.inv_rpow (by positivity)]
      apply inv_anti₀ (by positivity)
      exact Real.rpow_le_rpow hn0.le (by nlinarith) (by norm_num)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have hΛ := (ArithmeticFunction.vonMangoldt_nonneg (n := n))
    calc Λ n * ‖kernel (1 / x / n) (3 / 2) T‖
        ≤ Λ n * ((1 / x / n) ^ (3 / 2 : ℝ) / (π * T * |Real.log (1 / x / n)|)) := by gcongr
      _ ≤ Λ n * ((n : ℝ) ^ (-(3 / 2) : ℝ) / (π * T * Real.log x)) := by gcongr
      _ = B * ExplicitFormula.coeff (3 / 2) n := by
          rw [hB, ExplicitFormula.coeff]; field_simp
  have hsumB : Summable fun n : ℕ => B * ExplicitFormula.coeff (3 / 2) n :=
    (ExplicitFormula.coeff_summable (by norm_num)).mul_left B
  refine (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
    hsumB)).trans ?_
  refine ((Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsumB).tsum_le_tsum hterm
    hsumB).trans ?_
  rw [tsum_mul_left]
  have hB0 : 0 ≤ B := by positivity
  calc B * ∑' n : ℕ, ExplicitFormula.coeff (3 / 2) n ≤ B * 20 := by gcongr; exact S32_le
    _ = 20 / (π * T * Real.log x) := by rw [hB]; ring

/-! ## An integral -/

lemma integral_inv_one_add_abs {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in (-T)..T, (1 + |t|)⁻¹ = 2 * Real.log (1 + T) := by
  have hc : Continuous fun t : ℝ => (1 + |t|)⁻¹ :=
    (continuous_const.add continuous_abs).inv₀
      (fun t => (add_pos_of_pos_of_nonneg one_pos (abs_nonneg t)).ne')
  have hpos : ∫ t in (0 : ℝ)..T, (1 + |t|)⁻¹ = Real.log (1 + T) := by
    have e : ∫ t in (0 : ℝ)..T, (1 + |t|)⁻¹ = ∫ t in (0 : ℝ)..T, (1 + t)⁻¹ := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le hT] at ht
      simp only [abs_of_nonneg ht.1]
    rw [e, intervalIntegral.integral_comp_add_left (fun t => t⁻¹), add_zero,
      integral_inv_of_pos one_pos (by linarith), div_one]
  have hneg : ∫ t in (-T)..0, (1 + |t|)⁻¹ = Real.log (1 + T) := by
    rw [← hpos, ← neg_zero, ← intervalIntegral.integral_comp_neg]
    simp only [neg_zero, abs_neg]
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _), hneg, hpos]
  ring

end FleetExplicitPNTKernel
