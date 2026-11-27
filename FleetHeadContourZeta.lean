import Mathlib
import ZetaGrowth

/-!
# `ζ'` on `Re s ≥ 1/2`: the regular part, a Cauchy estimate, and `−ζ' = Σ log n · n^{-s}`

* `zetaReg := ζ(s) − 1/(s−1)`, completed at `s = 1` by Euler's constant, is **entire**
  (`differentiable_zetaReg`).
* `deriv_riemannZeta_eq`: `ζ'(s) = zetaReg'(s) − 1/(s−1)²` for `s ≠ 1`.
* `norm_zetaReg_le`: `‖zetaReg s‖ ≤ 5‖s‖` on `Re s ≥ 1/4` (Euler–Maclaurin remainder of `ZetaGrowth`).
* `norm_deriv_zetaReg_le`: `‖zetaReg' s‖ ≤ 20‖s‖ + 5` on `Re s ≥ 1/2` (Cauchy estimate, radius `1/4`).
* `norm_deriv_zeta_le`: `‖ζ'(s)‖ ≤ ‖s−1‖^{-2} + 20‖s‖ + 5` on `Re s ≥ 1/2`, `s ≠ 1`.
* `neg_deriv_zeta_eq_tsum`: `−ζ'(w) = Σ_{n ≥ 0} log(n+2) (n+2)^{-w}` for `Re w > 1`.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set LSeries
open scoped Real

namespace FleetHeadContour

/-- `ζ(s) − 1/(s−1)`, with the value `γ` (Euler's constant) at `s = 1`. -/
def zetaReg : ℂ → ℂ :=
  Function.update (fun s => riemannZeta s - 1 / (s - 1)) 1 (Real.eulerMascheroniConstant : ℂ)

lemma zetaReg_of_ne {s : ℂ} (hs : s ≠ 1) : zetaReg s = riemannZeta s - 1 / (s - 1) := by
  simp [zetaReg, Function.update_of_ne hs]

/-- **`zetaReg` is entire.** -/
theorem differentiable_zetaReg : Differentiable ℂ zetaReg := by
  rw [← differentiableOn_univ]
  refine (differentiableOn_compl_singleton_and_continuousAt_iff (f := zetaReg) (s := univ)
    (c := 1) univ_mem).mp ⟨?_, ?_⟩
  · intro z hz
    have hz1 : z ≠ 1 := hz.2
    have hd : DifferentiableAt ℂ (fun s => riemannZeta s - 1 / (s - 1)) z :=
      (differentiableAt_riemannZeta hz1).sub
        ((differentiableAt_const _).div (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hz1))
    have heq : zetaReg =ᶠ[𝓝 z] (fun s => riemannZeta s - 1 / (s - 1)) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hz1] with s hs
      exact zetaReg_of_ne hs
    exact (hd.congr_of_eventuallyEq heq).differentiableWithinAt
  · unfold zetaReg
    rw [continuousAt_update_same]
    exact tendsto_riemannZeta_sub_one_div

lemma riemannZeta_eq_zetaReg {s : ℂ} (hs : s ≠ 1) :
    riemannZeta s = zetaReg s + (s - 1)⁻¹ := by
  rw [zetaReg_of_ne hs, one_div]; ring

/-- **`ζ' = zetaReg' − (s−1)^{-2}`** off `s = 1`. -/
theorem deriv_riemannZeta_eq {s : ℂ} (hs : s ≠ 1) :
    deriv riemannZeta s = deriv zetaReg s - ((s - 1) ^ 2)⁻¹ := by
  have heq : riemannZeta =ᶠ[𝓝 s] (fun z => zetaReg z + (z - 1)⁻¹) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with z hz
    exact riemannZeta_eq_zetaReg hz
  rw [heq.deriv_eq]
  have h1 := (differentiable_zetaReg s).hasDerivAt
  have h2 : HasDerivAt (fun y : ℂ => (y - 1)⁻¹) (-1 / (s - 1) ^ 2) s := by
    simpa using ((hasDerivAt_id s).sub_const (1 : ℂ)).fun_inv (sub_ne_zero.mpr hs)
  rw [(h1.fun_add h2).deriv]
  ring

/-- **`‖zetaReg s‖ ≤ 5‖s‖`** on `Re s ≥ 1/4`. -/
theorem norm_zetaReg_le {s : ℂ} (hs : 1 / 4 ≤ s.re) : ‖zetaReg s‖ ≤ 5 * ‖s‖ := by
  by_cases hs1 : s = 1
  · subst hs1
    simp only [zetaReg, Function.update_self, norm_one, mul_one]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith [Real.one_half_lt_eulerMascheroniConstant])]
    linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  have hs0 : 0 < s.re := by linarith
  rw [zetaReg_of_ne hs1, ZetaGrowth.zeta_eq_zetaAbel hs0 hs1, ZetaGrowth.zetaAbel, add_sub_cancel_left]
  have hK := ZetaGrowth.tsum_add_one_rpow_le (p := 1 / 4) (by norm_num)
  have hsum := ZetaGrowth.summable_add_one_rpow (a := -(1 + 1 / 4)) (by norm_num)
  calc ‖∑' n : ℕ, ZetaGrowth.emTerm (n + 1) s‖
      ≤ ∑' n : ℕ, ‖s‖ * ((n : ℝ) + 1) ^ (-(1 + 1 / 4 : ℝ)) := by
        refine tsum_of_norm_bounded (hsum.mul_left ‖s‖).hasSum fun n => ?_
        calc ‖ZetaGrowth.emTerm (n + 1) s‖ ≤ ‖s‖ * ((n + 1 : ℕ) : ℝ) ^ (-s.re - 1) :=
              ZetaGrowth.norm_emTerm_le hs0 hs1 (by omega)
          _ ≤ ‖s‖ * ((n : ℝ) + 1) ^ (-(1 + 1 / 4 : ℝ)) := by
              push_cast
              apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
              apply Real.rpow_le_rpow_of_exponent_le
                (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
              linarith
    _ = ‖s‖ * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + 1 / 4 : ℝ)) := tsum_mul_left
    _ ≤ ‖s‖ * 5 := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        norm_num at hK ⊢; linarith
    _ = 5 * ‖s‖ := by ring

/-- **Cauchy estimate: `‖zetaReg' s‖ ≤ 20‖s‖ + 5`** on `Re s ≥ 1/2`. -/
theorem norm_deriv_zetaReg_le {s : ℂ} (hs : 1 / 2 ≤ s.re) : ‖deriv zetaReg s‖ ≤ 20 * ‖s‖ + 5 := by
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := s) (R := 1 / 4)
    (C := 5 * (‖s‖ + 1 / 4)) (f := zetaReg) (by norm_num) differentiable_zetaReg.diffContOnCl ?_
  · calc ‖deriv zetaReg s‖ ≤ 5 * (‖s‖ + 1 / 4) / (1 / 4) := h
      _ = 20 * ‖s‖ + 5 := by ring
  intro z hz
  rw [mem_sphere_iff_norm] at hz
  have hre : |(z - s).re| ≤ 1 / 4 := by
    rw [← hz]; exact Complex.abs_re_le_norm _
  have hzre : 1 / 4 ≤ z.re := by
    rw [sub_re] at hre; linarith [(abs_le.mp hre).1]
  have hzn : ‖z‖ ≤ ‖s‖ + 1 / 4 := by
    calc ‖z‖ = ‖s + (z - s)‖ := by ring_nf
      _ ≤ ‖s‖ + ‖z - s‖ := norm_add_le _ _
      _ = ‖s‖ + 1 / 4 := by rw [hz]
  calc ‖zetaReg z‖ ≤ 5 * ‖z‖ := norm_zetaReg_le hzre
    _ ≤ 5 * (‖s‖ + 1 / 4) := by linarith

/-- **`‖ζ'(s)‖ ≤ ‖s−1‖^{-2} + 20‖s‖ + 5`** on `Re s ≥ 1/2`, `s ≠ 1`. -/
theorem norm_deriv_zeta_le {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs1 : s ≠ 1) :
    ‖deriv riemannZeta s‖ ≤ (‖s - 1‖ ^ 2)⁻¹ + 20 * ‖s‖ + 5 := by
  rw [deriv_riemannZeta_eq hs1]
  calc ‖deriv zetaReg s - ((s - 1) ^ 2)⁻¹‖ ≤ ‖deriv zetaReg s‖ + ‖((s - 1) ^ 2)⁻¹‖ := norm_sub_le _ _
    _ ≤ (20 * ‖s‖ + 5) + (‖s - 1‖ ^ 2)⁻¹ := by
        rw [norm_inv, norm_pow]; linarith [norm_deriv_zetaReg_le hs]
    _ = _ := by ring

/-- `ζ'` is continuous off `s = 1`. -/
theorem continuousOn_deriv_zeta : ContinuousOn (deriv riemannZeta) {s : ℂ | s ≠ 1} := by
  have hc : Continuous (deriv zetaReg) :=
    (differentiable_zetaReg.contDiff (n := 1)).continuous_deriv le_rfl
  have h2 : ContinuousOn (fun s : ℂ => deriv zetaReg s - ((s - 1) ^ 2)⁻¹) {s : ℂ | s ≠ 1} := by
    refine hc.continuousOn.sub (ContinuousOn.inv₀ (by fun_prop) ?_)
    intro s hs
    exact pow_ne_zero 2 (sub_ne_zero.mpr hs)
  exact h2.congr (fun s hs => deriv_riemannZeta_eq hs)

lemma abscissa_one_lt {w : ℂ} (hw : 1 < w.re) : abscissaOfAbsConv (1 : ℕ → ℂ) < (w.re : EReal) := by
  rw [LSeries.abscissaOfAbsConv_one]; exact_mod_cast hw

/-- **`−ζ'(w) = Σ_{n ≥ 0} log(n+2) (n+2)^{-w}`** for `Re w > 1`. -/
theorem neg_deriv_zeta_eq_tsum {w : ℂ} (hw : 1 < w.re) :
    -deriv riemannZeta w
      = ∑' n : ℕ, (Real.log ((n : ℝ) + 2) : ℂ) * ((((n : ℝ) + 2 : ℝ)) : ℂ) ^ (-w) := by
  have h1 : deriv riemannZeta w = deriv (LSeries 1) w := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hw] with z hz
    exact (LSeries_one_eq_riemannZeta hz).symm
  rw [h1, LSeries_deriv (abscissa_one_lt hw), neg_neg]
  have hs : Summable (term (logMul 1) w) :=
    LSeriesSummable_logMul_of_lt_re (abscissa_one_lt hw)
  unfold LSeries
  rw [hs.tsum_eq_zero_add, ((summable_nat_add_iff 1).mpr hs).tsum_eq_zero_add]
  have e0 : term (logMul 1) w 0 = 0 := by simp [term]
  have e1 : term (logMul 1) w (0 + 1) = 0 := by simp [term, logMul]
  rw [e0, e1, zero_add, zero_add]
  congr 1; funext n
  have hn : (n + 1 + 1 : ℕ) ≠ 0 := by omega
  rw [term_of_ne_zero hn]
  simp only [logMul, Pi.one_apply, mul_one]
  have hc : ((n + 1 + 1 : ℕ) : ℂ) = ((((n : ℝ) + 2 : ℝ)) : ℂ) := by push_cast; ring
  rw [hc, Complex.cpow_neg, div_eq_mul_inv]
  congr 1
  rw [← Complex.ofReal_log (by positivity)]

/-- `Σ log(n+2) (n+2)^{-c}` converges for `c > 1`. -/
theorem summable_log_rpow {c : ℝ} (hc : 1 < c) :
    Summable (fun n : ℕ => Real.log ((n : ℝ) + 2) * ((n : ℝ) + 2) ^ (-c)) := by
  have hw : 1 < ((c : ℂ)).re := by simpa using hc
  have hs : Summable (term (logMul 1) (c : ℂ)) :=
    LSeriesSummable_logMul_of_lt_re (abscissa_one_lt hw)
  have hn := (summable_nat_add_iff 2).mpr (summable_norm_iff.mpr hs)
  refine hn.congr fun n => ?_
  have hn0 : (n + 2 : ℕ) ≠ 0 := by omega
  rw [term_of_ne_zero hn0]
  simp only [logMul, Pi.one_apply, mul_one, norm_div]
  rw [norm_natCast_cpow_of_pos (by omega), ← Complex.ofReal_natCast, ← Complex.ofReal_log (by positivity),
    Complex.norm_real, Real.norm_eq_abs, _root_.abs_of_nonneg (Real.log_nonneg (by norm_cast; omega)),
    Complex.ofReal_re, Real.rpow_neg (by positivity), div_eq_mul_inv]
  push_cast; ring_nf

end FleetHeadContour
