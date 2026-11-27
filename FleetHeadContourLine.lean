import FleetHeadContourZeta
import FleetHeadContourGauss
import FleetFiniteHeadRH

/-!
# The Möbius head as a vertical-line integral at `Re w = c > 1`

With `Φ(w) = LGw b α w · Mpoly M w` (entire):

* `inner_eq_line_integral`: for `m ≥ 1`, `c > 1`,
  `inner b α m = (1/2π) ∫_ℝ LGw(c+it) m^{-(c+it)} (−ζ'(c+it)) dt`.
* `head_eq_line_integral`: for `c > 1`,
  `head b α M = (1/2π) ∫_ℝ Φ(c+it) (−ζ'(c+it)) dt`.

Also `norm_deriv_zeta_line` (`ζ'` on a line `Re = x`, `x ≥ 1/2`, `x ≠ 1`) and `integrable_line`.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace FleetHeadContour

/-- `Φ(w) = LG(1/2 − w) · M_M(w)`. -/
def Phi (b α : ℝ) (M : ℕ) (w : ℂ) : ℂ := LGw b α w * Mpoly M w

theorem differentiable_Phi (b α : ℝ) (M : ℕ) : Differentiable ℂ (Phi b α M) :=
  (differentiable_LGw b α).mul (differentiable_Mpoly M)

/-- `ζ'` on the line `Re = x` (`x ≥ 1/2`, `x ≠ 1`). -/
theorem norm_deriv_zeta_line {x : ℝ} (hx : 1 / 2 ≤ x) (hx1 : x ≠ 1) (t : ℝ) :
    ‖deriv riemannZeta ((x : ℂ) + t * I)‖ ≤ (|x - 1| ^ 2)⁻¹ + 20 * (|x| + |t|) + 5 := by
  have hre : ((x : ℂ) + t * I).re = x := by simp
  have hne : (x : ℂ) + t * I ≠ 1 := by
    intro h; apply hx1; have := congrArg Complex.re h; simpa using this
  have h := norm_deriv_zeta_le (by rw [hre]; exact hx) hne
  have h1 : |x - 1| ≤ ‖(x : ℂ) + t * I - 1‖ := by
    have := Complex.abs_re_le_norm ((x : ℂ) + t * I - 1)
    simpa using this
  have hx0 : 0 < |x - 1| := abs_pos.mpr (sub_ne_zero.mpr hx1)
  have h2 : (‖(x : ℂ) + t * I - 1‖ ^ 2)⁻¹ ≤ (|x - 1| ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ hx0.le h1 2)
  have h3 : ‖(x : ℂ) + t * I‖ ≤ |x| + |t| := by
    calc ‖(x : ℂ) + t * I‖ ≤ ‖(x : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = |x| + |t| := by simp
  linarith

lemma line_ne_one {x : ℝ} (hx1 : x ≠ 1) (t : ℝ) : (x : ℂ) + t * I ≠ 1 := by
  intro h; apply hx1; have := congrArg Complex.re h; simpa using this

lemma continuous_line (x : ℝ) : Continuous (fun t : ℝ => (x : ℂ) + t * I) := by fun_prop

lemma continuous_deriv_zeta_line {x : ℝ} (hx1 : x ≠ 1) :
    Continuous (fun t : ℝ => deriv riemannZeta ((x : ℂ) + t * I)) :=
  continuousOn_deriv_zeta.comp_continuous (continuous_line x) (fun t => line_ne_one hx1 t)

/-- **Integrability on a vertical line** of `LGw · h · (−ζ')` for bounded continuous `h`. -/
theorem integrable_line {b : ℝ} (hb : 0 < b) (α : ℝ) {x : ℝ} (hx : 1 / 2 ≤ x) (hx1 : x ≠ 1)
    {h : ℝ → ℂ} (hh : Continuous h) {H : ℝ} (hH : ∀ t, ‖h t‖ ≤ H) :
    Integrable (fun t : ℝ => LGw b α ((x : ℂ) + t * I) * h t * (-deriv riemannZeta ((x : ℂ) + t * I))) := by
  have hH0 : 0 ≤ H := (norm_nonneg _).trans (hH 0)
  set K := Real.sqrt (π / b) * Real.exp ((x - 1 / 2) ^ 2 / (4 * b)) with hK
  have hK0 : 0 ≤ K := by positivity
  set A := (|x - 1| ^ 2)⁻¹ + 20 * |x| + 5 with hA
  refine integrable_of_gauss_bound hb α (K * H * A) (K * H * 20) ?_ (fun t => ?_)
  · exact (((differentiable_LGw b α).continuous.comp (continuous_line x)).mul hh).mul
      (continuous_deriv_zeta_line hx1).neg
  · have h1 := norm_LGw_le b α x t
    have h2 := hH t
    have h3 := norm_deriv_zeta_line hx hx1 t
    have hE : 0 ≤ Real.exp (-(t + α) ^ 2 / (4 * b)) + Real.exp (-(t - α) ^ 2 / (4 * b)) := by positivity
    rw [norm_mul, norm_mul, norm_neg]
    calc ‖LGw b α ((x : ℂ) + t * I)‖ * ‖h t‖ * ‖deriv riemannZeta ((x : ℂ) + t * I)‖
        ≤ (K * (Real.exp (-(t + α) ^ 2 / (4 * b)) + Real.exp (-(t - α) ^ 2 / (4 * b)))) * H
          * ((|x - 1| ^ 2)⁻¹ + 20 * (|x| + |t|) + 5) := by
          gcongr
    _ = (K * H * A + K * H * 20 * |t|) *
          (Real.exp (-(t + α) ^ 2 / (4 * b)) + Real.exp (-(t - α) ^ 2 / (4 * b))) := by
          rw [hA]; ring

lemma integrable_LGw_line {b : ℝ} (hb : 0 < b) (α c : ℝ) :
    Integrable (fun t : ℝ => LGw b α ((c : ℂ) + t * I)) := by
  have h := integrable_LGw_cpow hb α c (x := 1) one_pos
  simpa using h

lemma norm_ofReal_cpow_line {x : ℝ} (hx : 0 < x) (c t : ℝ) :
    ‖(x : ℂ) ^ (-((c : ℂ) + t * I))‖ = x ^ (-c) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- **`inner b α m` as a line integral** at `Re w = c > 1`. -/
theorem inner_eq_line_integral {b : ℝ} (hb : 0 < b) (α : ℝ) {m : ℕ} (hm : 1 ≤ m) {c : ℝ} (hc : 1 < c) :
    ((FleetMollifierTail.inner b α m : ℝ) : ℂ) = (1 / (2 * π) : ℂ) *
      ∫ t : ℝ, LGw b α ((c : ℂ) + t * I) * (m : ℂ) ^ (-((c : ℂ) + t * I))
        * (-deriv riemannZeta ((c : ℂ) + t * I)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set x : ℕ → ℝ := fun n => (m : ℝ) * ((n : ℝ) + 2) with hx
  have hxpos : ∀ n, 0 < x n := fun n => by simp only [hx]; positivity
  set F : ℕ → ℝ → ℂ := fun n t => (Real.log ((n : ℝ) + 2) : ℂ) *
    (LGw b α ((c : ℂ) + t * I) * ((x n : ℝ) : ℂ) ^ (-((c : ℂ) + t * I))) with hF
  have hFint : ∀ n, Integrable (F n) := fun n => (integrable_LGw_cpow hb α c (hxpos n)).const_mul _
  have hFnorm : ∀ n t, ‖F n t‖ = (Real.log ((n : ℝ) + 2) * x n ^ (-c)) * ‖LGw b α ((c : ℂ) + t * I)‖ := by
    intro n t
    simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      _root_.abs_of_nonneg (Real.log_nonneg (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)] : (1 : ℝ) ≤ n + 2)),
      norm_ofReal_cpow_line (hxpos n)]
    ring
  set KL := ∫ t : ℝ, ‖LGw b α ((c : ℂ) + t * I)‖ with hKL
  have hFsum : Summable fun n => ∫ t, ‖F n t‖ := by
    have e : (fun n => ∫ t, ‖F n t‖)
        = fun n : ℕ => ((m : ℝ) ^ (-c) * KL) * (Real.log ((n : ℝ) + 2) * ((n : ℝ) + 2) ^ (-c)) := by
      funext n
      simp_rw [hFnorm n]
      rw [integral_const_mul]
      simp only [hx]
      rw [Real.mul_rpow hmR.le (by positivity)]
      ring
    rw [e]
    exact (summable_log_rpow hc).mul_left _
  -- the kernel step
  have hterm : ∀ n : ℕ, ((Real.log ((n : ℝ) + 2) * FleetMollifierTail.kernel b α ((m : ℝ) * ((n : ℝ) + 2)) : ℝ) : ℂ)
      = (1 / (2 * π) : ℂ) * ∫ t, F n t := by
    intro n
    rw [Complex.ofReal_mul, kernel_eq_integral hb α c (hxpos n)]
    simp only [hF]
    rw [integral_const_mul]
    ring
  unfold FleetMollifierTail.inner
  rw [Complex.ofReal_tsum, tsum_congr hterm, tsum_mul_left,
    integral_tsum_of_summable_integral_norm hFint hFsum]
  congr 1
  congr 1
  funext t
  have hw : 1 < ((c : ℂ) + t * I).re := by simpa using hc
  rw [neg_deriv_zeta_eq_tsum hw, ← tsum_mul_left]
  congr 1
  funext n
  simp only [hF, hx]
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hmR.le (by positivity)]
  push_cast
  ring

lemma moebius_zero_complex : (ArithmeticFunction.moebius 0 : ℂ) = 0 := by simp

/-- **The head as a line integral at `Re w = c > 1`.** -/
theorem head_eq_line_integral {b : ℝ} (hb : 0 < b) (α : ℝ) (M : ℕ) {c : ℝ} (hc : 1 < c) :
    ((FleetFiniteHeadRH.head b α M : ℝ) : ℂ) = (1 / (2 * π) : ℂ) *
      ∫ t : ℝ, Phi b α M ((c : ℂ) + t * I) * (-deriv riemannZeta ((c : ℂ) + t * I)) := by
  set G : ℕ → ℝ → ℂ := fun m t => LGw b α ((c : ℂ) + t * I) * (m : ℂ) ^ (-((c : ℂ) + t * I))
        * (-deriv riemannZeta ((c : ℂ) + t * I)) with hG
  have hGint : ∀ m : ℕ, 1 ≤ m → Integrable (G m) := by
    intro m hm
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    refine integrable_line hb α (x := c) (by linarith) hc.ne' (h := fun t => (m : ℂ) ^ (-((c : ℂ) + t * I)))
      ?_ (H := (m : ℝ) ^ (-c)) ?_
    · have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hmR.ne'
      exact (continuous_line c).neg.const_cpow (Or.inl hm0)
    · intro t
      have := norm_ofReal_cpow_line hmR c t
      rw [show ((m : ℝ) : ℂ) = (m : ℂ) by push_cast; rfl] at this
      exact this.le
  have hstep : ∀ m ∈ Finset.range (M + 1),
      (((ArithmeticFunction.moebius m : ℝ) * FleetMollifierTail.inner b α m : ℝ) : ℂ)
        = (1 / (2 * π) : ℂ) * ∫ t, (ArithmeticFunction.moebius m : ℂ) * G m t := by
    intro m _
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    rw [Complex.ofReal_mul, inner_eq_line_integral hb α hm hc, integral_const_mul]
    push_cast
    ring
  unfold FleetFiniteHeadRH.head
  rw [Complex.ofReal_sum, Finset.sum_congr rfl hstep, ← Finset.mul_sum, ← integral_finset_sum]
  · congr 1
    congr 1
    funext t
    simp only [hG, Phi, Mpoly, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  · intro m _
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    exact (hGint m hm).const_mul _

end FleetHeadContour
