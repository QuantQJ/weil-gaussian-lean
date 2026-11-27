import FleetHeadContourShift
import FleetHeadContourLadder

/-!
# Window mean square of the Möbius polynomial ⇒ RH (conditional reduction)

**Hypothesis** `WindowMeanSquareBound`: for every `|α| ≥ 1/2` there are `C` and `k : ℕ` with
`∫_ℝ |M_{cut b}(1/2+it)|² e^{-(t−α)²/(4b)} dt ≤ C / b^k` for all `0 < b ≤ 1`,
where `M_M(w) = Σ_{m ≤ M} μ(m) m^{-w}` and `cut b = ⌊e^{1.1/b}⌋`.

**Theorem** `RH_of_window_meanSquare : WindowMeanSquareBound → RiemannHypothesis`.

Route: `head_eq_critical_line` (exact contour identity), `‖LG(−it)‖ ≤ √(π/b)(e^{-(t+α)²/4b} + e^{-(t−α)²/4b})`,
`|M||ζ'| ≤ (|M|² + |ζ'|²)/2`, the hypothesis at `α` and at `−α`, the unconditional window bound for
`|ζ'(1/2+it)|²` (`zeta_window`), a Cauchy estimate for the residue `Φ'(1)` (`norm_deriv_Phi_one_le`), so
`|head| ≤ √(π/b)·poly(1/b)`; then `head_exp_ladder` (every `e^{c/b}` loss, `c > 0`, is admissible).
This is a conditional reduction; the hypothesis is not proved here.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace FleetHeadContour

/-! ## Gaussian windows -/

lemma integrable_gauss_scale {d : ℝ} (hd : 0 < d) (β : ℝ) :
    Integrable (fun y : ℝ => Real.exp (-(y - β) ^ 2 / d)) := by
  have h := (integrable_exp_neg_mul_sq (b := 1 / d) (by positivity)).comp_sub_right β
  refine h.congr (ae_of_all _ fun y => ?_)
  simp only [Function.comp]
  congr 1; ring

lemma integral_gauss_scale {d : ℝ} (_hd : 0 < d) (β : ℝ) :
    ∫ y : ℝ, Real.exp (-(y - β) ^ 2 / d) = Real.sqrt (π * d) := by
  have h1 := integral_gaussian (1 / d)
  have h2 := integral_sub_right_eq_self (μ := (volume : Measure ℝ)) (fun y : ℝ => Real.exp (-(1 / d) * y ^ 2)) β
  have e : (fun y : ℝ => Real.exp (-(y - β) ^ 2 / d)) = fun y : ℝ => Real.exp (-(1 / d) * (y - β) ^ 2) := by
    funext y; congr 1; ring
  rw [e, h2, h1]
  congr 1; field_simp

lemma sq_gauss_le {b : ℝ} (hb : 0 < b) (u : ℝ) :
    u ^ 2 * Real.exp (-u ^ 2 / (4 * b)) ≤ 8 * b * Real.exp (-u ^ 2 / (8 * b)) := by
  set v := u ^ 2 / (8 * b) with hv
  have hv0 : 0 ≤ v := by positivity
  have e1 : u ^ 2 = 8 * b * v := by rw [hv]; field_simp
  have e2 : -u ^ 2 / (4 * b) = -v + -v := by rw [hv]; field_simp; ring
  have e3 : -u ^ 2 / (8 * b) = -v := by rw [hv]; ring
  rw [e2, e3, e1, Real.exp_add]
  have h := Real.add_one_le_exp v
  have hp := Real.exp_pos (-v)
  have hvle : v * Real.exp (-v) ≤ 1 := by
    have : Real.exp v * Real.exp (-v) = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hvle (by positivity : 0 ≤ 8 * b * Real.exp (-v))]

/-- The constant in the unconditional `ζ'` window bound. -/
def Zc (β : ℝ) : ℝ := (722 + 1600 * β ^ 2) * Real.sqrt (4 * π) + 12800 * Real.sqrt (8 * π)

lemma norm_deriv_zeta_half (t : ℝ) :
    ‖deriv riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖ ≤ 19 + 20 * |t| := by
  have h := norm_deriv_zeta_line (x := 1 / 2) (by norm_num) (by norm_num) t
  have e : (|(1 / 2 : ℝ) - 1| ^ 2)⁻¹ = 4 := by norm_num [abs_of_neg]
  rw [e, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h
  linarith

/-- **Unconditional `ζ'` window bound**: `∫ |ζ'(1/2+it)|² e^{-(t−β)²/4b} dt ≤ Zc β` for `0 < b ≤ 1`. -/
theorem zeta_window {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (β : ℝ) :
    Integrable (fun t : ℝ => ‖deriv riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2
      * Real.exp (-(t - β) ^ 2 / (4 * b))) ∧
    ∫ t : ℝ, ‖deriv riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 * Real.exp (-(t - β) ^ 2 / (4 * b))
      ≤ Zc β := by
  set g : ℝ → ℝ := fun t => (722 + 1600 * β ^ 2) * Real.exp (-(t - β) ^ 2 / (4 * b))
    + 12800 * Real.exp (-(t - β) ^ 2 / (8 * b)) with hg
  have hgi : Integrable g :=
    ((integrable_gauss_scale (by positivity) β).const_mul _).add
      ((integrable_gauss_scale (by positivity) β).const_mul _)
  have hpt : ∀ t : ℝ, ‖deriv riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2
      * Real.exp (-(t - β) ^ 2 / (4 * b)) ≤ g t := by
    intro t
    have hz := norm_deriv_zeta_half t
    have hz0 := norm_nonneg (deriv riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I))
    have hsq : ‖deriv riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2
        ≤ (722 + 1600 * β ^ 2) + 1600 * (t - β) ^ 2 := by
      have h1 : ‖deriv riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 ≤ (19 + 20 * |t|) ^ 2 :=
        pow_le_pow_left₀ hz0 hz 2
      have h2 : (19 + 20 * |t|) ^ 2 ≤ 722 + 800 * t ^ 2 := by
        nlinarith [sq_nonneg (19 - 20 * |t|), _root_.sq_abs t]
      nlinarith [sq_nonneg (t - 2 * β)]
    have hE := Real.exp_pos (-(t - β) ^ 2 / (4 * b))
    have hs := sq_gauss_le hb (t - β)
    have hE8 := Real.exp_pos (-(t - β) ^ 2 / (8 * b))
    have hb8 : 8 * b * Real.exp (-(t - β) ^ 2 / (8 * b)) ≤ 8 * Real.exp (-(t - β) ^ 2 / (8 * b)) := by
      nlinarith
    calc ‖deriv riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 * Real.exp (-(t - β) ^ 2 / (4 * b))
        ≤ ((722 + 1600 * β ^ 2) + 1600 * (t - β) ^ 2) * Real.exp (-(t - β) ^ 2 / (4 * b)) :=
          mul_le_mul_of_nonneg_right hsq hE.le
      _ = (722 + 1600 * β ^ 2) * Real.exp (-(t - β) ^ 2 / (4 * b))
          + 1600 * ((t - β) ^ 2 * Real.exp (-(t - β) ^ 2 / (4 * b))) := by ring
      _ ≤ g t := by simp only [hg]; nlinarith
  have hint : Integrable (fun t : ℝ => ‖deriv riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2
      * Real.exp (-(t - β) ^ 2 / (4 * b))) := by
    refine Integrable.mono' hgi ?_ (ae_of_all _ fun t => ?_)
    · exact (((continuous_deriv_zeta_line (x := 1 / 2) (by norm_num)).norm.pow 2).mul
        (by fun_prop)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, _root_.abs_of_nonneg (by positivity)]
      exact hpt t
  refine ⟨hint, ?_⟩
  calc ∫ t : ℝ, ‖deriv riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 * Real.exp (-(t - β) ^ 2 / (4 * b))
      ≤ ∫ t, g t := integral_mono hint hgi hpt
    _ = (722 + 1600 * β ^ 2) * Real.sqrt (π * (4 * b)) + 12800 * Real.sqrt (π * (8 * b)) := by
        simp only [hg]
        rw [integral_add ((integrable_gauss_scale (by positivity) β).const_mul _)
          ((integrable_gauss_scale (by positivity) β).const_mul _), integral_const_mul, integral_const_mul,
          integral_gauss_scale (by positivity), integral_gauss_scale (by positivity)]
    _ ≤ Zc β := by
        unfold Zc
        have h4 : Real.sqrt (π * (4 * b)) ≤ Real.sqrt (4 * π) := Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])
        have h8 : Real.sqrt (π * (8 * b)) ≤ Real.sqrt (8 * π) := Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])
        have hc : 0 ≤ 722 + 1600 * β ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h4 hc]

lemma integrable_M_window {b : ℝ} (hb : 0 < b) (M : ℕ) (β : ℝ) :
    Integrable (fun t : ℝ => ‖Mpoly M (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 * Real.exp (-(t - β) ^ 2 / (4 * b))) := by
  refine Integrable.mono' ((integrable_gauss_scale (d := 4 * b) (by positivity) β).const_mul (((M : ℝ) + 1) ^ 2))
    ?_ (ae_of_all _ fun t => ?_)
  · exact ((((differentiable_Mpoly M).continuous.comp (continuous_line (1 / 2))).norm.pow 2).mul
      (by fun_prop)).aestronglyMeasurable
  · have hM := norm_Mpoly_le M (w := ((1 / 2 : ℝ) : ℂ) + t * I) (by simp)
    rw [Real.norm_eq_abs, _root_.abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hM 2) (Real.exp_pos _).le

/-! ## The residue `Φ'(1)` -/

lemma norm_Mpoly_le_harm (M : ℕ) {σ : ℝ} (hσ : σ ≤ 1) {w : ℂ} (hw : σ ≤ w.re) :
    ‖Mpoly M w‖ ≤ (M : ℝ) ^ (1 - σ) * (1 + Real.log M) := by
  unfold Mpoly
  have hterm : ∀ m ∈ Finset.range (M + 1),
      ‖(ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-w)‖ ≤ (M : ℝ) ^ (1 - σ) * (m : ℝ)⁻¹ := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp
    have hmM : m ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm0
    rw [norm_mul, norm_natCast_cpow_of_pos hm0]
    have h1 : ‖(ArithmeticFunction.moebius m : ℂ)‖ ≤ 1 := by
      have := FleetMollifierTail.moebius_abs_le m
      rw [show (ArithmeticFunction.moebius m : ℂ) = ((ArithmeticFunction.moebius m : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs]
      exact this
    have h2 : (m : ℝ) ^ (-w).re ≤ (m : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_exponent_le hmR (by simp; linarith)
    have h3 : (m : ℝ) ^ (-σ) = (m : ℝ) ^ (1 - σ) * (m : ℝ)⁻¹ := by
      rw [show -σ = (1 - σ) + (-1) by ring, Real.rpow_add (by linarith), Real.rpow_neg_one]
    have h4 : (m : ℝ) ^ (1 - σ) ≤ (M : ℝ) ^ (1 - σ) :=
      Real.rpow_le_rpow (by linarith) (by exact_mod_cast hmM) (by linarith)
    have hp : 0 ≤ (m : ℝ) ^ (-w).re := by positivity
    calc ‖(ArithmeticFunction.moebius m : ℂ)‖ * (m : ℝ) ^ (-w).re ≤ 1 * (m : ℝ) ^ (-σ) :=
          mul_le_mul h1 h2 hp zero_le_one
      _ = (m : ℝ) ^ (1 - σ) * (m : ℝ)⁻¹ := by rw [one_mul, h3]
      _ ≤ (M : ℝ) ^ (1 - σ) * (m : ℝ)⁻¹ := mul_le_mul_of_nonneg_right h4 (by positivity)
  have hH : ∑ m ∈ Finset.range (M + 1), (m : ℝ)⁻¹ = (harmonic M : ℝ) := by
    rw [Finset.sum_range_succ']
    simp [harmonic]
  calc _ ≤ ∑ m ∈ Finset.range (M + 1), ‖(ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-w)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.range (M + 1), (M : ℝ) ^ (1 - σ) * (m : ℝ)⁻¹ := Finset.sum_le_sum hterm
    _ = (M : ℝ) ^ (1 - σ) * (harmonic M : ℝ) := by rw [← Finset.mul_sum, hH]
    _ ≤ (M : ℝ) ^ (1 - σ) * (1 + Real.log M) :=
        mul_le_mul_of_nonneg_left (harmonic_le_one_add_log M) (by positivity)

lemma exponent_le {b α x y : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (hα : 1 / 2 ≤ |α|)
    (hx : |x - 1| ≤ b) (hy : |y| ≤ b) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    (x - 1 / 2) ^ 2 / (4 * b) + -(y + σ * α) ^ 2 / (4 * b) ≤ (1 + |α|) / 2 := by
  have hα2 : 1 / 4 ≤ α ^ 2 := by rw [← _root_.sq_abs]; nlinarith [abs_nonneg α]
  have hx2 : (x - 1 / 2) ^ 2 ≤ b ^ 2 + b + 1 / 4 := by
    have h := abs_le.mp hx
    nlinarith
  have hσα : |σ * α| = |α| := by rcases hσ with rfl | rfl <;> simp
  have hyα : -(2 * (σ * α) * y) ≤ 2 * |α| * b := by
    have := abs_mul (σ * α) y
    have h1 : |σ * α * y| ≤ |α| * b := by
      rw [abs_mul, hσα]; exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)
    have h2 := neg_abs_le (σ * α * y)
    nlinarith
  have hsq : (σ * α) ^ 2 = α ^ 2 := by rcases hσ with rfl | rfl <;> ring
  have hnum : (x - 1 / 2) ^ 2 - (y + σ * α) ^ 2 ≤ 2 * b * (1 + |α|) := by
    nlinarith [sq_nonneg y]
  rw [← add_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- **Cauchy estimate for the residue**: with `M ≥ 1`,
`‖Φ'(1)‖ ≤ 2√(π/b) e^{(1+|α|)/2} M^b (1 + log M) / b` (`0 < b ≤ 1`, `|α| ≥ 1/2`). -/
theorem norm_deriv_Phi_one_le {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) {α : ℝ} (hα : 1 / 2 ≤ |α|) (M : ℕ) :
    ‖deriv (Phi b α M) 1‖ ≤
      2 * Real.sqrt (π / b) * Real.exp ((1 + |α|) / 2) * ((M : ℝ) ^ b * (1 + Real.log M)) / b := by
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := 1) (R := b) (f := Phi b α M)
    (C := 2 * Real.sqrt (π / b) * Real.exp ((1 + |α|) / 2) * ((M : ℝ) ^ b * (1 + Real.log M)))
    hb (differentiable_Phi b α M).diffContOnCl ?_
  · exact h
  intro z hz
  rw [mem_sphere_iff_norm] at hz
  have hre : |z.re - 1| ≤ b := by
    have := Complex.abs_re_le_norm (z - 1); rw [hz] at this; simpa using this
  have him : |z.im| ≤ b := by
    have := Complex.abs_im_le_norm (z - 1); rw [hz] at this; simpa using this
  have hz' : z = (z.re : ℂ) + z.im * I := (Complex.re_add_im z).symm
  have hM := norm_Mpoly_le_harm M (σ := 1 - b) (by linarith) (w := z) (by linarith [(abs_le.mp hre).1])
  rw [show 1 - (1 - b) = b by ring] at hM
  have hL := norm_LGw_le b α z.re z.im
  rw [← hz'] at hL
  have e1 := exponent_le hb hb1 hα hre him 1 (Or.inl rfl)
  have e2 := exponent_le hb hb1 hα hre him (-1) (Or.inr rfl)
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at e1 e2
  have hE : Real.exp ((z.re - 1 / 2) ^ 2 / (4 * b)) *
      (Real.exp (-(z.im + α) ^ 2 / (4 * b)) + Real.exp (-(z.im - α) ^ 2 / (4 * b)))
      ≤ 2 * Real.exp ((1 + |α|) / 2) := by
    rw [mul_add, ← Real.exp_add, ← Real.exp_add]
    linarith [Real.exp_le_exp.mpr e1, Real.exp_le_exp.mpr e2]
  have hL' : ‖LGw b α z‖ ≤ Real.sqrt (π / b) * (2 * Real.exp ((1 + |α|) / 2)) := by
    calc ‖LGw b α z‖ ≤ _ := hL
      _ = Real.sqrt (π / b) * (Real.exp ((z.re - 1 / 2) ^ 2 / (4 * b)) *
          (Real.exp (-(z.im + α) ^ 2 / (4 * b)) + Real.exp (-(z.im - α) ^ 2 / (4 * b)))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hE (Real.sqrt_nonneg _)
  unfold Phi
  rw [norm_mul]
  calc ‖LGw b α z‖ * ‖Mpoly M z‖
      ≤ (Real.sqrt (π / b) * (2 * Real.exp ((1 + |α|) / 2))) * ((M : ℝ) ^ b * (1 + Real.log M)) :=
        mul_le_mul hL' hM (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma cut_pos {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) : 1 ≤ FleetFiniteHeadRH.cut b :=
  (FleetMollifierTail.cutoff_floor_bounds b hb hb1).1

lemma cut_le {b : ℝ} : (FleetFiniteHeadRH.cut b : ℝ) ≤ Real.exp (11 / (10 * b)) :=
  Nat.floor_le (Real.exp_pos _).le

lemma cut_rpow_le {b : ℝ} (hb : 0 < b) : (FleetFiniteHeadRH.cut b : ℝ) ^ b ≤ Real.exp (11 / 10) := by
  calc (FleetFiniteHeadRH.cut b : ℝ) ^ b ≤ Real.exp (11 / (10 * b)) ^ b :=
        Real.rpow_le_rpow (by positivity) cut_le hb.le
    _ = Real.exp (11 / 10) := by
        rw [← Real.exp_mul]; congr 1; field_simp

lemma log_cut_le {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) : Real.log (FleetFiniteHeadRH.cut b) ≤ 11 / (10 * b) := by
  have h1 : (1 : ℝ) ≤ FleetFiniteHeadRH.cut b := by exact_mod_cast cut_pos hb hb1
  calc Real.log (FleetFiniteHeadRH.cut b) ≤ Real.log (Real.exp (11 / (10 * b))) :=
        Real.log_le_log (by linarith) cut_le
    _ = 11 / (10 * b) := Real.log_exp _

/-! ## The hypothesis and the conditional theorem -/

/-- **The window mean-square hypothesis.** For every `|α| ≥ 1/2` there are `C`, `k` with
`∫_ℝ |M_{cut b}(1/2+it)|² e^{-(t−α)²/(4b)} dt ≤ C / b^k` for all `0 < b ≤ 1`. -/
def WindowMeanSquareBound : Prop :=
  ∀ α : ℝ, 1 / 2 ≤ |α| → ∃ C : ℝ, ∃ k : ℕ, ∀ b : ℝ, 0 < b → b ≤ 1 →
    ∫ t : ℝ, ‖Mpoly (FleetFiniteHeadRH.cut b) (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2
      * Real.exp (-(t - α) ^ 2 / (4 * b)) ≤ C / b ^ k

/-- **Polynomial head bound under the hypothesis** (at a fixed `|α| ≥ 1/2`). -/
theorem head_le_of_window {α : ℝ} (hα : 1 / 2 ≤ |α|) {C₁ C₂ : ℝ} {k₁ k₂ : ℕ}
    (h₁ : ∀ b : ℝ, 0 < b → b ≤ 1 →
      ∫ t : ℝ, ‖Mpoly (FleetFiniteHeadRH.cut b) (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2
        * Real.exp (-(t - α) ^ 2 / (4 * b)) ≤ C₁ / b ^ k₁)
    (h₂ : ∀ b : ℝ, 0 < b → b ≤ 1 →
      ∫ t : ℝ, ‖Mpoly (FleetFiniteHeadRH.cut b) (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2
        * Real.exp (-(t - -α) ^ 2 / (4 * b)) ≤ C₂ / b ^ k₂)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    |FleetFiniteHeadRH.head b α (FleetFiniteHeadRH.cut b)| ≤ Real.sqrt (π / b) *
      (2 * Real.exp ((1 + |α|) / 2) * Real.exp (11 / 10) * ((1 / b) + (11 / 10) * (1 / b) ^ 2)
        + (|C₁| * (1 / b) ^ k₁ + |C₂| * (1 / b) ^ k₂ + 2 * Zc α) / (4 * π)) := by
  set M := FleetFiniteHeadRH.cut b with hM
  set sq := Real.sqrt (π / b) with hsq
  have hsq0 : 0 ≤ sq := Real.sqrt_nonneg _
  set u := 1 / b with hu
  have hu0 : 0 < u := by positivity
  -- the four window integrals
  set wp : ℝ → ℝ := fun t => Real.exp (-(t - -α) ^ 2 / (4 * b)) with hwp
  set wm : ℝ → ℝ := fun t => Real.exp (-(t - α) ^ 2 / (4 * b)) with hwm
  set Mn : ℝ → ℝ := fun t => ‖Mpoly M (((1 / 2 : ℝ) : ℂ) + t * I)‖ with hMn
  set Zn : ℝ → ℝ := fun t => ‖deriv riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖ with hZn
  have iMp : Integrable (fun t => Mn t ^ 2 * wp t) := integrable_M_window hb M (-α)
  have iMm : Integrable (fun t => Mn t ^ 2 * wm t) := integrable_M_window hb M α
  have hZcneg : Zc (-α) = Zc α := by unfold Zc; ring
  have iZp : Integrable (fun t => Zn t ^ 2 * wp t) := (zeta_window hb hb1 (-α)).1
  have iZm : Integrable (fun t => Zn t ^ 2 * wm t) := (zeta_window hb hb1 α).1
  have bZp : ∫ t, Zn t ^ 2 * wp t ≤ Zc α := by
    have := (zeta_window hb hb1 (-α)).2; rw [hZcneg] at this; exact this
  have bZm : ∫ t, Zn t ^ 2 * wm t ≤ Zc α := (zeta_window hb hb1 α).2
  have iM2 : Integrable (fun t => Mn t ^ 2 * wp t + Mn t ^ 2 * wm t) := iMp.add iMm
  have iZ2 : Integrable (fun t => Zn t ^ 2 * wp t + Zn t ^ 2 * wm t) := iZp.add iZm
  -- the integrand
  set F : ℝ → ℂ := fun t => LGw b α (((1 / 2 : ℝ) : ℂ) + t * I) * Mpoly M (((1 / 2 : ℝ) : ℂ) + t * I)
      * (-deriv riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)) with hF
  have hFi : Integrable F := by
    have := integrable_f_line hb α M (x := 1 / 2) (by norm_num) (by norm_num)
    simpa [Phi, hF] using this
  set G : ℝ → ℝ := fun t => (sq / 2) * ((Mn t ^ 2 * wp t + Mn t ^ 2 * wm t) + (Zn t ^ 2 * wp t + Zn t ^ 2 * wm t))
    with hG
  have hGi : Integrable G := (iM2.add iZ2).const_mul _
  have hFG : ∀ t, ‖F t‖ ≤ G t := by
    intro t
    have hL := norm_LGw_le b α (1 / 2) t
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
      Real.exp_zero, mul_one] at hL
    have hwpe : Real.exp (-(t + α) ^ 2 / (4 * b)) = wp t := by simp only [hwp, sub_neg_eq_add]
    rw [hwpe] at hL
    have hp := Real.exp_pos (-(t - -α) ^ 2 / (4 * b))
    have hm := Real.exp_pos (-(t - α) ^ 2 / (4 * b))
    have hMn0 : 0 ≤ Mn t := norm_nonneg _
    have hZn0 : 0 ≤ Zn t := norm_nonneg _
    have hamgm : Mn t * Zn t ≤ (Mn t ^ 2 + Zn t ^ 2) / 2 := by nlinarith [sq_nonneg (Mn t - Zn t)]
    simp only [hF, norm_mul, norm_neg]
    change ‖LGw b α (((1 / 2 : ℝ) : ℂ) + t * I)‖ * Mn t * Zn t ≤ G t
    calc ‖LGw b α (((1 / 2 : ℝ) : ℂ) + t * I)‖ * Mn t * Zn t
        ≤ (sq * (wp t + wm t)) * Mn t * Zn t := by
          apply mul_le_mul_of_nonneg_right _ hZn0
          apply mul_le_mul_of_nonneg_right _ hMn0
          simpa [hwm] using hL
      _ = (sq * (wp t + wm t)) * (Mn t * Zn t) := by ring
      _ ≤ (sq * (wp t + wm t)) * ((Mn t ^ 2 + Zn t ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left hamgm (by simp only [hwp, hwm]; positivity)
      _ = G t := by simp only [hG]; ring
  -- integral bound
  have hInt : ‖∫ t, F t‖ ≤ (sq / 2) * ((C₁ / b ^ k₁ + C₂ / b ^ k₂) + 2 * Zc α) := by
    calc ‖∫ t, F t‖ ≤ ∫ t, ‖F t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t, G t := integral_mono hFi.norm hGi hFG
      _ = (sq / 2) * (((∫ t, Mn t ^ 2 * wp t) + ∫ t, Mn t ^ 2 * wm t)
            + ((∫ t, Zn t ^ 2 * wp t) + ∫ t, Zn t ^ 2 * wm t)) := by
          simp only [hG]
          rw [integral_const_mul, integral_add iM2 iZ2, integral_add iMp iMm,
            integral_add iZp iZm]
      _ ≤ (sq / 2) * ((C₂ / b ^ k₂ + C₁ / b ^ k₁) + (Zc α + Zc α)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have a1 := h₂ b hb hb1
          have a2 := h₁ b hb hb1
          exact add_le_add (add_le_add a1 a2) (add_le_add bZp bZm)
      _ = (sq / 2) * ((C₁ / b ^ k₁ + C₂ / b ^ k₂) + 2 * Zc α) := by ring
  -- residue bound
  have hR := norm_deriv_Phi_one_le hb hb1 hα M
  have hMb := cut_rpow_le hb
  have hlog := log_cut_le hb hb1
  have hlog0 : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast cut_pos hb hb1)
  have hR' : ‖deriv (Phi b α M) 1‖ ≤ sq * (2 * Real.exp ((1 + |α|) / 2) * Real.exp (11 / 10) * (u + (11 / 10) * u ^ 2)) := by
    refine hR.trans ?_
    have h1 : (M : ℝ) ^ b * (1 + Real.log M) ≤ Real.exp (11 / 10) * (1 + 11 / (10 * b)) :=
      mul_le_mul hMb (by linarith) (by positivity) (Real.exp_pos _).le
    have e : u + (11 / 10) * u ^ 2 = (1 + 11 / (10 * b)) / b := by rw [hu]; field_simp
    rw [e]
    have hk : 0 ≤ 2 * Real.sqrt (π / b) * Real.exp ((1 + |α|) / 2) := by positivity
    calc 2 * Real.sqrt (π / b) * Real.exp ((1 + |α|) / 2) * ((M : ℝ) ^ b * (1 + Real.log M)) / b
        ≤ 2 * Real.sqrt (π / b) * Real.exp ((1 + |α|) / 2) * (Real.exp (11 / 10) * (1 + 11 / (10 * b))) / b :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hk) hb.le
      _ = _ := by rw [hsq]; ring
  -- assemble
  have hid := head_eq_critical_line hb α M
  have hhead : |FleetFiniteHeadRH.head b α M| ≤ ‖deriv (Phi b α M) 1‖ + (1 / (2 * π)) * ‖∫ t, F t‖ := by
    have : ‖((FleetFiniteHeadRH.head b α M : ℝ) : ℂ)‖ = |FleetFiniteHeadRH.head b α M| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [← this, hid]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_mul]
    congr 2
    rw [show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hC1 : C₁ / b ^ k₁ ≤ |C₁| * u ^ k₁ := by
    rw [hu, one_div_pow, ← div_eq_mul_one_div]
    exact div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
  have hC2 : C₂ / b ^ k₂ ≤ |C₂| * u ^ k₂ := by
    rw [hu, one_div_pow, ← div_eq_mul_one_div]
    exact div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
  have hpi : 0 < 2 * π := by positivity
  have hInt' : (1 / (2 * π)) * ‖∫ t, F t‖ ≤ sq * ((|C₁| * u ^ k₁ + |C₂| * u ^ k₂ + 2 * Zc α) / (4 * π)) := by
    calc (1 / (2 * π)) * ‖∫ t, F t‖ ≤ (1 / (2 * π)) * ((sq / 2) * ((C₁ / b ^ k₁ + C₂ / b ^ k₂) + 2 * Zc α)) :=
          mul_le_mul_of_nonneg_left hInt (by positivity)
      _ ≤ (1 / (2 * π)) * ((sq / 2) * ((|C₁| * u ^ k₁ + |C₂| * u ^ k₂) + 2 * Zc α)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
      _ = _ := by ring
  calc |FleetFiniteHeadRH.head b α M| ≤ ‖deriv (Phi b α M) 1‖ + (1 / (2 * π)) * ‖∫ t, F t‖ := hhead
    _ ≤ sq * (2 * Real.exp ((1 + |α|) / 2) * Real.exp (11 / 10) * (u + (11 / 10) * u ^ 2))
        + sq * ((|C₁| * u ^ k₁ + |C₂| * u ^ k₂ + 2 * Zc α) / (4 * π)) := add_le_add hR' hInt'
    _ = _ := by ring

/-- **Conditional reduction: the window mean-square bound for the Möbius polynomial implies RH.** -/
theorem RH_of_window_meanSquare (h : WindowMeanSquareBound) : RiemannHypothesis := by
  apply head_exp_ladder
  intro c hc α hα
  obtain ⟨C₁, k₁, h₁⟩ := h α hα
  obtain ⟨C₂, k₂, h₂⟩ := h (-α) (by rwa [abs_neg])
  set A := 2 * Real.exp ((1 + |α|) / 2) * Real.exp (11 / 10) with hA
  have hA0 : 0 ≤ A := by positivity
  have hZ0 : 0 ≤ Zc α := by unfold Zc; positivity
  refine ⟨A * ((Nat.factorial 1 / c ^ 1) + (11 / 10) * (Nat.factorial 2 / c ^ 2))
    + (|C₁| * (Nat.factorial k₁ / c ^ k₁) + |C₂| * (Nat.factorial k₂ / c ^ k₂) + 2 * Zc α) / (4 * π),
    fun b hb hb1 => ?_⟩
  have hmain := head_le_of_window hα h₁ h₂ hb hb1
  set u := 1 / b with hu
  have hu0 : 0 ≤ u := by positivity
  have hcu : c / b = c * u := by rw [hu]; ring
  rw [hcu]
  set E := Real.exp (c * u) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  have p1 := pow_le_exp 1 hc hu0
  have p2 := pow_le_exp 2 hc hu0
  have q1 := pow_le_exp k₁ hc hu0
  have q2 := pow_le_exp k₂ hc hu0
  rw [pow_one] at p1
  refine hmain.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
  have hpi : 0 < 4 * π := by positivity
  rw [← hE] at p1 p2 q1 q2
  have t1 : A * (u + (11 / 10) * u ^ 2) ≤ A * ((Nat.factorial 1 / c ^ 1) + (11 / 10) * (Nat.factorial 2 / c ^ 2)) * E := by
    have hh : u + (11 / 10) * u ^ 2 ≤ ((Nat.factorial 1 / c ^ 1) + (11 / 10) * (Nat.factorial 2 / c ^ 2)) * E := by
      nlinarith
    calc A * (u + (11 / 10) * u ^ 2) ≤ A * (((Nat.factorial 1 / c ^ 1) + (11 / 10) * (Nat.factorial 2 / c ^ 2)) * E) :=
          mul_le_mul_of_nonneg_left hh hA0
      _ = _ := by ring
  have t2 : (|C₁| * u ^ k₁ + |C₂| * u ^ k₂ + 2 * Zc α) / (4 * π)
      ≤ (|C₁| * (Nat.factorial k₁ / c ^ k₁) + |C₂| * (Nat.factorial k₂ / c ^ k₂) + 2 * Zc α) / (4 * π) * E := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hpi.le
    have r1 := mul_le_mul_of_nonneg_left q1 (abs_nonneg C₁)
    have r2 := mul_le_mul_of_nonneg_left q2 (abs_nonneg C₂)
    have r3 : 2 * Zc α ≤ 2 * Zc α * E := le_mul_of_one_le_right (by positivity) hE1
    nlinarith
  calc A * (u + (11 / 10) * u ^ 2) + (|C₁| * u ^ k₁ + |C₂| * u ^ k₂ + 2 * Zc α) / (4 * π)
      ≤ A * ((Nat.factorial 1 / c ^ 1) + (11 / 10) * (Nat.factorial 2 / c ^ 2)) * E
        + (|C₁| * (Nat.factorial k₁ / c ^ k₁) + |C₂| * (Nat.factorial k₂ / c ^ k₂) + 2 * Zc α) / (4 * π) * E :=
        add_le_add t1 t2
    _ = _ := by ring

end FleetHeadContour
