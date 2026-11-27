import Mathlib
import FleetHeadContourGauss

/-!
# The smooth Möbius sum `P_b(s) = Σ μ(n) n^{-s} e^{-b log² n}` and its Gaussian window

The sharp window of `FleetHeadContourConverse` uses `M_N(s) = Σ_{n ≤ N} μ(n) n^{-s}` with `N = ⌊e^{1.1/b}⌋`.
Here the cutoff is the Gaussian weight `e^{-b log² n}`, with the same `b` as the window Gaussian.

* `Psm b s = Σ_n μ(n) n^{-s} e^{-b log² n}`: entire (`differentiable_Psm`).
* `norm_Psm_le`: for every `η > 0`, `‖P_b(s)‖ ≤ S_η e^{m²/(4b)}`, `m = max 0 (1 + η − Re s)`,
  `S_η = Σ n^{-(1+η)}` (no hypothesis).
* `smoothWindow b α = ∫ ‖P_b(1/2+it)‖² e^{-(t−α)²/(4b)} dt`,
  `SmoothWindowRate c`: `smoothWindow b α ≤ C e^{c/b}` for `0 < b ≤ 1`, at every real `α` (`C` may depend on `α`).
* `smoothWindowRate_one_eighth`: `SmoothWindowRate (1/8 + ε)` for every `ε > 0`, unconditionally, with `C`
  independent of `α`.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace FleetSmoothWindow

/-- The smooth Möbius sum `P_b(s) = Σ_n μ(n) n^{-s} e^{-b log² n}` (the `n = 0` term is `0`). -/
def Psm (b : ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s) * (Real.exp (-b * Real.log n ^ 2) : ℂ)

/-- `S_η = Σ_n n^{-(1+η)}`. -/
def Sz (η : ℝ) : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-(1 + η))

/-- The window `∫ ‖P_b(1/2+it)‖² e^{-(t−α)²/(4b)} dt`. -/
def smoothWindow (b α : ℝ) : ℝ :=
  ∫ t : ℝ, ‖Psm b (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 * Real.exp (-(t - α) ^ 2 / (4 * b))

/-- **Smooth window rate `c`**: at every real centre `α` there is `C` with `smoothWindow b α ≤ C e^{c/b}`
for all `0 < b ≤ 1`. -/
def SmoothWindowRate (c : ℝ) : Prop :=
  ∀ α : ℝ, ∃ C : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 → smoothWindow b α ≤ C * Real.exp (c / b)

lemma summable_rpow_neg {η : ℝ} (hη : 0 < η) : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 + η))) :=
  Real.summable_nat_rpow.mpr (by linarith)

lemma Sz_nonneg (η : ℝ) : 0 ≤ Sz η :=
  tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _

/-- `n^{-σ} e^{-b log² n} ≤ n^{-(1+η)} e^{m²/(4b)}`, `m = max 0 (1+η−σ)`. -/
lemma rpow_mul_exp_le {b : ℝ} (hb : 0 < b) (σ η : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ (-σ) * Real.exp (-b * Real.log n ^ 2)
      ≤ (n : ℝ) ^ (-(1 + η)) * Real.exp (max 0 (1 + η - σ) ^ 2 / (4 * b)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  rw [Real.rpow_def_of_pos hn0, Real.rpow_def_of_pos hn0, ← Real.exp_add, ← Real.exp_add,
    Real.exp_le_exp]
  set L := Real.log n
  set m := max 0 (1 + η - σ)
  have hm : 1 + η - σ ≤ m := le_max_right _ _
  have hm0 : 0 ≤ m := le_max_left _ _
  have h1 : (1 + η - σ) * L ≤ m * L := mul_le_mul_of_nonneg_right hm hL
  have h2 : m * L - b * L ^ 2 ≤ m ^ 2 / (4 * b) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (m - 2 * b * L)]
  nlinarith

/-- The norm of the `n`-th term. -/
lemma norm_term_le {b : ℝ} (hb : 0 < b) {η : ℝ} (s : ℂ) (n : ℕ) :
    ‖(ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s) * (Real.exp (-b * Real.log n ^ 2) : ℂ)‖
      ≤ (n : ℝ) ^ (-(1 + η)) * Real.exp (max 0 (1 + η - s.re) ^ 2 / (4 * b)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [ArithmeticFunction.map_zero, Int.cast_zero, zero_mul, norm_zero]
    positivity
  rw [norm_mul, norm_mul, norm_natCast_cpow_of_pos hn, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have hμ : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    rw [show (ArithmeticFunction.moebius n : ℂ) = ((ArithmeticFunction.moebius n : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have h := rpow_mul_exp_le hb s.re η hn
  simp only [neg_re] at *
  calc ‖(ArithmeticFunction.moebius n : ℂ)‖ * (n : ℝ) ^ (-s.re) * Real.exp (-b * Real.log n ^ 2)
      ≤ 1 * (n : ℝ) ^ (-s.re) * Real.exp (-b * Real.log n ^ 2) := by gcongr
    _ ≤ _ := by rw [one_mul]; exact h

lemma summable_term {b : ℝ} (hb : 0 < b) (s : ℂ) :
    Summable (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s)
      * (Real.exp (-b * Real.log n ^ 2) : ℂ)) :=
  Summable.of_norm_bounded ((summable_rpow_neg (η := 1) one_pos).mul_right _)
    (fun n => norm_term_le hb (η := 1) s n)

/-- **`‖P_b(s)‖ ≤ S_η e^{m²/(4b)}`**, `m = max 0 (1 + η − Re s)`, for every `η > 0`. -/
theorem norm_Psm_le {b : ℝ} (hb : 0 < b) {η : ℝ} (hη : 0 < η) (s : ℂ) :
    ‖Psm b s‖ ≤ Sz η * Real.exp (max 0 (1 + η - s.re) ^ 2 / (4 * b)) := by
  unfold Psm Sz
  rw [← tsum_mul_right]
  exact tsum_of_norm_bounded ((summable_rpow_neg hη).mul_right _).hasSum
    (fun n => norm_term_le hb s n)

lemma term_eq (b : ℝ) (n : ℕ) :
    (fun w : ℂ => (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-w) * (Real.exp (-b * Real.log n ^ 2) : ℂ))
      = fun w : ℂ => if n = 0 then 0 else
          (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-w) * (Real.exp (-b * Real.log n ^ 2) : ℂ) := by
  funext w
  split_ifs with h
  · subst h; simp
  · rfl

lemma differentiable_term (b : ℝ) (n : ℕ) :
    Differentiable ℂ (fun w : ℂ => (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-w)
      * (Real.exp (-b * Real.log n ^ 2) : ℂ)) := by
  rw [term_eq b n]
  split_ifs with h
  · exact differentiable_const _
  · have hm : (n : ℂ) ≠ 0 := by exact_mod_cast h
    exact ((differentiable_const _).mul
      (fun w => (differentiableAt_neg_iff.mpr differentiableAt_id).const_cpow (Or.inl hm))).mul
      (differentiable_const _)

/-- **`P_b` is entire.** -/
theorem differentiable_Psm {b : ℝ} (hb : 0 < b) : Differentiable ℂ (Psm b) := by
  intro s
  set σ₀ := s.re - 1
  set U : Set ℂ := {w : ℂ | σ₀ < w.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hsU : s ∈ U := by show σ₀ < s.re; simp only [σ₀]; linarith
  have hD : DifferentiableOn ℂ (Psm b) U := by
    refine differentiableOn_tsum_of_summable_norm
      ((summable_rpow_neg (η := 1) one_pos).mul_right (Real.exp (max 0 (1 + 1 - σ₀) ^ 2 / (4 * b))))
      (fun n => (differentiable_term b n).differentiableOn) hU (fun n w hw => ?_)
    refine (norm_term_le hb (η := 1) w n).trans ?_
    have hmax : max 0 (1 + 1 - w.re) ≤ max 0 (1 + 1 - σ₀) :=
      max_le_max le_rfl (by have : σ₀ < w.re := hw; linarith)
    have h0 : 0 ≤ max 0 (1 + 1 - w.re) := le_max_left _ _
    gcongr
  exact hD.differentiableAt (hU.mem_nhds hsU)

theorem continuous_Psm {b : ℝ} (hb : 0 < b) : Continuous (Psm b) := (differentiable_Psm hb).continuous

/-- On the critical line: `‖P_b(1/2+it)‖ ≤ S_η e^{(1/2+η)²/(4b)}`. -/
theorem norm_Psm_half_le {b : ℝ} (hb : 0 < b) {η : ℝ} (hη : 0 < η) (t : ℝ) :
    ‖Psm b (((1 / 2 : ℝ) : ℂ) + t * I)‖ ≤ Sz η * Real.exp ((1 / 2 + η) ^ 2 / (4 * b)) := by
  have h := norm_Psm_le hb hη (((1 / 2 : ℝ) : ℂ) + t * I)
  have hre : (((1 / 2 : ℝ) : ℂ) + t * I).re = 1 / 2 := by simp
  rw [hre, show (1 + η - 1 / 2 : ℝ) = 1 / 2 + η by ring, max_eq_right (by linarith)] at h
  exact h

/-! ## Gaussian integrals -/

lemma integral_gauss_shift {b : ℝ} (hb : 0 < b) (β : ℝ) :
    ∫ y : ℝ, Real.exp (-(y - β) ^ 2 / (4 * b)) = Real.sqrt (4 * π * b) := by
  have h := integral_gaussian (1 / (4 * b))
  have e : (fun y : ℝ => Real.exp (-(y - β) ^ 2 / (4 * b)))
      = fun y : ℝ => (fun x : ℝ => Real.exp (-(1 / (4 * b)) * x ^ 2)) (y - β) := by
    funext y; congr 1; ring
  rw [e, integral_sub_right_eq_self (fun x : ℝ => Real.exp (-(1 / (4 * b)) * x ^ 2)) β, h]
  congr 1; field_simp

/-- **Integrability of the window integrand.** -/
theorem integrable_window {b : ℝ} (hb : 0 < b) (α : ℝ) :
    Integrable (fun t : ℝ => ‖Psm b (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 * Real.exp (-(t - α) ^ 2 / (4 * b))) := by
  set K := Sz 1 * Real.exp ((1 / 2 + 1) ^ 2 / (4 * b))
  refine Integrable.mono' ((FleetHeadContour.integrable_gauss_shift hb α).const_mul (K ^ 2)) ?_
    (ae_of_all _ fun t => ?_)
  · exact (((continuous_Psm hb).comp (by fun_prop)).norm.pow 2).mul (by fun_prop) |>.aestronglyMeasurable
  · have h := norm_Psm_half_le hb one_pos t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr

/-- **The unconditional bound**: `smoothWindow b α ≤ S_η² √(4πb) e^{(1/2+η)²/(2b)}`. -/
theorem smoothWindow_le {b : ℝ} (hb : 0 < b) {η : ℝ} (hη : 0 < η) (α : ℝ) :
    smoothWindow b α ≤ Sz η ^ 2 * Real.sqrt (4 * π * b) * Real.exp ((1 / 2 + η) ^ 2 / (2 * b)) := by
  set K := Sz η * Real.exp ((1 / 2 + η) ^ 2 / (4 * b))
  have hK : K ^ 2 = Sz η ^ 2 * Real.exp ((1 / 2 + η) ^ 2 / (2 * b)) := by
    simp only [K]; rw [mul_pow, ← Real.exp_nat_mul]; congr 2; field_simp; ring
  unfold smoothWindow
  calc ∫ t : ℝ, ‖Psm b (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 * Real.exp (-(t - α) ^ 2 / (4 * b))
      ≤ ∫ t : ℝ, K ^ 2 * Real.exp (-(t - α) ^ 2 / (4 * b)) := by
        refine integral_mono (integrable_window hb α)
          ((FleetHeadContour.integrable_gauss_shift hb α).const_mul _) (fun t => ?_)
        have h := norm_Psm_half_le hb hη t
        gcongr
    _ = K ^ 2 * Real.sqrt (4 * π * b) := by rw [integral_const_mul, integral_gauss_shift hb]
    _ = _ := by rw [hK]; ring

/-- **Unconditional smooth rate `1/8`**: `SmoothWindowRate (1/8 + ε)` for every `ε > 0`, with a constant
independent of `α`. -/
theorem smoothWindowRate_one_eighth {ε : ℝ} (hε : 0 < ε) : SmoothWindowRate (1 / 8 + ε) := by
  set η := min ε 1
  have hη : 0 < η := lt_min hε one_pos
  have hη1 : η ≤ 1 := min_le_right _ _
  have hηε : η ≤ ε := min_le_left _ _
  intro α
  refine ⟨Sz η ^ 2 * Real.sqrt (4 * π), fun b hb hb1 => ?_⟩
  refine (smoothWindow_le hb hη α).trans ?_
  have h1 : Real.sqrt (4 * π * b) ≤ Real.sqrt (4 * π) :=
    Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])
  have h2 : Real.exp ((1 / 2 + η) ^ 2 / (2 * b)) ≤ Real.exp ((1 / 8 + ε) / b) := by
    rw [Real.exp_le_exp, div_le_div_iff₀ (by positivity) hb]
    have hq : (1 / 2 + η) ^ 2 ≤ (1 / 8 + ε) * 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hq hb.le]
  have := Sz_nonneg η
  calc Sz η ^ 2 * Real.sqrt (4 * π * b) * Real.exp ((1 / 2 + η) ^ 2 / (2 * b))
      ≤ Sz η ^ 2 * Real.sqrt (4 * π) * Real.exp ((1 / 8 + ε) / b) := by gcongr
    _ = _ := rfl

end FleetSmoothWindow
