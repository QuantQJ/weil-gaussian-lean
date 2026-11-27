import Mathlib
import FleetMollifierTail

/-!
# The Gaussian factor `LG(1/2 − w)` and Mellin inversion of `FleetMollifierTail.kernel`

`G(u) = 2 e^{-b u²} cos(α u)`, `LG(s) = ∫ G(u) e^{-s u} du = √(π/b)[e^{(iα−s)²/4b} + e^{(−iα−s)²/4b}]`.
Here `LGw b α w = LG(1/2 − w)` (entire in `w`).

* `kernel_eq_integral`: for `x > 0` and every real `c`,
  `kernel b α x = (1/2π) ∫_ℝ LGw(c + it) x^{-(c+it)} dt`   (Mellin inversion; exact Gaussian integral).
* `norm_LGw_le`: `‖LGw(x+iy)‖ ≤ √(π/b) e^{(x−1/2)²/4b} (e^{-(y+α)²/4b} + e^{-(y−α)²/4b})`.
* `integrable_of_gauss_bound`: a continuous `g` with `‖g y‖ ≤ (P + Q|y|)(e^{-(y+α)²/4b} + e^{-(y−α)²/4b})`
  is integrable.
* `Mpoly M w = Σ_{m ≤ M} μ(m) m^{-w}`: entire, `‖Mpoly M w‖ ≤ M + 1` on `Re w ≥ 0`.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace FleetHeadContour

/-- `LG(1/2 − w) = √(π/b) [e^{(w − 1/2 + iα)²/4b} + e^{(w − 1/2 − iα)²/4b}]`. -/
def LGw (b α : ℝ) (w : ℂ) : ℂ :=
  (Real.sqrt (π / b) : ℂ) * (cexp ((w - 1 / 2 + I * α) ^ 2 / (4 * b))
    + cexp ((w - 1 / 2 - I * α) ^ 2 / (4 * b)))

theorem differentiable_LGw (b α : ℝ) : Differentiable ℂ (LGw b α) := by
  unfold LGw; fun_prop

/-- The quadratic exponent. -/
lemma quad_exp {b : ℝ} (hb : 0 < b) (z : ℂ) (c L t : ℝ) :
    cexp ((z + t * I) ^ 2 / (4 * b)) * cexp (-((c : ℂ) + t * I) * L)
      = cexp ((-1 / (4 * b) : ℂ) * (t : ℂ) ^ 2 + (I * (z / (2 * b) - L)) * t
          + (z ^ 2 / (4 * b) - c * L)) := by
  rw [← Complex.exp_add]
  congr 1
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

lemma re_neg_quarter {b : ℝ} (hb : 0 < b) : ((-1 / (4 * b) : ℂ)).re < 0 := by
  have : ((-1 / (4 * b) : ℂ)) = ((-1 / (4 * b) : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.ofReal_re]
  apply div_neg_of_neg_of_pos (by norm_num) (by positivity)

lemma integrable_quad {b : ℝ} (hb : 0 < b) (z : ℂ) (c L : ℝ) :
    Integrable (fun t : ℝ => cexp ((z + t * I) ^ 2 / (4 * b)) * cexp (-((c : ℂ) + t * I) * L)) := by
  simp_rw [quad_exp hb]
  exact integrable_cexp_quadratic' (re_neg_quarter hb) _ _

/-- **The Gaussian integral on a vertical line.** -/
lemma integral_quad {b : ℝ} (hb : 0 < b) (z : ℂ) (c L : ℝ) :
    ∫ t : ℝ, cexp ((z + t * I) ^ 2 / (4 * b)) * cexp (-((c : ℂ) + t * I) * L)
      = (Real.sqrt (4 * π * b) : ℂ) * cexp ((z - c) * L - b * L ^ 2) := by
  simp_rw [quad_exp hb]
  rw [integral_cexp_quadratic (re_neg_quarter hb)]
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  congr 1
  · have e : (π : ℂ) / -(-1 / (4 * b)) = ((4 * π * b : ℝ) : ℂ) := by
      push_cast; field_simp
    rw [e, Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    push_cast; ring_nf
  · congr 1
    have e : (I * (z / (2 * b) - L)) ^ 2 = -(z / (2 * b) - L) ^ 2 := by
      rw [mul_pow, Complex.I_sq]; ring
    rw [e]
    field_simp
    ring

lemma sqrt_mul_sqrt {b : ℝ} (hb : 0 < b) :
    (Real.sqrt (π / b) : ℂ) * (Real.sqrt (4 * π * b) : ℂ) = 2 * π := by
  rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by positivity)]
  have e : π / b * (4 * π * b) = (2 * π) ^ 2 := by field_simp; ring
  rw [e, Real.sqrt_sq (by positivity)]
  push_cast; ring

lemma LGw_line (b α c t : ℝ) :
    LGw b α ((c : ℂ) + t * I) = (Real.sqrt (π / b) : ℂ) *
      (cexp ((((c : ℂ) - 1 / 2 + I * α) + t * I) ^ 2 / (4 * b))
        + cexp ((((c : ℂ) - 1 / 2 - I * α) + t * I) ^ 2 / (4 * b))) := by
  unfold LGw; ring_nf

lemma cpow_eq_cexp {x : ℝ} (hx : 0 < x) (w : ℂ) :
    (x : ℂ) ^ (-w) = cexp (-w * (Real.log x : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le]
  ring_nf

theorem integrable_LGw_cpow {b : ℝ} (hb : 0 < b) (α c : ℝ) {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => LGw b α ((c : ℂ) + t * I) * (x : ℂ) ^ (-((c : ℂ) + t * I))) := by
  have h : (fun t : ℝ => LGw b α ((c : ℂ) + t * I) * (x : ℂ) ^ (-((c : ℂ) + t * I)))
      = fun t : ℝ => (Real.sqrt (π / b) : ℂ) *
        (cexp ((((c : ℂ) - 1 / 2 + I * α) + t * I) ^ 2 / (4 * b)) * cexp (-((c : ℂ) + t * I) * Real.log x)
        + cexp ((((c : ℂ) - 1 / 2 - I * α) + t * I) ^ 2 / (4 * b)) * cexp (-((c : ℂ) + t * I) * Real.log x)) := by
    funext t
    rw [LGw_line, cpow_eq_cexp hx]
    ring
  rw [h]
  exact ((integrable_quad hb _ c _).add (integrable_quad hb _ c _)).const_mul _

/-- **Mellin inversion of the kernel**: `kernel b α x = (1/2π) ∫ LGw(c+it) x^{-(c+it)} dt`. -/
theorem kernel_eq_integral {b : ℝ} (hb : 0 < b) (α c : ℝ) {x : ℝ} (hx : 0 < x) :
    ((FleetMollifierTail.kernel b α x : ℝ) : ℂ)
      = (1 / (2 * π) : ℂ) * ∫ t : ℝ, LGw b α ((c : ℂ) + t * I) * (x : ℂ) ^ (-((c : ℂ) + t * I)) := by
  set L := Real.log x with hL
  have h : (fun t : ℝ => LGw b α ((c : ℂ) + t * I) * (x : ℂ) ^ (-((c : ℂ) + t * I)))
      = fun t : ℝ => (Real.sqrt (π / b) : ℂ) *
        (cexp ((((c : ℂ) - 1 / 2 + I * α) + t * I) ^ 2 / (4 * b)) * cexp (-((c : ℂ) + t * I) * L)
        + cexp ((((c : ℂ) - 1 / 2 - I * α) + t * I) ^ 2 / (4 * b)) * cexp (-((c : ℂ) + t * I) * L)) := by
    funext t
    rw [LGw_line, cpow_eq_cexp hx]
    ring
  rw [h, integral_const_mul, integral_add (integrable_quad hb _ c _) (integrable_quad hb _ c _),
    integral_quad hb, integral_quad hb]
  have e1 : cexp (((c : ℂ) - 1 / 2 + I * α - c) * L - b * L ^ 2)
      = cexp (((-(L / 2) - b * L ^ 2 : ℝ) : ℂ)) * cexp (((α * L : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have e2 : cexp (((c : ℂ) - 1 / 2 - I * α - c) * L - b * L ^ 2)
      = cexp (((-(L / 2) - b * L ^ 2 : ℝ) : ℂ)) * cexp (-((α * L : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [e1, e2]
  have hk : ((FleetMollifierTail.kernel b α x : ℝ) : ℂ)
      = 2 * cexp (((-(L / 2) - b * L ^ 2 : ℝ) : ℂ)) * Complex.cos ((α * L : ℝ) : ℂ) := by
    unfold FleetMollifierTail.kernel
    rw [← hL]
    push_cast
    ring_nf
  rw [hk, Complex.cos]
  have hs := sqrt_mul_sqrt hb
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  calc 2 * cexp (((-(L / 2) - b * L ^ 2 : ℝ) : ℂ)) *
        ((cexp (((α * L : ℝ) : ℂ) * I) + cexp (-((α * L : ℝ) : ℂ) * I)) / 2)
      = (1 / (2 * π) : ℂ) * ((Real.sqrt (π / b) : ℂ) * (Real.sqrt (4 * π * b) : ℂ)) *
        (cexp (((-(L / 2) - b * L ^ 2 : ℝ) : ℂ)) * cexp (((α * L : ℝ) : ℂ) * I)
          + cexp (((-(L / 2) - b * L ^ 2 : ℝ) : ℂ)) * cexp (-((α * L : ℝ) : ℂ) * I)) := by
        rw [hs]; field_simp
    _ = _ := by ring

/-! ## Size on vertical lines -/

lemma norm_cexp_sq (b : ℝ) (a y : ℝ) :
    ‖cexp ((((a : ℂ) + I * ((y : ℂ)))) ^ 2 / (4 * b))‖ = Real.exp ((a ^ 2 - y ^ 2) / (4 * b)) := by
  rw [Complex.norm_exp]
  congr 1
  have e : (((a : ℂ) + I * ((y : ℂ)))) ^ 2 / (4 * b) = (((a ^ 2 - y ^ 2) / (4 * b) : ℝ) : ℂ)
      + ((2 * a * y / (4 * b) : ℝ) : ℂ) * I := by
    push_cast
    by_cases hb : b = 0
    · subst hb; simp
    have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb
    field_simp
    ring_nf
    rw [Complex.I_sq]; ring
  rw [e]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]
  ring

/-- **`‖LGw(x+iy)‖ ≤ √(π/b) e^{(x−1/2)²/4b} (e^{-(y+α)²/4b} + e^{-(y−α)²/4b})`.** -/
theorem norm_LGw_le (b α x y : ℝ) :
    ‖LGw b α ((x : ℂ) + y * I)‖ ≤ Real.sqrt (π / b) * Real.exp ((x - 1 / 2) ^ 2 / (4 * b)) *
      (Real.exp (-(y + α) ^ 2 / (4 * b)) + Real.exp (-(y - α) ^ 2 / (4 * b))) := by
  unfold LGw
  have e1 : (x : ℂ) + y * I - 1 / 2 + I * α = (((x - 1 / 2 : ℝ) : ℂ) + I * ((y + α : ℝ) : ℂ)) := by
    push_cast; ring
  have e2 : (x : ℂ) + y * I - 1 / 2 - I * α = (((x - 1 / 2 : ℝ) : ℂ) + I * ((y - α : ℝ) : ℂ)) := by
    push_cast; ring
  rw [e1, e2, norm_mul, Complex.norm_real, Real.norm_eq_abs, _root_.abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsplit : ∀ u v : ℝ, Real.exp ((u ^ 2 - v ^ 2) / (4 * b))
      = Real.exp (u ^ 2 / (4 * b)) * Real.exp (-v ^ 2 / (4 * b)) := by
    intro u v; rw [← Real.exp_add]; congr 1; ring
  calc Real.sqrt (π / b) * ‖cexp ((((x - 1 / 2 : ℝ) : ℂ) + I * ((y + α : ℝ) : ℂ)) ^ 2 / (4 * b))
        + cexp ((((x - 1 / 2 : ℝ) : ℂ) + I * ((y - α : ℝ) : ℂ)) ^ 2 / (4 * b))‖
      ≤ Real.sqrt (π / b) * (‖cexp ((((x - 1 / 2 : ℝ) : ℂ) + I * ((y + α : ℝ) : ℂ)) ^ 2 / (4 * b))‖
        + ‖cexp ((((x - 1 / 2 : ℝ) : ℂ) + I * ((y - α : ℝ) : ℂ)) ^ 2 / (4 * b))‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.sqrt_nonneg _)
    _ = _ := by
        rw [norm_cexp_sq, norm_cexp_sq, hsplit, hsplit]; ring

/-! ## Integrability from a Gaussian-times-linear bound -/

lemma integrable_gauss_shift {b : ℝ} (hb : 0 < b) (β : ℝ) :
    Integrable (fun y : ℝ => Real.exp (-(y - β) ^ 2 / (4 * b))) := by
  have h := (integrable_exp_neg_mul_sq (b := 1 / (4 * b)) (by positivity)).comp_sub_right β
  refine h.congr (ae_of_all _ fun y => ?_)
  simp only [Function.comp]
  congr 1; ring

lemma integrable_abs_gauss_shift {b : ℝ} (hb : 0 < b) (β : ℝ) :
    Integrable (fun y : ℝ => |y - β| * Real.exp (-(y - β) ^ 2 / (4 * b))) := by
  have h := ((integrable_mul_exp_neg_mul_sq (b := 1 / (4 * b)) (by positivity)).norm).comp_sub_right β
  refine h.congr (ae_of_all _ fun y => ?_)
  simp only [Function.comp, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  congr 2; ring

lemma integrable_lin_gauss {b : ℝ} (hb : 0 < b) (β P Q : ℝ) :
    Integrable (fun y : ℝ => (|P| + |Q| * |β|) * Real.exp (-(y - β) ^ 2 / (4 * b))
      + |Q| * (|y - β| * Real.exp (-(y - β) ^ 2 / (4 * b)))) :=
  ((integrable_gauss_shift hb β).const_mul _).add ((integrable_abs_gauss_shift hb β).const_mul _)

lemma lin_le (P Q y β : ℝ) : P + Q * |y| ≤ (|P| + |Q| * |β|) + |Q| * |y - β| := by
  have h1 : P ≤ |P| := le_abs_self P
  have h2 : Q * |y| ≤ |Q| * |y| := mul_le_mul_of_nonneg_right (le_abs_self Q) (abs_nonneg _)
  have h3 : |y| ≤ |y - β| + |β| := by
    calc |y| = |(y - β) + β| := by ring_nf
      _ ≤ |y - β| + |β| := abs_add_le _ _
  nlinarith [abs_nonneg Q]

/-- **Integrability from a Gaussian-times-linear majorant.** -/
theorem integrable_of_gauss_bound {b : ℝ} (hb : 0 < b) (α P Q : ℝ) {g : ℝ → ℂ} (hg : Continuous g)
    (h : ∀ y : ℝ, ‖g y‖ ≤ (P + Q * |y|) *
      (Real.exp (-(y + α) ^ 2 / (4 * b)) + Real.exp (-(y - α) ^ 2 / (4 * b)))) :
    Integrable g := by
  refine Integrable.mono' ((integrable_lin_gauss hb (-α) P Q).add (integrable_lin_gauss hb α P Q))
    hg.aestronglyMeasurable (ae_of_all _ fun y => ?_)
  have e : (y + α) = y - (-α) := by ring
  have hy := h y
  rw [e] at hy
  have hA := lin_le P Q y (-α)
  have hB := lin_le P Q y α
  have p1 := Real.exp_pos (-(y - -α) ^ 2 / (4 * b))
  have p2 := Real.exp_pos (-(y - α) ^ 2 / (4 * b))
  calc ‖g y‖ ≤ (P + Q * |y|) * (Real.exp (-(y - -α) ^ 2 / (4 * b)) + Real.exp (-(y - α) ^ 2 / (4 * b))) := hy
    _ = (P + Q * |y|) * Real.exp (-(y - -α) ^ 2 / (4 * b))
        + (P + Q * |y|) * Real.exp (-(y - α) ^ 2 / (4 * b)) := by ring
    _ ≤ ((|P| + |Q| * |-α|) + |Q| * |y - -α|) * Real.exp (-(y - -α) ^ 2 / (4 * b))
        + ((|P| + |Q| * |α|) + |Q| * |y - α|) * Real.exp (-(y - α) ^ 2 / (4 * b)) :=
        add_le_add (mul_le_mul_of_nonneg_right hA p1.le) (mul_le_mul_of_nonneg_right hB p2.le)
    _ = _ := by simp only [Pi.add_apply]; ring

/-! ## The Möbius polynomial -/

/-- `M_M(w) = Σ_{m ≤ M} μ(m) m^{-w}` (the `m = 0` term vanishes). -/
def Mpoly (M : ℕ) (w : ℂ) : ℂ :=
  ∑ m ∈ Finset.range (M + 1), (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-w)

lemma moebius_term_eq (m : ℕ) :
    (fun w : ℂ => (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-w))
      = fun w : ℂ => if m = 0 then 0 else (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-w) := by
  funext w
  split_ifs with h
  · subst h; simp
  · rfl

theorem differentiable_Mpoly (M : ℕ) : Differentiable ℂ (Mpoly M) := by
  unfold Mpoly
  have : (fun w : ℂ => ∑ m ∈ Finset.range (M + 1), (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-w))
      = fun w : ℂ => ∑ m ∈ Finset.range (M + 1),
        (fun w : ℂ => (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-w)) w := rfl
  rw [this]
  apply Differentiable.fun_sum
  intro m _
  rw [moebius_term_eq m]
  split_ifs with h
  · exact differentiable_const _
  · have hm : (m : ℂ) ≠ 0 := by exact_mod_cast h
    exact (differentiable_const _).mul (fun w => (differentiableAt_neg_iff.mpr (differentiableAt_id)).const_cpow (Or.inl hm))

lemma norm_moebius_cpow_le (m : ℕ) {w : ℂ} (hw : 0 ≤ w.re) :
    ‖(ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-w)‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  rw [norm_mul, norm_natCast_cpow_of_pos hm]
  have h1 : ‖(ArithmeticFunction.moebius m : ℂ)‖ ≤ 1 := by
    have := FleetMollifierTail.moebius_abs_le m
    rw [show (ArithmeticFunction.moebius m : ℂ) = ((ArithmeticFunction.moebius m : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs]
    exact this
  have h2 : (m : ℝ) ^ (-w).re ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm)
    simp; exact hw
  calc ‖(ArithmeticFunction.moebius m : ℂ)‖ * (m : ℝ) ^ (-w).re ≤ 1 * 1 :=
        mul_le_mul h1 h2 (by positivity) zero_le_one
    _ = 1 := by ring

theorem norm_Mpoly_le (M : ℕ) {w : ℂ} (hw : 0 ≤ w.re) : ‖Mpoly M w‖ ≤ M + 1 := by
  unfold Mpoly
  calc ‖∑ m ∈ Finset.range (M + 1), (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-w)‖
      ≤ ∑ m ∈ Finset.range (M + 1), ‖(ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-w)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.range (M + 1), (1 : ℝ) := Finset.sum_le_sum fun m _ => norm_moebius_cpow_le m hw
    _ = M + 1 := by simp

end FleetHeadContour
