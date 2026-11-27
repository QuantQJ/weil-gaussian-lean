import FleetSmoothWindowContour
import FleetLandauTransfer

/-!
# Strip `δ` ⇒ smooth window rate `δ²/2 + ε`

The Gaussian weight `e^{-b log² n}` is the Mellin transform of a Gaussian on a vertical line, so the smooth
Möbius sum is a Gaussian average of `1/ζ` (`Psm_eq_line`, unconditional, any line `Re u = σ > 1`, any `s`):

  `P_b(s) = (4πb)^{-1/2} ∫_ℝ e^{(σ + iy − s)²/(4b)} ζ(σ+iy)^{-1} dy`.

If `ζ ≠ 0` on `Re > 1/2 + δ₀`, the line moves to `Re u = 1/2 + κ`, `κ > δ₀`, where
`‖1/ζ(u)‖ ≪ 1 + |Im u|` (`FleetLandauTransfer.invZeta_bound`). On the critical line this gives
(`norm_Psm_half_le_of_zeroFree`)

  `‖P_b(1/2+it)‖ ≤ K (1 + |t|) e^{κ²/(4b)}`  (`0 < b ≤ 1`, every real `t`, `K` independent of `b, t`),

so the window is `≤ K' (1+|α|)² e^{κ²/(2b)}` (`smoothWindow_le_of_zeroFree`): the rate `κ²/2`, uniform in the
centre `α` (the constant grows like `(1+|α|)²`).

* `smoothWindowRate_of_strip`: `StripBound δ` (`δ ≥ 0`) ⇒ `SmoothWindowRate (δ²/2 + ε)` for every `ε > 0`.
* `smoothWindowRate_of_quasiRH`: `QuasiRH` ⇒ `SmoothWindowRate (9/128 + ε)`.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace FleetSmoothWindow

open FleetLandauTransfer FleetHeadContour

/-- `g_s(u) = e^{(u − s)²/(4b)} · (1/ζ)(u)`. -/
def gline (b : ℝ) (s u : ℂ) : ℂ := cexp ((u - s) ^ 2 / (4 * b)) * invZeta u

lemma norm_cexp_quad (b : ℝ) (s : ℂ) (x y : ℝ) :
    ‖cexp ((((x : ℂ) + y * I) - s) ^ 2 / (4 * b))‖
      = Real.exp (((x - s.re) ^ 2 - (y - s.im) ^ 2) / (4 * b)) := by
  have e : ((x : ℂ) + y * I) - s = (((x - s.re : ℝ) : ℂ) + I * ((y - s.im : ℝ) : ℂ)) := by
    apply Complex.ext <;> simp
  rw [e, norm_cexp_sq]

lemma term_moebius_eq {w : ℂ} {n : ℕ} (hn : n ≠ 0) :
    LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) w n
      = (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-w) := by
  rw [LSeries.term_of_ne_zero hn, Complex.cpow_neg, div_eq_mul_inv]

lemma norm_term_moebius_le (w : ℂ) (n : ℕ) :
    ‖LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) w n‖ ≤ (n : ℝ) ^ (-w.re) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [LSeries.term_zero, norm_zero]; positivity
  rw [term_moebius_eq hn.ne', norm_mul, norm_natCast_cpow_of_pos hn, neg_re]
  have hμ : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    rw [show (ArithmeticFunction.moebius n : ℂ) = ((ArithmeticFunction.moebius n : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  calc ‖(ArithmeticFunction.moebius n : ℂ)‖ * (n : ℝ) ^ (-w.re) ≤ 1 * (n : ℝ) ^ (-w.re) := by gcongr
    _ = _ := one_mul _

/-- The `n`-th Gaussian line integral. -/
lemma integral_term {b : ℝ} (hb : 0 < b) (s : ℂ) (σ : ℝ) (n : ℕ) :
    ∫ y : ℝ, cexp ((((σ : ℂ) + y * I) - s) ^ 2 / (4 * b))
        * LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) ((σ : ℂ) + y * I) n
      = (Real.sqrt (4 * π * b) : ℂ) * ((ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s)
          * (Real.exp (-b * Real.log n ^ 2) : ℂ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set L := Real.log n
  have hpt : ∀ y : ℝ, cexp ((((σ : ℂ) + y * I) - s) ^ 2 / (4 * b))
        * LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) ((σ : ℂ) + y * I) n
      = (ArithmeticFunction.moebius n : ℂ) *
        (cexp (((σ - s) + y * I) ^ 2 / (4 * b)) * cexp (-((σ : ℂ) + y * I) * L)) := by
    intro y
    rw [term_moebius_eq hn.ne', show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl, cpow_eq_cexp hn0]
    have e : ((σ : ℂ) + y * I) - s = (σ - s) + y * I := by ring
    rw [e]; ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_quad hb]
  have e2 : cexp (((σ : ℂ) - s - σ) * L - b * L ^ 2) = cexp (-s * L) * (Real.exp (-b * L ^ 2) : ℂ) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [e2, show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl, cpow_eq_cexp hn0]
  ring

lemma integrable_term {b : ℝ} (hb : 0 < b) (s : ℂ) (σ : ℝ) (n : ℕ) :
    Integrable (fun y : ℝ => cexp ((((σ : ℂ) + y * I) - s) ^ 2 / (4 * b))
        * LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) ((σ : ℂ) + y * I) n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hpt : (fun y : ℝ => cexp ((((σ : ℂ) + y * I) - s) ^ 2 / (4 * b))
        * LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) ((σ : ℂ) + y * I) n)
      = fun y : ℝ => (ArithmeticFunction.moebius n : ℂ) *
        (cexp (((σ - s) + y * I) ^ 2 / (4 * b)) * cexp (-((σ : ℂ) + y * I) * Real.log n)) := by
    funext y
    rw [term_moebius_eq hn.ne', show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl, cpow_eq_cexp hn0]
    have e : ((σ : ℂ) + y * I) - s = (σ - s) + y * I := by ring
    rw [e]; ring
  rw [hpt]
  exact (integrable_quad hb _ σ _).const_mul _

lemma integral_norm_term_le {b : ℝ} (hb : 0 < b) (s : ℂ) (σ : ℝ) (n : ℕ) :
    ∫ y : ℝ, ‖cexp ((((σ : ℂ) + y * I) - s) ^ 2 / (4 * b))
        * LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) ((σ : ℂ) + y * I) n‖
      ≤ (n : ℝ) ^ (-σ) * (Real.exp ((σ - s.re) ^ 2 / (4 * b)) * Real.sqrt (4 * π * b)) := by
  have hb' : ∀ y : ℝ, ‖cexp ((((σ : ℂ) + y * I) - s) ^ 2 / (4 * b))
        * LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) ((σ : ℂ) + y * I) n‖
      ≤ (n : ℝ) ^ (-σ) * Real.exp ((σ - s.re) ^ 2 / (4 * b)) * Real.exp (-(y - s.im) ^ 2 / (4 * b)) := by
    intro y
    rw [norm_mul, norm_cexp_quad]
    have h1 := norm_term_moebius_le ((σ : ℂ) + y * I) n
    have hre : ((σ : ℂ) + y * I).re = σ := by simp
    rw [hre] at h1
    have e : Real.exp (((σ - s.re) ^ 2 - (y - s.im) ^ 2) / (4 * b))
        = Real.exp ((σ - s.re) ^ 2 / (4 * b)) * Real.exp (-(y - s.im) ^ 2 / (4 * b)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e]
    calc Real.exp ((σ - s.re) ^ 2 / (4 * b)) * Real.exp (-(y - s.im) ^ 2 / (4 * b))
          * ‖LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) ((σ : ℂ) + y * I) n‖
        ≤ Real.exp ((σ - s.re) ^ 2 / (4 * b)) * Real.exp (-(y - s.im) ^ 2 / (4 * b)) * (n : ℝ) ^ (-σ) := by
          gcongr
      _ = _ := by ring
  calc _ ≤ ∫ y : ℝ, (n : ℝ) ^ (-σ) * Real.exp ((σ - s.re) ^ 2 / (4 * b))
          * Real.exp (-(y - s.im) ^ 2 / (4 * b)) :=
        integral_mono (integrable_term hb s σ n).norm
          ((FleetHeadContour.integrable_gauss_shift hb s.im).const_mul _) hb'
    _ = _ := by rw [integral_const_mul, integral_gauss_shift hb]; ring

/-- **`P_b` as a Gaussian average of `1/ζ`**: for every `s` and every `σ > 1`,
`√(4πb) · P_b(s) = ∫ e^{(σ+iy−s)²/(4b)} (1/ζ)(σ+iy) dy`. -/
theorem Psm_eq_line {b : ℝ} (hb : 0 < b) (s : ℂ) {σ : ℝ} (hσ : 1 < σ) :
    (Real.sqrt (4 * π * b) : ℂ) * Psm b s = ∫ y : ℝ, gline b s ((σ : ℂ) + y * I) := by
  have hpt : ∀ y : ℝ, gline b s ((σ : ℂ) + y * I) = ∑' n : ℕ, cexp ((((σ : ℂ) + y * I) - s) ^ 2 / (4 * b))
        * LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) ((σ : ℂ) + y * I) n := by
    intro y
    unfold gline
    rw [invZeta_eq_LSeries (by simpa using hσ), LSeries, tsum_mul_left]
  simp_rw [hpt]
  rw [← integral_tsum_of_summable_integral_norm (integrable_term hb s σ)]
  · simp_rw [integral_term hb s σ]
    rw [tsum_mul_left]
    rfl
  · refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun y => norm_nonneg _)
      (integral_norm_term_le hb s σ) ?_
    exact (Real.summable_nat_rpow.mpr (by linarith)).mul_right _

/-! ## The bound on the critical line under a zero-free half-plane -/

lemma one_add_abs_le_exp_gauss {b : ℝ} (hb : 0 < b) (v : ℝ) :
    (1 + |v|) * Real.exp (-v ^ 2 / (4 * b)) ≤ Real.exp (2 * b) * Real.exp (-v ^ 2 / (4 * (2 * b))) := by
  have h1 : 1 + |v| ≤ Real.exp |v| := by linarith [Real.add_one_le_exp |v|]
  calc (1 + |v|) * Real.exp (-v ^ 2 / (4 * b)) ≤ Real.exp |v| * Real.exp (-v ^ 2 / (4 * b)) := by gcongr
    _ ≤ Real.exp (2 * b) * Real.exp (-v ^ 2 / (4 * (2 * b))) := by
        rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
        have key : |v| - v ^ 2 / (8 * b) ≤ 2 * b := by
          rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ (by positivity)]
          nlinarith [sq_nonneg (|v| - 4 * b), sq_abs v]
        have e1 : -v ^ 2 / (4 * b) = -(v ^ 2 / (8 * b)) - v ^ 2 / (8 * b) := by field_simp; ring
        have e2 : -v ^ 2 / (4 * (2 * b)) = -(v ^ 2 / (8 * b)) := by field_simp; ring
        rw [e1, e2]; linarith

lemma two_abs_le_exp_gauss {b : ℝ} (hb : 0 < b) (v : ℝ) :
    (1 + |v|) ^ 2 * Real.exp (-v ^ 2 / (4 * b)) ≤ Real.exp (8 * b) * Real.exp (-v ^ 2 / (4 * (2 * b))) := by
  have h1 : 1 + |v| ≤ Real.exp |v| := by linarith [Real.add_one_le_exp |v|]
  have h2 : (1 + |v|) ^ 2 ≤ Real.exp (2 * |v|) := by
    rw [show 2 * |v| = |v| + |v| by ring, Real.exp_add, sq]
    exact mul_le_mul h1 h1 (by positivity) (Real.exp_pos _).le
  calc (1 + |v|) ^ 2 * Real.exp (-v ^ 2 / (4 * b)) ≤ Real.exp (2 * |v|) * Real.exp (-v ^ 2 / (4 * b)) := by
        gcongr
    _ ≤ Real.exp (8 * b) * Real.exp (-v ^ 2 / (4 * (2 * b))) := by
        rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
        have key : 2 * |v| - v ^ 2 / (8 * b) ≤ 8 * b := by
          rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ (by positivity)]
          nlinarith [sq_nonneg (|v| - 8 * b), sq_abs v]
        have e1 : -v ^ 2 / (4 * b) = -(v ^ 2 / (8 * b)) - v ^ 2 / (8 * b) := by field_simp; ring
        have e2 : -v ^ 2 / (4 * (2 * b)) = -(v ^ 2 / (8 * b)) := by field_simp; ring
        rw [e1, e2]; linarith

lemma rpow_le_one_add {C y η : ℝ} (hC : 0 ≤ C) (hη0 : 0 ≤ η) (hη : η ≤ 1) :
    C * (1 + |y|) ^ η ≤ C * (1 + |y|) := by
  apply mul_le_mul_of_nonneg_left _ hC
  have h1 : (1 : ℝ) ≤ 1 + |y| := by linarith [abs_nonneg y]
  calc (1 + |y|) ^ η ≤ (1 + |y|) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hη
    _ = 1 + |y| := Real.rpow_one _

/-- The pointwise bound for `g_s` on a line in the zero-free region. -/
lemma norm_gline_le {b : ℝ} {C : ℝ} {σ₀ : ℝ}
    (hb : ∀ u : ℂ, σ₀ ≤ u.re → ‖invZeta u‖ ≤ C * (1 + |u.im|) ^ (1 / 2 : ℝ)) (hC : 0 ≤ C)
    (s : ℂ) {x : ℝ} (hx : σ₀ ≤ x) (y : ℝ) :
    ‖gline b s ((x : ℂ) + y * I)‖
      ≤ Real.exp (((x - s.re) ^ 2 - (y - s.im) ^ 2) / (4 * b)) * (C * (1 + |y|)) := by
  unfold gline
  rw [norm_mul, norm_cexp_quad]
  have h := hb ((x : ℂ) + y * I) (by simpa using hx)
  have him : ((x : ℂ) + y * I).im = y := by simp
  rw [him] at h
  gcongr
  exact h.trans (rpow_le_one_add hC (by norm_num) (by norm_num))

lemma continuous_gline_line {b : ℝ} {δ₀ : ℝ} (hZ : ∀ s : ℂ, 1 / 2 + δ₀ < s.re → riemannZeta s ≠ 0)
    (s : ℂ) {x : ℝ} (hx : 1 / 2 + δ₀ < x) : Continuous (fun y : ℝ => gline b s ((x : ℂ) + y * I)) := by
  unfold gline
  refine Continuous.mul (by fun_prop) ?_
  refine continuous_iff_continuousAt.mpr fun y => ?_
  have hre : ((x : ℂ) + y * I).re = x := by simp
  exact ((invZeta_differentiableAt_of_zeroFree hZ (by rw [hre]; exact hx)).continuousAt).comp
    (by fun_prop : Continuous (fun y : ℝ => (x : ℂ) + y * I)).continuousAt

lemma integrable_gline_line {b : ℝ} (hb0 : 0 < b) {δ₀ C σ₀ : ℝ}
    (hZ : ∀ s : ℂ, 1 / 2 + δ₀ < s.re → riemannZeta s ≠ 0)
    (hb : ∀ u : ℂ, σ₀ ≤ u.re → ‖invZeta u‖ ≤ C * (1 + |u.im|) ^ (1 / 2 : ℝ)) (hC : 0 ≤ C)
    (hσ₀ : 1 / 2 + δ₀ < σ₀) (s : ℂ) {x : ℝ} (hx : σ₀ ≤ x) :
    Integrable (fun y : ℝ => gline b s ((x : ℂ) + y * I)) := by
  refine integrable_of_gauss1 hb0 (continuous_gline_line hZ s (by linarith))
    (P := Real.exp ((x - s.re) ^ 2 / (4 * b)) * C) (Q := Real.exp ((x - s.re) ^ 2 / (4 * b)) * C)
    (β := s.im) (by positivity) (by positivity) fun y => ?_
  refine (norm_gline_le hb hC s hx y).trans (le_of_eq ?_)
  rw [show ((x - s.re) ^ 2 - (y - s.im) ^ 2) / (4 * b)
      = (x - s.re) ^ 2 / (4 * b) + (-(y - s.im) ^ 2 / (4 * b)) by ring, Real.exp_add]
  ring

lemma tendsto_horiz_gline {b : ℝ} (hb0 : 0 < b) {C σ₀ : ℝ}
    (hb : ∀ u : ℂ, σ₀ ≤ u.re → ‖invZeta u‖ ≤ C * (1 + |u.im|) ^ (1 / 2 : ℝ)) (hC : 0 ≤ C)
    (s : ℂ) {a₁ a₂ : ℝ} (ha₁ : σ₀ ≤ a₁) (ha : a₁ ≤ a₂) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    Tendsto (fun T : ℝ => ∫ x in a₁..a₂, gline b s ((x : ℂ) + ((σ * T : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
  set A := Real.exp (((|a₁| + |a₂| + |s.re|) ^ 2) / (4 * b)) * C
  have hlim : Tendsto (fun T : ℝ => (A + A * T) * Real.exp (-(T - σ * s.im) ^ 2 / (4 * b))) atTop (𝓝 0) :=
    tendsto_lin_gauss hb0 _ A A
  refine tendsto_horiz_of_bound hlim fun T hT x hx => ?_
  rw [uIcc_of_le ha] at hx
  refine (norm_gline_le hb hC s (le_trans ha₁ hx.1) (σ * T)).trans ?_
  have hσT : |σ * T| = T := by
    rcases hσ with rfl | rfl <;> simp [abs_of_pos (by linarith : (0 : ℝ) < T)]
  rw [hσT]
  have h1 : (x - s.re) ^ 2 ≤ (|a₁| + |a₂| + |s.re|) ^ 2 := by
    have hx1 : |x| ≤ |a₁| + |a₂| := by
      rw [abs_le]; constructor <;> cases abs_cases a₁ <;> cases abs_cases a₂ <;> linarith [hx.1, hx.2]
    have : |x - s.re| ≤ |a₁| + |a₂| + |s.re| := (abs_sub _ _).trans (by linarith)
    calc (x - s.re) ^ 2 = |x - s.re| ^ 2 := (sq_abs _).symm
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) this 2
  have h2 : (σ * T - s.im) ^ 2 = (T - σ * s.im) ^ 2 := by
    rcases hσ with rfl | rfl <;> ring
  rw [h2, show ((x - s.re) ^ 2 - (T - σ * s.im) ^ 2) / (4 * b)
      = (x - s.re) ^ 2 / (4 * b) + (-(T - σ * s.im) ^ 2 / (4 * b)) by ring, Real.exp_add]
  have h3 : Real.exp ((x - s.re) ^ 2 / (4 * b)) ≤ Real.exp (((|a₁| + |a₂| + |s.re|) ^ 2) / (4 * b)) := by
    gcongr
  have hE := Real.exp_pos (-(T - σ * s.im) ^ 2 / (4 * b))
  calc Real.exp ((x - s.re) ^ 2 / (4 * b)) * Real.exp (-(T - σ * s.im) ^ 2 / (4 * b)) * (C * (1 + T))
      ≤ Real.exp (((|a₁| + |a₂| + |s.re|) ^ 2) / (4 * b)) * Real.exp (-(T - σ * s.im) ^ 2 / (4 * b))
          * (C * (1 + T)) := by gcongr
    _ = (A + A * T) * Real.exp (-(T - σ * s.im) ^ 2 / (4 * b)) := by simp only [A]; ring

/-- **The critical-line bound under a zero-free half-plane.** If `ζ ≠ 0` on `Re > 1/2 + δ₀` (`δ₀ ≥ 0`)
and `δ₀ < κ ≤ 1`, there is `K` with `‖P_b(1/2+it)‖ ≤ K (1+|t|) e^{κ²/(4b)}` for all `0 < b ≤ 1` and real `t`. -/
theorem norm_Psm_half_le_of_zeroFree {δ₀ : ℝ} (hδ₀ : 0 ≤ δ₀)
    (hZ : ∀ s : ℂ, 1 / 2 + δ₀ < s.re → riemannZeta s ≠ 0) {κ : ℝ} (hκ : δ₀ < κ) (hκ1 : κ ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b : ℝ, 0 < b → b ≤ 1 → ∀ t : ℝ,
      ‖Psm b (((1 / 2 : ℝ) : ℂ) + t * I)‖ ≤ K * (1 + |t|) * Real.exp (κ ^ 2 / (4 * b)) := by
  set σ₀ := 1 / 2 + κ
  have hσ₀ : 1 / 2 + δ₀ < σ₀ := by simp only [σ₀]; linarith
  obtain ⟨C, hC, hbd⟩ := invZeta_bound hδ₀ hZ hσ₀ (η := 1 / 2) (by norm_num)
  refine ⟨C * Real.exp 2 * Real.sqrt 2, by positivity, fun b hb hb1 t => ?_⟩
  set s : ℂ := ((1 / 2 : ℝ) : ℂ) + t * I
  have hsre : s.re = 1 / 2 := by simp [s]
  have hsim : s.im = t := by simp [s]
  -- the two lines `Re = σ₀` and `Re = 2`
  have hshift : ∫ y : ℝ, gline b s ((σ₀ : ℂ) + y * I) = ∫ y : ℝ, gline b s (((2 : ℝ) : ℂ) + y * I) := by
    refine line_shift_zero (by simp only [σ₀]; linarith) (fun z hz _ => ?_)
      (integrable_gline_line hb hZ hbd hC.le hσ₀ s le_rfl)
      (integrable_gline_line hb hZ hbd hC.le hσ₀ s (by simp only [σ₀]; linarith))
      (by simpa using (tendsto_horiz_gline hb hbd hC.le s le_rfl (by simp only [σ₀]; linarith) 1
        (Or.inl rfl)))
      (by simpa using (tendsto_horiz_gline hb hbd hC.le s le_rfl (by simp only [σ₀]; linarith) (-1)
        (Or.inr rfl)))
    have hd : DifferentiableAt ℂ (fun u : ℂ => cexp ((u - s) ^ 2 / (4 * b))) z := by fun_prop
    exact hd.mul (invZeta_differentiableAt_of_zeroFree hZ (by linarith))
  have hrep := Psm_eq_line hb s (σ := 2) (by norm_num)
  rw [← hshift] at hrep
  -- bound the line integral
  have hpt : ∀ y : ℝ, ‖gline b s ((σ₀ : ℂ) + y * I)‖
      ≤ C * (1 + |t|) * Real.exp (κ ^ 2 / (4 * b)) * Real.exp (2 * b)
        * Real.exp (-(y - t) ^ 2 / (4 * (2 * b))) := by
    intro y
    refine (norm_gline_le hbd hC.le s le_rfl y).trans ?_
    rw [hsre, hsim, show σ₀ - 1 / 2 = κ by simp only [σ₀]; ring,
      show (κ ^ 2 - (y - t) ^ 2) / (4 * b) = κ ^ 2 / (4 * b) + (-(y - t) ^ 2 / (4 * b)) by ring,
      Real.exp_add]
    have h1 : 1 + |y| ≤ (1 + |t|) * (1 + |y - t|) := by
      have : |y| ≤ |t| + |y - t| := by
        calc |y| = |t + (y - t)| := by ring_nf
          _ ≤ |t| + |y - t| := abs_add_le _ _
      nlinarith [abs_nonneg t, abs_nonneg (y - t)]
    have h2 := one_add_abs_le_exp_gauss hb (y - t)
    have hE := Real.exp_pos (κ ^ 2 / (4 * b))
    calc Real.exp (κ ^ 2 / (4 * b)) * Real.exp (-(y - t) ^ 2 / (4 * b)) * (C * (1 + |y|))
        ≤ Real.exp (κ ^ 2 / (4 * b)) * Real.exp (-(y - t) ^ 2 / (4 * b)) * (C * ((1 + |t|) * (1 + |y - t|))) := by
          gcongr
      _ = C * (1 + |t|) * Real.exp (κ ^ 2 / (4 * b)) * ((1 + |y - t|) * Real.exp (-(y - t) ^ 2 / (4 * b))) := by
          ring
      _ ≤ C * (1 + |t|) * Real.exp (κ ^ 2 / (4 * b)) * (Real.exp (2 * b) * Real.exp (-(y - t) ^ 2 / (4 * (2 * b)))) := by
          gcongr
      _ = _ := by ring
  have hint : ‖∫ y : ℝ, gline b s ((σ₀ : ℂ) + y * I)‖
      ≤ C * (1 + |t|) * Real.exp (κ ^ 2 / (4 * b)) * Real.exp (2 * b) * Real.sqrt (4 * π * (2 * b)) := by
    refine (norm_integral_le_of_norm_le
      ((FleetHeadContour.integrable_gauss_shift (by positivity : 0 < 2 * b) t).const_mul
        (C * (1 + |t|) * Real.exp (κ ^ 2 / (4 * b)) * Real.exp (2 * b)))
      (ae_of_all _ hpt)).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_gauss_shift (by positivity : 0 < 2 * b)]
  have hsq : 0 < Real.sqrt (4 * π * b) := Real.sqrt_pos.mpr (by positivity)
  have hnorm : Real.sqrt (4 * π * b) * ‖Psm b s‖ = ‖∫ y : ℝ, gline b s ((σ₀ : ℂ) + y * I)‖ := by
    rw [← hrep, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsq]
  have hs2 : Real.sqrt (4 * π * (2 * b)) = Real.sqrt 2 * Real.sqrt (4 * π * b) := by
    rw [← Real.sqrt_mul (by norm_num)]; congr 1; ring
  have he2 : Real.exp (2 * b) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by linarith)
  have key : Real.sqrt (4 * π * b) * ‖Psm b s‖
      ≤ Real.sqrt (4 * π * b) * (C * Real.exp 2 * Real.sqrt 2 * (1 + |t|) * Real.exp (κ ^ 2 / (4 * b))) := by
    rw [hnorm]
    refine hint.trans ?_
    rw [hs2]
    have : 0 ≤ C * (1 + |t|) * Real.exp (κ ^ 2 / (4 * b)) * (Real.sqrt 2 * Real.sqrt (4 * π * b)) := by
      positivity
    nlinarith
  exact le_of_mul_le_mul_left key hsq

/-- **The window bound under a zero-free half-plane**: `smoothWindow b α ≤ K² e^8 √(8π) (1+|α|)² e^{κ²/(2b)}`. -/
theorem smoothWindow_le_of_zeroFree {δ₀ : ℝ} (hδ₀ : 0 ≤ δ₀)
    (hZ : ∀ s : ℂ, 1 / 2 + δ₀ < s.re → riemannZeta s ≠ 0) {κ : ℝ} (hκ : δ₀ < κ) (hκ1 : κ ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b : ℝ, 0 < b → b ≤ 1 → ∀ α : ℝ,
      smoothWindow b α ≤ K * (1 + |α|) ^ 2 * Real.exp (κ ^ 2 / (2 * b)) := by
  obtain ⟨K, hK, hP⟩ := norm_Psm_half_le_of_zeroFree hδ₀ hZ hκ hκ1
  refine ⟨K ^ 2 * Real.exp 8 * Real.sqrt (8 * π), by positivity, fun b hb hb1 α => ?_⟩
  set E := Real.exp (κ ^ 2 / (4 * b))
  have hE2 : E ^ 2 = Real.exp (κ ^ 2 / (2 * b)) := by
    simp only [E]; rw [← Real.exp_nat_mul]; congr 1; field_simp; ring
  have hpt : ∀ t : ℝ, ‖Psm b (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 * Real.exp (-(t - α) ^ 2 / (4 * b))
      ≤ K ^ 2 * E ^ 2 * (1 + |α|) ^ 2 * (Real.exp (8 * b) * Real.exp (-(t - α) ^ 2 / (4 * (2 * b)))) := by
    intro t
    have h1 := hP b hb hb1 t
    have h2 : 1 + |t| ≤ (1 + |α|) * (1 + |t - α|) := by
      have : |t| ≤ |α| + |t - α| := by
        calc |t| = |α + (t - α)| := by ring_nf
          _ ≤ |α| + |t - α| := abs_add_le _ _
      nlinarith [abs_nonneg α, abs_nonneg (t - α)]
    have h3 := two_abs_le_exp_gauss hb (t - α)
    have hn : ‖Psm b (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 ≤ (K * ((1 + |α|) * (1 + |t - α|)) * E) ^ 2 := by
      have := h1.trans (by gcongr : K * (1 + |t|) * E ≤ K * ((1 + |α|) * (1 + |t - α|)) * E)
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    calc ‖Psm b (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 * Real.exp (-(t - α) ^ 2 / (4 * b))
        ≤ (K * ((1 + |α|) * (1 + |t - α|)) * E) ^ 2 * Real.exp (-(t - α) ^ 2 / (4 * b)) := by gcongr
      _ = K ^ 2 * E ^ 2 * (1 + |α|) ^ 2 * ((1 + |t - α|) ^ 2 * Real.exp (-(t - α) ^ 2 / (4 * b))) := by ring
      _ ≤ _ := by gcongr
  unfold smoothWindow
  calc ∫ t : ℝ, ‖Psm b (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 * Real.exp (-(t - α) ^ 2 / (4 * b))
      ≤ ∫ t : ℝ, K ^ 2 * E ^ 2 * (1 + |α|) ^ 2 * (Real.exp (8 * b) * Real.exp (-(t - α) ^ 2 / (4 * (2 * b)))) :=
        integral_mono (integrable_window hb α)
          (((FleetHeadContour.integrable_gauss_shift (by positivity : 0 < 2 * b) α).const_mul _).const_mul _) hpt
    _ = K ^ 2 * E ^ 2 * (1 + |α|) ^ 2 * (Real.exp (8 * b) * Real.sqrt (4 * π * (2 * b))) := by
        rw [integral_const_mul, integral_const_mul, integral_gauss_shift (by positivity : 0 < 2 * b)]
    _ ≤ K ^ 2 * E ^ 2 * (1 + |α|) ^ 2 * (Real.exp 8 * Real.sqrt (8 * π)) := by
        have h8 : Real.exp (8 * b) ≤ Real.exp 8 := Real.exp_le_exp.mpr (by linarith)
        have hs8 : Real.sqrt (4 * π * (2 * b)) ≤ Real.sqrt (8 * π) :=
          Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])
        have : 0 ≤ K ^ 2 * E ^ 2 * (1 + |α|) ^ 2 := by positivity
        gcongr
    _ = _ := by rw [← hE2]; ring

/-! ## Rates -/

theorem smoothWindowRate_mono {c c' : ℝ} (hcc : c ≤ c') (h : SmoothWindowRate c) : SmoothWindowRate c' := by
  intro α
  obtain ⟨C, hC⟩ := h α
  refine ⟨|C|, fun b hb hb1 => (hC b hb hb1).trans ?_⟩
  calc C * Real.exp (c / b) ≤ |C| * Real.exp (c / b) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
    _ ≤ |C| * Real.exp (c' / b) := by gcongr

/-- **Zero-free half-plane ⇒ rate `κ²/2`.** -/
theorem smoothWindowRate_of_zeroFree {δ₀ : ℝ} (hδ₀ : 0 ≤ δ₀)
    (hZ : ∀ s : ℂ, 1 / 2 + δ₀ < s.re → riemannZeta s ≠ 0) {κ : ℝ} (hκ : δ₀ < κ) (hκ1 : κ ≤ 1) :
    SmoothWindowRate (κ ^ 2 / 2) := by
  obtain ⟨K, hK, hW⟩ := smoothWindow_le_of_zeroFree hδ₀ hZ hκ hκ1
  intro α
  refine ⟨K * (1 + |α|) ^ 2, fun b hb hb1 => (hW b hb hb1 α).trans (le_of_eq ?_)⟩
  congr 2; field_simp

/-- **Strip `δ` ⇒ smooth window rate `δ²/2 + ε`**, every `ε > 0` (no further hypothesis; for `δ ≥ 1/2` this is
the unconditional rate `1/8 + ε`). -/
theorem smoothWindowRate_of_strip {δ : ℝ} (hδ : 0 ≤ δ) (hs : StripBound δ) {ε : ℝ} (hε : 0 < ε) :
    SmoothWindowRate (δ ^ 2 / 2 + ε) := by
  by_cases hδ' : δ < 1 / 2
  · have hZ : ∀ s : ℂ, 1 / 2 + δ < s.re → riemannZeta s ≠ 0 :=
      fun s hre => zeta_ne_zero_of_stripBound hδ hs hre
    set e := min (1 / 2) (ε / (δ + 1))
    have he : 0 < e := lt_min (by norm_num) (div_pos hε (by linarith))
    have he1 : e ≤ 1 / 2 := min_le_left _ _
    have he2 : e ≤ ε / (δ + 1) := min_le_right _ _
    refine smoothWindowRate_mono ?_ (smoothWindowRate_of_zeroFree hδ hZ (κ := δ + e) (by linarith)
      (by linarith))
    have h3 : e * (δ + 1) ≤ ε := by rwa [le_div_iff₀ (by linarith)] at he2
    nlinarith
  · push Not at hδ'
    exact smoothWindowRate_mono (by nlinarith) (smoothWindowRate_one_eighth hε)

/-- **The `QuasiRH` instance**: `QuasiRH` ⇒ smooth window rate `9/128 + ε` (`δ = 3/8`). -/
theorem smoothWindowRate_of_quasiRH (hQ : QuasiRHWiring.QuasiRH) {ε : ℝ} (hε : 0 < ε) :
    SmoothWindowRate (9 / 128 + ε) := by
  have h := smoothWindowRate_of_strip (by norm_num) (stripBound_of_quasiRH hQ) hε
  convert h using 2; norm_num

end FleetSmoothWindow
