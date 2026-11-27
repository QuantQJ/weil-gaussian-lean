import FleetSmoothWindowConverse
import FleetFiniteHeadRH
import FleetHeadContourLine

/-!
# The prime sum through the smooth Möbius sum: an exact identity

`1/ζ` is a horizontal Gaussian average of `P_b` (`invZeta_eq_gauss`, `Re w > 1`, unconditional):

  `ζ(w)^{-1} = (4πb)^{-1/2} ∫_ℝ e^{-x²/(4b)} P_b(w − x) dx`

(termwise: `∫ e^{-x²/(4b)} n^{x} e^{-b log² n} dx = √(4πb)`). Inserted into the line form of the prime sum
`S_b(α) = (1/2π) ∫ LG(1/2−w) ζ(w)^{-1} (−ζ'(w)) dt` (`Re w = 2`) and swapped (`primeSumSym_eq_double`):

  `S_b(α) = (1/2π) (4πb)^{-1/2} ∫_ℝ e^{-x²/(4b)} I_x dx`,
  `I_x = ∫_ℝ LG(1/2 − w) P_b(w − x) (−ζ'(w)) dt`, `w = 2 + it`.

For each `x` the `w`-line may then be moved to `Re w = 1/2 + x`, where `P_b(w − x)` sits on the critical line
and `|LG(1/2 − w)| e^{-x²/(4b)} = √(π/b) (e^{-(t+α)²/(4b)} + e^{-(t−α)²/(4b)})` exactly: the two Gaussians
cancel. That is the smooth replacement for the sharp head identity.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace FleetSmoothWindow

open FleetLandauTransfer FleetHeadContour

/-! ## Decay helpers -/

lemma exp_neg_abs_le {k : ℝ} (hk : 0 < k) (x : ℝ) :
    Real.exp (-(k * |x|)) ≤ (1 + 2 / k ^ 2) * (1 + x ^ 2)⁻¹ := by
  have h := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ k * |x|)
  have hx2 : (k * |x|) ^ 2 = k ^ 2 * x ^ 2 := by rw [mul_pow, sq_abs]
  rw [hx2] at h
  have hpos : 0 < 1 + x ^ 2 := by positivity
  rw [Real.exp_neg, ← div_eq_mul_inv, inv_le_iff_one_le_mul₀ (Real.exp_pos _), div_mul_eq_mul_div,
    one_le_div hpos]
  have hk2 : 0 < k ^ 2 := by positivity
  have hkx : 0 ≤ k * |x| := by positivity
  have e : (1 + 2 / k ^ 2) * (1 + k ^ 2 * x ^ 2 / 2) = 1 + x ^ 2 + 2 / k ^ 2 + k ^ 2 * x ^ 2 / 2 := by
    field_simp; ring
  have h2 : 0 ≤ 2 / k ^ 2 + k ^ 2 * x ^ 2 / 2 := by positivity
  calc 1 + x ^ 2 ≤ (1 + 2 / k ^ 2) * (1 + k ^ 2 * x ^ 2 / 2) := by rw [e]; linarith
    _ ≤ (1 + 2 / k ^ 2) * Real.exp (k * |x|) := by
        gcongr; linarith

/-- `e^{-x²/(4b)} e^{(max 0 (x − d))²/(4b)} ≤ e^{d²/(4b)} e^{-d|x|/(2b)}`. -/
lemma gauss_max_le {b d : ℝ} (hb : 0 < b) (hd : 0 < d) (x : ℝ) :
    Real.exp (-x ^ 2 / (4 * b)) * Real.exp (max 0 (x - d) ^ 2 / (4 * b))
      ≤ Real.exp (d ^ 2 / (4 * b)) * Real.exp (-((d / (2 * b)) * |x|)) := by
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have key : -x ^ 2 + max 0 (x - d) ^ 2 ≤ d ^ 2 - 2 * d * |x| := by
    rcases le_total x d with h | h
    · rw [max_eq_left (by linarith)]
      rcases le_total 0 x with h0 | h0
      · rw [abs_of_nonneg h0]; nlinarith [sq_nonneg (x - d)]
      · rw [abs_of_nonpos h0]; nlinarith [sq_nonneg (x + d)]
    · rw [max_eq_right (by linarith), abs_of_nonneg (by linarith)]; nlinarith
  have e : d ^ 2 / (4 * b) + -(d / (2 * b) * |x|) = (d ^ 2 - 2 * d * |x|) / (4 * b) := by
    field_simp; ring
  rw [e, show -x ^ 2 / (4 * b) + max 0 (x - d) ^ 2 / (4 * b) = (-x ^ 2 + max 0 (x - d) ^ 2) / (4 * b) by ring]
  exact div_le_div_of_nonneg_right key (by positivity)

/-! ## `1/ζ` as a horizontal Gaussian average of `P_b` -/

lemma gauss_term_eq {b : ℝ} (hb : 0 < b) (w : ℂ) (x : ℝ) {n : ℕ} (hn : 0 < n) :
    ((Real.exp (-x ^ 2 / (4 * b)) : ℝ) : ℂ) * ((ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-(w - x))
        * (Real.exp (-b * Real.log n ^ 2) : ℂ))
      = (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-w)
        * ((Real.exp (-(x - 2 * b * Real.log n) ^ 2 / (4 * b)) : ℝ) : ℂ) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have e1 : (n : ℂ) ^ (-(w - x)) = (n : ℂ) ^ (-w) * (((Real.exp (x * Real.log n)) : ℝ) : ℂ) := by
    rw [show -(w - x) = -w + (x : ℂ) by ring, Complex.cpow_add _ _ hn0]
    congr 1
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow hnR.le,
      Real.rpow_def_of_pos hnR, mul_comm]
  rw [e1]
  have e2 : Real.exp (-x ^ 2 / (4 * b)) * Real.exp (x * Real.log n) * Real.exp (-b * Real.log n ^ 2)
      = Real.exp (-(x - 2 * b * Real.log n) ^ 2 / (4 * b)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; field_simp; ring
  rw [← e2]
  push_cast
  ring

/-- **`1/ζ(w) = (4πb)^{-1/2} ∫ e^{-x²/(4b)} P_b(w − x) dx`** for `Re w > 1`. -/
theorem invZeta_eq_gauss {b : ℝ} (hb : 0 < b) {w : ℂ} (hw : 1 < w.re) :
    (Real.sqrt (4 * π * b) : ℂ) * invZeta w
      = ∫ x : ℝ, ((Real.exp (-x ^ 2 / (4 * b)) : ℝ) : ℂ) * Psm b (w - x) := by
  set T : ℕ → ℝ → ℂ := fun n x => (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-w)
    * ((Real.exp (-(x - 2 * b * Real.log n) ^ 2 / (4 * b)) : ℝ) : ℂ) with hT
  have hpt : ∀ x : ℝ, ((Real.exp (-x ^ 2 / (4 * b)) : ℝ) : ℂ) * Psm b (w - x) = ∑' n : ℕ, T n x := by
    intro x
    unfold Psm
    rw [← tsum_mul_left]
    congr 1; funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hT]
    · exact gauss_term_eq hb w x hn
  have hTint : ∀ n, Integrable (T n) := fun n =>
    ((FleetHeadContour.integrable_gauss_shift hb (2 * b * Real.log n)).ofReal).const_mul _
  have hTnorm : ∀ n, ∫ x, ‖T n x‖ ≤ (n : ℝ) ^ (-w.re) * Real.sqrt (4 * π * b) := by
    intro n
    have hb' : ∀ x, ‖T n x‖ ≤ (n : ℝ) ^ (-w.re) * Real.exp (-(x - 2 * b * Real.log n) ^ 2 / (4 * b)) := by
      intro x
      simp only [hT, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have h1 := norm_term_moebius_le w n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp only [ArithmeticFunction.map_zero, Int.cast_zero, zero_mul, norm_zero]
        exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg 0) _) (Real.exp_pos _).le
      rw [term_moebius_eq hn.ne', norm_mul] at h1
      gcongr
    calc ∫ x, ‖T n x‖ ≤ ∫ x, (n : ℝ) ^ (-w.re) * Real.exp (-(x - 2 * b * Real.log n) ^ 2 / (4 * b)) :=
          integral_mono (hTint n).norm
            ((FleetHeadContour.integrable_gauss_shift hb _).const_mul _) hb'
      _ = _ := by rw [integral_const_mul, integral_gauss_shift hb]
  have hsum : Summable fun n => ∫ x, ‖T n x‖ :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg _) hTnorm
      ((Real.summable_nat_rpow.mpr (by linarith)).mul_right _)
  simp_rw [hpt]
  rw [← integral_tsum_of_summable_integral_norm hTint hsum, invZeta_eq_LSeries hw, LSeries,
    ← tsum_mul_left]
  congr 1; funext n
  simp only [hT]
  rw [integral_const_mul, integral_complex_ofReal, integral_gauss_shift hb]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [term_moebius_eq hn.ne']
  ring

/-! ## The prime sum on the line `Re w = 2` with `1/ζ` -/

/-- `F(t) = LG(1/2 − w)(−ζ'(w))` on `w = 2 + it`. -/
def Fline (b α : ℝ) (t : ℝ) : ℂ :=
  LGw b α (((2 : ℝ) : ℂ) + t * I) * (-deriv riemannZeta (((2 : ℝ) : ℂ) + t * I))

lemma integrable_Fline {b : ℝ} (hb : 0 < b) (α : ℝ) : Integrable (Fline b α) := by
  have h := integrable_line hb α (x := 2) (by norm_num) (by norm_num) (h := fun _ => (1 : ℂ))
    continuous_const (H := 1) (fun t => by simp)
  refine h.congr (ae_of_all _ fun t => ?_)
  simp [Fline]

lemma continuous_Fline (b α : ℝ) : Continuous (Fline b α) :=
  ((differentiable_LGw b α).continuous.comp (continuous_line 2)).mul
    (continuous_deriv_zeta_line (x := 2) (by norm_num)).neg

/-- **`S_b(α) = (1/2π) ∫ LG(1/2−w) ζ(w)^{-1} (−ζ'(w)) dt`** on `Re w = 2`. -/
theorem primeSumSym_eq_invZeta_line {b : ℝ} (hb : 0 < b) (α : ℝ) :
    FleetPrimeSideConsequences.primeSumSym b α
      = (1 / (2 * π) : ℂ) * ∫ t : ℝ, Fline b α t * invZeta (((2 : ℝ) : ℂ) + t * I) := by
  set G : ℕ → ℝ → ℂ := fun m t => (ArithmeticFunction.moebius m : ℂ) *
    (LGw b α (((2 : ℝ) : ℂ) + t * I) * (m : ℂ) ^ (-(((2 : ℝ) : ℂ) + t * I))
      * (-deriv riemannZeta (((2 : ℝ) : ℂ) + t * I))) with hG
  have hGint : ∀ m, Integrable (G m) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hG]
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    refine Integrable.const_mul ?_ _
    refine integrable_line hb α (x := 2) (by norm_num) (by norm_num)
      (h := fun t => (m : ℂ) ^ (-(((2 : ℝ) : ℂ) + t * I))) ?_ (H := (m : ℝ) ^ (-(2 : ℝ))) ?_
    · have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hmR.ne'
      exact (continuous_line 2).neg.const_cpow (Or.inl hm0)
    · intro t
      have := norm_ofReal_cpow_line hmR 2 t
      rw [show ((m : ℝ) : ℂ) = (m : ℂ) by push_cast; rfl] at this
      exact this.le
  have hGnorm : ∀ m, ∫ t, ‖G m t‖ ≤ (m : ℝ) ^ (-(2 : ℝ)) * ∫ t, ‖Fline b α t‖ := by
    intro m
    rw [← integral_const_mul]
    refine integral_mono (hGint m).norm ((integrable_Fline hb α).norm.const_mul _) fun t => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hG]
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    simp only [hG, Fline, norm_mul]
    have h1 : ‖(ArithmeticFunction.moebius m : ℂ)‖ ≤ 1 := by
      rw [show (ArithmeticFunction.moebius m : ℂ) = ((ArithmeticFunction.moebius m : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have h2 : ‖(m : ℂ) ^ (-(((2 : ℝ) : ℂ) + t * I))‖ = (m : ℝ) ^ (-(2 : ℝ)) := by
      have := norm_ofReal_cpow_line hmR 2 t
      rwa [show ((m : ℝ) : ℂ) = (m : ℂ) by push_cast; rfl] at this
    rw [h2]
    have := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ ‖LGw b α (((2 : ℝ) : ℂ) + t * I)‖
      * (m : ℝ) ^ (-(2 : ℝ)) * ‖-deriv riemannZeta (((2 : ℝ) : ℂ) + t * I)‖)
    nlinarith
  have hsum : Summable fun m => ∫ t, ‖G m t‖ :=
    Summable.of_nonneg_of_le (fun m => integral_nonneg fun t => norm_nonneg _) hGnorm
      ((Real.summable_nat_rpow.mpr (by norm_num)).mul_right _)
  have hstep : ∀ m : ℕ, (((ArithmeticFunction.moebius m : ℝ) * FleetMollifierTail.inner b α m : ℝ) : ℂ)
      = (1 / (2 * π) : ℂ) * ∫ t, G m t := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hG]
    rw [Complex.ofReal_mul, inner_eq_line_integral hb α hm (c := 2) (by norm_num)]
    simp only [hG]
    rw [integral_const_mul]
    push_cast
    ring
  rw [FleetFiniteHeadRH.primeSumSym_eq_inner hb α, Complex.ofReal_tsum, tsum_congr hstep, tsum_mul_left,
    integral_tsum_of_summable_integral_norm hGint hsum]
  congr 1; congr 1; funext t
  have hw : 1 < ((((2 : ℝ) : ℂ) + t * I)).re := by norm_num
  rw [invZeta_eq_LSeries hw, LSeries, Fline, ← tsum_mul_left]
  congr 1; funext m
  simp only [hG]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  rw [term_moebius_eq hm.ne']
  ring

/-! ## Swapping the two integrals -/

/-- `I_x = ∫ LG(1/2 − w) P_b(w − x) (−ζ'(w)) dt`, `w = 2 + it`. -/
def Ix (b α x : ℝ) : ℂ :=
  ∫ t : ℝ, Fline b α t * Psm b ((((2 : ℝ) : ℂ) + t * I) - x)

lemma norm_Psm_shift_le {b : ℝ} (hb : 0 < b) (t x : ℝ) :
    ‖Psm b ((((2 : ℝ) : ℂ) + t * I) - x)‖ ≤ Sz (1 / 2) * Real.exp (max 0 (x - 1 / 2) ^ 2 / (4 * b)) := by
  have h := norm_Psm_le hb (η := 1 / 2) (by norm_num) ((((2 : ℝ) : ℂ) + t * I) - x)
  have hre : ((((2 : ℝ) : ℂ) + t * I) - x).re = 2 - x := by simp
  rw [hre, show (1 + 1 / 2 - (2 - x) : ℝ) = x - 1 / 2 by ring] at h
  exact h

/-- The `x`-majorant `e^{-x²/(4b)} S e^{(max 0 (x−1/2))²/(4b)}` is integrable. -/
lemma integrable_xmaj {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => Real.exp (-x ^ 2 / (4 * b)) *
      (Sz (1 / 2) * Real.exp (max 0 (x - 1 / 2) ^ 2 / (4 * b)))) := by
  set k := (1 / 2) / (2 * b)
  have hk : 0 < k := by positivity
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul
    (Sz (1 / 2) * Real.exp ((1 / 2) ^ 2 / (4 * b)) * (1 + 2 / k ^ 2))) ?_ (ae_of_all _ fun x => ?_)
  · exact (by fun_prop : Continuous (fun x : ℝ => Real.exp (-x ^ 2 / (4 * b)) *
      (Sz (1 / 2) * Real.exp (max 0 (x - 1 / 2) ^ 2 / (4 * b))))).aestronglyMeasurable
  · have h1 := gauss_max_le hb (by norm_num : (0 : ℝ) < 1 / 2) x
    have h2 := exp_neg_abs_le hk x
    have hS := Sz_nonneg (1 / 2)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc Real.exp (-x ^ 2 / (4 * b)) * (Sz (1 / 2) * Real.exp (max 0 (x - 1 / 2) ^ 2 / (4 * b)))
        = Sz (1 / 2) * (Real.exp (-x ^ 2 / (4 * b)) * Real.exp (max 0 (x - 1 / 2) ^ 2 / (4 * b))) := by ring
      _ ≤ Sz (1 / 2) * (Real.exp ((1 / 2) ^ 2 / (4 * b)) * Real.exp (-(k * |x|))) := by gcongr
      _ ≤ Sz (1 / 2) * (Real.exp ((1 / 2) ^ 2 / (4 * b)) * ((1 + 2 / k ^ 2) * (1 + x ^ 2)⁻¹)) := by gcongr
      _ = _ := by ring

/-- **The exact identity**: `S_b(α) = (1/2π) (4πb)^{-1/2} ∫ e^{-x²/(4b)} I_x dx`. -/
theorem primeSumSym_eq_double {b : ℝ} (hb : 0 < b) (α : ℝ) :
    (Real.sqrt (4 * π * b) : ℂ) * FleetPrimeSideConsequences.primeSumSym b α
      = (1 / (2 * π) : ℂ) * ∫ x : ℝ, ((Real.exp (-x ^ 2 / (4 * b)) : ℝ) : ℂ) * Ix b α x := by
  rw [primeSumSym_eq_invZeta_line hb α, ← mul_assoc, mul_comm (Real.sqrt (4 * π * b) : ℂ), mul_assoc,
    ← integral_const_mul]
  congr 1
  have hpt : ∀ t : ℝ, (Real.sqrt (4 * π * b) : ℂ) * (Fline b α t * invZeta (((2 : ℝ) : ℂ) + t * I))
      = ∫ x : ℝ, Fline b α t * (((Real.exp (-x ^ 2 / (4 * b)) : ℝ) : ℂ)
          * Psm b ((((2 : ℝ) : ℂ) + t * I) - x)) := by
    intro t
    have hw : 1 < ((((2 : ℝ) : ℂ) + t * I)).re := by norm_num
    rw [integral_const_mul, ← invZeta_eq_gauss hb hw]
    ring
  simp_rw [hpt]
  rw [integral_integral_swap]
  · congr 1; funext x
    unfold Ix
    rw [← integral_const_mul]
    congr 1; funext t
    ring
  · -- joint integrability
    have hmaj := (integrable_Fline hb α).norm.mul_prod (integrable_xmaj hb)
    refine hmaj.mono' ?_ (ae_of_all _ fun p => ?_)
    · have hc : Continuous (fun p : ℝ × ℝ => Fline b α p.1 * (((Real.exp (-p.2 ^ 2 / (4 * b)) : ℝ) : ℂ)
          * Psm b ((((2 : ℝ) : ℂ) + p.1 * I) - p.2))) := by
        refine ((continuous_Fline b α).comp continuous_fst).mul ?_
        refine Continuous.mul (by fun_prop) ((continuous_Psm hb).comp ?_)
        fun_prop
      exact hc.aestronglyMeasurable
    · obtain ⟨t, x⟩ := p
      show ‖Fline b α t * (((Real.exp (-x ^ 2 / (4 * b)) : ℝ) : ℂ) * Psm b ((((2 : ℝ) : ℂ) + t * I) - x))‖
        ≤ ‖Fline b α t‖ * (Real.exp (-x ^ 2 / (4 * b)) *
            (Sz (1 / 2) * Real.exp (max 0 (x - 1 / 2) ^ 2 / (4 * b))))
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have h := norm_Psm_shift_le hb t x
      have := norm_nonneg (Fline b α t)
      have := Real.exp_pos (-x ^ 2 / (4 * b))
      gcongr

end FleetSmoothWindow
