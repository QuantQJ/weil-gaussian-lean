import FleetSmoothWindowStrip
import FleetWindowLowerBound
import FleetLowZeroFree
import Mathlib

/-!
# A positive lower bound for the smooth window; no negative smooth window rate

`smoothWindow b α = ∫ ‖P_b(1/2+it)‖² e^{-(t−α)²/(4b)} dt`, `P_b(s) = Σ μ(n) n^{-s} e^{-b log² n}`.

* `smoothWindow_lower` : there is `b₀ > 0` with `smoothWindow b 0 ≥ κ √b` for `0 < b ≤ b₀`,
  `κ = √(4π) (|1/ζ(1/2)|/2)² > 0`. No hypothesis.
* `not_smoothWindowRate_of_neg` : `¬ SmoothWindowRate c` for every `c < 0`; `smoothWindowRate_nonneg`;
  `zeroDev_sq_half_le_of_smoothWindowRate` / `not_smoothWindowRate_of_lt'` (no `c ≥ 0` side condition);
  `sInf_smoothWindowRate_eq`.

Method.
1. Cauchy–Schwarz against the constant: `∫ P_b(1/2+it) e^{-t²/4b} dt = √(4πb) P_{2b}(1/2)` (termwise Gaussian
   integrals, `integral_Psm_gauss`), so `smoothWindow b 0 ≥ √(4πb) |P_{2b}(1/2)|²` (`smoothWindow_zero_ge`).
2. `P_β(1/2) → 1/ζ(1/2)` as `β → 0` (`Psm_half_err`): `√(4πβ) P_β(1/2) = ∫ e^{(5/4+iy−1/2)²/4β} (1/ζ)(5/4+iy) dy`
   (`Psm_eq_line`); on the rectangle `[1/2, 5/4] × [−1, 1]` `ζ` has no zeros (Mathlib for `Re ≥ 1`,
   `FleetLowZeroFree.zeta_ne_zero_low` for `|Im| ≤ 3/2`), so the segment `|y| ≤ 1` moves to `Re = 1/2`, where the
   kernel is the real Gaussian `e^{-y²/4β}`; the horizontal sides and the tails `|y| ≥ 1` on `Re = 5/4` are
   `O(e^{-7/(128β)})`, and `1/ζ(1/2+iy) − 1/ζ(1/2) = O(|y|)` gives `O(β)`. Result:
   `‖√(4πβ)(P_β(1/2) − 1/ζ(1/2))‖ ≤ 8√π L β + K e^{-7/(128β)}`.
3. `ζ(1/2) ≠ 0`, so `|P_{2b}(1/2)| ≥ |1/ζ(1/2)|/2` for small `b`.

The zero of `FleetFirstZero` is not used; what is used is the absence of zeros near `s = 1/2`.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace FleetSmoothWindowLower
open FleetSmoothWindow FleetHeadContour FleetLandauTransfer

/-! ## Pairing the smooth sum with the Gaussian weight -/

/-- `L = log n`, `n^{-(1/2+it)} = e^{-(1/2+it) L}` for `n ≥ 1`. -/
lemma integral_term_gauss {b : ℝ} (hb : 0 < b) {n : ℕ} (hn : 0 < n) :
    ∫ t : ℝ, (n : ℂ) ^ (-((1 / 2 : ℂ) + t * I)) * ((Real.exp (-(t - 0) ^ 2 / (4 * b)) : ℝ) : ℂ)
      = (Real.sqrt (4 * π * b) : ℂ) * ((n : ℂ) ^ (-(1 / 2 : ℂ)) * ((Real.exp (-b * Real.log n ^ 2) : ℝ) : ℂ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := integral_quad hb 0 (1 / 2) (Real.log n)
  have e1 : ∀ t : ℝ, (n : ℂ) ^ (-((1 / 2 : ℂ) + t * I)) * ((Real.exp (-(t - 0) ^ 2 / (4 * b)) : ℝ) : ℂ)
      = cexp ((0 + t * I) ^ 2 / (4 * b)) * cexp (-(((1 / 2 : ℝ) : ℂ) + t * I) * (Real.log n : ℝ)) := by
    intro t
    have := cpow_eq_cexp hnR ((1 / 2 : ℂ) + t * I)
    push_cast at this ⊢
    rw [this, mul_comm]
    congr 1
    congr 1
    rw [zero_add, mul_pow, Complex.I_sq]; ring
  simp_rw [e1]
  rw [h]
  congr 1
  have := cpow_eq_cexp hnR (1 / 2 : ℂ)
  push_cast at this ⊢
  rw [this, ← Complex.exp_add]
  congr 1
  ring

lemma norm_term_le (b : ℝ) (n : ℕ) (t : ℝ) :
    ‖(ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-((1 / 2 : ℂ) + t * I))
        * ((Real.exp (-b * Real.log n ^ 2) : ℝ) : ℂ) * ((Real.exp (-(t - 0) ^ 2 / (4 * b)) : ℝ) : ℂ)‖
      ≤ ((n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-b * Real.log n ^ 2)) * Real.exp (-(t - 0) ^ 2 / (4 * b)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [norm_mul, norm_mul, norm_mul, norm_natCast_cpow_of_pos hn, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
  have hμ : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    rw [show (ArithmeticFunction.moebius n : ℂ) = ((ArithmeticFunction.moebius n : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs]
    exact FleetMollifierTail.moebius_abs_le n
  have hre : (-((1 / 2 : ℂ) + t * I)).re = -(1 / 2 : ℝ) := by simp
  rw [hre]
  have h1 : 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
  have h2 := Real.exp_pos (-b * Real.log n ^ 2)
  have h3 := Real.exp_pos (-(t - 0) ^ 2 / (4 * b))
  calc ‖(ArithmeticFunction.moebius n : ℂ)‖ * (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-b * Real.log n ^ 2)
        * Real.exp (-(t - 0) ^ 2 / (4 * b))
      ≤ 1 * (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-b * Real.log n ^ 2) * Real.exp (-(t - 0) ^ 2 / (4 * b)) := by
        gcongr
    _ = _ := by ring

lemma coef_le {b : ℝ} (hb : 0 < b) (n : ℕ) :
    (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-b * Real.log n ^ 2) ≤ Real.exp (1 / b) * (n : ℝ) ^ (-(5 / 2 : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow (by norm_num : (-(5 / 2 : ℝ)) ≠ 0)]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set L := Real.log n
  rw [Real.rpow_def_of_pos hnR, Real.rpow_def_of_pos hnR, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have key : b * L ^ 2 - 2 * L + 1 / b = (b * L - 1) ^ 2 / b := by field_simp; ring
  have h0 : 0 ≤ (b * L - 1) ^ 2 / b := by positivity
  nlinarith

/-- **`∫ P_b(1/2+it) e^{-t²/4b} dt = √(4πb) P_{2b}(1/2)`.** -/
theorem integral_Psm_gauss {b : ℝ} (hb : 0 < b) :
    ∫ t : ℝ, Psm b (((1 / 2 : ℝ) : ℂ) + t * I) * ((Real.exp (-(t - 0) ^ 2 / (4 * b)) : ℝ) : ℂ)
      = (Real.sqrt (4 * π * b) : ℂ) * Psm (2 * b) (1 / 2) := by
  set F : ℕ → ℝ → ℂ := fun n t => (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-((1 / 2 : ℂ) + t * I))
        * ((Real.exp (-b * Real.log n ^ 2) : ℝ) : ℂ) * ((Real.exp (-(t - 0) ^ 2 / (4 * b)) : ℝ) : ℂ) with hF
  have hcont : ∀ n, Continuous (F n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [hF]; simp only [Nat.cast_zero, ArithmeticFunction.map_zero, Int.cast_zero, zero_mul]
      exact continuous_const
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    simp only [hF]
    refine ((continuous_const.mul ?_).mul continuous_const).mul (by fun_prop)
    exact (by fun_prop : Continuous fun t : ℝ => -((1 / 2 : ℂ) + t * I)).const_cpow (Or.inl hn0)
  have hFint : ∀ n, Integrable (F n) := fun n =>
    Integrable.mono' ((integrable_gauss_shift hb 0).const_mul _) (hcont n).aestronglyMeasurable
      (ae_of_all _ fun t => norm_term_le b n t)
  have hFsum : Summable fun n => ∫ t, ‖F n t‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _) (fun n => ?_)
      (((Real.summable_nat_rpow.mpr (by norm_num : -(5 / 2 : ℝ) < -1)).mul_left (Real.exp (1 / b))).mul_right
        (Real.sqrt (4 * π * b)))
    calc ∫ t, ‖F n t‖ ≤ ∫ t, ((n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-b * Real.log n ^ 2))
          * Real.exp (-(t - 0) ^ 2 / (4 * b)) :=
          integral_mono (hFint n).norm ((integrable_gauss_shift hb 0).const_mul _) (norm_term_le b n)
      _ = ((n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (-b * Real.log n ^ 2)) * Real.sqrt (4 * π * b) := by
          rw [integral_const_mul, integral_gauss_shift hb]
      _ ≤ _ := mul_le_mul_of_nonneg_right (coef_le hb n) (Real.sqrt_nonneg _)
  have hpt : ∀ t : ℝ, Psm b (((1 / 2 : ℝ) : ℂ) + t * I) * ((Real.exp (-(t - 0) ^ 2 / (4 * b)) : ℝ) : ℂ)
      = ∑' n, F n t := by
    intro t
    unfold Psm
    rw [← tsum_mul_right]
    congr 1; funext n
    simp only [hF]; push_cast; ring
  simp_rw [hpt]
  rw [← integral_tsum_of_summable_integral_norm hFint hFsum]
  have hterm : ∀ n, ∫ t, F n t = (Real.sqrt (4 * π * b) : ℂ) * ((ArithmeticFunction.moebius n : ℂ)
      * (n : ℂ) ^ (-(1 / 2 : ℂ)) * ((Real.exp (-(2 * b) * Real.log n ^ 2) : ℝ) : ℂ)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hF]
    have e : F n = fun t : ℝ => ((ArithmeticFunction.moebius n : ℂ) * ((Real.exp (-b * Real.log n ^ 2) : ℝ) : ℂ))
        * ((n : ℂ) ^ (-((1 / 2 : ℂ) + t * I)) * ((Real.exp (-(t - 0) ^ 2 / (4 * b)) : ℝ) : ℂ)) := by
      funext t; simp only [hF]; ring
    rw [e, integral_const_mul, integral_term_gauss hb hn]
    have e2 : ((Real.exp (-(2 * b) * Real.log n ^ 2) : ℝ) : ℂ)
        = ((Real.exp (-b * Real.log n ^ 2) : ℝ) : ℂ) * ((Real.exp (-b * Real.log n ^ 2) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring
    rw [e2]; ring
  simp_rw [hterm]
  rw [tsum_mul_left]
  unfold Psm
  congr 1


/-! ## `1/ζ` near `s = 1/2` -/

lemma zeta_ne_zero_box {s : ℂ} (h1 : 1 / 4 < s.re) (h2 : |s.im| ≤ 3 / 2) : riemannZeta s ≠ 0 := by
  by_cases h : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h
  · exact FleetLowZeroFree.zeta_ne_zero_low (by linarith) (by linarith) h2

lemma invZeta_diff_box {s : ℂ} (h1 : 1 / 4 < s.re) (h2 : |s.im| ≤ 3 / 2) : DifferentiableAt ℂ invZeta s :=
  invZeta_differentiableAt (Or.inr (zeta_ne_zero_box h1 h2))

/-- The open box on which `1/ζ` is used. -/
def Ubox : Set ℂ := (Ioo (1 / 4 : ℝ) 2) ×ℂ (Ioo (-(5 / 4) : ℝ) (5 / 4))

lemma isOpen_Ubox : IsOpen Ubox := isOpen_Ioo.reProdIm isOpen_Ioo

lemma diffOn_Ubox : DifferentiableOn ℂ invZeta Ubox := by
  intro z hz
  obtain ⟨⟨h1, _⟩, ⟨h3, h4⟩⟩ := hz
  exact (invZeta_diff_box h1 (by rw [abs_le]; constructor <;> linarith)).differentiableWithinAt

lemma exists_Kh : ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Icc (1 / 2 : ℝ) (5 / 4), ∀ y ∈ Icc (-1 : ℝ) 1,
    ‖invZeta ((x : ℂ) + y * I)‖ ≤ K := by
  have hc : IsCompact ((Icc (1 / 2 : ℝ) (5 / 4)) ×ℂ (Icc (-1 : ℝ) 1)) := isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn invZeta ((Icc (1 / 2 : ℝ) (5 / 4)) ×ℂ (Icc (-1 : ℝ) 1)) := by
    intro z hz
    obtain ⟨⟨h1, _⟩, ⟨h3, h4⟩⟩ := hz
    exact (invZeta_diff_box (by linarith) (by rw [abs_le]; constructor <;> linarith)).continuousAt.continuousWithinAt
  obtain ⟨K, hK⟩ := hc.exists_bound_of_continuousOn hcont
  refine ⟨max K 0, le_max_right _ _, fun x hx y hy => ?_⟩
  refine (hK _ ?_).trans (le_max_left _ _)
  exact ⟨by simpa using hx, by simpa using hy⟩

lemma exists_L : ∃ L : ℝ, 0 ≤ L ∧ ∀ y ∈ Icc (-1 : ℝ) 1, ‖deriv invZeta ((1 / 2 : ℂ) + y * I)‖ ≤ L := by
  have han := diffOn_Ubox.analyticOnNhd isOpen_Ubox
  have hdc : ContinuousOn (deriv invZeta) Ubox := han.deriv.continuousOn
  set p : ℝ → ℂ := fun y => (1 / 2 : ℂ) + y * I
  have hpc : Continuous p := by fun_prop
  have hsub : p '' Icc (-1 : ℝ) 1 ⊆ Ubox := by
    rintro _ ⟨y, ⟨h1, h2⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp [p] <;> norm_num <;> linarith
  obtain ⟨L, hL⟩ := (isCompact_Icc.image hpc).exists_bound_of_continuousOn (hdc.mono hsub)
  exact ⟨max L 0, le_max_right _ _, fun y hy => (hL _ ⟨y, hy, rfl⟩).trans (le_max_left _ _)⟩

lemma invZeta_lip {L : ℝ} (hL : ∀ y ∈ Icc (-1 : ℝ) 1, ‖deriv invZeta ((1 / 2 : ℂ) + y * I)‖ ≤ L)
    {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    ‖invZeta ((1 / 2 : ℂ) + y * I) - invZeta (1 / 2)‖ ≤ L * |y| := by
  have hd : ∀ x ∈ Icc (-1 : ℝ) 1, HasDerivWithinAt (fun y : ℝ => invZeta ((1 / 2 : ℂ) + y * I))
      (deriv invZeta ((1 / 2 : ℂ) + x * I) * I) (Icc (-1 : ℝ) 1) x := by
    intro x hx
    have hz : DifferentiableAt ℂ invZeta ((1 / 2 : ℂ) + x * I) := by
      refine invZeta_diff_box (by simp; norm_num) ?_
      simp; rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
    have hp : HasDerivAt (fun y : ℝ => (1 / 2 : ℂ) + y * I) I x := by
      simpa using ((hasDerivAt_id x).ofReal_comp.mul_const I).const_add (1 / 2 : ℂ)
    exact (hz.hasDerivAt.comp x hp).hasDerivWithinAt
  have hb : ∀ x ∈ Icc (-1 : ℝ) 1, ‖deriv invZeta ((1 / 2 : ℂ) + x * I) * I‖ ≤ L := by
    intro x hx; rw [norm_mul, Complex.norm_I, mul_one]; exact hL x hx
  have h0 : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb h0 hy
  simpa [Real.norm_eq_abs] using h


/-! ## `P_b(1/2) → 1/ζ(1/2)` as `b → 0` -/

lemma hZ_one : ∀ s : ℂ, 1 / 2 + 1 / 2 < s.re → riemannZeta s ≠ 0 :=
  fun s hs => riemannZeta_ne_zero_of_one_lt_re (by linarith)

lemma exists_C : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℂ, 5 / 4 ≤ u.re → ‖invZeta u‖ ≤ C * (1 + |u.im|) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, h⟩ := invZeta_bound (δ₀ := 1 / 2) (by norm_num) hZ_one (σ₀ := 5 / 4) (by norm_num)
    (η := 1 / 2) (by norm_num)
  exact ⟨C, hC.le, h⟩

/-- Tail bound on `Re = 5/4`, `|y| ≥ 1`. -/
lemma tail_pt {b C : ℝ} (hb : 0 < b) (hC : 0 ≤ C)
    (hbd : ∀ u : ℂ, 5 / 4 ≤ u.re → ‖invZeta u‖ ≤ C * (1 + |u.im|) ^ (1 / 2 : ℝ)) {y : ℝ} (hy : 1 ≤ |y|) :
    ‖gline b (1 / 2) (((5 / 4 : ℝ) : ℂ) + y * I)‖
      ≤ C * Real.exp (-(7 / (128 * b))) * (Real.exp (2 * (32 * b / 7))
          * Real.exp (-(y - 0) ^ 2 / (4 * (2 * (32 * b / 7))))) := by
  have h := norm_gline_le (b := b) hbd hC (1 / 2 : ℂ) (x := 5 / 4) le_rfl y
  have hre : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
  have him : (1 / 2 : ℂ).im = 0 := by norm_num
  rw [hre, him] at h
  refine h.trans ?_
  have hb' : 0 < 32 * b / 7 := by positivity
  have hg := one_add_abs_le_exp_gauss hb' y
  have hy2 : 1 ≤ y ^ 2 := by nlinarith [sq_abs y, abs_nonneg y]
  have hexp : Real.exp (((5 / 4 - 1 / 2 : ℝ) ^ 2 - (y - 0) ^ 2) / (4 * b))
      ≤ Real.exp (-(7 / (128 * b))) * Real.exp (-y ^ 2 / (4 * (32 * b / 7))) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have e : -(7 / (128 * b)) + -y ^ 2 / (4 * (32 * b / 7)) = (-7 - 7 * y ^ 2) / (128 * b) := by
      field_simp; ring
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hpos := Real.exp_pos (-(7 / (128 * b)))
  calc Real.exp (((5 / 4 - 1 / 2 : ℝ) ^ 2 - (y - 0) ^ 2) / (4 * b)) * (C * (1 + |y|))
      ≤ (Real.exp (-(7 / (128 * b))) * Real.exp (-y ^ 2 / (4 * (32 * b / 7)))) * (C * (1 + |y|)) :=
        mul_le_mul_of_nonneg_right hexp (by positivity)
    _ = C * Real.exp (-(7 / (128 * b))) * ((1 + |y|) * Real.exp (-y ^ 2 / (4 * (32 * b / 7)))) := by ring
    _ ≤ C * Real.exp (-(7 / (128 * b))) * (Real.exp (2 * (32 * b / 7))
          * Real.exp (-y ^ 2 / (4 * (2 * (32 * b / 7))))) := by gcongr
    _ = _ := by simp

/-- Bound for a set integral by the full integral of a nonnegative integrable majorant. -/
lemma norm_setIntegral_le_full {S : Set ℝ} (hS : MeasurableSet S) {F : ℝ → ℂ} {G : ℝ → ℝ}
    (hG : Integrable G) (hG0 : ∀ y, 0 ≤ G y) (h : ∀ y ∈ S, ‖F y‖ ≤ G y) :
    ‖∫ y in S, F y‖ ≤ ∫ y, G y := by
  refine (norm_integral_le_of_norm_le hG.integrableOn (ae_restrict_of_forall_mem hS h)).trans ?_
  exact setIntegral_le_integral hG (ae_of_all _ hG0)


/-- `∫ F = ∫_{y ≤ −1} F + ∫_{−1}^{1} F + ∫_{y > 1} F`. -/
lemma split3 {F : ℝ → ℂ} (hF : Integrable F) :
    ∫ y, F y = (∫ y in Iic (-1 : ℝ), F y) + (∫ y in (-1 : ℝ)..1, F y) + ∫ y in Ioi (1 : ℝ), F y := by
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := -1) hF.integrableOn hF.integrableOn,
    ← intervalIntegral.integral_interval_add_Ioi (a := -1) (b := 1) hF.integrableOn hF.integrableOn]
  ring

/-- `|y| e^{-y²/4b} ≤ √(8b) e^{-y²/8b}`. -/
lemma abs_mul_gauss_le {b : ℝ} (hb : 0 < b) (y : ℝ) :
    |y| * Real.exp (-(y - 0) ^ 2 / (4 * b)) ≤ Real.sqrt (8 * b) * Real.exp (-(y - 0) ^ 2 / (4 * (2 * b))) := by
  have h := sq_gauss_le (b := b / 2) (by positivity) y
  have hl : 0 ≤ |y| * Real.exp (-(y - 0) ^ 2 / (4 * b)) := by positivity
  have hr : 0 ≤ Real.sqrt (8 * b) * Real.exp (-(y - 0) ^ 2 / (4 * (2 * b))) := by positivity
  refine (pow_le_pow_iff_left₀ hl hr (by norm_num : (2 : ℕ) ≠ 0)).mp ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), sq_abs, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
  have e1 : ((2 : ℕ) : ℝ) * (-(y - 0) ^ 2 / (4 * b)) = -y ^ 2 / (4 * (b / 2)) := by
    push_cast; field_simp; ring
  have e2 : ((2 : ℕ) : ℝ) * (-(y - 0) ^ 2 / (4 * (2 * b))) = -y ^ 2 / (8 * (b / 2)) := by
    push_cast; field_simp; ring
  rw [e1, e2]
  nlinarith [Real.exp_pos (-y ^ 2 / (8 * (b / 2)))]

/-- **Main estimate**: `‖√(4πb) (P_b(1/2) − 1/ζ(1/2))‖ ≤ 8√π L b + K e^{-7/(128 b)}` for `0 < b ≤ 1`. -/
theorem Psm_half_err : ∃ L K : ℝ, 0 ≤ L ∧ 0 ≤ K ∧ ∀ b : ℝ, 0 < b → b ≤ 1 →
    ‖(Real.sqrt (4 * π * b) : ℂ) * (Psm b (1 / 2) - invZeta (1 / 2))‖
      ≤ 8 * Real.sqrt π * L * b + K * Real.exp (-(7 / (128 * b))) := by
  obtain ⟨C, hC, hbd⟩ := exists_C
  obtain ⟨Kh, hKh, hKhb⟩ := exists_Kh
  obtain ⟨L, hL0, hL⟩ := exists_L
  set g0 := invZeta (1 / 2)
  set Kt := C * Real.exp (64 / 7) * Real.sqrt (4 * π * (2 * (32 / 7))) with hKt
  refine ⟨L, 2 * Kt + 2 * (3 / 4 * Kh) + 2 * (‖g0‖ * Real.sqrt (4 * π * (2 * 1))), hL0, by positivity,
    fun b hb hb1 => ?_⟩
  set f : ℂ → ℂ := gline b (1 / 2) with hf
  set G : ℝ → ℝ := fun y => Real.exp (-(y - 0) ^ 2 / (4 * b)) with hG
  have hGi : Integrable G := integrable_gauss_shift hb 0
  have hGc : Integrable (fun y : ℝ => ((G y : ℝ) : ℂ)) := hGi.ofReal
  have hf5 : Integrable (fun y : ℝ => f (((5 / 4 : ℝ) : ℂ) + y * I)) :=
    integrable_gline_line hb hZ_one hbd hC (by norm_num) (1 / 2) le_rfl
  -- the two representations
  have hP := Psm_eq_line hb (1 / 2 : ℂ) (σ := 5 / 4) (by norm_num)
  have hS : (Real.sqrt (4 * π * b) : ℂ) = ∫ y, ((G y : ℝ) : ℂ) := by
    rw [integral_complex_ofReal, integral_gauss_shift hb]
  -- the rectangle
  have hdiff : ∀ z : ℂ, (1 / 2 : ℝ) ≤ z.re → z.re ≤ 5 / 4 → (-1 : ℝ) ≤ z.im → z.im ≤ 1 →
      DifferentiableAt ℂ f z := by
    intro z h1 _ h3 h4
    exact (by fun_prop : DifferentiableAt ℂ (fun u : ℂ => cexp ((u - 1 / 2) ^ 2 / (4 * b))) z).mul
      (invZeta_diff_box (by linarith) (by rw [abs_le]; constructor <;> linarith))
  have hrect := rect_zero (f := f) (a₁ := 1 / 2) (a₂ := 5 / 4) (y₁ := -1) (y₂ := 1) (by norm_num) (by norm_num)
    hdiff
  set bot := ∫ x in (1 / 2 : ℝ)..(5 / 4), f ((x : ℂ) + ((-1 : ℝ) : ℂ) * I)
  set top := ∫ x in (1 / 2 : ℝ)..(5 / 4), f ((x : ℂ) + ((1 : ℝ) : ℂ) * I)
  set A := ∫ y in (-1 : ℝ)..1, f (((5 / 4 : ℝ) : ℂ) + y * I)
  set B := ∫ y in (-1 : ℝ)..1, f (((1 / 2 : ℝ) : ℂ) + y * I)
  have hAB : A = B + I * (bot - top) := by
    have hI2 : I * I = -1 := I_mul_I
    linear_combination (-I) * hrect + (A - B) * hI2
  -- the critical segment
  have hseg : ∀ y : ℝ, f (((1 / 2 : ℝ) : ℂ) + y * I) = ((G y : ℝ) : ℂ) * invZeta ((1 / 2 : ℂ) + y * I) := by
    intro y
    simp only [hf, gline, hG]
    rw [Complex.ofReal_exp]
    push_cast
    congr 2
    rw [add_sub_cancel_left, mul_pow, Complex.I_sq]; ring
  have hcontg : ContinuousOn (fun y : ℝ => invZeta ((1 / 2 : ℂ) + y * I)) (uIcc (-1 : ℝ) 1) := by
    intro y hy
    rw [uIcc_of_le (by norm_num)] at hy
    refine ((invZeta_diff_box (by simp; norm_num) ?_).continuousAt.comp
      (by fun_prop : Continuous fun y : ℝ => (1 / 2 : ℂ) + y * I).continuousAt).continuousWithinAt
    simp; rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
  have hGcc : Continuous fun y : ℝ => ((G y : ℝ) : ℂ) := Complex.continuous_ofReal.comp (by fun_prop)
  have hBint : IntervalIntegrable (fun y : ℝ => f (((1 / 2 : ℝ) : ℂ) + y * I)) volume (-1) 1 := by
    simp_rw [hseg]
    exact (hGcc.continuousOn.mul hcontg).intervalIntegrable
  have hGMint : IntervalIntegrable (fun y : ℝ => g0 * ((G y : ℝ) : ℂ)) volume (-1) 1 :=
    (continuous_const.mul hGcc).intervalIntegrable _ _
  -- the decomposition
  set T1 := ∫ y in Iic (-1 : ℝ), f (((5 / 4 : ℝ) : ℂ) + y * I)
  set T2 := ∫ y in Ioi (1 : ℝ), f (((5 / 4 : ℝ) : ℂ) + y * I)
  set GLt := ∫ y in Iic (-1 : ℝ), ((G y : ℝ) : ℂ)
  set GMt := ∫ y in (-1 : ℝ)..1, ((G y : ℝ) : ℂ)
  set GRt := ∫ y in Ioi (1 : ℝ), ((G y : ℝ) : ℂ)
  set D := ∫ y in (-1 : ℝ)..1, (f (((1 / 2 : ℝ) : ℂ) + y * I) - g0 * ((G y : ℝ) : ℂ))
  have hD : D = B - g0 * GMt := by
    simp only [D]
    rw [intervalIntegral.integral_sub hBint hGMint, intervalIntegral.integral_const_mul]
  have hdec : (Real.sqrt (4 * π * b) : ℂ) * (Psm b (1 / 2) - g0)
      = (T1 - g0 * GLt) + (T2 - g0 * GRt) + D + I * (bot - top) := by
    have h1 : (Real.sqrt (4 * π * b) : ℂ) * Psm b (1 / 2) = T1 + A + T2 := by
      rw [hP]; exact split3 hf5
    have h2 : (Real.sqrt (4 * π * b) : ℂ) = GLt + GMt + GRt := by rw [hS]; exact split3 hGc
    rw [mul_sub, h1, hAB, hD]
    rw [h2]
    ring
  rw [hdec]
  -- the pieces
  have hE1 : Real.exp (-(1 / (8 * b))) ≤ Real.exp (-(7 / (128 * b))) := by
    apply Real.exp_le_exp.mpr; rw [neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hE2 : Real.exp (-(7 / (64 * b))) ≤ Real.exp (-(7 / (128 * b))) := by
    apply Real.exp_le_exp.mpr; rw [neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  set E := Real.exp (-(7 / (128 * b))) with hEdef
  -- tails on `Re = 5/4`
  set b' := 32 * b / 7 with hb'
  have hb'0 : 0 < b' := by positivity
  set Gt : ℝ → ℝ := fun y => C * E * (Real.exp (2 * b') * Real.exp (-(y - 0) ^ 2 / (4 * (2 * b'))))
  have hGti : Integrable Gt := ((integrable_gauss_shift (by positivity : 0 < 2 * b') 0).const_mul _).const_mul _
  have hGt0 : ∀ y, 0 ≤ Gt y := fun y => by positivity
  have hGtI : ∫ y, Gt y ≤ Kt * E := by
    simp only [Gt]
    rw [integral_const_mul, integral_const_mul, integral_gauss_shift (by positivity : 0 < 2 * b')]
    have h1 : Real.exp (2 * b') ≤ Real.exp (64 / 7) := Real.exp_le_exp.mpr (by rw [hb']; linarith)
    have h2 : Real.sqrt (4 * π * (2 * b')) ≤ Real.sqrt (4 * π * (2 * (32 / 7))) :=
      Real.sqrt_le_sqrt (by rw [hb']; nlinarith [Real.pi_pos])
    rw [hKt]
    have := mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.exp_pos _).le
    have hCE : 0 ≤ C * E := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hCE]
  have hT1 : ‖T1‖ ≤ Kt * E := by
    refine (norm_setIntegral_le_full measurableSet_Iic hGti hGt0 fun y hy => ?_).trans hGtI
    have hy' : 1 ≤ |y| := by rw [abs_of_nonpos (by linarith [mem_Iic.mp hy])]; linarith [mem_Iic.mp hy]
    exact tail_pt hb hC hbd hy'
  have hT2 : ‖T2‖ ≤ Kt * E := by
    refine (norm_setIntegral_le_full measurableSet_Ioi hGti hGt0 fun y hy => ?_).trans hGtI
    have hy' : 1 ≤ |y| := by rw [abs_of_pos (by linarith [mem_Ioi.mp hy])]; exact (mem_Ioi.mp hy).le
    exact tail_pt hb hC hbd hy'
  -- Gaussian tails
  set G2 : ℝ → ℝ := fun y => Real.exp (-(1 / (8 * b))) * Real.exp (-(y - 0) ^ 2 / (4 * (2 * b)))
  have hG2i : Integrable G2 := (integrable_gauss_shift (by positivity : 0 < 2 * b) 0).const_mul _
  have hG20 : ∀ y, 0 ≤ G2 y := fun y => by positivity
  have hG2I : ∫ y, G2 y ≤ Real.sqrt (4 * π * (2 * 1)) * E := by
    simp only [G2]
    rw [integral_const_mul, integral_gauss_shift (by positivity : 0 < 2 * b)]
    have h2 : Real.sqrt (4 * π * (2 * b)) ≤ Real.sqrt (4 * π * (2 * 1)) :=
      Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])
    nlinarith [mul_le_mul hE1 h2 (Real.sqrt_nonneg _) (Real.exp_pos _).le]
  have hGpt : ∀ y : ℝ, 1 ≤ |y| → ‖((G y : ℝ) : ℂ)‖ ≤ G2 y := by
    intro y hy
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simp only [G2]
    rw [← Real.exp_add, Real.exp_le_exp]
    have hy2 : 1 ≤ y ^ 2 := by nlinarith [sq_abs y, abs_nonneg y]
    have e : -(1 / (8 * b)) + -(y - 0) ^ 2 / (4 * (2 * b)) = (-1 - y ^ 2) / (8 * b) := by field_simp; ring
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hGL : ‖GLt‖ ≤ Real.sqrt (4 * π * (2 * 1)) * E := by
    refine (norm_setIntegral_le_full measurableSet_Iic hG2i hG20 fun y hy => hGpt y ?_).trans hG2I
    rw [abs_of_nonpos (by linarith [mem_Iic.mp hy])]; linarith [mem_Iic.mp hy]
  have hGR : ‖GRt‖ ≤ Real.sqrt (4 * π * (2 * 1)) * E := by
    refine (norm_setIntegral_le_full measurableSet_Ioi hG2i hG20 fun y hy => hGpt y ?_).trans hG2I
    rw [abs_of_pos (by linarith [mem_Ioi.mp hy])]; exact (mem_Ioi.mp hy).le
  -- horizontal sides
  have hhor : ∀ yv : ℝ, |yv| = 1 →
      ‖∫ x in (1 / 2 : ℝ)..(5 / 4), f ((x : ℂ) + (yv : ℂ) * I)‖ ≤ 3 / 4 * Kh * E := by
    intro yv hyv
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (1 / 2 : ℝ)) (b := 5 / 4)
      (C := Kh * E) (f := fun x : ℝ => f ((x : ℂ) + (yv : ℂ) * I)) (fun x hx => ?_)
    · rw [show |(5 / 4 : ℝ) - 1 / 2| = 3 / 4 by norm_num] at h; linarith
    · rw [uIoc_of_le (by norm_num)] at hx
      simp only [hf, gline]
      rw [norm_mul, norm_cexp_quad]
      have hre : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
      have him : (1 / 2 : ℂ).im = 0 := by norm_num
      rw [hre, him]
      have hk := hKhb x ⟨hx.1.le, hx.2⟩ yv (by rw [abs_eq (by norm_num)] at hyv; rcases hyv with h | h <;>
        rw [h] <;> norm_num)
      have hy2 : (yv - 0) ^ 2 = 1 := by rw [sub_zero, ← sq_abs, hyv]; norm_num
      have hex : Real.exp (((x - 1 / 2) ^ 2 - (yv - 0) ^ 2) / (4 * b)) ≤ E := by
        refine le_trans ?_ hE2
        apply Real.exp_le_exp.mpr
        rw [hy2, div_le_iff₀ (by positivity)]
        have : (x - 1 / 2) ^ 2 ≤ 9 / 16 := by nlinarith [hx.1, hx.2]
        field_simp
        nlinarith
      calc Real.exp (((x - 1 / 2) ^ 2 - (yv - 0) ^ 2) / (4 * b)) * ‖invZeta ((x : ℂ) + (yv : ℂ) * I)‖
          ≤ E * Kh := mul_le_mul hex hk (norm_nonneg _) (by positivity)
        _ = Kh * E := by ring
  have hbot : ‖bot‖ ≤ 3 / 4 * Kh * E := hhor (-1) (by norm_num)
  have htop : ‖top‖ ≤ 3 / 4 * Kh * E := by
    exact hhor 1 (by norm_num)
  -- the critical segment
  have hDb : ‖D‖ ≤ 8 * Real.sqrt π * L * b := by
    have hpt : ∀ᵐ y ∂volume, y ∈ Ioc (-1 : ℝ) 1 →
        ‖f (((1 / 2 : ℝ) : ℂ) + y * I) - g0 * ((G y : ℝ) : ℂ)‖
          ≤ L * (Real.sqrt (8 * b) * Real.exp (-(y - 0) ^ 2 / (4 * (2 * b)))) := by
      refine ae_of_all _ fun y hy => ?_
      rw [hseg, show ((G y : ℝ) : ℂ) * invZeta ((1 / 2 : ℂ) + y * I) - g0 * ((G y : ℝ) : ℂ)
          = ((G y : ℝ) : ℂ) * (invZeta ((1 / 2 : ℂ) + y * I) - g0) by ring, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have hl := invZeta_lip hL ⟨hy.1.le, hy.2⟩
      have hg := abs_mul_gauss_le hb y
      calc G y * ‖invZeta ((1 / 2 : ℂ) + y * I) - g0‖ ≤ G y * (L * |y|) :=
            mul_le_mul_of_nonneg_left hl (Real.exp_pos _).le
        _ = L * (|y| * G y) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hg hL0
    have hmaj : Integrable (fun y : ℝ => L * (Real.sqrt (8 * b) * Real.exp (-(y - 0) ^ 2 / (4 * (2 * b))))) :=
      ((integrable_gauss_shift (by positivity : 0 < 2 * b) 0).const_mul _).const_mul _
    have h1 := intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (-1 : ℝ) ≤ 1) hpt
      (hmaj.intervalIntegrable)
    refine h1.trans ?_
    rw [intervalIntegral.integral_of_le (by norm_num)]
    refine (setIntegral_le_integral hmaj (ae_of_all _ fun y => by positivity)).trans (le_of_eq ?_)
    rw [integral_const_mul, integral_const_mul, integral_gauss_shift (by positivity : 0 < 2 * b),
      ← mul_assoc L, mul_assoc L, ← Real.sqrt_mul (by positivity)]
    have : 8 * b * (4 * π * (2 * b)) = (8 * b) ^ 2 * π := by ring
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    ring
  -- assemble
  have hn1 : ‖T1 - g0 * GLt‖ ≤ Kt * E + ‖g0‖ * (Real.sqrt (4 * π * (2 * 1)) * E) := by
    refine (norm_sub_le _ _).trans (add_le_add hT1 ?_)
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left hGL (norm_nonneg _)
  have hn2 : ‖T2 - g0 * GRt‖ ≤ Kt * E + ‖g0‖ * (Real.sqrt (4 * π * (2 * 1)) * E) := by
    refine (norm_sub_le _ _).trans (add_le_add hT2 ?_)
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left hGR (norm_nonneg _)
  have hn3 : ‖I * (bot - top)‖ ≤ 2 * (3 / 4 * Kh * E) := by
    rw [norm_mul, Complex.norm_I, one_mul]
    exact (norm_sub_le _ _).trans (by linarith)
  calc ‖(T1 - g0 * GLt) + (T2 - g0 * GRt) + D + I * (bot - top)‖
      ≤ ‖T1 - g0 * GLt‖ + ‖T2 - g0 * GRt‖ + ‖D‖ + ‖I * (bot - top)‖ := by
        refine (norm_add_le _ _).trans ?_
        refine add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl
    _ ≤ (Kt * E + ‖g0‖ * (Real.sqrt (4 * π * (2 * 1)) * E)) + (Kt * E + ‖g0‖ * (Real.sqrt (4 * π * (2 * 1)) * E))
        + 8 * Real.sqrt π * L * b + 2 * (3 / 4 * Kh * E) :=
          add_le_add (add_le_add (add_le_add hn1 hn2) hDb) hn3
    _ = _ := by ring


/-! ## The lower bound for the smooth window at `α = 0` -/

/-- **Cauchy–Schwarz**: `smoothWindow b 0 ≥ √(4πb) ‖P_{2b}(1/2)‖²`. -/
theorem smoothWindow_zero_ge {b : ℝ} (hb : 0 < b) :
    Real.sqrt (4 * π * b) * ‖Psm (2 * b) (1 / 2)‖ ^ 2 ≤ smoothWindow b 0 := by
  set p : ℝ → ℝ := fun t => ‖Psm b (((1 / 2 : ℝ) : ℂ) + t * I)‖ with hp
  set w : ℝ → ℝ := fun t => Real.exp (-(t - 0) ^ 2 / (4 * b)) with hw
  have hX : Integrable (fun t => p t ^ 2 * w t) := integrable_window hb 0
  have hW : Integrable w := integrable_gauss_shift hb 0
  have hpc : Continuous p := ((continuous_Psm hb).comp (by fun_prop)).norm
  have hpw : Integrable (fun t => p t * w t) := by
    refine Integrable.mono' ((hX.add hW).div_const 2) (hpc.mul (by fun_prop)).aestronglyMeasurable
      (ae_of_all _ fun t => ?_)
    have hw0 : 0 ≤ w t := (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) hw0)]
    simp only [Pi.add_apply]
    nlinarith [mul_nonneg (sq_nonneg (p t - 1)) hw0]
  have hcs : ∫ t, p t * w t ≤ Real.sqrt (smoothWindow b 0) * Real.sqrt (∫ t, w t) := by
    apply FleetHeadContour.le_sqrt_mul_of_forall (integral_nonneg fun t => by positivity)
      (integral_nonneg fun t => by positivity)
    intro l hl
    have hpt : ∀ t, 2 * (p t * w t) ≤ l * (p t ^ 2 * w t) + w t / l := by
      intro t
      have hw0 : 0 ≤ w t := (Real.exp_pos _).le
      have key : 2 * p t ≤ l * p t ^ 2 + 1 / l := by
        have : 0 ≤ (l * p t - 1) ^ 2 / l := by positivity
        have e : (l * p t - 1) ^ 2 / l = l * p t ^ 2 - 2 * p t + 1 / l := by field_simp; ring
        linarith
      have := mul_le_mul_of_nonneg_right key hw0
      calc 2 * (p t * w t) = 2 * p t * w t := by ring
        _ ≤ (l * p t ^ 2 + 1 / l) * w t := this
        _ = _ := by ring
    have hint : ∫ t, 2 * (p t * w t) ≤ ∫ t, (l * (p t ^ 2 * w t) + w t / l) :=
      integral_mono (hpw.const_mul 2) ((hX.const_mul l).add (hW.div_const l)) hpt
    rw [MeasureTheory.integral_const_mul, integral_add (hX.const_mul l) (hW.div_const l),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_div] at hint
    exact hint
  have hWv : ∫ t, w t = Real.sqrt (4 * π * b) := integral_gauss_shift hb 0
  have hpair := integral_Psm_gauss hb
  have hnorm : Real.sqrt (4 * π * b) * ‖Psm (2 * b) (1 / 2)‖ ≤ ∫ t, p t * w t := by
    have h1 : ‖(Real.sqrt (4 * π * b) : ℂ) * Psm (2 * b) (1 / 2)‖
        = Real.sqrt (4 * π * b) * ‖Psm (2 * b) (1 / 2)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [← h1, ← hpair]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [hWv] at hcs
  have hsW : 0 ≤ smoothWindow b 0 := integral_nonneg fun t => by positivity
  set s := Real.sqrt (4 * π * b)
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hss : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs0.le
  have h2 := (hnorm.trans hcs)
  have h3 : (s * ‖Psm (2 * b) (1 / 2)‖) ^ 2 ≤ (Real.sqrt (smoothWindow b 0) * Real.sqrt s) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2 2
  rw [mul_pow, mul_pow, Real.sq_sqrt hsW, hss] at h3
  have : s * (s * ‖Psm (2 * b) (1 / 2)‖ ^ 2) ≤ s * smoothWindow b 0 := by nlinarith
  exact le_of_mul_le_mul_left this hs0

lemma invZeta_half_ne_zero : invZeta (1 / 2) ≠ 0 := by
  rw [invZeta_of_ne (by norm_num)]
  exact inv_ne_zero (zeta_ne_zero_box (by norm_num) (by norm_num))

/-- `P_b(1/2) → 1/ζ(1/2)`: eventually `‖P_b(1/2)‖ ≥ ‖1/ζ(1/2)‖/2`. -/
theorem eventually_Psm_half_ge :
    ∀ᶠ b in 𝓝[>] (0 : ℝ), ‖invZeta (1 / 2)‖ / 2 ≤ ‖Psm b (1 / 2)‖ := by
  obtain ⟨L, K, hL, hK, herr⟩ := Psm_half_err
  set g0 := invZeta (1 / 2)
  have hg0 : 0 < ‖g0‖ := norm_pos_iff.mpr invZeta_half_ne_zero
  -- the error `4L√b + K e^{-7/(128b)}/√(4πb)` tends to `0`
  have hA : Tendsto (fun b : ℝ => 4 * L * Real.sqrt b) (𝓝[>] 0) (𝓝 0) := by
    have := ((Real.continuous_sqrt.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))).const_mul (4 * L)
    simpa using this
  have hB : Tendsto (fun b : ℝ => (K / Real.sqrt (4 * π)) * Real.exp (-(7 / 128) * b⁻¹) * Real.sqrt b⁻¹)
      (𝓝[>] 0) (𝓝 0) := FleetWindowLowerBound.tendsto_exp_div_sqrt (by norm_num) _
  have hev : ∀ᶠ b in 𝓝[>] (0 : ℝ), 4 * L * Real.sqrt b +
      (K / Real.sqrt (4 * π)) * Real.exp (-(7 / 128) * b⁻¹) * Real.sqrt b⁻¹ < ‖g0‖ / 2 := by
    have h0 : (0 : ℝ) + 0 < ‖g0‖ / 2 := by linarith
    exact (hA.add hB).eventually (gt_mem_nhds h0)
  filter_upwards [hev, self_mem_nhdsWithin, Ioo_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with b hbe hb hb1
  have hb0 : 0 < b := hb
  have h := herr b hb0 hb1.2.le
  have hs : Real.sqrt (4 * π * b) = Real.sqrt (4 * π) * Real.sqrt b := Real.sqrt_mul (by positivity) _
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb0
  have hs4 : 0 < Real.sqrt (4 * π) := Real.sqrt_pos.mpr (by positivity)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr (by positivity)), hs] at h
  -- divide by `√(4π) √b`
  have hinv : Real.sqrt b * Real.sqrt b⁻¹ = 1 := by
    rw [← Real.sqrt_mul hb0.le, mul_inv_cancel₀ hb0.ne', Real.sqrt_one]
  have hπ : Real.sqrt π / Real.sqrt (4 * π) = 1 / 2 := by
    rw [show (4 : ℝ) * π = 2 ^ 2 * π by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    field_simp
  have hE : Real.exp (-(7 / (128 * b))) = Real.exp (-(7 / 128) * b⁻¹) := by congr 1; field_simp
  have hdiff : ‖Psm b (1 / 2) - g0‖ ≤ 4 * L * Real.sqrt b +
      (K / Real.sqrt (4 * π)) * Real.exp (-(7 / 128) * b⁻¹) * Real.sqrt b⁻¹ := by
    rw [← hE]
    have hden : 0 < Real.sqrt (4 * π) * Real.sqrt b := mul_pos hs4 hsb
    rw [← mul_le_mul_iff_of_pos_left hden]
    calc Real.sqrt (4 * π) * Real.sqrt b * ‖Psm b (1 / 2) - g0‖
        ≤ 8 * Real.sqrt π * L * b + K * Real.exp (-(7 / (128 * b))) := h
      _ = Real.sqrt (4 * π) * Real.sqrt b * (4 * L * Real.sqrt b +
          (K / Real.sqrt (4 * π)) * Real.exp (-(7 / (128 * b))) * Real.sqrt b⁻¹) := by
          have hbb : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb0.le
          have h8 : 8 * Real.sqrt π = 4 * Real.sqrt (4 * π) := by
            have := hπ; field_simp at this; linarith
          rw [h8]
          set e := Real.exp (-(7 / (128 * b)))
          have hs4ne : Real.sqrt (4 * π) ≠ 0 := hs4.ne'
          calc 4 * Real.sqrt (4 * π) * L * b + K * e
              = 4 * Real.sqrt (4 * π) * L * (Real.sqrt b * Real.sqrt b) + K * e * (Real.sqrt b * Real.sqrt b⁻¹) := by
                rw [hbb, hinv]; ring
            _ = _ := by field_simp
  have := norm_sub_norm_le g0 (Psm b (1 / 2))
  rw [norm_sub_rev] at hdiff
  linarith


/-- `κ = √(4π) ‖1/ζ(1/2)‖² / 4 > 0`. -/
def kappa : ℝ := Real.sqrt (4 * π) * (‖invZeta (1 / 2)‖ / 2) ^ 2

lemma kappa_pos : 0 < kappa := by
  unfold kappa
  have := norm_pos_iff.mpr invZeta_half_ne_zero
  positivity

/-- **Positive lower bound for the smooth window** (no hypothesis): there is `b₀ > 0` with
`smoothWindow b 0 ≥ κ √b` for all `0 < b ≤ b₀`, where `κ = √(4π) (|1/ζ(1/2)|/2)² > 0`. -/
theorem smoothWindow_lower :
    ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b ≤ b₀ → kappa * Real.sqrt b ≤ smoothWindow b 0 := by
  have hev : ∀ᶠ b in 𝓝[>] (0 : ℝ), ‖invZeta (1 / 2)‖ / 2 ≤ ‖Psm (2 * b) (1 / 2)‖ := by
    have ht : Tendsto (fun b : ℝ => 2 * b) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h0 : Tendsto (fun b : ℝ => 2 * b) (𝓝 0) (𝓝 (2 * 0)) :=
          (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul 2
        rw [mul_zero] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with b hb
        exact mul_pos two_pos (mem_Ioi.mp hb)
    exact ht.eventually eventually_Psm_half_ge
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨u / 2, half_pos hu, fun b hb hbu => ?_⟩
  have hbU : b ∈ Ioo 0 u := ⟨hb, by linarith⟩
  have h1 : ‖invZeta (1 / 2)‖ / 2 ≤ ‖Psm (2 * b) (1 / 2)‖ := hsub hbU
  have h2 := smoothWindow_zero_ge hb
  have hs : Real.sqrt (4 * π * b) = Real.sqrt (4 * π) * Real.sqrt b := Real.sqrt_mul (by positivity) _
  rw [hs] at h2
  have h3 : (‖invZeta (1 / 2)‖ / 2) ^ 2 ≤ ‖Psm (2 * b) (1 / 2)‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  unfold kappa
  have hp : 0 ≤ Real.sqrt (4 * π) * Real.sqrt b := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h3 hp]

/-- **No negative smooth window rate**: `SmoothWindowRate c` fails for every `c < 0`, unconditionally. -/
theorem not_smoothWindowRate_of_neg {c : ℝ} (hc : c < 0) : ¬ SmoothWindowRate c := by
  intro h
  obtain ⟨C, hC⟩ := h 0
  obtain ⟨b₀, hb₀, hlow⟩ := smoothWindow_lower
  have hev : ∀ᶠ b in 𝓝[>] (0 : ℝ), |C| * Real.exp (c * b⁻¹) * Real.sqrt b⁻¹ < kappa :=
    (FleetWindowLowerBound.tendsto_exp_div_sqrt hc |C|).eventually (gt_mem_nhds kappa_pos)
  have hev2 : ∀ᶠ b in 𝓝[>] (0 : ℝ), b < min b₀ 1 := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min hb₀ one_pos)] with b hb using hb.2
  obtain ⟨b, ⟨h1, h2⟩, hb⟩ := ((hev.and hev2).and self_mem_nhdsWithin).exists
  have hb' : 0 < b := hb
  have hL := hlow b hb' (h2.trans_le (min_le_left _ _)).le
  have hU := (hC b hb' (h2.trans_le (min_le_right _ _)).le).trans
    (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)
  rw [div_eq_mul_inv] at hU
  have hs : Real.sqrt b * Real.sqrt b⁻¹ = 1 := by
    rw [← Real.sqrt_mul hb'.le, mul_inv_cancel₀ hb'.ne', Real.sqrt_one]
  have hsp : 0 < Real.sqrt b⁻¹ := Real.sqrt_pos.mpr (inv_pos.mpr hb')
  have key : kappa * Real.sqrt b ≤ |C| * Real.exp (c * b⁻¹) := hL.trans hU
  have := mul_le_mul_of_nonneg_right key hsp.le
  rw [mul_assoc, hs, mul_one] at this
  linarith

/-- Every admissible smooth rate is nonnegative. -/
theorem smoothWindowRate_nonneg {c : ℝ} (h : SmoothWindowRate c) : 0 ≤ c :=
  not_lt.mp fun hc => not_smoothWindowRate_of_neg hc h

/-- **`SmoothWindowRate c ⇒ D²/2 ≤ c`**, with no side condition. -/
theorem zeroDev_sq_half_le_of_smoothWindowRate {c : ℝ} (h : SmoothWindowRate c) :
    FleetHeadContour.zeroDev ^ 2 / 2 ≤ c := by
  by_contra hlt
  push Not at hlt
  exact not_smoothWindowRate_of_lt (smoothWindowRate_nonneg h) hlt h

theorem not_smoothWindowRate_of_lt' {c : ℝ} (hc : c < FleetHeadContour.zeroDev ^ 2 / 2) :
    ¬ SmoothWindowRate c :=
  fun h => absurd (zeroDev_sq_half_le_of_smoothWindowRate h) (not_le.mpr hc)

/-- The infimum over **all** real admissible smooth rates is `smoothWindowRateInf` (`= D²/2`). -/
theorem sInf_smoothWindowRate_eq : sInf {c : ℝ | SmoothWindowRate c} = smoothWindowRateInf := by
  unfold smoothWindowRateInf
  congr 1
  ext c
  exact ⟨fun h => ⟨smoothWindowRate_nonneg h, h⟩, fun h => h.2⟩

end FleetSmoothWindowLower
