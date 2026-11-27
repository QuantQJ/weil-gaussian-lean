/-
Kerr/PNT/MobiusContour.lean — new file (written for this repo, not copied).
CONDITIONAL contour estimate for the smoothed Perron integral
  ∫_{(b)} x^s/(s(s+1)) · G(s) ds,
for an arbitrary function `G` that is holomorphic and bounded by `B` on the rectangle
[σ₀, b] × [-T, T] and bounded by `Bb` on the line Re s = b. Uses the copied PrimeNumberTheoremAnd
rectangle machinery (`HolomorphicOn.vanishesOnRectangle`, `verticalIntegral_split_three`;
Apache-2.0, © the PrimeNumberTheoremAnd contributors).
-/
import Kerr.PNT.MobiusPerron

open Complex Filter Topology Set MeasureTheory
open scoped Interval

namespace KerrPNT.Mobius

lemma norm_perron_f_le_re {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖Perron.f x s‖ ≤ 4 / 3 * x ^ s.re := by
  have h1 : 1 / 2 ≤ ‖s‖ := hs.trans (re_le_norm s)
  have h2 : 3 / 2 ≤ ‖s + 1‖ := by
    have := re_le_norm (s + 1); simp at this; linarith
  have hprod : 3 / 4 ≤ ‖s * (s + 1)‖ := by
    rw [norm_mul]; nlinarith
  simp only [Perron.f, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  rw [div_le_iff₀ (by linarith)]
  have : 0 ≤ x ^ s.re := Real.rpow_nonneg hx.le _
  nlinarith

lemma norm_perron_f_le_im {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : s.im ≠ 0) :
    ‖Perron.f x s‖ ≤ x ^ s.re / s.im ^ 2 := by
  have h1 : |s.im| ≤ ‖s‖ := abs_im_le_norm s
  have h2 : |s.im| ≤ ‖s + 1‖ := by
    have := abs_im_le_norm (s + 1); simpa using this
  have hprod : s.im ^ 2 ≤ ‖s * (s + 1)‖ := by
    rw [norm_mul, ← sq_abs, sq]
    exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
  simp only [Perron.f, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) (by positivity) hprod

lemma integral_Ioi_inv_sq {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun t : ℝ ↦ (t ^ 2)⁻¹) (Ioi T) ∧ ∫ t in Ioi T, (t ^ 2)⁻¹ = T⁻¹ := by
  have heq : EqOn (fun t : ℝ ↦ (t ^ 2)⁻¹) (fun t ↦ t ^ (-2 : ℝ)) (Ioi T) := by
    intro t ht
    have : 0 < t := hT.trans ht
    simp only
    rw [Real.rpow_neg this.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  refine ⟨(integrableOn_Ioi_rpow_of_lt (by norm_num) hT).congr_fun heq.symm measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_Ioi_rpow_of_lt (by norm_num) hT]
  rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  ring

/-- **Conditional contour estimate.** -/
theorem contour_bound {G : ℂ → ℂ} {x b σ₀ T B Bb : ℝ} (hx : 1 < x) (hσ₀ : 1 / 2 ≤ σ₀)
    (hσ₀b : σ₀ ≤ b) (hT : 0 < T)
    (hdiff : ∀ σ ∈ Icc σ₀ b, ∀ t ∈ Icc (-T) T, DifferentiableAt ℂ G (σ + t * I))
    (hB : ∀ σ ∈ Icc σ₀ b, ∀ t ∈ Icc (-T) T, ‖G (σ + t * I)‖ ≤ B)
    (hBb : ∀ t : ℝ, ‖G (b + t * I)‖ ≤ Bb)
    (hint : Integrable (fun t : ℝ ↦ Perron.f x (b + t * I) * G (b + t * I))) :
    ‖VerticalIntegral (fun s ↦ Perron.f x s * G s) b‖ ≤
      8 / 3 * B * x ^ σ₀ * T + 2 * (b - σ₀) * B * x ^ b / T ^ 2 + 2 * Bb * x ^ b / T := by
  set F : ℂ → ℂ := fun s ↦ Perron.f x s * G s with hF
  have hx0 : 0 < x := by linarith
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB σ₀ ⟨le_rfl, hσ₀b⟩ 0 ⟨by linarith, by linarith⟩)
  have hBb0 : 0 ≤ Bb := (norm_nonneg _).trans (hBb 0)
  -- rectangle
  have hrect : RectangleIntegral F ((σ₀ : ℂ) - T * I) (b + T * I) = 0 := by
    apply HolomorphicOn.vanishesOnRectangle (U := Rectangle ((σ₀ : ℂ) - T * I) (b + T * I))
      _ subset_rfl
    intro s hs
    have hre : s.re ∈ Icc σ₀ b := by
      have h : s.re ∈ [[((σ₀ : ℂ) - T * I).re, ((b : ℂ) + T * I).re]] := hs.1
      have e1 : ((σ₀ : ℂ) - T * I).re = σ₀ := by simp
      have e2 : ((b : ℂ) + T * I).re = b := by simp
      rwa [e1, e2, uIcc_of_le hσ₀b] at h
    have him : s.im ∈ Icc (-T) T := by
      have h : s.im ∈ [[((σ₀ : ℂ) - T * I).im, ((b : ℂ) + T * I).im]] := hs.2
      have e1 : ((σ₀ : ℂ) - T * I).im = -T := by simp
      have e2 : ((b : ℂ) + T * I).im = T := by simp
      rwa [e1, e2, uIcc_of_le (by linarith)] at h
    have hG : DifferentiableAt ℂ G s := by
      have := hdiff s.re hre s.im him; rwa [re_add_im] at this
    have hf : DifferentiableAt ℂ (Perron.f x) s := by
      apply (Perron.isHolomorphicOn hx0).differentiableAt
      apply IsOpen.mem_nhds
      · exact (Set.toFinite ({0, -1} : Set ℂ)).isClosed.isOpen_compl
      · simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
        constructor
        · intro h; have := congrArg Complex.re h; simp at this; linarith [hre.1]
        · intro h; have := congrArg Complex.re h; simp at this; linarith [hre.1]
    exact (hf.mul hG).differentiableWithinAt
  simp only [RectangleIntegral, sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
    mul_one, sub_self, sub_zero, add_re, add_zero, sub_im, mul_im, zero_add, zero_sub,
    add_im] at hrect
  -- split the vertical line
  have hsplit := verticalIntegral_split_three (f := F) (σ := b) (-T) T hint
  have hV : VIntegral F b (-T) T =
      VIntegral F σ₀ (-T) T - HIntegral F σ₀ b (-T) + HIntegral F σ₀ b T := by
    linear_combination hrect
  rw [hsplit, hV]
  -- left edge
  have hleft : ‖VIntegral F σ₀ (-T) T‖ ≤ 8 / 3 * B * x ^ σ₀ * T := by
    simp only [VIntegral, norm_smul, norm_I, one_mul]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -T) (b := T)
      (C := 4 / 3 * x ^ σ₀ * B) (f := fun y : ℝ ↦ F (σ₀ + y * I)) (by
        intro y hy
        rw [uIoc_of_le (by linarith)] at hy
        simp only [hF, norm_mul]
        have h1 := norm_perron_f_le_re hx0 (s := σ₀ + y * I) (by simpa using hσ₀)
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero] at h1
        exact mul_le_mul h1 (hB σ₀ ⟨le_rfl, hσ₀b⟩ y ⟨hy.1.le, hy.2⟩) (norm_nonneg _)
          (by positivity))
    calc _ ≤ 4 / 3 * x ^ σ₀ * B * |T - -T| := this
      _ = 8 / 3 * B * x ^ σ₀ * T := by rw [abs_of_pos (by linarith)]; ring
  -- horizontal edges
  have hhor : ∀ y : ℝ, |y| = T → ‖HIntegral F σ₀ b y‖ ≤ (b - σ₀) * B * x ^ b / T ^ 2 := by
    intro y hy
    have hy0 : y ≠ 0 := by intro h; rw [h] at hy; simp at hy; linarith
    have hyI : y ∈ Icc (-T) T := by rw [← hy]; exact ⟨neg_abs_le y, le_abs_self y⟩
    simp only [HIntegral]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := σ₀) (b := b)
      (C := x ^ b / T ^ 2 * B) (f := fun σ : ℝ ↦ F (σ + y * I)) (by
        intro σ hσ
        rw [uIoc_of_le hσ₀b] at hσ
        simp only [hF, norm_mul]
        have h1 := norm_perron_f_le_im hx0 (s := σ + y * I) (by simpa using hy0)
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero, add_im, mul_im, zero_add] at h1
        have h2 : x ^ σ / y ^ 2 ≤ x ^ b / T ^ 2 := by
          rw [← sq_abs, hy]
          gcongr
          · exact hx.le
          · exact hσ.2
        exact mul_le_mul (h1.trans h2) (hB σ ⟨hσ.1.le, hσ.2⟩ y hyI) (norm_nonneg _)
          (by positivity))
    calc _ ≤ x ^ b / T ^ 2 * B * |b - σ₀| := this
      _ = (b - σ₀) * B * x ^ b / T ^ 2 := by rw [abs_of_nonneg (by linarith)]; ring
  -- tails
  obtain ⟨hIi, hIv⟩ := integral_Ioi_inv_sq hT
  have htailbound : ∀ t : ℝ, T < |t| → ‖F (b + t * I)‖ ≤ Bb * x ^ b * (t ^ 2)⁻¹ := by
    intro t ht
    have ht0 : t ≠ 0 := by intro h; rw [h] at ht; simp at ht; linarith
    simp only [hF, norm_mul]
    have h1 := norm_perron_f_le_im hx0 (s := b + t * I) (by simpa using ht0)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, add_im, mul_im, zero_add] at h1
    calc ‖Perron.f x (b + t * I)‖ * ‖G (b + t * I)‖ ≤ x ^ b / t ^ 2 * Bb :=
          mul_le_mul h1 (hBb t) (norm_nonneg _) (by positivity)
      _ = Bb * x ^ b * (t ^ 2)⁻¹ := by ring
  have htop : ‖I • ∫ t in Ici T, F (b + t * I)‖ ≤ Bb * x ^ b / T := by
    rw [norm_smul, norm_I, one_mul, integral_Ici_eq_integral_Ioi]
    refine (norm_integral_le_integral_norm _).trans ?_
    calc ∫ t in Ioi T, ‖F (b + t * I)‖ ≤ ∫ t in Ioi T, Bb * x ^ b * (t ^ 2)⁻¹ := by
          apply integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ norm_nonneg _)
            (hIi.const_mul _)
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact htailbound t (by rw [abs_of_pos (hT.trans ht)]; exact ht)
      _ = Bb * x ^ b / T := by rw [integral_const_mul, hIv]; ring
  have hbot : ‖I • ∫ t in Iic (-T), F (b + t * I)‖ ≤ Bb * x ^ b / T := by
    rw [norm_smul, norm_I, one_mul]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hc := integral_comp_neg_Iic (-T) (fun u : ℝ ↦ ‖F (b + (-u) * I)‖)
    simp only [ofReal_neg, neg_neg] at hc
    rw [hc]
    calc _ ≤ ∫ t in Ioi T, Bb * x ^ b * (t ^ 2)⁻¹ := by
          apply integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ norm_nonneg _)
            (hIi.const_mul _)
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have := htailbound (-t) (by rw [abs_neg, abs_of_pos (hT.trans ht)]; exact ht)
          simpa using this
      _ = Bb * x ^ b / T := by rw [integral_const_mul, hIv]; ring
  have hTm : |(-T)| = T := by rw [abs_neg, abs_of_pos hT]
  have hTp : |T| = T := abs_of_pos hT
  have hA := hhor _ hTm
  have hC := hhor _ hTp
  have n1 := norm_add_le (I • (∫ t in Iic (-T), F (b + t * I)) +
      (VIntegral F σ₀ (-T) T - HIntegral F σ₀ b (-T) + HIntegral F σ₀ b T))
      (I • ∫ t in Ici T, F (b + t * I))
  have n2 := norm_add_le (I • (∫ t in Iic (-T), F (b + t * I)))
      (VIntegral F σ₀ (-T) T - HIntegral F σ₀ b (-T) + HIntegral F σ₀ b T)
  have n3 := norm_add_le (VIntegral F σ₀ (-T) T - HIntegral F σ₀ b (-T)) (HIntegral F σ₀ b T)
  have n4 := norm_sub_le (VIntegral F σ₀ (-T) T) (HIntegral F σ₀ b (-T))
  have : 2 * (b - σ₀) * B * x ^ b / T ^ 2 = (b - σ₀) * B * x ^ b / T ^ 2 +
      (b - σ₀) * B * x ^ b / T ^ 2 := by ring
  have : 2 * Bb * x ^ b / T = Bb * x ^ b / T + Bb * x ^ b / T := by ring
  linarith

end KerrPNT.Mobius
