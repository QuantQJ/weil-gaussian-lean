import TestFunctions
import Mathlib

open Complex MeasureTheory Set
open scoped FourierTransform

namespace FleetFourierNormalization

lemma support_condition {a : ℝ} {g : ℝ → ℂ}
    (hsupp : ∀ u, a < |u| → g u = 0) :
    ∀ u, u ∉ Icc (-a) a → g u = 0 := by
  intro u hu
  apply hsupp u
  by_contra hh
  exact hu (abs_le.mp (le_of_not_gt hh))

lemma hfun_eq_fourier {a : ℝ} {g : ℝ → ℂ} (h : TestFunctions.IsTestFn a g)
    (hsupp : ∀ u, a < |u| → g u = 0) (t : ℝ) :
    TestFunctions.hfun a g (t : ℂ) = 𝓕 g (-(1 / (2 * Real.pi)) * t) := by
  have he := TestFunctions.Gt_half_line_eq_fourier h.nonneg (support_condition hsupp)
    (t / (2 * Real.pi))
  have harg : (1 / 2 : ℂ) + 2 * Real.pi * (t / (2 * Real.pi) : ℝ) * I =
      1 / 2 + I * (t : ℂ) := by
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [harg, TestFunctions.Gt_half_add_I_mul] at he
  convert he using 1
  congr 1
  ring

lemma integrable_hfun {a : ℝ} {g : ℝ → ℂ} (h : TestFunctions.IsTestFn a g) :
    Integrable (fun t : ℝ => TestFunctions.hfun a g (t : ℂ)) := by
  have hi := TestFunctions.integrable_on_vertical_line h (1 / 2)
  convert hi using 1
  funext t
  push_cast
  rw [mul_comm (t : ℂ) I, TestFunctions.Gt_half_add_I_mul]

/-- The exact 2π Fourier normalization; no real-valuedness or evenness is assumed. -/
theorem integral_hfun {a : ℝ} {g : ℝ → ℂ} (h : TestFunctions.IsTestFn a g)
    (hsupp : ∀ u, a < |u| → g u = 0) :
    (∫ t : ℝ, TestFunctions.hfun a g (t : ℂ)) = (2 * (Real.pi : ℂ)) * g 0 := by
  have hc : HasCompactSupport g :=
    HasCompactSupport.intro' isCompact_Icc isClosed_Icc (support_condition hsupp)
  have hg : Integrable g := h.continuous.integrable_of_hasCompactSupport hc
  have hnonzero : (-(1 / (2 * Real.pi)) : ℝ) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero one_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  have hfg : Integrable (𝓕 g) := by
    apply (integrable_comp_mul_left_iff (𝓕 g) hnonzero).mp
    simpa only [← hfun_eq_fourier h hsupp] using integrable_hfun h
  have hinv := hg.fourierInv_fourier_eq hfg (h.continuous.continuousAt (x := 0))
  have hzero : (∫ x : ℝ, 𝓕 g x) = g 0 := by
    simpa [Real.fourierInv_eq'] using hinv
  simp_rw [hfun_eq_fourier h hsupp]
  rw [Measure.integral_comp_mul_left, hzero]
  have hscale : |(-(1 / (2 * Real.pi)) : ℝ)|⁻¹ = 2 * Real.pi := by
    rw [abs_neg, abs_of_pos (by positivity), inv_div, div_one]
  rw [abs_inv, hscale, Complex.real_smul]
  push_cast
  rfl

end FleetFourierNormalization
