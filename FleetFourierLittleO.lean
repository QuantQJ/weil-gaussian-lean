import TestFunctions
import Mathlib

noncomputable section

open Complex Filter Topology MeasureTheory Set
open scoped FourierTransform

namespace FleetFourierLittleO

lemma hfun_eq_fourier_indicator {a : ℝ} (ha : 0 ≤ a) (g : ℝ → ℂ) (t : ℝ) :
    TestFunctions.hfun a g (t : ℂ) =
      𝓕 ((Ioc (-a) a).indicator g) ((-(1 / (2 * Real.pi))) * t) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  rw [TestFunctions.hfun, intervalIntegral.integral_of_le (by linarith)]
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [] with u
  by_cases hu : u ∈ Ioc (-a) a
  · simp only [indicator_of_mem hu, smul_eq_mul]
    rw [mul_comm (Complex.exp _)]
    congr 2
    push_cast
    have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp [hp]
  · simp [indicator_of_notMem hu]

/-- Riemann--Lebesgue for the interval transform, with its actual frequency convention. -/
theorem hfun_tendsto_zero {a : ℝ} (ha : 0 ≤ a) (g : ℝ → ℂ) :
    Tendsto (fun t : ℝ => TestFunctions.hfun a g (t : ℂ))
      (cocompact ℝ) (𝓝 0) := by
  have hc : (-(1 / (2 * Real.pi)) : ℝ) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero one_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  have ht := (Real.zero_at_infty_fourier ((Ioc (-a) a).indicator g)).comp
    (Filter.tendsto_cocompact_mul_left₀ hc)
  simpa only [Function.comp_def, ← hfun_eq_fourier_indicator ha] using ht

/-- Twice integration by parts improves the weighted transform from bounded to vanishing. -/
theorem weighted_hfun_tendsto_zero {a : ℝ} {g : ℝ → ℂ}
    (h : TestFunctions.IsTestFn a g) :
    Tendsto (fun t : ℝ => (1 + (t : ℂ)^2) * TestFunctions.hfun a g (t : ℂ))
      (cocompact ℝ) (𝓝 0) := by
  have hid (t : ℝ) : (1 + (t : ℂ)^2) * TestFunctions.hfun a g (t : ℂ) =
      TestFunctions.hfun a g (t : ℂ) -
        TestFunctions.hfun a (deriv (deriv g)) (t : ℂ) := by
    have hi := TestFunctions.sq_mul_Gt_eq h (1 / 2 + I * (t : ℂ))
    rw [TestFunctions.Gt_half_add_I_mul] at hi
    simp only [add_sub_cancel_left] at hi
    change (I * (t : ℂ)) ^ 2 * TestFunctions.hfun a g (t : ℂ) =
      TestFunctions.hfun a (deriv (deriv g)) (t : ℂ) at hi
    rw [mul_pow, Complex.I_sq] at hi
    linear_combination -hi
  simp_rw [hid]
  simpa using (hfun_tendsto_zero h.nonneg g).sub
    (hfun_tendsto_zero h.nonneg (deriv (deriv g)))

/-- The corresponding real nonnegative weighted norm vanishes at both ends. -/
theorem weighted_norm_hfun_tendsto_zero {a : ℝ} {g : ℝ → ℂ}
    (h : TestFunctions.IsTestFn a g) :
    Tendsto (fun t : ℝ => (1 + t^2) * ‖TestFunctions.hfun a g (t : ℂ)‖)
      (cocompact ℝ) (𝓝 0) := by
  have ht := (weighted_hfun_tendsto_zero h).norm
  simp only [norm_zero, norm_mul] at ht
  convert ht using 1
  funext t
  have he : (1 + (t : ℂ)^2) = ((1 + t^2 : ℝ) : ℂ) := by push_cast; rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs, _root_.abs_of_nonneg (by positivity)]

end FleetFourierLittleO
