import FleetFourierLittleO
import Mathlib

noncomputable section
open Complex Filter Topology MeasureTheory Set
open scoped FourierTransform
namespace FleetFullLineFourier

def h (g : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ u : ℝ, g u * Complex.exp (I*z*(u : ℂ))

lemma h_eq_fourier (g : ℝ → ℂ) (t : ℝ) :
    h g (t : ℂ) = 𝓕 g ((-(1/(2*Real.pi)))*t) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [smul_eq_mul]
  rw [mul_comm (Complex.exp _)]
  congr 2
  push_cast
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hp]

lemma h_deriv {g : ℝ → ℂ} (hg : Integrable g) (hd : Differentiable ℝ g)
    (hg' : Integrable (deriv g)) (t : ℝ) :
    h (deriv g) (t : ℂ) = (-I*(t : ℂ))*h g (t : ℂ) := by
  rw [h_eq_fourier, Real.fourier_deriv hg hd hg']
  dsimp only
  rw [← h_eq_fourier]
  simp only [smul_eq_mul]
  congr 1
  push_cast
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hp]

lemma norm_h_le (g : ℝ → ℂ) (t : ℝ) : ‖h g (t : ℂ)‖ ≤ ∫ u, ‖g u‖ := by
  calc
    ‖h g (t : ℂ)‖ ≤ ∫ u : ℝ, ‖g u * Complex.exp (I*(t : ℂ)*(u : ℂ))‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      congr 1
      funext u
      rw [norm_mul]
      have he : I*(t : ℂ)*(u : ℂ) = ((t*u : ℝ) : ℂ)*I := by push_cast; ring
      rw [he, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- Two Fourier differentiation identities give the full inverse-quadratic bound. -/
theorem weighted_norm_h_le {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g)
    (hi : Integrable g) (hi' : Integrable (deriv g))
    (hi'' : Integrable (deriv (deriv g))) (t : ℝ) :
    (1+t^2)*‖h g (t : ℂ)‖ ≤ (∫ u, ‖g u‖)+(∫ u, ‖deriv (deriv g) u‖) := by
  have hd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hd' : Differentiable ℝ (deriv g) :=
    ((contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1+1) g from hg)).2.2).differentiable (by norm_num)
  have he := h_deriv hi' hd' hi'' t
  rw [h_deriv hi hd hi' t] at he
  have he' : h (deriv (deriv g)) (t : ℂ) = -(t : ℂ)^2*h g (t : ℂ) := by
    rw [he]
    ring_nf
    simp [Complex.I_sq]
  have hn : t^2*‖h g (t : ℂ)‖ = ‖h (deriv (deriv g)) (t : ℂ)‖ := by
    rw [he', norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs, _root_.sq_abs]
  calc
    (1+t^2)*‖h g (t : ℂ)‖ = ‖h g (t : ℂ)‖+t^2*‖h g (t : ℂ)‖ := by ring
    _ = ‖h g (t : ℂ)‖+‖h (deriv (deriv g)) (t : ℂ)‖ := by rw [hn]
    _ ≤ _ := add_le_add (norm_h_le g t) (norm_h_le (deriv (deriv g)) t)

/-- The full-line transform agrees with the repository's interval transform on its
supported test class, including complex arguments used for pole evaluations. -/
theorem h_eq_hfun {a : ℝ} {g : ℝ → ℂ} (hg : TestFunctions.IsTestFn a g)
    (hs : ∀ u, a < |u| → g u = 0) (z : ℂ) : h g z = TestFunctions.hfun a g z := by
  rw [h, TestFunctions.hfun, intervalIntegral.integral_of_le (by linarith [hg.nonneg])]
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [] with u
  by_cases hu : u ∈ Ioc (-a) a
  · simp only [indicator_of_mem hu]
  · rw [indicator_of_notMem hu]
    have hz : g u = 0 := by
      by_cases he : u = -a
      · rw [he]; exact hg.left
      · apply hs
        simp only [mem_Ioc, not_and_or, not_lt, not_le] at hu
        rcases hu with hu | hu
        · have hlt : u < -a := lt_of_le_of_ne hu he
          have hneg := neg_abs_le u
          linarith
        · exact hu.trans_le (le_abs_self u)
    rw [hz, zero_mul]

end FleetFullLineFourier
