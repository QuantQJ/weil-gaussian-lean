import TestFunctions
import Mathlib

namespace FleetOffLineResponse
open Complex MeasureTheory TestFunctions

/-- Symmetric displacement cancels the linear response exactly, for complex test functions. -/
theorem symmetric_response {a : ℝ} {g : ℝ → ℂ} (hg : Continuous g) (t δ : ℝ) :
    hfun a g ((t : ℂ) + I * δ) + hfun a g ((t : ℂ) - I * δ) - 2 * hfun a g (t : ℂ) =
      2 * ∫ u in (-a)..a, g u * exp (I * (t : ℂ) * u) * (cosh ((δ : ℂ) * u) - 1) := by
  have hi (s : ℂ) : IntervalIntegrable (fun u : ℝ => g u * exp (I * s * u)) volume (-a) a :=
    (hg.mul (by fun_prop)).intervalIntegrable _ _
  have he (u : ℝ) :
      g u * exp (I * ((t : ℂ)+I*δ) * u) + g u * exp (I * ((t : ℂ)-I*δ) * u) -
      2 * (g u * exp (I * (t : ℂ) * u)) =
      2 * (g u * exp (I * (t : ℂ) * u) * (cosh ((δ : ℂ)*u)-1)) := by
    have hp : I * ((t : ℂ)+I*δ) * u = I * (t : ℂ) * u + -((δ : ℂ)*u) := by
      ring_nf
      simp [I_sq, sub_eq_add_neg]
    have hm : I * ((t : ℂ)-I*δ) * u = I * (t : ℂ) * u + (δ : ℂ)*u := by
      ring_nf
      simp [I_sq, sub_eq_add_neg]
    rw [hp, hm, exp_add, exp_add]
    unfold cosh
    ring
  unfold hfun
  rw [← intervalIntegral.integral_add (hi _) (hi _),
    ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub ((hi _).add (hi _)) ((hi _).const_mul 2),
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _
  exact he u

private theorem sinh_le_mul_exp (x : ℝ) :
    Real.sinh x ≤ x * Real.exp x := by
  have he := Real.add_one_le_exp (-2*x)
  have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos x).le
  have hid : Real.exp x * Real.exp (-2*x) = Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hid] at hm
  rw [Real.sinh_eq]
  nlinarith

/-- A global second-order bound, with an explicit constant, for real arguments. -/
theorem norm_cosh_sub_one (x : ℝ) :
    ‖Complex.cosh (x : ℂ) - 1‖ ≤ x^2 * Real.exp |x| / 2 := by
  have hy : 0 ≤ |x|/2 := by positivity
  have hs := sinh_le_mul_exp (|x|/2)
  have hsn : 0 ≤ Real.sinh (|x|/2) := Real.sinh_nonneg_iff.mpr hy
  have hsq := mul_self_le_mul_self hsn hs
  have hexp : Real.exp (|x|/2) ^ 2 = Real.exp |x| := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hcosh := Real.cosh_two_mul (|x|/2)
  have hcoshsq := Real.cosh_sq (|x|/2)
  have hc : Real.cosh x - 1 = 2 * Real.sinh (|x|/2)^2 := by
    have ht : 2*(|x|/2) = |x| := by ring
    rw [ht, Real.cosh_abs] at hcosh
    nlinarith
  have hn : 0 ≤ Real.cosh x - 1 := by nlinarith [Real.one_le_cosh x]
  rw [← Complex.ofReal_cosh, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, _root_.abs_of_nonneg hn, hc]
  have habs : |x|^2 = x^2 := _root_.sq_abs x
  nlinarith [sq_nonneg (Real.sinh (|x|/2)), hexp]

/-- A finite-support second-order response bound. This is an upper bound, not an invisibility theorem. -/
theorem norm_symmetric_response_le {a : ℝ} {g : ℝ → ℂ} (ha : 0 ≤ a)
    (hg : Continuous g) (t δ : ℝ) :
    ‖hfun a g ((t : ℂ) + I * δ) + hfun a g ((t : ℂ) - I * δ) -
      2 * hfun a g (t : ℂ)‖ ≤
      δ^2 * a^2 * Real.exp (|δ| * a) * (∫ u in (-a)..a, ‖g u‖) := by
  let B : ℝ := δ^2 * a^2 * Real.exp (|δ| * a) / 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hp (u : ℝ) (hu : u ∈ Set.Icc (-a) a) :
      ‖g u * exp (I * (t : ℂ) * u) * (cosh ((δ : ℂ)*u)-1)‖ ≤ ‖g u‖*B := by
    have huabs : |u| ≤ a := abs_le.mpr hu
    have hd : |δ*u| ≤ |δ| * a := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left huabs (abs_nonneg δ)
    have hs : (δ*u)^2 ≤ δ^2*a^2 := by
      have hu2 : u^2 ≤ a^2 := by nlinarith [_root_.sq_abs u, abs_nonneg u]
      nlinarith [sq_nonneg δ]
    have hc := norm_cosh_sub_one (δ*u)
    push_cast at hc
    have hx : ‖cosh ((δ : ℂ)*u)-1‖ ≤ B := by
      apply hc.trans
      dsimp [B]
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul hs (Real.exp_le_exp.mpr hd) (Real.exp_pos _).le (by positivity)
    have he : ‖exp (I * (t : ℂ) * u)‖ = 1 := by rw [Complex.norm_exp]; simp
    rw [norm_mul, norm_mul, he, mul_one]
    exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)
  have hint : IntervalIntegrable (fun u : ℝ =>
      ‖g u * exp (I * (t : ℂ) * u) * (cosh ((δ : ℂ)*u)-1)‖) volume (-a) a := by
    apply Continuous.intervalIntegrable
    apply Continuous.norm
    exact (hg.mul (by fun_prop)).mul (by fun_prop)
  have hbound : IntervalIntegrable (fun u : ℝ => ‖g u‖*B) volume (-a) a :=
    (hg.norm.mul continuous_const).intervalIntegrable _ _
  have hi := (intervalIntegral.norm_integral_le_integral_norm (f := fun u : ℝ =>
      g u * exp (I * (t : ℂ) * u) * (cosh ((δ : ℂ)*u)-1)) (by linarith : -a ≤ a)).trans
    (intervalIntegral.integral_mono_on (by linarith : -a ≤ a) hint hbound hp)
  rw [intervalIntegral.integral_mul_const] at hi
  rw [symmetric_response hg t δ, norm_mul]
  norm_num only [Complex.norm_ofNat] 
  dsimp [B] at hi
  skip
  nlinarith

end FleetOffLineResponse

#print axioms FleetOffLineResponse.symmetric_response

#print axioms FleetOffLineResponse.norm_cosh_sub_one
#print axioms FleetOffLineResponse.norm_symmetric_response_le
