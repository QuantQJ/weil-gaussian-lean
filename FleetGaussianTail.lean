import Mathlib

namespace FleetGaussianTail
open Real Set MeasureTheory

/-- The quadratic exponent lies below its tangent at L on the positive tail. -/
theorem translated_envelope (σ L v : ℝ) (hL : 0 ≤ L) (hv : 0 ≤ v) :
    (L+v) * exp ((L+v)/2 - σ^2*(L+v)^2/2) ≤
      exp (L/2-σ^2*L^2/2) * ((L+v)*exp (-(σ^2*L-1/2)*v)) := by
  have he : (L+v)/2-σ^2*(L+v)^2/2 =
      (L/2-σ^2*L^2/2) + (-(σ^2*L-1/2)*v) - σ^2*v^2/2 := by ring
  have hb : (L+v)/2-σ^2*(L+v)^2/2 ≤
      (L/2-σ^2*L^2/2) + (-(σ^2*L-1/2)*v) := by
    rw [he]
    nlinarith [sq_nonneg σ, sq_nonneg v, mul_nonneg (sq_nonneg σ) (sq_nonneg v)]
  have ht := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hb) (add_nonneg hL hv)
  rw [Real.exp_add] at ht
  nlinarith

private theorem integrable_exp_tail {κ : ℝ} (hκ : 0 < κ) :
    IntegrableOn (fun v : ℝ => exp (-κ*v)) (Ioi 0) := by
  simpa using (integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := 1) (s := 0) (b := κ) (by norm_num) (by norm_num) hκ)

private theorem integrable_mul_exp_tail {κ : ℝ} (hκ : 0 < κ) :
    IntegrableOn (fun v : ℝ => v*exp (-κ*v)) (Ioi 0) := by
  simpa using (integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := 1) (s := 1) (b := κ) (by norm_num) (by norm_num) hκ)

/-- The tangent-envelope integral is explicitly computable. -/
theorem integral_linear_exp_tail (L κ : ℝ) (hκ : 0 < κ) :
    (∫ v : ℝ in Ioi 0, (L+v)*exp (-κ*v)) = L/κ+1/κ^2 := by
  have hi0 := integrable_exp_tail hκ
  have hi1 := integrable_mul_exp_tail hκ
  have h0 : (∫ v : ℝ in Ioi 0, exp (-κ*v)) = 1/κ := by
    simpa using Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (r := κ) (by norm_num) hκ
  have h1 : (∫ v : ℝ in Ioi 0, v*exp (-κ*v)) = 1/κ^2 := by
    have hh := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := κ) (by norm_num) hκ
    norm_num [Real.Gamma_add_one, Real.Gamma_one] at hh
    simpa [div_pow] using hh
  simp_rw [add_mul]
  rw [integral_add (hi0.const_mul L) hi1, MeasureTheory.integral_const_mul, h0, h1]
  ring

/-- Integrability and the rigorous Gaussian tail bound in translated coordinates. -/
theorem translated_gaussian_tail (σ L : ℝ) (hL : 0 ≤ L)
    (hκ : 0 < σ^2*L-1/2) :
    IntegrableOn (fun v : ℝ => (L+v)*exp ((L+v)/2-σ^2*(L+v)^2/2)) (Ioi 0) ∧
    (∫ v : ℝ in Ioi 0, (L+v)*exp ((L+v)/2-σ^2*(L+v)^2/2)) ≤
      exp (L/2-σ^2*L^2/2) * (L/(σ^2*L-1/2)+1/(σ^2*L-1/2)^2) := by
  let κ := σ^2*L-1/2
  let B := exp (L/2-σ^2*L^2/2)
  have hi : IntegrableOn (fun v : ℝ => B*((L+v)*exp (-κ*v))) (Ioi 0) := by
    have hh := ((integrable_exp_tail hκ).const_mul L).add (integrable_mul_exp_tail hκ)
    unfold IntegrableOn
    simpa only [κ, add_mul, mul_add, Pi.add_apply] using hh.const_mul B
  have hf : IntegrableOn (fun v : ℝ => (L+v)*exp ((L+v)/2-σ^2*(L+v)^2/2)) (Ioi 0) := by
    apply hi.mono' ((show Continuous (fun v : ℝ => (L+v)*exp ((L+v)/2-σ^2*(L+v)^2/2)) by fun_prop).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (add_nonneg hL (le_of_lt hv)) (exp_pos _).le)]
    exact translated_envelope σ L v hL (le_of_lt hv)
  refine ⟨hf, ?_⟩
  have hh := integral_mono_ae hf hi
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv; exact translated_envelope σ L v hL (le_of_lt hv))
  rw [MeasureTheory.integral_const_mul, integral_linear_exp_tail L κ hκ] at hh
  exact hh

/-- The real tail integral and its integrability, in the original logarithmic coordinate.
This is the analytic envelope only; a discrete von Mangoldt tail is not asserted here. -/
theorem gaussian_tail_integral (σ L : ℝ) (hL : 0 ≤ L)
    (hκ : 0 < σ^2*L-1/2) :
    IntegrableOn (fun u : ℝ => u*exp (u/2-σ^2*u^2/2)) (Ioi L) ∧
    (∫ u : ℝ in Ioi L, u*exp (u/2-σ^2*u^2/2)) ≤
      exp (L/2-σ^2*L^2/2) * (L/(σ^2*L-1/2)+1/(σ^2*L-1/2)^2) := by
  obtain ⟨hi, hb⟩ := translated_gaussian_tail σ L hL hκ
  let f : ℝ → ℝ := fun u => u*exp (u/2-σ^2*u^2/2)
  let H := (Ioi (0 : ℝ)).indicator (fun v => f (L+v))
  have hshift : (fun u : ℝ => H (-L+u)) = (Ioi L).indicator f := by
    funext u
    by_cases hu : L < u
    · have hv : 0 < -L+u := by linarith
      simp [H, hu, hv, add_neg_cancel_left]
    · have hv : ¬0 < -L+u := by linarith
      simp [H, hu, hv]
  have hH : Integrable H := by
    exact (integrable_indicator_iff measurableSet_Ioi).mpr hi
  have hfi : IntegrableOn f (Ioi L) := by
    apply (integrable_indicator_iff measurableSet_Ioi).mp
    rw [← hshift]
    exact hH.comp_add_left (-L)
  have he : (∫ u : ℝ in Ioi L, f u) =
      ∫ v : ℝ in Ioi 0, f (L+v) := by
    rw [← integral_indicator measurableSet_Ioi, ← hshift,
      integral_add_left_eq_self H (-L)]
    exact integral_indicator measurableSet_Ioi
  refine ⟨hfi, ?_⟩
  change (∫ u : ℝ in Ioi L, f u) ≤ _
  rw [he]
  exact hb

end FleetGaussianTail

#print axioms FleetGaussianTail.translated_gaussian_tail

#print axioms FleetGaussianTail.gaussian_tail_integral
