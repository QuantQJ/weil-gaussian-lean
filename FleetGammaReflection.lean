import Mathlib

noncomputable section

namespace FleetGammaReflection

open Complex

lemma not_neg_nat_of_re_pos {z : ℂ} (h : 0 < z.re) (n : ℕ) : z ≠ -(n : ℂ) := by
  intro hz
  have hr := congrArg Complex.re hz
  simp only [neg_re, natCast_re] at hr
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

lemma sin_pi_mul_ne_zero {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) :
    Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
  have hr : 0 < (1 - z).re := by simp only [sub_re, one_re]; linarith
  have hg := Complex.Gamma_mul_Gamma_one_sub z
  intro hs
  rw [hs, div_zero] at hg
  exact (mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos h0)
    (Complex.Gamma_ne_zero_of_re_pos hr)) hg

/-- Differentiated Euler reflection on the open strip, with explicit logarithmic derivatives. -/
theorem digamma_reflection {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) :
    deriv Complex.Gamma (1 - z) / Complex.Gamma (1 - z) -
      deriv Complex.Gamma z / Complex.Gamma z =
    (Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * z) /
      Complex.sin ((Real.pi : ℂ) * z) := by
  have hr : 0 < (1 - z).re := by simp only [sub_re, one_re]; linarith
  have hz := (Complex.differentiableAt_Gamma z (not_neg_nat_of_re_pos h0)).hasDerivAt
  have hw := (Complex.differentiableAt_Gamma (1-z) (not_neg_nat_of_re_pos hr)).hasDerivAt
  have hcomp := hw.comp z ((hasDerivAt_id z).const_sub 1)
  have hleft := hz.mul hcomp
  have hsin := (Complex.hasDerivAt_sin ((Real.pi : ℂ) * z)).comp z
    ((hasDerivAt_id z).const_mul (Real.pi : ℂ))
  have hs := sin_pi_mul_ne_zero h0 h1
  have hright := (hasDerivAt_const z (Real.pi : ℂ)).div hsin hs
  have heq : (fun w : ℂ => Complex.Gamma w * Complex.Gamma (1-w)) =
      (fun w : ℂ => (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * w)) := by
    funext w
    exact Complex.Gamma_mul_Gamma_one_sub w
  simp only [Function.comp_def] at hleft hright
  have hleft' : HasDerivAt (fun w : ℂ => Complex.Gamma w * Complex.Gamma (1-w))
      (deriv Complex.Gamma z * Complex.Gamma (1 - z) +
        Complex.Gamma z * (deriv Complex.Gamma (1 - z) * -1)) z := hleft
  rw [heq] at hleft'
  have hd := hleft'.unique hright
  have hg := Complex.Gamma_mul_Gamma_one_sub z
  have hg0 := Complex.Gamma_ne_zero_of_re_pos h0
  have hg1 := Complex.Gamma_ne_zero_of_re_pos hr
  simp only [mul_one, zero_mul, zero_sub] at hd
  have hgprod : Complex.Gamma z * Complex.Gamma (1-z) *
      Complex.sin ((Real.pi : ℂ) * z) = (Real.pi : ℂ) := by
    exact (eq_div_iff hs).mp hg
  rw [eq_div_iff (pow_ne_zero 2 hs)] at hd
  rw [div_sub_div _ _ hg1 hg0, div_eq_div_iff (mul_ne_zero hg1 hg0) hs]
  apply mul_left_cancel₀ hs
  linear_combination -hd - (Real.pi : ℂ) * Complex.cos ((Real.pi : ℂ) * z) * hgprod

end FleetGammaReflection
