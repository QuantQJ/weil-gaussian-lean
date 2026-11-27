import Mathlib

namespace FleetGammaDuplication

open Complex

private lemma gamma_differentiable_of_re_pos (z : ℂ) (hz : 0 < z.re) :
    DifferentiableAt ℂ Complex.Gamma z := by
  apply Complex.differentiableAt_Gamma
  intro n he
  have hre := congrArg Complex.re he
  simp at hre
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- Logarithmically differentiated Gamma duplication on the right half-plane. -/
theorem logDeriv_Gamma_two_mul (z : ℂ) (hz : 0 < z.re) :
    deriv Complex.Gamma (2*z) / Complex.Gamma (2*z) =
      (Real.log 2 : ℂ) +
        (deriv Complex.Gamma z / Complex.Gamma z +
          deriv Complex.Gamma (z+1/2) / Complex.Gamma (z+1/2))/2 := by
  have hzhalf : 0 < (z + 1 / 2).re := by simp; linarith
  have hzdouble : 0 < (2 * z).re := by simp; linarith
  have hG := (gamma_differentiable_of_re_pos z hz).hasDerivAt
  have hH := ((gamma_differentiable_of_re_pos (z + 1 / 2) hzhalf).hasDerivAt).comp z
    ((hasDerivAt_id z).add_const (1 / 2))
  have hD := ((gamma_differentiable_of_re_pos (2 * z) hzdouble).hasDerivAt).comp z
    ((hasDerivAt_id z).const_mul 2)
  have hP := (((hasDerivAt_id z).const_mul (2 : ℂ)).const_sub 1).const_cpow
    (c := (2 : ℂ)) (Or.inl (by norm_num))
  have hleft := hG.mul hH
  have hright := (hD.mul hP).mul_const (Real.sqrt Real.pi : ℂ)
  have heq : (fun w : ℂ => Gamma w * Gamma (w + 1 / 2)) =
      (fun w : ℂ => Gamma (2 * w) * (2 : ℂ) ^ (1 - 2 * w) * (Real.sqrt Real.pi : ℂ)) :=
    funext Complex.Gamma_mul_Gamma_add_half
  simp only [Function.comp_apply, id_eq] at hright hleft
  have hright' : HasDerivAt (fun w : ℂ => Gamma w * Gamma (w + 1 / 2))
      ((deriv Gamma (2 * z) * (2 * 1) * 2 ^ (1 - 2 * z) +
        Gamma (2 * z) * (2 ^ (1 - 2 * z) * Complex.log 2 * -(2 * 1))) *
          (Real.sqrt Real.pi : ℂ)) z := by
    rw [heq]
    exact hright
  have hleft' : HasDerivAt (fun w : ℂ => Gamma w * Gamma (w + 1 / 2))
      (deriv Gamma z * Gamma (z + 1 / 2) + Gamma z * (deriv Gamma (z + 1 / 2) * 1)) z := hleft
  have hdiff := hleft'.unique hright'
  have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
    exact (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  simp only [mul_one, hlog] at hdiff
  have hdup := Complex.Gamma_mul_Gamma_add_half z
  have hnG := Complex.Gamma_ne_zero_of_re_pos hz
  have hnH := Complex.Gamma_ne_zero_of_re_pos hzhalf
  have hnD := Complex.Gamma_ne_zero_of_re_pos hzdouble
  have halg (a b c da db dc e l : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
      (h₁ : da * b + a * db = (dc * 2 - c * 2 * l) * e)
      (h₂ : a * b = c * e) : dc / c = l + (da / a + db / b) / 2 := by
    field_simp
    linear_combination -c * h₁ + (2 * dc - 2 * c * l) * h₂
  apply halg (Gamma z) (Gamma (z + 1 / 2)) (Gamma (2 * z))
    (deriv Gamma z) (deriv Gamma (z + 1 / 2)) (deriv Gamma (2 * z))
    ((2 : ℂ) ^ (1 - 2 * z) * (Real.sqrt Real.pi : ℂ)) (Real.log 2 : ℂ)
    hnG hnH hnD
  · linear_combination hdiff
  · linear_combination hdup

end FleetGammaDuplication
