import Mathlib

namespace FleetGammaConjugation

open Complex ComplexConjugate

private lemma gamma_differentiable_of_re_pos (z : ℂ) (hz : 0 < z.re) :
    DifferentiableAt ℂ Complex.Gamma z := by
  apply Complex.differentiableAt_Gamma
  intro n he
  have hre := congrArg Complex.re he
  simp at hre
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

private lemma hasDerivAt_gamma_real_translate (z : ℂ) (hz : 0 < z.re) :
    HasDerivAt (fun t : ℝ => Gamma (z + t)) (deriv Gamma z) 0 := by
  have h : HasDerivAt (fun w : ℂ => Gamma (z + w)) (deriv Gamma z) (0 : ℂ) := by
    have h0 := (gamma_differentiable_of_re_pos z hz).hasDerivAt.comp_of_eq
      (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).const_add z) (by simp)
    simp only [mul_one] at h0
    exact h0
  exact h.comp_ofReal

/-- Gamma's complex derivative respects conjugation on the right half-plane.
The proof differentiates along real translates, where conjugation is real linear. -/
theorem deriv_Gamma_conj (z : ℂ) (hz : 0 < z.re) :
    deriv Gamma (conj z) = conj (deriv Gamma z) := by
  have h₁ := hasDerivAt_gamma_real_translate (conj z) (by simpa using hz)
  have h₂ := (hasDerivAt_gamma_real_translate z hz).star
  have h₂' : HasDerivAt (fun t : ℝ => Gamma (conj z + t))
      (conj (deriv Gamma z)) 0 := by
    simpa only [Complex.star_def, ← Complex.Gamma_conj, map_add, Complex.conj_ofReal] using h₂
  exact h₁.unique h₂'

/-- The logarithmic derivative of Gamma respects conjugation on the right half-plane. -/
theorem logDeriv_Gamma_conj (z : ℂ) (hz : 0 < z.re) :
    deriv Gamma (conj z) / Gamma (conj z) = conj (deriv Gamma z / Gamma z) := by
  rw [deriv_Gamma_conj z hz, Complex.Gamma_conj, map_div₀]

end FleetGammaConjugation

#print axioms FleetGammaConjugation.deriv_Gamma_conj
#print axioms FleetGammaConjugation.logDeriv_Gamma_conj
