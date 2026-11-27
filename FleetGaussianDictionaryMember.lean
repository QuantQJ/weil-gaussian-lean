import GaussianTest
import FleetArithmeticContinuity

noncomputable section
namespace FleetGaussianDictionaryMember
open GaussianTest FleetExponentialEnvelope FleetArithmeticContinuity

lemma h_eq_gaussHat (b α : ℝ) (z : ℂ) :
    FleetFullLineFourier.h (gauss b α) z = gaussHat b α z := rfl

lemma h_gauss_eq {b : ℝ} (hb : 0 < b) (α : ℝ) (z : ℂ) :
    FleetFullLineFourier.h (gauss b α) z =
      (Real.sqrt (Real.pi/b) : ℂ) * Complex.exp (-(z-α)^2/(4*b)) := gaussHat_eq hb α z

lemma polynomial_envelope {b : ℝ} (hb : 0 < b) (A₀ A₁ A₂ : ℝ)
    (h0 : 0 ≤ A₀) (h1 : 0 ≤ A₁) (h2 : 0 ≤ A₂) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ u : ℝ,
      (A₀+A₁*|u|+A₂*u^2)*Real.exp (-b*u^2) ≤ E*envelope 3 u := by
  obtain ⟨E, hE, he⟩ := majorant hb (by norm_num : (0:ℝ)≤3) A₀ A₁ A₂ h0 h1 h2
  refine ⟨E, hE, ?_⟩
  intro u
  have hh := he u
  have hex : Real.exp (-(b/4)*u^2) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg u))
  have hc := hh.trans (mul_le_of_le_one_right hE hex)
  have hp := mul_le_mul_of_nonneg_right hc (Real.exp_pos (-3*|u|)).le
  have heq : Real.exp (3*|u|)*Real.exp (-3*|u|) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  simpa only [mul_assoc, heq, mul_one, envelope] using hp

lemma deriv_gauss (b α : ℝ) : deriv (gauss b α) = fun u => gaussD b α u * gauss b α u := by
  funext u
  exact (hasDerivAt_gauss b α u).deriv

lemma deriv2_gauss (b α : ℝ) : deriv (deriv (gauss b α)) =
    fun u => (-2*(b : ℂ)+gaussD b α u^2)*gauss b α u := by
  rw [deriv_gauss]
  funext u
  exact (hasDerivAt_gauss' b α u).deriv

lemma norm_deriv2_le {b : ℝ} (hb : 0 < b) (α u : ℝ) :
    ‖deriv (deriv (gauss b α)) u‖ ≤
      (2*b+|α|^2+(4*b*|α|)*|u|+(4*b^2)*u^2)*Real.exp (-b*u^2) := by
  rw [deriv2_gauss, norm_mul, norm_gauss]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  calc
    ‖-2*(b : ℂ)+gaussD b α u^2‖ ≤ ‖-2*(b : ℂ)‖+‖gaussD b α u^2‖ := norm_add_le _ _
    _ = 2*b+‖gaussD b α u‖^2 := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]
      norm_num
    _ ≤ 2*b+(2*b*|u|+|α|)^2 := by
      gcongr
      exact norm_gaussD_le hb α u
    _ = _ := by rw [← sq_abs u]; ring

 theorem exists_bound {b : ℝ} (hb : 0 < b) (α : ℝ) :
    ∃ E : ℝ, 0 ≤ E ∧ Bound E (gauss b α) := by
  obtain ⟨E0,hE0,h0⟩ := polynomial_envelope hb 1 0 0 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨E1,hE1,h1⟩ := polynomial_envelope hb |α| (2*b) 0 (abs_nonneg _) (by positivity) (by norm_num)
  obtain ⟨E2,hE2,h2⟩ := polynomial_envelope hb (2*b+|α|^2) (4*b*|α|) (4*b^2) (by positivity) (by positivity) (by positivity)
  refine ⟨E0+E1+E2, by positivity, ⟨gauss_contDiff b α 2, ?_, ?_, ?_⟩⟩
  · intro u
    rw [norm_gauss]
    have hh : Real.exp (-b*u^2) ≤ E0*envelope 3 u := by simpa using h0 u
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)
  · intro u
    rw [deriv_gauss, norm_mul, norm_gauss]
    have hh := mul_le_mul_of_nonneg_right (norm_gaussD_le hb α u) (Real.exp_pos (-b*u^2)).le
    have he : (2*b*|u|+|α|)*Real.exp (-b*u^2) ≤ E1*envelope 3 u := by
      simpa [add_comm] using h1 u
    exact (hh.trans he).trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)
  · intro u
    exact ((norm_deriv2_le hb α u).trans (h2 u)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)

end FleetGaussianDictionaryMember
#print axioms FleetGaussianDictionaryMember.exists_bound
