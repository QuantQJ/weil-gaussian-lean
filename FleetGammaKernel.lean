import GammaExplicitFormula
import FleetGammaDuplication
import FleetGammaConjugation
import FleetGammaReflection

noncomputable section
open Complex ComplexConjugate

namespace FleetGammaKernel

def psi (s : ℂ) : ℂ := deriv Gamma s / Gamma s

theorem kernel_eq_symmetric_psi {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    GammaExplicitFormula.gammaKernel s = -(Real.log Real.pi : ℂ) +
      (psi (s / 2) + psi ((1 - s) / 2)) / 2 := by
  have hhalf : 0 < (s / 2).re := by simp; linarith
  have hd := FleetGammaDuplication.logDeriv_Gamma_two_mul (s / 2) hhalf
  have hc0 : 0 < ((1 - s) / 2).re := by simp; linarith
  have hc1 : ((1 - s) / 2).re < 1 := by simp; linarith
  have hr := FleetGammaReflection.digamma_reflection hc0 hc1
  have he1 : 2 * (s / 2) = s := by ring
  have he2 : 1 - (1 - s) / 2 = s / 2 + 1 / 2 := by ring
  have he3 : (Real.pi : ℂ) * ((1 - s) / 2) = (Real.pi : ℂ) / 2 - (Real.pi : ℂ) * s / 2 := by ring
  rw [he1] at hd
  rw [he2, he3, Complex.sin_pi_div_two_sub, Complex.cos_pi_div_two_sub] at hr
  have hl : (Real.log (2 * Real.pi) : ℂ) = (Real.log 2 : ℂ) + (Real.log Real.pi : ℂ) := by
    rw [Real.log_mul (by norm_num) Real.pi_ne_zero, Complex.ofReal_add]
  unfold GammaExplicitFormula.gammaKernel psi
  rw [hl, Complex.tan_eq_sin_div_cos]
  linear_combination hd + (1 / 2 : ℂ) * hr

/-- The gamma kernel on the critical line is the usual real digamma weight. -/
theorem kernel_critical_line (t : ℝ) :
    GammaExplicitFormula.gammaKernel (1 / 2 + (t : ℂ) * I) =
      (((psi (1 / 4 + (t : ℂ) * I / 2)).re - Real.log Real.pi : ℝ) : ℂ) := by
  have h0 : 0 < (1 / 2 + (t : ℂ) * I).re := by norm_num
  have h1 : (1 / 2 + (t : ℂ) * I).re < 1 := by norm_num
  rw [kernel_eq_symmetric_psi h0 h1]
  have he1 : (1 / 2 + (t : ℂ) * I) / 2 = 1 / 4 + (t : ℂ) * I / 2 := by ring
  have he2 : (1 - (1 / 2 + (t : ℂ) * I)) / 2 = conj (1 / 4 + (t : ℂ) * I / 2) := by
    simp only [map_add, map_div₀, map_mul, map_one, map_ofNat, conj_ofReal, conj_I]
    ring
  rw [he1, he2]
  have hz : 0 < (1 / 4 + (t : ℂ) * I / 2).re := by norm_num
  have hc := FleetGammaConjugation.logDeriv_Gamma_conj _ hz
  change psi (conj (1 / 4 + (t : ℂ) * I / 2)) = conj (psi (1 / 4 + (t : ℂ) * I / 2)) at hc
  rw [hc]
  have hs := Complex.add_conj (psi (1 / 4 + (t : ℂ) * I / 2))
  push_cast
  rw [hs]
  push_cast
  ring

/-- The real critical-line archimedean weight, with the logarithmic constant included. -/
def weight (t : ℝ) : ℝ := (psi (1 / 4 + (t : ℂ) * I / 2)).re - Real.log Real.pi

theorem weight_neg (t : ℝ) : weight (-t) = weight t := by
  have hz : 0 < (1 / 4 + (t : ℂ) * I / 2).re := by norm_num
  have he : (1 / 4 + ((-t : ℝ) : ℂ) * I / 2) = conj (1 / 4 + (t : ℂ) * I / 2) := by
    simp only [map_add, map_div₀, map_mul, map_one, map_ofNat, conj_ofReal, conj_I, ofReal_neg]
    ring
  unfold weight psi
  rw [he, FleetGammaConjugation.logDeriv_Gamma_conj _ hz, conj_re]

/-- Convert the reflected critical-line pairing to the conventional test-function pairing. -/
theorem critical_integral_eq (a : ℝ) (g : ℝ → ℂ) :
    (∫ t : ℝ, GammaExplicitFormula.gammaKernel (1 / 2 + (t : ℂ) * I) *
      TestFunctions.Gt a g (1 / 2 - (t : ℂ) * I)) =
    ∫ t : ℝ, TestFunctions.hfun a g (t : ℂ) * (weight t : ℂ) := by
  have he (t : ℝ) : TestFunctions.Gt a g (1 / 2 - (t : ℂ) * I) =
      TestFunctions.hfun a g ((-t : ℝ) : ℂ) := by
    have ha : (1 / 2 - (t : ℂ) * I) = 1 / 2 + I * ((-t : ℝ) : ℂ) := by push_cast; ring
    rw [ha, TestFunctions.Gt_half_add_I_mul]
  simp_rw [kernel_critical_line, he]
  change (∫ t : ℝ, (weight t : ℂ) * TestFunctions.hfun a g ((-t : ℝ) : ℂ)) = _
  have hc (t : ℝ) : (weight t : ℂ) * TestFunctions.hfun a g ((-t : ℝ) : ℂ) =
      TestFunctions.hfun a g ((-t : ℝ) : ℂ) * (weight (-t) : ℂ) := by rw [weight_neg]; ring
  simp_rw [hc]
  exact MeasureTheory.integral_neg_eq_self
    (fun t : ℝ => TestFunctions.hfun a g (t : ℂ) * (weight t : ℂ)) MeasureTheory.volume

end FleetGammaKernel
