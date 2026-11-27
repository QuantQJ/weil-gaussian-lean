import FleetGammaFiniteProduct
import FleetDigammaSeries
import Mathlib

noncomputable section
open Complex Filter Topology

namespace FleetGammaIdentification

lemma tendsto_log_sub_harmonic_succ :
    Tendsto (fun n : ℕ => (Real.log n : ℂ) - (harmonic (n + 1) : ℂ)) atTop
      (𝓝 (-(Real.eulerMascheroniConstant : ℂ))) := by
  have hi : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hr := (Real.tendsto_harmonic_sub_log.add hi).neg
  have hr' : Tendsto (fun n : ℕ => Real.log n - (harmonic (n + 1) : ℝ)) atTop
      (𝓝 (-Real.eulerMascheroniConstant)) := by
    convert hr using 1
    · funext n
      rw [harmonic_succ]
      push_cast
      ring
    · simp
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hr'
  simpa only [Function.comp_def, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_ratCast] using hc

theorem tendsto_logApprox (z : ℂ) :
    Tendsto (fun n : ℕ => FleetGammaFiniteProduct.logApprox n z) atTop
      (𝓝 (FleetDigammaSeries.regularizedLogGamma z)) := by
  have hsum := (FleetDigammaSeries.summable_q z).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have h := (tendsto_log_sub_harmonic_succ.const_mul (z - 1)).sub hsum
  simpa [FleetGammaFiniteProduct.logApprox_eq_regularized, FleetDigammaSeries.regularizedLogGamma,
    FleetDigammaSeries.q, mul_neg, neg_mul, mul_comm] using h

/-- The regularized logarithm series exponentiates to Gamma on the right half-plane. -/
theorem exp_regularizedLogGamma (z : ℂ) (hz : 0 < z.re) :
    Complex.exp (FleetDigammaSeries.regularizedLogGamma z) = Complex.Gamma z := by
  exact tendsto_nhds_unique (Complex.continuous_exp.continuousAt.tendsto.comp (tendsto_logApprox z))
    (FleetGammaFiniteProduct.tendsto_exp_logApprox z hz)

/-- The digamma partial-fraction series, obtained without differentiating a pointwise limit. -/
theorem digamma_eq_series (z : ℂ) (hz : 0 < z.re) :
    deriv Complex.Gamma z / Complex.Gamma z = -(Real.eulerMascheroniConstant : ℂ) -
      ∑' k : ℕ, ((z + (k : ℂ))⁻¹ - ((k : ℂ) + 1)⁻¹) := by
  have he : (fun w : ℂ => Complex.exp (FleetDigammaSeries.regularizedLogGamma w)) =ᶠ[𝓝 z]
      Complex.Gamma := by
    have ho : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds hz] with w hw
    exact exp_regularizedLogGamma w hw
  have hd := (FleetDigammaSeries.hasDerivAt_regularizedLogGamma hz).cexp
  have hd' := hd.congr_of_eventuallyEq he.symm
  rw [exp_regularizedLogGamma z hz] at hd'
  rw [hd'.deriv]
  have hn := Complex.Gamma_ne_zero_of_re_pos hz
  field_simp

end FleetGammaIdentification
