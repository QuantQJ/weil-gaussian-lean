import FleetStandardExplicitFormula
import FleetFourierNormalization

noncomputable section
open Complex MeasureTheory TestFunctions
open scoped Real ArithmeticFunction

namespace FleetSeparatedExplicitFormula

/-- The digamma part before extracting the elementary log-pi constant. -/
def digammaWeight (t : ℝ) : ℝ :=
  (FleetGammaKernel.psi (1 / 4 + (t : ℂ) * I / 2)).re

theorem integrable_digamma {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) :
    Integrable (fun t : ℝ => hfun a g (t : ℂ) * (digammaWeight t : ℂ)) := by
  have hi := (FleetStandardExplicitFormula.integrable_standard h).add
    ((FleetFourierNormalization.integrable_hfun h).mul_const (Real.log Real.pi : ℂ))
  apply hi.congr
  filter_upwards [] with t
  dsimp [FleetGammaKernel.weight, digammaWeight]
  push_cast
  ring

/-- The usual presentation has the log-pi contribution outside the integral. -/
theorem standardArchimedean_eq_separated {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g)
    (hsupp : ∀ u, a < |u| → g u = 0) :
    FleetStandardExplicitFormula.standardArchimedean a g =
      -(Real.log Real.pi : ℂ) * g 0 + (1 / (2 * (Real.pi : ℂ))) *
        ∫ t : ℝ, hfun a g (t : ℂ) * (digammaWeight t : ℂ) := by
  have he (t : ℝ) : hfun a g (t : ℂ) * (FleetGammaKernel.weight t : ℂ) =
      hfun a g (t : ℂ) * (digammaWeight t : ℂ) -
        hfun a g (t : ℂ) * (Real.log Real.pi : ℂ) := by
    dsimp [FleetGammaKernel.weight, digammaWeight]
    push_cast
    ring
  unfold FleetStandardExplicitFormula.standardArchimedean
  simp_rw [he]
  rw [integral_sub (integrable_digamma h)
      ((FleetFourierNormalization.integrable_hfun h).mul_const _),
    integral_mul_const, FleetFourierNormalization.integral_hfun h hsupp]
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

/-- Standard unconditional Weil formula, with both pole terms and explicit log-pi term. -/
theorem explicit_formula_separated {ι : Type*} {zeros : ι → ℂ}
    (hz : ZeroSumLimit.MultEnum zeros) {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g)
    (hsupp : ∀ u, a < |u| → g u = 0) :
    HasSum (fun i => hfun a g (Reduction.ordinate (zeros i)))
      (Gt a g 0 + Gt a g 1 - (Real.log Real.pi : ℂ) * g 0 +
        (1 / (2 * (Real.pi : ℂ))) *
          (∫ t : ℝ, hfun a g (t : ℂ) * (digammaWeight t : ℂ)) -
        ∑' n : ℕ, (Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2) : ℂ) *
          (g (Real.log n) + g (-Real.log n))) := by
  have hf := FleetStandardExplicitFormula.explicit_formula_standard hz h hsupp
  rw [standardArchimedean_eq_separated h hsupp] at hf
  convert hf using 1; ring

end FleetSeparatedExplicitFormula
