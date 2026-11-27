import FleetKernelGrowth
import FleetGammaContourLimit

noncomputable section
open Complex MeasureTheory TestFunctions
open scoped Real ArithmeticFunction

namespace FleetStandardExplicitFormula

/-- The conventional critical-line digamma functional, with the log-pi constant included. -/
def standardArchimedean (a : ℝ) (g : ℝ → ℂ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ t : ℝ, hfun a g (t : ℂ) * (FleetGammaKernel.weight t : ℂ)

/-- Unconditional normalization: no growth, contour, RH, or spectrum hypothesis remains. -/
theorem archimedean_eq_standard {a : ℝ} {g : ℝ → ℂ} (hg : IsTestFn a g) :
    GammaExplicitFormula.archimedean a g = standardArchimedean a g := by
  obtain ⟨C, hC⟩ := FleetKernelGrowth.exists_kernel_log_bound
  exact FleetGammaContourLimit.archimedean_eq_digamma_of_bound hg hC

/-- The conventional integral is absolutely convergent for the stated test class. -/
theorem integrable_standard {a : ℝ} {g : ℝ → ℂ} (hg : IsTestFn a g) :
    Integrable (fun t : ℝ => hfun a g (t : ℂ) * (FleetGammaKernel.weight t : ℂ)) := by
  obtain ⟨C, hC⟩ := FleetKernelGrowth.exists_kernel_log_bound
  have hi := (FleetGammaContourLimit.integrable_critical hg hC).comp_neg
  apply hi.congr
  filter_upwards [] with t
  have he : (1 / 2 - ((-t : ℝ) : ℂ) * I) = 1 / 2 + I * (t : ℂ) := by push_cast; ring
  rw [FleetGammaKernel.kernel_critical_line, he, Gt_half_add_I_mul]
  change (FleetGammaKernel.weight (-t) : ℂ) * hfun a g (t : ℂ) = _
  rw [FleetGammaKernel.weight_neg]
  ring

/-- The unconditional two-sided explicit formula with the conventional digamma integral. -/
theorem explicit_formula_standard {ι : Type*} {zeros : ι → ℂ}
    (hz : ZeroSumLimit.MultEnum zeros) {a : ℝ} {g : ℝ → ℂ} (hg : IsTestFn a g)
    (hsupp : ∀ u, a < |u| → g u = 0) :
    HasSum (fun i => hfun a g (Reduction.ordinate (zeros i)))
      (Gt a g 0 + Gt a g 1 + standardArchimedean a g -
        ∑' n : ℕ, (Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2) : ℂ) *
          (g (Real.log n) + g (-Real.log n))) := by
  rw [← archimedean_eq_standard hg]
  exact GammaExplicitFormula.explicit_formula_two_sided hz hg hsupp

/-- Prime and conventional archimedean terms, with no zeta or zero data in the definition. -/
def standardRHS (a : ℝ) (g : ℝ → ℂ) : ℂ :=
  Gt a g 0 + Gt a g 1 + standardArchimedean a g -
    GammaExplicitFormula.primeSum g - GammaExplicitFormula.primeSum (GammaExplicitFormula.reflect g)

theorem gammaRHS_eq_standardRHS {a : ℝ} {g : ℝ → ℂ} (hg : IsTestFn a g) :
    GammaExplicitFormula.gammaRHS a g = standardRHS a g := by
  rw [GammaExplicitFormula.gammaRHS_eq_two_poles, archimedean_eq_standard hg]
  rfl

def RealSpectrumRealizesStandard {ι : Type*} (γ : ι → ℝ) : Prop :=
  ∀ (a : ℝ) (g : ℝ → ℂ), IsTestFn a g → (∀ u, a < |u| → g u = 0) →
    HasSum (fun i => hfun a g (γ i)) (standardRHS a g)

theorem realizes_standard_iff {ι : Type*} (γ : ι → ℝ) :
    RealSpectrumRealizesStandard γ ↔ GammaExplicitFormula.RealSpectrumRealizesGamma γ := by
  constructor
  · intro h a g hg hs
    rw [gammaRHS_eq_standardRHS hg]
    exact h a g hg hs
  · intro h a g hg hs
    rw [← gammaRHS_eq_standardRHS hg]
    exact h a g hg hs

/-- Equivalent realization criterion with the standard functional. This does not construct a spectrum. -/
theorem RH_iff_exists_standard_spectrum :
    RiemannHypothesis ↔ ∃ (ι : Type) (γ : ι → ℝ),
      Summable (fun i => 1 / (1 + (γ i) ^ 2)) ∧ RealSpectrumRealizesStandard γ := by
  rw [GammaExplicitFormula.RH_iff_exists_gamma_spectrum]
  constructor
  · rintro ⟨ι, γ, hs, hr⟩
    exact ⟨ι, γ, hs, (realizes_standard_iff γ).mpr hr⟩
  · rintro ⟨ι, γ, hs, hr⟩
    exact ⟨ι, γ, hs, (realizes_standard_iff γ).mp hr⟩

end FleetStandardExplicitFormula
