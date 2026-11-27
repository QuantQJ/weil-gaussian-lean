import FleetFullLineFourier
import FleetPrimeFunctionalBound
import FleetStandardExplicitFormula

noncomputable section
open Complex MeasureTheory

namespace FleetFullLineArithmetic

/-- The conventional archimedean integral for a full-line test function.
Convergence is a separate obligation, not part of this definition. -/
def archimedean (g : ℝ → ℂ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ t : ℝ, FleetFullLineFourier.h g (t : ℂ) * (FleetGammaKernel.weight t : ℂ)

/-- Arithmetic-only functional, extended to full-line test functions. -/
def rhs (g : ℝ → ℂ) : ℂ :=
  FleetFullLineFourier.h g (I / 2) + FleetFullLineFourier.h g (-I / 2) + archimedean g -
    GammaExplicitFormula.primeSum g - GammaExplicitFormula.primeSum (GammaExplicitFormula.reflect g)

theorem archimedean_eq_standard {a : ℝ} {g : ℝ → ℂ} (hg : TestFunctions.IsTestFn a g)
    (hs : ∀ u, a < |u| → g u = 0) :
    archimedean g = FleetStandardExplicitFormula.standardArchimedean a g := by
  unfold archimedean FleetStandardExplicitFormula.standardArchimedean
  simp_rw [FleetFullLineFourier.h_eq_hfun hg hs]

/-- Agreement with the already normalized compact-support explicit formula. -/
theorem rhs_eq_gammaRHS {a : ℝ} {g : ℝ → ℂ} (hg : TestFunctions.IsTestFn a g)
    (hs : ∀ u, a < |u| → g u = 0) :
    rhs g = GammaExplicitFormula.gammaRHS a g := by
  rw [FleetStandardExplicitFormula.gammaRHS_eq_standardRHS hg]
  unfold rhs FleetStandardExplicitFormula.standardRHS
  rw [archimedean_eq_standard hg hs]
  simp_rw [FleetFullLineFourier.h_eq_hfun hg hs]
  have h0 := TestFunctions.Gt_half_add_I_mul a g (I / 2)
  have h1 := TestFunctions.Gt_half_add_I_mul a g (-I / 2)
  have e0 : (1 / 2 : ℂ) + I * (I / 2) = 0 := by ring_nf; simp [I_sq]
  have e1 : (1 / 2 : ℂ) + I * (-I / 2) = 1 := by ring_nf; norm_num [I_sq]
  rw [e0] at h0
  rw [e1] at h1
  rw [← h0, ← h1]

end FleetFullLineArithmetic
