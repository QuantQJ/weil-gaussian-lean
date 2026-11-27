import FleetGaussianArchimedeanNormalization
import FleetArchimedeanTailCertificate
import FleetGaussianPrimeTailCertificate

/-!
An unconditional reduction of the width-one arithmetic functional to a finite
integral and finite prime sums, with an explicit error on the stage-100 window.
The finite quantities themselves still require numerical enclosures. This is
not a proof of the candidate's residual bound or of stage-100 feasibility.
-/

noncomputable section
open MeasureTheory Set GaussianTest

namespace FleetGaussianFiniteReduction

def finiteArchimedean (q : ℝ) : ℂ :=
  (((1 / Real.sqrt Real.pi) *
    ∫ u : ℝ in Ioc (-12) 12, FleetArchimedeanTailCertificate.integrand q u : ℝ) : ℂ)

/-- The exact finite target. All prime powers through 1000 are retained by
the von Mangoldt sum; the archimedean integral is restricted to [-12,12]. -/
def finiteRHS (q : ℝ) : ℂ :=
  FleetFullLineFourier.h (gauss 1 q) (Complex.I / 2) +
  FleetFullLineFourier.h (gauss 1 q) (-Complex.I / 2) + finiteArchimedean q -
  FleetGaussianPrimeTailCertificate.partialSum 1000 q -
  FleetGaussianPrimeTailCertificate.partialSum 1000 (-q)

/-- A concrete tail bound for the original complex archimedean functional. -/
theorem archimedean_sub_finite_le {q : ℝ} (hq : |q| ≤ 100) :
    ‖FleetFullLineArithmetic.archimedean (gauss 1 q) - finiteArchimedean q‖ ≤
      (1 / 10^21 : ℝ) := by
  rw [FleetGaussianArchimedeanNormalization.archimedean_gauss_one]
  unfold finiteArchimedean
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact FleetArchimedeanTailCertificate.normalized_truncation_twelve_le hq

/-- The complete infinite arithmetic target differs from the finite target
by at most three trillionths, uniformly throughout the stage-100 window.
This theorem has no assumed external numerical enclosures. -/
theorem rhs_sub_finiteRHS_le {q : ℝ} (hq : |q| ≤ 100) :
    ‖FleetFullLineArithmetic.rhs (gauss 1 q) - finiteRHS q‖ ≤
      (3 / 1000000000000 : ℝ) := by
  have he : FleetFullLineArithmetic.rhs (gauss 1 q) - finiteRHS q =
      (FleetFullLineArithmetic.archimedean (gauss 1 q) - finiteArchimedean q) -
      ((GammaExplicitFormula.primeSum (gauss 1 q) +
          GammaExplicitFormula.primeSum (GammaExplicitFormula.reflect (gauss 1 q))) -
        (FleetGaussianPrimeTailCertificate.partialSum 1000 q +
          FleetGaussianPrimeTailCertificate.partialSum 1000 (-q))) := by
    unfold FleetFullLineArithmetic.rhs finiteRHS
    ring
  rw [he]
  have ha := archimedean_sub_finite_le hq
  have hp := FleetGaussianPrimeTailCertificate.two_primeSums_truncation_1000_le q
  refine (norm_sub_le _ _).trans ?_
  linarith

end FleetGaussianFiniteReduction
