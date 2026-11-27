import FleetFullLineLinearity
import FleetExponentialFourierBound
import FleetArchimedeanFunctionalBound

noncomputable section
open Complex MeasureTheory
namespace FleetArithmeticContinuity

/-- One exponential envelope controls the function and its first two derivatives. -/
structure Bound (E : ℝ) (g : ℝ → ℂ) : Prop where
  smooth : ContDiff ℝ 2 g
  zero : ∀ u, ‖g u‖ ≤ E * FleetExponentialEnvelope.envelope 3 u
  first : ∀ u, ‖deriv g u‖ ≤ E * FleetExponentialEnvelope.envelope 3 u
  second : ∀ u, ‖deriv (deriv g) u‖ ≤ E * FleetExponentialEnvelope.envelope 3 u

/-- A single finite constant bounds the full arithmetic functional in the
exponential C² topology, including absolute convergence of the Gamma integral. -/
theorem exists_rhs_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : ℝ) (g : ℝ → ℂ),
    0 ≤ E → Bound E g →
    Integrable (fun t : ℝ => FleetFullLineFourier.h g t * (FleetGammaKernel.weight t : ℂ)) ∧
    ‖FleetFullLineArithmetic.rhs g‖ ≤ C * E := by
  obtain ⟨K, hK, hk⟩ := FleetArchimedeanFunctionalBound.exists_weight_integral_bound
  let A : ℝ := ‖(1 / (2 * (Real.pi : ℂ)))‖
  let Z : ℝ := ∑' n : ℕ, 1/(n : ℝ)^2
  have hA : 0 ≤ A := norm_nonneg _
  have hZ : 0 ≤ Z := tsum_nonneg (fun n => by positivity)
  refine ⟨8/5 + A*K*(4/3) + 2*Z, by positivity, ?_⟩
  intro E g hE hg
  have hgi := FleetExponentialEnvelope.integrable_of_bound (by norm_num : (0:ℝ)<3)
    hE hg.smooth.continuous.aestronglyMeasurable hg.zero
  have hG : AEStronglyMeasurable (fun t : ℝ => FleetFullLineFourier.h g t) :=
    (FleetFullLineLinearity.continuous_h_real hgi).aestronglyMeasurable
  have ht (t : ℝ) : ‖FleetFullLineFourier.h g t‖ ≤ (4*E/3)/(1+t^2) := by
    apply (le_div_iff₀ (by positivity : (0:ℝ)<1+t^2)).mpr
    simpa only [mul_comm] using
      FleetExponentialFourierBound.weighted_norm_h_le hE hg.smooth hg.zero hg.first hg.second t
  obtain ⟨hi, hb⟩ := hk _ hG (4*E/3) ht
  refine ⟨hi, ?_⟩
  have hp := FleetExponentialFourierBound.pole_norm_h_le hE hg.smooth.continuous.aestronglyMeasurable hg.zero
  have hpg : FleetPrimeFunctionalBound.ExponentialBound E g := hg.zero
  have hn := FleetPrimeFunctionalBound.norm_primeSum_le hE hpg
  have hnr := FleetPrimeFunctionalBound.norm_primeSum_le hE (FleetPrimeFunctionalBound.bound_reflect hpg)
  have ha : ‖FleetFullLineArithmetic.archimedean g‖ ≤ A*(K*(4*E/3)) := by
    unfold FleetFullLineArithmetic.archimedean
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hb hA
  unfold FleetFullLineArithmetic.rhs
  calc
    _ ≤ ‖FleetFullLineFourier.h g (I/2)‖ + ‖FleetFullLineFourier.h g (-I/2)‖ +
        ‖FleetFullLineArithmetic.archimedean g‖ + ‖GammaExplicitFormula.primeSum g‖ +
        ‖GammaExplicitFormula.primeSum (GammaExplicitFormula.reflect g)‖ := by
      calc
        _ ≤ ‖FleetFullLineFourier.h g (I/2) + FleetFullLineFourier.h g (-I/2) +
          FleetFullLineArithmetic.archimedean g - GammaExplicitFormula.primeSum g‖ +
          ‖GammaExplicitFormula.primeSum (GammaExplicitFormula.reflect g)‖ := norm_sub_le _ _
        _ ≤ _ := by gcongr; exact (norm_sub_le _ _).trans (by gcongr; exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _))
    _ ≤ 4*E/5 + 4*E/5 + A*(K*(4*E/3)) + E*Z + E*Z := by
      gcongr
      · exact hp.1
      · exact hp.2
    _ = (8/5 + A*K*(4/3) + 2*Z)*E := by ring

end FleetArithmeticContinuity
