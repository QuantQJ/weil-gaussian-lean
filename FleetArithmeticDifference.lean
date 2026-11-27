import FleetArithmeticContinuity

noncomputable section
open Complex MeasureTheory
namespace FleetArithmeticDifference
open FleetArithmeticContinuity FleetFullLineFourier

lemma integrable_of_Bound {E : ℝ} {g : ℝ → ℂ} (hE : 0 ≤ E) (hg : Bound E g) :
    Integrable g := FleetExponentialEnvelope.integrable_of_bound (by norm_num : (0:ℝ)<3)
      hE hg.smooth.continuous.aestronglyMeasurable hg.zero

lemma h_sub_imaginary {Ef Eg y : ℝ} {f g : ℝ → ℂ}
    (hfE : 0 ≤ Ef) (hgE : 0 ≤ Eg) (hf : Bound Ef f) (hg : Bound Eg g)
    (hy : |y| < 3) : h (f-g) (I*(y : ℂ)) = h f (I*(y : ℂ))-h g (I*(y : ℂ)) := by
  apply FleetFullLineLinearity.h_sub
  · exact FleetExponentialFourierBound.imaginary_integrable hfE
      hf.smooth.continuous.aestronglyMeasurable hf.zero hy
  · exact FleetExponentialFourierBound.imaginary_integrable hgE
      hg.smooth.continuous.aestronglyMeasurable hg.zero hy

/-- Every component is subtracted only after its integral or series convergence is proved. -/
theorem rhs_sub {Ef Eg : ℝ} {f g : ℝ → ℂ}
    (hfE : 0 ≤ Ef) (hgE : 0 ≤ Eg) (hf : Bound Ef f) (hg : Bound Eg g) :
    FleetFullLineArithmetic.rhs (f-g) = FleetFullLineArithmetic.rhs f-FleetFullLineArithmetic.rhs g := by
  obtain ⟨C, _, hb⟩ := exists_rhs_bound
  have hA := FleetFullLineLinearity.archimedean_sub (integrable_of_Bound hfE hf)
    (integrable_of_Bound hgE hg) (hb Ef f hfE hf).1 (hb Eg g hgE hg).1
  have hp : h (f-g) (I/2) = h f (I/2)-h g (I/2) := by
    convert h_sub_imaginary hfE hgE hf hg (by norm_num [abs_div] : |(1/2 : ℝ)| < 3) using 1 <;> norm_num <;> ring_nf
  have hm : h (f-g) (-I/2) = h f (-I/2)-h g (-I/2) := by
    convert h_sub_imaginary hfE hgE hf hg (by norm_num [abs_div] : |(-1/2 : ℝ)| < 3) using 1 <;> norm_num <;> ring_nf
  have sf := FleetPrimeFunctionalBound.summable_terms hfE (show FleetPrimeFunctionalBound.ExponentialBound Ef f from hf.zero)
  have sg := FleetPrimeFunctionalBound.summable_terms hgE (show FleetPrimeFunctionalBound.ExponentialBound Eg g from hg.zero)
  have sfr := FleetPrimeFunctionalBound.summable_terms hfE (FleetPrimeFunctionalBound.bound_reflect hf.zero)
  have sgr := FleetPrimeFunctionalBound.summable_terms hgE (FleetPrimeFunctionalBound.bound_reflect hg.zero)
  have hP := FleetPrimeFunctionalBound.primeSum_sub sf sg
  have hPr := FleetPrimeFunctionalBound.primeSum_sub sfr sgr
  have href : GammaExplicitFormula.reflect (f-g) =
      (fun u => GammaExplicitFormula.reflect f u-GammaExplicitFormula.reflect g u) := rfl
  unfold FleetFullLineArithmetic.rhs
  rw [hp, hm, hA, href, hPr]
  change _ - GammaExplicitFormula.primeSum (fun u => f u-g u) - _ = _
  rw [hP]
  ring

/-- Joint control of the arithmetic value and weighted real-axis trace difference. -/
theorem exists_difference_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (Ef Eg ε : ℝ) (f g : ℝ → ℂ), 0 ≤ Ef → 0 ≤ Eg → 0 ≤ ε →
      Bound Ef f → Bound Eg g → Bound ε (f-g) →
      ‖FleetFullLineArithmetic.rhs f-FleetFullLineArithmetic.rhs g‖ ≤ C*ε ∧
      ∀ t : ℝ, (1+t^2)*‖h f (t : ℂ)-h g (t : ℂ)‖ ≤ 4*ε/3 := by
  obtain ⟨C, hC, hb⟩ := exists_rhs_bound
  refine ⟨C, hC, ?_⟩
  intro Ef Eg ε f g hfE hgE hε hf hg hd
  constructor
  · rw [← rhs_sub hfE hgE hf hg]
    exact (hb ε (f-g) hε hd).2
  · intro t
    rw [← FleetFullLineLinearity.h_sub_real (integrable_of_Bound hfE hf) (integrable_of_Bound hgE hg)]
    exact FleetExponentialFourierBound.weighted_norm_h_le hε hd.smooth hd.zero hd.first hd.second t

end FleetArithmeticDifference
