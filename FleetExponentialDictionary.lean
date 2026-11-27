import FleetArithmeticDifference
import FleetCompactExponentialBound
import FleetApproximationTransfer

noncomputable section
open Filter Topology FleetArithmeticContinuity
namespace FleetExponentialDictionary

/-- Exponential C² density supplies both approximation obligations in the
explicit-formula dictionary interface. This theorem does not assert Gaussian density. -/
theorem joint_approximation {D : Type*} (dictionary : D → ℝ → ℂ)
    (hd : ∀ d, ∃ E : ℝ, 0 ≤ E ∧ Bound E (dictionary d))
    (ha : ∀ (a : ℝ) (g : ℝ → ℂ), TestFunctions.IsTestFn a g →
      (∀ u, a < |u| → g u = 0) → ∀ ε : ℝ, 0 < ε →
      ∃ d, Bound ε (g-dictionary d))
    (a : ℝ) (g : ℝ → ℂ) (hg : TestFunctions.IsTestFn a g)
    (hs : ∀ u, a < |u| → g u = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ d, (∀ t : ℝ, ‖TestFunctions.hfun a g t-FleetFullLineFourier.h (dictionary d) t‖ ≤ ε/(1+t^2)) ∧
      ‖GammaExplicitFormula.gammaRHS a g-FleetFullLineArithmetic.rhs (dictionary d)‖ ≤ ε := by
  obtain ⟨C, hC, hb⟩ := FleetArithmeticDifference.exists_difference_bound
  let δ := ε/(C+2)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have he : δ*(C+2) = ε := div_mul_cancel₀ _ (by positivity)
  obtain ⟨d, hgd⟩ := ha a g hg hs δ hδ
  obtain ⟨Eg, hEg, h0, h1, h2⟩ := FleetCompactExponentialBound.testFn_exists_common_envelope hg hs
  obtain ⟨Ed, hEd, hD⟩ := hd d
  obtain ⟨hr, ht⟩ := hb Eg Ed δ g (dictionary d) hEg hEd hδ.le ⟨hg.smooth, h0, h1, h2⟩ hD hgd
  refine ⟨d, ?_, ?_⟩
  · intro t
    rw [← FleetFullLineFourier.h_eq_hfun hg hs]
    apply (le_div_iff₀ (by positivity : (0:ℝ)<1+t^2)).mpr
    have hh := ht t
    nlinarith
  · rw [← FleetFullLineArithmetic.rhs_eq_gammaRHS hg hs]
    nlinarith

/-- An arithmetic family with convergent residuals on an exponentially C²-dense
bank realizes all compact tests. The existence of that family is still a hypothesis. -/
theorem RH_of_exponential_dictionary {D : Type*}
    (c : ℕ → ℕ) (x : ∀ n, Fin (c n) → ℝ) {M : ℝ}
    (hm : ∀ n, (∑ i, (1+(x n i)^2)⁻¹) ≤ M)
    (dictionary : D → ℝ → ℂ)
    (hd : ∀ d, ∃ E : ℝ, 0 ≤ E ∧ Bound E (dictionary d))
    (ha : ∀ (a : ℝ) (g : ℝ → ℂ), TestFunctions.IsTestFn a g →
      (∀ u, a < |u| → g u = 0) → ∀ ε : ℝ, 0 < ε →
      ∃ d, Bound ε (g-dictionary d))
    (hr : ∀ d, Tendsto (fun n => (∑ i, FleetFullLineFourier.h (dictionary d) (x n i))-
      FleetFullLineArithmetic.rhs (dictionary d)) atTop (𝓝 0)) : RiemannHypothesis := by
  apply FleetApproximationTransfer.RH_of_dictionary_approximation c x hm
    (fun d t => FleetFullLineFourier.h (dictionary d) t) (fun d => FleetFullLineArithmetic.rhs (dictionary d)) hr
  exact joint_approximation dictionary hd ha

end FleetExponentialDictionary
