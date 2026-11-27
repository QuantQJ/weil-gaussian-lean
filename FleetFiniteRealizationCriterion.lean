import FleetFiniteSpectrumCompactness
import FleetFiniteTruncation

noncomputable section
open Filter Topology MeasureTheory TestFunctions

namespace FleetFiniteRealizationCriterion

/-- A summable strictly positive weight forces its full atom index to be countable. -/
theorem countable_of_tempered {ι : Type*} (γ : ι → ℝ)
    (hs : Summable (fun i => (1+(γ i)^2)⁻¹)) : Countable ι := by
  have hsupport : Function.support (fun i => (1+(γ i)^2)⁻¹) = Set.univ := by
    ext i
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact inv_ne_zero (by positivity)
  have hc := hs.countable_support
  rw [hsupport] at hc
  exact Set.countable_univ_iff.mp hc

/-- One finite real approximation family works simultaneously for every admissible
test and has one uniform weighted bound. This is an existence property, not a solver. -/
def FiniteArithmeticApproximation : Prop :=
  ∃ c : ℕ → ℕ, ∃ x : ∀ n, Fin (c n) → ℝ, ∃ M : ℝ,
    (∀ n, (∑ i : Fin (c n), (1+(x n i)^2)⁻¹) ≤ M) ∧
    (∀ (a : ℝ) (g : ℝ → ℂ), IsTestFn a g → (∀ u, a < |u| → g u = 0) →
      Tendsto (fun n => (∑ i : Fin (c n), hfun a g (x n i : ℂ)) -
        GammaExplicitFormula.gammaRHS a g) atTop (𝓝 0))

/-- Compactness proves the forward implication; truncation of a realizing
spectrum proves the reverse. The finite existence property remains equivalent to RH. -/
theorem RH_iff_finite_arithmetic_approximation :
    RiemannHypothesis ↔ FiniteArithmeticApproximation := by
  constructor
  · intro hRH
    obtain ⟨ι, γ, hs, hr⟩ := GammaExplicitFormula.RH_iff_exists_gamma_spectrum.mp hRH
    have hs' : Summable (fun i => (1+(γ i)^2)⁻¹) := by simpa only [one_div] using hs
    letI := countable_of_tempered γ hs'
    obtain ⟨c, x, hm, ht⟩ := FleetFiniteTruncation.exists_inverse_quadratic_truncations γ hs'
    refine ⟨c, x, ∑' i, (1+(γ i)^2)⁻¹, hm, ?_⟩
    intro a g hg hsupp
    have htrace := ht (fun t : ℝ => hfun a g (t : ℂ))
      (GammaExplicitFormula.gammaRHS a g) (hr a g hg hsupp)
    simpa only [sub_self] using htrace.sub_const (GammaExplicitFormula.gammaRHS a g)
  · rintro ⟨c, x, M, hm, hr⟩
    exact FleetFiniteSpectrumCompactness.RH_of_uniform_finite_approximation c x hm hr

end FleetFiniteRealizationCriterion
