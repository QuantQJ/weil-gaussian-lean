import FleetWeightedAtomicClosure

noncomputable section
open Filter Topology MeasureTheory TestFunctions

namespace FleetFiniteApproximation

/-- A criterion stated directly in terms of finite real coordinate lists.
The weighted bound, a compact-test limit, and all-test arithmetic residuals
are the remaining hypotheses; no spectrum or atom decomposition is supplied. -/
theorem RH_of_finite_trace_approximation
    (c : ℕ → ℕ) (x : ∀ n, Fin (c n) → ℝ)
    (ν : Measure ℝ) [IsFiniteMeasureOnCompacts ν]
    {M : ℝ} (hm : ∀ n, (∑ i : Fin (c n), (1+(x n i)^2)⁻¹) ≤ M)
    (hvague : ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun n => ∑ i : Fin (c n), φ (x n i)) atTop (𝓝 (∫ t, φ t ∂ν)))
    (hresidual : ∀ (a : ℝ) (g : ℝ → ℂ), IsTestFn a g →
      (∀ u, a < |u| → g u = 0) →
      Tendsto (fun n => (∑ i : Fin (c n), hfun a g (x n i : ℂ)) -
        GammaExplicitFormula.gammaRHS a g) atTop (𝓝 0)) :
    RiemannHypothesis := by
  let μ : ℕ → Measure ℝ := fun n => ∑ i : Fin (c n), Measure.dirac (x n i)
  letI : ∀ n, IsFiniteMeasureOnCompacts (μ n) := fun n => by
    dsimp [μ]
    infer_instance
  have hw : ∀ n, Integrable FleetWeightedTrace.weight (μ n) := by
    intro n
    apply integrable_finset_sum_measure.mpr
    intro i _
    exact (integrable_const (FleetWeightedTrace.weight (x n i))).congr
      (ae_eq_dirac FleetWeightedTrace.weight).symm
  have hm' : ∀ n, (∫ t, FleetWeightedTrace.weight t ∂μ n) ≤ M := by
    intro n
    simpa only [μ, FleetWeightedTrace.weight, FleetLocalAtomicLimit.integral_real_unit_atoms]
      using hm n
  have hv : ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun n => ∫ t, φ t ∂μ n) atTop (𝓝 (∫ t, φ t ∂ν)) := by
    intro φ hc hs
    simpa only [μ, FleetAtomicLimit.integral_unit_atoms] using hvague φ hc hs
  have hr : ∀ (a : ℝ) (g : ℝ → ℂ), IsTestFn a g →
      (∀ u, a < |u| → g u = 0) →
      Tendsto (fun n => (∫ t, hfun a g (t : ℂ) ∂μ n) -
        GammaExplicitFormula.gammaRHS a g) atTop (𝓝 0) := by
    intro a g hg hs
    simpa only [μ, FleetAtomicLimit.integral_unit_atoms] using hresidual a g hg hs
  exact FleetWeightedAtomicClosure.RH_of_finite_arithmetic_approximation
    c x μ ν (fun _ => rfl) hw hm' hv hr

end FleetFiniteApproximation
