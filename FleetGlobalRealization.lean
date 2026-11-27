import FleetSpectralTraceLimit
import FleetStandardExplicitFormula

noncomputable section
open Filter Topology MeasureTheory TestFunctions

namespace FleetGlobalRealization

/-- A supplied decomposition into unit real atoms turns an integrable trace
into the corresponding unordered spectral sum. Multiplicities are retained. -/
theorem hasSum_of_unit_atoms {ι : Type*} (γ : ι → ℝ) (ν : Measure ℝ)
    (hatoms : ν = Measure.sum (fun i => Measure.dirac (γ i)))
    {f : ℝ → ℂ} (hf : Integrable f ν) :
    HasSum (fun i => f (γ i)) (∫ t, f t ∂ν) := by
  rw [hatoms] at hf ⊢
  simpa only [integral_dirac] using hasSum_integral_measure hf

/-- The construction obligations imply RH. In particular, the unit-atom
representation and the all-test arithmetic residual are explicit hypotheses;
neither is inferred from a finite numerical fit. -/
theorem RH_of_arithmetic_approximation
    (μ : ℕ → Measure ℝ) (ν : Measure ℝ)
    [∀ n, IsFiniteMeasureOnCompacts (μ n)] [IsFiniteMeasureOnCompacts ν]
    (hw : ∀ n, Integrable FleetWeightedTrace.weight (μ n)) {M : ℝ}
    (hm : ∀ n, (∫ t, FleetWeightedTrace.weight t ∂μ n) ≤ M)
    (hvague : ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun n => ∫ t, φ t ∂μ n) atTop (𝓝 (∫ t, φ t ∂ν)))
    (hresidual : ∀ (a : ℝ) (g : ℝ → ℂ), IsTestFn a g →
      (∀ u, a < |u| → g u = 0) →
      Tendsto (fun n => (∫ t, hfun a g (t : ℂ) ∂μ n) -
        GammaExplicitFormula.gammaRHS a g) atTop (𝓝 0))
    {ι : Type} (γ : ι → ℝ)
    (hatoms : ν = Measure.sum (fun i => Measure.dirac (γ i))) :
    RiemannHypothesis := by
  have hwν := (FleetWeightedTrace.weight_integrable_and_bound_of_compact_tests
    μ ν hw hm hvague).1
  have hs : Summable (fun i => 1 / (1 + (γ i)^2)) := by
    rw [hatoms] at hwν
    have hh := hasSum_integral_measure hwν
    simpa only [integral_dirac, FleetWeightedTrace.weight, one_div] using hh.summable
  apply GammaExplicitFormula.RH_iff_exists_gamma_spectrum.mpr
  refine ⟨ι, γ, hs, ?_⟩
  intro a g hg hsupp
  have hi : Integrable (fun t : ℝ => hfun a g (t : ℂ)) ν :=
    FleetWeightedTrace.integrable_of_weighted_vanishing
      (FleetSpectralTraceLimit.continuous_hfun_real hg)
      (FleetFourierLittleO.weighted_norm_hfun_tendsto_zero hg) ν hwν
  have he := FleetSpectralTraceLimit.integral_eq_gammaRHS_of_residual_tendsto_zero
    μ ν hw hm hvague hg (hresidual a g hg hsupp)
  rw [← he]
  exact hasSum_of_unit_atoms γ ν hatoms hi

end FleetGlobalRealization
