import FleetWeightedTrace
import FleetFourierLittleO
import GammaExplicitFormula

noncomputable section
open Filter Topology MeasureTheory TestFunctions Complex

namespace FleetSpectralTraceLimit

theorem continuous_hfun_real {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) :
    Continuous (fun t : ℝ => hfun a g (t : ℂ)) := by
  have he : (fun t : ℝ => hfun a g (t : ℂ)) =
      (fun t : ℝ => Gt a g (1 / 2 + I * (t : ℂ))) := by
    funext t
    exact (Gt_half_add_I_mul a g (t : ℂ)).symm
  rw [he]
  exact (Gt_continuous h.continuous).comp (by fun_prop)

/-- The explicit-formula test transforms pass through a vaguely convergent,
uniformly weighted-bounded family of spectral measures. -/
theorem hfun_integral_tendsto
    (μ : ℕ → Measure ℝ) (ν : Measure ℝ)
    [∀ n, IsFiniteMeasureOnCompacts (μ n)] [IsFiniteMeasureOnCompacts ν]
    (hw : ∀ n, Integrable FleetWeightedTrace.weight (μ n)) {M : ℝ}
    (hm : ∀ n, (∫ t, FleetWeightedTrace.weight t ∂μ n) ≤ M)
    (hvague : ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun n => ∫ t, φ t ∂μ n) atTop (𝓝 (∫ t, φ t ∂ν)))
    {a : ℝ} {g : ℝ → ℂ} (hg : IsTestFn a g) :
    Tendsto (fun n => ∫ t, hfun a g (t : ℂ) ∂μ n) atTop
      (𝓝 (∫ t, hfun a g (t : ℂ) ∂ν)) :=
  FleetWeightedTrace.integral_tendsto_of_compact_tests_of_uniform_weight
    μ ν hw hm hvague (continuous_hfun_real hg)
    (FleetFourierLittleO.weighted_norm_hfun_tendsto_zero hg)

/-- A vanishing arithmetic residual identifies the limit trace. Existence of a
family satisfying the uniform bound and residual hypothesis is not asserted. -/
theorem integral_eq_gammaRHS_of_residual_tendsto_zero
    (μ : ℕ → Measure ℝ) (ν : Measure ℝ)
    [∀ n, IsFiniteMeasureOnCompacts (μ n)] [IsFiniteMeasureOnCompacts ν]
    (hw : ∀ n, Integrable FleetWeightedTrace.weight (μ n)) {M : ℝ}
    (hm : ∀ n, (∫ t, FleetWeightedTrace.weight t ∂μ n) ≤ M)
    (hvague : ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun n => ∫ t, φ t ∂μ n) atTop (𝓝 (∫ t, φ t ∂ν)))
    {a : ℝ} {g : ℝ → ℂ} (hg : IsTestFn a g)
    (hresidual : Tendsto (fun n => (∫ t, hfun a g (t : ℂ) ∂μ n) -
      GammaExplicitFormula.gammaRHS a g) atTop (𝓝 0)) :
    (∫ t, hfun a g (t : ℂ) ∂ν) = GammaExplicitFormula.gammaRHS a g := by
  have ht := (hfun_integral_tendsto μ ν hw hm hvague hg).sub_const
    (GammaExplicitFormula.gammaRHS a g)
  exact sub_eq_zero.mp (tendsto_nhds_unique ht hresidual)

end FleetSpectralTraceLimit
