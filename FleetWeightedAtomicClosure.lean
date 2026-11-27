import FleetAtomicGluing
import FleetLocalMeasureIdentity
import FleetGlobalRealization

noncomputable section
open Filter Topology MeasureTheory Set TestFunctions

namespace FleetWeightedAtomicClosure

/-- A compact-test limit of uniformly weighted-bounded finite unit spectra is
itself a countable unit spectrum. Neither integer weights nor an atom decomposition
of the limit are assumed. Existence of the limit is still a hypothesis. -/
theorem exists_countable_spectrum
    (c : ℕ → ℕ) (x : ∀ n, Fin (c n) → ℝ)
    (μ : ℕ → Measure ℝ) (ν : Measure ℝ) [IsFiniteMeasureOnCompacts ν]
    (hμ : ∀ n, μ n = ∑ i : Fin (c n), Measure.dirac (x n i))
    {M : ℝ} (hm : ∀ n, (∫ t : ℝ, (1+t^2)⁻¹ ∂μ n) ≤ M)
    (hvague : ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun n => ∫ t, φ t ∂μ n) atTop (𝓝 (∫ t, φ t ∂ν))) :
    ∃ ι : Type, ∃ _ : Countable ι, ∃ γ : ι → ℝ,
      ν = Measure.sum (fun i => Measure.dirac (γ i)) := by
  let U : ℕ → Set ℝ := fun n => Ioo (-(n : ℝ)-1) ((n : ℝ)+1)
  have hcover : ⋃ n, U n = univ := by
    apply eq_univ_of_forall
    intro t
    obtain ⟨n, hn⟩ := exists_nat_gt |t|
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    change -(n : ℝ)-1 < t ∧ t < (n : ℝ)+1
    constructor <;> linarith [le_abs_self t, neg_abs_le t]
  apply FleetAtomicGluing.exists_countable_atomic_decomposition ν U
    (fun _ => measurableSet_Ioo) hcover
  intro n
  obtain ⟨m, _, y, _, he⟩ :=
    FleetLocalMeasureIdentity.exists_local_restricted_counting_measure
      c x μ ν hμ hm hvague ((n : ℝ)+1) (by positivity)
  refine ⟨m, y, Finset.univ.filter (fun i => y i ∈ Ioo (-((n : ℝ)+1)) ((n : ℝ)+1)), ?_⟩
  simpa only [U, neg_add_rev, add_comm, ← sub_eq_add_neg] using he

/-- The finite-spectrum approximation criterion no longer assumes that the
limit is integer-atomic. The uniform bound, actual compact-test limit, and vanishing
arithmetic residual for every admissible test remain explicit obligations. -/
theorem RH_of_finite_arithmetic_approximation
    (c : ℕ → ℕ) (x : ∀ n, Fin (c n) → ℝ)
    (μ : ℕ → Measure ℝ) (ν : Measure ℝ)
    [∀ n, IsFiniteMeasureOnCompacts (μ n)] [IsFiniteMeasureOnCompacts ν]
    (hμ : ∀ n, μ n = ∑ i : Fin (c n), Measure.dirac (x n i))
    (hw : ∀ n, Integrable FleetWeightedTrace.weight (μ n)) {M : ℝ}
    (hm : ∀ n, (∫ t, FleetWeightedTrace.weight t ∂μ n) ≤ M)
    (hvague : ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun n => ∫ t, φ t ∂μ n) atTop (𝓝 (∫ t, φ t ∂ν)))
    (hresidual : ∀ (a : ℝ) (g : ℝ → ℂ), IsTestFn a g →
      (∀ u, a < |u| → g u = 0) →
      Tendsto (fun n => (∫ t, hfun a g (t : ℂ) ∂μ n) -
        GammaExplicitFormula.gammaRHS a g) atTop (𝓝 0)) :
    RiemannHypothesis := by
  obtain ⟨ι, _, γ, hatoms⟩ := exists_countable_spectrum c x μ ν hμ hm hvague
  exact FleetGlobalRealization.RH_of_arithmetic_approximation
    μ ν hw hm hvague hresidual γ hatoms

end FleetWeightedAtomicClosure
