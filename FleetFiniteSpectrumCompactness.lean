import FleetEncodedAtoms
import FleetSlotLimit
import FleetFiniteApproximation

noncomputable section
open Filter Topology Set MeasureTheory TestFunctions

namespace FleetFiniteSpectrumCompactness

/-- Uniform inverse-quadratic bounds on finite unit spectra give a subsequence
converging against every compact continuous test to a locally finite measure.
The limit is constructed, not supplied as a hypothesis. -/
theorem exists_vague_subsequence
    (c : ℕ → ℕ) (x : ∀ n, Fin (c n) → ℝ) {M : ℝ}
    (hm : ∀ n, (∑ i : Fin (c n), (1+(x n i)^2)⁻¹) ≤ M) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ ν : Measure ℝ,
      IsFiniteMeasureOnCompacts ν ∧
      ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ →
        Tendsto (fun n => ∑ i : Fin (c (s n)), φ (x (s n) i)) atTop
          (𝓝 (∫ t, φ t ∂ν)) := by
  classical
  choose e he using (fun n => FleetOrderedAtoms.exists_ordered_permutation (x n))
  let z : ℕ → ℕ → ℝ := fun n => FleetEncodedAtoms.encode (x n) (e n)
  have hz : ∀ n k, z n k ∈ Icc (-1 : ℝ) 1 :=
    fun n k => FleetEncodedAtoms.encode_mem (x n) (e n) k
  obtain ⟨a, _, s, hs, hconv⟩ := FleetCompactSlots.exists_slot_subsequence z hz
  have hprefix : ∀ R : ℝ, 0 ≤ R → ∃ N : ℕ,
      ∀ n k, N ≤ k → R/(1+R) ≤ |z (s n) k| := by
    intro R hR
    refine ⟨⌈M*(1+R^2)⌉₊, ?_⟩
    intro n k hk
    exact FleetEncodedAtoms.encode_prefix (x (s n)) (e (s n)) (he (s n)) hR (hm (s n)) k hk
  have hpad : ∀ n k, c (s n) ≤ k → z (s n) k = 1 :=
    fun n k hk => FleetEncodedAtoms.encode_pad (x (s n)) (e (s n)) k hk
  let ν := FleetSlotLimit.limitMeasure a
  letI : IsLocallyFiniteMeasure ν := FleetSlotLimit.limit_locallyFinite hconv hprefix
  refine ⟨s, hs, ν, inferInstance, ?_⟩
  intro φ hφ hcomp
  have ht := FleetSlotLimit.compact_trace_tendsto hconv (fun n => c (s n))
    hpad hprefix hφ hcomp
  simpa only [z, FleetEncodedAtoms.trace_encode] using ht

/-- The remaining construction obligations: finite real lists with one uniform
weighted bound and vanishing arithmetic residuals for every admissible test imply RH.
No limit measure, convergence subsequence, or atom decomposition is assumed. -/
theorem RH_of_uniform_finite_approximation
    (c : ℕ → ℕ) (x : ∀ n, Fin (c n) → ℝ) {M : ℝ}
    (hm : ∀ n, (∑ i : Fin (c n), (1+(x n i)^2)⁻¹) ≤ M)
    (hresidual : ∀ (a : ℝ) (g : ℝ → ℂ), IsTestFn a g →
      (∀ u, a < |u| → g u = 0) →
      Tendsto (fun n => (∑ i : Fin (c n), hfun a g (x n i : ℂ)) -
        GammaExplicitFormula.gammaRHS a g) atTop (𝓝 0)) :
    RiemannHypothesis := by
  obtain ⟨s, hs, ν, hν, hvague⟩ := exists_vague_subsequence c x hm
  letI := hν
  apply FleetFiniteApproximation.RH_of_finite_trace_approximation
    (fun n => c (s n)) (fun n => x (s n)) ν (fun n => hm (s n)) hvague
  intro a g hg hsupp
  exact (hresidual a g hg hsupp).comp hs.tendsto_atTop

end FleetFiniteSpectrumCompactness
