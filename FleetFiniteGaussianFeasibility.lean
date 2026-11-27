import FleetGaussianCriterion

noncomputable section
open Filter Topology
namespace FleetFiniteGaussianFeasibility
open GaussianTest

/-- Finite feasibility at every stage, with one uniform mass bound and errors tending
to zero, supplies a common family satisfying every fixed rational Gaussian probe.
The finite feasibility hypotheses are not asserted to hold. -/
theorem RH_of_finite_bank_feasibility {b M : ℝ} (hb : 0 < b)
    (bank : ℕ → Finset ℚ) (error : ℕ → ℝ)
    (hcover : ∀ q : ℚ, ∀ᶠ n in atTop, q ∈ bank n)
    (herror : Tendsto error atTop (𝓝 0))
    (hfeasible : ∀ n : ℕ, ∃ N : ℕ, ∃ x : Fin N → ℝ,
      (∑ i, (1+(x i)^2)⁻¹) ≤ M ∧
      ∀ q ∈ bank n,
        ‖(∑ i : Fin N, FleetFullLineFourier.h (gauss b (q : ℝ)) (x i))-
          FleetFullLineArithmetic.rhs (gauss b (q : ℝ))‖ ≤ error n) :
    RiemannHypothesis := by
  choose c x hm hr using hfeasible
  apply FleetGaussianCriterion.RH_of_rational_gaussian_residuals hb c x hm
  intro q
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := (Metric.tendsto_nhds.mp herror) ε hε
  filter_upwards [hcover q, he] with n hq hn
  rw [dist_zero_right]
  have hn' : error n < ε := by
    rw [Real.dist_eq, sub_zero] at hn
    exact (le_abs_self _).trans_lt hn
  exact (hr n q hq).trans_lt hn'

/-- A monotone finite rational bank can exhaust every rational center. -/
theorem exists_exhausting_bank : ∃ bank : ℕ → Finset ℚ,
    Monotone bank ∧ ∀ q : ℚ, ∀ᶠ n in atTop, q ∈ bank n := by
  obtain ⟨bank, hm, ht⟩ := exists_seq_monotone_tendsto_atTop_atTop (Finset ℚ)
  refine ⟨bank, hm, ?_⟩
  intro q
  have he := ht (eventually_ge_atTop ({q} : Finset ℚ))
  filter_upwards [he] with n hn
  exact hn (Finset.mem_singleton_self q)

end FleetFiniteGaussianFeasibility
