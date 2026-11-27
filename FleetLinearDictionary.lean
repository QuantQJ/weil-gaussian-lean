import FleetApproximationTransfer

noncomputable section
open Filter Topology

namespace FleetLinearDictionary

/-- Residual convergence of primitive probes gives convergence of every fixed
finite complex linear combination, with the same coefficients on arithmetic targets. -/
theorem residual_tendsto_linear_combination {D : Type*}
    (c : ℕ → ℕ) (x : ∀ n, Fin (c n) → ℝ)
    (probe : D → ℝ → ℂ) (target : D → ℂ)
    (s : Finset D) (coefficient : D → ℂ)
    (hd : ∀ d ∈ s, Tendsto (fun n => (∑ i, probe d (x n i))-target d)
      atTop (𝓝 0)) :
    Tendsto (fun n => (∑ i : Fin (c n), ∑ d ∈ s, coefficient d * probe d (x n i)) -
      ∑ d ∈ s, coefficient d * target d) atTop (𝓝 0) := by
  have ht := tendsto_finset_sum s (fun d hd' => (hd d hd').const_mul (coefficient d))
  have heq (n : ℕ) :
      (∑ i : Fin (c n), ∑ d ∈ s, coefficient d * probe d (x n i)) -
        ∑ d ∈ s, coefficient d * target d =
      ∑ d ∈ s, coefficient d * ((∑ i : Fin (c n), probe d (x n i))-target d) := by
    rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    rw [mul_sub, Finset.mul_sum]
  simpa only [← heq, mul_zero, Finset.sum_const_zero] using ht

end FleetLinearDictionary
