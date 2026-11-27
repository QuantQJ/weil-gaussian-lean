import FleetFiniteGaussianFeasibility
import FleetRationalBanks

noncomputable section
namespace FleetRationalBankCriterion
open GaussianTest

/-- The concrete stage-n problem uses fractions p/q with |p|≤n and 1≤q≤n,
residual tolerance 1/(n+1), and one externally fixed weighted-mass bound. -/
def Feasible (b M : ℝ) (n : ℕ) : Prop :=
  ∃ N : ℕ, ∃ x : Fin N → ℝ,
    (∑ i, (1+(x i)^2)⁻¹) ≤ M ∧
    ∀ q ∈ FleetRationalBanks.bank n,
      ‖(∑ i : Fin N, FleetFullLineFourier.h (gauss b (q : ℝ)) (x i))-
        FleetFullLineArithmetic.rhs (gauss b (q : ℝ))‖ ≤ 1/((n : ℝ)+1)

/-- Feasibility of every concrete stage with the same bound implies RH. -/
theorem RH_of_feasible_stages {b M : ℝ} (hb : 0 < b)
    (hf : ∀ n : ℕ, Feasible b M n) : RiemannHypothesis := by
  exact FleetFiniteGaussianFeasibility.RH_of_finite_bank_feasibility hb
    FleetRationalBanks.bank (fun n => 1/((n : ℝ)+1))
    FleetRationalBanks.eventually_mem_bank tendsto_one_div_add_atTop_nhds_zero_nat hf

/-- An existence property, not an asserted construction or finite stopping rule. -/
def UniformFeasibility (b : ℝ) : Prop := ∃ M : ℝ, ∀ n : ℕ, Feasible b M n

theorem RH_of_uniform_feasibility {b : ℝ} (hb : 0 < b)
    (hf : UniformFeasibility b) : RiemannHypothesis := by
  obtain ⟨M, hm⟩ := hf
  exact RH_of_feasible_stages hb hm

end FleetRationalBankCriterion
