import FleetFiniteProbeCertificate
import FleetFiniteIntervalCertificate
import FleetGaussianDictionaryMember

/-!
Weak dual certificates for the actual rational Gaussian bank. A certificate must bound
its real probe combination at every real point, not just at sampled points. The resulting
lower bounds apply to each residual-feasible finite configuration without a mass-cap
assumption. The non-RH consequence is qualitative and uses no dual-completeness claim.
-/

noncomputable section
namespace FleetGaussianDualCertificate
open GaussianTest FleetRationalBankCriterion

/-- The full-line Fourier probe used in the rational Gaussian criterion. -/
def probe (b : ℝ) (q : ℚ) (t : ℝ) : ℂ :=
  FleetFullLineFourier.h (gauss b (q : ℝ)) t

def arithmeticTarget (b : ℝ) (q : ℚ) : ℂ :=
  FleetFullLineArithmetic.rhs (gauss b (q : ℝ))

def weightedMass {N : ℕ} (x : Fin N → ℝ) : ℝ := ∑ i, (1+(x i)^2)⁻¹

/-- The stage's matching conditions, without any assumed weighted-mass budget. -/
def ResidualFeasible (b : ℝ) (n : ℕ) {N : ℕ} (x : Fin N → ℝ) : Prop :=
  ∀ q ∈ FleetRationalBanks.bank n,
    ‖(∑ i, probe b q (x i))-arithmeticTarget b q‖ ≤ 1/((n : ℝ)+1)

/-- Weak duality for an individual residual-feasible configuration. -/
theorem weak_duality_config {b B : ℝ} {n N : ℕ} (x : Fin N → ℝ)
    (coeff : ℚ → ℂ) (hB : 0 ≤ B)
    (hpoint : ∀ t : ℝ, (∑ q ∈ FleetRationalBanks.bank n, coeff q*probe b q t).re ≤ B/(1+t^2))
    (hr : ResidualFeasible b n x) :
    (∑ q ∈ FleetRationalBanks.bank n, coeff q*arithmeticTarget b q).re ≤
      B*weightedMass x + (1/((n : ℝ)+1))*(∑ q ∈ FleetRationalBanks.bank n, ‖coeff q‖) := by
  apply FleetFiniteProbeCertificate.necessary_inequality (FleetRationalBanks.bank n) x
    (probe b) (arithmeticTarget b) coeff hB (le_refl (weightedMass x)) hpoint
  intro q hq
  rw [norm_sub_rev]
  exact hr q hq

/-- Any feasible mass budget dominates every certified dual objective after residual error. -/
theorem weak_duality {b M B : ℝ} {n : ℕ} (coeff : ℚ → ℂ) (hB : 0 ≤ B)
    (hpoint : ∀ t : ℝ, (∑ q ∈ FleetRationalBanks.bank n, coeff q*probe b q t).re ≤ B/(1+t^2))
    (hf : Feasible b M n) :
    (∑ q ∈ FleetRationalBanks.bank n, coeff q*arithmeticTarget b q).re ≤
      B*M + (1/((n : ℝ)+1))*(∑ q ∈ FleetRationalBanks.bank n, ‖coeff q‖) := by
  obtain ⟨N,x,hm,hr⟩ := hf
  exact (weak_duality_config x coeff hB hpoint hr).trans
    (add_le_add_left (mul_le_mul_of_nonneg_left hm hB) _)

/-- A positive pointwise normalization gives a mass lower bound without a mass-cap premise. -/
theorem mass_lower_bound {b B : ℝ} {n N : ℕ} (x : Fin N → ℝ)
    (coeff : ℚ → ℂ) (hB : 0 < B)
    (hpoint : ∀ t : ℝ, (∑ q ∈ FleetRationalBanks.bank n, coeff q*probe b q t).re ≤ B/(1+t^2))
    (hr : ResidualFeasible b n x) :
    ((∑ q ∈ FleetRationalBanks.bank n, coeff q*arithmeticTarget b q).re -
      (1/((n : ℝ)+1))*(∑ q ∈ FleetRationalBanks.bank n, ‖coeff q‖))/B ≤ weightedMass x := by
  apply (div_le_iff₀ hB).mpr
  have hh := weak_duality_config x coeff hB.le hpoint hr
  nlinarith

/-- Uniform arithmetic uncertainty adds `eta * ∑ ‖coeff q‖` to the residual allowance. -/
theorem weak_duality_approximate_config {b B eta : ℝ} {n N : ℕ}
    (x : Fin N → ℝ) (approximate coeff : ℚ → ℂ) (hB : 0 ≤ B)
    (happrox : ∀ q ∈ FleetRationalBanks.bank n, ‖approximate q-arithmeticTarget b q‖ ≤ eta)
    (hpoint : ∀ t : ℝ, (∑ q ∈ FleetRationalBanks.bank n, coeff q*probe b q t).re ≤ B/(1+t^2))
    (hr : ResidualFeasible b n x) :
    (∑ q ∈ FleetRationalBanks.bank n, coeff q*approximate q).re ≤
      B*weightedMass x + (eta+1/((n : ℝ)+1))*(∑ q ∈ FleetRationalBanks.bank n, ‖coeff q‖) := by
  apply FleetFiniteProbeCertificate.necessary_inequality (FleetRationalBanks.bank n) x
    (probe b) approximate coeff hB (le_refl (weightedMass x)) hpoint
  intro q hq
  calc
    ‖approximate q-∑ i, probe b q (x i)‖ ≤
      ‖approximate q-arithmeticTarget b q‖+
        ‖arithmeticTarget b q-∑ i, probe b q (x i)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ eta+1/((n : ℝ)+1) := by
      apply add_le_add (happrox q hq)
      rw [norm_sub_rev]
      exact hr q hq

theorem weak_duality_approximate {b M B eta : ℝ} {n : ℕ}
    (approximate coeff : ℚ → ℂ) (hB : 0 ≤ B)
    (happrox : ∀ q ∈ FleetRationalBanks.bank n, ‖approximate q-arithmeticTarget b q‖ ≤ eta)
    (hpoint : ∀ t : ℝ, (∑ q ∈ FleetRationalBanks.bank n, coeff q*probe b q t).re ≤ B/(1+t^2))
    (hf : Feasible b M n) :
    (∑ q ∈ FleetRationalBanks.bank n, coeff q*approximate q).re ≤
      B*M + (eta+1/((n : ℝ)+1))*(∑ q ∈ FleetRationalBanks.bank n, ‖coeff q‖) := by
  obtain ⟨N,x,hm,hr⟩ := hf
  exact (weak_duality_approximate_config x approximate coeff hB happrox hpoint hr).trans
    (add_le_add_left (mul_le_mul_of_nonneg_left hm hB) _)

theorem mass_lower_bound_approximate {b B eta : ℝ} {n N : ℕ}
    (x : Fin N → ℝ) (approximate coeff : ℚ → ℂ) (hB : 0 < B)
    (happrox : ∀ q ∈ FleetRationalBanks.bank n, ‖approximate q-arithmeticTarget b q‖ ≤ eta)
    (hpoint : ∀ t : ℝ, (∑ q ∈ FleetRationalBanks.bank n, coeff q*probe b q t).re ≤ B/(1+t^2))
    (hr : ResidualFeasible b n x) :
    ((∑ q ∈ FleetRationalBanks.bank n, coeff q*approximate q).re -
      (eta+1/((n : ℝ)+1))*(∑ q ∈ FleetRationalBanks.bank n, ‖coeff q‖))/B ≤ weightedMass x := by
  apply (div_le_iff₀ hB).mpr
  have hh := weak_duality_approximate_config x approximate coeff hB.le happrox hpoint hr
  nlinarith

/-- Under non-RH, every fixed mass budget eventually fails at every subsequent bank stage.
This provides no quantitative bound on the first failing stage. -/
theorem exists_eventually_infeasible_of_not_RH {b : ℝ} (hb : 0 < b)
    (hnot : ¬ RiemannHypothesis) (M : ℝ) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ¬ Feasible b M n := by
  classical
  have hnotall : ¬ ∀ n : ℕ, Feasible b M n := fun hf =>
    hnot (RH_of_feasible_stages hb hf)
  obtain ⟨n0,hn0⟩ := not_forall.mp hnotall
  exact ⟨n0, fun n hn hf => hn0 (FleetFiniteIntervalCertificate.feasible_mono_stage hn hf)⟩

/-- Configuration form of eventual infeasibility. This neither assumes existence of a
residual-feasible configuration nor assumes that a mass infimum is attained. -/
theorem eventually_mass_gt_of_not_RH {b : ℝ} (hb : 0 < b)
    (hnot : ¬ RiemannHypothesis) (M : ℝ) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ N : ℕ, ∀ x : Fin N → ℝ,
      ResidualFeasible b n x → M < weightedMass x := by
  obtain ⟨n0,hn0⟩ := exists_eventually_infeasible_of_not_RH hb hnot M
  refine ⟨n0,?_⟩
  intro n hn N x hr
  by_contra h
  exact hn0 n hn ⟨N,x,le_of_not_gt h,hr⟩

end FleetGaussianDualCertificate
