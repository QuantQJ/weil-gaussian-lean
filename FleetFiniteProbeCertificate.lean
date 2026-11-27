import FleetApproximationTransfer

noncomputable section
open Complex
namespace FleetFiniteProbeCertificate

/-- A continuum upper bound on one linear combination of probes gives a necessary
finite-bank feasibility inequality. Pointwise validity is required on ALL real coordinates. -/
theorem necessary_inequality {D : Type*} (s : Finset D) {N : ℕ} (x : Fin N → ℝ)
    (probe : D → ℝ → ℂ) (target coeff : D → ℂ) {M B ε : ℝ}
    (hB : 0 ≤ B)
    (hm : (∑ i, (1+(x i)^2)⁻¹) ≤ M)
    (hpoint : ∀ t : ℝ, (∑ d ∈ s, coeff d*probe d t).re ≤ B/(1+t^2))
    (hr : ∀ d ∈ s, ‖target d-∑ i, probe d (x i)‖ ≤ ε) :
    (∑ d ∈ s, coeff d*target d).re ≤ B*M + ε*(∑ d ∈ s, ‖coeff d‖) := by
  let trace : ℂ := ∑ d ∈ s, coeff d*(∑ i, probe d (x i))
  have heq : trace = ∑ i, ∑ d ∈ s, coeff d*probe d (x i) := by
    dsimp [trace]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  have ht : trace.re ≤ B*M := by
    rw [heq, Complex.re_sum]
    calc
      _ ≤ ∑ i, B/(1+(x i)^2) := Finset.sum_le_sum (fun i _ => hpoint (x i))
      _ = B*∑ i, (1+(x i)^2)⁻¹ := by simp only [div_eq_mul_inv, Finset.mul_sum]
      _ ≤ B*M := mul_le_mul_of_nonneg_left hm hB
  have herr : ‖(∑ d ∈ s, coeff d*target d)-trace‖ ≤ ε*(∑ d ∈ s, ‖coeff d‖) := by
    change ‖(∑ d ∈ s, coeff d*target d)-(∑ d ∈ s, coeff d*(∑ i, probe d (x i)))‖ ≤ _
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub]
    calc
      _ ≤ ∑ d ∈ s, ‖coeff d*(target d-∑ i, probe d (x i))‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ s, ‖coeff d‖*ε := by
        apply Finset.sum_le_sum
        intro d hd
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hr d hd) (norm_nonneg _)
      _ = ε*(∑ d ∈ s, ‖coeff d‖) := by rw [← Finset.sum_mul]; ring
  have hre := Complex.re_le_norm ((∑ d ∈ s, coeff d*target d)-trace)
  change ((∑ d ∈ s, coeff d*target d)-trace).re ≤ ‖(∑ d ∈ s, coeff d*target d)-trace‖ at hre
  rw [sub_re] at hre
  linarith

/-- A strict violation certifies infeasibility of these simultaneous constraints.
This does not infer a wider RH verdict from a failed finite or mass-constrained instance. -/
theorem infeasible_of_certificate {D : Type*} (s : Finset D)
    (probe : D → ℝ → ℂ) (target coeff : D → ℂ) {M B ε : ℝ}
    (hB : 0 ≤ B)
    (hpoint : ∀ t : ℝ, (∑ d ∈ s, coeff d*probe d t).re ≤ B/(1+t^2))
    (hgap : B*M + ε*(∑ d ∈ s, ‖coeff d‖) < (∑ d ∈ s, coeff d*target d).re) :
    ¬ ∃ (N : ℕ) (x : Fin N → ℝ), (∑ i, (1+(x i)^2)⁻¹) ≤ M ∧
      ∀ d ∈ s, ‖target d-∑ i, probe d (x i)‖ ≤ ε := by
  rintro ⟨N,x,hm,hr⟩
  exact (not_lt_of_ge (necessary_inequality s x probe target coeff hB hm hpoint hr)) hgap

/-- Arithmetic enclosure uncertainty must be charged to the separation margin. -/
theorem infeasible_of_approximate_certificate {D : Type*} (s : Finset D)
    (probe : D → ℝ → ℂ) (target approximate coeff : D → ℂ) {M B ε η : ℝ}
    (hB : 0 ≤ B)
    (ha : ∀ d ∈ s, ‖approximate d-target d‖ ≤ η)
    (hpoint : ∀ t : ℝ, (∑ d ∈ s, coeff d*probe d t).re ≤ B/(1+t^2))
    (hgap : B*M + (η+ε)*(∑ d ∈ s, ‖coeff d‖) < (∑ d ∈ s, coeff d*approximate d).re) :
    ¬ ∃ (N : ℕ) (x : Fin N → ℝ), (∑ i, (1+(x i)^2)⁻¹) ≤ M ∧
      ∀ d ∈ s, ‖target d-∑ i, probe d (x i)‖ ≤ ε := by
  rintro ⟨N,x,hm,hr⟩
  apply infeasible_of_certificate s probe approximate coeff hB hpoint hgap
  refine ⟨N,x,hm,?_⟩
  intro d hd
  calc
    ‖approximate d-∑ i, probe d (x i)‖ ≤ ‖approximate d-target d‖+‖target d-∑ i, probe d (x i)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ η+ε := add_le_add (ha d hd) (hr d hd)

end FleetFiniteProbeCertificate
