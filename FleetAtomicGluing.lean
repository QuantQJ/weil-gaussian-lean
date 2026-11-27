import Mathlib

noncomputable section
open Set MeasureTheory
namespace FleetAtomicGluing
attribute [local instance] Classical.propDecidable

lemma restrict_finite_atoms {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (U : Set ℝ) :
    (∑ i ∈ s, Measure.dirac (γ i)).restrict U =
      ∑ i ∈ s.filter (fun i => γ i ∈ U), Measure.dirac (γ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    by_cases h : γ a ∈ U
    · simp [Finset.filter_insert, Finset.sum_insert, ha, Measure.restrict_add, restrict_dirac, h, ih]
    · simp [Finset.filter_insert, Finset.sum_insert, ha, Measure.restrict_add, restrict_dirac, h, ih]

/-- A countable measurable cover whose restrictions are finite sums of unit
atoms gives a countably indexed global sum of unit atoms. Multiplicity is retained;
no infinitude of the index type or enumeration by all natural numbers is asserted. -/
theorem exists_countable_atomic_decomposition (ν : Measure ℝ) (U : ℕ → Set ℝ)
    (hU : ∀ n, MeasurableSet (U n)) (hcover : ⋃ n, U n = univ)
    (hloc : ∀ n, ∃ N : ℕ, ∃ γ : Fin N → ℝ, ∃ s : Finset (Fin N),
      ν.restrict (U n) = ∑ i ∈ s, Measure.dirac (γ i)) :
    ∃ ι : Type, ∃ _ : Countable ι, ∃ γ : ι → ℝ,
      ν = Measure.sum (fun i => Measure.dirac (γ i)) := by
  classical
  choose N γ s hs using hloc
  let t : (n : ℕ) → Finset (Fin (N n)) := fun n =>
    (s n).filter (fun i => γ n i ∈ disjointed U n)
  have hshell (n : ℕ) : ν.restrict (disjointed U n) =
      Measure.sum (fun i : t n => Measure.dirac (γ n i)) := by
    rw [← Measure.restrict_restrict_of_subset (disjointed_subset U n), hs n,
      restrict_finite_atoms]
    exact (Measure.sum_coe_finset (t n) (fun i => Measure.dirac (γ n i))).symm
  refine ⟨(n : ℕ) × (t n), inferInstance, (fun i => γ i.1 i.2), ?_⟩
  have hdecomp := Measure.restrict_iUnion (μ := ν) (disjoint_disjointed U)
    (MeasurableSet.disjointed hU)
  rw [iUnion_disjointed, hcover, Measure.restrict_univ] at hdecomp
  rw [hdecomp]
  simp_rw [hshell]
  ext A hA
  simp only [Measure.sum_apply _ hA]
  exact (ENNReal.tsum_sigma' (fun i : (n : ℕ) × (t n) =>
    (Measure.dirac (γ i.1 i.2)) A)).symm

end FleetAtomicGluing
