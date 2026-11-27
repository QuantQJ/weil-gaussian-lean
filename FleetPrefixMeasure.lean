import Mathlib

namespace FleetPrefixMeasure
open MeasureTheory Set Filter Topology

/-- Unit atoms indexed with multiplicity; coincident ordinates are not identified. -/
noncomputable def atomMeasure {ι : Type*} (γ : ι → ℝ) : Measure ℝ :=
  Measure.sum (fun i => Measure.dirac (γ i))

/-- Finitely many indexed atoms over each compact set gives finite measure on compacts. -/
theorem finiteOnCompacts {ι : Type*} (γ : ι → ℝ)
    (hγ : ∀ K : Set ℝ, IsCompact K → {i : ι | γ i ∈ K}.Finite) :
    IsFiniteMeasureOnCompacts (atomMeasure γ) := by
  classical
  constructor
  intro K hK
  let J := (hγ K hK).toFinset
  have hzero (i : ι) (hi : i ∉ J) : Measure.dirac (γ i) K = 0 := by
    rw [Measure.dirac_apply' _ hK.isClosed.measurableSet]
    have hn : γ i ∉ K := by simpa [J] using hi
    simp [hn]
  rw [atomMeasure, Measure.sum_apply _ hK.isClosed.measurableSet,
    tsum_eq_sum hzero]
  apply ENNReal.sum_lt_top.mpr
  intro i hi
  rw [Measure.dirac_apply' _ hK.isClosed.measurableSet]
  by_cases hik : γ i ∈ K <;> simp [hik]

/-- Local finiteness requires no choice of distinct spectral values. -/
theorem locallyFinite {ι : Type*} (γ : ι → ℝ)
    (hγ : ∀ K : Set ℝ, IsCompact K → {i : ι | γ i ∈ K}.Finite) :
    IsLocallyFiniteMeasure (atomMeasure γ) := by
  letI := finiteOnCompacts γ hγ
  infer_instance

/-- Continuous compact probes integrate as a sum of their values at the unit atoms. -/
theorem hasSum_integral {ι : Type*} (γ : ι → ℝ)
    (hγ : ∀ K : Set ℝ, IsCompact K → {i : ι | γ i ∈ K}.Finite)
    {φ : ℝ → ℂ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    HasSum (fun i => φ (γ i)) (∫ x, φ x ∂atomMeasure γ) := by
  letI := finiteOnCompacts γ hγ
  have hi : Integrable φ (atomMeasure γ) := hφ.integrable_of_hasCompactSupport hc
  simpa only [atomMeasure, integral_dirac] using hasSum_integral_measure hi

/-- Any finite prefix containing the test's nonzero atom values gives its exact integral. -/
theorem integral_eq_finset_sum {ι : Type*} (γ : ι → ℝ)
    (hγ : ∀ K : Set ℝ, IsCompact K → {i : ι | γ i ∈ K}.Finite)
    {φ : ℝ → ℂ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (J : Finset ι) (hJ : ∀ i ∉ J, φ (γ i) = 0) :
    (∫ x, φ x ∂atomMeasure γ) = ∑ i ∈ J, φ (γ i) := by
  rw [← (hasSum_integral γ hγ hφ hc).tsum_eq]
  exact tsum_eq_sum hJ

/-- Uniform prefix localization implies finite indexed preimages of compact sets. -/
theorem compact_preimage_finite_of_prefix {ι : Type*} (γ : ι → ℝ) (index : ι → ℕ)
    (hinj : Function.Injective index)
    (hprefix : ∀ R : ℝ, 0 ≤ R → ∃ N : ℕ, ∀ i, N ≤ index i → R < |γ i|)
    (K : Set ℝ) (hK : IsCompact K) : {i : ι | γ i ∈ K}.Finite := by
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (continuous_id : Continuous (id : ℝ → ℝ)).continuousOn
  obtain ⟨N, hN⟩ := hprefix (max B 0) (le_max_right _ _)
  have hf : {i : ι | index i < N}.Finite :=
    (Set.finite_Iio N).preimage hinj.injOn
  apply hf.subset
  intro i hi
  by_contra hn
  have hni : N ≤ index i := Nat.le_of_not_gt hn
  have ht := hN i hni
  have hb := hB (γ i) hi
  simp only [id_eq, Real.norm_eq_abs] at hb
  linarith [le_max_left B 0]

/-- The requested retained-index localization hypothesis gives a locally finite atomic measure. -/
theorem locallyFinite_of_prefix {ι : Type*} (γ : ι → ℝ) (index : ι → ℕ)
    (hinj : Function.Injective index)
    (hprefix : ∀ R : ℝ, 0 ≤ R → ∃ N : ℕ, ∀ i, N ≤ index i → R < |γ i|) :
    IsLocallyFiniteMeasure (atomMeasure γ) :=
  locallyFinite γ (compact_preimage_finite_of_prefix γ index hinj hprefix)

/-- Every compact continuous test is represented by one finite index prefix exactly. -/
theorem exists_prefix_integral_eq {ι : Type*} (γ : ι → ℝ) (index : ι → ℕ)
    (hinj : Function.Injective index)
    (hprefix : ∀ R : ℝ, 0 ≤ R → ∃ N : ℕ, ∀ i, N ≤ index i → R < |γ i|)
    {φ : ℝ → ℂ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    ∃ N : ℕ, ∃ J : Finset ι,
      (∀ i, i ∈ J ↔ index i < N) ∧
      (∫ x, φ x ∂atomMeasure γ) = ∑ i ∈ J, φ (γ i) := by
  classical
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuousOn
    (continuous_id : Continuous (id : ℝ → ℝ)).continuousOn
  obtain ⟨N, hN⟩ := hprefix (max B 0) (le_max_right _ _)
  have hf : {i : ι | index i < N}.Finite := (Set.finite_Iio N).preimage hinj.injOn
  let J := hf.toFinset
  have hJ : ∀ i, i ∈ J ↔ index i < N := by intro i; simp [J]
  refine ⟨N, J, hJ, ?_⟩
  apply integral_eq_finset_sum γ (compact_preimage_finite_of_prefix γ index hinj hprefix) hφ hc J
  intro i hi
  by_contra hne
  have ht : γ i ∈ tsupport φ := subset_closure hne
  have hb := hB (γ i) ht
  simp only [id_eq, Real.norm_eq_abs] at hb
  have hni : N ≤ index i := Nat.le_of_not_gt (fun h => hi ((hJ i).mpr h))
  have hfar := hN i hni
  linarith [le_max_left B 0]

end FleetPrefixMeasure

#print axioms FleetPrefixMeasure.locallyFinite_of_prefix
#print axioms FleetPrefixMeasure.hasSum_integral
#print axioms FleetPrefixMeasure.integral_eq_finset_sum

#print axioms FleetPrefixMeasure.exists_prefix_integral_eq
