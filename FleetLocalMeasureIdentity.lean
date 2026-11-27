import FleetLocalAtomicLimit

noncomputable section
open Filter Topology MeasureTheory Set
open scoped Classical

namespace FleetLocalMeasureIdentity

/-- Local compact tests bound a compact subset's mass in one measure by its mass
in the other, using cutoffs supported in the prescribed open set. -/
theorem compact_measure_le_of_local_tests (μ ν : Measure ℝ)
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    {U : Set ℝ} (hU : IsOpen U)
    (heq : ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ →
      (∀ t, t ∉ U → φ t = 0) → (∫ t, φ t ∂μ) = ∫ t, φ t ∂ν)
    {K : Set ℝ} (hK : IsCompact K) (hKU : K ⊆ U) : μ K ≤ ν K := by
  rw [K.measure_eq_iInf_isOpen ν]
  apply le_iInf
  intro V
  apply le_iInf
  intro hKV
  apply le_iInf
  intro hV
  obtain ⟨c, hcK, hcV, hcs, hc01⟩ :=
    exists_continuous_one_zero_of_isCompact hK (hV.inter hU).isClosed_compl
      (disjoint_compl_right_iff_subset.mpr (subset_inter hKV hKU))
  have hczero (t : ℝ) (ht : t ∉ U) : c t = 0 :=
    hcV (fun h => ht h.2)
  have hcc : Continuous (fun t => (c t : ℂ)) := Complex.continuous_ofReal.comp c.continuous
  have hsc : HasCompactSupport (fun t => (c t : ℂ)) :=
    hcs.comp_left (show ((0 : ℝ) : ℂ) = 0 by simp)
  have hci : (∫ t, c t ∂μ) = ∫ t, c t ∂ν := by
    have h := congrArg Complex.re (heq (fun t => (c t : ℂ)) hcc hsc
      (fun t ht => by change (c t : ℂ) = 0; rw [hczero t ht]; simp))
    simpa only [_root_.integral_complex_ofReal, Complex.ofReal_re] using h
  calc
    μ K ≤ ENNReal.ofReal (∫ t, c t ∂μ) :=
      (c.continuous.integrable_of_hasCompactSupport hcs).measure_le_integral
        (Filter.Eventually.of_forall (fun t => (hc01 t).1))
        (fun t ht => by have he : c t = 1 := hcK ht; rw [he])
    _ = ENNReal.ofReal (∫ t, c t ∂ν) := congrArg ENNReal.ofReal hci
    _ ≤ ν V := integral_le_measure (fun t _ => (hc01 t).2)
      (fun t ht => by have he : c t = 0 := hcV (fun h => ht h.1); rw [he])

/-- Tests supported in an open U determine the restrictions of locally finite
measures to U. No boundary-null hypothesis is necessary. -/
theorem measure_restrict_eq_of_local_test_integrals (μ ν : Measure ℝ)
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    {U : Set ℝ} (hU : IsOpen U)
    (heq : ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ →
      (∀ t, t ∉ U → φ t = 0) → (∫ t, φ t ∂μ) = ∫ t, φ t ∂ν) :
    μ.restrict U = ν.restrict U := by
  have hcompact (K : Set ℝ) (hK : IsCompact K) (hKU : K ⊆ U) : μ K = ν K :=
    le_antisymm (compact_measure_le_of_local_tests μ ν hU heq hK hKU)
      (compact_measure_le_of_local_tests ν μ hU (fun φ hc hs hz => (heq φ hc hs hz).symm) hK hKU)
  have hopen (V : Set ℝ) (hV : IsOpen V) : (μ.restrict U) V = (ν.restrict U) V := by
    rw [Measure.restrict_apply hV.measurableSet, Measure.restrict_apply hV.measurableSet]
    rw [(hV.inter hU).measure_eq_iSup_isCompact μ, (hV.inter hU).measure_eq_iSup_isCompact ν]
    congr 1
    funext K
    congr 1
    funext hKV
    congr 1
    funext hK
    exact hcompact K hK (fun t ht => (hKV ht).2)
  apply Measure.ext
  intro A _
  rw [A.measure_eq_iInf_isOpen (μ.restrict U), A.measure_eq_iInf_isOpen (ν.restrict U)]
  congr 1
  funext V
  congr 1
  funext hAV
  congr 1
  funext hV
  exact hopen V hV

/-- Restriction of a finite unit-atom measure retains precisely the indices
whose coordinates lie in U; coinciding coordinates remain repeated. -/
theorem restrict_unit_atoms {N : ℕ} (y : Fin N → ℝ) (U : Set ℝ) :
    (∑ i : Fin N, Measure.dirac (y i)).restrict U =
      ∑ i ∈ Finset.univ.filter (fun i => y i ∈ U), Measure.dirac (y i) := by
  classical
  change Measure.restrictₗ U (∑ i : Fin N, Measure.dirac (y i)) = _
  rw [map_sum]
  simp only [Measure.restrictₗ_apply, restrict_dirac, Finset.sum_filter]

/-- A local finite trace representation is an actual restricted measure identity. -/
theorem restrict_eq_unit_atoms_of_local_trace {N : ℕ} (y : Fin N → ℝ)
    (ν : Measure ℝ) [IsFiniteMeasureOnCompacts ν] {U : Set ℝ} (hU : IsOpen U)
    (htrace : ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ →
      (∀ t, t ∉ U → φ t = 0) → (∫ t, φ t ∂ν) = ∑ i : Fin N, φ (y i)) :
    ν.restrict U = ∑ i ∈ Finset.univ.filter (fun i => y i ∈ U), Measure.dirac (y i) := by
  rw [← restrict_unit_atoms]
  apply measure_restrict_eq_of_local_test_integrals ν _ hU
  intro φ hc hs hz
  rw [FleetAtomicLimit.integral_unit_atoms]
  exact htrace φ hc hs hz

/-- Every bounded open window of the weighted compact-test limit is an actual
finite counting measure. No integer-atomic assumption on ν is used. -/
theorem exists_local_restricted_counting_measure
    (c : ℕ → ℕ) (x : ∀ n, Fin (c n) → ℝ)
    (μ : ℕ → Measure ℝ) (ν : Measure ℝ) [IsFiniteMeasureOnCompacts ν]
    (hμ : ∀ n, μ n = ∑ i : Fin (c n), Measure.dirac (x n i))
    {M : ℝ} (hm : ∀ n, (∫ t : ℝ, (1+t^2)⁻¹ ∂μ n) ≤ M)
    (hvague : ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun n => ∫ t, φ t ∂μ n) atTop (𝓝 (∫ t, φ t ∂ν)))
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ m ≤ ⌈M * (1+(R+1)^2)⌉₊, ∃ y : Fin m → ℝ,
      (∀ i, |y i| ≤ R+1) ∧
      ν.restrict (Ioo (-R) R) =
        ∑ i ∈ Finset.univ.filter (fun i => y i ∈ Ioo (-R) R), Measure.dirac (y i) := by
  obtain ⟨m, hmN, y, hy, htrace⟩ :=
    FleetLocalAtomicLimit.exists_local_trace_representation_of_unit_atom_measures
      c x μ ν hμ hm hvague R hR
  refine ⟨m, hmN, y, hy, ?_⟩
  refine (restrict_eq_unit_atoms_of_local_trace y ν isOpen_Ioo htrace).trans ?_
  apply Finset.sum_congr
  · ext i
    simp
  · intro i _
    rfl

end FleetLocalMeasureIdentity
