import Mathlib

noncomputable section
open Filter Topology MeasureTheory Set

namespace FleetAtomicLimit

/-- A weighted bound controls the number of indices in a compact window.
Indices are counted with repetitions; equal coordinates are not deduplicated. -/
theorem local_card_bound {ι : Type*} [DecidableEq ι] (s : Finset ι) (γ : ι → ℝ)
    {R M : ℝ} (hR : 0 ≤ R)
    (hM : (∑ i ∈ s, (1 + (γ i)^2)⁻¹) ≤ M) :
    ((s.filter (fun i => |γ i| ≤ R)).card : ℝ) ≤ M * (1+R^2) := by
  let u := s.filter (fun i => |γ i| ≤ R)
  have hD : 0 < 1+R^2 := by positivity
  have heach (i : ι) (hi : i ∈ u) : 1 ≤ (1+R^2) * (1+(γ i)^2)⁻¹ := by
    have hγ := (Finset.mem_filter.mp hi).2
    have hsq : (γ i)^2 ≤ R^2 := by
      have ha := abs_nonneg (γ i)
      nlinarith [sq_abs (γ i)]
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : 0 < 1+(γ i)^2)]
    linarith
  have hsum : (∑ i ∈ u, (1+(γ i)^2)⁻¹) ≤ ∑ i ∈ s, (1+(γ i)^2)⁻¹ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro i _ _
    positivity
  calc
    ((u.card : ℕ) : ℝ) = ∑ i ∈ u, (1 : ℝ) := by simp
    _ ≤ ∑ i ∈ u, (1+R^2) * (1+(γ i)^2)⁻¹ := Finset.sum_le_sum heach
    _ = (1+R^2) * ∑ i ∈ u, (1+(γ i)^2)⁻¹ := (Finset.mul_sum _ _ _).symm
    _ ≤ (1+R^2) * M := mul_le_mul_of_nonneg_left (hsum.trans hM) hD.le
    _ = M * (1+R^2) := mul_comm _ _

/-- In a single compact region, a fixed number of unit atoms has a subsequential
configuration limit. A supplied compact-test limit is represented by exactly these
unit atoms, including collisions with their full integer multiplicities. -/
theorem exists_finite_trace_representation_of_compact_configurations
    {N : ℕ} (x : ℕ → Fin N → ℝ) {K : Set ℝ} (hK : IsCompact K)
    (hx : ∀ n i, x n i ∈ K) (ν : Measure ℝ) [IsFiniteMeasureOnCompacts ν]
    (htrace : ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun n => ∑ i : Fin N, φ (x n i)) atTop (𝓝 (∫ t, φ t ∂ν))) :
    ∃ y : Fin N → ℝ, (∀ i, y i ∈ K) ∧
      ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ →
        (∫ t, φ t ∂ν) = ∑ i : Fin N, φ (y i) := by
  have hp : IsCompact {y : Fin N → ℝ | ∀ i, y i ∈ K} :=
    isCompact_pi_infinite (fun _ => hK)
  obtain ⟨y, hy, r, hr, hconv⟩ := hp.tendsto_subseq (fun n => hx n)
  refine ⟨y, hy, ?_⟩
  intro φ hc hs
  have hc' : Continuous (fun y : Fin N → ℝ => ∑ i : Fin N, φ (y i)) :=
    continuous_finsetSum _ (fun i _ => hc.comp (continuous_apply i))
  have hsum := hc'.continuousAt.tendsto.comp hconv
  have hgiven := (htrace φ hc hs).comp hr.tendsto_atTop
  exact tendsto_nhds_unique hgiven hsum

/-- A finite sum of unit Dirac masses integrates as a sum with repetitions. -/
theorem integral_unit_atoms {N : ℕ} (y : Fin N → ℝ) (φ : ℝ → ℂ) :
    (∫ t, φ t ∂(∑ i : Fin N, Measure.dirac (y i))) = ∑ i : Fin N, φ (y i) := by
  rw [integral_finsetSum_measure]
  · simp only [integral_dirac]
  · intro i _
    exact (integrable_const (φ (y i))).congr (ae_eq_dirac φ).symm

/-- Measure-facing version of the bounded configuration result. It asserts exact
compact-test representation by unit Dirac masses, not the unrestricted local
point-measure closure theorem. -/
theorem compact_test_representation_of_unit_atom_measures
    {N : ℕ} (x : ℕ → Fin N → ℝ) {K : Set ℝ} (hK : IsCompact K)
    (hx : ∀ n i, x n i ∈ K) (μ : ℕ → Measure ℝ) (ν : Measure ℝ)
    [IsFiniteMeasureOnCompacts ν]
    (hμ : ∀ n, μ n = ∑ i : Fin N, Measure.dirac (x n i))
    (hvague : ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun n => ∫ t, φ t ∂μ n) atTop (𝓝 (∫ t, φ t ∂ν))) :
    ∃ y : Fin N → ℝ, (∀ i, y i ∈ K) ∧
      ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ →
        (∫ t, φ t ∂ν) = (∫ t, φ t ∂(∑ i : Fin N, Measure.dirac (y i))) := by
  have htrace : ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun n => ∑ i : Fin N, φ (x n i)) atTop (𝓝 (∫ t, φ t ∂ν)) := by
    intro φ hc hs
    have ht := hvague φ hc hs
    simpa only [hμ, integral_unit_atoms] using ht
  obtain ⟨y, hy, hrep⟩ :=
    exists_finite_trace_representation_of_compact_configurations x hK hx ν htrace
  refine ⟨y, hy, ?_⟩
  intro φ hc hs
  rw [integral_unit_atoms]
  exact hrep φ hc hs

/-- Compactly supported continuous complex tests determine locally finite real
Borel measures. Regularity supplies the compact/open-set approximation. -/
theorem measure_eq_of_compact_test_integrals (μ ν : Measure ℝ)
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (heq : ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ →
      (∫ t, φ t ∂μ) = ∫ t, φ t ∂ν) : μ = ν := by
  have hreal (f : ℝ → ℝ) (hc : Continuous f) (hs : HasCompactSupport f) :
      (∫ t, f t ∂μ) = ∫ t, f t ∂ν := by
    have hcc : Continuous (fun t => (f t : ℂ)) := Complex.continuous_ofReal.comp hc
    have hss : HasCompactSupport (fun t => (f t : ℂ)) :=
      hs.comp_left (show ((0 : ℝ) : ℂ) = 0 by simp)
    have h := congrArg Complex.re (heq (fun t => (f t : ℂ)) hcc hss)
    simpa only [_root_.integral_complex_ofReal, Complex.ofReal_re] using h
  have hcompact (K : Set ℝ) (hK : IsCompact K) : μ K = ν K := by
    rw [hK.measure_eq_biInf_integral_hasCompactSupport μ,
      hK.measure_eq_biInf_integral_hasCompactSupport ν]
    congr 1
    funext f
    congr 1
    funext hc
    congr 1
    funext hs
    rw [hreal f hc hs]
  have hopen (U : Set ℝ) (hU : IsOpen U) : μ U = ν U := by
    rw [hU.measure_eq_iSup_isCompact μ, hU.measure_eq_iSup_isCompact ν]
    congr 1
    funext K
    congr 1
    funext hKU
    congr 1
    funext hK
    exact hcompact K hK
  apply Measure.ext
  intro A _
  rw [A.measure_eq_iInf_isOpen μ, A.measure_eq_iInf_isOpen ν]
  congr 1
  funext U
  congr 1
  funext hAU
  congr 1
  funext hU
  exact hopen U hU

/-- Full measure equality for the fixed-N, compactly confined configuration case. -/
theorem measure_eq_unit_atoms_of_compact_configurations
    {N : ℕ} (x : ℕ → Fin N → ℝ) {K : Set ℝ} (hK : IsCompact K)
    (hx : ∀ n i, x n i ∈ K) (μ : ℕ → Measure ℝ) (ν : Measure ℝ)
    [IsFiniteMeasureOnCompacts ν]
    (hμ : ∀ n, μ n = ∑ i : Fin N, Measure.dirac (x n i))
    (hvague : ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun n => ∫ t, φ t ∂μ n) atTop (𝓝 (∫ t, φ t ∂ν))) :
    ∃ y : Fin N → ℝ, (∀ i, y i ∈ K) ∧ ν = ∑ i : Fin N, Measure.dirac (y i) := by
  obtain ⟨y, hy, heq⟩ :=
    compact_test_representation_of_unit_atom_measures x hK hx μ ν hμ hvague
  exact ⟨y, hy, measure_eq_of_compact_test_integrals ν _ heq⟩

/-- A uniformly bounded natural count is constant along a strictly increasing
subsequence. No convergence of the original count sequence is assumed. -/
theorem exists_constant_count_subsequence (c : ℕ → ℕ) (N : ℕ) (hc : ∀ n, c n ≤ N) :
    ∃ m ≤ N, ∃ r : ℕ → ℕ, StrictMono r ∧ ∀ n, c (r n) = m := by
  have hs : IsCompact (Set.Iic N) := (Set.finite_Iic N).isCompact
  obtain ⟨m, hm, r, hr, ht⟩ := hs.tendsto_subseq hc
  have hev : ∀ᶠ n in atTop, c (r n) = m := by
    simpa only [nhds_discrete, tendsto_pure, Function.comp_def] using ht
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨m, hm, (fun n => r (n+n₀)), ?_, ?_⟩
  · intro a b hab
    exact hr (by omega)
  · intro n
    exact hn₀ (n+n₀) (by omega)

/-- Variable counts bounded by N are allowed when all atoms remain in one fixed
compact set. The limit is an actual finite counting measure, with multiplicities. -/
theorem measure_eq_unit_atoms_of_bounded_compact_configurations
    (c : ℕ → ℕ) (N : ℕ) (hc : ∀ n, c n ≤ N)
    (x : ∀ n, Fin (c n) → ℝ) {K : Set ℝ} (hK : IsCompact K)
    (hx : ∀ n i, x n i ∈ K) (μ : ℕ → Measure ℝ) (ν : Measure ℝ)
    [IsFiniteMeasureOnCompacts ν]
    (hμ : ∀ n, μ n = ∑ i : Fin (c n), Measure.dirac (x n i))
    (hvague : ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun n => ∫ t, φ t ∂μ n) atTop (𝓝 (∫ t, φ t ∂ν))) :
    ∃ m ≤ N, ∃ y : Fin m → ℝ, (∀ i, y i ∈ K) ∧
      ν = ∑ i : Fin m, Measure.dirac (y i) := by
  obtain ⟨m, hm, r, hr, hcount⟩ := exists_constant_count_subsequence c N hc
  let y : ℕ → Fin m → ℝ := fun n i => x (r n) (Fin.cast (hcount n).symm i)
  have hy (n : ℕ) (i : Fin m) : y n i ∈ K := hx (r n) _
  have hμ' (n : ℕ) : μ (r n) = ∑ i : Fin m, Measure.dirac (y n i) := by
    rw [hμ (r n)]
    exact (Equiv.sum_comp (finCongr (hcount n).symm)
      (fun i : Fin (c (r n)) => Measure.dirac (x (r n) i))).symm
  have hv' : ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun n => ∫ t, φ t ∂μ (r n)) atTop (𝓝 (∫ t, φ t ∂ν)) := by
    intro φ hφ hs
    exact (hvague φ hφ hs).comp hr.tendsto_atTop
  obtain ⟨z, hz, heq⟩ := measure_eq_unit_atoms_of_compact_configurations
    y hK hy (fun n => μ (r n)) ν hμ' hv'
  exact ⟨m, hm, z, hz, heq⟩

/-- Natural-valued counts with a finite real limit eventually stabilize.
This lemma requires actual count convergence; compact-test convergence alone
has not yet been converted to interval-count convergence here. -/
theorem count_limit_eventually_constant {c : ℕ → ℕ} {L : ℝ}
    (hc : Tendsto (fun n => (c n : ℝ)) atTop (𝓝 L)) :
    ∃ m : ℕ, L = (m : ℝ) ∧ ∀ᶠ n in atTop, c n = m := by
  have hclosed : IsClosed (Set.range ((↑) : ℕ → ℝ)) :=
    Nat.isClosedEmbedding_coe_real.isClosed_range
  have hmem : L ∈ Set.range ((↑) : ℕ → ℝ) :=
    hclosed.mem_of_tendsto hc (Filter.Eventually.of_forall (fun n => ⟨c n, rfl⟩))
  obtain ⟨m, hm⟩ := hmem
  refine ⟨m, hm.symm, ?_⟩
  have hcm : Tendsto c atTop (𝓝 m) :=
    Nat.isClosedEmbedding_coe_real.isEmbedding.tendsto_nhds_iff.mpr
      (by simpa [hm, Function.comp_def] using hc)
  simpa only [nhds_discrete, tendsto_pure] using hcm

end FleetAtomicLimit
