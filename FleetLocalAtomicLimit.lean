import FleetAtomicLimit

noncomputable section
open Filter Topology MeasureTheory Set

namespace FleetLocalAtomicLimit

lemma sum_enumerate_finset {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (∑ j : Fin s.card, f (((s.equivFin).symm j) : ι)) = ∑ i ∈ s, f i := by
  calc
    _ = ∑ i : s, f (i : ι) := (Equiv.sum_comp s.equivFin.symm (fun i : s => f (i : ι)))
    _ = _ := Finset.sum_coe_sort s f

/-- Buffered finite selection preserves every trace supported in the inner window. -/
lemma sum_buffer_eq {N : ℕ} (x : Fin N → ℝ) (R : ℝ) (φ : ℝ → ℂ)
    (hφ : ∀ t, t ∉ Ioo (-R) R → φ t = 0) :
    (∑ i ∈ Finset.univ.filter (fun i => |x i| ≤ R+1), φ (x i)) = ∑ i, φ (x i) := by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i hi hn
  apply hφ
  intro hx
  have hbuf : |x i| ≤ R+1 := abs_le.mpr (by constructor <;> linarith [hx.1, hx.2])
  exact hn (Finset.mem_filter.mpr ⟨hi, hbuf⟩)

/-- Uniformly weighted finite unit configurations have a finite unit-atom trace
representation on each bounded open window. No integer-atomic assumption on the
limit measure is made. Selected atom limits may lie at the outer buffer boundary. -/
theorem exists_local_trace_representation
    (c : ℕ → ℕ) (x : ∀ n, Fin (c n) → ℝ) {M : ℝ}
    (hm : ∀ n, (∑ i : Fin (c n), (1+(x n i)^2)⁻¹) ≤ M)
    (ν : Measure ℝ) [IsFiniteMeasureOnCompacts ν]
    (hvague : ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun n => ∑ i : Fin (c n), φ (x n i)) atTop (𝓝 (∫ t, φ t ∂ν)))
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ m ≤ ⌈M * (1+(R+1)^2)⌉₊, ∃ y : Fin m → ℝ,
      (∀ i, |y i| ≤ R+1) ∧
      ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ →
        (∀ t, t ∉ Ioo (-R) R → φ t = 0) →
        (∫ t, φ t ∂ν) = ∑ i : Fin m, φ (y i) := by
  classical
  let u : (n : ℕ) → Finset (Fin (c n)) :=
    fun n => Finset.univ.filter (fun i => |x n i| ≤ R+1)
  let d : ℕ → ℕ := fun n => (u n).card
  let N : ℕ := ⌈M * (1+(R+1)^2)⌉₊
  have hd (n : ℕ) : d n ≤ N := by
    have hb := FleetAtomicLimit.local_card_bound Finset.univ (x n)
      (show 0 ≤ R+1 by linarith) (hm n)
    have hbc : ((d n : ℕ) : ℝ) ≤ (N : ℝ) := hb.trans (Nat.le_ceil _)
    exact_mod_cast hbc
  let q : (n : ℕ) → Fin (d n) → ℝ :=
    fun n j => x n (((u n).equivFin.symm j) : Fin (c n))
  have hq (n : ℕ) (j : Fin (d n)) : |q n j| ≤ R+1 :=
    (Finset.mem_filter.mp ((u n).equivFin.symm j).property).2
  have hqsum (φ : ℝ → ℂ) (hφ : ∀ t, t ∉ Ioo (-R) R → φ t = 0) (n : ℕ) :
      (∑ j : Fin (d n), φ (q n j)) = ∑ i : Fin (c n), φ (x n i) := by
    change (∑ j : Fin (u n).card, (fun i => φ (x n i)) (((u n).equivFin.symm j))) = _
    exact (sum_enumerate_finset (u n) (fun i => φ (x n i))).trans
      (sum_buffer_eq (x n) R φ hφ)
  obtain ⟨m, hmN, r, hr, hcount⟩ := FleetAtomicLimit.exists_constant_count_subsequence d N hd
  let z : ℕ → Fin m → ℝ := fun n i => q (r n) (Fin.cast (hcount n).symm i)
  have hz (n : ℕ) (i : Fin m) : |z n i| ≤ R+1 := hq (r n) _
  have hzsum (φ : ℝ → ℂ) (hφ : ∀ t, t ∉ Ioo (-R) R → φ t = 0) (n : ℕ) :
      (∑ i : Fin m, φ (z n i)) = ∑ i : Fin (c (r n)), φ (x (r n) i) := by
    calc
      _ = ∑ j : Fin (d (r n)), φ (q (r n) j) :=
        Equiv.sum_comp (finCongr (hcount n).symm) (fun j => φ (q (r n) j))
      _ = _ := hqsum φ hφ (r n)
  have hK : IsCompact {y : Fin m → ℝ | ∀ i, y i ∈ Icc (-(R+1)) (R+1)} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  obtain ⟨y, hy, s, hs, hconv⟩ := hK.tendsto_subseq (fun n i => abs_le.mp (hz n i))
  refine ⟨m, hmN, y, (fun i => abs_le.mpr (hy i)), ?_⟩
  intro φ hc hcs hφ
  have hcontinuous : Continuous (fun y : Fin m → ℝ => ∑ i : Fin m, φ (y i)) :=
    continuous_finset_sum _ (fun i _ => hc.comp (continuous_apply i))
  have hlim := hcontinuous.continuousAt.tendsto.comp hconv
  have hgiven := (hvague φ hc hcs).comp (hr.comp hs).tendsto_atTop
  have heq : (fun n => ∑ i : Fin (c (r (s n))), φ (x (r (s n)) i)) =
      (fun n => ∑ i : Fin m, φ (z (s n) i)) := by
    funext n
    exact (hzsum φ hφ (s n)).symm
  simp only [Function.comp_def] at hgiven hlim
  rw [heq] at hgiven
  exact tendsto_nhds_unique hgiven hlim

lemma integral_real_unit_atoms {N : ℕ} (y : Fin N → ℝ) (f : ℝ → ℝ) :
    (∫ t, f t ∂(∑ i : Fin N, Measure.dirac (y i))) = ∑ i : Fin N, f (y i) := by
  rw [integral_finset_sum_measure]
  · simp only [integral_dirac]
  · intro i _
    exact (integrable_const (f (y i))).congr (ae_eq_dirac f).symm

/-- Measure-facing buffered localization: actual finite unit-atom measures with
uniform inverse-quadratic mass yield local finite trace representations of their
locally finite compact-test limit. Atoms need not be globally confined. -/
theorem exists_local_trace_representation_of_unit_atom_measures
    (c : ℕ → ℕ) (x : ∀ n, Fin (c n) → ℝ)
    (μ : ℕ → Measure ℝ) (ν : Measure ℝ) [IsFiniteMeasureOnCompacts ν]
    (hμ : ∀ n, μ n = ∑ i : Fin (c n), Measure.dirac (x n i))
    {M : ℝ} (hm : ∀ n, (∫ t : ℝ, (1+t^2)⁻¹ ∂μ n) ≤ M)
    (hvague : ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun n => ∫ t, φ t ∂μ n) atTop (𝓝 (∫ t, φ t ∂ν)))
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ m ≤ ⌈M * (1+(R+1)^2)⌉₊, ∃ y : Fin m → ℝ,
      (∀ i, |y i| ≤ R+1) ∧
      ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ →
        (∀ t, t ∉ Ioo (-R) R → φ t = 0) →
        (∫ t, φ t ∂ν) = ∑ i : Fin m, φ (y i) := by
  have hmsum (n : ℕ) : (∑ i : Fin (c n), (1+(x n i)^2)⁻¹) ≤ M := by
    simpa only [hμ, integral_real_unit_atoms] using hm n
  have hsum : ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun n => ∑ i : Fin (c n), φ (x n i)) atTop (𝓝 (∫ t, φ t ∂ν)) := by
    intro φ hc hs
    simpa only [hμ, FleetAtomicLimit.integral_unit_atoms] using hvague φ hc hs
  exact exists_local_trace_representation c x hmsum ν hsum R hR

end FleetLocalAtomicLimit
