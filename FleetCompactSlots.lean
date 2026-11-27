import FleetAtomicLimit

noncomputable section
open Filter Topology Set

namespace FleetCompactSlots

/-- One subsequence simultaneously converges in every compactified atom slot.
No measure limit or arithmetic assertion is assumed or concluded here. -/
theorem exists_slot_subsequence (z : ℕ → ℕ → ℝ)
    (hz : ∀ n k, z n k ∈ Icc (-1 : ℝ) 1) :
    ∃ a : ℕ → ℝ, (∀ k, a k ∈ Icc (-1 : ℝ) 1) ∧
      ∃ r : ℕ → ℕ, StrictMono r ∧
        Tendsto (fun n => z (r n)) atTop (𝓝 a) := by
  have hK : IsCompact {a : ℕ → ℝ | ∀ k, a k ∈ Icc (-1 : ℝ) 1} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  obtain ⟨a, ha, r, hr, hconv⟩ := hK.tendsto_subseq (fun n => hz n)
  exact ⟨a, ha, r, hr, hconv⟩

/-- Slot convergence passes through a continuous probe on every fixed finite prefix. -/
theorem finite_prefix_trace_tendsto {z : ℕ → ℕ → ℝ} {a : ℕ → ℝ}
    (hc : Tendsto z atTop (𝓝 a)) (F : ℝ → ℂ) (hF : Continuous F) (N : ℕ) :
    Tendsto (fun n => ∑ k ∈ Finset.range N, F (z n k)) atTop
      (𝓝 (∑ k ∈ Finset.range N, F (a k))) := by
  have hsum : Continuous (fun a : ℕ → ℝ => ∑ k ∈ Finset.range N, F (a k)) :=
    continuous_finset_sum _ (fun k _ => hF.comp (continuous_apply k))
  exact hsum.continuousAt.tendsto.comp hc

/-- Two finite truncations agree when every term beyond either cutoff vanishes. -/
theorem sum_range_eq_of_vanish (f : ℕ → ℂ) (c N : ℕ)
    (hc : ∀ k, c ≤ k → f k = 0) (hN : ∀ k, N ≤ k → f k = 0) :
    (∑ k ∈ Finset.range c, f k) = ∑ k ∈ Finset.range N, f k := by
  have hle (a b : ℕ) (hab : a ≤ b) (ha : ∀ k, a ≤ k → f k = 0) :
      (∑ k ∈ Finset.range a, f k) = ∑ k ∈ Finset.range b, f k := by
    apply Finset.sum_subset (Finset.range_mono hab)
    intro k _ hk
    exact ha k (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hk))
  rcases le_total c N with h | h
  · exact hle c N h hc
  · exact (hle N c h hN).symm

end FleetCompactSlots
