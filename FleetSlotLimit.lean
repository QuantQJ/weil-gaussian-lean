import FleetPrefixMeasure
import FleetRealCompactification
import FleetCompactSlots

noncomputable section

namespace FleetSlotLimit
open Set Filter Topology MeasureTheory FleetRealCompactification

abbrev Retained (a : ℕ → ℝ) := {k : ℕ // |a k| < 1}
def ordinate (a : ℕ → ℝ) (i : Retained a) : ℝ := r (a i)
noncomputable def limitMeasure (a : ℕ → ℝ) : Measure ℝ :=
  FleetPrefixMeasure.atomMeasure (ordinate a)

/-- Uniform closed lower bounds survive coordinatewise convergence. -/
theorem limit_prefix_bound {z : ℕ → ℕ → ℝ} {a : ℕ → ℝ}
    (hc : Tendsto z atTop (𝓝 a)) {S : ℝ} {N : ℕ}
    (hN : ∀ n k, N ≤ k → S/(1+S) ≤ |z n k|) :
    ∀ k, N ≤ k → S/(1+S) ≤ |a k| := by
  intro k hk
  have ht : Tendsto (fun n => |z n k|) atTop (𝓝 |a k|) :=
    continuous_abs.continuousAt.tendsto.comp ((continuous_apply k).continuousAt.tendsto.comp hc)
  exact isClosed_Ici.mem_of_tendsto ht (Eventually.of_forall (fun n => hN n k hk))

/-- Interior limit slots define a locally finite unit-atom measure. -/
theorem limit_locallyFinite {z : ℕ → ℕ → ℝ} {a : ℕ → ℝ}
    (hc : Tendsto z atTop (𝓝 a))
    (hprefix : ∀ S : ℝ, 0 ≤ S → ∃ N : ℕ, ∀ n k, N ≤ k → S/(1+S) ≤ |z n k|) :
    IsLocallyFiniteMeasure (limitMeasure a) := by
  apply FleetPrefixMeasure.locallyFinite_of_prefix (ordinate a) Subtype.val Subtype.val_injective
  intro R hR
  obtain ⟨N, hN⟩ := hprefix (R+1) (by linarith)
  refine ⟨N, ?_⟩
  intro i hi
  have hb := limit_prefix_bound hc hN i hi
  have hh := (threshold_r (by linarith : 0 ≤ R+1) i.property).mp hb
  change R < |r (a i)|
  linarith

/-- Padded source traces converge to the constructed measure on every continuous compact probe. -/
theorem compact_trace_tendsto {z : ℕ → ℕ → ℝ} {a : ℕ → ℝ}
    (hc : Tendsto z atTop (𝓝 a)) (c : ℕ → ℕ)
    (hpad : ∀ n k, c n ≤ k → z n k = 1)
    (hprefix : ∀ S : ℝ, 0 ≤ S → ∃ N : ℕ, ∀ n k, N ≤ k → S/(1+S) ≤ |z n k|)
    {φ : ℝ → ℂ} (hφ : Continuous φ) (hcomp : HasCompactSupport φ) :
    Tendsto (fun n => ∑ k ∈ Finset.range (c n), extend φ (z n k)) atTop
      (𝓝 (∫ x, φ x ∂limitMeasure a)) := by
  classical
  obtain ⟨R, hR, hbound⟩ := hcomp.isBounded.exists_pos_norm_le
  have hzero : ∀ t : ℝ, R < |t| → φ t = 0 := by
    intro t ht
    by_contra hn
    have hb := hbound t (subset_tsupport φ (Function.mem_support.mpr hn))
    simp only [Real.norm_eq_abs] at hb
    linarith
  obtain ⟨N, hN⟩ := hprefix (R+1) (by linarith)
  have hthreshold : q R < (R+1)/(1+(R+1)) := by
    rw [q, abs_of_pos hR]
    apply (div_lt_div_iff₀ (by linarith : 0 < 1+R) (by linarith : 0 < 1+(R+1))).mpr
    nlinarith
  have hsource : ∀ n k, N ≤ k → extend φ (z n k) = 0 := by
    intro n k hk
    exact extend_eq_zero_of_lt hR hzero (hthreshold.trans_le (hN n k hk))
  have hlimit : ∀ k, N ≤ k → extend φ (a k) = 0 := by
    intro k hk
    exact extend_eq_zero_of_lt hR hzero (hthreshold.trans_le (limit_prefix_bound hc hN k hk))
  have heq (n : ℕ) : (∑ k ∈ Finset.range (c n), extend φ (z n k)) =
      ∑ k ∈ Finset.range N, extend φ (z n k) := by
    apply FleetCompactSlots.sum_range_eq_of_vanish
    · intro k hk
      rw [hpad n k hk, extend_one]
    · exact hsource n
  have hcompact : ∀ K : Set ℝ, IsCompact K → {i : Retained a | ordinate a i ∈ K}.Finite := by
    apply FleetPrefixMeasure.compact_preimage_finite_of_prefix (ordinate a) Subtype.val Subtype.val_injective
    intro S hS
    obtain ⟨M, hM⟩ := hprefix (S+1) (by linarith)
    refine ⟨M, ?_⟩
    intro i hi
    have hh := (threshold_r (by linarith : 0 ≤ S+1) i.property).mp (limit_prefix_bound hc hM i hi)
    change S < |r (a i)|
    linarith
  have hs := FleetPrefixMeasure.hasSum_integral (ordinate a) hcompact hφ hcomp
  have hsub : HasSum (fun i : Retained a => extend φ (a i)) (∫ x, φ x ∂limitMeasure a) := by
    have hext : (fun i : Retained a => extend φ (a i)) = (fun i => φ (ordinate a i)) := by
      funext i
      simp only [FleetRealCompactification.extend, if_pos i.property, ordinate]
    rw [hext]
    exact hs
  have hsupp : Function.support (fun k => extend φ (a k)) ⊆ {k | |a k| < 1} := by
    intro k hk
    by_contra hn
    have hn' : ¬ |a k| < 1 := hn
    have hh : extend φ (a k) = 0 := by
      simp only [FleetRealCompactification.extend, if_neg hn']
    exact hk hh
  have hfull : HasSum (fun k => extend φ (a k)) (∫ x, φ x ∂limitMeasure a) :=
    (hasSum_subtype_iff_of_support_subset hsupp).mp hsub
  have hfinite : HasSum (fun k => extend φ (a k)) (∑ k ∈ Finset.range N, extend φ (a k)) :=
    hasSum_sum_of_ne_finset_zero (fun k hk => hlimit k (Nat.le_of_not_gt (by simpa using hk)))
  have hid := hfinite.unique hfull
  simp_rw [heq]
  rw [← hid]
  exact FleetCompactSlots.finite_prefix_trace_tendsto hc (extend φ) (continuous_extend hφ hcomp) N

end FleetSlotLimit

#print axioms FleetSlotLimit.limit_locallyFinite
#print axioms FleetSlotLimit.compact_trace_tendsto
