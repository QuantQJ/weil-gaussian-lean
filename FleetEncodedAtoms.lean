import FleetOrderedAtoms
import FleetRealCompactification

noncomputable section
open Set

namespace FleetEncodedAtoms
open FleetRealCompactification

/-- Missing slots encode an endpoint, not an extra real atom. -/
def encode {N : ℕ} (x : Fin N → ℝ) (e : Fin N ≃ Fin N) (k : ℕ) : ℝ :=
  if h : k < N then q (x (e ⟨k, h⟩)) else 1

theorem encode_mem {N : ℕ} (x : Fin N → ℝ) (e : Fin N ≃ Fin N) (k : ℕ) :
    encode x e k ∈ Icc (-1 : ℝ) 1 := by
  unfold encode
  split_ifs with h
  · exact ⟨(q_mem_Ioo _).1.le, (q_mem_Ioo _).2.le⟩
  · constructor <;> norm_num

theorem encode_pad {N : ℕ} (x : Fin N → ℝ) (e : Fin N ≃ Fin N)
    (k : ℕ) (hk : N ≤ k) : encode x e k = 1 := by
  simp only [encode, dif_neg (Nat.not_lt.mpr hk)]

/-- Weighted boundedness supplies a uniform encoded prefix at each radius. -/
theorem encode_prefix {N : ℕ} (x : Fin N → ℝ) (e : Fin N ≃ Fin N)
    (he : Monotone (fun i => |x (e i)|)) {R M : ℝ}
    (hR : 0 ≤ R) (hm : (∑ i, (1+(x i)^2)⁻¹) ≤ M)
    (k : ℕ) (hk : ⌈M*(1+R^2)⌉₊ ≤ k) :
    R/(1+R) ≤ |encode x e k| := by
  unfold encode
  split_ifs with h
  · apply (threshold_q hR _).mpr
    exact (FleetOrderedAtoms.radius_lt_of_rank_ge x e he ⟨k, h⟩ hR hm hk).le
  · rw [abs_one, div_le_one (by positivity : 0 < 1+R)]
    linarith

/-- Encoding, ordering and padding do not change the finite trace. -/
theorem trace_encode {N : ℕ} (x : Fin N → ℝ) (e : Fin N ≃ Fin N) (φ : ℝ → ℂ) :
    (∑ k ∈ Finset.range N, extend φ (encode x e k)) = ∑ i, φ (x i) := by
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    (∑ i : Fin N, extend φ (encode x e i.val)) = ∑ i : Fin N, φ (x (e i)) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [encode, dif_pos i.isLt, extend_q]
    _ = _ := FleetOrderedAtoms.sum_ordered x e φ

end FleetEncodedAtoms
