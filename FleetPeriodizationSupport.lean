import Mathlib

noncomputable section
namespace FleetPeriodizationSupport
open Set Filter Topology

lemma unique_shift {F : ℝ → ℂ} {R P u : ℝ} (hR : 0 ≤ R) (hP : 2*R < P)
    (hs : ∀ x, R < |x| → F x = 0) {j k : ℤ}
    (hj : F (u+j*P) ≠ 0) (hk : F (u+k*P) ≠ 0) : j = k := by
  have bj : |u+(j:ℝ)*P| ≤ R := le_of_not_gt (fun h => hj (hs _ h))
  have bk : |u+(k:ℝ)*P| ≤ R := le_of_not_gt (fun h => hk (hs _ h))
  rw [abs_le] at bj bk
  by_contra hn
  rcases lt_or_gt_of_ne hn with h | h
  · have hi : (j:ℝ)+1 ≤ k := by exact_mod_cast h
    nlinarith
  · have hi : (k:ℝ)+1 ≤ j := by exact_mod_cast h
    nlinarith

lemma locallyFinite_shifts {F : ℝ → ℂ} {R P : ℝ} (hP : 0 < P)
    (hs : ∀ x, R < |x| → F x = 0) :
    LocallyFinite (fun k : ℤ => Function.support (fun u : ℝ => F (u+k*P))) := by
  intro u
  obtain ⟨N, hN⟩ := exists_nat_gt ((|u|+1+|R|)/P)
  refine ⟨Metric.ball u 1, Metric.ball_mem_nhds u (by norm_num), ?_⟩
  apply (Set.finite_Icc (-(N:ℤ)) (N:ℤ)).subset
  intro k hk
  obtain ⟨x, hx, hxu⟩ := hk
  have hn : F (x+(k:ℝ)*P) ≠ 0 := hx
  have hb : |x+(k:ℝ)*P| ≤ R := le_of_not_gt (fun h => hn (hs _ h))
  have hd : |x-u| < 1 := by simpa [Real.dist_eq] using hxu
  have hsum : |x| ≤ |x-u|+|u| := by simpa using abs_add_le (x-u) u
  have hmul : |(k:ℝ)*P| ≤ |x+(k:ℝ)*P|+|x| := by
    simpa using abs_sub (x+(k:ℝ)*P) x
  rw [abs_mul, abs_of_pos hP] at hmul
  have hn' : |u|+1+|R| < (N:ℝ)*P := (div_lt_iff₀ hP).mp hN
  have hk' : |(k:ℝ)| < N := by nlinarith [le_abs_self R]
  have hi := abs_lt.mp hk'
  constructor
  · exact_mod_cast hi.1.le
  · exact_mod_cast hi.2.le

lemma central_zero {F : ℝ → ℂ} {R P u : ℝ} (hR : 0 ≤ R)
    (hs : ∀ x, R < |x| → F x = 0) (hu : |u| < P-R) {k : ℤ} (hk : k ≠ 0) :
    F (u+k*P) = 0 := by
  apply hs
  have hP : 0 < P := by linarith [abs_nonneg u]
  have hk' : 1 ≤ |(k:ℝ)| := by exact_mod_cast Int.one_le_abs hk
  have hh : |(k:ℝ)*P| ≤ |u+(k:ℝ)*P|+|u| := by
    simpa using abs_sub (u+(k:ℝ)*P) u
  rw [abs_mul, abs_of_pos hP] at hh
  nlinarith

lemma central_tsum_eq {F : ℝ → ℂ} {R P u : ℝ} (hR : 0 ≤ R)
    (hs : ∀ x, R < |x| → F x = 0) (hu : |u| < P-R) :
    (∑' k : ℤ, F (u+k*P)) = F u := by
  rw [tsum_eq_single 0 (fun k hk => central_zero hR hs hu hk)]
  simp

lemma norm_tsum_le {F : ℝ → ℂ} {R P C u : ℝ} (hR : 0 ≤ R) (hP : 2*R < P)
    (hs : ∀ x, R < |x| → F x = 0) (hC : 0 ≤ C) (hb : ∀ x, ‖F x‖ ≤ C) :
    ‖∑' k : ℤ, F (u+k*P)‖ ≤ C := by
  classical
  by_cases hn : ∃ k : ℤ, F (u+k*P) ≠ 0
  · obtain ⟨k,hk⟩ := hn
    rw [tsum_eq_single k]
    · exact hb _
    · intro j hj
      by_contra hh
      exact hj (unique_shift hR hP hs hh hk)
  · have hz : ∀ k : ℤ, F (u+k*P) = 0 := by simpa using hn
    simp only [hz, tsum_zero, norm_zero]
    exact hC

end FleetPeriodizationSupport
#print axioms FleetPeriodizationSupport.unique_shift
#print axioms FleetPeriodizationSupport.locallyFinite_shifts
#print axioms FleetPeriodizationSupport.central_tsum_eq
#print axioms FleetPeriodizationSupport.norm_tsum_le
