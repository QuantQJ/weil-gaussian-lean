import FleetExponentialEnvelope
import TestFunctions
import Mathlib

noncomputable section
namespace FleetCompactExponentialBound
open FleetExponentialEnvelope Set

theorem exists_envelope {f : ℝ → ℂ} (hf : Continuous f) (hs : HasCompactSupport f) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ u, ‖f u‖ ≤ E * envelope 3 u := by
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous hf
  have hC0 : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  obtain ⟨R, hR, hbound⟩ := hs.isBounded.exists_pos_norm_le
  refine ⟨C * Real.exp (3*R), mul_nonneg hC0 (Real.exp_pos _).le, ?_⟩
  intro u
  by_cases hu : f u = 0
  · rw [hu, norm_zero]
    exact mul_nonneg (mul_nonneg hC0 (Real.exp_pos _).le) (Real.exp_pos _).le
  · have hRu := hbound u (subset_tsupport f (Function.mem_support.mpr hu))
    rw [Real.norm_eq_abs] at hRu
    have hh : 1 ≤ Real.exp (3*R-3*|u|) := Real.one_le_exp_iff.mpr (by linarith)
    calc
      ‖f u‖ ≤ C := hC u
      _ ≤ C * Real.exp (3*R-3*|u|) := le_mul_of_one_le_right hC0 hh
      _ = C * Real.exp (3*R) * envelope 3 u := by
        rw [envelope, show -3 * |u| = -(3*|u|) by ring, Real.exp_sub, Real.exp_neg]
        ring

theorem exists_common_envelope {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g)
    (hs : HasCompactSupport g) : ∃ E : ℝ, 0 ≤ E ∧
      (∀ u, ‖g u‖ ≤ E * envelope 3 u) ∧
      (∀ u, ‖deriv g u‖ ≤ E * envelope 3 u) ∧
      (∀ u, ‖deriv (deriv g) u‖ ≤ E * envelope 3 u) := by
  have hc1 : ContDiff ℝ 1 (deriv g) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1+1) g from hg)).2.2
  have hc2 : Continuous (deriv (deriv g)) :=
    ((contDiff_succ_iff_deriv.mp (show ContDiff ℝ (0+1) (deriv g) from hc1)).2.2).continuous
  obtain ⟨E0, hE0, h0⟩ := exists_envelope hg.continuous hs
  obtain ⟨E1, hE1, h1⟩ := exists_envelope hc1.continuous hs.deriv
  obtain ⟨E2, hE2, h2⟩ := exists_envelope hc2 hs.deriv.deriv
  refine ⟨E0+E1+E2, by positivity, ?_, ?_, ?_⟩
  · intro u
    exact (h0 u).trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)
  · intro u
    exact (h1 u).trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)
  · intro u
    exact (h2 u).trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)

theorem testFn_exists_common_envelope {a : ℝ} {g : ℝ → ℂ}
    (hg : TestFunctions.IsTestFn a g) (hs : ∀ u, a < |u| → g u = 0) :
    ∃ E : ℝ, 0 ≤ E ∧ (∀ u, ‖g u‖ ≤ E * envelope 3 u) ∧
      (∀ u, ‖deriv g u‖ ≤ E * envelope 3 u) ∧
      (∀ u, ‖deriv (deriv g) u‖ ≤ E * envelope 3 u) := by
  apply exists_common_envelope hg.smooth
  apply IsCompact.of_isClosed_subset (isCompact_Icc : IsCompact (Icc (-a) a)) (isClosed_tsupport g)
  apply closure_minimal _ isClosed_Icc
  intro u hu
  have hn : g u ≠ 0 := hu
  have hb : |u| ≤ a := le_of_not_gt (fun h => hn (hs u h))
  exact abs_le.mp hb

end FleetCompactExponentialBound
#print axioms FleetCompactExponentialBound.testFn_exists_common_envelope
