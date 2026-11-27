import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! The paste's own model, with `Mathlib.Algebra.BigOperators.Basic` dropped
(that module no longer exists — same broken import as the first paste today). -/

set_option autoImplicit false
open Finset

def lwe_q : ℕ := 3329

noncomputable def GaussianWeight (σ x : ℝ) : ℝ := Real.exp (- (x ^ 2) / (2 * σ ^ 2))

structure DefectiveSampler where
  σ : ℝ
  B : ℝ
  σ_pos : 0 < σ
  B_nonneg : 0 ≤ B

noncomputable def SampledProbability (s : DefectiveSampler) (x : ℤ) : ℝ :=
  if |(x : ℝ)| > s.B then 0 else GaussianWeight s.σ x

noncomputable def StatisticalNoiseLeak (s : DefectiveSampler) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, |GaussianWeight s.σ i - SampledProbability s i|

/-- **The leak at index 0 is exactly zero.** With `B = 0` the guard `|0| > 0`
is false, so the sampler returns the ideal weight and the terms cancel. -/
theorem leak_at_zero_is_zero (s : DefectiveSampler) (h : s.B = 0) :
    StatisticalNoiseLeak s 1 = 0 := by
  unfold StatisticalNoiseLeak SampledProbability
  simp [h]

/-- **So the stated theorem is FALSE, not merely unproven.** `> 1/2` cannot
hold at `N = 1`; the `sorry` was hiding a refutation. -/
theorem stated_theorem_is_false (s : DefectiveSampler) (h : s.B = 0) :
    ¬ (StatisticalNoiseLeak s 1 > 1 / 2) := by
  rw [leak_at_zero_is_zero s h]; norm_num

/-- **The true statement.** The truncation first bites at `x = 1`, not `x = 0`.
With `B = 0` crushed and `σ ≥ 1`, the leak over two indices does exceed `1/2`. -/
theorem lattice_noise_tail_leak_corrected
    (s : DefectiveSampler) (h : s.B = 0) (hσ : 1 ≤ s.σ) :
    StatisticalNoiseLeak s 2 > 1 / 2 := by
  have hσ0 : (0:ℝ) < s.σ := s.σ_pos
  unfold StatisticalNoiseLeak SampledProbability
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp only [h, Nat.cast_zero, Nat.cast_one, Int.cast_zero, Int.cast_one]
  norm_num [GaussianWeight]
  -- remaining goal: 1/2 < exp (-(1 / (2 * σ^2)))
  have hsq : (1:ℝ) ≤ s.σ ^ 2 := by nlinarith
  have hle : -(1 / (2 * s.σ ^ 2)) ≥ -(1/2 : ℝ) := by
    rw [ge_iff_le, neg_le_neg_iff]
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have hhalf : (1:ℝ)/2 < Real.exp (-(1/2 : ℝ)) := by
    have := Real.add_one_lt_exp (x := (-(1/2) : ℝ)) (by norm_num)
    linarith
  calc (1:ℝ)/2 < Real.exp (-(1/2 : ℝ)) := hhalf
    _ ≤ Real.exp (-(1 / (2 * s.σ ^ 2))) := Real.exp_le_exp.mpr (by linarith [hle])
    _ = Real.exp (-1 / (2 * s.σ ^ 2)) := by rw [neg_div]

#print axioms leak_at_zero_is_zero
#print axioms stated_theorem_is_false
#print axioms lattice_noise_tail_leak_corrected
