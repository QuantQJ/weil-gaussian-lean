import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace PhiSpectral

/-!
# Entropy Barrier Lock Dynamics

This module formalizes the core mechanism observed in the phi-spectral
training runs:

`E_{n+1} = min(B, E_n + gain_n)`

where `B` is the entropy barrier (`B = 6 * φ^4` in experiments) and
`gain_n ≥ 0` is the net upward drive from optimization at step `n`.

Theorems proved here:
1. The barrier is never exceeded.
2. Energy is monotone non-decreasing below the barrier.
3. The barrier is an absorbing state: once reached, it stays locked.
-/

/-- One clipped energy step with hard barrier `B`. -/
def clippedStep (B gain E : ℝ) : ℝ :=
  min B (E + gain)

/-- A clipped step can never exceed the barrier. -/
theorem clippedStep_le_barrier (B gain E : ℝ) :
    clippedStep B gain E ≤ B := by
  simp [clippedStep]

/-- If the unconstrained step crosses the barrier, clipping lands exactly at `B`. -/
theorem clippedStep_eq_barrier_of_crossed (B gain E : ℝ)
    (hCross : B ≤ E + gain) :
    clippedStep B gain E = B := by
  simp [clippedStep, min_eq_left hCross]

/-- With nonnegative gain and `E ≤ B`, the clipped step is at least the current energy. -/
theorem clippedStep_ge_current_of_nonneg_gain (B gain E : ℝ)
    (hEB : E ≤ B) (hGain : 0 ≤ gain) :
    E ≤ clippedStep B gain E := by
  have hEG : E ≤ E + gain := by linarith
  exact le_min hEB hEG

/-- If the current energy is exactly the barrier, one more clipped step keeps it at the barrier. -/
theorem clippedStep_absorbing (B gain : ℝ) (hGain : 0 ≤ gain) :
    clippedStep B gain B = B := by
  apply clippedStep_eq_barrier_of_crossed
  linarith

/-- Energy trajectory under clipped dynamics. -/
def energyTrajectory (B E₀ : ℝ) (gain : ℕ → ℝ) : ℕ → ℝ
  | 0 => E₀
  | n + 1 => clippedStep B (gain n) (energyTrajectory B E₀ gain n)

/-- If initialized below the barrier, the trajectory stays below the barrier forever. -/
theorem trajectory_le_barrier (B E₀ : ℝ) (gain : ℕ → ℝ)
    (hE₀ : E₀ ≤ B) :
    ∀ n, energyTrajectory B E₀ gain n ≤ B := by
  intro n
  induction n with
  | zero =>
      simpa [energyTrajectory] using hE₀
  | succ n ih =>
      simpa [energyTrajectory] using
        clippedStep_le_barrier B (gain n) (energyTrajectory B E₀ gain n)

/-- With nonnegative gain, the clipped trajectory is monotone non-decreasing. -/
theorem trajectory_monotone (B E₀ : ℝ) (gain : ℕ → ℝ)
    (hE₀ : E₀ ≤ B) (hGain : ∀ n, 0 ≤ gain n) :
    ∀ n, energyTrajectory B E₀ gain n ≤ energyTrajectory B E₀ gain (n + 1) := by
  intro n
  have hBound : energyTrajectory B E₀ gain n ≤ B := trajectory_le_barrier B E₀ gain hE₀ n
  have hGainN : 0 ≤ gain n := hGain n
  simpa [energyTrajectory] using
    clippedStep_ge_current_of_nonneg_gain B (gain n) (energyTrajectory B E₀ gain n) hBound hGainN

/-- Once a trajectory step hits the barrier, the next step remains locked at the barrier. -/
theorem trajectory_lock_after_hit (B E₀ : ℝ) (gain : ℕ → ℝ)
    (hGain : ∀ n, 0 ≤ gain n) :
    ∀ n, energyTrajectory B E₀ gain n = B →
      energyTrajectory B E₀ gain (n + 1) = B := by
  intro n hHit
  calc
    energyTrajectory B E₀ gain (n + 1)
        = clippedStep B (gain n) (energyTrajectory B E₀ gain n) := by
            simp [energyTrajectory]
    _ = clippedStep B (gain n) B := by simp [hHit]
    _ = B := clippedStep_absorbing B (gain n) (hGain n)

/--
Optimizer bridge gain for a one-step pull toward the barrier:
`gain = η * (B - E)`.
-/
def bridgeGain (η B E : ℝ) : ℝ :=
  η * (B - E)

/-- Under `η ≥ 0` and `E ≤ B`, the optimizer bridge gain is nonnegative. -/
theorem bridgeGain_nonneg (η B E : ℝ)
    (hη : 0 ≤ η) (hEB : E ≤ B) :
    0 ≤ bridgeGain η B E := by
  have hGap : 0 ≤ B - E := by linarith
  exact mul_nonneg hη hGap

/--
With `0 ≤ η ≤ 1` and `E ≤ B`, the affine optimizer step remains below the barrier.
-/
theorem bridge_step_le_barrier (η B E : ℝ)
    (hη1 : η ≤ 1) (hEB : E ≤ B) :
    E + bridgeGain η B E ≤ B := by
  have hGap : 0 ≤ B - E := by linarith
  have hScale' : η * (B - E) ≤ 1 * (B - E) := by
    exact mul_le_mul_of_nonneg_right hη1 hGap
  have hScale : η * (B - E) ≤ B - E := by simpa using hScale'
  have hStep : E + η * (B - E) ≤ E + (B - E) := add_le_add_left hScale E
  have hEq : E + (B - E) = B := by linarith
  have hMain : E + η * (B - E) ≤ B := by linarith [hStep, hEq]
  simpa [bridgeGain] using hMain

/--
Optimizer-to-dynamics bridge:
if the gain is `η*(B-E)` with `0 ≤ η ≤ 1` and `E ≤ B`, clipped dynamics equals
the affine update and thus induces nonnegative gain toward `B`.
-/
theorem clippedStep_eq_optimizer_bridge (η B E : ℝ)
    (hη1 : η ≤ 1) (hEB : E ≤ B) :
    clippedStep B (bridgeGain η B E) E = E + bridgeGain η B E := by
  have hLe : E + bridgeGain η B E ≤ B := by
    simpa [bridgeGain] using bridge_step_le_barrier η B E hη1 hEB
  simp [clippedStep, min_eq_right hLe]

end PhiSpectral

