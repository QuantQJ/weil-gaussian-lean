import LogDerivSegmentBound
import ZetaGrowthEM3
import ZeroAvoidingHeights
import Mathlib

/-!
# The horizontal-segment bound for `ζ'/ζ`, unconditional

`LogDerivSegmentBound.norm_logDeriv_zeta_le_on_full_segment_of_growth` bounds
`‖ζ'/ζ(σ + iT)‖` on the whole contour segment `-1/2 ≤ σ ≤ 3/2` at heights `T`
that stay a distance `δ` from every zero ordinate, **given** polynomial growth
of `ζ` on `-5/2 ≤ Re s ≤ 2`. `ZetaGrowthEM3.zeta_growth_left_rpow` proves that
growth with `C₃ = 12`, `A = 4`. This module instantiates it, and evaluates the
bound along the zero-avoiding heights of `ZeroAvoidingHeights.exists_seq_heights`.

Everything here is unconditional: it depends only on Mathlib and the
project's own standard-axiom theorems. No `sorry`, no custom axioms.
-/

noncomputable section
open Reduction Complex

namespace SegmentBoundUnconditional

/-- The constant `Λ₀ := log(3 + 12·2⁴) + 4 + 3` of the segment bound at `C₃ = 12`, `A = 4`. -/
def Λ₀ : ℝ := Real.log (3 + 12 * (2:ℝ) ^ (4:ℝ)) + 4 + 3

/-- **Segment bound, unconditional.** For `|T| ≥ 6` at distance `≥ δ > 0` from
every zero ordinate, and every `σ ∈ [-1/2, 3/2]`,
`‖ζ'/ζ(σ + iT)‖ ≤ 623 Λ₀ log|T| + 2 Λ₀ log|T| / δ`. -/
theorem norm_logDeriv_zeta_le_on_full_segment (T : ℝ) (hT : 6 ≤ |T|) (δ : ℝ) (hδpos : 0 < δ)
    (hδ : ∀ ρ, IsNontrivialZero ρ → δ ≤ |ρ.im - T|) :
    ∀ σ ∈ Set.Icc (-1/2 : ℝ) (3/2),
      ‖deriv riemannZeta (σ + T * I) / riemannZeta (σ + T * I)‖
        ≤ 623 * Λ₀ * Real.log |T| + 2 * Λ₀ * Real.log |T| / δ :=
  LogDerivSegmentBound.norm_logDeriv_zeta_le_on_full_segment_of_growth
    (C₃ := 12) (A := 4) (by norm_num) (by norm_num)
    (fun s h₁ h₂ ht => ZetaGrowthEM3.zeta_growth_left_rpow h₁ h₂ ht) T hT δ hδpos hδ

/-- **Along zero-avoiding heights.** There is a sequence of heights
`T k ∈ [4 + k, 5 + k]` such that for every `k ≥ 2` and `σ ∈ [-1/2, 3/2]`,
`‖ζ'/ζ(σ + i T k)‖ ≤ 623 Λ₀ log (T k) + 2 Λ₀ log (T k) / δ(4 + k)`, with
`δ` the explicit gap of `ZeroAvoidingHeights` (of order `1 / log k`). -/
theorem exists_heights_with_segment_bound :
    ∃ T : ℕ → ℝ, (∀ k : ℕ, 4 + (k : ℝ) ≤ T k ∧ T k ≤ 5 + (k : ℝ)) ∧
      ∀ k : ℕ, 2 ≤ k → ∀ σ ∈ Set.Icc (-1/2 : ℝ) (3/2),
        ‖deriv riemannZeta (σ + T k * I) / riemannZeta (σ + T k * I)‖
          ≤ 623 * Λ₀ * Real.log (T k)
            + 2 * Λ₀ * Real.log (T k) / ZeroAvoidingHeights.δ (4 + (k : ℝ)) := by
  obtain ⟨T, hT, hgap⟩ := ZeroAvoidingHeights.exists_seq_heights
  refine ⟨T, hT, fun k hk σ hσ => ?_⟩
  have hTk : 6 ≤ |T k| := by
    have h1 := (hT k).1
    have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
    rw [abs_of_pos (by linarith)]
    linarith
  have hδpos : 0 < ZeroAvoidingHeights.δ (4 + (k : ℝ)) := by
    unfold ZeroAvoidingHeights.δ
    have hK := ZeroDensity.K_nonneg (C := 7) (by norm_num)
    have hlog : 0 ≤ Real.log (4 + (k : ℝ) + 1) := Real.log_nonneg (by linarith)
    have hprod : 0 ≤ 8 * ZeroDensity.K 7 * Real.log (4 + (k : ℝ) + 1) :=
      mul_nonneg (mul_nonneg (by norm_num) hK) hlog
    exact one_div_pos.mpr (by linarith)
  have := norm_logDeriv_zeta_le_on_full_segment (T k) hTk _ hδpos (fun ρ hρ => hgap k ρ hρ) σ hσ
  have habs : |T k| = T k := abs_of_pos (by linarith [(hT k).1])
  rwa [habs] at this

end SegmentBoundUnconditional

end
