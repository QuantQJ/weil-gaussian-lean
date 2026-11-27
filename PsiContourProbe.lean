import ExplicitFormulaZeroSide

/-!
# Probe: does the contour identity need `IsTestFn`, or only continuity?

`ExplicitFormulaZeroSide.contour_identity_at_height` is stated for `IsTestFn a g`, but its proof
uses `h` exactly once, as `h.continuous`.  Underneath,
`PrincipalPartDischarge.vertical_lines_difference_of_G` is general in `G`, needing only
`DifferentiableOn ℂ G` on the rectangle, and
`SegmentIntegrability.segmentIntegrable_F_of_differentiableOn` likewise.

If the hypothesis really can be weakened to `Continuous g`, then kernels that are *not* test
functions become admissible — in particular `g u = exp (u/2)` with **no cutoff at all**, whose
`Gt` is the Perron-type kernel `(x^s - x^{-s})/s`, entire with no smoothing loss.  That is the
instrument the smoothed route cannot reach.
-/

set_option autoImplicit false

noncomputable section

open Complex ExplicitFormulaZeroSide
open scoped Real Interval

namespace PsiContourProbe

open TestFunctions HorizontalVanishingSeq PrincipalPartDischarge

/-- **The contour identity needs only continuity of `g`.**  Verbatim the proof of
`contour_identity_at_height` with `IsTestFn a g` replaced by `Continuous g`. -/
theorem contour_identity_of_continuous {a : ℝ} {g : ℝ → ℂ} (hg : Continuous g)
    (k : ℕ) (hk : 2 ≤ k) :
    (∫ x in (-1/2 : ℝ)..(3/2),
        deriv riemannZeta (x + ((-heights k : ℝ) : ℂ) * I)
            / riemannZeta (x + ((-heights k : ℝ) : ℂ) * I)
          * Gt a g (x + ((-heights k : ℝ) : ℂ) * I))
      - (∫ x in (-1/2 : ℝ)..(3/2),
        deriv riemannZeta (x + heights k * I) / riemannZeta (x + heights k * I)
          * Gt a g (x + heights k * I))
      + I * (∫ y in (-heights k)..(heights k),
        deriv riemannZeta (3/2 + y * I) / riemannZeta (3/2 + y * I) * Gt a g (3/2 + y * I))
      - I * (∫ y in (-heights k)..(heights k),
        deriv riemannZeta (-1/2 + y * I) / riemannZeta (-1/2 + y * I) * Gt a g (-1/2 + y * I))
    = 2 * (Real.pi : ℂ) * I * (∑ ρ ∈ zeroFinset (3/2) (heights k), (zetaOrder ρ : ℂ) * Gt a g ρ
        - Gt a g 1) := by
  have hc : (1 : ℝ) < 3/2 := by norm_num
  have hT : 0 < heights k := heights_pos k
  have hG : DifferentiableOn ℂ (Gt a g)
      ([[1 - (3/2 : ℝ), (3/2 : ℝ)]] ×ℂ [[-heights k, heights k]]) :=
    (Gt_differentiable hg).differentiableOn
  have hF := SegmentIntegrability.segmentIntegrable_F_of_differentiableOn (3/2) (heights k) hc hT
    (Gt a g) hG (boundary_nonvanishing k hk)
  have key := PrincipalPartDischarge.vertical_lines_difference_of_G (3/2) (heights k) hc hT
    (Gt a g) hG hF (zeros_interior k)
  simp only [ContourShift.F, right_pt, left_pt, bottom_pt] at key
  rw [show (1 - 3/2 : ℝ) = -1/2 by norm_num] at key
  linear_combination key

end PsiContourProbe

end

#print axioms PsiContourProbe.contour_identity_of_continuous
