import FleetFiniteIntervalCertificate

/-!
# Side-wise enclosures compose into a residual box

`FleetFiniteIntervalCertificate.residual b x q` is `probeSum − rhs`.  Its enclosure cannot be
obtained by bounding the two sides separately and adding — the residual is small precisely
because the two sides nearly cancel, so a triangle bound returns roughly twice their common
size instead of the difference.

What does work is interval subtraction: enclose each side in a rectangle, then subtract the
rectangles.  This module supplies that step, which is the piece between a numeric certificate
(which naturally produces a box per side) and
`FleetFiniteIntervalCertificate.feasible_of_scalar_enclosures` (which wants a norm bound on the
residual).

Nothing analytic is proved here. The two side enclosures remain obligations.
-/

noncomputable section
open Complex

namespace FleetSideEnclosures

/-! ## Interval subtraction for complex rectangles -/

/-- **Interval subtraction.** Rectangles for `P` and `R` give a rectangle for `P - R`. -/
theorem sub_box {P R : ℂ} {pLoRe pHiRe pLoIm pHiIm rLoRe rHiRe rLoIm rHiIm : ℝ}
    (hpr : pLoRe ≤ P.re) (hpR : P.re ≤ pHiRe)
    (hpi : pLoIm ≤ P.im) (hpI : P.im ≤ pHiIm)
    (hrr : rLoRe ≤ R.re) (hrR : R.re ≤ rHiRe)
    (hri : rLoIm ≤ R.im) (hrI : R.im ≤ rHiIm) :
    ((pLoRe - rHiRe) ≤ (P - R).re ∧ (P - R).re ≤ (pHiRe - rLoRe)) ∧
    ((pLoIm - rHiIm) ≤ (P - R).im ∧ (P - R).im ≤ (pHiIm - rLoIm)) := by
  simp only [Complex.sub_re, Complex.sub_im]
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- The resulting conservative norm bound on the difference. -/
theorem norm_sub_le_of_sides {P R : ℂ} {pLoRe pHiRe pLoIm pHiIm rLoRe rHiRe rLoIm rHiIm : ℝ}
    (hpr : pLoRe ≤ P.re) (hpR : P.re ≤ pHiRe)
    (hpi : pLoIm ≤ P.im) (hpI : P.im ≤ pHiIm)
    (hrr : rLoRe ≤ R.re) (hrR : R.re ≤ rHiRe)
    (hri : rLoIm ≤ R.im) (hrI : R.im ≤ rHiIm) :
    ‖P - R‖ ≤ max |pLoRe - rHiRe| |pHiRe - rLoRe|
             + max |pLoIm - rHiIm| |pHiIm - rLoIm| :=
  FleetFiniteIntervalCertificate.norm_le_box
    (sub_box hpr hpR hpi hpI hrr hrR hri hrI).1
    (sub_box hpr hpR hpi hpI hrr hrR hri hrI).2

/-! ## Specialised to the bank residual -/

open GaussianTest

/-- **The residual norm from a probe-side box and an arithmetic-side box.**  This is exactly
the shape a numeric certificate produces: one rectangle for the probe sum
`∑ h (gauss b q) (xᵢ)`, one for the arithmetic target `rhs (gauss b q)`. -/
theorem residual_norm_le_of_sides {N : ℕ} {b : ℝ} {x : Fin N → ℝ} {q : ℚ}
    {pLoRe pHiRe pLoIm pHiIm rLoRe rHiRe rLoIm rHiIm : ℝ}
    (hpr : pLoRe ≤ (∑ i : Fin N, FleetFullLineFourier.h (gauss b (q : ℝ)) (x i)).re)
    (hpR : (∑ i : Fin N, FleetFullLineFourier.h (gauss b (q : ℝ)) (x i)).re ≤ pHiRe)
    (hpi : pLoIm ≤ (∑ i : Fin N, FleetFullLineFourier.h (gauss b (q : ℝ)) (x i)).im)
    (hpI : (∑ i : Fin N, FleetFullLineFourier.h (gauss b (q : ℝ)) (x i)).im ≤ pHiIm)
    (hrr : rLoRe ≤ (FleetFullLineArithmetic.rhs (gauss b (q : ℝ))).re)
    (hrR : (FleetFullLineArithmetic.rhs (gauss b (q : ℝ))).re ≤ rHiRe)
    (hri : rLoIm ≤ (FleetFullLineArithmetic.rhs (gauss b (q : ℝ))).im)
    (hrI : (FleetFullLineArithmetic.rhs (gauss b (q : ℝ))).im ≤ rHiIm) :
    ‖FleetFiniteIntervalCertificate.residual b x q‖
      ≤ max |pLoRe - rHiRe| |pHiRe - rLoRe|
      + max |pLoIm - rHiIm| |pHiIm - rLoIm| := by
  unfold FleetFiniteIntervalCertificate.residual
  exact norm_sub_le_of_sides hpr hpR hpi hpI hrr hrR hri hrI

end FleetSideEnclosures

end

#print axioms FleetSideEnclosures.sub_box
#print axioms FleetSideEnclosures.norm_sub_le_of_sides
#print axioms FleetSideEnclosures.residual_norm_le_of_sides
