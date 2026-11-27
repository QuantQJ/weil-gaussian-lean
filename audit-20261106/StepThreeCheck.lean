import StripWidthDependency

set_option autoImplicit false
noncomputable section
open Complex
open scoped Real

namespace StepThreeCheck

open Reduction ZeroSumLimit GaussianTest OffLineDetection StripWidthDependency

/-- RH, in the strip-width language, is half-width exactly zero. -/
def OrdinatesReal : Prop := ∀ x : Index, (t x).im = 0

/-- **The gap step 3 asserts away.** A half-width of `2/5` does not force the
ordinate to vanish: `|r| < 2/5` is satisfied by nonzero reals. -/
theorem width_two_fifths_does_not_pin_the_line :
    ¬ ∀ r : ℝ, |r| < 2 / 5 → r = 0 := by
  intro h
  have h5 : |(1 : ℝ) / 5| < 2 / 5 := by rw [abs_lt]; norm_num
  have := h (1 / 5) h5
  norm_num at this

/-- The direction the repo actually has: RH gives every positive half-width.
Step 3 needs the converse, which is nowhere proved. -/
theorem available_direction {δ : ℝ} (hδ : 0 < δ) (h : OrdinatesReal) :
    StripHalfWidth δ := by
  intro x
  rw [h x, abs_zero]
  exact hδ

end StepThreeCheck

#print axioms StepThreeCheck.width_two_fifths_does_not_pin_the_line
#print axioms StepThreeCheck.available_direction
