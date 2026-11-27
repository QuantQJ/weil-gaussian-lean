import FleetTraceBoundRH

/-!
# RH from a growth bound on the arithmetic side

`GaussianTraceFormula.gaussian_formula_zeros` says the Gaussian zero trace has sum
`weilRHSInf (gauss b α)` = pole term − prime sum − archimedean term. Substituting into
`FleetTraceBoundRH.RH_iff_zero_trace_bound'` moves the criterion entirely to the arithmetic side:

  RH ↔ for every centre `α` there is `C'` with `‖weilRHSInf (gauss b α)‖ ≤ √(π/b) · C'`
       for all `0 < b ≤ 1`.

No zero enters the right-hand statement. An off-line zero `½ + e + iγ` makes the arithmetic side at
`α = γ` grow like `2√(π/b) · e^{e²/(4b)}`, which no `√(π/b) · C'` absorbs as `b → 0`.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter
open scoped Real
open OffLineDetection Reduction ZeroSumLimit GaussianTest

namespace FleetArithmeticBoundRH

/-- The zero trace equals the arithmetic side, for every width and centre. -/
theorem zero_trace_eq_arithmetic {b : ℝ} (hb : 0 < b) (α : ℝ) :
    ∑' x : Index, gaussHat b α (ordinate (canonical x))
      = GaussianTraceFormula.weilRHSInf (gauss b α) :=
  (GaussianTraceFormula.gaussian_formula_zeros hb α).tsum_eq

/-- **RH iff the arithmetic side is `O(b^{-1/2})` at every centre**, uniformly for `0 < b ≤ 1`. -/
theorem RH_iff_arithmetic_bound :
    RiemannHypothesis ↔ ∀ α : ℝ, ∃ C' : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      ‖GaussianTraceFormula.weilRHSInf (gauss b α)‖ ≤ Real.sqrt (π / b) * C' := by
  rw [FleetTraceBoundRH.RH_iff_zero_trace_bound']
  constructor
  · intro h α
    obtain ⟨C', hC'⟩ := h α
    exact ⟨C', fun b hb hb1 => by rw [← zero_trace_eq_arithmetic hb α]; exact hC' b hb hb1⟩
  · intro h α
    obtain ⟨C', hC'⟩ := h α
    exact ⟨C', fun b hb hb1 => by rw [zero_trace_eq_arithmetic hb α]; exact hC' b hb hb1⟩

end FleetArithmeticBoundRH
