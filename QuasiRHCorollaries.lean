import QuasiRHProved
import FleetLandauTransfer
import FleetPsiStrip
import FleetSmoothWindowStrip
import FleetSquarefreeError
import FleetExplicitPNT

/-!
# Unconditional corollaries of the 7/8 zero-free half-plane

`QuasiRHWiring.quasiRH_holds` (OpenAI's Lean proof, vendored under `OAI/`, Apache-2.0) discharges the
`QuasiRH` hypothesis of the conditional theorems proved earlier in this repository. Each theorem below is
the corresponding `…_of_quasiRH` statement with that hypothesis removed; no new mathematics.
-/

namespace QuasiRHCorollaries

open QuasiRHWiring

/-- Sharp-cutoff window rate `33/40 + ε`, unconditionally. -/
theorem windowRate_unconditional {ε : ℝ} (hε : 0 < ε) :
    FleetHeadContour.WindowRate (33 / 40 + ε) :=
  FleetHeadContour.windowRate_of_quasiRH' quasiRH_holds hε

/-- Smooth-cutoff window rate `9/128 + ε`, unconditionally. -/
theorem smoothWindowRate_unconditional {ε : ℝ} (hε : 0 < ε) :
    FleetSmoothWindow.SmoothWindowRate (9 / 128 + ε) :=
  FleetSmoothWindow.smoothWindowRate_of_quasiRH quasiRH_holds hε

/-- The optimal smooth window rate is at most `9/128`, unconditionally. -/
theorem smoothWindowRateInf_le_unconditional : FleetSmoothWindow.smoothWindowRateInf ≤ 9 / 128 :=
  FleetSmoothWindow.smoothWindowRateInf_le_of_quasiRH quasiRH_holds

/-- `|ψ(x) − x| ≤ C x^{7/8+ε}`, unconditionally. -/
theorem psi_error_unconditional {ε : ℝ} (hε : 0 < ε) :
    ∃ C, ∀ x : ℝ, 2 ≤ x → |Chebyshev.psi x - x| ≤ C * x ^ (7 / 8 + ε) :=
  FleetPsiStrip.psi_error_of_quasiRH quasiRH_holds hε

/-- Explicit: `|ψ(x) − x| ≤ 12000 x^{7/8} log² x` for `x ≥ 1000`, unconditionally. -/
theorem psi_explicit_unconditional :
    ∀ x ≥ (1000 : ℝ), |Chebyshev.psi x - x| ≤ 12000 * x ^ (7 / 8 : ℝ) * Real.log x ^ 2 :=
  FleetExplicitPNT.psi_explicit_of_quasiRH quasiRH_holds

/-- Squarefree counting error `O(x^{8/17+ε})`, unconditionally. -/
theorem squarefreeError_unconditional :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |(FleetSquarefreeError.Q x : ℝ) - 6 * x / Real.pi ^ 2| ≤ C * x ^ (8 / 17 + ε) :=
  FleetSquarefreeError.squarefreeError_of_quasiRH quasiRH_holds

end QuasiRHCorollaries
