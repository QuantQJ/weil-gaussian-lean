import SpectralFluctuation
import SierraXp
import XpSpectrum
import Mathlib

/-!
# The fluctuation barrier (and why crossing it is not the prize)

`SpectralFluctuation` proves: every Bohr–Sommerfeld spectrum for a *monotone*
quantization `A` has `|S(E)| ≤ 1`. The zeta ordinates are believed to have
unbounded `S(T)` (Littlewood/Selberg — cited as hypothesis, not proven here),
so they are not a BS spectrum of any monotone `A`. That obstruction is real.

`CrossesFluctuationBarrier` names the complementary property: RVM fluctuation
unbounded. **That property is not prize-relevant.** See
`CascadeCounterexample`: the exponential stack `λ_n = eⁿ` is self-adjoint
layerwise and crosses the barrier for every offset `c`. Crossing is cheap.
Wildness is not the criterion.

What would single out the zeros is the **specific** fluctuation `S(T)` from
the explicit formula (prime sum) — arithmetic, not mere unboundedness. See
`ExplicitFormula` for the machine-checked arithmetic half.

No `sorry`, no custom axioms. The old “Clay target / prize side” language in
this module is **retired** after the cascade counterexample.
-/

noncomputable section
open SpectralFluctuation

namespace FluctuationCapable

/-- Fluctuation against the Berry–Keating / RVM smooth term. -/
def rvmFluct (c : ℝ) (lam : ℕ → ℝ) (E : ℝ) : ℝ :=
  fluct XpSpectrum.A c lam E

/-- RVM fluctuation unbounded on `[lam 0, ∞)`.
A *negative* filter (rules out monotone BS), not a prize goal.
Inhabited by `CascadeCounterexample.cascade` (see that module). -/
def CrossesFluctuationBarrier (c : ℝ) (lam : ℕ → ℝ) : Prop :=
  ∀ K : ℝ, ∃ E ≥ lam 0, K < |rvmFluct c lam E|

/-- Crossing ⇒ not Bohr–Sommerfeld for `(XpSpectrum.A, c)`. -/
theorem crosses_not_bohrSommerfeld {c : ℝ} {lam : ℕ → ℝ}
    (hcross : CrossesFluctuationBarrier c lam)
    (B : BohrSommerfeld XpSpectrum.A c)
    (hlim : Filter.Tendsto B.lam Filter.atTop Filter.atTop) :
    B.lam ≠ lam :=
  not_bohrSommerfeld_of_unbounded_fluct (A := XpSpectrum.A) (c := c)
    (γ := lam) hcross B hlim

/-- Same exclusion, named without prize language. -/
theorem crosses_excludes_bohrSommerfeld {c : ℝ} {lam : ℕ → ℝ}
    (h : CrossesFluctuationBarrier c lam) :
    ∀ (B : BohrSommerfeld XpSpectrum.A c)
      (hlim : Filter.Tendsto B.lam Filter.atTop Filter.atTop), B.lam ≠ lam :=
  crosses_not_bohrSommerfeld h

/-- Sierra smooth-density candidate: smooth / barrier side only. -/
theorem sierra_smooth_is_barrier_side :
    SierraXp.SmoothDensityCandidate fun E => Real.log E :=
  SierraXp.log_is_smooth_density_candidate

/-- Retired marker. Formerly suggested “inhabit this for Clay.”
Crossing is cheap (`CascadeCounterexample.barrier_crossing_is_cheap`).
Arithmetic `S(T)` is the criterion; this structure stays uninhabited. -/
structure ClayFluctuationOperator where
  retired_crossing_is_not_the_prize : False  -- audit:allow-false-field (deliberately uninhabited: names the open problem)

def ClayFluctuationOperatorProgress : Prop :=
  Nonempty ClayFluctuationOperator

theorem clay_package_retired_uninhabited :
    ClayFluctuationOperatorProgress ↔ False := by
  constructor
  · rintro ⟨⟨h⟩⟩; exact h
  · exact False.elim

end FluctuationCapable
