import ZeroDensity
import ZetaGrowthNeg
import ZetaLowerBound
import Mathlib

/-!
# Zero density, unconditional

`ZeroDensity` proves the Riemann–von Mangoldt-type bound `N(T) = O(T log T)`
and the local bound "≤ K log T zeros within height 1 of T" from Jensen's
formula, taking two analytic inputs as named hypotheses:

* `hgrowth`: `‖ζ s‖ ≤ C |Im s|^{3/2}` on `-1/2 ≤ Re s ≤ 2`, `|Im s| ≥ 2`;
* `hlow`: `1/3 ≤ ‖ζ(3/2 + it)‖`.

Both were proven in the same fleet, in `ZetaGrowthNeg` (with `C = 7`, via the
second-order Euler–Maclaurin continuation to `Re s > -1`) and `ZetaLowerBound`
(via the Euler product). This module instantiates them, so every zero-density
statement below is **unconditional**: it depends only on Mathlib and the
project's own standard-axiom theorems.

No `sorry`, no custom axioms.
-/

noncomputable section
open Reduction

namespace ZeroDensityUnconditional

/-- The growth input, discharged with `C = 7`. -/
theorem hgrowth : ∀ s : ℂ, -1/2 ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| →
    ‖riemannZeta s‖ ≤ 7 * |s.im| ^ (3/2 : ℝ) :=
  fun _ h₁ h₂ ht => ZetaGrowthNeg.zeta_growth_wide_bound h₁ h₂ ht

/-- The lower-bound input, discharged. -/
theorem hlow : ∀ t : ℝ, 1/3 ≤ ‖riemannZeta (3/2 + t * Complex.I)‖ :=
  ZetaLowerBound.norm_zeta_three_halves_ge

/-- **Local zero density**: for `|T| ≥ 4`, the number of nontrivial zeros with
`|Im ρ − T| ≤ 1` is at most `2 K(7) log |T|`. Unconditional. -/
theorem ncard_zeros_near_height_le (T : ℝ) (hT : 4 ≤ |T|) :
    ({ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im - T| ≤ 1}.ncard : ℝ)
      ≤ 2 * ZeroDensity.K 7 * Real.log |T| :=
  ZeroDensity.ncard_zeros_near_height_le 7 (by norm_num) hgrowth hlow T hT

/-- **Riemann–von Mangoldt-type bound**: `N(T) ≤ C' · T · log T` for `T ≥ 2`.
Unconditional. -/
theorem count_le_T_log_T :
    ∃ C' : ℝ, ∀ T : ℝ, 2 ≤ T →
      ({ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im| ≤ T}.ncard : ℝ) ≤ C' * T * Real.log T :=
  ZeroDensity.count_le_T_log_T 7 (by norm_num) hgrowth hlow

/-- **`Σ 1/γ² < ∞`** along any injective enumeration of nontrivial zeros with
`|Im| ≥ 2` listed by non-decreasing `|Im|`. Unconditional. -/
theorem summable_inv_sq_ordinates
    (zeros : ℕ → ℂ) (hinj : Function.Injective zeros) (hz : ∀ n, IsNontrivialZero (zeros n))
    (hγ : ∀ n, 2 ≤ |(zeros n).im|) (hmono : Monotone (fun n => |(zeros n).im|)) :
    Summable (fun n => 1 / ((zeros n).im) ^ 2) :=
  ZeroDensity.summable_inv_sq_ordinates 7 (by norm_num) hgrowth hlow zeros hinj hz hγ hmono

/-- The hypotheses of `ZeroSumConvergence` hold for the actual zeros: finite
level sets and the `T log T` counting bound. Unconditional. -/
theorem zeroSumConvergence_hypotheses
    (zeros : ℕ → ℂ) (hinj : Function.Injective zeros) (hz : ∀ n, IsNontrivialZero (zeros n)) :
    (∀ T, {n : ℕ | |(zeros n).im| ≤ T}.Finite) ∧
    ∃ C' : ℝ, ∀ T ≥ (2 : ℝ),
      (ZeroSumConvergence.count (fun n => (zeros n).im) T : ℝ) ≤ C' * T * Real.log T :=
  ZeroDensity.zeroSumConvergence_hypotheses 7 (by norm_num) hgrowth hlow zeros hinj hz

end ZeroDensityUnconditional

end
