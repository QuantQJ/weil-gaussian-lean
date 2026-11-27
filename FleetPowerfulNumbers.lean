/-
Copyright 2026 James C. Kerr (QuantQJ). Apache-2.0.
-/
import QuasiRHProved
import Kerr.NumberTheory.PowerfulNumbers

/-!
# Powerful numbers: the formal-conjectures error-term problem, unconditionally

`Kerr.PowerfulNumbers.ErrorTermImprovement` is the statement of
google-deepmind/formal-conjectures `PowerfulNumbersDensity.error_term_improvement`
(commit a425ca3e, Apache-2.0, © The Formal Conjectures Authors), copied verbatim in
`Kerr/NumberTheory/PowerfulNumbers/Reduction.lean`: there is `δ > 0` with
`Q(x) − A x^{1/2} − B x^{1/3} = O(x^{1/6−δ})`, `Q(x)` the number of powerful `n ≤ x`.

The modules under `Kerr/` are copied from QJ's kerr-lean repository (commit 99e57f1), where the
statement is proved from the hypothesis `QuasiRH (7/8)`. Here that hypothesis is discharged by
`QuasiRHWiring.quasiRH_holds` (OpenAI's Lean proof of the zero-free half-plane `Re s > 7/8`,
vendored under `OAI/`). The resulting `δ` is `(1 − 15/16)/240 = 1/3840`.
-/

namespace FleetPowerfulNumbers

/-- The zero-free half-plane `Re s > 7/8`, in kerr-lean's `QuasiRH` form. -/
theorem kerrQuasiRH : Kerr.PowerfulNumbers.QuasiRH (7 / 8) :=
  fun s hs => QuasiRHWiring.quasiRH_holds s (by exact_mod_cast hs)

/-- **formal-conjectures `PowerfulNumbersDensity.error_term_improvement`, proved.** -/
theorem errorTermImprovement : Kerr.PowerfulNumbers.ErrorTermImprovement :=
  Kerr.PowerfulNumbers.errorTermImprovement_of_quasiRH_seven_eighths_only kerrQuasiRH

/-- Mertens: `|M(x)| ≤ K x^{7/8+ε}` for `x ≥ 1`, unconditionally. -/
theorem mertens_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ K > 0, ∀ x : ℝ, 1 ≤ x →
      |∑ n ∈ Finset.Iic ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ)| ≤ K * x ^ (7 / 8 + ε) :=
  Kerr.PowerfulNumbers.mertens_bound_quasi (by norm_num) (by norm_num) kerrQuasiRH hε

end FleetPowerfulNumbers
