import QuasiRHWiring
import OAI.NumberTheory.DirichletL.Nonvanishing

/-!
# The quasi-RH half-plane, proved

`QuasiRHWiring.QuasiRH` (`riemannZeta s ≠ 0` whenever `7/8 < Re s`) was carried as an explicit
hypothesis. It is discharged here by OpenAI's Lean proof
`OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` (https://github.com/openai/math, commit
4eaee87548250b2682affda7d05d947c05554bae, `lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean`,
Apache-2.0, Copyright (c) OpenAI), whose import closure is vendored under `OAI/` (see NOTICE).
-/

set_option autoImplicit false
noncomputable section

namespace QuasiRHWiring

open Reduction ZetaStrip OffLineDetection StripWidthDependency ZeroSymmetry

/-- `QuasiRH` holds: OpenAI's theorem `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`. -/
theorem quasiRH_holds : QuasiRH :=
  fun _ hs => OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re hs

/-- Every nontrivial zero satisfies `|1/2 - Re ρ| ≤ 3/8`, unconditionally. -/
theorem abs_half_sub_re_le' {ρ : ℂ} (hρ : IsNontrivialZero ρ) : |1 / 2 - ρ.re| ≤ 3 / 8 :=
  abs_half_sub_re_le quasiRH_holds hρ

/-- The strip half-width `2/5`, unconditionally. -/
theorem stripHalfWidth_two_fifths' : StripHalfWidth (2 / 5) :=
  stripHalfWidth_two_fifths quasiRH_holds

end QuasiRHWiring
