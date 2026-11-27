/-
Portions of this file are copied from google-deepmind/formal-conjectures,
file `FormalConjectures/Paper/RiemannHypothesisEquivalents.lean`, at commit
a425ca3eb797fe927cb88c950565fdcbbbbada70 (file last changed in 3d4c73a6c80c4105c14160dba548a09edd3bba37).

Copyright 2026 The Formal Conjectures Authors (Google DeepMind).

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib

/-!
# Weil's positivity criterion, as stated in Formal Conjectures

The definitions `weilArchimedean`, `weilNonArchimedean`, `IsTestFunction` and the right-hand side
of `weil_positivity_criterion` are copied verbatim from
`FormalConjectures/Paper/RiemannHypothesisEquivalents.lean` (formal-conjectures commit
`a425ca3e`), with their docstrings.

Adaptations, and nothing else:
* `module`, `public import FormalConjecturesUtil`, `@[expose] public section` removed
  (hp-proof does not use the module system; it imports `Mathlib`).
* The `@[category ...]`/`AMS` attributes (from `FormalConjecturesUtil`) removed.
* Namespace `RiemannHypothesis` renamed to `FleetWeilCriterion`.
* The two theorems, which Formal Conjectures leaves unproved, are not copied as theorems. Their
  statement is recorded verbatim as the `Prop`s `WeilPositivity` (the right-hand side, for all test
  functions) and `WeilPositivityCriterion` (the iff). The proofs are in `FleetWeilPositivity`
  (RH ⇒ `WeilPositivity`) and `FleetWeilRH` (`WeilPositivity` ⇒ RH, and
  `FleetWeilCriterion.weil_positivity_criterion : WeilPositivityCriterion`).
-/

open Real MeasureTheory
open scoped CompactlySupported Convolution ContDiff

namespace FleetWeilCriterion

/-- The additive Archimedean factor appearing in the Weil criterion. -/
noncomputable def weilArchimedean (f : ℝ → ℝ) : ℝ :=
  ((4 * π).log + eulerMascheroniConstant) * f 0 +
    ∫ x in Set.Ioi 0, (f x + f (-x) - 2 * exp (-x / 2) * f 0) * exp (x / 2) / (exp x - exp (-x))

/-- The additive non-Archimedean factor appearing in the Weil criterion. -/
noncomputable def weilNonArchimedean (p : ℕ) (f : ℝ → ℝ) : ℝ :=
    log p * ∑' m : ℕ, exp (-(m + 1) * log p / 2) * (f ((m + 1) * log p) + f (-(m + 1) * log p))

/-- The additive condition on test functions. The property in [Co26] that $\hat{g}(\pm i/2) = 0$,
where $\hat{g}$ is the Mellin transform, corresponds to the vanishing of the Fourier transform
at $\pm 1/2$. -/
def IsTestFunction (g : ℝ → ℝ) : Prop := ∫ x, g x * exp (x / 2) = 0 ∧ ∫ x, g x * exp (-x / 2) = 0

/-- The right-hand side of Formal Conjectures' `weil_positivity_criterion`, verbatim. -/
def WeilPositivity : Prop :=
  ∀ g : C_c(ℝ, ℝ), ContDiff ℝ ∞ g → IsTestFunction g →
      weilArchimedean (g ⋆ fun x ↦ g (-x)) +
        ∑' p : Nat.Primes, weilNonArchimedean p (g ⋆ fun x ↦ g (-x)) ≤ 0

/-- Formal Conjectures' `weil_positivity_criterion`, verbatim, as a proposition. -/
def WeilPositivityCriterion : Prop :=
  RiemannHypothesis ↔ ∀ g : C_c(ℝ, ℝ), ContDiff ℝ ∞ g → IsTestFunction g →
      weilArchimedean (g ⋆ fun x ↦ g (-x)) +
        ∑' p : Nat.Primes, weilNonArchimedean p (g ⋆ fun x ↦ g (-x)) ≤ 0

theorem weilPositivityCriterion_iff : WeilPositivityCriterion ↔ (RiemannHypothesis ↔ WeilPositivity) :=
  Iff.rfl

end FleetWeilCriterion
