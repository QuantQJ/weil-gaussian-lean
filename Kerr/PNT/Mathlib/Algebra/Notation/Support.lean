/-
Copied from PrimeNumberTheoremAnd (github.com/AlexKontorovich/PrimeNumberTheoremAnd), PrimeNumberTheoremAnd/Mathlib/Algebra/Notation/Support.lean, Apache-2.0, © the PrimeNumberTheoremAnd contributors (Kontorovich, Tao et al.). Included with QJ's approval, 2026-11-11.
Adaptations (mechanical only): `import Architect` removed; LeanArchitect `@[blueprint ...]` attributes and
`blueprint_comment` commands turned into ordinary comments (text kept); `PrimeNumberTheoremAnd.*` imports
renamed to `Kerr.PNT.*`.
-/
import Mathlib.Algebra.Notation.Support

namespace Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function
