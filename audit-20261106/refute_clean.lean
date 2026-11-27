import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

structure SingularCurve (p : ℕ) [Fact p.Prime] where
  a : ZMod p
  b : ZMod p

inductive Point (p : ℕ) [Fact p.Prime] (E : SingularCurve p)
| O : Point p E
| Affine : ZMod p → ZMod p → Point p E

-- NO sorry anywhere: any total group law whatsoever.
/-- The shape of `singular_break` / `spectral_discrete_log_break` is FALSE for
every possible definition of the group addition. -/
theorem break_shape_is_false
    (add : ∀ {p : ℕ} [Fact p.Prime] {E : SingularCurve p}, Point p E → Point p E → Point p E) :
    ¬ (∀ {p : ℕ} [inst : Fact p.Prime] (E : SingularCurve p) (phi : Point p E → ZMod p),
        (∃ P, phi P ≠ 0) → (∀ P Q : Point p E, phi (add P Q) = phi P + phi Q)) := by
  have h10 : (1 : ZMod 3) ≠ 0 := by decide
  have h11 : ¬ ((1 : ZMod 3) = 1 + 1) := by decide
  intro h
  have hp : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact h11 (h (⟨0, 0⟩ : SingularCurve 3) (fun _ => (1 : ZMod 3)) ⟨Point.O, h10⟩ Point.O Point.O)

#print axioms break_shape_is_false
