import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Under-constrained bit decomposition, proved generically in the prime

`phi-verify`'s generated exploits are `example`s hard-coded at `p = 97`, and a
64-bit range-proof overflow cannot be expressed there at all. These statements
are generic in `p`, so they hold at BN254 — without a 254-bit primality
certificate and without a single `decide` call.
-/

set_option autoImplicit false

namespace ZKUnderconstraint

variable {p : ℕ} [Fact p.Prime]

private lemma two_ne_zero (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  have hp' : Nat.Prime p := Fact.out
  intro h
  have hc : ((2 : ℕ) : ZMod p) = 0 := by push_cast; exact h
  have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp hc
  exact hp ((Nat.prime_dvd_prime_iff_eq hp' Nat.prime_two).mp hd)

/-- The range-proof relation as a vulnerable circuit writes it: the weighted
sum alone. (`(2 : ZMod p) * b₁`, not the paste's `b * (2^i : ℕ)`, which does
not typecheck — a field element times a natural.) -/
def SumConstraint (x b₀ b₁ : ZMod p) : Prop := b₀ + 2 * b₁ = x

/-- The constraint the vulnerable circuit omits. -/
def Boolean (b : ZMod p) : Prop := b * (1 - b) = 0

/-- **The exploit, at every prime field.** Two distinct witnesses satisfy the
same weighted sum for the same `x`. True at BN254 because true at every prime. -/
theorem underconstrained_has_two_witnesses :
    SumConstraint (2 : ZMod p) 0 1 ∧ SumConstraint (2 : ZMod p) 2 0 ∧
      ((0 : ZMod p), (1 : ZMod p)) ≠ ((2 : ZMod p), (0 : ZMod p)) := by
  refine ⟨by simp [SumConstraint], by simp [SumConstraint], ?_⟩
  intro h
  exact one_ne_zero (congrArg Prod.snd h)

/-- **The omitted constraint is exactly what blocks the forgery.** The forging
witness `b₀ = 2` fails `Boolean` at every prime except 2. -/
theorem forgery_violates_boolean (hp : p ≠ 2) : ¬ Boolean (2 : ZMod p) := by
  intro h
  have h2 := two_ne_zero (p := p) hp
  have : (2 : ZMod p) * (1 - 2) = -(2 : ZMod p) := by ring
  rw [Boolean, this, neg_eq_zero] at h
  exact h2 h

/-- The honest witness does satisfy it, so the two are distinguished precisely
by the dropped constraint. -/
theorem honest_satisfies_boolean : Boolean (0 : ZMod p) ∧ Boolean (1 : ZMod p) := by
  constructor <;> simp [Boolean]

end ZKUnderconstraint

#print axioms ZKUnderconstraint.underconstrained_has_two_witnesses
#print axioms ZKUnderconstraint.forgery_violates_boolean
#print axioms ZKUnderconstraint.honest_satisfies_boolean
