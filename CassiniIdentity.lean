import Mathlib

/-!
# Cassini's identity for Fibonacci numbers, over `ℤ`

`F_{n+2} · F_n − F_{n+1}² = (−1)^{n+1}` for every `n : ℕ`, stated over `ℤ`
so that no truncated `ℕ` subtraction occurs, and proved by induction on `n`
(no Binet / golden-ratio input).

Companion: the textbook-indexed form `F_{n+1} · F_{n−1} − F_n² = (−1)^n` for `n ≥ 1`.
-/

namespace CassiniIdentity

/-- **Cassini's identity** over `ℤ`:
`F_{n+2} · F_n − F_{n+1}² = (−1)^{n+1}`. -/
theorem fib_cassini (n : ℕ) :
    (Nat.fib (n + 2) : ℤ) * (Nat.fib n : ℤ) - (Nat.fib (n + 1) : ℤ) ^ 2
      = (-1 : ℤ) ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    have e2 : (Nat.fib (k + 2) : ℤ) = (Nat.fib k : ℤ) + (Nat.fib (k + 1) : ℤ) := by
      rw [show Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) from Nat.fib_add_two]
      push_cast
      ring
    have e3 : (Nat.fib (k + 3) : ℤ) = (Nat.fib (k + 1) : ℤ) + (Nat.fib (k + 2) : ℤ) := by
      rw [show Nat.fib (k + 1 + 2) = Nat.fib (k + 1) + Nat.fib (k + 1 + 1) from Nat.fib_add_two]
      push_cast
      ring
    have hpow : (-1 : ℤ) ^ (k + 1 + 1) = -((-1 : ℤ) ^ (k + 1)) := by ring
    show (Nat.fib (k + 3) : ℤ) * (Nat.fib (k + 1) : ℤ) - (Nat.fib (k + 2) : ℤ) ^ 2
        = (-1 : ℤ) ^ (k + 1 + 1)
    rw [hpow, ← ih, e3, e2]
    ring

/-- **Cassini's identity**, textbook indexing: `F_{n+1} · F_{n−1} − F_n² = (−1)^n` for `n ≥ 1`. -/
theorem fib_cassini_classic (n : ℕ) (hn : 1 ≤ n) :
    (Nat.fib (n + 1) : ℤ) * (Nat.fib (n - 1) : ℤ) - (Nat.fib n : ℤ) ^ 2
      = (-1 : ℤ) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simpa using fib_cassini m

#print axioms fib_cassini
#print axioms fib_cassini_classic

end CassiniIdentity
