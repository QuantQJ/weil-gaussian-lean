/-
Copyright 2026 James C. Kerr (QuantQJ). Apache-2.0.
-/
import Mathlib

/-!
# Lucas numbers

`Nat.lucas` and the Lucas analogue of Mathlib's `Real.coe_fib_eq`, built **on** Mathlib's
`Real.goldenRatio` rather than re-deriving φ.

Mathlib has `Real.goldenRatio`, `Real.goldenConj`, `Real.coe_fib_eq` (Binet for `Nat.fib`),
Cassini (`Mathlib/Data/Int/Fib/Lemmas.lean`) and the ratio limit
(`Mathlib/Analysis/SpecificLimits/Fibonacci.lean`).  It does **not** have the Lucas numbers:
`LucasPrimality` and `LucasLehmer` are different objects.  This file supplies them.

* `Nat.lucas` : `L 0 = 2`, `L 1 = 1`, `L (n+2) = L (n+1) + L n`.
* `Nat.coe_lucas_eq` : `(L n : ℝ) = φ ^ n + ψ ^ n` — the additive companion of `coe_fib_eq`.
* `Nat.lucas_succ_eq` : `L (n+1) = F n + F (n+2)`, in `ℕ`, no casts.
* `Nat.fib_two_mul_eq` : `F (2n) = F n * L n`, in `ℕ`.
* `Nat.coe_lucas_sq_sub` : `L n ^ 2 - 5 * F n ^ 2 = 4 * (-1) ^ n`.

Gotcha for anyone upstreaming this: inside `namespace Nat` the scoped notation `φ` for
`Real.goldenRatio` is ambiguous with `Nat.totient`, so the full names are used throughout.
-/

set_option autoImplicit false
open Real

namespace Nat

/-- Lucas numbers: `L 0 = 2`, `L 1 = 1`, `L (n+2) = L (n+1) + L n`. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

@[simp] theorem lucas_zero : lucas 0 = 2 := rfl
@[simp] theorem lucas_one : lucas 1 = 1 := rfl
theorem lucas_add_two (n : ℕ) : lucas (n + 2) = lucas (n + 1) + lucas n := rfl

/-- Paired induction for the Fibonacci recurrence: two sequences with equal first two values
satisfying `u (n+2) = u (n+1) + u n` agree. -/
theorem rec2_unique {u v : ℕ → ℝ} (h0 : u 0 = v 0) (h1 : u 1 = v 1)
    (hu : ∀ n, u (n + 2) = u (n + 1) + u n) (hv : ∀ n, v (n + 2) = v (n + 1) + v n) :
    ∀ n, u n = v n := by
  have key : ∀ n, u n = v n ∧ u (n + 1) = v (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨h0, h1⟩
    | succ k ih => exact ⟨ih.2, by rw [hu k, hv k, ih.1, ih.2]⟩
  exact fun n => (key n).1

/-- **Binet's formula for the Lucas numbers**: `L n = φ ^ n + ψ ^ n`.
The additive companion of Mathlib's `Real.coe_fib_eq`. -/
theorem coe_lucas_eq (n : ℕ) : (lucas n : ℝ) = goldenRatio ^ n + goldenConj ^ n := by
  have hrec : ∀ x : ℝ, x ^ 2 = x + 1 → ∀ m : ℕ, x ^ (m + 2) = x ^ (m + 1) + x ^ m := by
    intro x hx m
    calc x ^ (m + 2) = x ^ m * x ^ 2 := by ring
      _ = x ^ m * (x + 1) := by rw [hx]
      _ = x ^ (m + 1) + x ^ m := by ring
  refine rec2_unique (u := fun k => (lucas k : ℝ)) (v := fun k => goldenRatio ^ k + goldenConj ^ k)
    (by norm_num) (by simp [goldenRatio_add_goldenConj]) (fun m => by push_cast [lucas]; ring)
    (fun m => by rw [hrec goldenRatio goldenRatio_sq, hrec goldenConj goldenConj_sq]; ring) n

/-- `L (n+1) = F n + F (n+2)`. -/
theorem lucas_succ_eq (n : ℕ) : lucas (n + 1) = fib n + fib (n + 2) := by
  have key : ∀ n, lucas (n + 1) = fib n + fib (n + 2) ∧
      lucas (n + 2) = fib (n + 1) + fib (n + 3) := by
    intro n
    induction n with
    | zero => constructor <;> simp [lucas, fib_add_two]
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [lucas_add_two, ih.1, ih.2]
      simp only [fib_add_two]
      omega
  exact (key n).1

/-- `F (2n) = F n * L n`. -/
theorem fib_two_mul_eq (n : ℕ) : fib (2 * n) = fib n * lucas n := by
  have h : ((fib (2 * n) : ℝ)) = ((fib n * lucas n : ℕ) : ℝ) := by
    push_cast
    rw [coe_fib_eq, coe_fib_eq, coe_lucas_eq]
    have h5 : (√5 : ℝ) ≠ 0 := by positivity
    field_simp
    rw [two_mul]
    ring
  exact Nat.cast_injective h

/-- `L n ^ 2 - 5 * F n ^ 2 = 4 * (-1) ^ n`, over `ℝ`. -/
theorem coe_lucas_sq_sub (n : ℕ) :
    (lucas n : ℝ) ^ 2 - 5 * (fib n : ℝ) ^ 2 = 4 * (-1 : ℝ) ^ n := by
  rw [coe_lucas_eq, coe_fib_eq]
  have h5 : (√5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5' : (√5 : ℝ) ≠ 0 := by positivity
  have hstep : 5 * ((goldenRatio ^ n - goldenConj ^ n) / √5) ^ 2
      = (goldenRatio ^ n - goldenConj ^ n) ^ 2 := by
    rw [div_pow, h5]
    field_simp
  rw [hstep]
  have key : (goldenRatio ^ n + goldenConj ^ n) ^ 2 - (goldenRatio ^ n - goldenConj ^ n) ^ 2
      = 4 * (goldenRatio ^ n * goldenConj ^ n) := by ring
  rw [key, ← mul_pow, goldenRatio_mul_goldenConj]

end Nat
