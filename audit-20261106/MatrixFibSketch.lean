/-
# Matrix form of the Fibonacci recurrence (sketch)

This file preserves the matrix‑form Fibonacci ideas you wrote down, without
pulling heavy matrix machinery into the core `Certification.lean` file yet.

Nothing in this file is imported by the main framework; it is a **parking spot**
for future, fully‑formal Lean development.

The following block is Lean‑style pseudocode (as you wrote it) and can be
turned into real theorems by:

- importing the appropriate `Matrix` modules from `mathlib`
- replacing tactic calls (`omega`, etc.) with Lean 4 equivalents
- wiring in the existing `Certification` lemmas (`phi`, `psi`, `phi_sq`, …)

```lean
/-! ## Matrix form of the Fibonacci recurrence -/

/-- The companion matrix of the Fibonacci recurrence,
    often called the "Fibonacci matrix". -/
def FibMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  ![[1, 1],
    [1, 0]]

/-- Raising the Fibonacci matrix to the n-th power
    gives Fibonacci numbers in the entries. -/
theorem fib_matrix_pow (n : ℕ) :
    (FibMatrix ^ n) 0 0 = (Nat.fib (n + 1) : ℝ) ∧
    (FibMatrix ^ n) 0 1 = (Nat.fib n : ℝ)     ∧
    (FibMatrix ^ n) 1 0 = (Nat.fib n : ℝ)     ∧
    (FibMatrix ^ n) 1 1 = (Nat.fib (n - 1) : ℝ) := by
  induction n using Nat.rec_two with
  | zero =>
      -- n = 0: FibMatrix^0 = I
      simp [FibMatrix, Matrix.pow_zero]
      norm_num [Nat.fib_zero, Nat.fib_one]
  | one =>
      -- n = 1: FibMatrix^1 = FibMatrix
      simp [FibMatrix, Matrix.pow_one]
      norm_num [Nat.fib_one, Nat.fib_two, Nat.fib_zero]
  | ind k hk ih =>
      -- Inductive step: FibMatrix^{k+2} = FibMatrix^{k+1} * FibMatrix
      have hmul : FibMatrix ^ (k + 2) = FibMatrix ^ (k + 1) * FibMatrix := by
        rw [←Matrix.pow_succ, ←Nat.add_one, Nat.add_comm, Matrix.pow_add]
      rw [hmul]
      -- Multiply the two matrices using the IH
      have h11 : ((FibMatrix ^ (k + 1)) * FibMatrix) 0 0
          = (FibMatrix ^ (k + 1)) 0 0 * 1 + (FibMatrix ^ (k + 1)) 0 1 * 1 := by
        exact (Matrix.mul_apply _ _ _ _).symm
      have h12 : ((FibMatrix ^ (k + 1)) * FibMatrix) 0 1
          = (FibMatrix ^ (k + 1)) 0 0 * 1 + (FibMatrix ^ (k + 1)) 0 1 * 0 := by
        exact (Matrix.mul_apply _ _ _ _).symm
      have h21 : ((FibMatrix ^ (k + 1)) * FibMatrix) 1 0
          = (FibMatrix ^ (k + 1)) 1 0 * 1 + (FibMatrix ^ (k + 1)) 1 1 * 1 := by
        exact (Matrix.mul_apply _ _ _ _).symm
      have h22 : ((FibMatrix ^ (k + 1)) * FibMatrix) 1 1
          = (FibMatrix ^ (k + 1)) 1 0 * 1 + (FibMatrix ^ (k + 1)) 1 1 * 0 := by
        exact (Matrix.mul_apply _ _ _ _).symm
      rcases ih with ⟨ih00, ih01, ih10, ih11⟩
      constructor
      · rw [h11]; simp [ih00, ih01]; ring; exact (fib_recurrence (k + 2) (by omega)).symm
      constructor
      · rw [h12]; simp [ih00]; exact ih00
      constructor
      · rw [h21]; simp [ih10, ih11]; ring; exact (fib_recurrence (k + 1) (by omega)).symm
      · rw [h22]; simp [ih10]; exact ih10

/-- The most famous closed-form expression using matrices:
\n\begin{pmatrix} 1 & 1 \\ 1 & 0 \end{pmatrix}^n
= \begin{pmatrix} F_{n+1} & F_n \\ F_n & F_{n-1} \end{pmatrix} -/
theorem fib_matrix_closed_form (n : ℕ) (hn : n ≥ 1) :
    FibMatrix ^ n =
      ![[(Nat.fib (n + 1) : ℝ), (Nat.fib n : ℝ)],
        [(Nat.fib n : ℝ),     (Nat.fib (n - 1) : ℝ)]] := by
  ext i j
  rcases fib_matrix_pow n with ⟨h00, h01, h10, _⟩
  cases i <;> cases j <;> simp [FibMatrix]
  · exact h00
  · exact h01
  · exact h10
  · have : n - 1 + 1 = n := Nat.sub_add_cancel hn
    rw [←this]
    exact (fib_matrix_pow (n - 1)).2.2.2

/-- Vector form: the Fibonacci numbers arise from iterating the matrix on the initial vector. -/
theorem fib_vector_iteration (n : ℕ) :
    Matrix.vecMul ![(Nat.fib 1 : ℝ), (Nat.fib 0 : ℝ)] (FibMatrix ^ n)
      = ![(Nat.fib (n + 1) : ℝ), (Nat.fib n : ℝ)] := by
  rw [←Matrix.mul_vec, ←Matrix.pow_succ]
  induction n with
  | zero => simp [Matrix.pow_zero, Matrix.one_vecMul]
  | succ n ih =>
      simp [Matrix.pow_succ, Matrix.vecMul_assoc, ih]
      have : Nat.fib (n + 2) = Nat.fib (n + 1) + Nat.fib n := fib_succ_succ n
      simp [this, FibMatrix, Matrix.vecMul]
      ring

/-- Bonus: explicit Binet-style formula from diagonalizing the Fibonacci matrix -/
theorem fib_matrix_diagonalization :
    ∃ (P : Matrix (Fin 2) (Fin 2) ℝ) (D : Matrix (Fin 2) (Fin 2) ℝ),
      Invertible P ∧
      FibMatrix = P * D * P⁻¹ ∧
      D = Matrix.diagonal (fun i => if i.val = 0 then phi else psi) := by
  let P : Matrix (Fin 2) (Fin 2) ℝ := ![[phi, psi], [1, 1]]
  use P, Matrix.diagonal (fun i => if i.val = 0 then phi else psi)
  constructor
  · apply Matrix.invertible_of_det_ne_zero
    simp [P, Matrix.det_fin_two]
    field_simp [phi_mul_psi, phi_sub_psi]
    norm_num
  constructor
  · ext i j
    cases i <;> cases j <;> simp [P, FibMatrix, phi_sq, psi_sq, phi_add_psi]
    all_goals ring
  · ext i; fin_cases i <;> rfl
```

When you’re ready to formalize this:

1. Move the definitions/theorems out of the comment.
2. Add the appropriate imports:
   - `Mathlib.Data.Matrix.Basic`
   - `Mathlib.Data.Matrix.Notation`
   - `Mathlib.Data.Fin.Basic`
   - plus `Cooler!.Tex.Certification` for `phi`, `psi`, etc.
3. Replace any non‑Lean‑4 tactics (`omega`) with the current equivalents.

For now, this keeps the matrix story **documented but non‑intrusive**.
-/


