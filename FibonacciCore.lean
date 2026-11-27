import Mathlib

/-!
# Fibonacci / Golden-Ratio Core (salvaged, verified)

Clean-room verification of the φ/Fibonacci corpus found in
`Fibonacci-Formal/Lean/Fibonacci_Diagonalization.lean` and
`H_phi_SPECTRAL_MASTERCLASS/2_TRUTH_ENGINE.lean` (2026-08-01 salvage).
The original files stated correct mathematics with AI-drafted proofs that
never compiled; this module re-proves the same results against Mathlib
v4.16.0 with no `sorry` and no custom axioms:

* φ/ψ algebra: `phi_sq`, `psi_sq`, `phi_add_psi`, `phi_mul_psi`, `phi_sub_psi`
* `rec2_unique` — uniqueness for order-2 linear recurrences (correct induction)
* **Binet's formula** (`binet_formula`), Lucas Binet (`lucas_binet`)
* `fib_succ_phi` : `F_{n+1} = φ·F_n + ψⁿ` (exact, division-free)
* **Cassini's identity** (`cassini'`, `cassini`)
* **Pell identity** `L_n² − 5F_n² = 4(−1)ⁿ` (`pell_lucas_fib`)
* golden power identity `φ^{n+2} = F_{n+2}φ + F_{n+1}` (`golden_power_fib`)
* `psi_pow_tendsto_zero`, `fib_ratio_tendsto_phi` (convergents → φ)
* irrationality: `sqrt5_irrational`, `phi_irrational`
* Fibonacci matrix: `fib_matrix_pow` (companion-matrix powers)
* flagship: `phi_pow_four`, `flagship_identity` (6φ⁴ = 21 + 9√5),
  `flagship_bound` (|42 − 6φ⁴| < 1)
-/

noncomputable section
open Filter Real

namespace FibonacciCore

/-- The golden ratio `φ = (1 + √5)/2`. -/
def phi : ℝ := (1 + Real.sqrt 5) / 2

/-- The conjugate root `ψ = (1 - √5)/2`. -/
def psi : ℝ := (1 - Real.sqrt 5) / 2

lemma sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

lemma sqrt5_pos : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)

lemma sqrt5_ne_zero : Real.sqrt 5 ≠ 0 := ne_of_gt sqrt5_pos

lemma sqrt5_lt_three : Real.sqrt 5 < 3 := by
  have h : (5 : ℝ) < 3 ^ 2 := by norm_num
  calc Real.sqrt 5 < Real.sqrt (3 ^ 2) := by
        exact Real.sqrt_lt_sqrt (by norm_num) h
    _ = 3 := by
        rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3)]

lemma two_lt_sqrt5 : (2 : ℝ) < Real.sqrt 5 := by
  have h : (2 : ℝ) ^ 2 < 5 := by norm_num
  calc (2 : ℝ) = Real.sqrt (2 ^ 2) := by
        rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    _ < Real.sqrt 5 := Real.sqrt_lt_sqrt (by positivity) h

/-- `φ² = φ + 1`. -/
theorem phi_sq : phi ^ 2 = phi + 1 := by
  unfold phi
  have h := sqrt5_sq
  field_simp
  nlinarith [h]

/-- `ψ² = ψ + 1`. -/
theorem psi_sq : psi ^ 2 = psi + 1 := by
  unfold psi
  have h := sqrt5_sq
  field_simp
  nlinarith [h]

/-- `φ + ψ = 1`. -/
theorem phi_add_psi : phi + psi = 1 := by unfold phi psi; ring

/-- `φ·ψ = −1`. -/
theorem phi_mul_psi : phi * psi = -1 := by
  unfold phi psi
  have h := sqrt5_sq
  field_simp
  nlinarith [h]

/-- `φ − ψ = √5`. -/
theorem phi_sub_psi : phi - psi = Real.sqrt 5 := by unfold phi psi; ring

lemma abs_psi_lt_one : |psi| < 1 := by
  unfold psi
  rw [abs_lt]
  constructor <;> nlinarith [two_lt_sqrt5, sqrt5_lt_three]

/-- `ψⁿ → 0`. -/
theorem psi_pow_tendsto_zero :
    Tendsto (fun n : ℕ => psi ^ n) atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_abs_lt_one abs_psi_lt_one

/-! ## Order-2 recurrence uniqueness and Binet -/

/-- **Uniqueness of order-2 linear recurrences**: two sequences with the same
first two values satisfying `x_{n+2} = x_{n+1} + x_n` agree everywhere.
(The original file's `Nat.rec` proof was invalid; this is the standard
paired-induction argument.) -/
lemma rec2_unique {u v : ℕ → ℝ}
    (h0 : u 0 = v 0) (h1 : u 1 = v 1)
    (hu : ∀ n, u (n + 2) = u (n + 1) + u n)
    (hv : ∀ n, v (n + 2) = v (n + 1) + v n) :
    ∀ n, u n = v n := by
  have key : ∀ n, u n = v n ∧ u (n + 1) = v (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨h0, h1⟩
    | succ k ih => exact ⟨ih.2, by rw [hu k, hv k, ih.1, ih.2]⟩
  exact fun n => (key n).1

lemma pow_rec_phi (n : ℕ) : phi ^ (n + 2) = phi ^ (n + 1) + phi ^ n := by
  have h := phi_sq
  calc phi ^ (n + 2) = phi ^ n * phi ^ 2 := by ring
    _ = phi ^ n * (phi + 1) := by rw [h]
    _ = phi ^ (n + 1) + phi ^ n := by ring

lemma pow_rec_psi (n : ℕ) : psi ^ (n + 2) = psi ^ (n + 1) + psi ^ n := by
  have h := psi_sq
  calc psi ^ (n + 2) = psi ^ n * psi ^ 2 := by ring
    _ = psi ^ n * (psi + 1) := by rw [h]
    _ = psi ^ (n + 1) + psi ^ n := by ring

/-- The Binet closed form. -/
def binet (n : ℕ) : ℝ := (phi ^ n - psi ^ n) / Real.sqrt 5

/-- **Binet's formula**: `F_n = (φⁿ − ψⁿ)/√5`. -/
theorem binet_formula (n : ℕ) : (Nat.fib n : ℝ) = binet n := by
  have h0 : ((Nat.fib 0 : ℝ)) = binet 0 := by simp [binet]
  have h1 : ((Nat.fib 1 : ℝ)) = binet 1 := by
    rw [binet, pow_one, pow_one, phi_sub_psi, Nat.fib_one, Nat.cast_one,
        div_self sqrt5_ne_zero]
  have hu : ∀ m, ((Nat.fib (m + 2) : ℝ)) = (Nat.fib (m + 1) : ℝ) + (Nat.fib m : ℝ) := by
    intro m; push_cast [Nat.fib_add_two]; ring
  have hv : ∀ m, binet (m + 2) = binet (m + 1) + binet m := by
    intro m; rw [binet, binet, binet, pow_rec_phi, pow_rec_psi]; ring
  exact rec2_unique (u := fun k => (Nat.fib k : ℝ)) (v := binet) h0 h1 hu hv n

/-! ## Lucas numbers -/

/-- Lucas numbers: `L₀ = 2`, `L₁ = 1`, `L_{n+2} = L_{n+1} + L_n`. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

/-- **Lucas Binet formula**: `L_n = φⁿ + ψⁿ`. -/
theorem lucas_binet (n : ℕ) : (lucas n : ℝ) = phi ^ n + psi ^ n := by
  have h0 : ((lucas 0 : ℝ)) = phi ^ 0 + psi ^ 0 := by simp [lucas]; norm_num
  have h1 : ((lucas 1 : ℝ)) = phi ^ 1 + psi ^ 1 := by
    simp only [lucas, Nat.cast_one, pow_one]
    rw [phi_add_psi]
  have hu : ∀ m, ((lucas (m + 2) : ℝ)) = (lucas (m + 1) : ℝ) + (lucas m : ℝ) := by
    intro m; push_cast [lucas]; ring
  have hv : ∀ m, phi ^ (m + 2) + psi ^ (m + 2)
      = (phi ^ (m + 1) + psi ^ (m + 1)) + (phi ^ m + psi ^ m) := by
    intro m; rw [pow_rec_phi, pow_rec_psi]; ring
  exact rec2_unique (u := fun k => (lucas k : ℝ))
    (v := fun k => phi ^ k + psi ^ k) h0 h1 hu hv n

/-! ## Exact identities -/

/-- Division-free step identity: `F_{n+1} = φ·F_n + ψⁿ`. -/
theorem fib_succ_phi (n : ℕ) :
    (Nat.fib (n + 1) : ℝ) = phi * (Nat.fib n : ℝ) + psi ^ n := by
  rw [binet_formula, binet_formula, binet, binet]
  have hsub : phi - psi = Real.sqrt 5 := phi_sub_psi
  field_simp
  linear_combination (psi ^ n) * hsub

/-- **Cassini's identity**, subtraction-free form:
`F_{m+1}² − F_m·F_{m+2} = (−1)^m`. -/
theorem cassini' (m : ℕ) :
    (Nat.fib (m + 1) : ℝ) ^ 2
      - (Nat.fib m : ℝ) * (Nat.fib (m + 2) : ℝ) = (-1 : ℝ) ^ m := by
  rw [binet_formula, binet_formula, binet_formula, binet, binet, binet]
  have h5 := sqrt5_sq
  have hprod : phi * psi = -1 := phi_mul_psi
  have hsub : phi - psi = Real.sqrt 5 := phi_sub_psi
  have key : (phi ^ (m + 1) - psi ^ (m + 1)) ^ 2
      - (phi ^ m - psi ^ m) * (phi ^ (m + 2) - psi ^ (m + 2))
      = (phi * psi) ^ m * (phi - psi) ^ 2 := by ring
  field_simp
  rw [key, hprod, hsub, sqrt5_sq]
  ring

/-- **Cassini's identity**, classical form for `n ≥ 1`:
`F_n² − F_{n−1}·F_{n+1} = (−1)^{n−1}`. -/
theorem cassini (n : ℕ) (hn : 1 ≤ n) :
    (Nat.fib n : ℝ) ^ 2
      - (Nat.fib (n - 1) : ℝ) * (Nat.fib (n + 1) : ℝ) = (-1 : ℝ) ^ (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h1 : 1 + m - 1 = m := by omega
  have h2 : 1 + m + 1 = m + 2 := by omega
  have h3 : 1 + m = m + 1 := by omega
  rw [h1, h2, h3]
  exact cassini' m

/-- **Pell identity**: `L_n² − 5·F_n² = 4·(−1)ⁿ`. -/
theorem pell_lucas_fib (n : ℕ) :
    (lucas n : ℝ) ^ 2 - 5 * (Nat.fib n : ℝ) ^ 2 = 4 * (-1 : ℝ) ^ n := by
  rw [lucas_binet, binet_formula, binet]
  have h5 := sqrt5_sq
  have hprod : phi * psi = -1 := phi_mul_psi
  have hF2 : 5 * ((phi ^ n - psi ^ n) / Real.sqrt 5) ^ 2
      = (phi ^ n - psi ^ n) ^ 2 := by
    rw [div_pow, sqrt5_sq]
    ring
  rw [hF2]
  calc (phi ^ n + psi ^ n) ^ 2 - (phi ^ n - psi ^ n) ^ 2
      = 4 * (phi * psi) ^ n := by ring
    _ = 4 * (-1 : ℝ) ^ n := by rw [hprod]

/-- **Golden power identity**: `φ^{n+2} = F_{n+2}·φ + F_{n+1}`. -/
theorem golden_power_fib (n : ℕ) :
    phi ^ (n + 2) = (Nat.fib (n + 2) : ℝ) * phi + (Nat.fib (n + 1) : ℝ) := by
  induction n with
  | zero => simpa [pow_two] using phi_sq
  | succ k ih =>
      have hfib : (Nat.fib (k + 3) : ℝ)
          = (Nat.fib (k + 2) : ℝ) + (Nat.fib (k + 1) : ℝ) := by
        push_cast [Nat.fib_add_two]; ring
      calc phi ^ (k + 3) = phi * phi ^ (k + 2) := by ring
        _ = phi * ((Nat.fib (k + 2) : ℝ) * phi + (Nat.fib (k + 1) : ℝ)) := by
              rw [ih]
        _ = (Nat.fib (k + 2) : ℝ) * phi ^ 2 + (Nat.fib (k + 1) : ℝ) * phi := by
              ring
        _ = (Nat.fib (k + 2) : ℝ) * (phi + 1) + (Nat.fib (k + 1) : ℝ) * phi := by
              rw [phi_sq]
        _ = ((Nat.fib (k + 2) : ℝ) + (Nat.fib (k + 1) : ℝ)) * phi
              + (Nat.fib (k + 2) : ℝ) := by ring
        _ = (Nat.fib (k + 3) : ℝ) * phi + (Nat.fib (k + 2) : ℝ) := by
              rw [hfib]

/-! ## Convergents: `F_{n+1}/F_n → φ` -/

lemma fib_pos_real {n : ℕ} (hn : 1 ≤ n) : (0 : ℝ) < (Nat.fib n : ℝ) := by
  exact_mod_cast Nat.fib_pos.mpr hn

lemma one_le_fib_real {n : ℕ} (hn : 1 ≤ n) : (1 : ℝ) ≤ (Nat.fib n : ℝ) := by
  have := Nat.fib_pos.mpr hn
  exact_mod_cast this

/-- Exact convergent formula: for `n ≥ 1`,
`F_{n+1}/F_n = φ + ψⁿ/F_n`. -/
theorem fib_ratio_eq (n : ℕ) (hn : 1 ≤ n) :
    (Nat.fib (n + 1) : ℝ) / (Nat.fib n : ℝ)
      = phi + psi ^ n / (Nat.fib n : ℝ) := by
  have hpos := fib_pos_real hn
  rw [fib_succ_phi]
  field_simp

/-- **The Fibonacci convergents tend to φ.**
(Replaces the axiom `fibonacci_ratio_tendsto_phi` found in
phi-spectral-framework/Certification.lean.) -/
theorem fib_ratio_tendsto_phi :
    Tendsto (fun n : ℕ => (Nat.fib (n + 1) : ℝ) / (Nat.fib n : ℝ))
      atTop (nhds phi) := by
  have herr : Tendsto (fun n : ℕ => psi ^ n / (Nat.fib n : ℝ)) atTop (nhds 0) := by
    have habs : |(|psi|)| < 1 := by rw [abs_abs]; exact abs_psi_lt_one
    apply squeeze_zero_norm _ (tendsto_pow_atTop_nhds_zero_of_abs_lt_one habs)
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp
    · have h1 : (1 : ℝ) ≤ |(Nat.fib n : ℝ)| := by
        rw [abs_of_pos (fib_pos_real hpos)]
        exact one_le_fib_real hpos
      calc ‖psi ^ n / (Nat.fib n : ℝ)‖
          = |psi| ^ n / |(Nat.fib n : ℝ)| := by
            rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
        _ ≤ |psi| ^ n := div_le_self (by positivity) h1
  have hshift : ∀ᶠ n : ℕ in atTop,
      (Nat.fib (n + 1) : ℝ) / (Nat.fib n : ℝ)
        = phi + psi ^ n / (Nat.fib n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact fib_ratio_eq n hn
  have hlim : Tendsto (fun n : ℕ => phi + psi ^ n / (Nat.fib n : ℝ))
      atTop (nhds (phi + 0)) := tendsto_const_nhds.add herr
  rw [add_zero] at hlim
  exact hlim.congr' (by filter_upwards [hshift] with n h using h.symm)

/-! ## Irrationality -/

/-- `√5` is irrational. (Replaces the axiom `sqrt5_irrational` in
phi-spectral-framework/Certification.lean — it's a Mathlib one-liner.) -/
theorem sqrt5_irrational : Irrational (Real.sqrt 5) := by
  have h : Nat.Prime 5 := by norm_num
  simpa using h.irrational_sqrt

/-- The golden ratio is irrational. -/
theorem phi_irrational : Irrational phi := by
  have h1 : Irrational (1 + Real.sqrt 5) := by
    simpa using Irrational.ratCast_add 1 sqrt5_irrational
  have h2 : Irrational ((1 + Real.sqrt 5) / 2) := by
    simpa using Irrational.div_natCast h1 (by norm_num : (2:ℕ) ≠ 0)
  exact h2

/-! ## The Fibonacci companion matrix -/

open Matrix

/-- The Fibonacci companion matrix `[[1,1],[1,0]]`. -/
def FibMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 0]

/-- **Companion-matrix powers carry Fibonacci numbers**:
`A^{n+1} = [[F_{n+2}, F_{n+1}], [F_{n+1}, F_n]]`. -/
theorem fib_matrix_pow (n : ℕ) :
    FibMatrix ^ (n + 1)
      = !![(Nat.fib (n + 2) : ℝ), (Nat.fib (n + 1) : ℝ);
           (Nat.fib (n + 1) : ℝ), (Nat.fib n : ℝ)] := by
  induction n with
  | zero => simp [FibMatrix, pow_one]
  | succ k ih =>
      have h3 : (Nat.fib (k + 3) : ℝ)
          = (Nat.fib (k + 2) : ℝ) + (Nat.fib (k + 1) : ℝ) := by
        push_cast [Nat.fib_add_two]; ring
      have h2 : (Nat.fib (k + 2) : ℝ)
          = (Nat.fib (k + 1) : ℝ) + (Nat.fib k : ℝ) := by
        push_cast [Nat.fib_add_two]; ring
      rw [pow_succ, ih, FibMatrix, Matrix.mul_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp <;> linarith [h3, h2]

/-- Determinant of the companion matrix is `−1` — the structural source of
Cassini's identity. -/
theorem fib_matrix_det : FibMatrix.det = -1 := by
  simp [FibMatrix, Matrix.det_fin_two_of]

/-! ## Flagship identities (from `2_TRUTH_ENGINE.lean`) -/

/-- `φ⁴ = (7 + 3√5)/2`. -/
theorem phi_pow_four : phi ^ 4 = (7 + 3 * Real.sqrt 5) / 2 := by
  have h2 : phi ^ 2 = phi + 1 := phi_sq
  have h4 : phi ^ 4 = (phi + 1) ^ 2 := by
    calc phi ^ 4 = (phi ^ 2) ^ 2 := by ring
      _ = (phi + 1) ^ 2 := by rw [h2]
  rw [h4]
  have : (phi + 1) ^ 2 = phi ^ 2 + 2 * phi + 1 := by ring
  rw [this, h2]
  unfold phi
  ring

/-- **Flagship identity**: `6φ⁴ = 21 + 9√5` (exact). -/
theorem flagship_identity : 6 * phi ^ 4 = 21 + 9 * Real.sqrt 5 := by
  rw [phi_pow_four]; ring

/-- Interval bounds `2.23 < √5 < 2.24` — tight enough for `flagship_bound`,
which needs `20/9 < √5 < 22/9`. -/
lemma sqrt5_bounds : 2.23 < Real.sqrt 5 ∧ Real.sqrt 5 < 2.24 := by
  constructor
  · have h : (2.23 : ℝ) ^ 2 < 5 := by norm_num
    calc (2.23 : ℝ) = Real.sqrt (2.23 ^ 2) := by
          rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2.23)]
      _ < Real.sqrt 5 := Real.sqrt_lt_sqrt (by positivity) h
  · have h : (5 : ℝ) < 2.24 ^ 2 := by norm_num
    calc Real.sqrt 5 < Real.sqrt (2.24 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) h
      _ = 2.24 := Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2.24)

/-- **Flagship bound**: `|42 − 6φ⁴| < 1`. The "entropy barrier" 6φ⁴ ≈ 41.12
is within 1 of 42 — proven by interval arithmetic, not asserted. -/
theorem flagship_bound : |42 - 6 * phi ^ 4| < 1 := by
  rw [flagship_identity]
  obtain ⟨hlo, hhi⟩ := sqrt5_bounds
  rw [abs_lt]
  constructor <;> nlinarith [hlo, hhi]

end FibonacciCore
