/-
Copyright 2026 James C. Kerr (QuantQJ). Apache-2.0.
The target statement (`Q`, `A`, `B`, `ErrorTermImprovement`) is copied from
google-deepmind/formal-conjectures, `FormalConjectures/Wikipedia/PowerfulNumbersDensity.lean`
(commit a425ca3e, theorem `PowerfulNumbersDensity.error_term_improvement`), Apache-2.0,
© 2026 The Formal Conjectures Authors.
-/
import Kerr.NumberTheory.PowerfulNumbers.QuasiRH
import Kerr.NumberTheory.PowerfulNumbers.Reduction
import Kerr.NumberTheory.PowerfulNumbers.DivisorBound

/-!
# Powerful numbers: `Q(x) = A x^{1/2} + B x^{1/3} + O(x^{1/6−δ})` from a zero-free half-plane

`Q(x)` = number of powerful `n ≤ x`, `A = ζ(3/2)/ζ(3)`, `B = ζ(2/3)/ζ(2)`. The formal-conjectures
problem `error_term_improvement` asks for some `δ > 0` with error `O(x^{1/6−δ})`.

Route (Bateman–Grosswald 1958; the classical elementary route):
* `Q(x) = ∑_d μ(d) D(x/d⁶)`, `D(y) = #{a²c³ ≤ y}` (`Q_eq_sum_moebius_D`);
* `QuasiRH σ₀` (`ζ ≠ 0` on `Re s > σ₀`, `σ₀ < 1`) ⇒ `M(x) = O(x^{σ₀+ε})` (`mertens_bound_quasi`,
  Littlewood's method: Borel–Carathéodory + three circles + Perron);
* `M(x) = O(x^α)` with `α < 1` and `Δ_{2,3}(y) = O(y^θ)` with `θ < 1/6` ⇒ the conjecture with
  `δ = (1−α)(1−6θ)/24` (`errorTerm_of_bounds`).

* `Δ_{2,3}(y) = O(y^{3/20})` unconditionally (`divisorBound23_three_twentieths`, from
  `Kerr.NumberTheory.PowerfulNumbers.DivisorBound`: hyperbola method, second-order Euler–Maclaurin
  for `ζ(3/2)`, `ζ(2/3)`, and van der Corput's second-derivative test via Kusmin–Landau).

Final result: `errorTermImprovement_of_quasiRH_only` — `QuasiRH σ₀` for some `σ₀ < 1` implies
the formal-conjectures statement; `errorTermImprovement_of_quasiRH_seven_eighths_only` is the
instance `σ₀ = 7/8`. The only hypothesis is the zero-free half-plane; it is not proved here.
-/

noncomputable section
open Finset Real Filter Asymptotics

open scoped ArithmeticFunction.Moebius

namespace Kerr.PowerfulNumbers

/-- `Δ_{2,3}(y) = O(y^θ)` for `y ≥ 1`. -/
def DivisorBound23 (θ : ℝ) : Prop := ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → |Δ23 t| ≤ C * t ^ θ

lemma mert_eq_sum_Iic (n : ℕ) : mert n = ∑ k ∈ Finset.Iic ⌊(n : ℝ)⌋₊, (μ k : ℝ) := by
  have h : Finset.Iic n = Finset.Icc 0 n := by ext k; simp
  rw [Nat.floor_natCast, mert, h, Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons]
  simp

/-- `QuasiRH σ₀` (`1/2 ≤ σ₀ < 1`) ⇒ `|M(n)| ≤ C n^{σ₀+ε}`. -/
theorem mert_bound_of_quasiRH {σ₀ : ℝ} (hσ₀ : 1 / 2 ≤ σ₀) (hσ₀1 : σ₀ < 1) (hQ : QuasiRH σ₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → |mert n| ≤ C * (n : ℝ) ^ (σ₀ + ε) := by
  obtain ⟨K, -, hK⟩ := mertens_bound_quasi hσ₀ hσ₀1 hQ hε
  exact ⟨K, fun n hn => by rw [mert_eq_sum_Iic]; exact hK n (by exact_mod_cast hn)⟩

/-- **Main theorem (conditional).** If `ζ(s) ≠ 0` for `Re s > σ₀` with `σ₀ < 1`, and
`Δ_{2,3}(y) = O(y^θ)` for some `θ < 1/6`, then the formal-conjectures statement
`error_term_improvement` holds. -/
theorem errorTermImprovement_of_quasiRH {σ₀ : ℝ} (hσ₀ : 1 / 2 ≤ σ₀) (hσ₀1 : σ₀ < 1)
    (hQ : QuasiRH σ₀) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 6) (hD : DivisorBound23 θ) :
    ErrorTermImprovement := by
  set α := σ₀ + (1 - σ₀) / 2 with hα
  obtain ⟨C₁, hC₁⟩ := mert_bound_of_quasiRH hσ₀ hσ₀1 hQ (ε := (1 - σ₀) / 2) (by linarith)
  obtain ⟨C₂, hC₂⟩ := hD
  refine ⟨(1 - α) * (1 - 6 * θ) / 24, ?_, errorTerm_of_bounds (by linarith) (by linarith) hθ0 hθ
    hC₁ hC₂⟩
  have : 0 < 1 - α := by linarith
  have : 0 < 1 - 6 * θ := by linarith
  positivity

/-- The instance `σ₀ = 7/8` (the zero-free half-plane of the OpenAI preprint, used here only as
the hypothesis `QuasiRH (7/8)`). -/
theorem errorTermImprovement_of_quasiRH_seven_eighths (hQ : QuasiRH (7 / 8)) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 6) (hD : DivisorBound23 θ) : ErrorTermImprovement :=
  errorTermImprovement_of_quasiRH (by norm_num) (by norm_num) hQ hθ0 hθ hD

/-- **Unconditional `(2,3)` divisor bound** `Δ_{2,3}(y) = O(y^{3/20})`. -/
theorem divisorBound23_three_twentieths : DivisorBound23 (3 / 20) := divisor23_bound

/-- **Main theorem.** If `ζ(s) ≠ 0` for `Re s > σ₀` with `1/2 ≤ σ₀ < 1`, then the formal-conjectures
statement `PowerfulNumbersDensity.error_term_improvement` holds, with
`δ = (1 − α)(1 − 6·3/20)/24 = (1 − α)/240`, `α = (1 + σ₀)/2`. -/
theorem errorTermImprovement_of_quasiRH_only {σ₀ : ℝ} (hσ₀ : 1 / 2 ≤ σ₀) (hσ₀1 : σ₀ < 1)
    (hQ : QuasiRH σ₀) : ErrorTermImprovement :=
  errorTermImprovement_of_quasiRH hσ₀ hσ₀1 hQ (by norm_num) (by norm_num)
    divisorBound23_three_twentieths

/-- The instance `σ₀ = 7/8`: `QuasiRH (7/8)` (the OpenAI preprint's zero-free half-plane, used here
only as a hypothesis) implies `error_term_improvement`. -/
theorem errorTermImprovement_of_quasiRH_seven_eighths_only (hQ : QuasiRH (7 / 8)) :
    ErrorTermImprovement :=
  errorTermImprovement_of_quasiRH_only (by norm_num) (by norm_num) hQ

end Kerr.PowerfulNumbers
