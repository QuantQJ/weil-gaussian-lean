import FleetRationalBankCriterion
import FleetGaussianDictionaryMember

/-!
# A three-centre inequality forced by any feasible stage

For a real point `t` the width-one probe at centre `q` is the real Gaussian
`√π · exp (-(t-q)²/4)`. By the arithmetic–geometric mean inequality every real atom obeys

  `2 · exp (-r²/4) · probe c t ≤ probe (c-r) t + probe (c+r) t`.

Summing over the atoms of a feasible list, and using that the list matches the arithmetic
target within `1/(n+1)` at the three centres, gives an inequality on the arithmetic target
alone. No mass budget enters. Its contrapositive is an infeasibility certificate for the stage.

This file proves that implication only. It does not assert that the arithmetic target
satisfies or violates the inequality at any particular centres.
-/

noncomputable section
open GaussianTest Complex

namespace FleetThreeCentreInequality

/-- The width-one probe at a real point is a real Gaussian. -/
lemma probe_real (q t : ℝ) :
    FleetFullLineFourier.h (gauss 1 q) (t : ℂ) =
      ((Real.sqrt Real.pi * Real.exp (-(t-q)^2/4) : ℝ) : ℂ) := by
  rw [FleetGaussianDictionaryMember.h_gauss_eq (by norm_num : (0 : ℝ) < 1)]
  have he : (-((t : ℂ)-(q : ℂ))^2/(4*((1 : ℝ) : ℂ))) = ((-(t-q)^2/4 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he, ← Complex.ofReal_exp, div_one, ← Complex.ofReal_mul]

/-- Arithmetic–geometric mean inequality for three equally spaced Gaussians. -/
lemma three_point (s r : ℝ) :
    2 * Real.exp (-r^2/4) * Real.exp (-s^2/4) ≤
      Real.exp (-(s+r)^2/4) + Real.exp (-(s-r)^2/4) := by
  have h1 : Real.exp (-(s+r)^2/4) = Real.exp (-(s+r)^2/8) * Real.exp (-(s+r)^2/8) := by
    rw [← Real.exp_add]
    ring_nf
  have h2 : Real.exp (-(s-r)^2/4) = Real.exp (-(s-r)^2/8) * Real.exp (-(s-r)^2/8) := by
    rw [← Real.exp_add]
    ring_nf
  have h3 : Real.exp (-r^2/4) * Real.exp (-s^2/4) =
      Real.exp (-(s+r)^2/8) * Real.exp (-(s-r)^2/8) := by
    rw [← Real.exp_add, ← Real.exp_add]
    ring_nf
  rw [h1, h2, mul_assoc, h3]
  nlinarith [sq_nonneg (Real.exp (-(s+r)^2/8) - Real.exp (-(s-r)^2/8))]

/-- If stage `n` is feasible for the width-one probes, with any mass budget, then at any three
bank centres `c - r`, `c`, `c + r` the arithmetic target satisfies this inequality. -/
theorem three_centre_of_feasible {M : ℝ} {n : ℕ}
    (hf : FleetRationalBankCriterion.Feasible 1 M n) {a c d : ℚ}
    (ha : a ∈ FleetRationalBanks.bank n) (hc : c ∈ FleetRationalBanks.bank n)
    (hd : d ∈ FleetRationalBanks.bank n) (r : ℝ)
    (hl : (a : ℝ) = (c : ℝ) - r) (hr : (d : ℝ) = (c : ℝ) + r) :
    2 * Real.exp (-r^2/4) * (FleetFullLineArithmetic.rhs (gauss 1 (c : ℝ))).re
        - (FleetFullLineArithmetic.rhs (gauss 1 (a : ℝ))).re
        - (FleetFullLineArithmetic.rhs (gauss 1 (d : ℝ))).re
      ≤ (2 * Real.exp (-r^2/4) + 2) / ((n : ℝ) + 1) := by
  obtain ⟨N, x, -, hres⟩ := hf
  let S : ℝ → ℝ := fun q => ∑ i : Fin N, Real.sqrt Real.pi * Real.exp (-(x i - q)^2/4)
  have htrace : ∀ q : ℝ,
      (∑ i : Fin N, FleetFullLineFourier.h (gauss 1 q) (x i)) = ((S q : ℝ) : ℂ) := by
    intro q
    simp only [S]
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun i _ => probe_real q (x i))
  have hclose : ∀ q ∈ FleetRationalBanks.bank n,
      |S (q : ℝ) - (FleetFullLineArithmetic.rhs (gauss 1 (q : ℝ))).re| ≤ 1/((n : ℝ)+1) := by
    intro q hq
    have h := hres q hq
    rw [htrace] at h
    have h2 := Complex.abs_re_le_norm
      (((S (q : ℝ) : ℝ) : ℂ) - FleetFullLineArithmetic.rhs (gauss 1 (q : ℝ)))
    rw [Complex.sub_re, Complex.ofReal_re] at h2
    exact h2.trans h
  have hkey : 2 * Real.exp (-r^2/4) * S (c : ℝ) ≤ S (a : ℝ) + S (d : ℝ) := by
    simp only [S]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have h3 := three_point (x i - (c : ℝ)) r
    have e1 : x i - (a : ℝ) = (x i - (c : ℝ)) + r := by rw [hl]; ring
    have e2 : x i - (d : ℝ) = (x i - (c : ℝ)) - r := by rw [hr]; ring
    rw [e1, e2]
    have hs : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h3 hs]
  have h1 := abs_le.mp (hclose a ha)
  have h2 := abs_le.mp (hclose c hc)
  have h3 := abs_le.mp (hclose d hd)
  have he : 0 ≤ Real.exp (-r^2/4) := (Real.exp_pos _).le
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hdiv : (2 * Real.exp (-r^2/4) + 2) / ((n : ℝ) + 1) =
      (2 * Real.exp (-r^2/4) + 2) * (1/((n : ℝ)+1)) := by ring
  rw [hdiv]
  nlinarith [mul_nonneg he (by linarith [h2.1] :
    (0 : ℝ) ≤ S (c : ℝ) - (FleetFullLineArithmetic.rhs (gauss 1 (c : ℝ))).re + 1/((n : ℝ)+1))]

/-- Contrapositive: a violation of the three-centre inequality by the arithmetic target
certifies that the stage is infeasible for every mass budget. -/
theorem infeasible_of_three_centre_violation {M : ℝ} {n : ℕ} {a c d : ℚ}
    (ha : a ∈ FleetRationalBanks.bank n) (hc : c ∈ FleetRationalBanks.bank n)
    (hd : d ∈ FleetRationalBanks.bank n) (r : ℝ)
    (hl : (a : ℝ) = (c : ℝ) - r) (hr : (d : ℝ) = (c : ℝ) + r)
    (hv : (2 * Real.exp (-r^2/4) + 2) / ((n : ℝ) + 1) <
      2 * Real.exp (-r^2/4) * (FleetFullLineArithmetic.rhs (gauss 1 (c : ℝ))).re
        - (FleetFullLineArithmetic.rhs (gauss 1 (a : ℝ))).re
        - (FleetFullLineArithmetic.rhs (gauss 1 (d : ℝ))).re) :
    ¬ FleetRationalBankCriterion.Feasible 1 M n :=
  fun hf => (not_lt_of_ge (three_centre_of_feasible hf ha hc hd r hl hr)) hv

end FleetThreeCentreInequality
