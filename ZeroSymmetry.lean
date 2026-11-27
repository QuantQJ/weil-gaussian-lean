import Mathlib
import Reduction

/-!
# Functional-equation symmetry of the nontrivial zeros

The set of nontrivial zeros of `ζ` (in the sense of `Reduction.IsNontrivialZero`,
which is exactly the quantifier of Mathlib's `RiemannHypothesis`) is invariant
under `ρ ↦ 1 - ρ`.

**Proven (unconditionally, no custom axioms):**

* `bernoulli_two_mul_ne_zero` — `B_{2k} ≠ 0` for `k ≥ 1`, via Euler's formula
  `ζ(2k) = (−1)^{k+1} 2^{2k−1} π^{2k} B_{2k} / (2k)!` and `ζ(2k) ≠ 0`.
* `riemannZeta_neg_odd_ne_zero` — `ζ(−(2m+1)) ≠ 0`, via
  `ζ(−n) = (−1)^n B_{n+1}/(n+1)`.
* `ne_neg_nat_of_isNontrivialZero` — a nontrivial zero is not in `−ℕ`
  (`ρ = 0`: `ζ(0) = −1/2`; even negative: excluded as trivial; odd negative:
  the previous lemma).
* `isNontrivialZero_one_sub` — `IsNontrivialZero ρ → IsNontrivialZero (1 − ρ)`,
  from `riemannZeta_one_sub` and `riemannZeta_ne_zero_of_one_le_re`.
* `isNontrivialZero_iff_one_sub` — the biconditional.

Nothing is left unproven in this module.
-/

noncomputable section
open Complex

namespace ZeroSymmetry

open Reduction

/-- The even-index Bernoulli numbers `B_{2k}` (`k ≥ 1`) are nonzero. This is read
off Euler's formula for `ζ(2k)` together with the nonvanishing of `ζ` on
`re > 1`. -/
theorem bernoulli_two_mul_ne_zero {k : ℕ} (hk : k ≠ 0) : bernoulli (2 * k) ≠ 0 := by
  intro h
  have hζ := riemannZeta_two_mul_nat hk
  rw [h] at hζ
  simp only [Rat.cast_zero, mul_zero, zero_div] at hζ
  have hre : 1 < ((2 * k : ℕ) : ℂ).re := by
    rw [Complex.natCast_re]
    exact_mod_cast (by omega : 1 < 2 * k)
  exact riemannZeta_ne_zero_of_one_lt_re hre (by exact_mod_cast hζ)

/-- `ζ` does not vanish at the negative odd integers `−(2m+1)`. -/
theorem riemannZeta_neg_odd_ne_zero (m : ℕ) : riemannZeta (-(2 * m + 1 : ℂ)) ≠ 0 := by
  have h := riemannZeta_neg_nat_eq_bernoulli (2 * m + 1)
  have hcast : (-(2 * m + 1 : ℂ)) = -((2 * m + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [hcast, h]
  have hB : bernoulli (2 * m + 1 + 1) ≠ 0 := by
    have : 2 * m + 1 + 1 = 2 * (m + 1) := by ring
    rw [this]
    exact bernoulli_two_mul_ne_zero (Nat.succ_ne_zero m)
  have hB' : (bernoulli (2 * m + 1 + 1) : ℂ) ≠ 0 := by exact_mod_cast hB
  have hden : (((2 * m + 1 : ℕ) : ℂ) + 1) ≠ 0 := by
    have : (((2 * m + 1 : ℕ) : ℂ) + 1) = ((2 * m + 1 + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this]
    exact_mod_cast Nat.succ_ne_zero (2 * m + 1)
  exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hB') hden

/-- A nontrivial zero of `ζ` is not a non-positive integer. -/
theorem ne_neg_nat_of_isNontrivialZero {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    ∀ n : ℕ, ρ ≠ -n := by
  obtain ⟨h0, htriv, _⟩ := hρ
  intro n hn
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · -- ρ = 0, but ζ 0 = -1/2
      rw [hn] at h0
      simp only [Nat.cast_zero, mul_zero, neg_zero, riemannZeta_zero] at h0
      norm_num at h0
    · -- ρ = -2 m with m ≥ 1: a trivial zero, excluded
      obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hm)
      apply htriv
      refine ⟨m', ?_⟩
      rw [hn]; push_cast; ring
  · -- ρ = -(2 m + 1): ζ does not vanish there
    apply riemannZeta_neg_odd_ne_zero m
    rw [← h0, hn]; push_cast; ring_nf

/-- **Functional-equation symmetry.** If `ρ` is a nontrivial zero of `ζ`, so is
`1 − ρ`. -/
theorem isNontrivialZero_one_sub {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    IsNontrivialZero (1 - ρ) := by
  have hnat := ne_neg_nat_of_isNontrivialZero hρ
  obtain ⟨h0, _, h1⟩ := hρ
  refine ⟨?_, ?_, ?_⟩
  · -- ζ(1-ρ) = 2 (2π)^(-ρ) Γ(ρ) cos(πρ/2) ζ(ρ) = 0
    rw [riemannZeta_one_sub hnat h1, h0, mul_zero]
  · -- 1 - ρ = -2(n+1) would force ρ = 2n+3, where ζ ≠ 0
    rintro ⟨n, hn⟩
    have hρeq : ρ = 2 * n + 3 := by linear_combination -hn
    apply riemannZeta_ne_zero_of_one_le_re _ h0
    rw [hρeq]
    simp only [add_re, mul_re, re_ofNat, im_ofNat, natCast_re, natCast_im, mul_zero, sub_zero]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    norm_num
    linarith
  · -- 1 - ρ ≠ 1 since ρ ≠ 0
    intro h
    have hρ0 : ρ = 0 := by linear_combination -h
    exact hnat 0 (by rw [hρ0]; simp)

/-- The nontrivial zeros are exactly symmetric under `ρ ↦ 1 − ρ`. -/
theorem isNontrivialZero_iff_one_sub (ρ : ℂ) :
    IsNontrivialZero ρ ↔ IsNontrivialZero (1 - ρ) := by
  constructor
  · exact isNontrivialZero_one_sub
  · intro h
    have := isNontrivialZero_one_sub h
    rwa [sub_sub_cancel] at this

end ZeroSymmetry

end
