import Mathlib

/-!
Proof-producing elementary enclosures for the finite Gaussian calculation.
The rational endpoints supplied to these rules are checked by Lean; none of
the rules accepts an external numerical answer as evidence about a real value.
-/

namespace FleetElementaryIntervalCertificate

def expPolynomial (n : ℕ) (x : ℚ) : ℚ :=
  ∑ k ∈ Finset.range n, x ^ k / k.factorial

def expRemainder (n : ℕ) (x : ℚ) : ℚ :=
  |x| ^ n * ((n + 1 : ℕ) / ((n.factorial : ℚ) * n))

/-- A rational Taylor calculation certifies an exponential at a small input. -/
theorem exp_small {x l u : ℚ} {n : ℕ} (hn : 0 < n) (hx : |x| ≤ 1)
    (hl : l ≤ expPolynomial n x - expRemainder n x)
    (hu : expPolynomial n x + expRemainder n x ≤ u) :
    (l : ℝ) ≤ Real.exp x ∧ Real.exp x ≤ (u : ℝ) := by
  have hx' : |(x : ℝ)| ≤ 1 := by exact_mod_cast hx
  have h := Real.exp_bound hx' hn
  have hp : (expPolynomial n x : ℝ) =
      ∑ k ∈ Finset.range n, (x : ℝ)^k / k.factorial := by
    simp [expPolynomial]
  have hr : (expRemainder n x : ℝ) =
      |(x : ℝ)|^n * ((n.succ : ℝ) / ((n.factorial : ℝ)*n)) := by
    simp [expRemainder, Nat.succ_eq_add_one]
  rw [← hp, ← hr] at h
  have hl' : (l : ℝ) ≤ (expPolynomial n x : ℝ) - (expRemainder n x : ℝ) := by
    exact_mod_cast hl
  have hu' : (expPolynomial n x : ℝ) + (expRemainder n x : ℝ) ≤ (u : ℝ) := by
    exact_mod_cast hu
  obtain ⟨h1, h2⟩ := abs_le.mp h
  constructor <;> linarith

/-- Doubling the argument only requires rational squaring and outward rounding. -/
theorem exp_double {x : ℝ} {l u L U : ℚ}
    (h : (l : ℝ) ≤ Real.exp x ∧ Real.exp x ≤ (u : ℝ))
    (hl : 0 ≤ l) (hL : L ≤ l^2) (hU : u^2 ≤ U) :
    (L : ℝ) ≤ Real.exp (2*x) ∧ Real.exp (2*x) ≤ (U : ℝ) := by
  have he : Real.exp (2*x) = Real.exp x ^ 2 := by
    simpa using Real.exp_nat_mul x 2
  rw [he]
  have hl' : (0 : ℝ) ≤ l := by exact_mod_cast hl
  have hL' : (L : ℝ) ≤ (l : ℝ)^2 := by exact_mod_cast hL
  have hU' : (u : ℝ)^2 ≤ (U : ℝ) := by exact_mod_cast hU
  have hu' : (0 : ℝ) ≤ u := (Real.exp_pos x).le.trans h.2
  constructor
  · exact hL'.trans (pow_le_pow_left₀ hl' h.1 2)
  · exact (pow_le_pow_left₀ (Real.exp_pos x).le h.2 2).trans hU'

/-- Exponential endpoint proofs give a logarithm enclosure. -/
theorem log_of_exp {x l u : ℝ} (hx : 0 < x)
    (hl : Real.exp l ≤ x) (hu : x ≤ Real.exp u) :
    l ≤ Real.log x ∧ Real.log x ≤ u :=
  ⟨(Real.le_log_iff_exp_le hx).mpr hl, (Real.log_le_iff_le_exp hx).mpr hu⟩

/-- The small-input cosine enclosure has a proved fourth-order remainder. -/
theorem cos_small {x l u : ℚ} (hx : |x| ≤ 1)
    (hl : l ≤ 1 - x^2/2 - |x|^4*(5/96))
    (hu : 1 - x^2/2 + |x|^4*(5/96) ≤ u) :
    (l : ℝ) ≤ Real.cos x ∧ Real.cos x ≤ (u : ℝ) := by
  have h := Real.cos_bound (show |(x : ℝ)| ≤ 1 by exact_mod_cast hx)
  have hl' : (l : ℝ) ≤ 1 - (x : ℝ)^2/2 - |(x : ℝ)|^4*(5/96) := by
    have hcast := (show (l : ℝ) ≤ ((1 - x^2/2 - |x|^4*(5/96) : ℚ) : ℝ) from by exact_mod_cast hl)
    norm_num only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
      Rat.cast_abs, Rat.cast_one, Rat.cast_ofNat] at hcast
    exact hcast
  have hu' : 1 - (x : ℝ)^2/2 + |(x : ℝ)|^4*(5/96) ≤ (u : ℝ) := by
    have hcast := (show (((1 - x^2/2 + |x|^4*(5/96)) : ℚ) : ℝ) ≤ (u : ℝ) from by exact_mod_cast hu)
    norm_num only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
      Rat.cast_pow, Rat.cast_abs, Rat.cast_one, Rat.cast_ofNat] at hcast
    exact hcast
  obtain ⟨h1, h2⟩ := abs_le.mp h
  constructor <;> linarith

/-- Propagate a cosine enclosure through the double-angle identity, including
intervals that cross zero. The two square bounds are exact rational checks. -/
theorem cos_double {x : ℝ} {l u a b L U : ℚ}
    (h : (l : ℝ) ≤ Real.cos x ∧ Real.cos x ≤ (u : ℝ))
    (ha : a ≤ l^2 ∧ a ≤ u^2 ∧ (l ≤ 0 → 0 ≤ u → a ≤ 0))
    (hb : l^2 ≤ b ∧ u^2 ≤ b)
    (hL : L ≤ 2*a-1) (hU : 2*b-1 ≤ U) :
    (L : ℝ) ≤ Real.cos (2*x) ∧ Real.cos (2*x) ≤ (U : ℝ) := by
  have ha1 : (a : ℝ) ≤ (l : ℝ)^2 := by exact_mod_cast ha.1
  have ha2 : (a : ℝ) ≤ (u : ℝ)^2 := by exact_mod_cast ha.2.1
  have hb1 : (l : ℝ)^2 ≤ (b : ℝ) := by exact_mod_cast hb.1
  have hb2 : (u : ℝ)^2 ≤ (b : ℝ) := by exact_mod_cast hb.2
  have hL' : (L : ℝ) ≤ 2*(a : ℝ)-1 := by exact_mod_cast hL
  have hU' : 2*(b : ℝ)-1 ≤ (U : ℝ) := by exact_mod_cast hU
  have hslo : (a : ℝ) ≤ Real.cos x ^ 2 := by
    by_cases hl : 0 ≤ l
    · have hl' : (0 : ℝ) ≤ l := by exact_mod_cast hl
      exact ha1.trans (pow_le_pow_left₀ hl' h.1 2)
    · by_cases hu : u ≤ 0
      · have hu' : (u : ℝ) ≤ 0 := by exact_mod_cast hu
        nlinarith [sq_nonneg (Real.cos x - (u : ℝ))]
      · have ha0 : (a : ℝ) ≤ 0 := by
          exact_mod_cast ha.2.2 (le_of_not_ge hl) (le_of_not_ge hu)
        exact ha0.trans (sq_nonneg _)
  have hshi : Real.cos x ^ 2 ≤ (b : ℝ) := by
    by_cases hx : 0 ≤ Real.cos x
    · exact (pow_le_pow_left₀ hx h.2 2).trans hb2
    · have hx' : Real.cos x ≤ 0 := le_of_not_ge hx
      nlinarith [sq_nonneg ((l : ℝ) - Real.cos x)]
  rw [Real.cos_two_mul]
  constructor <;> linarith

end FleetElementaryIntervalCertificate
