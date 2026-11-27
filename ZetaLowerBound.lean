import Mathlib
import ZetaGrowth

/-!
# ZetaLowerBound — a quantitative lower bound for `ζ` to the right of the strip

**Proven (unconditionally):**

* `norm_zeta_eq_exp_tsum_logTerm`: for `Re s > 1`,
  `‖ζ s‖ = exp (Σ_p -log ‖1 - p^{-s}‖)` (real part of Mathlib's `riemannZeta_eulerProduct_exp_log`).
* `logTerm_two_le`: the termwise Euler-factor inequality
  `-log(1 - p^{-2σ}) ≤ -log ‖1 - p^{-s}‖ - log(1 - p^{-σ})`, `σ = Re s`, from
  `‖1 - p^{-s}‖ ≤ 1 + p^{-σ}` and `1 - p^{-2σ} = (1 - p^{-σ})(1 + p^{-σ})`.
* `norm_zeta_two_re_le_mul`: `ζ(2σ) ≤ ‖ζ s‖ · ζ(σ)` for `Re s = σ > 1`.
* `norm_zeta_ge_of_one_lt_re`: the classical bound **`ζ(2σ)/ζ(σ) ≤ ‖ζ s‖`** for `Re s = σ > 1`
  (`ζ(x)` for real `x > 1` written as `‖riemannZeta x‖`, a positive real).
* `one_le_norm_zeta_real`: `1 ≤ ζ(x)` for real `x > 1`.
* `norm_zeta_three_halves_le_three`: `ζ(3/2) ≤ 3` (constant `K = 3`, via the telescoping
  `p`-series bound `ZetaGrowth.tsum_add_one_rpow_le`).
* `norm_zeta_three_halves_ge`: **`1/3 ≤ ‖ζ(3/2 + it)‖`** for every real `t` — the `|f(c)| ≥ 1`-type
  input for Jensen's zero-counting corollary (any positive constant suffices there).

**Hypothesis-dependent:** nothing. **Not proven:** nothing beyond the stated targets; the
constant `3` for `ζ(3/2)` is clean, not sharp (`ζ(3/2) ≈ 2.612`).
-/

noncomputable section

open Complex

namespace ZetaLowerBound

/-! ## Euler-factor bookkeeping -/

/-- `‖p^{-s}‖ = p^{-Re s}` for a prime `p`. -/
theorem norm_prime_cpow_neg (p : Nat.Primes) (s : ℂ) :
    ‖(p : ℂ) ^ (-s)‖ = ((p : ℕ) : ℝ) ^ (-s.re) := by
  rw [norm_natCast_cpow_of_pos p.prop.pos, neg_re]

/-- `Σ_p p^{-x}` converges over the primes for real `x > 1`. -/
theorem summable_primes_rpow {x : ℝ} (hx : 1 < x) :
    Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-x) :=
  (Real.summable_nat_rpow.mpr (by linarith)).comp_injective Nat.Primes.coe_nat_injective

/-- `p^{-x} < 1` for a prime `p` and `x > 0`. -/
theorem prime_rpow_neg_lt_one (p : Nat.Primes) {x : ℝ} (hx : 0 < x) :
    ((p : ℕ) : ℝ) ^ (-x) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (by linarith)

/-- `0 < p^{-x}` for a prime `p`. -/
theorem prime_rpow_neg_pos (p : Nat.Primes) (x : ℝ) : 0 < ((p : ℕ) : ℝ) ^ (-x) :=
  Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _

/-- The complex logarithms of the Euler factors are summable for `Re s > 1`. -/
theorem summable_neg_log_one_sub {s : ℂ} (hs : 1 < s.re) :
    Summable fun p : Nat.Primes => -Complex.log (1 - (p : ℂ) ^ (-s)) := by
  have hf : Summable fun p : Nat.Primes => (p : ℂ) ^ (-s) := by
    refine Summable.of_norm ?_
    simp_rw [norm_prime_cpow_neg]
    exact summable_primes_rpow hs
  exact hf.clog_one_sub.neg

/-- The real log-term `-log ‖1 - p^{-s}‖` of the Euler product. -/
def logTerm (s : ℂ) (p : Nat.Primes) : ℝ := -Real.log ‖(1 : ℂ) - (p : ℂ) ^ (-s)‖

/-- `-Re log(1 - p^{-s}) = logTerm s p`. -/
theorem re_neg_log_eq_logTerm (s : ℂ) (p : Nat.Primes) :
    (-Complex.log (1 - (p : ℂ) ^ (-s))).re = logTerm s p := by
  rw [neg_re, log_re, logTerm]

/-- The real log-terms are summable for `Re s > 1`. -/
theorem summable_logTerm {s : ℂ} (hs : 1 < s.re) : Summable (logTerm s) := by
  have h := (Complex.hasSum_re (summable_neg_log_one_sub hs).hasSum).summable
  exact h.congr fun p => re_neg_log_eq_logTerm s p

/-- **Log form of the Euler product for the norm:** for `Re s > 1`,
`‖ζ s‖ = exp (Σ_p -log ‖1 - p^{-s}‖)`. -/
theorem norm_zeta_eq_exp_tsum_logTerm {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ = Real.exp (∑' p : Nat.Primes, logTerm s p) := by
  rw [← riemannZeta_eulerProduct_exp_log hs, Complex.norm_exp,
    re_tsum (summable_neg_log_one_sub hs)]
  congr 1
  exact tsum_congr fun p => re_neg_log_eq_logTerm s p

/-- For real `x`, the Euler factor `1 - p^{-x}` is the real number `1 - p^{-x}`. -/
theorem one_sub_prime_cpow_ofReal (p : Nat.Primes) (x : ℝ) :
    (1 : ℂ) - (p : ℂ) ^ (-(x : ℂ)) = ((1 - ((p : ℕ) : ℝ) ^ (-x) : ℝ) : ℂ) := by
  have : ((p : ℕ) : ℂ) ^ (-(x : ℂ)) = ((((p : ℕ) : ℝ) ^ (-x) : ℝ) : ℂ) := by
    rw [ofReal_cpow (Nat.cast_nonneg _), ofReal_neg, ofReal_natCast]
  rw [this]
  push_cast
  ring

/-- For real `x > 0`, `logTerm x p = -log (1 - p^{-x})`. -/
theorem logTerm_ofReal {x : ℝ} (hx : 0 < x) (p : Nat.Primes) :
    logTerm (x : ℂ) p = -Real.log (1 - ((p : ℕ) : ℝ) ^ (-x)) := by
  rw [logTerm, one_sub_prime_cpow_ofReal, norm_real, Real.norm_of_nonneg]
  linarith [prime_rpow_neg_lt_one p hx]

/-! ## The termwise inequality and the classical bound `ζ(2σ)/ζ(σ) ≤ ‖ζ s‖` -/

/-- **Termwise Euler-factor inequality.** With `σ = Re s > 1`,
`-log(1 - p^{-2σ}) ≤ -log ‖1 - p^{-s}‖ + (-log(1 - p^{-σ}))`. -/
theorem logTerm_two_le {s : ℂ} (hs : 1 < s.re) (p : Nat.Primes) :
    logTerm ((2 * s.re : ℝ) : ℂ) p ≤ logTerm s p + logTerm (s.re : ℂ) p := by
  have hσ : 0 < s.re := by linarith
  have ha0 : 0 < ((p : ℕ) : ℝ) ^ (-s.re) := prime_rpow_neg_pos p _
  have ha1 : ((p : ℕ) : ℝ) ^ (-s.re) < 1 := prime_rpow_neg_lt_one p hσ
  have h2 : ((p : ℕ) : ℝ) ^ (-(2 * s.re)) = (((p : ℕ) : ℝ) ^ (-s.re)) ^ 2 := by
    rw [← Real.rpow_two, ← Real.rpow_mul (Nat.cast_nonneg _)]
    ring_nf
  rw [logTerm_ofReal (by linarith), logTerm_ofReal hσ, h2]
  have hn : ‖(1 : ℂ) - (p : ℂ) ^ (-s)‖ ≤ 1 + ((p : ℕ) : ℝ) ^ (-s.re) := by
    calc ‖(1 : ℂ) - (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ := norm_sub_le _ _
      _ = 1 + ((p : ℕ) : ℝ) ^ (-s.re) := by rw [norm_one, norm_prime_cpow_neg]
  have hpos : 0 < ‖(1 : ℂ) - (p : ℂ) ^ (-s)‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    intro h
    have := congrArg norm h
    rw [norm_one, norm_prime_cpow_neg] at this
    linarith
  have hlog : Real.log ‖(1 : ℂ) - (p : ℂ) ^ (-s)‖ ≤ Real.log (1 + ((p : ℕ) : ℝ) ^ (-s.re)) :=
    Real.log_le_log hpos hn
  have hsq : 1 - (((p : ℕ) : ℝ) ^ (-s.re)) ^ 2
      = (1 - ((p : ℕ) : ℝ) ^ (-s.re)) * (1 + ((p : ℕ) : ℝ) ^ (-s.re)) := by ring
  rw [hsq, Real.log_mul (by linarith) (by linarith)]
  unfold logTerm
  linarith

/-- **Product form:** `ζ(2σ) ≤ ‖ζ s‖ · ζ(σ)` for `σ = Re s > 1`. -/
theorem norm_zeta_two_re_le_mul {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta ((2 * s.re : ℝ) : ℂ)‖ ≤ ‖riemannZeta s‖ * ‖riemannZeta (s.re : ℂ)‖ := by
  have h2 : 1 < ((2 * s.re : ℝ) : ℂ).re := by rw [ofReal_re]; linarith
  have h1 : 1 < ((s.re : ℝ) : ℂ).re := by rw [ofReal_re]; exact hs
  rw [norm_zeta_eq_exp_tsum_logTerm h2, norm_zeta_eq_exp_tsum_logTerm hs,
    norm_zeta_eq_exp_tsum_logTerm h1, ← Real.exp_add, Real.exp_le_exp,
    ← (summable_logTerm hs).tsum_add (summable_logTerm h1)]
  exact Summable.tsum_le_tsum (logTerm_two_le hs) (summable_logTerm h2)
    ((summable_logTerm hs).add (summable_logTerm h1))

/-- `ζ(x) > 0` (as `‖riemannZeta x‖`) for real `x > 1`. -/
theorem norm_zeta_real_pos {x : ℝ} (hx : 1 < x) : 0 < ‖riemannZeta (x : ℂ)‖ := by
  rw [norm_zeta_eq_exp_tsum_logTerm (by rw [ofReal_re]; exact hx)]
  exact Real.exp_pos _

/-- `1 ≤ ζ(x)` for real `x > 1`: every Euler log-term `-log(1 - p^{-x})` is nonnegative. -/
theorem one_le_norm_zeta_real {x : ℝ} (hx : 1 < x) : 1 ≤ ‖riemannZeta (x : ℂ)‖ := by
  rw [norm_zeta_eq_exp_tsum_logTerm (by rw [ofReal_re]; exact hx)]
  apply Real.one_le_exp
  refine tsum_nonneg fun p => ?_
  rw [logTerm_ofReal (by linarith)]
  have h1 := prime_rpow_neg_lt_one p (by linarith : 0 < x)
  have h0 := prime_rpow_neg_pos p x
  have := Real.log_nonpos (by linarith) (by linarith : 1 - ((p : ℕ) : ℝ) ^ (-x) ≤ 1)
  linarith

/-- **Classical lower bound to the right of the strip:** for `Re s = σ > 1`,
`ζ(2σ) / ζ(σ) ≤ ‖ζ s‖`, where `ζ(x) = ‖riemannZeta x‖` for real `x > 1`. -/
theorem norm_zeta_ge_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta ((2 * s.re : ℝ) : ℂ)‖ / ‖riemannZeta (s.re : ℂ)‖ ≤ ‖riemannZeta s‖ := by
  rw [div_le_iff₀ (norm_zeta_real_pos hs)]
  exact norm_zeta_two_re_le_mul hs

/-- Weaker but self-contained form: `‖ζ s‖ ≥ 1 / ζ(Re s)` for `Re s > 1`. -/
theorem inv_norm_zeta_re_le_norm_zeta {s : ℂ} (hs : 1 < s.re) :
    1 / ‖riemannZeta (s.re : ℂ)‖ ≤ ‖riemannZeta s‖ := by
  refine le_trans ?_ (norm_zeta_ge_of_one_lt_re hs)
  exact div_le_div_of_nonneg_right (one_le_norm_zeta_real (by linarith)) (norm_zeta_real_pos hs).le

/-! ## Numerics at `Re s = 3/2` -/

/-- `ζ(3/2) ≤ 3`: `Σ_{n≥1} n^{-3/2} ≤ 1 + 1/(1/2)` by the telescoping bound in `ZetaGrowth`. -/
theorem norm_zeta_three_halves_le_three : ‖riemannZeta ((3 / 2 : ℝ) : ℂ)‖ ≤ 3 := by
  rw [ZetaGrowth.norm_zeta_real_eq (by norm_num)]
  have hs : Summable fun n : ℕ => 1 / (n : ℝ) ^ (3 / 2 : ℝ) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  rw [hs.tsum_eq_zero_add]
  have h0 : (1 : ℝ) / ((0 : ℕ) : ℝ) ^ (3 / 2 : ℝ) = 0 := by
    rw [Nat.cast_zero, Real.zero_rpow (by norm_num), div_zero]
  have hshift : ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ)) ^ (3 / 2 : ℝ)
      = ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
    refine tsum_congr fun n => ?_
    rw [Real.rpow_neg (by positivity), one_div]
    push_cast
    rfl
  have hK := ZetaGrowth.K_le_three
  rw [ZetaGrowth.K] at hK
  rw [h0, zero_add, hshift]
  exact hK

/-- **Numeric corollary:** `1/3 ≤ ‖ζ(3/2 + it)‖` for every real `t`
(from `ζ(3)/ζ(3/2) ≤ ‖ζ(3/2 + it)‖`, `ζ(3) ≥ 1`, `ζ(3/2) ≤ 3`). -/
theorem norm_zeta_three_halves_ge (t : ℝ) :
    (1 / 3 : ℝ) ≤ ‖riemannZeta (3 / 2 + t * I)‖ := by
  have hre : (3 / 2 + t * I : ℂ).re = 3 / 2 := by simp
  have hs : 1 < (3 / 2 + t * I : ℂ).re := by rw [hre]; norm_num
  have h := norm_zeta_ge_of_one_lt_re hs
  rw [hre] at h
  have h3 : 1 ≤ ‖riemannZeta ((2 * (3 / 2 : ℝ) : ℝ) : ℂ)‖ :=
    one_le_norm_zeta_real (by norm_num)
  have hK := norm_zeta_three_halves_le_three
  have hpos := norm_zeta_real_pos (by norm_num : (1 : ℝ) < 3 / 2)
  refine le_trans ?_ h
  rw [le_div_iff₀ hpos]
  nlinarith

/-- Restatement on the line `Re s = 3/2`: `1/3 ≤ ‖ζ s‖`. -/
theorem norm_zeta_ge_third_of_re_eq_three_halves {s : ℂ} (hs : s.re = 3 / 2) :
    (1 / 3 : ℝ) ≤ ‖riemannZeta s‖ := by
  have : s = 3 / 2 + s.im * I := by
    apply Complex.ext <;> simp [hs]
  rw [this]
  exact norm_zeta_three_halves_ge s.im

end ZetaLowerBound

end
