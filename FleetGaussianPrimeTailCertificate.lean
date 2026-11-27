import FleetGaussianDictionaryMember
import FleetDigammaGrowth
import Mathlib

/-!
# A proved Gaussian prime-tail bound at width one

For `gauss 1 q`, uniformly in the real center `q`, the exact prime term at
`n ≥ 1000` has norm at most `n⁻⁵`. Indeed, `log n ≥ 6` gives
`exp (-(log n)^2) ≤ n⁻⁶`; the von Mangoldt and inverse-square-root factors
have product at most `n`. Comparing the resulting fifth-power tail with the
proved inverse-square tail gives error at most `N⁻⁴` after retaining all integer
locations through `N ≥ 1000`.

In particular the cutoff 1000 has norm error at most `10⁻¹²` for either prime
sum in `FleetFullLineArithmetic.rhs`, and at most `2 * 10⁻¹²` for their sum.
These are analytic theorems about the exact infinite prime sums. They assume
no externally supplied enclosure. The retained finite sums, pole evaluations,
and archimedean integral are not evaluated by this module; no complete Gaussian
residual certificate or finite-stage feasibility statement is asserted.
-/

noncomputable section
namespace FleetGaussianPrimeTailCertificate
open GaussianTest FleetPrimeFunctionalBound
open scoped ArithmeticFunction

/-- A simple proved exponential bound supplies the logarithmic threshold. -/
lemma six_le_log_of_ge_1000 {n : ℕ} (hn : 1000 ≤ n) :
    (6 : ℝ) ≤ Real.log n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn' : (1000 : ℝ) ≤ n := by exact_mod_cast hn
  have he1 : Real.exp 1 ≤ (3 : ℝ) := Real.exp_one_lt_d9.le.trans (by norm_num)
  have he6 : Real.exp (6 : ℝ) ≤ (3 : ℝ)^6 := by
    calc
      _ = Real.exp 1 ^ (6 : ℕ) := by rw [Real.exp_one_pow]; norm_num
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos 1).le he1 _
  apply Real.exp_le_exp.mp
  rw [Real.exp_log hn0]
  norm_num at he6
  linarith

/-- Beyond the threshold, the Gaussian in `log n` is bounded by the sixth power. -/
lemma gaussian_log_le_inv_sixth {n : ℕ} (hn : 1000 ≤ n) :
    Real.exp (-(Real.log n)^2) ≤ 1/(n : ℝ)^6 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hl := six_le_log_of_ge_1000 hn
  calc
    _ ≤ Real.exp (-(6*Real.log n)) := Real.exp_le_exp.mpr (by nlinarith)
    _ = _ := by
      rw [Real.exp_neg]
      have he : Real.exp ((6 : ℕ)*Real.log (n : ℝ)) = (n : ℝ)^6 := by
        rw [Real.exp_nat_mul, Real.exp_log hn0]
      norm_num at he
      rw [he, one_div]

/-- The bound includes the exact von Mangoldt and complex inverse-square-root
factors of the existing prime-sum definition, uniformly in the center. -/
lemma norm_gaussian_prime_term_le_inv_fifth (q : ℝ) {n : ℕ} (hn : 1000 ≤ n) :
    ‖term (gauss 1 q) n‖ ≤ 1/(n : ℝ)^5 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hΛ : Λ n ≤ (n : ℝ) :=
    ArithmeticFunction.vonMangoldt_le_log.trans (by linarith [Real.log_le_sub_one_of_pos hn0])
  have hΛ0 : (0 : ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  rw [term, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hΛ0, GaussianTest.norm_gauss]
  simp only [neg_mul, one_mul]
  calc
    Λ n * ‖(n : ℂ)^(-(1/2) : ℂ)‖ * Real.exp (-(Real.log n)^2)
      ≤ (n : ℝ) * (1/(n : ℝ)^6) := by
        apply mul_le_mul _ (gaussian_log_le_inv_sixth hn) (Real.exp_pos _).le hn0.le
        calc
          Λ n * ‖(n : ℂ)^(-(1/2) : ℂ)‖ ≤ Λ n * 1 :=
            mul_le_mul_of_nonneg_left (GaussianTraceFormula.norm_natCast_cpow_neg_half_le n) hΛ0
          _ ≤ _ := by simpa using hΛ
    _ = _ := by field_simp

/-- Domination suitable for the existing inverse-square tail estimate. -/
lemma inv_fifth_le_cube_mul_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    1/b^5 ≤ (1/a^3)*(1/b^2) := by
  have hb : 0 < b := ha.trans_le hab
  calc
    _ = (1/b^3)*(1/b^2) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ ha.le hab 3))
      (by positivity)

/-- Actual absolute convergence of the width-one Gaussian prime series. -/
lemma summable_gaussian_prime_terms (q : ℝ) : Summable (term (gauss 1 q)) := by
  obtain ⟨E,hE,hg⟩ := FleetGaussianDictionaryMember.exists_bound (by norm_num : (0 : ℝ) < 1) q
  exact FleetPrimeFunctionalBound.summable_terms hE hg.zero

/-- The entire infinite tail beyond `N` has a rational-power norm bound. -/
lemma norm_gaussian_prime_tail_le (q : ℝ) {N : ℕ} (hN : 1000 ≤ N) :
    ‖∑' k : ℕ, term (gauss 1 q) (k+N+1)‖ ≤ 1/(N : ℝ)^4 := by
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hs : Summable (fun k : ℕ => term (gauss 1 q) (k+N+1)) := by
    simpa only [Nat.add_assoc] using
      (summable_nat_add_iff (N+1)).mpr (summable_gaussian_prime_terms q)
  have hu0 : Summable (fun k : ℕ => 1/((N : ℝ)+k+1)^2) := by
    have hh := (summable_nat_add_iff (N+1)).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
    simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using hh
  have hu := hu0.mul_left (1/(N : ℝ)^3)
  calc
    _ ≤ ∑' k : ℕ, ‖term (gauss 1 q) (k+N+1)‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' k : ℕ, (1/(N : ℝ)^3)*(1/((N : ℝ)+k+1)^2) := by
      apply Summable.tsum_le_tsum _ hs.norm hu
      intro k
      have ht := norm_gaussian_prime_term_le_inv_fifth q (show 1000 ≤ k+N+1 by omega)
      have hk : (N : ℝ) ≤ N+k+1 := by linarith [show (0 : ℝ) ≤ k by positivity]
      have hb := inv_fifth_le_cube_mul_sq hNr hk
      exact ht.trans (by simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using hb)
    _ = (1/(N : ℝ)^3)*(∑' k : ℕ, 1/((N : ℝ)+k+1)^2) := by rw [tsum_mul_left]
    _ ≤ (1/(N : ℝ)^3)*(1/(N : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (FleetDigammaGrowth.tsum_inv_sq_tail_le N hNpos) (by positivity)
    _ = _ := by field_simp

/-- Retain every integer location from zero through `N`, so all prime powers
at most `N` are included with the existing von Mangoldt normalization. -/
def partialSum (N : ℕ) (q : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (N+1), term (gauss 1 q) n

/-- Absolute convergence identifies the omitted tail with the exact truncation
error in `GammaExplicitFormula.primeSum`. -/
lemma primeSum_sub_partial_eq (q : ℝ) (N : ℕ) :
    GammaExplicitFormula.primeSum (gauss 1 q) - partialSum N q =
      ∑' k : ℕ, term (gauss 1 q) (k+N+1) := by
  change (∑' n : ℕ, term (gauss 1 q) n) -
    (∑ n ∈ Finset.range (N+1), term (gauss 1 q) n) = _
  rw [← Summable.sum_add_tsum_nat_add (N+1) (summable_gaussian_prime_terms q)]
  simp only [Nat.add_assoc, add_sub_cancel_left]

/-- Quantitative truncation of the exact prime sum, for every real center. -/
theorem primeSum_truncation_le (q : ℝ) {N : ℕ} (hN : 1000 ≤ N) :
    ‖GammaExplicitFormula.primeSum (gauss 1 q) - partialSum N q‖ ≤
      1/(N : ℝ)^4 := by
  rw [primeSum_sub_partial_eq]
  exact norm_gaussian_prime_tail_le q hN

/-- The concrete cutoff 1000 has error at most one trillionth. -/
theorem primeSum_truncation_1000_le (q : ℝ) :
    ‖GammaExplicitFormula.primeSum (gauss 1 q) - partialSum 1000 q‖ ≤
      (1/1000000000000 : ℝ) := by
  convert primeSum_truncation_le q (le_refl 1000) using 1; norm_num

/-- Reflection negates the Gaussian modulation center. -/
lemma reflect_gauss_one (q : ℝ) : GammaExplicitFormula.reflect (gauss 1 q) = gauss 1 (-q) := by
  funext u
  simp only [GammaExplicitFormula.reflect, gauss]
  congr 1
  push_cast
  ring

/-- The reflected prime sum obeys the same concrete error bound. -/
theorem reflected_primeSum_truncation_1000_le (q : ℝ) :
    ‖GammaExplicitFormula.primeSum (GammaExplicitFormula.reflect (gauss 1 q)) -
      partialSum 1000 (-q)‖ ≤ (1/1000000000000 : ℝ) := by
  rw [reflect_gauss_one]
  exact primeSum_truncation_1000_le (-q)

/-- The sum of the two prime terms in the full-line arithmetic functional has
error at most two trillionths at cutoff 1000. -/
theorem two_primeSums_truncation_1000_le (q : ℝ) :
    ‖(GammaExplicitFormula.primeSum (gauss 1 q) +
        GammaExplicitFormula.primeSum (GammaExplicitFormula.reflect (gauss 1 q))) -
      (partialSum 1000 q + partialSum 1000 (-q))‖ ≤
      (1/500000000000 : ℝ) := by
  have he : (GammaExplicitFormula.primeSum (gauss 1 q) +
        GammaExplicitFormula.primeSum (GammaExplicitFormula.reflect (gauss 1 q))) -
      (partialSum 1000 q + partialSum 1000 (-q)) =
      (GammaExplicitFormula.primeSum (gauss 1 q) - partialSum 1000 q) +
      (GammaExplicitFormula.primeSum (GammaExplicitFormula.reflect (gauss 1 q)) -
        partialSum 1000 (-q)) := by ring
  rw [he]
  exact (norm_add_le _ _).trans (by linarith [primeSum_truncation_1000_le q,
    reflected_primeSum_truncation_1000_le q])

end FleetGaussianPrimeTailCertificate
