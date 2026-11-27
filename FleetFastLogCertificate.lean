import Mathlib
import FleetRationalInterval

/-!
# A rational series evaluator for logarithms

For `1 ≤ r ≤ 2`, put `z = (r-1)/(r+1)`. The proved logarithm series has
nonnegative terms `2*z^(2*k+1)/(2*k+1)`. Its tail after `n` terms is bounded
by `2*z^(2*n+1)/(1-z^2)`. Eight terms give absolute error at most `2*10⁻⁸`
on the whole reduced interval.

The computable `logAtFast` returns a rational `FleetRationalInterval.Box`.
It halves positive rational arguments until they lie in `[1,2]`, uses this
finite series there, and adds the already proved interval for `log 2`.
`logAtFast_contains` proves its enclosure on `[1,65536]`. No exponential
bisection, unchecked floating-point enclosure, or evaluation axiom is used.
-/

namespace FleetFastLogCertificate
open Finset

/-- The exact odd-power logarithm-series summand. -/
noncomputable def oddTerm (z : ℝ) (k : ℕ) : ℝ :=
  2*(1/(2*(k : ℝ)+1))*z^(2*k+1)

/-- Nonnegative series tails are dominated by a geometric series. -/
lemma odd_tail_bound {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) (n : ℕ) :
    0 ≤ (∑' k : ℕ, oddTerm z (k+n)) ∧
    (∑' k : ℕ, oddTerm z (k+n)) ≤ 2*z^(2*n+1)/(1-z^2) := by
  have ha : |z| < 1 := by rwa [abs_of_nonneg hz]
  have hs : Summable (oddTerm z) := (Real.hasSum_log_sub_log_of_abs_lt_one ha).summable
  have htail := (summable_nat_add_iff n).mpr hs
  have hz2 : z^2 < 1 := by nlinarith
  have hgeo := (summable_geometric_of_lt_one (sq_nonneg z) hz2).mul_left (2*z^(2*n+1))
  constructor
  · exact tsum_nonneg (fun k => by dsimp [oddTerm]; positivity)
  · calc
      _ ≤ ∑' k : ℕ, 2*z^(2*n+1)*(z^2)^k := by
        apply Summable.tsum_le_tsum _ htail hgeo
        intro k
        have hp : z^(2*(k+n)+1) = z^(2*n+1)*(z^2)^k := by
          rw [← pow_mul, ← pow_add]
          congr 1
          omega
        unfold oddTerm
        rw [hp]
        have hd : 1/(2*((k+n : ℕ) : ℝ)+1) ≤ 1 := by
          apply (div_le_one (by positivity)).mpr
          linarith [show (0 : ℝ) ≤ (k+n : ℕ) by positivity]
        calc
          _ ≤ 2*1*(z^(2*n+1)*(z^2)^k) := by gcongr
          _ = _ := by ring
      _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one (sq_nonneg z) hz2]; ring

/-- The real finite approximation after reducing the argument to `[1,2]`. -/
noncomputable def logPolynomial (r : ℝ) (n : ℕ) : ℝ :=
  2*∑ k ∈ range n, ((r-1)/(r+1))^(2*k+1)/((2*k+1 : ℕ) : ℝ)

/-- Reduction to `[1,2]` places the series parameter in `[0,1/3]`. -/
lemma reduced_parameter_bounds {r : ℝ} (hr : 1 ≤ r) (hr2 : r ≤ 2) :
    0 ≤ (r-1)/(r+1) ∧ (r-1)/(r+1) ≤ (1/3 : ℝ) := by
  constructor
  · exact div_nonneg (by linarith) (by linarith)
  · apply (div_le_iff₀ (by linarith : 0 < r+1)).mpr
    linarith

/-- The library power series sums to the exact logarithm of the reduced argument. -/
lemma reduced_log_hasSum {r : ℝ} (hr : 1 ≤ r) (hr2 : r ≤ 2) :
    HasSum (oddTerm ((r-1)/(r+1))) (Real.log r) := by
  let z := (r-1)/(r+1)
  have hz := reduced_parameter_bounds hr hr2
  have hz1 : |z| < 1 := by dsimp [z]; rw [abs_of_nonneg hz.1]; linarith [hz.2]
  have hlog : Real.log (1+z)-Real.log (1-z) = Real.log r := by
    rw [← Real.log_div (by dsimp [z]; linarith [hz.1]) (by dsimp [z]; linarith [hz.2])]
    congr 1
    dsimp [z]
    field_simp
    ring
  have key := Real.hasSum_log_sub_log_of_abs_lt_one hz1
  rw [hlog] at key
  exact key

/-- Explicit error bound for every finite truncation of the odd-power series. -/
theorem logPolynomial_error {r : ℝ} (hr : 1 ≤ r) (hr2 : r ≤ 2) (n : ℕ) :
    |Real.log r-logPolynomial r n| ≤
      2*((r-1)/(r+1))^(2*n+1)/(1-((r-1)/(r+1))^2) := by
  have hs := reduced_log_hasSum hr hr2
  have hz := reduced_parameter_bounds hr hr2
  have ht := odd_tail_bound hz.1 (show (r-1)/(r+1) < 1 by linarith [hz.2]) n
  have hp : logPolynomial r n = ∑ k ∈ range n, oddTerm ((r-1)/(r+1)) k := by
    unfold logPolynomial
    rw [mul_sum]
    apply sum_congr rfl
    intro k _
    unfold oddTerm
    push_cast
    ring
  have he : Real.log r-logPolynomial r n = ∑' k : ℕ, oddTerm ((r-1)/(r+1)) (k+n) := by
    rw [hp, ← hs.tsum_eq, ← Summable.sum_add_tsum_nat_add n hs.summable]
    ring
  rw [he, abs_of_nonneg ht.1]
  exact ht.2

/-- Exact power-of-two scaling; the reduced argument may be enclosed separately. -/
lemma log_scale_pow_two {x : ℝ} (hx : 0 < x) (k : ℕ) :
    Real.log x = (k : ℝ)*Real.log 2 + Real.log (x/2^k) := by
  rw [Real.log_div hx.ne' (by positivity), Real.log_pow]
  ring

/-- Eight terms have absolute error at most two hundred-millionths. -/
lemma logPolynomial_error_eight {r : ℝ} (hr : 1 ≤ r) (hr2 : r ≤ 2) :
    |Real.log r-logPolynomial r 8| ≤ (1/50000000 : ℝ) := by
  have hz := reduced_parameter_bounds hr hr2
  have hz1 : 0 < 1-((r-1)/(r+1))^2 := by nlinarith
  refine (logPolynomial_error hr hr2 8).trans ?_
  have hp := pow_le_pow_left₀ hz.1 hz.2 17
  have hs := pow_le_pow_left₀ hz.1 hz.2 2
  norm_num at hp hs ⊢
  apply (div_le_iff₀ hz1).mpr
  nlinarith

open FleetRationalInterval

/-- A computable rational version of the finite polynomial. -/
def logPolynomialQ (r : ℚ) (n : ℕ) : ℚ :=
  2*∑ k ∈ range n, ((r-1)/(r+1))^(2*k+1)/((2*k+1 : ℕ) : ℚ)

/-- The computable rational geometric-tail bound. -/
def logErrorQ (r : ℚ) (n : ℕ) : ℚ :=
  2*((r-1)/(r+1))^(2*n+1)/(1-((r-1)/(r+1))^2)

/-- The finite polynomial with its explicit rational error on both sides. -/
def reducedLog (r : ℚ) (n : ℕ) : Box :=
  ⟨logPolynomialQ r n-logErrorQ r n, logPolynomialQ r n+logErrorQ r n⟩

lemma logPolynomialQ_cast (r : ℚ) (n : ℕ) :
    ((logPolynomialQ r n : ℚ) : ℝ) = logPolynomial r n := by
  unfold logPolynomialQ logPolynomial
  push_cast
  rfl

lemma logErrorQ_cast (r : ℚ) (n : ℕ) :
    ((logErrorQ r n : ℚ) : ℝ) =
      2*(((r : ℝ)-1)/((r : ℝ)+1))^(2*n+1)/(1-(((r : ℝ)-1)/((r : ℝ)+1))^2) := by
  unfold logErrorQ
  push_cast
  rfl

/-- Soundness of the computable reduced-argument interval. -/
theorem reducedLog_contains (r : ℚ) (n : ℕ) (hr : 1 ≤ r) (hr2 : r ≤ 2) :
    Contains (reducedLog r n) (Real.log r) := by
  have h := abs_le.mp (logPolynomial_error (r := (r : ℝ)) (by exact_mod_cast hr) (by exact_mod_cast hr2) n)
  unfold Contains reducedLog
  dsimp only
  push_cast
  rw [logPolynomialQ_cast, logErrorQ_cast]
  constructor <;> linarith [h.1,h.2]

/-- Reuse the previously kernel-checked enclosure for `log 2`. -/
def logTwoBox : Box := ⟨693147180559/1000000000000, 693147180560/1000000000000⟩

lemma logTwoBox_contains : Contains logTwoBox (Real.log 2) := by
  have h := FleetElementaryNumericalInstances.log_two
  norm_num [Contains, logTwoBox] at h ⊢
  exact h

/-- At most `steps` rational halvings, followed by the eight-term series. -/
def logFast : ℕ → ℚ → Box
  | 0, q => reducedLog q 8
  | steps+1, q => if 2 < q then add logTwoBox (logFast steps (q/2)) else reducedLog q 8

/-- Halving and interval addition preserve the exact logarithm enclosure. -/
theorem logFast_contains (steps : ℕ) (q : ℚ) (hq : 1 ≤ q) (hQ : q ≤ 2^(steps+1)) :
    Contains (logFast steps q) (Real.log q) := by
  induction steps generalizing q with
  | zero =>
    exact reducedLog_contains q 8 hq (by simpa using hQ)
  | succ steps ih =>
    unfold logFast
    split_ifs with hq2
    · have hhalf : q/2 ≤ 2^(steps+1) := by
        rw [div_le_iff₀ (by norm_num : (0 : ℚ) < 2)]
        have hp : (2 : ℚ)^(steps+1+1) = 2^(steps+1)*2 := pow_succ _ _
        simpa only [Nat.succ_eq_add_one, hp] using hQ
      have h := add_contains logTwoBox_contains (ih (q/2) (by linarith) hhalf)
      convert h using 1
      push_cast
      rw [Real.log_div (by exact_mod_cast (show q ≠ 0 by linarith)) (by norm_num)]
      ring
    · exact reducedLog_contains q 8 hq (by linarith)

/-- The public evaluator covers the existing logarithm domain `[1,65536]`. -/
def logAtFast (q : ℚ) : Box := logFast 15 q

/-- Every interval returned on the specified domain contains the exact logarithm. -/
theorem logAtFast_contains (q : ℚ) (hq : 1 ≤ q) (hQ : q ≤ 65536) :
    Contains (logAtFast q) (Real.log q) := by
  exact logFast_contains 15 q hq (by norm_num; exact hQ)

/-- Apply monotonicity to the two endpoints of a rational input interval. -/
def logIntervalFast (a : Box) : Box := ⟨(logAtFast a.lo).lo, (logAtFast a.hi).hi⟩

/-- The endpoint evaluator also encloses the logarithm of any real value
inside an input interval contained in the supported domain. -/
theorem logIntervalFast_contains {a : Box} {x : ℝ}
    (hl : 1 ≤ a.lo) (hu : a.hi ≤ 65536) (hx : Contains a x) :
    Contains (logIntervalFast a) (Real.log x) := by
  have hab : a.lo ≤ a.hi := by exact_mod_cast hx.1.trans hx.2
  have hpos : (0 : ℝ) < a.lo := by
    exact_mod_cast (show (0 : ℚ) < a.lo by linarith)
  exact ⟨(logAtFast_contains a.lo hl (hab.trans hu)).1.trans (Real.log_le_log hpos hx.1),
    (Real.log_le_log (hpos.trans_le hx.1) hx.2).trans
      (logAtFast_contains a.hi (hl.trans hab) hu).2⟩

end FleetFastLogCertificate
