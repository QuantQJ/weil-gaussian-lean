import FleetDigammaPointCertificate
import FleetEfficientArchimedeanCertificate

/-! Rational enclosures of the actual finite integrand used for quadrature.
The digamma replacement error is charged once at the integral level, not at
every sample. The remaining point computations have exact rational endpoints. -/

namespace FleetArchimedeanPointCertificate
open FleetRationalInterval FleetDigammaPointCertificate
open FleetDigammaEfficientCertificate FleetEfficientArchimedeanCertificate

def efficientWeightAt (t : ℚ) : Box := sub (psiApproxAt (t/2)) logPiBox

theorem efficientWeightAt_contains (t : ℚ) (ht : |t| ≤ 124) :
    Contains (efficientWeightAt t) (efficientWeightApprox 32 t) := by
  have ht' : |t/2| ≤ 62 := by rw [abs_div]; norm_num; linarith
  have h := sub_contains (psiApproxAt_contains (t/2) ht') logPiBox_contains
  simpa [efficientWeightAt, efficientWeightApprox] using h

def integrandAt (q u : ℚ) : Box :=
  rounded (mul (expAt (-u^2)) (efficientWeightAt (q+2*u)))

theorem integrandAt_contains (q u : ℚ) (hq : |q| ≤ 100) (hu : |u| ≤ 12) :
    Contains (integrandAt q u) (efficientIntegrand 32 q u) := by
  have ht : |q+2*u| ≤ 124 := by
    calc
      _ ≤ |q|+|2*u| := abs_add_le _ _
      _ = |q|+2*|u| := by rw [abs_mul]; norm_num
      _ ≤ 124 := by linarith
  have h := rounded_contains (mul_contains (expAt_contains (-u^2) (by nlinarith [sq_nonneg u]))
    (efficientWeightAt_contains (q+2*u) ht))
  simpa [integrandAt, efficientIntegrand] using h

/-- Fixed rational square-root bounds are checked against the proved bounds
for pi. The normalization therefore does not introduce a floating-point premise. -/
def sqrtPiBox : Box := ⟨1772453850905515/10^15, 1772453850905517/10^15⟩

theorem sqrtPiBox_contains : Contains sqrtPiBox (Real.sqrt Real.pi) := by
  have hp := piBox_contains
  have hs := Real.sq_sqrt Real.pi_pos.le
  have hnonneg := Real.sqrt_nonneg Real.pi
  norm_num [Contains, sqrtPiBox, piBox] at hp ⊢
  constructor <;> nlinarith [hp.1, hp.2]

def invSqrtPiBox : Box := invPositive sqrtPiBox

theorem invSqrtPiBox_contains : Contains invSqrtPiBox (1/Real.sqrt Real.pi) := by
  rw [one_div]
  exact invPositive_contains (by norm_num [sqrtPiBox]) sqrtPiBox_contains

/-- Tail recursion keeps large midpoint grids within the evaluator's stack. -/
def sumRangeAux (a : ℕ → Box) : ℕ → Box → Box
  | 0, acc => acc
  | n+1, acc => sumRangeAux a n (rounded (add acc (a n)))

theorem sumRangeAux_contains (a : ℕ → Box) (f : ℕ → ℝ) (n : ℕ)
    (ha : ∀ k < n, Contains (a k) (f k)) {acc : Box} {x : ℝ}
    (hx : Contains acc x) :
    Contains (sumRangeAux a n acc) (x+∑ k ∈ Finset.range n, f k) := by
  induction n generalizing acc x with
  | zero => simpa [sumRangeAux] using hx
  | succ n ih =>
    have h := ih (fun k hk => ha k (by omega))
      (rounded_contains (add_contains hx (ha n (by omega))))
    rw [Finset.sum_range_succ]
    convert h using 1 <;> first | rfl | ring

/-- Round after each addition to keep denominators bounded in large sums. -/
def sumRange (a : ℕ → Box) (n : ℕ) : Box := sumRangeAux a n (point 0)

theorem sumRange_contains (a : ℕ → Box) (f : ℕ → ℝ) (n : ℕ)
    (ha : ∀ k < n, Contains (a k) (f k)) :
    Contains (sumRange a n) (∑ k ∈ Finset.range n, f k) := by
  simpa [sumRange] using sumRangeAux_contains a f n ha (point_contains 0)

/-- A balanced tree also keeps kernel reduction depth logarithmic in the
number of samples. Each internal node still rounds outward. -/
def sumPowerTwo (a : ℕ → Box) : ℕ → ℕ → Box
  | 0, start => a start
  | depth+1, start => rounded (add (sumPowerTwo a depth start)
      (sumPowerTwo a depth (start+2^depth)))

theorem sumPowerTwo_contains (a : ℕ → Box) (f : ℕ → ℝ) (depth start : ℕ)
    (ha : ∀ k < 2^depth, Contains (a (start+k)) (f (start+k))) :
    Contains (sumPowerTwo a depth start)
      (∑ k ∈ Finset.range (2^depth), f (start+k)) := by
  induction depth generalizing start with
  | zero => simpa [sumPowerTwo] using ha 0 (by norm_num)
  | succ depth ih =>
    have he : 2^(depth+1) = 2^depth+2^depth := by rw [pow_succ]; omega
    have hl := ih start (fun k hk => ha k (by rw [he]; omega))
    have hr := ih (start+2^depth) (fun k hk => by
      simpa [Nat.add_assoc] using ha (2^depth+k) (by rw [he]; omega))
    have h := rounded_contains (add_contains hl hr)
    rw [he, Finset.sum_range_add]
    simpa [sumPowerTwo, Nat.add_assoc] using h

end FleetArchimedeanPointCertificate
