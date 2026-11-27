import FleetRationalInterval
import FleetFastLogCertificate
import FleetDigammaEfficientCertificate

/-! Computable rational enclosures of actual digamma values. The computation
is justified by the proved 32-term approximation and the rational interval
logarithm evaluator. Successful concrete examples use kernel reduction. -/

namespace FleetDigammaPointCertificate
open FleetRationalInterval
open FleetFastLogCertificate

def rationalTerms (y : ℚ) : ℚ :=
  ∑ k ∈ Finset.range 32, ((k : ℚ)+1/4)/(((k : ℚ)+1/4)^2+y^2)

/-- Round individual fractions before summation to avoid the huge common
denominator of the exact partial-fraction sum. -/
def rationalTermsBox (y : ℚ) : Box :=
  ⟨∑ k ∈ Finset.range 32, roundDown (((k : ℚ)+1/4)/(((k : ℚ)+1/4)^2+y^2)),
   ∑ k ∈ Finset.range 32, roundUp (((k : ℚ)+1/4)/(((k : ℚ)+1/4)^2+y^2))⟩

theorem rationalTermsBox_contains (y : ℚ) : Contains (rationalTermsBox y) (rationalTerms y) := by
  have hl : (rationalTermsBox y).lo ≤ rationalTerms y := by
    exact Finset.sum_le_sum (fun k _ => roundDown_le _)
  have hu : rationalTerms y ≤ (rationalTermsBox y).hi := by
    exact Finset.sum_le_sum (fun k _ => le_roundUp _)
  exact ⟨by exact_mod_cast hl, by exact_mod_cast hu⟩

def denominator (y : ℚ) : ℚ := (129/4)^2+y^2

def psiApproxAt (y : ℚ) : Box := rounded
  (sub (sub (mul (point (1/2)) (logAtFast (denominator y)))
    (point ((129/4)/(2*denominator y)))) (rationalTermsBox y))

theorem denominator_bounds {y : ℚ} (hy : |y| ≤ 62) :
    1 ≤ denominator y ∧ denominator y ≤ 65536 := by
  have h := abs_le.mp hy
  unfold denominator
  constructor <;> nlinarith [sq_nonneg y, mul_nonneg (sub_nonneg.mpr h.2) (show 0 ≤ 62+y by linarith)]

theorem rationalTerms_cast (y : ℚ) :
    (rationalTerms y : ℝ) =
      ∑ k ∈ Finset.range 32, ((k : ℝ)+1/4)/(((k : ℝ)+1/4)^2+(y : ℝ)^2) := by
  simp [rationalTerms]

theorem psiApproxAt_contains (y : ℚ) (hy : |y| ≤ 62) :
    Contains (psiApproxAt y) (FleetDigammaEfficientCertificate.efficientPsiApprox 32 y) := by
  obtain ⟨hl, hu⟩ := denominator_bounds hy
  have h := rounded_contains (sub_contains (sub_contains
    (mul_contains (point_contains (1/2)) (logAtFast_contains (denominator y) hl hu))
    (point_contains ((129/4)/(2*denominator y)))) (rationalTermsBox_contains y))
  change Contains (psiApproxAt y) _ at h
  rw [rationalTerms_cast] at h
  unfold FleetDigammaEfficientCertificate.efficientPsiApprox
  norm_num [denominator] at h ⊢
  convert h using 1 <;> congr 1 <;> ring

def psiAt (y : ℚ) : Box := add (psiApproxAt y) ⟨-1/961, 1/961⟩

/-- Contains the actual real part of the logarithmic Gamma derivative. -/
theorem psiAt_contains (y : ℚ) (hy : |y| ≤ 62) :
    Contains (psiAt y)
      (FleetGammaKernel.psi (FleetDigammaIntervalCertificate.quarterPoint y)).re := by
  have he := FleetDigammaEfficientCertificate.abs_re_psi_sub_efficientPsiApprox_le
    32 (by norm_num) (y : ℝ)
  norm_num at he
  have he' : Contains (⟨-1/961, 1/961⟩ : Box)
      ((FleetGammaKernel.psi (FleetDigammaIntervalCertificate.quarterPoint y)).re -
        FleetDigammaEfficientCertificate.efficientPsiApprox 32 y) := by
    unfold Contains
    norm_num
    have hh := abs_le.mp he
    constructor <;> linarith [hh.1, hh.2]
  have h := add_contains (psiApproxAt_contains y hy) he'
  rw [add_sub_cancel] at h
  exact h

def piBox : Box := ⟨314159265358979323846/10^20, 314159265358979323847/10^20⟩

theorem piBox_contains : Contains piBox Real.pi := by
  unfold Contains piBox
  constructor
  · have h := Real.pi_gt_d20.le
    norm_num at h ⊢
    exact h
  · have h := Real.pi_lt_d20.le
    norm_num at h ⊢
    exact h

def logPiBox : Box := logIntervalFast piBox

theorem logPiBox_contains : Contains logPiBox (Real.log Real.pi) := by
  exact logIntervalFast_contains (by norm_num [piBox]) (by norm_num [piBox]) piBox_contains

def weightAt (t : ℚ) : Box := sub (psiAt (t/2)) logPiBox

theorem weightAt_contains (t : ℚ) (ht : |t| ≤ 124) :
    Contains (weightAt t) (FleetGammaKernel.weight t) := by
  have ht' : |t/2| ≤ 62 := by rw [abs_div]; norm_num; linarith
  have h := sub_contains (psiAt_contains (t/2) ht') logPiBox_contains
  change Contains (weightAt t) _ at h
  unfold FleetGammaKernel.weight
  convert h using 1
  congr 3
  unfold FleetDigammaIntervalCertificate.quarterPoint
  push_cast
  ring

end FleetDigammaPointCertificate
