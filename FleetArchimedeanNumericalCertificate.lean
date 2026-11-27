import FleetArchimedeanPointCertificate
import FleetEfficientMidpointCertificate
import FleetSharpMidpointCertificate

/-! A computable interval for the original finite Gaussian integral. Every
sample is enclosed using proved rational operations, and the final interval
includes the proved digamma replacement and midpoint quadrature errors. -/

namespace FleetArchimedeanNumericalCertificate
open FleetRationalInterval FleetArchimedeanPointCertificate
open FleetEfficientMidpointCertificate FleetEfficientArchimedeanCertificate
open FleetSharpMidpointCertificate

def sample (n k : ℕ) : ℚ := -12+((k:ℚ)+1/2)*(24/(n:ℚ))

theorem sample_bounds (n k : ℕ) (hn : 0 < n) (hk : k < n) : |sample n k| ≤ 12 := by
  have hn' : (0:ℚ) < n := by exact_mod_cast hn
  have hk' : (k:ℚ)+1 ≤ n := by exact_mod_cast (show k+1 ≤ n by omega)
  have hlow : 0 ≤ ((k:ℚ)+1/2)*(24/(n:ℚ)) := by positivity
  have hu : ((k:ℚ)+1/2)*(24/(n:ℚ)) ≤ 24 := by
    rw [← mul_div_assoc, div_le_iff₀ hn']
    linarith
  unfold sample
  exact abs_le.mpr ⟨by linarith, by linarith⟩

def midpointBox (q : ℚ) (depth : ℕ) : Box := rounded
  (mul invSqrtPiBox (mul (point (24/((2^depth:ℕ):ℚ)))
    (sumPowerTwo (fun k => integrandAt q (sample (2^depth) k)) depth 0)))

theorem midpointBox_contains (q : ℚ) (hq : |q| ≤ 100) (depth : ℕ) :
    Contains (midpointBox q depth) ((1/Real.sqrt Real.pi)*midpointSum 32 q (2^depth)) := by
  have hs := sumPowerTwo_contains (fun k => integrandAt q (sample (2^depth) k))
    (fun k => efficientIntegrand 32 q (sample (2^depth) k)) depth 0
    (fun k hk => by
      simpa using integrandAt_contains q (sample (2^depth) k) hq
        (sample_bounds (2^depth) k (by positivity) hk))
  have h := rounded_contains (mul_contains invSqrtPiBox_contains
    (mul_contains (point_contains (24/((2^depth:ℕ):ℚ))) hs))
  simpa [midpointBox, midpointSum, sample] using h

/-- A fixed grid with its total analytic error allowance. Explicit decimal
bounds additionally require checking the computed rational endpoints. -/
def archimedeanAt (q : ℚ) : Box := add (midpointBox q 12) ⟨-1/160, 1/160⟩

theorem archimedeanAt_contains (q : ℚ) (hq : |q| ≤ 100) :
    Contains (archimedeanAt q)
      ((1/Real.sqrt Real.pi)*(∫ u : ℝ in Set.Ioc (-12) 12,
        FleetArchimedeanTailCertificate.integrand q u)) := by
  have he := actual_normalized_midpoint_4096_le (q := (q:ℝ)) (by exact_mod_cast hq)
  have he' : Contains (⟨-1/160, 1/160⟩ : Box)
      ((1/Real.sqrt Real.pi)*(∫ u : ℝ in Set.Ioc (-12) 12,
        FleetArchimedeanTailCertificate.integrand q u) -
      (1/Real.sqrt Real.pi)*midpointSum 32 q 4096) := by
    have hh := abs_le.mp he
    unfold Contains
    norm_num at hh ⊢
    constructor <;> linarith [hh.1, hh.2]
  have hm := midpointBox_contains q hq 12
  norm_num only [Nat.reducePow] at hm
  have h := add_contains hm he'
  rw [add_sub_cancel] at h
  exact h

end FleetArchimedeanNumericalCertificate
