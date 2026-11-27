import FleetEfficientArchimedeanDerivatives
import FleetMidpointDerivativeGrid

/-! Midpoint quadrature applied to the actual finite digamma approximation,
and the resulting replacement bound for the original Gaussian kernel. -/

noncomputable section
open Real Set MeasureTheory Finset
open FleetEfficientArchimedeanCertificate FleetEfficientArchimedeanDerivatives

namespace FleetEfficientMidpointCertificate

def midpointSum (N : ℕ) (q : ℝ) (n : ℕ) : ℝ :=
  (24/(n:ℝ)) * ∑ k ∈ range n,
    efficientIntegrand N q (-12+((k:ℝ)+1/2)*(24/(n:ℝ)))

theorem midpoint_error (N : ℕ) (hN : 2 ≤ N) {q : ℝ} (hq : |q| ≤ 100)
    (n : ℕ) (hn : 0 < n) :
    |(∫ u : ℝ in Ioc (-12) 12, efficientIntegrand N q u)-midpointSum N q n| ≤
      576000/(n:ℝ)^2 := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hend : (-12:ℝ)+(n:ℝ)*(24/(n:ℝ)) = 12 := by field_simp; ring
  have hb : ∀ t ∈ Icc (-12:ℝ) (-12+(n:ℝ)*(24/(n:ℝ))),
      |integrandSecond N q t| ≤ 1000 := by
    intro t ht
    rw [hend] at ht
    exact abs_integrandSecond_le N hN hq (abs_le.mpr ht)
  have h := FleetMidpointDerivativeGrid.uniform_midpoint_error_of_hasDerivAt
    (hasDerivAt_integrand N q) (hasDerivAt_integrandFirst N q)
    (-12) (24/(n:ℝ)) 1000 n (by positivity) hb
  rw [hend, intervalIntegral.integral_of_le (show (-12:ℝ) ≤ 12 by norm_num)] at h
  change |(∫ u : ℝ in Ioc (-12) 12, efficientIntegrand N q u)-midpointSum N q n| ≤ _ at h
  convert h using 1
  field_simp
  ring

theorem normalized_midpoint_error (N : ℕ) (hN : 2 ≤ N) {q : ℝ} (hq : |q| ≤ 100)
    (n : ℕ) (hn : 0 < n) :
    |(1/sqrt Real.pi)*(∫ u : ℝ in Ioc (-12) 12, efficientIntegrand N q u)-
      (1/sqrt Real.pi)*midpointSum N q n| ≤
      576000/((n:ℝ)^2*sqrt Real.pi) := by
  rw [← mul_sub, abs_mul, _root_.abs_of_nonneg (show 0 ≤ 1/sqrt Real.pi by positivity)]
  have h := mul_le_mul_of_nonneg_left (midpoint_error N hN hq n hn)
    (show 0 ≤ 1/sqrt Real.pi by positivity)
  convert h using 1
  ring

theorem actual_normalized_midpoint_error (N : ℕ) (hN : 2 ≤ N) {q : ℝ}
    (hq : |q| ≤ 100) (n : ℕ) (hn : 0 < n) :
    |(1/sqrt Real.pi)*
      (∫ u : ℝ in Ioc (-12) 12, FleetArchimedeanTailCertificate.integrand q u)-
      (1/sqrt Real.pi)*midpointSum N q n| ≤
      1/((N:ℝ)-1)^2+576000/((n:ℝ)^2*sqrt Real.pi) := by
  have h1 := normalized_replacement_bound N hN q (Ioc (-12) 12)
  have h2 := normalized_midpoint_error N hN hq n hn
  exact (abs_sub_le _ _ _).trans (add_le_add h1 h2)

/-- A fixed concrete grid: 32 digamma terms and 16384 midpoint cells give
an analytic replacement error below 0.004 before evaluating the finite sum. -/
theorem actual_normalized_midpoint_error_stage100 {q : ℝ} (hq : |q| ≤ 100) :
    |(1/sqrt Real.pi)*
      (∫ u : ℝ in Ioc (-12) 12, FleetArchimedeanTailCertificate.integrand q u)-
      (1/sqrt Real.pi)*midpointSum 32 q 16384| ≤ (1/250:ℝ) := by
  have h := actual_normalized_midpoint_error 32 (by norm_num) hq 16384 (by norm_num)
  have hs : 1 ≤ sqrt Real.pi := by
    nlinarith [Real.sq_sqrt Real.pi_pos.le, Real.sqrt_nonneg Real.pi, Real.pi_gt_three]
  have hb : (576000:ℝ)/((16384:ℝ)^2*sqrt Real.pi) ≤ 576000/(16384:ℝ)^2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  norm_num only [Nat.cast_ofNat] at h
  have he : 1/((32:ℝ)-1)^2+576000/(16384:ℝ)^2 ≤ 1/250 := by norm_num
  have hh := (add_le_add_right hb _).trans he
  norm_num at hh
  exact h.trans hh

theorem actual_normalized_midpoint_16384_le {q : ℝ} (hq : |q| ≤ 100) :
    |(1/sqrt Real.pi)*
      (∫ u : ℝ in Ioc (-12) 12, FleetArchimedeanTailCertificate.integrand q u)-
      (1/sqrt Real.pi)*midpointSum 32 q 16384| ≤ (1/250:ℝ) :=
  actual_normalized_midpoint_error_stage100 hq

end FleetEfficientMidpointCertificate
