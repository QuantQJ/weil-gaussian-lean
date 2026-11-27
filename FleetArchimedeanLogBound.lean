/-
Copyright 2026 James C. Kerr (QuantQJ). Apache-2.0.
-/
import FleetPrimePoleBoundRH

/-!
# The archimedean constant is `O(log |α|)`, not `O(α²)`

`FleetPrimePoleBoundRH.norm_archimedean_le` bounds the archimedean functional by
`√(π/b) · ‖1/(2π)‖ · K · (9 + 2α²)`.  The `α²` is not in the mathematics: it is the cost of
forcing the Gaussian probe, which is concentrated at `α`, through the **origin-centred**
envelope `M/(1+t²)` of `FleetArchimedeanFunctionalBound.exists_weight_integral_bound`.  That
envelope must cover `t = α`, hence `M ≳ √(π/b)·α²`.

Routing through the **shifted** envelope `M/(1+(t-α)²)` removes it.  Two cheap ingredients:

* `envelope_shift` — `‖h (gauss b α) t‖ ≤ 4√(π/b)/(1+(t-α)²)` for `0 < b ≤ 1`.  The constant
  `4` (rather than the sharp `≈ 1.89`) makes the proof one line from `1 + v ≤ exp v`:
  `(1+u²) exp(-u²/(4b)) ≤ 1 + 4v ≤ 4 + 4v ≤ 4 exp v`.
* `logShift_le` — `log(|t|+2) ≤ (log(|α|+2)/log 2 + 1) · log(|t-α|+2)`, pointwise, since
  `log(|t-α|+2) ≥ log 2`.  This keeps the majorant a pure **translate** of
  `LeftLineBound.integrable_log_div_one_add_sq`, so no new integral is needed and
  `FleetArchimedeanFunctionalBound.logIntegral` is reused verbatim.

The outcome, `norm_archimedean_le_log`:

  `‖archimedean (gauss b α)‖ ≤ √(π/b) · C · (log (|α| + 2) + 1)`.

Numerically the exact value is `2(log(α/2) − log π)·√(b/π)` for the symmetrised probe,
confirmed to 0.3% against the digamma integral (0.6469 predicted vs 0.64471 computed at
`b = 0.5, α = 14.1347`), and the Weil identity `zeros = pole − primes + archimedean` closes to
`2.7 × 10⁻¹⁵`.  So `log` is the true order and `α²` was pure packaging loss.

This constant enters every criterion in the chain that imports `norm_archimedean_le`, and each
of those quantifies over `α`, which is exactly where `α²` hurt.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Complex
open scoped Real
open GaussianTest

namespace FleetArchimedeanLogBound

open FleetArchimedeanFunctionalBound

/-- The shifted-envelope constant. -/
def shiftConst (α : ℝ) : ℝ := Real.log (|α| + 2) / Real.log 2 + 1

theorem shiftConst_nonneg (α : ℝ) : 0 ≤ shiftConst α := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : 0 ≤ Real.log (|α| + 2) := Real.log_nonneg (by linarith [abs_nonneg α])
  unfold shiftConst; positivity

/-- **Pointwise log shift.**  Keeps the majorant a translate of the origin-centred one. -/
theorem logShift_le (α t : ℝ) :
    Real.log (|t| + 2) ≤ shiftConst α * Real.log (|t - α| + 2) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlb : Real.log 2 ≤ Real.log (|t - α| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg (t - α)])
  have ht : |t| ≤ |α| + |t - α| := by
    have := abs_sub_abs_le_abs_sub t α
    linarith
  have hsplit : Real.log (|t| + 2) ≤ Real.log (|α| + 2) + Real.log (|t - α| + 2) := by
    rw [← Real.log_mul (by linarith [abs_nonneg α]) (by linarith [abs_nonneg (t - α)])]
    refine Real.log_le_log (by linarith [abs_nonneg t]) ?_
    nlinarith [abs_nonneg α, abs_nonneg (t - α)]
  have hna : 0 ≤ Real.log (|α| + 2) := Real.log_nonneg (by linarith [abs_nonneg α])
  have hscale : Real.log (|α| + 2)
      ≤ (Real.log (|α| + 2) / Real.log 2) * Real.log (|t - α| + 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ h2]
    nlinarith
  unfold shiftConst
  nlinarith

/-- **The shifted envelope for the Gaussian probe.** -/
theorem envelope_shift {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (α t : ℝ) :
    ‖FleetFullLineFourier.h (gauss b α) (t : ℂ)‖
      ≤ (4 * Real.sqrt (π / b)) / (1 + (t - α) ^ 2) := by
  rw [FleetGaussianDictionaryMember.h_eq_gaussHat, norm_gaussHat hb]
  simp only [Complex.ofReal_im, Complex.ofReal_re]
  rw [show ((0 : ℝ) ^ 2 - (t - α) ^ 2) / (4 * b) = -((t - α) ^ 2 / (4 * b)) by ring]
  set u : ℝ := t - α with hu
  set v : ℝ := u ^ 2 / (4 * b) with hv
  have hb4 : (0:ℝ) < 4 * b := by positivity
  have hv0 : 0 ≤ v := by rw [hv]; positivity
  have hu2 : u ^ 2 ≤ 4 * v := by
    rw [hv, mul_div_assoc', le_div_iff₀ hb4]
    nlinarith [sq_nonneg u]
  have hsq : (0:ℝ) < 1 + u ^ 2 := by positivity
  have hkey : (1 + u ^ 2) * Real.exp (-v) ≤ 4 := by
    have hev : 0 < Real.exp v := Real.exp_pos v
    have h2 : v + 1 ≤ Real.exp v := Real.add_one_le_exp v
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hev]
    nlinarith
  rw [le_div_iff₀ hsq]
  have hs : (0:ℝ) ≤ Real.sqrt (π / b) := Real.sqrt_nonneg _
  calc Real.sqrt (π / b) * Real.exp (-v) * (1 + u ^ 2)
      = Real.sqrt (π / b) * ((1 + u ^ 2) * Real.exp (-v)) := by ring
    _ ≤ Real.sqrt (π / b) * 4 := mul_le_mul_of_nonneg_left hkey hs
    _ = 4 * Real.sqrt (π / b) := by ring

/-- **The shifted integral bound.**  Same proof shape as
`FleetArchimedeanFunctionalBound.integral_bound`, with the envelope centred at `α` and the
majorant a translate, so `logIntegral` is reused unchanged. -/
theorem integral_bound_shift {f G : ℝ → ℂ} (hf : Continuous f)
    (hG : AEStronglyMeasurable G) {B M α : ℝ} (hB0 : 0 ≤ B) (hM0 : 0 ≤ M)
    (hB : ∀ t, ‖f t‖ ≤ B * Real.log (|t| + 2))
    (hM : ∀ t, ‖G t‖ ≤ M / (1 + (t - α) ^ 2)) :
    ‖∫ t, f t * G t‖ ≤ B * M * shiftConst α * logIntegral := by
  have hBM : 0 ≤ B * M := mul_nonneg hB0 hM0
  set c : ℝ := B * M * shiftConst α with hc
  have hc0 : 0 ≤ c := by rw [hc]; exact mul_nonneg hBM (shiftConst_nonneg α)
  set maj : ℝ → ℝ := fun t => Real.log (|t - α| + 2) / (1 + (t - α) ^ 2) with hmaj
  have hmajI : Integrable maj :=
    LeftLineBound.integrable_log_div_one_add_sq.comp_sub_right α
  have hmajInt : ∫ t, maj t = logIntegral := by
    rw [hmaj, logIntegral]
    exact integral_sub_right_eq_self (fun u => Real.log (|u| + 2) / (1 + u ^ 2)) α
  have hbound : ∀ t, ‖f t * G t‖ ≤ c * maj t := by
    intro t
    rw [norm_mul]
    have h1 : ‖f t‖ * ‖G t‖ ≤ (B * Real.log (|t| + 2)) * (M / (1 + (t - α) ^ 2)) :=
      mul_le_mul (hB t) (hM t) (norm_nonneg _) ((norm_nonneg _).trans (hB t))
    refine h1.trans ?_
    have hd : (0:ℝ) < 1 + (t - α) ^ 2 := by positivity
    have hnum : B * Real.log (|t| + 2) * M
        ≤ B * M * shiftConst α * Real.log (|t - α| + 2) := by
      nlinarith [logShift_le α t, hBM]
    calc (B * Real.log (|t| + 2)) * (M / (1 + (t - α) ^ 2))
        = (B * Real.log (|t| + 2) * M) / (1 + (t - α) ^ 2) := by ring
      _ ≤ (B * M * shiftConst α * Real.log (|t - α| + 2)) / (1 + (t - α) ^ 2) := by
          gcongr
      _ = c * maj t := by rw [hc, hmaj]; ring
  have hi : Integrable (fun t => f t * G t) :=
    (hmajI.const_mul c).mono' (hf.aestronglyMeasurable.mul hG)
      (Filter.Eventually.of_forall hbound)
  calc ‖∫ t, f t * G t‖ ≤ ∫ t, ‖f t * G t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, c * maj t := integral_mono hi.norm (hmajI.const_mul c) hbound
    _ = c * logIntegral := by rw [MeasureTheory.integral_const_mul, hmajInt]

/-- **`O(log |α|)` archimedean bound.**  Replaces the `(9 + 2α²)` of
`FleetPrimePoleBoundRH.norm_archimedean_le` by `C · (log (|α| + 2) + 1)`. -/
theorem norm_archimedean_le_log : ∃ C : ℝ, 0 ≤ C ∧ ∀ (α b : ℝ), 0 < b → b ≤ 1 →
    ‖FleetFullLineArithmetic.archimedean (gauss b α)‖
      ≤ Real.sqrt (π / b) * (C * (Real.log (|α| + 2) + 1)) := by
  obtain ⟨B, hB, hb⟩ := exists_weight_log_bound
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLI : 0 ≤ logIntegral := logIntegral_nonneg
  set N : ℝ := ‖(1 / (2 * (Real.pi : ℂ)))‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  have hC0 : 0 ≤ 4 * B * logIntegral * (1 / Real.log 2 + 1) * N := by
    have : (0:ℝ) ≤ 1 / Real.log 2 + 1 := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hLI) this) hN0
  refine ⟨4 * B * logIntegral * (1 / Real.log 2 + 1) * N, hC0, fun α b hbp hb1 => ?_⟩
  have hGc : Continuous (fun t : ℝ => FleetFullLineFourier.h (gauss b α) (t : ℂ)) := by
    simp_rw [FleetGaussianDictionaryMember.h_gauss_eq hbp]
    fun_prop
  have hwB : ∀ t : ℝ, ‖(FleetGammaKernel.weight t : ℂ)‖ ≤ B * Real.log (|t| + 2) := by
    intro t
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hb t
  have hwc : Continuous (fun t : ℝ => (FleetGammaKernel.weight t : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_weight
  have hkey := integral_bound_shift hwc hGc.aestronglyMeasurable hB
    (by positivity : (0:ℝ) ≤ 4 * Real.sqrt (π / b)) hwB (envelope_shift hbp hb1 α)
  set S : ℝ := Real.sqrt (π / b) with hS
  have hS0 : (0:ℝ) ≤ S := Real.sqrt_nonneg _
  have hna : 0 ≤ Real.log (|α| + 2) := Real.log_nonneg (by linarith [abs_nonneg α])
  have hL : shiftConst α ≤ (1 / Real.log 2 + 1) * (Real.log (|α| + 2) + 1) := by
    unfold shiftConst
    have hinv : 1 / Real.log 2 * Real.log 2 = 1 := by field_simp
    rw [div_add' _ _ _ (ne_of_gt h2), div_le_iff₀ h2]
    nlinarith
  have hpre : (0:ℝ) ≤ 4 * B * logIntegral * N :=
    mul_nonneg (mul_nonneg (by linarith) hLI) hN0
  unfold FleetFullLineArithmetic.archimedean
  rw [norm_mul]
  have hcomm : (fun t : ℝ => FleetFullLineFourier.h (gauss b α) (t : ℂ)
      * (FleetGammaKernel.weight t : ℂ))
      = fun t : ℝ => (FleetGammaKernel.weight t : ℂ)
      * FleetFullLineFourier.h (gauss b α) (t : ℂ) := by
    funext t; ring
  rw [hcomm]
  calc N * ‖∫ t : ℝ, (FleetGammaKernel.weight t : ℂ)
        * FleetFullLineFourier.h (gauss b α) (t : ℂ)‖
      ≤ N * (B * (4 * S) * shiftConst α * logIntegral) :=
        mul_le_mul_of_nonneg_left hkey hN0
    _ = S * ((4 * B * logIntegral * N) * shiftConst α) := by rw [hS]; ring
    _ ≤ S * ((4 * B * logIntegral * N)
        * ((1 / Real.log 2 + 1) * (Real.log (|α| + 2) + 1))) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL hpre) hS0
    _ = S * ((4 * B * logIntegral * (1 / Real.log 2 + 1) * N)
        * (Real.log (|α| + 2) + 1)) := by ring

end FleetArchimedeanLogBound
