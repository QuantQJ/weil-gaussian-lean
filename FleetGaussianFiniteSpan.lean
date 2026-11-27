import FleetGaussianDictionaryMember
import FleetExponentialSpace
import FleetArithmeticDifference
import FleetTrigPrimitive

noncomputable section
open Complex MeasureTheory
namespace FleetGaussianFiniteSpan
open FleetArithmeticContinuity GaussianTest

/-- Every fixed finite complex Gaussian span has a common exponential C² envelope. -/
theorem exists_bound {D : Type*} {b : ℝ} (hb : 0 < b) (s : Finset D)
    (α : D → ℝ) (c : D → ℂ) :
    ∃ E : ℝ, 0 ≤ E ∧ Bound E (fun u => ∑ d ∈ s, c d * gauss b (α d) u) := by
  classical
  choose E hE hg using (fun d => FleetGaussianDictionaryMember.exists_bound hb (α d))
  refine ⟨∑ d ∈ s, ‖c d‖*E d, Finset.sum_nonneg (fun d _ => mul_nonneg (norm_nonneg _) (hE d)), ?_⟩
  exact FleetExponentialSpace.bound_sum s (fun d => ‖c d‖*E d)
    (fun d u => c d*gauss b (α d) u)
    (fun d _ => FleetExponentialSpace.bound_const_mul (hg d) (c d))

/-- Full-line real transforms use the same coefficients and exact Gaussian normalization. -/
theorem h_sum_real {D : Type*} {b : ℝ} (hb : 0 < b) (s : Finset D)
    (α : D → ℝ) (c : D → ℂ) (t : ℝ) :
    FleetFullLineFourier.h (fun u => ∑ d ∈ s, c d*gauss b (α d) u) t =
      ∑ d ∈ s, c d * ((Real.sqrt (Real.pi/b) : ℂ) *
        Complex.exp (-((t : ℂ)-α d)^2/(4*b))) := by
  have hi (d : D) : Integrable (fun u : ℝ => (c d*gauss b (α d) u)*exp (I*(t : ℂ)*(u : ℂ))) := by
    obtain ⟨E, hE, hg⟩ := FleetGaussianDictionaryMember.exists_bound hb (α d)
    have hh := FleetFullLineLinearity.integrable_real_integrand
      (FleetArithmeticDifference.integrable_of_Bound hE hg) t
    simpa only [mul_assoc] using hh.const_mul (c d)
  unfold FleetFullLineFourier.h
  simp_rw [Finset.sum_mul]
  rw [integral_finset_sum s (fun d _ => hi d)]
  apply Finset.sum_congr rfl
  intro d hd
  simp_rw [mul_assoc]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  simpa only [FleetFullLineFourier.h, mul_assoc] using FleetGaussianDictionaryMember.h_gauss_eq hb (α d) t

/-- The center sign is negative for a positive Fourier mode. -/
theorem damped_fourier_mode {m : ℕ} (hm : 0 < m) (b : ℝ) (k : ℤ) (u : ℝ) :
    gauss b 0 u * fourier k (u : AddCircle (2*Real.pi*m)) =
      gauss b (-((k : ℝ)/m)) u := by
  rw [fourier_coe_apply]
  unfold gauss
  rw [← Complex.exp_add]
  congr 1
  push_cast
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hp0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

/-- Choosing period 2πm produces rational centers −k/m, with exact coefficient matching. -/
theorem damped_polynomial {m : ℕ} (hm : 0 < m) (b : ℝ) (s : Finset ℤ)
    (c : ℤ → ℂ) (u : ℝ) :
    gauss b 0 u * FleetTrigPrimitive.polynomial (2*Real.pi*m) s c u =
      ∑ k ∈ s, c k * gauss b ((-((k : ℚ)/m) : ℚ) : ℝ) u := by
  unfold FleetTrigPrimitive.polynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← mul_assoc, mul_comm (gauss b 0 u) (c k), mul_assoc, damped_fourier_mode hm]
  push_cast
  rfl

end FleetGaussianFiniteSpan
