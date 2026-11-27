import FleetArithmeticDifference
import FleetExponentialSpace

noncomputable section
open Complex MeasureTheory
namespace FleetArithmeticLinearSpan
open FleetArithmeticContinuity FleetFullLineArithmetic

lemma h_const_mul (c : ℂ) (g : ℝ → ℂ) (z : ℂ) :
    FleetFullLineFourier.h (fun u => c*g u) z = c*FleetFullLineFourier.h g z := by
  simp only [FleetFullLineFourier.h, mul_assoc, MeasureTheory.integral_const_mul]

lemma prime_const_mul (c : ℂ) (g : ℝ → ℂ) :
    GammaExplicitFormula.primeSum (fun u => c*g u) = c*GammaExplicitFormula.primeSum g := by
  unfold GammaExplicitFormula.primeSum
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  ring

lemma archimedean_const_mul (c : ℂ) (g : ℝ → ℂ) :
    archimedean (fun u => c*g u) = c*archimedean g := by
  unfold archimedean
  simp_rw [h_const_mul, mul_assoc, MeasureTheory.integral_const_mul]
  ring

lemma rhs_const_mul (c : ℂ) (g : ℝ → ℂ) :
    rhs (fun u => c*g u) = c*rhs g := by
  unfold rhs
  rw [h_const_mul, h_const_mul, archimedean_const_mul, prime_const_mul]
  change _ - GammaExplicitFormula.primeSum (fun u => c*GammaExplicitFormula.reflect g u) = _
  rw [prime_const_mul]
  ring

lemma rhs_zero : rhs (0 : ℝ → ℂ) = 0 := by
  have h := rhs_const_mul 0 (0 : ℝ → ℂ)
  simp only [zero_mul] at h
  exact h

lemma rhs_add {Ef Eg : ℝ} {f g : ℝ → ℂ} (hEf : 0 ≤ Ef) (hEg : 0 ≤ Eg)
    (hf : Bound Ef f) (hg : Bound Eg g) : rhs (f+g) = rhs f+rhs g := by
  have hneg := FleetExponentialSpace.bound_const_mul hg (-1)
  have hneg' : Bound Eg (-g) := by simp at hneg; exact hneg
  have hs := FleetArithmeticDifference.rhs_sub hEf hEg hf hneg'
  have hr : rhs (-g) = -rhs g := by
    have h := rhs_const_mul (-1) g
    simp at h
    exact h
  simpa only [sub_neg_eq_add, hr] using hs

/-- Fixed finite linear combinations have exactly the corresponding arithmetic targets. -/
theorem rhs_sum {D : Type*} (s : Finset D) (E : D → ℝ) (g : D → ℝ → ℂ)
    (hE : ∀ d ∈ s, 0 ≤ E d) (hg : ∀ d ∈ s, Bound (E d) (g d)) :
    rhs (fun u => ∑ d ∈ s, g d u) = ∑ d ∈ s, rhs (g d) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact rhs_zero
  | @insert d s hd ih =>
    simp only [Finset.sum_insert hd]
    rw [show (fun u => g d u+∑ e ∈ s, g e u) = g d+(fun u => ∑ e ∈ s, g e u) by rfl]
    rw [rhs_add (hE d (Finset.mem_insert_self _ _))
      (Finset.sum_nonneg (fun e he => hE e (Finset.mem_insert_of_mem he)))
      (hg d (Finset.mem_insert_self _ _))
      (FleetExponentialSpace.bound_sum s E g (fun e he => hg e (Finset.mem_insert_of_mem he)))]
    rw [ih (fun e he => hE e (Finset.mem_insert_of_mem he)) (fun e he => hg e (Finset.mem_insert_of_mem he))]

end FleetArithmeticLinearSpan
