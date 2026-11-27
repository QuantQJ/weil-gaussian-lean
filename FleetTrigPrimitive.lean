import FleetPeriodicApproximation
import Mathlib

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace FleetTrigPrimitive

def frequency (P : ℝ) (k : ℤ) : ℂ := 2 * Real.pi * Complex.I * k / P

def polynomial (P : ℝ) (s : Finset ℤ) (c : ℤ → ℂ) (t : ℝ) : ℂ :=
  ∑ k ∈ s, c k * fourier k (t : AddCircle P)

def primitive (P : ℝ) (s : Finset ℤ) (c : ℤ → ℂ) : ℝ → ℂ :=
  polynomial P s (fun k => c k / frequency P k)

def doublePrimitive (P : ℝ) (s : Finset ℤ) (c : ℤ → ℂ) : ℝ → ℂ :=
  primitive P s (fun k => c k / frequency P k)

lemma frequency_ne_zero {P : ℝ} (hP : 0 < P) {k : ℤ} (hk : k ≠ 0) :
    frequency P k ≠ 0 := by
  simp [frequency, hP.ne', Real.pi_ne_zero, hk]

lemma periodic_polynomial (P : ℝ) (s : Finset ℤ) (c : ℤ → ℂ) :
    Function.Periodic (polynomial P s c) P := by
  intro t
  simp only [polynomial, AddCircle.coe_add_period]

lemma hasDerivAt_primitive {P : ℝ} (hP : 0 < P) (s : Finset ℤ) (c : ℤ → ℂ)
    (hc : c 0 = 0) (t : ℝ) :
    HasDerivAt (primitive P s c) (polynomial P s c t) t := by
  unfold primitive polynomial
  apply HasDerivAt.fun_sum
  intro k hk
  have hh := (hasDerivAt_fourier P k t).const_mul (c k / frequency P k)
  by_cases hk0 : k = 0
  · subst k
    simpa [hc] using hh
  · convert hh using 1
    change c k * fourier k (t : AddCircle P) =
      c k / frequency P k * (frequency P k * fourier k (t : AddCircle P))
    field_simp [frequency_ne_zero hP hk0]

lemma hasDerivAt_doublePrimitive {P : ℝ} (hP : 0 < P) (s : Finset ℤ)
    (c : ℤ → ℂ) (t : ℝ) :
    HasDerivAt (doublePrimitive P s c) (primitive P s c t) t := by
  exact hasDerivAt_primitive hP s (fun k => c k / frequency P k)
    (by simp [frequency]) t

lemma deriv_doublePrimitive {P : ℝ} (hP : 0 < P) (s : Finset ℤ)
    (c : ℤ → ℂ) : deriv (doublePrimitive P s c) = primitive P s c := by
  funext t
  exact (hasDerivAt_doublePrimitive hP s c t).deriv

/-- Dividing nonconstant Fourier coefficients twice constructs a periodic
second primitive. The zero-mode condition is explicit, not an assumed C² density. -/
theorem doublePrimitive_second_deriv {P : ℝ} (hP : 0 < P) (s : Finset ℤ)
    (c : ℤ → ℂ) (hc : c 0 = 0) :
    deriv (deriv (doublePrimitive P s c)) = polynomial P s c := by
  rw [deriv_doublePrimitive hP]
  funext t
  exact (hasDerivAt_primitive hP s c hc t).deriv

/-- Every finite Fourier sum with zero constant coefficient has an explicit
periodic twice-differentiable second primitive. -/
theorem exists_periodic_second_primitive {P : ℝ} (hP : 0 < P) (s : Finset ℤ)
    (c : ℤ → ℂ) (hc : c 0 = 0) :
    ∃ F : ℝ → ℂ, Function.Periodic F P ∧ Differentiable ℝ F ∧
      Differentiable ℝ (deriv F) ∧ deriv (deriv F) = polynomial P s c := by
  refine ⟨doublePrimitive P s c, periodic_polynomial P s _, ?_, ?_,
    doublePrimitive_second_deriv hP s c hc⟩
  · exact fun t => (hasDerivAt_doublePrimitive hP s c t).differentiableAt
  · rw [deriv_doublePrimitive hP]
    exact fun t => (hasDerivAt_primitive hP s c hc t).differentiableAt

end FleetTrigPrimitive
