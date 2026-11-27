import TestFunctions
import Mathlib

/-!
# The test function for the Chebyshev function `ψ(x)`

`TestFunctions.Gt a g s = ∫_{-a}^{a} g u * exp ((s - 1/2) u)` is the Mellin kernel of the
explicit formula.  Taking `g u ≈ exp (u/2) * 1_{[0,L]} u` with `L = log x` gives

  `Gt a g s = ∫_0^L exp (s u) du = (x^s - 1)/s`,

so `Gt a g 1 = x - 1` is the main term and the prime side
`∑ Λ n * n^{-1/2} * g (log n)` collapses to `∑_{n ≤ x} Λ n = ψ x`, because
`exp ((log n)/2) = √n` cancels the `n^{-1/2}`.

The indicator must be smoothed to land in `IsTestFn`, which demands `C²` together with the
vanishing of `g` **and** `g'` at `±a`.  Two design choices keep that cheap:

* the smoothing uses `Real.smoothTransition`, which is `C^∞`, so the `C²` obligation reduces to
  closure of `ContDiff` under products;
* the support `[0, L]` is placed **strictly inside** `[-a, a]` by taking `a = L + 1`, so `g`
  vanishes on a whole neighbourhood of each endpoint and both boundary conditions are the
  derivative of the zero function rather than a limit computation.

Placing the support on the *positive* half has a second payoff used downstream: the reflected
prime sum `∑ Λ n * n^{-1/2} * g (-log n)` of the two-sided formula vanishes identically, since
`-log n ≤ 0` for `n ≥ 1` and `Λ 1 = 0`.
-/

set_option autoImplicit false

noncomputable section

open Real

namespace PsiTestFunction

/-! ## The smooth window -/

/-- Smooth ramp: `0` for `u ≤ 0`, `1` for `u ≥ η`, values in `[0,1]`. -/
def ramp (η u : ℝ) : ℝ := Real.smoothTransition (u / η)

/-- Smooth window: `0` outside `[0, L]`, `1` on `[η, L - η]`. -/
def window (L η u : ℝ) : ℝ := ramp η u * ramp η (L - u)

/-- The real-valued test function: `exp (u/2)` cut off smoothly to `[0, L]`. -/
def wR (L η u : ℝ) : ℝ := Real.exp (u / 2) * window L η u

/-- The test function, complex-valued as `IsTestFn` requires. -/
def w (L η : ℝ) : ℝ → ℂ := fun u => (wR L η u : ℂ)

/-! ## Regularity -/

theorem ramp_contDiff (η : ℝ) {n : ℕ∞} : ContDiff ℝ n (ramp η) :=
  Real.smoothTransition.contDiff.comp (contDiff_id.div_const η)

theorem window_contDiff (L η : ℝ) {n : ℕ∞} : ContDiff ℝ n (window L η) := by
  unfold window
  exact (ramp_contDiff η).mul ((ramp_contDiff η).comp
    ((contDiff_const (c := L)).sub contDiff_id))

theorem wR_contDiff (L η : ℝ) {n : ℕ∞} : ContDiff ℝ n (wR L η) := by
  unfold wR
  exact (Real.contDiff_exp.comp (contDiff_id.div_const 2)).mul (window_contDiff L η)

theorem w_contDiff (L η : ℝ) {n : ℕ∞} : ContDiff ℝ n (w L η) :=
  Complex.ofRealCLM.contDiff.comp (wR_contDiff L η)

/-! ## Vanishing outside `[0, L]` -/

theorem ramp_eq_zero {η u : ℝ} (hη : 0 < η) (hu : u ≤ 0) : ramp η u = 0 := by
  unfold ramp
  exact Real.smoothTransition.zero_of_nonpos (div_nonpos_iff.mpr (Or.inr ⟨hu, hη.le⟩))

theorem ramp_eq_one {η u : ℝ} (hη : 0 < η) (hu : η ≤ u) : ramp η u = 1 := by
  unfold ramp
  exact Real.smoothTransition.one_of_one_le ((one_le_div hη).mpr hu)

theorem window_eq_zero_of_nonpos {L η u : ℝ} (hη : 0 < η) (hu : u ≤ 0) :
    window L η u = 0 := by
  unfold window
  rw [ramp_eq_zero hη hu, zero_mul]

theorem window_eq_zero_of_ge {L η u : ℝ} (hη : 0 < η) (hu : L ≤ u) :
    window L η u = 0 := by
  unfold window
  rw [show ramp η (L - u) = 0 from ramp_eq_zero hη (by linarith), mul_zero]

theorem window_eq_one {L η u : ℝ} (hη : 0 < η) (h1 : η ≤ u) (h2 : u ≤ L - η) :
    window L η u = 1 := by
  unfold window
  rw [ramp_eq_one hη h1, ramp_eq_one hη (by linarith), one_mul]

theorem w_eq_zero_of_nonpos {L η u : ℝ} (hη : 0 < η) (hu : u ≤ 0) : w L η u = 0 := by
  unfold w wR
  rw [window_eq_zero_of_nonpos hη hu, mul_zero, Complex.ofReal_zero]

theorem w_eq_zero_of_ge {L η u : ℝ} (hη : 0 < η) (hu : L ≤ u) : w L η u = 0 := by
  unfold w wR
  rw [window_eq_zero_of_ge hη hu, mul_zero, Complex.ofReal_zero]

/-- **The evaluation that makes the prime side `ψ`.** On the plateau the test function is
exactly `exp (u/2)`, so at `u = log n` it is `√n` and cancels the `n^{-1/2}`. -/
theorem w_eq_exp {L η u : ℝ} (hη : 0 < η) (h1 : η ≤ u) (h2 : u ≤ L - η) :
    w L η u = (Real.exp (u / 2) : ℂ) := by
  unfold w wR
  rw [window_eq_one hη h1 h2, mul_one]

/-! ## The support is strictly inside `[-a, a]` for `a = L + 1` -/

theorem w_eventuallyEq_zero_right {L η : ℝ} (hη : 0 < η) :
    w L η =ᶠ[nhds (L + 1)] fun _ => (0 : ℂ) := by
  have hmem : Set.Ioi L ∈ nhds (L + 1) :=
    isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr (by linarith))
  filter_upwards [hmem] with u hu
  exact w_eq_zero_of_ge hη (le_of_lt (Set.mem_Ioi.mp hu))

theorem w_eventuallyEq_zero_left {L η : ℝ} (hη : 0 < η) (hL : 0 ≤ L) :
    w L η =ᶠ[nhds (-(L + 1))] fun _ => (0 : ℂ) := by
  have hmem : Set.Iio (0 : ℝ) ∈ nhds (-(L + 1)) :=
    isOpen_Iio.mem_nhds (Set.mem_Iio.mpr (by linarith))
  filter_upwards [hmem] with u hu
  exact w_eq_zero_of_nonpos hη (le_of_lt (Set.mem_Iio.mp hu))

/-! ## The test-function certificate -/

/-- **`w L η` is a legitimate explicit-formula test function at radius `a = L + 1`.** -/
theorem isTestFn {L η : ℝ} (hη : 0 < η) (hL : 0 ≤ L) :
    TestFunctions.IsTestFn (L + 1) (w L η) where
  nonneg := by linarith
  smooth := w_contDiff L η
  left := w_eq_zero_of_nonpos hη (by linarith)
  right := w_eq_zero_of_ge hη (by linarith)
  deriv_left := by
    rw [(w_eventuallyEq_zero_left hη hL).deriv_eq, deriv_const]
  deriv_right := by
    rw [(w_eventuallyEq_zero_right (L := L) hη).deriv_eq, deriv_const]

/-- The support hypothesis `explicit_formula_standard` asks for, at the same radius. -/
theorem support {L η : ℝ} (hη : 0 < η) :
    ∀ u : ℝ, L + 1 < |u| → w L η u = 0 := by
  intro u hu
  rcases le_or_gt u 0 with h | h
  · exact w_eq_zero_of_nonpos hη h
  · refine w_eq_zero_of_ge hη ?_
    rw [abs_of_pos h] at hu
    linarith

end PsiTestFunction

end

#print axioms PsiTestFunction.isTestFn
#print axioms PsiTestFunction.w_eq_exp
