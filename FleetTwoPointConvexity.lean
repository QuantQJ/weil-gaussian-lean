import FleetHeatPositivityRH

/-!
# Two-point log-convexity of the heat-smoothed trace

Let `R_b(α) = Re rhs(gauss b α)` (arithmetic side; equal to the Gaussian zero trace). For real zeros
`F(α) = e^{α²/4b} R_b(α)` is a positive combination of exponentials, hence log-convex; at spacing `h` this reads

  `R_b(α + h)² ≤ e^{h²/(2b)} · R_b(α) · R_b(α + 2h)`.            (two-point condition)

Its `h → 0` limit is the curvature condition `R R'' − R'² + R²/(2b) ≥ 0`; at finite `h` it is the 2 × 2 square bank
(`FleetSquareBank`, `n = 1`), so a three-centre witness is a violation of it.

* `twoPoint_of_RH` : RH ⇒ the two-point condition for every `b ∈ (0,1]`, `α`, `h`.
* `RH_of_twoPoint` : the two-point condition for all `α, h` plus one positive value `R_b(α₀) > 0` (for each `b`) ⇒ RH.
  No derivatives: taking `α + 2h = α₀` gives `R_b(α) R_b(α₀) ≥ 0`, so `R_b` never changes sign, and
  `FleetHeatPositivityRH.RH_iff_rhs_positivity` finishes.
-/

set_option autoImplicit false
noncomputable section
open Complex Finset
open scoped Real
open GaussianTest

namespace FleetTwoPointConvexity

/-- The arithmetic side of the Gaussian of width `b` at `α` (real part). -/
def Rb (b α : ℝ) : ℝ := (FleetFullLineArithmetic.rhs (gauss b α)).re

lemma bankForm_one (b q₀ h : ℝ) (a : ℕ → ℝ) :
    FleetSquareBank.bankForm b q₀ h 1 a
      = a 0 ^ 2 * Rb b q₀ + 2 * a 0 * a 1 * Real.exp (-h ^ 2 / (4 * b)) * Rb b (q₀ + h)
        + a 1 ^ 2 * Rb b (q₀ + 2 * h) := by
  unfold FleetSquareBank.bankForm FleetSquareBank.W
  rw [Finset.sum_range_succ, Finset.sum_range_one, Finset.sum_range_succ, Finset.sum_range_one,
    Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Nat.cast_zero, Nat.cast_one, Rb]
  have e1 : -((0:ℝ) - 1) ^ 2 * h ^ 2 / (4 * b) = -h ^ 2 / (4 * b) := by ring
  have e2 : -((1:ℝ) - 0) ^ 2 * h ^ 2 / (4 * b) = -h ^ 2 / (4 * b) := by ring
  have e0 : -((0:ℝ) - 0) ^ 2 * h ^ 2 / (4 * b) = 0 := by ring
  have e3 : -((1:ℝ) - 1) ^ 2 * h ^ 2 / (4 * b) = 0 := by ring
  have q1 : q₀ + ((0:ℝ) + 1) * h = q₀ + h := by ring
  have q1' : q₀ + ((1:ℝ) + 0) * h = q₀ + h := by ring
  have q0' : q₀ + ((0:ℝ) + 0) * h = q₀ := by ring
  have q2 : q₀ + ((1:ℝ) + 1) * h = q₀ + 2 * h := by ring
  rw [e1, e2, e0, e3, Real.exp_zero, q1, q1', q0', q2]
  ring

/-- The 2 × 2 algebra: a nonnegative binary quadratic form gives the two-point inequality. -/
lemma two_by_two {r0 r1 r2 W E : ℝ} (hW : 0 < W) (hE : 0 < E) (hWE : W ^ 2 * E = 1)
    (hQ : ∀ x y : ℝ, 0 ≤ x ^ 2 * r0 + 2 * x * y * W * r1 + y ^ 2 * r2) :
    r1 ^ 2 ≤ E * r0 * r2 := by
  have h0 : 0 ≤ r0 := by have := hQ 1 0; simpa using this
  have h2 : 0 ≤ r2 := by have := hQ 0 1; simpa using this
  rcases h0.lt_or_eq with hpos | hzero
  · have h := hQ (W * r1) (-r0)
    have hdet : W ^ 2 * r1 ^ 2 ≤ r0 * r2 := by nlinarith
    calc r1 ^ 2 = (W ^ 2 * E) * r1 ^ 2 := by rw [hWE, one_mul]
      _ = E * (W ^ 2 * r1 ^ 2) := by ring
      _ ≤ E * (r0 * r2) := mul_le_mul_of_nonneg_left hdet hE.le
      _ = E * r0 * r2 := by ring
  · have hr1 : r1 = 0 := by
      by_contra hne
      have hc : W * r1 ≠ 0 := mul_ne_zero hW.ne' hne
      have h := hQ (-(r2 + 1) / (2 * (W * r1))) 1
      rw [← hzero] at h
      have e : 2 * (-(r2 + 1) / (2 * (W * r1))) * 1 * W * r1 = -(r2 + 1) := by field_simp
      nlinarith [e]
    rw [hr1, ← hzero]; simp

/-- **RH ⇒ two-point log-convexity**, at every width `b ∈ (0,1]`, height `α` and spacing `h`. -/
theorem twoPoint_of_RH (hRH : RiemannHypothesis) {b : ℝ} (hb : 0 < b) (α h : ℝ) :
    Rb b (α + h) ^ 2 ≤ Real.exp (h ^ 2 / (2 * b)) * Rb b α * Rb b (α + 2 * h) := by
  have hWE : Real.exp (-h ^ 2 / (4 * b)) ^ 2 * Real.exp (h ^ 2 / (2 * b)) = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast
    rw [show (2:ℝ) * (-h ^ 2 / (4 * b)) + h ^ 2 / (2 * b) = 0 by field_simp; ring, Real.exp_zero]
  refine two_by_two (Real.exp_pos _) (Real.exp_pos _) hWE (fun x y => ?_)
  have := FleetSquareBank.bank_form_nonneg_of_RH hRH hb α h 1 (fun i => if i = 0 then x else y)
  rw [bankForm_one] at this
  simpa using this

/-- **Two-point log-convexity plus one positive value at each width ⇒ RH.** -/
theorem RH_of_twoPoint
    (hlc : ∀ b : ℝ, 0 < b → b ≤ 1 → ∀ α h : ℝ,
      Rb b (α + h) ^ 2 ≤ Real.exp (h ^ 2 / (2 * b)) * Rb b α * Rb b (α + 2 * h))
    (hseed : ∀ b : ℝ, 0 < b → b ≤ 1 → ∃ α₀ : ℝ, 0 < Rb b α₀) :
    RiemannHypothesis := by
  rw [FleetHeatPositivityRH.RH_iff_rhs_positivity]
  intro b hb hb1 x
  obtain ⟨α₀, hα₀⟩ := hseed b hb hb1
  have h := hlc b hb hb1 x ((α₀ - x) / 2)
  have e : x + 2 * ((α₀ - x) / 2) = α₀ := by ring
  rw [e] at h
  have hE := Real.exp_pos (((α₀ - x) / 2) ^ 2 / (2 * b))
  have hsq := sq_nonneg (Rb b (x + (α₀ - x) / 2))
  have h1 : 0 ≤ Real.exp (((α₀ - x) / 2) ^ 2 / (2 * b)) * (Rb b x * Rb b α₀) := by
    have : Real.exp (((α₀ - x) / 2) ^ 2 / (2 * b)) * Rb b x * Rb b α₀
        = Real.exp (((α₀ - x) / 2) ^ 2 / (2 * b)) * (Rb b x * Rb b α₀) := by ring
    linarith
  have h2 : 0 ≤ Rb b x * Rb b α₀ := by
    by_contra hneg; push_neg at hneg
    have := mul_neg_of_pos_of_neg hE hneg; linarith
  show 0 ≤ Rb b x
  by_contra hneg; push_neg at hneg
  have := mul_neg_of_neg_of_pos hneg hα₀; linarith

/-- **RH ⟺ two-point log-convexity**, given a positive value at each width (true under RH whenever ζ has a zero). -/
theorem RH_iff_twoPoint
    (hseed : ∀ b : ℝ, 0 < b → b ≤ 1 → ∃ α₀ : ℝ, 0 < Rb b α₀) :
    RiemannHypothesis ↔ ∀ b : ℝ, 0 < b → b ≤ 1 → ∀ α h : ℝ,
      Rb b (α + h) ^ 2 ≤ Real.exp (h ^ 2 / (2 * b)) * Rb b α * Rb b (α + 2 * h) :=
  ⟨fun hRH b hb _ α h => twoPoint_of_RH hRH hb α h, fun hlc => RH_of_twoPoint hlc hseed⟩

end FleetTwoPointConvexity
