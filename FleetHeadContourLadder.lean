import FleetFiniteHeadRH
import FleetExponentLadder

/-!
# The exponent ladder for the Möbius head

`head_exp_ladder`: if for **every** `c > 0` and every `|α| ≥ 1/2` there is `C` with
`|head b α (cut b)| ≤ √(π/b) · C · e^{c/b}` for `0 < b ≤ 1`, then RH holds.

(Low centres `|α| < 1/2` are covered unconditionally by `VerifiedTo (3/2)`; at `|α| ≥ 1/2` the pole term is
`≤ 2√(π/b)` and the discarded Möbius tail is `≤ 8e^{-0.6375/b}`. `FleetExponentLadder` then confines every
zero to `|Re ρ − 1/2| ≤ 2√c`, for all `c > 0`.)

`pow_le_exp`: `u^j ≤ (j!/c^j) e^{c u}` — so any polynomial loss in `1/b` is admissible.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology
open scoped Real
open OffLineDetection Reduction ZeroSumLimit GaussianTest

namespace FleetHeadContour

/-- `u^j ≤ (j!/c^j) e^{c u}` for `u ≥ 0`, `c > 0`. -/
lemma pow_le_exp (j : ℕ) {c u : ℝ} (hc : 0 < c) (hu : 0 ≤ u) :
    u ^ j ≤ (j.factorial / c ^ j) * Real.exp (c * u) := by
  have h := Real.pow_div_factorial_le_exp (c * u) (mul_nonneg hc.le hu) j
  have hf : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  have hcj : 0 < c ^ j := pow_pos hc j
  rw [mul_pow, div_le_iff₀ hf] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ hcj]
  linarith

/-- Every nontrivial zero is on the line once all strips `|Re ρ − 1/2| ≤ 2√c`, `c > 0`, hold. -/
lemma RH_of_strips (h : ∀ c : ℝ, 0 < c → ∀ x : Index, |(canonical x).re - 1 / 2| ≤ 2 * Real.sqrt c) :
    RiemannHypothesis := by
  apply RH_of_nontrivial_zeros_on_critical_line
  intro ρ hρ
  obtain ⟨x, hx⟩ := multEnum_canonical.exists_index hρ
  rw [← hx]
  by_contra hne
  have hd : 0 < |(canonical x).re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hne)
  set d := |(canonical x).re - 1 / 2|
  have h1 := h (d ^ 2 / 16) (by positivity) x
  have hs : Real.sqrt (d ^ 2 / 16) = d / 4 := by
    rw [show d ^ 2 / 16 = (d / 4) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hs] at h1
  linarith

/-- **The exponent ladder for the head.** -/
theorem head_exp_ladder
    (h : ∀ c : ℝ, 0 < c → ∀ α : ℝ, 1 / 2 ≤ |α| → ∃ C : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      |FleetFiniteHeadRH.head b α (FleetFiniteHeadRH.cut b)| ≤ Real.sqrt (π / b) * (C * Real.exp (c / b))) :
    RiemannHypothesis := by
  apply RH_of_strips
  intro c hc
  apply FleetExponentLadder.zeros_in_strip_of_pole_prime_exp_bound hc.le
  intro α
  by_cases hα : 1 / 2 ≤ |α|
  · obtain ⟨C, hC⟩ := h c hc α hα
    refine ⟨|C| + 10, fun b hb hb1 => ?_⟩
    have hE : 1 ≤ Real.exp (c / b) := Real.one_le_exp (div_nonneg hc.le hb.le)
    have hsq := Real.sqrt_nonneg (π / b)
    have h1 := hC b hb hb1
    have h2 := FleetFiniteHeadRH.primeSumSym_sub_head hb hb1 α
    have h3 := FleetFiniteHeadRH.exp_tail_le hb hb1
    have h4 := FleetPrimeSideConsequences.norm_poleTerm_le_of_half_le_abs hb hα
    have hh : ‖(FleetFiniteHeadRH.head b α (FleetFiniteHeadRH.cut b) : ℂ)‖
        = |FleetFiniteHeadRH.head b α (FleetFiniteHeadRH.cut b)| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    have h5 : ‖FleetPrimeSideConsequences.primeSumSym b α‖
        ≤ |FleetFiniteHeadRH.head b α (FleetFiniteHeadRH.cut b)| + 8 * Real.exp (-51 / (80 * b)) := by
      have := norm_le_insert' (FleetPrimeSideConsequences.primeSumSym b α)
        (FleetFiniteHeadRH.head b α (FleetFiniteHeadRH.cut b) : ℂ)
      rw [hh] at this; linarith
    rw [FleetPrimeSideConsequences.poleMinusPrimes_eq]
    have hCC : C * Real.exp (c / b) ≤ |C| * Real.exp (c / b) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
    calc ‖FleetPrimeSideConsequences.poleTerm b α - FleetPrimeSideConsequences.primeSumSym b α‖
        ≤ ‖FleetPrimeSideConsequences.poleTerm b α‖ + ‖FleetPrimeSideConsequences.primeSumSym b α‖ :=
          norm_sub_le _ _
      _ ≤ 2 * Real.sqrt (π / b) + (Real.sqrt (π / b) * (|C| * Real.exp (c / b)) + Real.sqrt (π / b) * 8) := by
          nlinarith [mul_le_mul_of_nonneg_left hCC hsq]
      _ ≤ Real.sqrt (π / b) * ((|C| + 10) * Real.exp (c / b)) := by
          nlinarith [mul_le_mul_of_nonneg_left hE hsq, abs_nonneg C]
  · push_neg at hα
    obtain ⟨C', hC'⟩ := FleetPrimeSideConsequences.pole_prime_bound_of_verified
      FleetLowZeroFree.verifiedTo_three_halves (α := α) (by linarith)
    refine ⟨|C'|, fun b hb hb1 => ?_⟩
    have hE : 1 ≤ Real.exp (c / b) := Real.one_le_exp (div_nonneg hc.le hb.le)
    have hsq := Real.sqrt_nonneg (π / b)
    calc ‖FleetPrimePoleBoundRH.poleMinusPrimes b α‖ ≤ Real.sqrt (π / b) * C' := hC' b hb hb1
      _ ≤ Real.sqrt (π / b) * |C'| := mul_le_mul_of_nonneg_left (le_abs_self _) hsq
      _ ≤ Real.sqrt (π / b) * (|C'| * Real.exp (c / b)) := by
          apply mul_le_mul_of_nonneg_left _ hsq
          nlinarith [abs_nonneg C']

end FleetHeadContour
