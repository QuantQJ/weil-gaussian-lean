/-
Copyright 2026 James C. Kerr (QuantQJ). Apache-2.0.
-/
import FleetLowZeroFree

/-!
# The criterion does not need the sharp `b^{-1/2}`: any polynomial will do

Every RH criterion in the prime-side chain is stated with the normalisation `√(π/b)`:

  `RH_iff_zero_trace_bound'`, `RH_iff_pole_prime_bound`, `RH_iff_primeSumSym_bound`.

`FleetPairCosh` explains why that exponent looks forced — `√(π/b)` is the probe's own mass, so
the constant is dimensionless.  But the exponent is **not** what drives the converse.  In
`FleetTraceBoundRH.key_estimate_of_bound` the factor `√(π/b)` appears on *both* sides and is
divided out identically; the contradiction then pits the normalised trace against
`exp (M · s)` with `s = 1/(4b)`, i.e. against `exp (M/(4b))`, where `M > 0` is the squared
off-line offset.  Any power of `1/b` loses that race.

So, for every fixed `K : ℕ`:

* `RH_iff_zero_trace_poly_bound` — RH holds iff the Gaussian zero trace is `O(b^{-1/2-K})`.
* `RH_iff_pole_prime_poly_bound` — iff the pole-minus-primes functional is `O(b^{-1/2-K})`.
* `RH_iff_primeSumSym_poly_bound`, `RH_iff_primeOnlySym_poly_bound` — iff the smoothed von
  Mangoldt sum (resp. the prime-only sum) is `O(b^{-1/2-K})` at every centre `|α| ≥ 1/2`,
  with no hypothesis, via `FleetLowZeroFree.verifiedTo_three_halves`.

What this buys: the analytic target is no longer a *sharp* constant against `√(π/b)` but
**any polynomial bound whatsoever**.  A measured shortfall that is a power of `b` — the
`b^{-1/4}` growth of the uniform-in-`α` constant — is therefore not an obstruction to these
criteria at all.  Only a bound that degrades faster than every power of `1/b`, i.e.
essentially `exp(c/b)`, can obstruct them, and that is exactly the rate an off-line zero
produces (`FleetPairCosh.gaussRatioB`, `2 (exp (e²/(4b)) - 1)`).
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology
open scoped Real
open OffLineDetection Reduction ZeroSumLimit GaussianTest

namespace FleetPolyNormalization

/-! ## Polynomial slack -/

/-- For `0 < b ≤ 1` a nonnegative constant can always be absorbed into `· / b ^ K`. -/
theorem le_div_pow {b A : ℝ} (K : ℕ) (hb : 0 < b) (hb1 : b ≤ 1) (hA : 0 ≤ A) :
    A ≤ A / b ^ K := by
  have hbk : 0 < b ^ K := pow_pos hb K
  have h1 : b ^ K ≤ 1 := pow_le_one₀ hb.le hb1
  rw [le_div_iff₀ hbk]
  nlinarith

/-- Adding a constant-normalised term to a polynomial-normalised one stays polynomial. -/
theorem add_le_div_pow {b C A : ℝ} (K : ℕ) (hb : 0 < b) (hb1 : b ≤ 1) (hA : 0 ≤ A) :
    C / b ^ K + A ≤ (C + A) / b ^ K := by
  rw [add_div]
  linarith [le_div_pow K hb hb1 hA]

/-- A sharp `√(π/b)` bound is a special case of the polynomial one. -/
theorem sharp_to_poly {X : ℝ → ℝ} {C : ℝ} (K : ℕ)
    (h : ∀ b : ℝ, 0 < b → b ≤ 1 → X b ≤ Real.sqrt (π / b) * C) :
    ∀ b : ℝ, 0 < b → b ≤ 1 → X b ≤ Real.sqrt (π / b) * (max C 0 / b ^ K) := by
  intro b hb hb1
  refine (h b hb hb1).trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
  exact (le_max_left C 0).trans (le_div_pow K hb hb1 (le_max_right C 0))

/-! ## The zero trace -/

/-- **RH iff the Gaussian zero trace is `O(b^{-1/2-K})`,** for any fixed `K : ℕ`. -/
theorem RH_iff_zero_trace_poly_bound (K : ℕ) :
    RiemannHypothesis ↔ ∀ α : ℝ, ∃ C' : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      ‖∑' x : Index, gaussHat b α (ordinate (canonical x))‖
        ≤ Real.sqrt (π / b) * (C' / b ^ K) := by
  constructor
  · intro hRH α
    obtain ⟨C', hC'⟩ := FleetTraceBoundRH.zero_trace_bound_of_RH hRH α
    exact ⟨max C' 0, sharp_to_poly K hC'⟩
  · exact FleetTraceBoundRH.RH_of_zero_trace_poly_bound K
      (fun _ hb α => (GaussianTraceFormula.gaussian_formula_zeros hb α).summable)

/-! ## The prime side -/

/-- **RH iff pole-minus-primes is `O(b^{-1/2-K})`.**  No zero and no Gamma factor appears. -/
theorem RH_iff_pole_prime_poly_bound (K : ℕ) :
    RiemannHypothesis ↔ ∀ α : ℝ, ∃ C' : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      ‖FleetPrimePoleBoundRH.poleMinusPrimes b α‖ ≤ Real.sqrt (π / b) * (C' / b ^ K) := by
  obtain ⟨Ka, hKa, hA⟩ := FleetPrimePoleBoundRH.norm_archimedean_le
  rw [RH_iff_zero_trace_poly_bound K]
  constructor
  · intro h α
    obtain ⟨C', hC'⟩ := h α
    set A : ℝ := ‖(1 / (2 * (Real.pi : ℂ)))‖ * Ka * (9 + 2 * α ^ 2) with hA_def
    have hA0 : 0 ≤ A := by
      have : (0:ℝ) ≤ 9 + 2 * α ^ 2 := by positivity
      exact mul_nonneg (mul_nonneg (norm_nonneg _) hKa) this
    refine ⟨C' + A, fun b hb hb1 => ?_⟩
    have e : FleetPrimePoleBoundRH.poleMinusPrimes b α
        = FleetFullLineArithmetic.rhs (gauss b α)
          - FleetFullLineArithmetic.archimedean (gauss b α) := by
      rw [FleetPrimePoleBoundRH.rhs_split]; ring
    rw [e, ← FleetPrimePoleBoundRH.zero_trace_eq_rhs hb α]
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add (hC' b hb hb1) (hA α b hb hb1)).trans ?_
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (add_le_div_pow K hb hb1 hA0) (Real.sqrt_nonneg _)
  · intro h α
    obtain ⟨C', hC'⟩ := h α
    set A : ℝ := ‖(1 / (2 * (Real.pi : ℂ)))‖ * Ka * (9 + 2 * α ^ 2) with hA_def
    have hA0 : 0 ≤ A := by
      have : (0:ℝ) ≤ 9 + 2 * α ^ 2 := by positivity
      exact mul_nonneg (mul_nonneg (norm_nonneg _) hKa) this
    refine ⟨C' + A, fun b hb hb1 => ?_⟩
    rw [FleetPrimePoleBoundRH.zero_trace_eq_rhs hb α, FleetPrimePoleBoundRH.rhs_split]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (hC' b hb hb1) (hA α b hb hb1)).trans ?_
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (add_le_div_pow K hb hb1 hA0) (Real.sqrt_nonneg _)

/-- Converting the pole term, polynomial normalisation.  `‖poleTerm‖ ≤ 2√(π/b)` for
`|α| ≥ 1/2` (`FleetPrimeSideConsequences.norm_poleTerm_le_of_half_le_abs`). -/
theorem poleMinusPrimes_poly_iff_primeSumSym_poly (K : ℕ) {α : ℝ} (hα : (1 / 2 : ℝ) ≤ |α|) :
    (∃ C' : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
        ‖FleetPrimePoleBoundRH.poleMinusPrimes b α‖ ≤ Real.sqrt (π / b) * (C' / b ^ K)) ↔
    (∃ C'' : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
        ‖FleetPrimeSideConsequences.primeSumSym b α‖ ≤ Real.sqrt (π / b) * (C'' / b ^ K)) := by
  constructor
  · rintro ⟨C', hC'⟩
    refine ⟨C' + 2, fun b hb hb1 => ?_⟩
    have e : FleetPrimeSideConsequences.primeSumSym b α
        = FleetPrimeSideConsequences.poleTerm b α
          - FleetPrimePoleBoundRH.poleMinusPrimes b α := by
      rw [FleetPrimeSideConsequences.poleMinusPrimes_eq]; ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add (FleetPrimeSideConsequences.norm_poleTerm_le_of_half_le_abs hb hα)
      (hC' b hb hb1)).trans ?_
    rw [show 2 * Real.sqrt (π / b) + Real.sqrt (π / b) * (C' / b ^ K)
        = Real.sqrt (π / b) * (C' / b ^ K + 2) by ring]
    exact mul_le_mul_of_nonneg_left (add_le_div_pow K hb hb1 (by norm_num))
      (Real.sqrt_nonneg _)
  · rintro ⟨C'', hC''⟩
    refine ⟨C'' + 2, fun b hb hb1 => ?_⟩
    rw [FleetPrimeSideConsequences.poleMinusPrimes_eq]
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add (FleetPrimeSideConsequences.norm_poleTerm_le_of_half_le_abs hb hα)
      (hC'' b hb hb1)).trans ?_
    rw [show 2 * Real.sqrt (π / b) + Real.sqrt (π / b) * (C'' / b ^ K)
        = Real.sqrt (π / b) * (C'' / b ^ K + 2) by ring]
    exact mul_le_mul_of_nonneg_left (add_le_div_pow K hb hb1 (by norm_num))
      (Real.sqrt_nonneg _)

/-- **RH iff the smoothed von Mangoldt sum is `O(b^{-1/2-K})` at every centre `|α| ≥ 1/2`,**
for any fixed `K : ℕ`.  No hypothesis: the low range is discharged by
`FleetLowZeroFree.verifiedTo_three_halves`. -/
theorem RH_iff_primeSumSym_poly_bound (K : ℕ) :
    RiemannHypothesis ↔ ∀ α : ℝ, 1 / 2 ≤ |α| → ∃ C'' : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      ‖FleetPrimeSideConsequences.primeSumSym b α‖
        ≤ Real.sqrt (π / b) * (C'' / b ^ K) := by
  rw [RH_iff_pole_prime_poly_bound K]
  constructor
  · intro h α hα
    exact (poleMinusPrimes_poly_iff_primeSumSym_poly K hα).mp (h α)
  · intro h α
    by_cases hα : 1 / 2 ≤ |α|
    · exact (poleMinusPrimes_poly_iff_primeSumSym_poly K hα).mpr (h α hα)
    · push_neg at hα
      have hαle : |α| + 1 ≤ 3 / 2 := by linarith
      obtain ⟨C', hC'⟩ := FleetPrimeSideConsequences.pole_prime_bound_of_verified
        FleetLowZeroFree.verifiedTo_three_halves hαle
      exact ⟨max C' 0, sharp_to_poly K hC'⟩

end FleetPolyNormalization
