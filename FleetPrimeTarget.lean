import FleetLowZeroFree

/-!
# The target, stated once, in real form

`primeOnlySym b α` (a complex `tsum`) is the real sum
`2 Σ_p log p · p^{-1/2} · e^{-b log² p} · cos(α log p)` (`primeOnlySym_eq_real`).

`PrimeTarget` is the open statement: at every `|α| ≥ 1/2` that sum is `O(b^{-1/2})` for
`0 < b ≤ 1`. `RH_iff_PrimeTarget` (no hypotheses; standard axioms only) says it is equivalent to
the Riemann Hypothesis. A proof of `PrimeTarget` closes RH in one line; nothing here asserts it.
-/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Real
open GaussianTest FleetPrimeOnlyRH

namespace FleetPrimeTarget

/-- The real prime sum `S_b^prime(α) = 2 Σ_p log p · p^{-1/2} e^{-b log² p} cos(α log p)`. -/
def primeSumReal (b α : ℝ) : ℝ :=
  ∑' n : ℕ, thetaW n * ((n : ℝ) ^ (-(1 / 2) : ℝ) * (2 * Real.exp (-b * Real.log n ^ 2) * Real.cos (α * Real.log n)))

lemma gauss_add_neg (b α u : ℝ) :
    gauss b α u + gauss b α (-u) = ((2 * Real.exp (-b * u ^ 2) * Real.cos (α * u) : ℝ) : ℂ) := by
  unfold gauss
  push_cast
  have h1 : cexp (-(b : ℂ) * (u : ℂ) ^ 2 - I * (α : ℂ) * (u : ℂ))
      = cexp (-(b : ℂ) * (u : ℂ) ^ 2) * cexp (-((α : ℂ) * (u : ℂ)) * I) := by
    rw [← Complex.exp_add]; ring_nf
  have h2 : cexp (-(b : ℂ) * ((-u : ℝ) : ℂ) ^ 2 - I * (α : ℂ) * ((-u : ℝ) : ℂ))
      = cexp (-(b : ℂ) * (u : ℂ) ^ 2) * cexp (((α : ℂ) * (u : ℂ)) * I) := by
    rw [← Complex.exp_add]; push_cast; ring_nf
  push_cast at h2
  rw [h1, h2, ← mul_add, add_comm (cexp (-((α : ℂ) * (u : ℂ)) * I)), ← Complex.two_cos]
  ring

lemma term_eq_real (b α : ℝ) (n : ℕ) :
    term thetaW b α n = ((thetaW n * ((n : ℝ) ^ (-(1 / 2) : ℝ) *
      (2 * Real.exp (-b * Real.log n ^ 2) * Real.cos (α * Real.log n))) : ℝ) : ℂ) := by
  unfold term
  rw [gauss_add_neg]
  have hc : (((n : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) = (n : ℂ) ^ (-(1 / 2) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]; push_cast; ring_nf
  push_cast
  rw [hc]; ring

/-- **The complex `primeOnlySym` is the real cosine sum.** -/
theorem primeOnlySym_eq_real (b α : ℝ) : primeOnlySym b α = (primeSumReal b α : ℂ) := by
  unfold primeOnlySym primeSumReal
  rw [Complex.ofReal_tsum]
  congr 1; funext n; exact term_eq_real b α n

/-- **The open target.** At every height `|α| ≥ 1/2`, the Gaussian-smoothed sum over primes is
`O(b^{-1/2})` as `b → 0`. -/
def PrimeTarget : Prop :=
  ∀ α : ℝ, 1 / 2 ≤ |α| → ∃ C : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
    |primeSumReal b α| ≤ Real.sqrt (π / b) * C

/-- **RH ⟺ PrimeTarget**, with no hypotheses. -/
theorem RH_iff_PrimeTarget : RiemannHypothesis ↔ PrimeTarget := by
  rw [FleetLowZeroFree.RH_iff_primeOnlySym_bound]
  unfold PrimeTarget
  simp only [primeOnlySym_eq_real, Complex.norm_real, Real.norm_eq_abs]

end FleetPrimeTarget
