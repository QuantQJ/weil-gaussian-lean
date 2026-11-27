import FleetPrimeOnlyRH
import ZetaGrowthEM3
import Mathlib

/-!
# No zeta zeros with `|Im s| ≤ 3/2` in the critical strip

From the fourth-order Euler–Maclaurin continuation `ζ = zetaAbel₄` (`ZetaGrowthEM3`):
`(s-1) ζ(s) = (s+2)(s+3)/12 − (s-1)s(s+1)(s+2)/720 + (s-1)·R(s)` with
`‖R(s)‖ ≤ ‖s‖‖s+1‖‖s+2‖‖s+3‖/720 · π²/6`. On `0 < Re s < 1`, `|Im s| ≤ 3/2` the first term has
norm `≥ 1/2` and the other two together at most `≈ 0.31`, so `ζ(s) ≠ 0`. No numerics beyond
`π < 3.15`.

Consequences: `verifiedTo_three_halves : VerifiedTo (3/2)` holds outright, and
`RH_iff_primeOnlySym_bound` / `RH_iff_primeSumSym_bound` are the pure prime-sum criteria at
`|α| ≥ 1/2` with no hypothesis.
-/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Real
open ZetaGrowth ZetaGrowthNeg ZetaGrowthEM3 OffLineDetection Reduction ZeroSumLimit

namespace FleetLowZeroFree

lemma norm_le_of_sq {z : ℂ} {c : ℝ} (hc : 0 ≤ c) (h : z.re ^ 2 + z.im ^ 2 ≤ c ^ 2) : ‖z‖ ≤ c := by
  rw [Complex.norm_def, Complex.normSq_apply]
  exact (Real.sqrt_le_left hc).mpr (by nlinarith)

lemma sum_inv_sq : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simpa using h

/-- **`ζ(s) ≠ 0` for `0 < Re s < 1`, `|Im s| ≤ 3/2`.** -/
theorem zeta_ne_zero_low {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (ht : |s.im| ≤ 3 / 2) :
    riemannZeta s ≠ 0 := by
  have hs1 : s ≠ 1 := fun h => by rw [h] at h1; simp at h1
  have hsm1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have ht2 : s.im ^ 2 ≤ 9 / 4 := by
    have := abs_le.mp ht; nlinarith
  -- norm bounds on the box
  have nA : ‖s‖ ≤ 1.81 := norm_le_of_sq (by norm_num) (by nlinarith)
  have nB : ‖s + 1‖ ≤ 2.5 :=
    norm_le_of_sq (by norm_num) (by simp only [add_re, add_im, one_re, one_im]; nlinarith)
  have nC : ‖s + 2‖ ≤ 3.36 :=
    norm_le_of_sq (by norm_num) (by
      simp only [add_re, add_im]; norm_num; nlinarith)
  have nD : ‖s + 3‖ ≤ 4.28 :=
    norm_le_of_sq (by norm_num) (by
      simp only [add_re, add_im]; norm_num; nlinarith)
  have nE : ‖s - 1‖ ≤ 1.81 :=
    norm_le_of_sq (by norm_num) (by simp only [sub_re, sub_im, one_re, one_im]; nlinarith)
  have lC : 2 ≤ ‖s + 2‖ := by
    have := Complex.re_le_norm (s + 2); simp only [add_re] at this
    norm_num at this; linarith
  have lD : 3 ≤ ‖s + 3‖ := by
    have := Complex.re_le_norm (s + 3); simp only [add_re] at this
    norm_num at this; linarith
  -- the remainder
  set K : ℝ := ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ / 720
  have hK0 : 0 ≤ K := by positivity
  have hKle : K ≤ 1.81 * 2.5 * 3.36 * 4.28 / 720 := by
    have := mul_le_mul (mul_le_mul (mul_le_mul nA nB (norm_nonneg _) (by norm_num)) nC
      (norm_nonneg _) (by norm_num)) nD (norm_nonneg _) (by norm_num)
    simp only [K]; linarith [div_le_div_of_nonneg_right this (by norm_num : (0:ℝ) ≤ 720)]
  have hterm : ∀ n : ℕ, ‖emTerm₄ (n + 1) s‖ ≤ K * (1 / ((n : ℝ) + 1) ^ 2) := by
    intro n
    have h := norm_emTerm₄_le (by linarith : (-4 : ℝ) ≤ s.re) hs1 (by omega : 1 ≤ n + 1)
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hK0)
    push_cast
    have hx : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    calc ((n : ℝ) + 1) ^ (-s.re - 4) ≤ ((n : ℝ) + 1) ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx (by linarith)
      _ = 1 / ((n : ℝ) + 1) ^ 2 := by
          rw [Real.rpow_neg (by linarith), one_div]; norm_cast
  have hsumK : HasSum (fun n : ℕ => K * (1 / ((n : ℝ) + 1) ^ 2)) (K * (π ^ 2 / 6)) :=
    sum_inv_sq.mul_left K
  have hnorm : Summable (fun n : ℕ => ‖emTerm₄ (n + 1) s‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsumK.summable
  set R : ℂ := ∑' n : ℕ, emTerm₄ (n + 1) s
  have hR : ‖R‖ ≤ K * (π ^ 2 / 6) :=
    (norm_tsum_le_tsum_norm hnorm).trans
      ((Summable.tsum_le_tsum hterm hnorm hsumK.summable).trans (le_of_eq hsumK.tsum_eq))
  have hpi : π ^ 2 / 6 ≤ 1.66 := by
    have := Real.pi_lt_d2; have := Real.pi_pos; nlinarith
  -- the identity (s-1) ζ(s) = A - B + (s-1) R
  intro hz
  have hζ := zeta_eq_zetaAbel₄ (by linarith : (-3 : ℝ) < s.re) hs1
  rw [hz] at hζ
  unfold zetaAbel₄ at hζ
  have hζ' : 1 / (s - 1) + 1 / 2 + s / 12 - s * (s + 1) * (s + 2) / 720 + R = 0 := hζ.symm
  have e : (s - 1) * (1 / (s - 1) + 1 / 2 + s / 12 - s * (s + 1) * (s + 2) / 720 + R) = 0 := by
    rw [hζ', mul_zero]
  have hinv : (s - 1) * (1 / (s - 1)) = 1 := mul_one_div_cancel hsm1
  have key : (s + 2) * (s + 3) / 12 = (s - 1) * s * (s + 1) * (s + 2) / 720 - (s - 1) * R := by
    linear_combination e - hinv
  have hA : (1 / 2 : ℝ) ≤ ‖(s + 2) * (s + 3) / 12‖ := by
    rw [norm_div, norm_mul]
    have : ‖(12 : ℂ)‖ = 12 := by simp
    rw [this]
    have := mul_le_mul lC lD (by norm_num) (norm_nonneg _)
    linarith [div_le_div_of_nonneg_right this (by norm_num : (0:ℝ) ≤ 12)]
  have hB : ‖(s - 1) * s * (s + 1) * (s + 2) / 720‖ ≤ 1.81 * 1.81 * 2.5 * 3.36 / 720 := by
    rw [norm_div, norm_mul, norm_mul, norm_mul]
    have : ‖(720 : ℂ)‖ = 720 := by simp
    rw [this]
    have := mul_le_mul (mul_le_mul (mul_le_mul nE nA (norm_nonneg _) (by norm_num)) nB
      (norm_nonneg _) (by norm_num)) nC (norm_nonneg _) (by norm_num)
    exact div_le_div_of_nonneg_right this (by norm_num)
  have hC : ‖(s - 1) * R‖ ≤ 1.81 * ((1.81 * 2.5 * 3.36 * 4.28 / 720) * 1.66) := by
    rw [norm_mul]
    apply mul_le_mul nE _ (norm_nonneg _) (by norm_num)
    calc ‖R‖ ≤ K * (π ^ 2 / 6) := hR
      _ ≤ (1.81 * 2.5 * 3.36 * 4.28 / 720) * 1.66 :=
          mul_le_mul hKle hpi (by positivity) (by norm_num)
  have htri := norm_sub_le ((s - 1) * s * (s + 1) * (s + 2) / 720) ((s - 1) * R)
  rw [← key] at htri
  norm_num at hA hB hC htri
  linarith

/-- **`VerifiedTo (3/2)` holds outright**: there is no nontrivial zero with `|Im ρ| ≤ 3/2`. -/
theorem verifiedTo_three_halves : FleetPrimeSideConsequences.VerifiedTo (3 / 2) := by
  intro x hx
  exfalso
  have h := multEnum_canonical.nontrivial x
  obtain ⟨h0, h1⟩ := ZetaStrip.mem_strip_of_isNontrivialZero h
  exact zeta_ne_zero_low h0 h1 hx h.1

/-- **RH iff the pure prime-power sum bound at `|α| ≥ 1/2`**, no hypothesis. -/
theorem RH_iff_primeSumSym_bound :
    RiemannHypothesis ↔ ∀ α : ℝ, 1 / 2 ≤ |α| → ∃ C'' : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      ‖FleetPrimeSideConsequences.primeSumSym b α‖ ≤ Real.sqrt (π / b) * C'' :=
  FleetPrimeOnlyRH.RH_iff_primeSumSym_bound_of_verified le_rfl verifiedTo_three_halves

/-- **RH iff the pure prime sum bound at `|α| ≥ 1/2`**, primes only, no hypothesis. -/
theorem RH_iff_primeOnlySym_bound :
    RiemannHypothesis ↔ ∀ α : ℝ, 1 / 2 ≤ |α| → ∃ C'' : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      ‖FleetPrimeOnlyRH.primeOnlySym b α‖ ≤ Real.sqrt (π / b) * C'' :=
  FleetPrimeOnlyRH.RH_iff_primeOnlySym_bound_of_verified le_rfl verifiedTo_three_halves

end FleetLowZeroFree
