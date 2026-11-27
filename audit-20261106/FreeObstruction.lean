import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# The obstruction, unconditional for the free Dirichlet operator

`GrowthObstruction` proves that a quadratically-growing sequence cannot equal an
`o(n^2)` one, taking the quadratic lower bound as a hypothesis about some
operator. `DirichletEigen` constructs the eigenpairs of `-d^2/dx^2` on `[0,L]`
and computes the eigenvalues exactly as `(n*pi/L)^2`.

Here the two are joined: for the free operator the lower bound is an equality,
so no hypothesis about an operator is left. The only input is
`gamma n = o(n)`, which Riemann-von Mangoldt supplies.
-/

set_option autoImplicit false
open Filter Topology

namespace FreeObstruction

/-- The growth obstruction (as in `GrowthObstruction`). -/
theorem no_match_of_quadratic_growth
    {lam t : ℕ → ℝ} {c M : ℝ} (hc : 0 < c)
    (hlam : ∀ n : ℕ, c * (n : ℝ) ^ 2 - M ≤ lam n)
    (ht : Tendsto (fun n : ℕ => t n / (n : ℝ) ^ 2) atTop (nhds 0)) :
    ¬ (∀ n : ℕ, lam n = t n) := by
  intro hmatch
  have h1 : ∀ᶠ n : ℕ in atTop, t n / (n : ℝ) ^ 2 < c / 2 :=
    ht.eventually (eventually_lt_nhds (by linarith : (0:ℝ) < c / 2))
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (2 * M / c))
  have h2 : ∀ᶠ n : ℕ in atTop, (1:ℝ) ≤ (n:ℝ) ∧ 2 * M / c < (n:ℝ) ^ 2 := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hNn : (N:ℝ) ≤ (n:ℝ) := Nat.cast_le.mpr hn
    have h1n : (1:ℝ) ≤ (n:ℝ) := le_trans (le_trans (le_max_left _ _) hN.le) hNn
    refine ⟨h1n, ?_⟩
    have hlt : 2 * M / c < (n:ℝ) :=
      lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hN) hNn
    nlinarith
  obtain ⟨n, hn1, h1n, hn2⟩ := (h1.and h2).exists
  have hsq : (0:ℝ) < (n:ℝ) ^ 2 := by nlinarith
  have hlt : t n < c / 2 * (n:ℝ) ^ 2 := by rw [div_lt_iff₀ hsq] at hn1; linarith
  have hge : c * (n:ℝ) ^ 2 - M ≤ t n := by rw [← hmatch n]; exact hlam n
  rw [div_lt_iff₀ hc] at hn2
  nlinarith

/-- The exact Dirichlet spectrum of `-d^2/dx^2` on `[0,L]`, from `DirichletEigen`. -/
noncomputable def freeEigenvalue (L : ℝ) (n : ℕ) : ℝ := ((n : ℝ) * Real.pi / L) ^ 2

lemma freeEigenvalue_eq (L : ℝ) (hL : 0 < L) (n : ℕ) :
    freeEigenvalue L n = (Real.pi / L) ^ 2 * (n : ℝ) ^ 2 := by
  unfold freeEigenvalue
  field_simp; ring

/-- **Unconditional for the free operator, convention A.** No hypothesis about
an operator survives: the eigenvalues are known exactly. -/
theorem free_cannot_match_ordinates {L : ℝ} (hL : 0 < L) {gam : ℕ → ℝ}
    (hg : Tendsto (fun n : ℕ => gam n / (n : ℝ)) atTop (nhds 0)) :
    ¬ (∀ n : ℕ, freeEigenvalue L n = gam n) := by
  have hc : (0:ℝ) < (Real.pi / L) ^ 2 := by positivity
  refine no_match_of_quadratic_growth (M := 0) hc (fun n => ?_) ?_
  · rw [freeEigenvalue_eq L hL n]; linarith
  · have h := hg.mul (tendsto_one_div_atTop_nhds_zero_nat)
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : ((n:ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    rw [div_mul_div_comm, mul_one, ← pow_two]

/-- **Unconditional for the free operator, convention B** (`lam = 1/4 + gamma^2`). -/
theorem free_cannot_match_quarter_plus_sq {L : ℝ} (hL : 0 < L) {gam : ℕ → ℝ}
    (hg : Tendsto (fun n : ℕ => gam n / (n : ℝ)) atTop (nhds 0)) :
    ¬ (∀ n : ℕ, freeEigenvalue L n = 1 / 4 + gam n ^ 2) := by
  have hc : (0:ℝ) < (Real.pi / L) ^ 2 := by positivity
  refine no_match_of_quadratic_growth (M := 0) hc (fun n => ?_) ?_
  · rw [freeEigenvalue_eq L hL n]; linarith
  · have hone : Tendsto (fun n : ℕ => 1 / (n:ℝ) ^ 2) atTop (nhds 0) := by
      have h := tendsto_one_div_atTop_nhds_zero_nat
      have := h.mul h
      rw [mul_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have : ((n:ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      rw [div_mul_div_comm, mul_one, ← pow_two]
    have hq := hone.const_mul (1/4 : ℝ); rw [mul_zero] at hq
    have hs : Tendsto (fun n : ℕ => (gam n / (n:ℝ)) ^ 2) atTop (nhds 0) := by
      simpa using hg.pow 2
    have h := hq.add hs; rw [add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hne : ((n:ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    rw [div_pow, add_div]; congr 1; rw [mul_one_div]

/-- **And with a bounded potential.** `min-max` gives `lam n >= (n*pi/L)^2 - M`
for `|V| <= M`; that single inequality is the only input, and it is named. -/
theorem bounded_potential_cannot_match {L M : ℝ} (hL : 0 < L) {lam gam : ℕ → ℝ}
    (hminmax : ∀ n : ℕ, freeEigenvalue L n - M ≤ lam n)
    (hg : Tendsto (fun n : ℕ => gam n / (n : ℝ)) atTop (nhds 0)) :
    ¬ (∀ n : ℕ, lam n = gam n) := by
  have hc : (0:ℝ) < (Real.pi / L) ^ 2 := by positivity
  refine no_match_of_quadratic_growth (M := M) hc (fun n => ?_) ?_
  · have := hminmax n; rw [freeEigenvalue_eq L hL n] at this; linarith
  · have h := hg.mul (tendsto_one_div_atTop_nhds_zero_nat)
    rw [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have : ((n:ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    rw [div_mul_div_comm, mul_one, ← pow_two]

end FreeObstruction

#print axioms FreeObstruction.free_cannot_match_ordinates
#print axioms FreeObstruction.free_cannot_match_quarter_plus_sq
#print axioms FreeObstruction.bounded_potential_cannot_match
