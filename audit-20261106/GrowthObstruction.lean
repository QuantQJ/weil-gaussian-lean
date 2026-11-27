import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# The growth obstruction, as a theorem rather than a docstring

`SHOSelfAdjoint.SpectrumMatchesZeros` carries this in prose: "no bounded
potential on a bounded interval can satisfy it for all `n`". Proved here, in a
form covering **both** conventions for the Hilbert-Polya correspondence, so no
choice of convention escapes it.

Eigenvalue side: for `-d^2/dx^2 + V` on `[0,L]` with `|V| <= M`, min-max gives
`lam n >= (n*pi/L)^2 - M`. That quadratic lower bound is the only thing the
obstruction needs from the operator.

Target side: Riemann-von Mangoldt gives `gamma n ~ 2*pi*n/log n`, hence
`gamma n = o(n)`. That single fact kills both conventions.
-/

set_option autoImplicit false
open Filter Topology

namespace GrowthObstruction

/-- **The obstruction.** A sequence with a quadratic lower bound cannot equal a
sequence that is `o(n^2)`. -/
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
    have h1n : (1:ℝ) ≤ (n:ℝ) :=
      le_trans (le_trans (le_max_left _ _) hN.le) hNn
    refine ⟨h1n, ?_⟩
    have hlt : 2 * M / c < (n:ℝ) :=
      lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hN) hNn
    nlinarith
  obtain ⟨n, hn1, h1n, hn2⟩ := (h1.and h2).exists
  have hsq : (0:ℝ) < (n:ℝ) ^ 2 := by nlinarith
  have hlt : t n < c / 2 * (n:ℝ) ^ 2 := by
    rw [div_lt_iff₀ hsq] at hn1; linarith
  have hge : c * (n:ℝ) ^ 2 - M ≤ t n := by rw [← hmatch n]; exact hlam n
  rw [div_lt_iff₀ hc] at hn2
  nlinarith

/-! ## The two conventions, both killed by `gamma n = o(n)` -/

/-- `1/n -> 0` and `1/n^2 -> 0`, as sequences over ℕ. -/
private lemma one_div_sq : Tendsto (fun n : ℕ => 1 / (n:ℝ) ^ 2) atTop (nhds 0) := by
  have h := tendsto_one_div_atTop_nhds_zero_nat
  have := h.mul h
  rw [mul_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have : ((n:ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [div_mul_div_comm, mul_one, ← pow_two]

/-- Convention A: eigenvalues equal the ordinates, `lam n = gamma n`. -/
theorem no_match_ordinates
    {lam gam : ℕ → ℝ} {c M : ℝ} (hc : 0 < c)
    (hlam : ∀ n : ℕ, c * (n : ℝ) ^ 2 - M ≤ lam n)
    (hg : Tendsto (fun n : ℕ => gam n / (n : ℝ)) atTop (nhds 0)) :
    ¬ (∀ n : ℕ, lam n = gam n) := by
  refine no_match_of_quadratic_growth hc hlam ?_
  have h := hg.mul (tendsto_one_div_atTop_nhds_zero_nat)
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have : ((n:ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [div_mul_div_comm, mul_one, ← pow_two]

/-- Convention B, the standard Hilbert-Polya form: `lam n = 1/4 + gamma n ^ 2`.
Also killed, and by the same hypothesis. -/
theorem no_match_quarter_plus_sq
    {lam gam : ℕ → ℝ} {c M : ℝ} (hc : 0 < c)
    (hlam : ∀ n : ℕ, c * (n : ℝ) ^ 2 - M ≤ lam n)
    (hg : Tendsto (fun n : ℕ => gam n / (n : ℝ)) atTop (nhds 0)) :
    ¬ (∀ n : ℕ, lam n = 1 / 4 + gam n ^ 2) := by
  refine no_match_of_quadratic_growth hc hlam ?_
  have hq := one_div_sq.const_mul (1/4 : ℝ)
  rw [mul_zero] at hq
  have hs : Tendsto (fun n : ℕ => (gam n / (n:ℝ)) ^ 2) atTop (nhds 0) := by
    simpa using hg.pow 2
  have h := hq.add hs
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hne : ((n:ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [div_pow, add_div]
  congr 1
  rw [mul_one_div]

end GrowthObstruction

#print axioms GrowthObstruction.no_match_of_quadratic_growth
#print axioms GrowthObstruction.no_match_ordinates
#print axioms GrowthObstruction.no_match_quarter_plus_sq
