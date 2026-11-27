import FleetDigammaSeries
import Mathlib

open Filter Finset
open scoped Topology

namespace FleetDigammaGrowth

lemma inv_sq_le_sub_inv {x : ℝ} (hx : 0 < x) :
    1 / (x + 1)^2 ≤ 1 / x - 1 / (x + 1) := by
  have hx1 : 0 < x + 1 := by linarith
  have he : 1 / x - 1 / (x + 1) = 1 / (x * (x + 1)) := by
    field_simp
    ring
  rw [he]
  apply one_div_le_one_div_of_le (mul_pos hx hx1)
  nlinarith

lemma sum_inv_sq_tail_le (N n : ℕ) (hN : 0 < N) :
    (∑ k ∈ range n, 1 / ((N : ℝ) + k + 1)^2) ≤
      1 / (N : ℝ) - 1 / ((N : ℝ) + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have h : 0 < (N : ℝ) + n := by positivity
    have ht := inv_sq_le_sub_inv h
    simp only [Nat.cast_add, Nat.cast_one, ← add_assoc]
    linarith

lemma tsum_inv_sq_tail_le (N : ℕ) (hN : 0 < N) :
    (∑' k : ℕ, 1 / ((N : ℝ) + k + 1)^2) ≤ 1 / (N : ℝ) := by
  apply Real.tsum_le_of_sum_range_le (fun _ => by positivity)
  intro n
  exact (sum_inv_sq_tail_le N n hN).trans (sub_le_self _ (by positivity))

lemma norm_term_le (k : ℕ) {z : ℂ} {δ : ℝ}
    (hd : 0 < δ) (hd1 : δ ≤ 1) (hz : δ ≤ z.re) :
    ‖(z + (k : ℂ))⁻¹ - ((k : ℂ) + 1)⁻¹‖ ≤
      (1 + 1 / δ) / ((k : ℝ) + 1) := by
  have hp : 0 < (k : ℝ) + 1 := by positivity
  have hre : δ * ((k : ℝ) + 1) ≤ ‖z + (k : ℂ)‖ := by
    have hh : (z + (k : ℂ)).re ≤ ‖z + (k : ℂ)‖ := Complex.re_le_norm _
    simp only [Complex.add_re, Complex.natCast_re] at hh
    have hk : (0 : ℝ) ≤ k := by positivity
    nlinarith
  calc
    _ ≤ ‖(z + (k : ℂ))⁻¹‖ + ‖((k : ℂ) + 1)⁻¹‖ := norm_sub_le _ _
    _ = 1 / ‖z + (k : ℂ)‖ + 1 / ((k : ℝ) + 1) := by
      simp only [norm_inv, one_div, FleetDigammaSeries.norm_nat_add_one]
    _ ≤ 1 / (δ * ((k : ℝ) + 1)) + 1 / ((k : ℝ) + 1) := by
      gcongr
    _ = (1 + 1 / δ) / ((k : ℝ) + 1) := by
      field_simp
      ring

lemma norm_head_le (N : ℕ) {z : ℂ} {δ : ℝ}
    (hd : 0 < δ) (hd1 : δ ≤ 1) (hz : δ ≤ z.re) :
    ‖∑ k ∈ range N, ((z + (k : ℂ))⁻¹ - ((k : ℂ) + 1)⁻¹)‖ ≤
      (1 + 1 / δ) * (1 + Real.log N) := by
  calc
    _ ≤ ∑ k ∈ range N, ‖(z + (k : ℂ))⁻¹ - ((k : ℂ) + 1)⁻¹‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ range N, (1 + 1 / δ) / ((k : ℝ) + 1) :=
      sum_le_sum (fun k _ => norm_term_le k hd hd1 hz)
    _ = (1 + 1 / δ) * (harmonic N : ℝ) := by
      simp [harmonic, mul_sum, div_eq_mul_inv]
    _ ≤ (1 + 1 / δ) * (1 + Real.log N) := by
      gcongr
      exact harmonic_le_one_add_log N

lemma norm_tail_le (N : ℕ) (hN : 0 < N) {z : ℂ} {δ : ℝ}
    (hd : 0 < δ) (hd1 : δ ≤ 1) (hz : δ ≤ z.re) :
    ‖∑' k : ℕ, ((z + ((k + N : ℕ) : ℂ))⁻¹ - (((k + N : ℕ) : ℂ) + 1)⁻¹)‖ ≤
      (‖z - 1‖ / δ) / (N : ℝ) := by
  have hs := FleetDigammaSeries.summable_deriv_q (lt_of_lt_of_le hd hz)
  have hss := (summable_nat_add_iff N).mpr hs
  have hu : Summable (fun k : ℕ => (‖z - 1‖ / δ) / ((N : ℝ) + k + 1)^2) := by
    have h := (summable_nat_add_iff N).mpr
      (FleetDigammaSeries.summable_majorant (‖z - 1‖ / δ))
    simpa [Nat.cast_add, add_comm, add_left_comm, add_assoc] using h
  calc
    _ ≤ ∑' k : ℕ, ‖(z + ((k + N : ℕ) : ℂ))⁻¹ - (((k + N : ℕ) : ℂ) + 1)⁻¹‖ :=
      norm_tsum_le_tsum_norm hss.norm
    _ ≤ ∑' k : ℕ, (‖z - 1‖ / δ) / ((N : ℝ) + k + 1)^2 := by
      apply Summable.tsum_le_tsum _ hss.norm hu
      intro k
      simpa [Nat.cast_add, div_mul_eq_div_div, add_comm, add_left_comm, add_assoc] using
        FleetDigammaSeries.norm_deriv_q_le (k + N) hd hd1 hz (le_refl ‖z - 1‖)
    _ = (‖z - 1‖ / δ) * (∑' k : ℕ, 1 / ((N : ℝ) + k + 1)^2) := by
      rw [← tsum_mul_left]
      congr 1
      ext k
      ring
    _ ≤ (‖z - 1‖ / δ) * (1 / (N : ℝ)) := by
      gcongr
      exact tsum_inv_sq_tail_le N hN
    _ = (‖z - 1‖ / δ) / (N : ℝ) := by ring

lemma norm_series_le {z : ℂ} {δ : ℝ}
    (hd : 0 < δ) (hd1 : δ ≤ 1) (hz : δ ≤ z.re) :
    ‖∑' k : ℕ, ((z + (k : ℂ))⁻¹ - ((k : ℂ) + 1)⁻¹)‖ ≤
      (1 + 1 / δ) * (1 + Real.log (2 + ‖z - 1‖)) + 1 / δ := by
  let N : ℕ := ⌈‖z - 1‖⌉₊ + 1
  have hN : 0 < N := Nat.succ_pos _
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hA : ‖z - 1‖ ≤ (N : ℝ) := by
    have h := Nat.le_ceil ‖z - 1‖
    dsimp only [N]
    push_cast
    linarith
  have hB : (N : ℝ) ≤ 2 + ‖z - 1‖ := by
    have h := Nat.ceil_lt_add_one (norm_nonneg (z - 1))
    dsimp only [N]
    push_cast
    linarith
  have hs := FleetDigammaSeries.summable_deriv_q (lt_of_lt_of_le hd hz)
  rw [← Summable.sum_add_tsum_nat_add N hs]
  refine (norm_add_le _ _).trans ?_
  calc
    _ ≤ (1 + 1 / δ) * (1 + Real.log N) + (‖z - 1‖ / δ) / (N : ℝ) :=
      add_le_add (norm_head_le N hd hd1 hz) (norm_tail_le N hN hd hd1 hz)
    _ ≤ (1 + 1 / δ) * (1 + Real.log (2 + ‖z - 1‖)) + 1 / δ := by
      apply add_le_add
      · gcongr
      · rw [div_div, mul_comm δ, ← div_div]
        apply div_le_div_of_nonneg_right _ hd.le
        exact (div_le_one hNr).mpr hA

/-- Explicit logarithmic bound for the derivative of the regularized Euler logarithm.
This theorem does not assume or use its identification with Gamma. -/
lemma norm_logDerivative_le {z : ℂ} {δ : ℝ}
    (hd : 0 < δ) (hd1 : δ ≤ 1) (hz : δ ≤ z.re) :
    ‖-(Real.eulerMascheroniConstant : ℂ) -
        ∑' k : ℕ, ((z + (k : ℂ))⁻¹ - ((k : ℂ) + 1)⁻¹)‖ ≤
      |Real.eulerMascheroniConstant| +
        (1 + 1 / δ) * (1 + Real.log (2 + ‖z - 1‖)) + 1 / δ := by
  refine (norm_sub_le _ _).trans ?_
  rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have h := norm_series_le hd hd1 hz
  linarith

lemma exists_logDerivative_bound (δ : ℝ) (hd : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, δ ≤ z.re →
      ‖-(Real.eulerMascheroniConstant : ℂ) -
        ∑' k : ℕ, ((z + (k : ℂ))⁻¹ - ((k : ℂ) + 1)⁻¹)‖ ≤
          C * (1 + Real.log (2 + ‖z - 1‖)) := by
  let m : ℝ := min δ 1
  have hm : 0 < m := lt_min hd zero_lt_one
  refine ⟨|Real.eulerMascheroniConstant| + 1 + 2 / m, by positivity, ?_⟩
  intro z hz
  have h := norm_logDerivative_le hm (min_le_right _ _) ((min_le_left _ _).trans hz)
  refine h.trans ?_
  have hl : 0 ≤ Real.log (2 + ‖z - 1‖) := Real.log_nonneg (by linarith [norm_nonneg (z - 1)])
  have hγ := mul_nonneg (abs_nonneg Real.eulerMascheroniConstant) hl
  have hmL := mul_nonneg (one_div_pos.mpr hm).le hl
  have he : 2 / m = 2 * (1 / m) := by ring
  rw [he]
  nlinarith


end FleetDigammaGrowth
