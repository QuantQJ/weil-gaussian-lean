import Mathlib

open Complex Filter Set
open scoped Topology

namespace FleetDigammaSeries

noncomputable def q (k : ℕ) (z : ℂ) : ℂ :=
  Complex.log (1 + (z - 1) / (k + 1)) - (z - 1) / (k + 1)

lemma nat_add_one_ne_zero (k : ℕ) : (k : ℂ) + 1 ≠ 0 := by
  exact_mod_cast Nat.succ_ne_zero k

lemma q_argument_eq (k : ℕ) (z : ℂ) :
    1 + (z - 1) / (k + 1) = (z + k) / (k + 1) := by
  field_simp [nat_add_one_ne_zero]
  ring

lemma q_argument_mem_slitPlane (k : ℕ) {z : ℂ} (hz : 0 < z.re) :
    1 + (z - 1) / (k + 1) ∈ Complex.slitPlane := by
  rw [q_argument_eq]
  apply Or.inl
  have h : 0 < (k : ℝ) + 1 := by positivity
  have he : (((z + k) / ((k : ℂ) + 1)).re) = (z.re + k) / (k + 1) := by
    simp [Complex.div_re, Complex.normSq, Complex.add_re]
    field_simp
  rw [he]
  exact div_pos (by positivity) h

lemma hasDerivAt_q (k : ℕ) {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (q k) ((z + k)⁻¹ - ((k : ℂ) + 1)⁻¹) z := by
  have hd := ((hasDerivAt_id z).sub_const 1).div_const ((k : ℂ) + 1)
  have hlog := (hd.const_add 1).clog (q_argument_mem_slitPlane k hz)
  have hn : z + (k : ℂ) ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    have : (0 : ℝ) ≤ k := by positivity
    linarith
  convert hlog.sub hd using 1
  · funext w
    rfl
  · simp only [id_eq]
    rw [q_argument_eq]
    field_simp [nat_add_one_ne_zero k, hn]

lemma norm_nat_add_one (k : ℕ) : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
  norm_cast

lemma norm_q_le_sq (k : ℕ) {z : ℂ}
    (h : ‖(z - 1) / ((k : ℂ) + 1)‖ ≤ 1 / 2) :
    ‖q k z‖ ≤ ‖(z - 1) / ((k : ℂ) + 1)‖ ^ 2 := by
  have hh : ‖(z - 1) / ((k : ℂ) + 1)‖ < 1 := by linarith
  have hb := Complex.norm_log_one_add_sub_self_le hh
  change ‖q k z‖ ≤ _ at hb
  refine hb.trans ?_
  have hinv : (1 - ‖(z - 1) / ((k : ℂ) + 1)‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
    linarith
  nlinarith [sq_nonneg ‖(z - 1) / ((k : ℂ) + 1)‖]

lemma norm_q_le (k : ℕ) {z : ℂ} {R : ℝ}
    (hz : ‖z - 1‖ ≤ R) (hk : 2 * R ≤ (k : ℝ) + 1) :
    ‖q k z‖ ≤ R ^ 2 / ((k : ℝ) + 1) ^ 2 := by
  have hp : 0 < (k : ℝ) + 1 := by positivity
  have hnorm : ‖(z - 1) / ((k : ℂ) + 1)‖ = ‖z - 1‖ / ((k : ℝ) + 1) := by
    rw [norm_div, norm_nat_add_one]
  have hh : ‖(z - 1) / ((k : ℂ) + 1)‖ ≤ 1 / 2 := by
    rw [hnorm, div_le_iff₀ hp]
    linarith
  refine (norm_q_le_sq k hh).trans ?_
  rw [hnorm, div_pow]
  gcongr

lemma norm_deriv_q_le (k : ℕ) {z : ℂ} {δ R : ℝ}
    (hd : 0 < δ) (hd1 : δ ≤ 1) (hz : δ ≤ z.re) (hR : ‖z - 1‖ ≤ R) :
    ‖(z + k)⁻¹ - ((k : ℂ) + 1)⁻¹‖ ≤
      R / (δ * ((k : ℝ) + 1) ^ 2) := by
  have hp : 0 < (k : ℝ) + 1 := by positivity
  have hre : δ * ((k : ℝ) + 1) ≤ ‖z + (k : ℂ)‖ := by
    have hh : (z + (k : ℂ)).re ≤ ‖z + (k : ℂ)‖ := Complex.re_le_norm _
    simp only [Complex.add_re, Complex.natCast_re] at hh
    have hk : (0 : ℝ) ≤ k := by positivity
    nlinarith
  have hn : z + (k : ℂ) ≠ 0 := by
    intro he
    rw [he, norm_zero] at hre
    exact (not_le_of_gt (mul_pos hd hp)) hre
  have he : (z + (k : ℂ))⁻¹ - ((k : ℂ) + 1)⁻¹ =
      -(z - 1) / ((z + k) * (k + 1)) := by
    field_simp [hn, nat_add_one_ne_zero k]
    ring
  rw [he, norm_div, norm_neg, norm_mul, norm_nat_add_one]
  calc
    ‖z - 1‖ / (‖z + (k : ℂ)‖ * ((k : ℝ) + 1)) ≤
        R / ((δ * ((k : ℝ) + 1)) * ((k : ℝ) + 1)) := by
      gcongr
      exact le_trans (norm_nonneg _) hR
    _ = R / (δ * ((k : ℝ) + 1) ^ 2) := by ring

lemma summable_majorant (C : ℝ) :
    Summable (fun k : ℕ => C / ((k : ℝ) + 1) ^ 2) := by
  have h : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hs := ((summable_nat_add_iff 1).mpr h).mul_left C
  refine hs.congr (fun k => ?_)
  push_cast
  ring

lemma summable_q (z : ℂ) : Summable (fun k => q k z) := by
  apply (summable_majorant (‖z - 1‖ ^ 2)).of_norm_bounded_eventually_nat
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * ‖z - 1‖)
  filter_upwards [eventually_ge_atTop N] with k hk
  apply norm_q_le k le_rfl
  have hh : (N : ℝ) ≤ k := by exact_mod_cast hk
  linarith

lemma summable_deriv_q {z : ℂ} (hz : 0 < z.re) :
    Summable (fun k : ℕ => (z + k)⁻¹ - ((k : ℂ) + 1)⁻¹) := by
  let δ := min z.re 1
  have hd : 0 < δ := lt_min hz zero_lt_one
  have hu : Summable (fun k : ℕ => ‖z - 1‖ / (δ * ((k : ℝ) + 1)^2)) := by
    simpa only [div_mul_eq_div_div] using summable_majorant (‖z - 1‖ / δ)
  apply hu.of_norm_bounded
  intro k
  exact norm_deriv_q_le k hd (min_le_right _ _) (min_le_left _ _) le_rfl

lemma hasDerivAt_tsum_q {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (fun w : ℂ => ∑' k : ℕ, q k w)
      (∑' k : ℕ, ((z + (k : ℂ))⁻¹ - ((k : ℂ) + 1)⁻¹)) z := by
  let δ : ℝ := min (z.re / 2) 1
  let r : ℝ := min (z.re / 2) 1
  let R : ℝ := ‖z - 1‖ + 1
  have hd : 0 < δ := lt_min (half_pos hz) zero_lt_one
  have hr : 0 < r := hd
  have hball : ∀ w ∈ Metric.ball z r, δ ≤ w.re ∧ ‖w - 1‖ ≤ R := by
    intro w hw
    have hw' : ‖w - z‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
    have hre : |(w - z).re| ≤ ‖w - z‖ := Complex.abs_re_le_norm _
    simp only [Complex.sub_re] at hre
    have hδ : δ ≤ z.re / 2 := min_le_left _ _
    have hr1 : r ≤ 1 := min_le_right _ _
    have hlow : δ ≤ w.re := by
      have := (abs_le.mp hre).1
      have hrhalf : r ≤ z.re / 2 := min_le_left _ _
      have := lt_of_lt_of_le hw' hrhalf
      linarith
    refine ⟨hlow, ?_⟩
    have hn := norm_add_le (w - z) (z - 1)
    rw [sub_add_sub_cancel] at hn
    change ‖w - 1‖ ≤ ‖z - 1‖ + 1
    linarith
  have hu : Summable (fun k : ℕ => R / (δ * ((k : ℝ) + 1)^2)) := by
    simpa only [div_mul_eq_div_div] using summable_majorant (R / δ)
  have huni := tendstoUniformlyOn_tsum_nat hu (s := Metric.ball z r)
    (f := fun k (w : ℂ) => (w + k)⁻¹ - ((k : ℂ) + 1)⁻¹)
    (fun k w hw => norm_deriv_q_le k hd (min_le_right _ _) (hball w hw).1 (hball w hw).2)
  apply hasDerivAt_of_tendstoUniformlyOn Metric.isOpen_ball huni
    (f := fun n w => ∑ k ∈ Finset.range n, q k w)
  · filter_upwards with n w hw
    exact HasDerivAt.fun_sum (fun k _ => hasDerivAt_q k (lt_of_lt_of_le hd (hball w hw).1))
  · intro w _
    exact (summable_q w).hasSum.tendsto_sum_nat
  · exact Metric.mem_ball_self hr

/-- The regularized Euler logarithm; identification of its exponential with Gamma
is a separate theorem and is not assumed here. -/
noncomputable def regularizedLogGamma (z : ℂ) : ℂ :=
  -(Real.eulerMascheroniConstant : ℂ) * (z - 1) - ∑' k : ℕ, q k z

lemma hasDerivAt_regularizedLogGamma {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt regularizedLogGamma
      (-(Real.eulerMascheroniConstant : ℂ) -
        ∑' k : ℕ, ((z + (k : ℂ))⁻¹ - ((k : ℂ) + 1)⁻¹)) z := by
  convert (((hasDerivAt_id z).sub_const 1).const_mul
    (-(Real.eulerMascheroniConstant : ℂ))).sub (hasDerivAt_tsum_q hz) using 1
  · funext w
    simp only [regularizedLogGamma, Pi.sub_apply, id_eq]
  · ring

lemma tendstoUniformlyOn_deriv_q {δ R : ℝ} (hd : 0 < δ) (hd1 : δ ≤ 1) :
    TendstoUniformlyOn
      (fun n (z : ℂ) => ∑ k ∈ Finset.range n,
        ((z + (k : ℂ))⁻¹ - ((k : ℂ) + 1)⁻¹))
      (fun z : ℂ => ∑' k : ℕ, ((z + (k : ℂ))⁻¹ - ((k : ℂ) + 1)⁻¹))
      atTop {z : ℂ | δ ≤ z.re ∧ ‖z - 1‖ ≤ R} := by
  have hu : Summable (fun k : ℕ => R / (δ * ((k : ℝ) + 1)^2)) := by
    simpa only [div_mul_eq_div_div] using summable_majorant (R / δ)
  exact tendstoUniformlyOn_tsum_nat hu
    (fun k z hz => norm_deriv_q_le k hd hd1 hz.1 hz.2)

lemma tendstoUniformlyOn_q (R : ℝ) :
    TendstoUniformlyOn (fun n (z : ℂ) => ∑ k ∈ Finset.range n, q k z)
      (fun z : ℂ => ∑' k : ℕ, q k z) atTop {z : ℂ | ‖z - 1‖ ≤ R} := by
  apply tendstoUniformlyOn_tsum_nat_eventually (summable_majorant (R^2))
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * R)
  filter_upwards [eventually_ge_atTop N] with k hk z hz
  apply norm_q_le k hz
  have hh : (N : ℝ) ≤ k := by exact_mod_cast hk
  linarith


end FleetDigammaSeries
