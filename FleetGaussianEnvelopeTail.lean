import Mathlib

noncomputable section
open Filter Topology
namespace FleetGaussianEnvelopeTail

lemma shifted_polynomial_exp_tendsto (k : ℕ) :
    Tendsto (fun v : ℝ => (1+v)^k*Real.exp (-v)) atTop (𝓝 0) := by
  have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
    (tendsto_atTop_add_const_left atTop 1 tendsto_id)
  have hm := ht.mul_const (Real.exp 1)
  convert hm using 1
  · funext v
    dsimp only [Function.comp_def, id_eq]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  · simp

/-- Gaussian damping dominates the exponential C² envelope and every fixed polynomial degree. -/
theorem polynomial_gaussian_tendsto_atTop {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Tendsto (fun v : ℝ => (1+v)^k*Real.exp (-a*v^2+3*v)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (shifted_polynomial_exp_tendsto k)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with v hv
    positivity
  · filter_upwards [eventually_ge_atTop (max 0 (4/a))] with v hv
    have hv0 : 0 ≤ v := (le_max_left _ _).trans hv
    have hva : 4 ≤ a*v := by
      have hh : 4/a ≤ v := (le_max_right _ _).trans hv
      have hh' := (div_le_iff₀ ha).mp hh
      nlinarith
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith) k)
    apply Real.exp_le_exp.mpr
    have hh := mul_nonneg (sub_nonneg.mpr hva) hv0
    nlinarith

/-- The required two-sided tail statement, formulated on the cocompact filter. -/
theorem polynomial_gaussian_tendsto_cocompact {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Tendsto (fun u : ℝ => (1+|u|)^k*Real.exp (-a*u^2+3*|u|))
      (cocompact ℝ) (𝓝 0) := by
  have ht : Tendsto (fun u : ℝ => |u|) (cocompact ℝ) atTop := by
    exact (tendsto_norm_cocompact_atTop : Tendsto (fun u : ℝ => ‖u‖) (cocompact ℝ) atTop).congr
      (fun u => Real.norm_eq_abs u)
  simpa only [Function.comp_def, sq_abs] using (polynomial_gaussian_tendsto_atTop ha k).comp ht

/-- Uniform outside-radius form convenient for the periodization error. -/
theorem exists_tail_bound {a : ℝ} (ha : 0 < a) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ u : ℝ, R ≤ |u| →
      (1+|u|)^k*Real.exp (-a*u^2+3*|u|) < ε := by
  have he := (Metric.tendsto_nhds.mp (polynomial_gaussian_tendsto_atTop ha k)) ε hε
  obtain ⟨R, hR⟩ := eventually_atTop.mp he
  refine ⟨max R 0, le_max_right _ _, ?_⟩
  intro u hu
  have hh := hR |u| ((le_max_left R 0).trans hu)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hh
  simpa only [sq_abs] using hh

end FleetGaussianEnvelopeTail
