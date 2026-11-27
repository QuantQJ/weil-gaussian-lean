import Mathlib

noncomputable section
open Filter Topology MeasureTheory Set

namespace FleetWeightedTrace

def weight (t : ℝ) : ℝ := (1 + t^2)⁻¹

lemma continuous_weight : Continuous weight := by
  exact (continuous_const.add (continuous_id.pow 2)).inv₀ (fun t => (by positivity : (0 : ℝ) < 1 + t^2).ne')

lemma weight_pos (t : ℝ) : 0 < weight t := by unfold weight; positivity

/-- A weighted-vanishing continuous function has compact approximations with a
uniform pointwise error measured by the inverse-quadratic weight. -/
theorem exists_compact_approx {f : ℝ → ℂ} (hf : Continuous f)
    (hv : Tendsto (fun t : ℝ => (1+t^2)*‖f t‖) (cocompact ℝ) (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : ℝ → ℂ, Continuous φ ∧ HasCompactSupport φ ∧
      ∀ t, ‖f t - φ t‖ ≤ ε * weight t := by
  have hev : ∀ᶠ t in cocompact ℝ, (1+t^2)*‖f t‖ < ε :=
    (tendsto_order.1 hv).2 ε hε
  obtain ⟨K, hK, htail⟩ := Filter.mem_cocompact.1 hev
  obtain ⟨c, hcK, _, hcs, hc01⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (disjoint_empty K)
  refine ⟨fun t => c t • f t, c.continuous.smul hf, hcs.smul_right, ?_⟩
  intro t
  by_cases ht : t ∈ K
  · have hct : c t = 1 := hcK ht
    simp only [hct, one_smul, sub_self, norm_zero]
    exact mul_nonneg hε.le (weight_pos t).le
  · have hb : ‖f t‖ ≤ ε * weight t := by
      have hp : 0 < 1+t^2 := by positivity
      rw [weight, ← div_eq_mul_inv, le_div_iff₀ hp]
      have he : (1+t^2)*‖f t‖ < ε := htail ht
      rw [mul_comm]
      exact he.le
    have heq : f t - c t • f t = (1 - c t) • f t := by rw [sub_smul, one_smul]
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hc01 t).2)]
    have hcle : 1 - c t ≤ (1 : ℝ) := by linarith [(hc01 t).1]
    have hprod : (1-c t)*‖f t‖ ≤ ‖f t‖ := by
      simpa only [one_mul] using (mul_le_mul_of_nonneg_right hcle (norm_nonneg (f t)))
    exact hprod.trans hb

/-- Weighted decay ensures absolute integrability for every locally finite
measure with finite integral of the weight. -/
theorem integrable_of_weighted_vanishing {f : ℝ → ℂ} (hf : Continuous f)
    (hv : Tendsto (fun t : ℝ => (1+t^2)*‖f t‖) (cocompact ℝ) (𝓝 0))
    (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ] (hw : Integrable weight μ) :
    Integrable f μ := by
  obtain ⟨φ, hc, hs, herr⟩ := exists_compact_approx hf hv (show (0 : ℝ) < 1 by norm_num)
  have hφ : Integrable φ μ := hc.integrable_of_hasCompactSupport hs
  have hrem : Integrable (fun t => f t - φ t) μ := by
    apply hw.mono' (hf.sub hc).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun t => by simpa using herr t)
  convert hrem.add hφ using 1
  funext t
  simp

/-- A pointwise weighted error yields an integral error with the same mass bound. -/
theorem norm_integral_sub_le {f φ : ℝ → ℂ} {μ : Measure ℝ}
    (hf : Integrable f μ) (hφ : Integrable φ μ) (hw : Integrable weight μ)
    {ε M : ℝ} (hε : 0 ≤ ε) (hM : (∫ t, weight t ∂μ) ≤ M)
    (herr : ∀ t, ‖f t - φ t‖ ≤ ε * weight t) :
    ‖(∫ t, f t ∂μ) - (∫ t, φ t ∂μ)‖ ≤ ε * M := by
  rw [← integral_sub hf hφ]
  calc
    ‖∫ t, f t - φ t ∂μ‖ ≤ ∫ t, ε * weight t ∂μ :=
      norm_integral_le_of_norm_le (hw.const_mul ε) (Filter.Eventually.of_forall herr)
    _ = ε * ∫ t, weight t ∂μ := by simpa only [smul_eq_mul] using integral_smul ε weight
    _ ≤ ε * M := mul_le_mul_of_nonneg_left hM hε

/-- Compact-test convergence extends to every continuous function whose weighted
norm vanishes, provided the sequence and limit have uniformly bounded weight mass. -/
theorem integral_tendsto_of_compact_tests
    (μ : ℕ → Measure ℝ) (ν : Measure ℝ)
    [∀ n, IsFiniteMeasureOnCompacts (μ n)] [IsFiniteMeasureOnCompacts ν]
    (hwμ : ∀ n, Integrable weight (μ n)) (hwν : Integrable weight ν)
    {M : ℝ} (hM : 0 ≤ M)
    (hmμ : ∀ n, (∫ t, weight t ∂μ n) ≤ M)
    (hmν : (∫ t, weight t ∂ν) ≤ M)
    (hcompact : ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun n => ∫ t, φ t ∂μ n) atTop (𝓝 (∫ t, φ t ∂ν)))
    {f : ℝ → ℂ} (hf : Continuous f)
    (hv : Tendsto (fun t : ℝ => (1+t^2)*‖f t‖) (cocompact ℝ) (𝓝 0)) :
    Tendsto (fun n => ∫ t, f t ∂μ n) atTop (𝓝 (∫ t, f t ∂ν)) := by
  have hifμ (n : ℕ) := integrable_of_weighted_vanishing hf hv (μ n) (hwμ n)
  have hifν := integrable_of_weighted_vanishing hf hv ν hwν
  apply Metric.tendsto_nhds.2
  intro ε hε
  let δ : ℝ := ε / (4 * (M + 1))
  have hden : 0 < 4 * (M + 1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hδeq : δ * (4 * (M + 1)) = ε := div_mul_cancel₀ ε hden.ne'
  have hδM : 2 * (δ * M) < ε / 2 := by nlinarith
  obtain ⟨φ, hc, hs, herr⟩ := exists_compact_approx hf hv hδ
  have hiφμ (n : ℕ) : Integrable φ (μ n) := hc.integrable_of_hasCompactSupport hs
  have hiφν : Integrable φ ν := hc.integrable_of_hasCompactSupport hs
  have heμ (n : ℕ) := norm_integral_sub_le (hifμ n) (hiφμ n) (hwμ n) hδ.le (hmμ n) herr
  have heν := norm_integral_sub_le hifν hiφν hwν hδ.le hmν herr
  have hmid := (Metric.tendsto_nhds.1 (hcompact φ hc hs)) (ε/2) (by positivity)
  filter_upwards [hmid] with n hn
  have htri := dist_triangle (∫ t, f t ∂μ n) (∫ t, φ t ∂μ n) (∫ t, f t ∂ν)
  have htri' := dist_triangle (∫ t, φ t ∂μ n) (∫ t, φ t ∂ν) (∫ t, f t ∂ν)
  have heμ' : dist (∫ t, f t ∂μ n) (∫ t, φ t ∂μ n) ≤ δ*M := by
    simpa only [dist_eq_norm] using heμ n
  have heν' : dist (∫ t, φ t ∂ν) (∫ t, f t ∂ν) ≤ δ*M := by
    rw [dist_comm, dist_eq_norm]
    exact heν
  linarith

/-- Compact-test convergence passes the uniform weight bound to every compact
restriction of the limit measure. No global integrability of the limit is assumed. -/
theorem compact_weight_bound
    (μ : ℕ → Measure ℝ) (ν : Measure ℝ)
    [∀ n, IsFiniteMeasureOnCompacts (μ n)] [IsFiniteMeasureOnCompacts ν]
    (hwμ : ∀ n, Integrable weight (μ n)) {M : ℝ}
    (hmμ : ∀ n, (∫ t, weight t ∂μ n) ≤ M)
    (hcompact : ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun n => ∫ t, φ t ∂μ n) atTop (𝓝 (∫ t, φ t ∂ν)))
    {K : Set ℝ} (hK : IsCompact K) : (∫ t in K, weight t ∂ν) ≤ M := by
  obtain ⟨c, hcK, _, hcs, hc01⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (disjoint_empty K)
  let q : ℝ → ℝ := fun t => c t * weight t
  have hqcont : Continuous q := c.continuous.mul continuous_weight
  have hqsupp : HasCompactSupport q := hcs.mul_right
  have hqμ (n : ℕ) : Integrable q (μ n) := hqcont.integrable_of_hasCompactSupport hqsupp
  have hqν : Integrable q ν := hqcont.integrable_of_hasCompactSupport hqsupp
  have hqnonneg (t : ℝ) : 0 ≤ q t := mul_nonneg (hc01 t).1 (weight_pos t).le
  have hqle (t : ℝ) : q t ≤ weight t := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hc01 t).2 (weight_pos t).le
  have hqbound (n : ℕ) : (∫ t, q t ∂μ n) ≤ M :=
    (integral_mono (hqμ n) (hwμ n) hqle).trans (hmμ n)
  have hcc : Continuous (fun t => (q t : ℂ)) := Complex.continuous_ofReal.comp hqcont
  have hcs' : HasCompactSupport (fun t => (q t : ℂ)) :=
    hqsupp.comp_left (show ((0 : ℝ) : ℂ) = 0 by simp)
  have hcvg := (Complex.continuous_re.tendsto (∫ t, (q t : ℂ) ∂ν)).comp
    (hcompact (fun t => (q t : ℂ)) hcc hcs')
  have hcvg' : Tendsto (fun n => ∫ t, q t ∂μ n) atTop (𝓝 (∫ t, q t ∂ν)) := by
    simpa only [Function.comp_def, _root_.integral_complex_ofReal, Complex.ofReal_re] using hcvg
  have hlim : (∫ t, q t ∂ν) ≤ M := le_of_tendsto' hcvg' hqbound
  calc
    (∫ t in K, weight t ∂ν) = ∫ t in K, q t ∂ν := by
      apply setIntegral_congr_fun hK.measurableSet
      intro t ht
      have he : c t = 1 := hcK ht
      simp only [q, he, one_mul]
    _ ≤ ∫ t, q t ∂ν := setIntegral_le_integral hqν (Filter.Eventually.of_forall hqnonneg)
    _ ≤ M := hlim

/-- Uniform inverse-quadratic mass is inherited by the locally finite limit. -/
theorem weight_integrable_and_bound_of_compact_tests
    (μ : ℕ → Measure ℝ) (ν : Measure ℝ)
    [∀ n, IsFiniteMeasureOnCompacts (μ n)] [IsFiniteMeasureOnCompacts ν]
    (hwμ : ∀ n, Integrable weight (μ n)) {M : ℝ}
    (hmμ : ∀ n, (∫ t, weight t ∂μ n) ≤ M)
    (hcompact : ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun n => ∫ t, φ t ∂μ n) atTop (𝓝 (∫ t, φ t ∂ν))) :
    Integrable weight ν ∧ (∫ t, weight t ∂ν) ≤ M := by
  let K : ℕ → Set ℝ := fun n => Metric.closedBall (0 : ℝ) (n : ℝ)
  have hK (n : ℕ) : IsCompact (K n) := isCompact_closedBall 0 n
  have hcover : AECover ν atTop K := aecover_closedBall tendsto_natCast_atTop_atTop
  have hbound (n : ℕ) : (∫ t in K n, weight t ∂ν) ≤ M :=
    compact_weight_bound μ ν hwμ hmμ hcompact (hK n)
  have hi : Integrable weight ν :=
    hcover.integrable_of_integral_bounded_of_nonneg_ae M
      (fun n => continuous_weight.continuousOn.integrableOn_compact' (hK n) (hK n).measurableSet)
      (Filter.Eventually.of_forall (fun t => (weight_pos t).le))
      (Filter.Eventually.of_forall hbound)
  exact ⟨hi, le_of_tendsto' (hcover.integral_tendsto_of_countably_generated hi) hbound⟩

/-- Weighted trace passage with no separate assumption on the limit's mass. -/
theorem integral_tendsto_of_compact_tests_of_uniform_weight
    (μ : ℕ → Measure ℝ) (ν : Measure ℝ)
    [∀ n, IsFiniteMeasureOnCompacts (μ n)] [IsFiniteMeasureOnCompacts ν]
    (hwμ : ∀ n, Integrable weight (μ n)) {M : ℝ}
    (hmμ : ∀ n, (∫ t, weight t ∂μ n) ≤ M)
    (hcompact : ∀ φ : ℝ → ℂ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun n => ∫ t, φ t ∂μ n) atTop (𝓝 (∫ t, φ t ∂ν)))
    {f : ℝ → ℂ} (hf : Continuous f)
    (hv : Tendsto (fun t : ℝ => (1+t^2)*‖f t‖) (cocompact ℝ) (𝓝 0)) :
    Tendsto (fun n => ∫ t, f t ∂μ n) atTop (𝓝 (∫ t, f t ∂ν)) := by
  obtain ⟨hwν, hmν⟩ := weight_integrable_and_bound_of_compact_tests μ ν hwμ hmμ hcompact
  have hM : 0 ≤ M := (integral_nonneg (fun t => (weight_pos t).le)).trans (hmμ 0)
  exact integral_tendsto_of_compact_tests μ ν hwμ hwν hM hmμ hmν hcompact hf hv

end FleetWeightedTrace
