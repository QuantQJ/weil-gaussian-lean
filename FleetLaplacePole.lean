import Mathlib

/-!
# A bounded exponential series has no growing mode (Laplace-pole lemma)

Let `h y = ∑ₖ cₖ e^{λₖ y}` with `∑ ‖cₖ‖ < ∞`, `Re λₖ ≤ σ`, the points `λₖ` locally finite, and
`cₖ = g(λₖ)` for a nowhere-vanishing `g` (so equal points carry equal, nonzero coefficients).
If `h` is continuous and bounded on `[0, ∞)`, then `Re λₖ ≤ 0` for every `k`.

Proof (step 4 of `research_notes/DUAL-INEQUALITY/CONVERSE.md`). For `Re z > σ` the Laplace transform
`∫₀^∞ h(y) e^{-zy} dy` equals `∑ cₖ/(z − λₖ)`. The left side is holomorphic on `Re z > 0` (boundedness
of `h`); the right side is holomorphic off the points `λₖ`. If some `Re λₖ > 0`, take the rightmost
point `z₀` on its horizontal line; on a thin rectangle to the right of `z₀` both sides are holomorphic
and agree near its right end, hence everywhere on it (identity theorem). Approaching `z₀` from the
right, `(z − z₀)·(right side) → (#{k : λₖ = z₀}) g(z₀) ≠ 0` while `(z − z₀)·(left side) → 0`.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set MeasureTheory

namespace FleetLaplacePole

/-- A finite set on which `f` is positive has a positive lower bound for `f`. -/
lemma exists_pos_le_of_finite {ι : Type*} {s : Set ι} (hs : s.Finite) (f : ι → ℝ)
    (hf : ∀ k ∈ s, 0 < f k) : ∃ δ : ℝ, 0 < δ ∧ ∀ k ∈ s, δ ≤ f k := by
  rcases s.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · obtain ⟨a, ha, hmin⟩ := Set.exists_min_image s f hs h
    exact ⟨f a, hf a ha, hmin⟩

/-- Laplace transform on the half-line. -/
def lap (h : ℝ → ℂ) (z : ℂ) : ℂ := ∫ y in Ioi (0 : ℝ), h y * cexp (-(z * y))

lemma norm_cexp_neg_mul (z : ℂ) (y : ℝ) : ‖cexp (-(z * y))‖ = Real.exp (-(z.re * y)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- The Laplace transform of a bounded continuous function is holomorphic on `Re z > 0`. -/
theorem lap_differentiableAt {h : ℝ → ℂ} (hcont : Continuous h) {C : ℝ}
    (hbd : ∀ y : ℝ, 0 ≤ y → ‖h y‖ ≤ C) {z₁ : ℂ} (hz₁ : 0 < z₁.re) :
    DifferentiableAt ℂ (lap h) z₁ := by
  set a : ℝ := z₁.re / 2 with ha_def
  have ha : 0 < a := by positivity
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let F : ℂ → ℝ → ℂ := fun z y => h y * cexp (-(z * y))
  let F' : ℂ → ℝ → ℂ := fun z y => h y * (-(y : ℂ) * cexp (-(z * y)))
  have hC : 0 ≤ C := (norm_nonneg _).trans (hbd 0 le_rfl)
  have hmeasF : ∀ z, AEStronglyMeasurable (F z) μ := fun z =>
    (hcont.mul (by fun_prop)).aestronglyMeasurable
  have hmeasF' : ∀ z, AEStronglyMeasurable (F' z) μ := fun z =>
    (hcont.mul (by fun_prop)).aestronglyMeasurable
  have hball : ∀ z ∈ Metric.ball z₁ a, a ≤ z.re := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have := Complex.abs_re_le_norm (z - z₁)
    rw [Complex.sub_re] at this
    have h2 := (abs_le.mp (this.trans hz.le)).1
    rw [ha_def] at h2 ⊢; linarith
  have hexp_int : IntegrableOn (fun y : ℝ => Real.exp (-a * y)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 ha
  have hbound_int : Integrable (fun y : ℝ => C * (y * Real.exp (-a * y))) μ := by
    refine Integrable.const_mul ?_ C
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := a)
      (by norm_num) one_pos ha
    refine this.congr_fun (fun y hy => ?_) measurableSet_Ioi
    simp [Real.rpow_one]
  have hF_int : Integrable (F z₁) μ := by
    refine Integrable.mono' (hexp_int.const_mul C) (hmeasF z₁) ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono (fun y hy => ?_)
    simp only [F, norm_mul, norm_cexp_neg_mul]
    have hy0 : (0 : ℝ) < y := hy
    have h1 : Real.exp (-(z₁.re * y)) ≤ Real.exp (-a * y) := by
      apply Real.exp_le_exp.2; rw [ha_def]; nlinarith
    exact mul_le_mul (hbd y hy0.le) h1 (by positivity) hC
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (F' := F')
    (x₀ := z₁) (Metric.ball_mem_nhds z₁ (by positivity : (0:ℝ) < a))
    (Eventually.of_forall hmeasF) hF_int (hmeasF' z₁)
    (bound := fun y => C * (y * Real.exp (-a * y))) ?_ hbound_int ?_
  · exact hderiv.2.differentiableAt
  · refine (ae_restrict_mem measurableSet_Ioi).mono (fun y hy z hz => ?_)
    have hy0 : (0 : ℝ) < y := hy
    simp only [F', norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0,
      norm_cexp_neg_mul]
    have h1 : Real.exp (-(z.re * y)) ≤ Real.exp (-a * y) := by
      apply Real.exp_le_exp.2; have := hball z hz; nlinarith
    exact mul_le_mul (hbd y hy0.le) (mul_le_mul_of_nonneg_left h1 hy0.le) (by positivity) hC
  · refine Eventually.of_forall (fun y z _ => ?_)
    simp only [F, F']
    have h1 : HasDerivAt (fun z : ℂ => -(z * (y : ℂ))) (-(y : ℂ)) z := by
      have := ((hasDerivAt_id z).mul_const (y : ℂ)).neg
      convert this using 1
      · funext w; simp
      · simp
    have h2 := h1.cexp
    have h3 := h2.const_mul (h y)
    convert h3 using 1
    ring

/-- For `Re z > σ ≥ Re λₖ`, the Laplace transform of `∑ cₖ e^{λₖ y}` is `∑ cₖ/(z − λₖ)`. -/
theorem lap_eq_tsum {ι : Type*} [Countable ι] (c lam : ι → ℂ) (hsum : Summable (fun k => ‖c k‖))
    {σ : ℝ} (hσ : ∀ k, (lam k).re ≤ σ) {z : ℂ} (hz : σ < z.re) :
    lap (fun y : ℝ => ∑' k, c k * cexp (lam k * y)) z = ∑' k, c k / (z - lam k) := by
  unfold lap
  set b : ℝ := z.re - σ with hb_def
  have hb : 0 < b := by rw [hb_def]; linarith
  let F : ι → ℝ → ℂ := fun k y => c k * cexp ((lam k - z) * y)
  have hre : ∀ k, (lam k - z).re < 0 := by
    intro k; rw [Complex.sub_re]; linarith [hσ k]
  have hpt : ∀ y : ℝ, (∑' k, c k * cexp (lam k * y)) * cexp (-(z * y)) = ∑' k, F k y := by
    intro y
    rw [← tsum_mul_right]
    refine tsum_congr (fun k => ?_)
    simp only [F, mul_assoc, ← Complex.exp_add]
    congr 2; ring
  simp_rw [hpt]
  have hint : ∀ k, Integrable (F k) (volume.restrict (Ioi 0)) := fun k =>
    (integrableOn_exp_mul_complex_Ioi (hre k) 0).const_mul (c k)
  have hexp_int : IntegrableOn (fun y : ℝ => Real.exp (-b * y)) (Ioi 0) :=
    exp_neg_integrableOn_Ioi 0 hb
  have hnorm_le : ∀ k, ∫ y in Ioi (0:ℝ), ‖F k y‖ ≤ ‖c k‖ * ∫ y in Ioi (0:ℝ), Real.exp (-b * y) := by
    intro k
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall (fun y => norm_nonneg _))
      (hexp_int.const_mul _) ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono (fun y hy => ?_)
    have hy0 : (0 : ℝ) < y := hy
    simp only [F, norm_mul, Complex.norm_exp]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.2
    have : ((lam k - z) * (y : ℂ)).re = ((lam k).re - z.re) * y := by
      simp [Complex.mul_re]
    rw [this, hb_def]
    nlinarith [hσ k]
  have hsum_int : Summable (fun k => ∫ y in Ioi (0:ℝ), ‖F k y‖) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg (fun y => norm_nonneg _)) hnorm_le ?_
    exact hsum.mul_right _
  rw [← integral_tsum_of_summable_integral_norm hint hsum_int]
  refine tsum_congr (fun k => ?_)
  simp only [F]
  rw [integral_const_mul, integral_exp_mul_complex_Ioi (hre k) 0]
  have hne : lam k - z ≠ 0 := by
    intro h0; have := hre k; rw [h0, Complex.zero_re] at this; exact lt_irrefl _ this
  have hne' : z - lam k ≠ 0 := by
    intro h0; apply hne; rw [← neg_sub, h0, neg_zero]
  push_cast
  rw [mul_zero, Complex.exp_zero]
  field_simp
  ring

/-- `∑ cₖ/(z − λₖ)` is holomorphic at any point at positive distance from all `λₖ`. -/
theorem tsum_div_differentiableAt {ι : Type*} (c lam : ι → ℂ) (hsum : Summable (fun k => ‖c k‖))
    {z : ℂ} {r : ℝ} (hr : 0 < r) (hdist : ∀ k, r ≤ ‖z - lam k‖) :
    DifferentiableAt ℂ (fun w => ∑' k, c k / (w - lam k)) z := by
  have hd : DifferentiableOn ℂ (fun w => ∑' k, c k / (w - lam k)) (Metric.ball z (r / 2)) := by
    refine differentiableOn_tsum_of_summable_norm (u := fun k => ‖c k‖ * (2 / r))
      (hsum.mul_right _) (fun k => ?_) Metric.isOpen_ball (fun k w hw => ?_)
    · intro w hw
      apply DifferentiableAt.differentiableWithinAt
      apply DifferentiableAt.div (differentiableAt_const _) (differentiableAt_id.sub_const _)
      intro h0
      rw [Metric.mem_ball, dist_eq_norm] at hw
      have h1 := hdist k
      have : ‖z - lam k‖ ≤ ‖z - w‖ + ‖w - lam k‖ := by
        calc ‖z - lam k‖ = ‖(z - w) + (w - lam k)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      rw [h0, norm_zero, add_zero, norm_sub_rev z w] at this
      linarith
    · rw [Metric.mem_ball, dist_eq_norm] at hw
      have h1 := hdist k
      have h2 : ‖z - lam k‖ ≤ ‖z - w‖ + ‖w - lam k‖ := by
        calc ‖z - lam k‖ = ‖(z - w) + (w - lam k)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      rw [norm_sub_rev z w] at h2
      have h3 : r / 2 ≤ ‖w - lam k‖ := by linarith
      have h4 : 0 < ‖w - lam k‖ := by linarith
      rw [norm_div, div_le_iff₀ h4]
      calc ‖c k‖ = ‖c k‖ * (2 / r) * (r / 2) := by field_simp
        _ ≤ ‖c k‖ * (2 / r) * ‖w - lam k‖ :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
  exact hd.differentiableAt (Metric.ball_mem_nhds z (by positivity))

/-- **Laplace-pole lemma.** A continuous exponential series `∑ cₖ e^{λₖ y}`, bounded on `[0, ∞)`,
with summable coefficients `cₖ = g(λₖ)`, `g` nowhere zero, `Re λₖ ≤ σ` and locally finite points,
has `Re λₖ ≤ 0` for every `k`. -/
theorem re_nonpos_of_bounded {ι : Type*} [Countable ι] (c lam : ι → ℂ) (g : ℂ → ℂ)
    (hg : ∀ z, g z ≠ 0) (hc : ∀ k, c k = g (lam k))
    (hsum : Summable (fun k => ‖c k‖)) {σ : ℝ} (hσ : ∀ k, (lam k).re ≤ σ)
    (hfin : ∀ (z : ℂ) (r : ℝ), {k | ‖lam k - z‖ < r}.Finite)
    (hcont : Continuous (fun y : ℝ => ∑' k, c k * cexp (lam k * y)))
    {C : ℝ} (hbd : ∀ y : ℝ, 0 ≤ y → ‖∑' k, c k * cexp (lam k * y)‖ ≤ C) :
    ∀ k, (lam k).re ≤ 0 := by
  classical
  intro k₁
  by_contra hpos
  push Not at hpos
  set h : ℝ → ℂ := fun y => ∑' k, c k * cexp (lam k * y) with h_def
  set RHS : ℂ → ℂ := fun w => ∑' k, c k / (w - lam k) with RHS_def
  have hσ0 : 0 < σ := hpos.trans_le (hσ k₁)
  -- the rightmost point on the horizontal line of `λ k₁`
  set A : Set ι := {k | ‖lam k - lam k₁‖ < σ + 1 ∧ (lam k).im = (lam k₁).im ∧
    (lam k₁).re ≤ (lam k).re} with hA_def
  have hAfin : A.Finite := (hfin (lam k₁) (σ + 1)).subset (fun k hk => hk.1)
  have hk₁A : k₁ ∈ A := ⟨by rw [sub_self, norm_zero]; linarith, rfl, le_rfl⟩
  obtain ⟨k₀, hk₀A, hk₀max⟩ := Set.exists_max_image A (fun k => (lam k).re) hAfin ⟨k₁, hk₁A⟩
  set z₀ := lam k₀ with hz₀_def
  have hz₀re : 0 < z₀.re := hpos.trans_le hk₀A.2.2
  have hz₀σ : z₀.re ≤ σ := hσ k₀
  have hline : ∀ k, (lam k).im = z₀.im → (lam k).re ≤ z₀.re := by
    intro k hk
    by_contra hlt
    push Not at hlt
    have hkA : k ∈ A := by
      refine ⟨?_, hk.trans hk₀A.2.1, (hk₀A.2.2.trans hlt.le)⟩
      have him : (lam k - lam k₁).im = 0 := by
        rw [Complex.sub_im, hk, hk₀A.2.1, sub_self]
      have := Complex.norm_le_abs_re_add_abs_im (lam k - lam k₁)
      rw [him, abs_zero, add_zero, Complex.sub_re] at this
      have h1 : |(lam k).re - (lam k₁).re| ≤ σ := by
        rw [abs_le]; constructor <;> linarith [hσ k, hk₀A.2.2]
      linarith
    have := hk₀max k hkA
    linarith
  -- separation constants
  set R : ℝ := σ - z₀.re + 3 with hR_def
  have hR : 0 < R := by rw [hR_def]; linarith
  set B : Set ι := {k | ‖lam k - z₀‖ < R}
  have hBfin : B.Finite := hfin z₀ R
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_of_finite (hBfin.subset (fun k hk => hk.1) :
      ({k | k ∈ B ∧ (lam k).im ≠ z₀.im}).Finite) (fun k => |(lam k).im - z₀.im|)
    (fun k hk => abs_pos.2 (sub_ne_zero.2 hk.2))
  obtain ⟨ρ, hρ, hρle⟩ := exists_pos_le_of_finite (hBfin.subset (fun k hk => hk.1) :
      ({k | k ∈ B ∧ lam k ≠ z₀}).Finite) (fun k => ‖lam k - z₀‖)
    (fun k hk => norm_pos_iff.2 (sub_ne_zero.2 hk.2))
  set δ' := min δ 1 with hδ'_def
  have hδ' : 0 < δ' := lt_min hδ one_pos
  have hδ'1 : δ' ≤ 1 := min_le_right _ _
  set ρ' := min ρ R with hρ'_def
  have hρ' : 0 < ρ' := lt_min hρ hR
  have hfar : ∀ k, lam k ≠ z₀ → ρ' ≤ ‖lam k - z₀‖ := by
    intro k hk
    by_cases hkB : k ∈ B
    · exact (min_le_left _ _).trans (hρle k ⟨hkB, hk⟩)
    · have : R ≤ ‖lam k - z₀‖ := by simpa [B] using hkB
      exact (min_le_right _ _).trans this
  -- the rectangle
  set U : Set ℂ := Complex.re ⁻¹' Ioo z₀.re (σ + 1) ∩
    Complex.im ⁻¹' Ioo (z₀.im - δ' / 2) (z₀.im + δ' / 2) with hU_def
  have hUopen : IsOpen U :=
    (isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)
  have hUconv : Convex ℝ U :=
    ((convex_Ioo _ _).linear_preimage Complex.reLm).inter
      ((convex_Ioo _ _).linear_preimage Complex.imLm)
  -- every point of `U` is at positive distance from all `λ k`
  have hUdist : ∀ z ∈ U, ∃ r : ℝ, 0 < r ∧ ∀ k, r ≤ ‖z - lam k‖ := by
    intro z hz
    obtain ⟨⟨hz1, hz2⟩, ⟨hz3, hz4⟩⟩ := hz
    have hzim : |z.im - z₀.im| < δ' / 2 := by rw [abs_lt]; constructor <;> linarith
    have hzn : ‖z - z₀‖ < R := by
      have := Complex.norm_le_abs_re_add_abs_im (z - z₀)
      rw [Complex.sub_re, Complex.sub_im, abs_of_pos (by linarith : 0 < z.re - z₀.re)] at this
      rw [hR_def]; linarith
    refine ⟨min (δ' / 2 - |z.im - z₀.im|) (min (z.re - z₀.re) (R - ‖z - z₀‖)),
      lt_min (by linarith) (lt_min (by linarith) (by linarith)), fun k => ?_⟩
    by_cases hkB : k ∈ B
    · by_cases hkim : (lam k).im = z₀.im
      · have h1 := hline k hkim
        have h2 := Complex.abs_re_le_norm (z - lam k)
        rw [Complex.sub_re, abs_of_pos (by linarith)] at h2
        exact (min_le_right _ _).trans ((min_le_left _ _).trans (by linarith))
      · have h1 : δ ≤ |(lam k).im - z₀.im| := hδle k ⟨hkB, hkim⟩
        have h2 := Complex.abs_im_le_norm (z - lam k)
        rw [Complex.sub_im] at h2
        have h3 : |(lam k).im - z₀.im| ≤ |z.im - (lam k).im| + |z.im - z₀.im| := by
          calc |(lam k).im - z₀.im| = |(z.im - z₀.im) - (z.im - (lam k).im)| := by ring_nf
            _ ≤ |z.im - z₀.im| + |z.im - (lam k).im| := abs_sub _ _
            _ = _ := add_comm _ _
        have h4 : δ' ≤ δ := min_le_left _ _
        exact (min_le_left _ _).trans (by linarith)
    · have h1 : R ≤ ‖lam k - z₀‖ := by simpa [B] using hkB
      have h2 : ‖lam k - z₀‖ ≤ ‖z - lam k‖ + ‖z - z₀‖ := by
        calc ‖lam k - z₀‖ = ‖(z - z₀) - (z - lam k)‖ := by ring_nf
          _ ≤ ‖z - z₀‖ + ‖z - lam k‖ := norm_sub_le _ _
          _ = _ := add_comm _ _
      exact (min_le_right _ _).trans ((min_le_right _ _).trans (by linarith))
  -- analyticity of both sides on `U`
  have hC : 0 ≤ C := (norm_nonneg _).trans (hbd 0 le_rfl)
  have hlapU : AnalyticOnNhd ℂ (lap h) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
    exact (lap_differentiableAt hcont hbd (hz₀re.trans hz.1.1)).differentiableWithinAt
  have hRHSU : AnalyticOnNhd ℂ RHS U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
    obtain ⟨r, hr, hdist⟩ := hUdist z hz
    exact (tsum_div_differentiableAt c lam hsum hr hdist).differentiableWithinAt
  -- they agree near the right end of `U`
  set zs : ℂ := ((σ + 1 / 2 : ℝ) : ℂ) + z₀.im * I with hzs_def
  have hzs_re : zs.re = σ + 1 / 2 := by simp [hzs_def]
  have hzs_im : zs.im = z₀.im := by simp [hzs_def]
  have hzsU : zs ∈ U := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [hzs_re, hzs_im] <;> linarith
  have hev : lap h =ᶠ[𝓝 zs] RHS := by
    have hopen : IsOpen {w : ℂ | σ < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by simp only [mem_ofPred_eq, hzs_re]; linarith)] with w hw
    exact lap_eq_tsum c lam hsum hσ hw
  have heq : EqOn (lap h) RHS U :=
    hlapU.eqOn_of_preconnected_of_eventuallyEq hRHSU hUconv.isPreconnected hzsU hev
  -- approach `z₀` from the right
  set Fz : Set ι := {k | lam k = z₀} with hFz_def
  have hFzfin : Fz.Finite := (hfin z₀ 1).subset (fun k hk => by
    simp only [hFz_def, mem_ofPred_eq] at hk; simp [hk])
  have hk₀F : k₀ ∈ Fz := rfl
  set n₀ : ℕ := hFzfin.toFinset.card with hn₀_def
  have hn₀ : 1 ≤ n₀ := Finset.card_pos.2 ⟨k₀, hFzfin.mem_toFinset.2 hk₀F⟩
  set L : ℂ := (n₀ : ℂ) * g z₀ with hL_def
  have hL : L ≠ 0 := mul_ne_zero (by exact_mod_cast (show n₀ ≠ 0 by omega)) (hg z₀)
  -- left side: `ε · lap h (z₀ + ε) → 0`
  have hlim1 : Tendsto (fun ε : ℝ => (ε : ℂ) * lap h (z₀ + ε)) (𝓝[>] 0) (𝓝 0) := by
    have hca : ContinuousAt (fun ε : ℝ => (ε : ℂ) * lap h (z₀ + ε)) 0 := by
      apply ContinuousAt.mul (Complex.continuous_ofReal.continuousAt)
      have hd := (lap_differentiableAt hcont hbd (z₁ := z₀ + ((0 : ℝ) : ℂ))
        (by simpa using hz₀re)).continuousAt
      exact ContinuousAt.comp (g := lap h) (f := fun ε : ℝ => z₀ + (ε : ℂ)) hd (by fun_prop)
    have := hca.tendsto
    simp only [Complex.ofReal_zero, zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  -- right side: `ε · RHS (z₀ + ε) → L`
  set K : ℝ := (2 / ρ') * ∑' k, ‖c k‖ with hK_def
  have hbound : ∀ ε : ℝ, 0 < ε → ε < ρ' / 2 →
      ‖(ε : ℂ) * RHS (z₀ + ε) - L‖ ≤ K * ε := by
    intro ε hε hερ
    have hεC : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
    have hdk : ∀ k, lam k ≠ z₀ → ρ' / 2 ≤ ‖z₀ + ε - lam k‖ := by
      intro k hk
      have h1 := hfar k hk
      have h2 : ‖lam k - z₀‖ ≤ ‖z₀ + ε - lam k‖ + ε := by
        calc ‖lam k - z₀‖ = ‖(ε : ℂ) - (z₀ + ε - lam k)‖ := by ring_nf
          _ ≤ ‖(ε : ℂ)‖ + ‖z₀ + ε - lam k‖ := norm_sub_le _ _
          _ = _ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε, add_comm]
      linarith
    let d1 : ι → ℂ := fun k => (ε : ℂ) * (c k / (z₀ + ε - lam k))
    let d2 : ι → ℂ := fun k => if lam k = z₀ then c k else 0
    have hd1n : ∀ k, ‖d1 k‖ ≤ ‖c k‖ := by
      intro k
      simp only [d1, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
      by_cases hk : lam k = z₀
      · rw [hk, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
        field_simp; rfl
      · have h1 := hdk k hk
        have h2 : ε ≤ ‖z₀ + ε - lam k‖ := by linarith
        have h3 : 0 < ‖z₀ + ε - lam k‖ := by linarith
        rw [mul_div_assoc', div_le_iff₀ h3]
        nlinarith [mul_le_mul_of_nonneg_right h2 (norm_nonneg (c k))]
    have hd1s : Summable d1 := Summable.of_norm_bounded hsum hd1n
    have hd2s : Summable d2 := by
      apply summable_of_ne_finset_zero (s := hFzfin.toFinset)
      intro k hk
      simp only [d2]
      rw [if_neg]
      intro h'; exact hk (hFzfin.mem_toFinset.2 h')
    have hd2sum : ∑' k, d2 k = L := by
      rw [tsum_eq_sum (s := hFzfin.toFinset)]
      · rw [hL_def, hn₀_def, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun k hk => ?_)
        have hk' : lam k = z₀ := hFzfin.mem_toFinset.1 hk
        simp only [d2, if_pos hk', hc k, hk', Nat.cast_one, one_mul]
      · intro k hk
        simp only [d2]
        rw [if_neg]
        intro h'; exact hk (hFzfin.mem_toFinset.2 h')
    have hsplit : (ε : ℂ) * RHS (z₀ + ε) - L = ∑' k, (d1 k - d2 k) := by
      rw [hd1s.tsum_sub hd2s, hd2sum, RHS_def]
      simp only [d1]
      rw [tsum_mul_left]
    rw [hsplit]
    have hterm : ∀ k, ‖d1 k - d2 k‖ ≤ (2 / ρ') * ε * ‖c k‖ := by
      intro k
      by_cases hk : lam k = z₀
      · simp only [d1, d2, if_pos hk, hk, add_sub_cancel_left]
        rw [mul_div_cancel₀ _ hεC, sub_self, norm_zero]
        positivity
      · simp only [d1, d2, if_neg hk, sub_zero, norm_mul, norm_div, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hε]
        have h1 := hdk k hk
        have h3 : 0 < ‖z₀ + ε - lam k‖ := by linarith
        rw [mul_div_assoc', div_le_iff₀ h3]
        have : (2 / ρ') * ε * ‖c k‖ * (ρ' / 2) = ε * ‖c k‖ := by field_simp
        nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 2 / ρ') hε.le) (norm_nonneg (c k))]
    have hg' : HasSum (fun k => (2 / ρ') * ε * ‖c k‖) ((2 / ρ') * ε * ∑' k, ‖c k‖) :=
      (hsum.hasSum).mul_left _
    have := tsum_of_norm_bounded hg' hterm
    calc ‖∑' k, (d1 k - d2 k)‖ ≤ (2 / ρ') * ε * ∑' k, ‖c k‖ := this
      _ = K * ε := by rw [hK_def]; ring
  have hlim2 : Tendsto (fun ε : ℝ => (ε : ℂ) * RHS (z₀ + ε)) (𝓝[>] 0) (𝓝 L) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hKt : Tendsto (fun ε : ℝ => K * ε) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun ε : ℝ => K * ε) (𝓝 0) (𝓝 (K * 0)) := tendsto_const_nhds.mul tendsto_id
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero' (Eventually.of_forall (fun ε => norm_nonneg _)) ?_ hKt
    filter_upwards [Ioo_mem_nhdsGT (by positivity : (0:ℝ) < ρ' / 2)] with ε hε
    exact hbound ε hε.1 hε.2
  -- the two sides agree for small `ε > 0`
  have hagree : (fun ε : ℝ => (ε : ℂ) * lap h (z₀ + ε)) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ => (ε : ℂ) * RHS (z₀ + ε)) := by
    have hpos' : (0 : ℝ) < σ + 1 - z₀.re := by linarith
    filter_upwards [Ioo_mem_nhdsGT hpos'] with ε hε
    have hmem : z₀ + (ε : ℂ) ∈ U := by
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
        simp only [mem_preimage, Complex.add_re, Complex.add_im, Complex.ofReal_re,
          Complex.ofReal_im, add_zero] <;> linarith [hε.1, hε.2]
    rw [heq hmem]
  have := tendsto_nhds_unique (hlim1.congr' hagree) hlim2
  exact hL this.symm

end FleetLaplacePole
