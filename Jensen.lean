import Mathlib

/-!
# Jensen's formula and zero counting on a disc

Everything in this file is PROVEN unconditionally (Lean's standard foundations only:
`propext`, `Classical.choice`, `Quot.sound`). Stages of the plan:

* **S1** `integral_circleMap_eq_two_pi_mul`, `integral_re_circleMap_eq_two_pi_mul`,
  `circle_mean_value`: mean value property `g c = (1/2π) ∫₀^{2π} g (c + R e^{iθ}) dθ` for `g`
  differentiable on the closed disc, and its real part (from Mathlib's Cauchy formula).
* **S2'** `differentiableOn_log_comp_of_mem_slitPlane`: `log ∘ g` is a holomorphic logarithm when
  `g` maps into the slit plane.
* **S2** `exists_differentiableOn_exp_eq_of_ne_zero`: a *general* holomorphic logarithm of a
  nonvanishing holomorphic `g` on an open disc, built from the term-wise primitive of the power
  series of `g'/g` (`hasDerivAt_primitive_of_hasFPowerSeriesOnBall`).
* **S3** `integral_log_norm_circleMap_sub_of_mem_ball` (interior zero: average is `log R`) and
  `integral_log_norm_circleMap_sub_of_not_mem_closedBall` (exterior point: average is `log ‖a-c‖`).
* **S4** `jensen_formula` / `jensen_formula_multiplicity`: Jensen's formula for
  `f = (∏ (z - aₖ)^{mₖ}) · g`, `g` holomorphic nonvanishing on a slightly larger disc.
* **S5** `card_mul_log_two_le_log`, `card_zeros_le_log_div_log_two`, `sum_mult_mul_log_two_le_log`:
  `#{zeros in ball c (R/2)} ≤ log M / log 2` when `‖f‖ ≤ M` on the circle and `‖f c‖ ≥ 1`.
* **Factorisation** `exists_factorization_of_finite_zeros`: a holomorphic `f` whose zero set in
  `ball c R'` is a finite `Z ⊆ ball c R` factors as `∏_{b∈Z} (z-b)^{m b} · g`, `m b ≥ 1`;
  hence `jensen_formula_of_finite_zeros` and `card_zeros_le_log_div_log_two_of_finite_zeros`
  are stated directly for `f` (no factorisation hypothesis).

Convention: "differentiable on a neighbourhood of the closed disc" is formalised as
differentiable on `ball c R'` with `R < R'`. Not proven: nothing from the target list is missing.
-/

noncomputable section

open Complex Metric Set
open scoped Real

namespace Jensen

/-! ## S1: the mean value property on a circle -/

/-- **S1 (mean value property, complex form).** If `g` is complex differentiable on the closed
disc `closedBall c R` (`R > 0`), then `∫ θ in 0..2π, g (c + R e^{iθ}) = 2π · g c`.
Here `circleMap c R θ = c + R * exp (θ * I)` definitionally. -/
theorem integral_circleMap_eq_two_pi_mul {c : ℂ} {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (closedBall c R)) :
    (∫ θ in (0 : ℝ)..(2 * π), g (circleMap c R θ)) = 2 * π * g c := by
  have h := hg.circleIntegral_sub_inv_smul (mem_ball_self hR)
  simp only [circleIntegral, deriv_circleMap, circleMap_sub_center, smul_eq_mul] at h
  have h2 : ∀ θ : ℝ,
      circleMap 0 R θ * I * ((circleMap 0 R θ)⁻¹ * g (circleMap c R θ)) = I * g (circleMap c R θ) := by
    intro θ
    have hne : circleMap 0 R θ ≠ 0 := circleMap_ne_center hR.ne'
    field_simp
  simp_rw [h2] at h
  rw [intervalIntegral.integral_const_mul] at h
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have h3 : I * (∫ θ in (0 : ℝ)..(2 * π), g (circleMap c R θ)) = I * (2 * π * g c) := by
    rw [h]; ring
  exact mul_left_cancel₀ hI h3

/-- **S1 (mean value property, real part).** For `g` complex differentiable on `closedBall c R`,
`∫ θ in 0..2π, Re (g (c + R e^{iθ})) = 2π · Re (g c)`. -/
theorem integral_re_circleMap_eq_two_pi_mul {c : ℂ} {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (closedBall c R)) :
    (∫ θ in (0 : ℝ)..(2 * π), (g (circleMap c R θ)).re) = 2 * π * (g c).re := by
  have hcont : Continuous (fun θ : ℝ => g (circleMap c R θ)) :=
    hg.continuousOn.comp_continuous (continuous_circleMap c R)
      (fun θ => circleMap_mem_closedBall c hR.le θ)
  have hint : IntervalIntegrable (fun θ : ℝ => g (circleMap c R θ)) MeasureTheory.volume 0 (2 * π) :=
    hcont.intervalIntegrable 0 (2 * π)
  have h2 := Complex.reCLM.intervalIntegral_comp_comm hint
  simp only [Complex.reCLM_apply] at h2
  rw [h2, integral_circleMap_eq_two_pi_mul hR hg]
  have : (2 * π * g c : ℂ) = ((2 * π : ℝ) : ℂ) * g c := by push_cast; ring
  rw [this, Complex.re_ofReal_mul]

/-- **S1 (normalised form).** `g c = (1/2π) ∫ θ in 0..2π, g (c + R e^{iθ})`. -/
theorem circle_mean_value {c : ℂ} {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (closedBall c R)) :
    g c = (2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), g (c + R * exp (θ * I)) := by
  have h := integral_circleMap_eq_two_pi_mul hR hg
  simp only [circleMap] at h
  rw [h]
  have hπ : (2 * π : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  field_simp


/-! ## S2': a holomorphic logarithm when the values stay in the slit plane -/

/-- **S2' (holomorphic logarithm, slit-plane case).** If `g` is complex differentiable on `s` and
maps `s` into the slit plane `ℂ ∖ (-∞, 0]`, then `log ∘ g` is complex differentiable on `s` and
`exp (log (g z)) = g z` on `s`. -/
theorem differentiableOn_log_comp_of_mem_slitPlane {s : Set ℂ} {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g s) (hs : ∀ z ∈ s, g z ∈ slitPlane) :
    DifferentiableOn ℂ (fun z => log (g z)) s ∧ ∀ z ∈ s, exp (log (g z)) = g z :=
  ⟨hg.clog hs, fun z hz => exp_log (slitPlane_ne_zero (hs z hz))⟩

/-! ## S3: the circle average of `log ‖z - a‖` -/

/-- Algebraic identity behind S3: on the circle `‖z - c‖ = R`,
`‖R² - conj (a - c) · (z - c)‖ = R · ‖z - a‖`. -/
theorem norm_sq_sub_conj_mul_of_mem_sphere {c a z : ℂ} {R : ℝ} (hz : z ∈ sphere c R) :
    ‖(R : ℂ) ^ 2 - (starRingEnd ℂ) (a - c) * (z - c)‖ = R * ‖z - a‖ := by
  have hu : ‖z - c‖ = R := mem_sphere_iff_norm.mp hz
  have h1 : (z - c) * (starRingEnd ℂ) (z - c) = (R : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]; push_cast; ring
  have key : (R : ℂ) ^ 2 - (starRingEnd ℂ) (a - c) * (z - c) = (z - c) * (starRingEnd ℂ) (z - a) := by
    have h2 : (starRingEnd ℂ) (z - a) = (starRingEnd ℂ) (z - c) - (starRingEnd ℂ) (a - c) := by
      rw [← map_sub]; congr 1; ring
    linear_combination -h1 - (z - c) * h2
  rw [key, norm_mul, hu, Complex.norm_conj]

/-- **S3 (single zero factor, interior case).** For `a` in the open disc `ball c R`,
`∫ θ in 0..2π, log ‖c + R e^{iθ} - a‖ = 2π · log R`. -/
theorem integral_log_norm_circleMap_sub_of_mem_ball {c a : ℂ} {R : ℝ} (hR : 0 < R)
    (ha : a ∈ ball c R) :
    (∫ θ in (0 : ℝ)..(2 * π), Real.log ‖circleMap c R θ - a‖) = 2 * π * Real.log R := by
  set w : ℂ := (starRingEnd ℂ) (a - c) with hw
  have haR : ‖a - c‖ < R := mem_ball_iff_norm.mp ha
  have hwn : ‖w‖ < R := by
    rw [hw, Complex.norm_conj]; exact haR
  have hslit : ∀ z ∈ closedBall c R, (R : ℂ) ^ 2 - w * (z - c) ∈ slitPlane := by
    intro z hz
    have hz' : ‖z - c‖ ≤ R := mem_closedBall_iff_norm.mp hz
    rw [mem_slitPlane_iff]; left
    have h1 : (w * (z - c)).re ≤ ‖w * (z - c)‖ := by
      skip; exact Complex.re_le_norm _
    have h2 : ‖w * (z - c)‖ ≤ ‖w‖ * R := by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left hz' (norm_nonneg _)
    have h3 : ‖w‖ * R < R * R := by nlinarith [norm_nonneg w]
    have h4 : ((R : ℂ) ^ 2 - w * (z - c)).re = R ^ 2 - (w * (z - c)).re := by
      rw [Complex.sub_re, ← Complex.ofReal_pow, Complex.ofReal_re]
    rw [h4]; nlinarith
  have hdiff : DifferentiableOn ℂ (fun z => log ((R : ℂ) ^ 2 - w * (z - c))) (closedBall c R) := by
    apply DifferentiableOn.clog _ hslit
    fun_prop
  have hmean := integral_re_circleMap_eq_two_pi_mul hR hdiff
  have hc : (log ((R : ℂ) ^ 2 - w * (c - c))).re = 2 * Real.log R := by
    rw [sub_self, mul_zero, sub_zero, Complex.log_re, ← Complex.ofReal_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (pow_pos hR 2), Real.log_pow]
    push_cast; ring
  have hcirc : ∀ θ : ℝ, (log ((R : ℂ) ^ 2 - w * (circleMap c R θ - c))).re
      = Real.log R + Real.log ‖circleMap c R θ - a‖ := by
    intro θ
    have hne : circleMap c R θ - a ≠ 0 := sub_ne_zero.mpr (circleMap_ne_mem_ball ha θ)
    rw [Complex.log_re, hw,
      norm_sq_sub_conj_mul_of_mem_sphere (circleMap_mem_sphere c hR.le θ),
      Real.log_mul hR.ne' (norm_ne_zero_iff.mpr hne)]
  simp only [hcirc, hc] at hmean
  have hcont : Continuous (fun θ : ℝ => Real.log ‖circleMap c R θ - a‖) :=
    (continuous_norm.comp ((continuous_circleMap c R).sub continuous_const)).log
      (fun θ => norm_ne_zero_iff.mpr (sub_ne_zero.mpr (circleMap_ne_mem_ball ha θ)))
  have hint : IntervalIntegrable (fun θ : ℝ => Real.log ‖circleMap c R θ - a‖)
      MeasureTheory.volume 0 (2 * π) := hcont.intervalIntegrable 0 (2 * π)
  rw [intervalIntegral.integral_add intervalIntegrable_const hint,
    intervalIntegral.integral_const] at hmean
  simp only [smul_eq_mul, sub_zero] at hmean
  linarith

/-- **S3 (single zero factor, exterior case).** For `a` outside the closed disc, i.e. `R < ‖a - c‖`,
`∫ θ in 0..2π, log ‖c + R e^{iθ} - a‖ = 2π · log ‖a - c‖`. -/
theorem integral_log_norm_circleMap_sub_of_not_mem_closedBall {c a : ℂ} {R : ℝ} (hR : 0 < R)
    (ha : R < ‖a - c‖) :
    (∫ θ in (0 : ℝ)..(2 * π), Real.log ‖circleMap c R θ - a‖) = 2 * π * Real.log ‖a - c‖ := by
  have hca : c - a ≠ 0 := by
    intro h; rw [← neg_sub, h, neg_zero, norm_zero] at ha; exact absurd ha (not_lt.mpr hR.le)
  have hslit : ∀ z ∈ closedBall c R, 1 + (z - c) / (c - a) ∈ slitPlane := by
    intro z hz
    apply mem_slitPlane_of_norm_lt_one
    have hz' : ‖z - c‖ ≤ R := mem_closedBall_iff_norm.mp hz
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hca), ← neg_sub a c, norm_neg]
    exact hz'.trans_lt ha
  have hdiff : DifferentiableOn ℂ (fun z => log (1 + (z - c) / (c - a))) (closedBall c R) := by
    apply DifferentiableOn.clog _ hslit
    fun_prop (disch := exact hca)
  have hmean := integral_re_circleMap_eq_two_pi_mul hR hdiff
  have hc : (log (1 + (c - c) / (c - a))).re = 0 := by
    rw [sub_self, zero_div, add_zero, Complex.log_one, Complex.zero_re]
  have hne' : ∀ θ : ℝ, circleMap c R θ - a ≠ 0 := by
    intro θ h
    have h' : a = circleMap c R θ := (sub_eq_zero.mp h).symm
    have : ‖a - c‖ = R := by
      rw [h', circleMap_sub_center, norm_circleMap_zero, abs_of_pos hR]
    linarith
  have heq : ∀ z : ℂ, 1 + (z - c) / (c - a) = (z - a) / (c - a) := by
    intro z; field_simp; ring
  have hcirc : ∀ θ : ℝ, (log (1 + (circleMap c R θ - c) / (c - a))).re
      = Real.log ‖circleMap c R θ - a‖ - Real.log ‖a - c‖ := by
    intro θ
    rw [heq, Complex.log_re, norm_div,
      Real.log_div (norm_ne_zero_iff.mpr (hne' θ)) (norm_ne_zero_iff.mpr hca), ← norm_neg (c - a),
      neg_sub]
  simp only [hcirc, hc, mul_zero] at hmean
  have hcont : Continuous (fun θ : ℝ => Real.log ‖circleMap c R θ - a‖) :=
    (continuous_norm.comp ((continuous_circleMap c R).sub continuous_const)).log
      (fun θ => norm_ne_zero_iff.mpr (hne' θ))
  have hint : IntervalIntegrable (fun θ : ℝ => Real.log ‖circleMap c R θ - a‖)
      MeasureTheory.volume 0 (2 * π) := hcont.intervalIntegrable 0 (2 * π)
  rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
    intervalIntegral.integral_const] at hmean
  simp only [smul_eq_mul, sub_zero] at hmean
  linarith

/-! ## S2: a holomorphic logarithm of a nonvanishing function on a disc -/

/-- Term-wise antiderivative of a power series. If `h` has the power series `p` on `ball c r`,
then `L z := ∑' n, p.coeff n * (z - c)^(n+1) / (n+1)` satisfies `L' = h` on `ball c r`. -/
theorem hasDerivAt_primitive_of_hasFPowerSeriesOnBall {h : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {c : ℂ} {r : NNReal} (hp : HasFPowerSeriesOnBall h p c r)
    {z : ℂ} (hz : z ∈ ball c r) :
    HasDerivAt (fun z => ∑' n : ℕ, p.coeff n * (z - c) ^ (n + 1) / (n + 1)) (h z) z := by
  have hzr : nndist z c < r := by
    rw [← NNReal.coe_lt_coe, coe_nndist]; exact mem_ball.mp hz
  obtain ⟨r', hzr', hr'r⟩ := exists_between hzr
  have hr'rad : (r' : ENNReal) < p.radius := (ENNReal.coe_lt_coe.mpr hr'r).trans_le hp.r_le
  have hu : Summable (fun n : ℕ => ‖p n‖ * (r' : ℝ) ^ n) := p.summable_norm_mul_pow hr'rad
  have hz' : z ∈ ball c r' := by
    rw [mem_ball, ← coe_nndist, NNReal.coe_lt_coe]; exact hzr'
  have hderiv := hasDerivAt_tsum_of_isPreconnected hu isOpen_ball (convex_ball c (r' : ℝ)).isPreconnected
    (g := fun n z => p.coeff n * (z - c) ^ (n + 1) / (n + 1))
    (g' := fun n z => p.coeff n * (z - c) ^ n)
    (fun n y _ => by
      have h1 : HasDerivAt (fun y => (y - c) ^ (n + 1)) (((n + 1 : ℕ) : ℂ) * (y - c) ^ (n + 1 - 1) * 1) y :=
        ((hasDerivAt_id y).sub_const c).pow (n + 1)
      have h2 := (h1.const_mul (p.coeff n)).div_const ((n : ℂ) + 1)
      convert h2 using 1
      have : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
      field_simp
      rw [Nat.add_sub_cancel]
      push_cast
      ring)
    (fun n y hy => by
      have hy' : ‖y - c‖ < r' := mem_ball_iff_norm.mp hy
      rw [norm_mul, norm_pow, p.norm_apply_eq_norm_coef]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hy'.le n) (norm_nonneg _))
    (mem_ball_self (by exact_mod_cast zero_le.trans_lt hzr' : (0 : ℝ) < r'))
    (by simp)
    hz'
  have hsum : HasSum (fun n : ℕ => p.coeff n * (z - c) ^ n) (h z) := by
    have hmem : z - c ∈ Metric.eball (0 : ℂ) r := by
      rw [Metric.eball_coe, mem_ball_zero_iff]; exact mem_ball_iff_norm.mp hz
    have := hp.hasSum hmem
    simp only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul, add_sub_cancel] at this
    simpa only [mul_comm] using this
  rw [← hsum.tsum_eq]
  exact hderiv

/-- A function differentiable on an open disc has a single power series at the centre that
converges on every smaller closed disc. -/
theorem exists_hasFPowerSeriesOnBall_of_differentiableOn_ball {c : ℂ} {R : ℝ} (hR : 0 < R)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (ball c R)) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, ∀ r : NNReal, 0 < r → (r : ℝ) < R →
      HasFPowerSeriesOnBall h p c r := by
  have key : ∀ r : NNReal, 0 < r → (r : ℝ) < R →
      HasFPowerSeriesOnBall h (cauchyPowerSeries h c r) c r := by
    intro r hr hrR
    exact (hh.mono (closedBall_subset_ball hrR)).hasFPowerSeriesOnBall hr
  set r₀ : NNReal := ⟨R / 2, by positivity⟩ with hr₀
  have hr₀pos : 0 < r₀ := by
    rw [← NNReal.coe_pos]; show (0 : ℝ) < R / 2; positivity
  have hr₀R : (r₀ : ℝ) < R := by show R / 2 < R; linarith
  refine ⟨cauchyPowerSeries h c r₀, fun r hr hrR => ?_⟩
  have h1 := key r hr hrR
  have h2 := key r₀ hr₀pos hr₀R
  have := h1.hasFPowerSeriesAt.eq_formalMultilinearSeries h2.hasFPowerSeriesAt
  rwa [this] at h1

/-- **S2 (holomorphic logarithm on a disc).** If `g` is complex differentiable and nonvanishing on
the open disc `ball c R` (`R > 0`), then there is `L` complex differentiable on `ball c R` with
`exp (L z) = g z` for all `z ∈ ball c R`. The logarithm is built as `log (g c)` plus the term-wise
primitive of the power series of `g'/g` at `c`. -/
theorem exists_differentiableOn_exp_eq_of_ne_zero {c : ℂ} {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball c R)) (hg0 : ∀ z ∈ ball c R, g z ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L (ball c R) ∧ ∀ z ∈ ball c R, exp (L z) = g z := by
  have hgan : AnalyticOnNhd ℂ g (ball c R) := hg.analyticOnNhd isOpen_ball
  have hd : DifferentiableOn ℂ (deriv g) (ball c R) := hgan.deriv.differentiableOn
  have hhd : DifferentiableOn ℂ (fun z => deriv g z / g z) (ball c R) := hd.div hg hg0
  obtain ⟨p, hp⟩ := exists_hasFPowerSeriesOnBall_of_differentiableOn_ball hR hhd
  set L₀ : ℂ → ℂ := fun z => ∑' n : ℕ, p.coeff n * (z - c) ^ (n + 1) / (n + 1) with hL₀
  have hL₀d : ∀ z ∈ ball c R, HasDerivAt L₀ (deriv g z / g z) z := by
    intro z hz
    obtain ⟨r, hzr, hrR⟩ := exists_between (mem_ball_iff_norm.mp hz)
    have hr0 : 0 < r := (norm_nonneg _).trans_lt hzr
    have hp' := hp (Real.toNNReal r) (Real.toNNReal_pos.mpr hr0)
      (by rw [Real.coe_toNNReal _ hr0.le]; exact hrR)
    exact hasDerivAt_primitive_of_hasFPowerSeriesOnBall hp'
      (by rw [mem_ball_iff_norm, Real.coe_toNNReal _ hr0.le]; exact hzr)
  have hL₀c : L₀ c = 0 := by simp [hL₀]
  refine ⟨fun z => L₀ z + log (g c), ?_, ?_⟩
  · intro z hz
    exact ((hL₀d z hz).differentiableAt.add_const _).differentiableWithinAt
  · set F : ℂ → ℂ := fun z => g z * exp (-(L₀ z + log (g c))) with hF
    have hFd : ∀ z ∈ ball c R, HasDerivAt F 0 z := by
      intro z hz
      have h1 : HasDerivAt g (deriv g z) z :=
        (hg.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
      have h2 : HasDerivAt (fun z => exp (-(L₀ z + log (g c))))
          (exp (-(L₀ z + log (g c))) * (-(deriv g z / g z))) z :=
        (((hL₀d z hz).add_const _).neg).cexp
      have h3 := h1.mul h2
      convert h3 using 1
      field_simp [hg0 z hz]
      ring
    have hFconst : ∀ z ∈ ball c R, F z = F c := by
      intro z hz
      refine Convex.is_const_of_fderivWithin_eq_zero (convex_ball c R)
        (fun x hx => (hFd x hx).differentiableAt.differentiableWithinAt) ?_ hz (mem_ball_self hR)
      intro x hx
      rw [fderivWithin_of_isOpen isOpen_ball hx, ← toSpanSingleton_deriv, (hFd x hx).deriv]
      ext; simp
    have hFc : F c = 1 := by
      simp only [hF, hL₀c, zero_add, Complex.exp_neg, exp_log (hg0 c (mem_ball_self hR))]
      exact mul_inv_cancel₀ (hg0 c (mem_ball_self hR))
    intro z hz
    have := hFconst z hz
    rw [hFc] at this
    simp only [hF, Complex.exp_neg] at this
    exact ((mul_inv_eq_one₀ (Complex.exp_ne_zero _)).mp this).symm


/-! ## S4: Jensen's formula -/

/-- Pointwise splitting of `log ‖f z‖` under the factorisation `f = (∏ (z - aₖ)^{mₖ}) · g`. -/
theorem log_norm_eq_sum_add_log_norm {ι : Type*} {c : ℂ} {R : ℝ} {s : Finset ι} {a : ι → ℂ}
    {m : ι → ℕ} {f g : ℂ → ℂ}
    (hfg : ∀ z ∈ closedBall c R, f z = (∏ k ∈ s, (z - a k) ^ m k) * g z) {z : ℂ}
    (hz : z ∈ closedBall c R) (hza : ∀ k ∈ s, z ≠ a k) (hgz : g z ≠ 0) :
    Real.log ‖f z‖ = ∑ k ∈ s, m k * Real.log ‖z - a k‖ + Real.log ‖g z‖ := by
  have hne : ∀ k ∈ s, ‖(z - a k) ^ m k‖ ≠ 0 :=
    fun k hk => norm_ne_zero_iff.mpr (pow_ne_zero _ (sub_ne_zero.mpr (hza k hk)))
  rw [hfg z hz, norm_mul, norm_prod,
    Real.log_mul (Finset.prod_ne_zero_iff.mpr hne) (norm_ne_zero_iff.mpr hgz),
    Real.log_prod hne]
  simp only [norm_pow, Real.log_pow]

/-- **S4 (Jensen's formula, with multiplicities).** Let `R > 0`, let `a k` (`k ∈ s`) be points of
the open disc `ball c R` with multiplicities `m k`, none equal to `c`, and suppose
`f z = (∏ k ∈ s, (z - a k) ^ m k) * g z` on `closedBall c R`, where `g` is complex differentiable
and nonvanishing on a slightly larger open disc `ball c R'` (`R < R'`). Then
`log ‖f c‖ = (1/2π) ∫ θ in 0..2π, log ‖f (c + R e^{iθ})‖ - ∑ k ∈ s, m k · log (R / ‖a k - c‖)`.
The holomorphic logarithm of `g` is supplied by `exists_differentiableOn_exp_eq_of_ne_zero`. -/
theorem jensen_formula_multiplicity {ι : Type*} {c : ℂ} {R R' : ℝ} (hR : 0 < R) (hRR' : R < R')
    {s : Finset ι} {a : ι → ℂ} {m : ι → ℕ} (ha : ∀ k ∈ s, a k ∈ ball c R)
    (hac : ∀ k ∈ s, a k ≠ c) {f g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball c R')) (hg0 : ∀ z ∈ ball c R', g z ≠ 0)
    (hfg : ∀ z ∈ closedBall c R, f z = (∏ k ∈ s, (z - a k) ^ m k) * g z) :
    Real.log ‖f c‖ = (2 * π)⁻¹ * (∫ θ in (0 : ℝ)..(2 * π), Real.log ‖f (c + R * exp (θ * I))‖)
      - ∑ k ∈ s, m k * Real.log (R / ‖a k - c‖) := by
  have hR' : 0 < R' := hR.trans hRR'
  obtain ⟨L, hL, hLg⟩ := exists_differentiableOn_exp_eq_of_ne_zero hR' hg hg0
  have hsub : closedBall c R ⊆ ball c R' := closedBall_subset_ball hRR'
  have hLc : DifferentiableOn ℂ L (closedBall c R) := hL.mono hsub
  -- `log ‖g z‖ = Re (L z)` on the closed disc
  have hlogg : ∀ z ∈ closedBall c R, Real.log ‖g z‖ = (L z).re := by
    intro z hz
    rw [← hLg z (hsub hz), Complex.norm_exp, Real.log_exp]
  -- mean value of `Re L`
  have hmean := integral_re_circleMap_eq_two_pi_mul hR hLc
  -- pointwise identity on the circle
  have hcirc : ∀ θ : ℝ, Real.log ‖f (circleMap c R θ)‖
      = ∑ k ∈ s, m k * Real.log ‖circleMap c R θ - a k‖ + (L (circleMap c R θ)).re := by
    intro θ
    have hmem := circleMap_mem_closedBall c hR.le θ
    rw [log_norm_eq_sum_add_log_norm hfg hmem (fun k hk => circleMap_ne_mem_ball (ha k hk) θ)
      (hg0 _ (hsub hmem)), hlogg _ hmem]
  -- value at the centre
  have hcenter : Real.log ‖f c‖ = ∑ k ∈ s, m k * Real.log ‖c - a k‖ + (L c).re := by
    have hmem : c ∈ closedBall c R := mem_closedBall_self hR.le
    rw [log_norm_eq_sum_add_log_norm hfg hmem (fun k hk => (hac k hk).symm) (hg0 _ (hsub hmem)),
      hlogg _ hmem]
  -- integrability
  have hcontk : ∀ k ∈ s, Continuous (fun θ : ℝ => (m k : ℝ) * Real.log ‖circleMap c R θ - a k‖) :=
    fun k hk => continuous_const.mul
      ((continuous_norm.comp ((continuous_circleMap c R).sub continuous_const)).log
        (fun θ => norm_ne_zero_iff.mpr (sub_ne_zero.mpr (circleMap_ne_mem_ball (ha k hk) θ))))
  have hcontL : Continuous (fun θ : ℝ => (L (circleMap c R θ)).re) :=
    Complex.continuous_re.comp (hLc.continuousOn.comp_continuous (continuous_circleMap c R)
      (fun θ => circleMap_mem_closedBall c hR.le θ))
  have hintk : ∀ k ∈ s,
      IntervalIntegrable (fun θ : ℝ => (m k : ℝ) * Real.log ‖circleMap c R θ - a k‖)
        MeasureTheory.volume 0 (2 * π) :=
    fun k hk => (hcontk k hk).intervalIntegrable 0 (2 * π)
  have hintsum : IntervalIntegrable
      (fun θ : ℝ => ∑ k ∈ s, (m k : ℝ) * Real.log ‖circleMap c R θ - a k‖)
      MeasureTheory.volume 0 (2 * π) :=
    (continuous_finset_sum s hcontk).intervalIntegrable 0 (2 * π)
  have hintL : IntervalIntegrable (fun θ : ℝ => (L (circleMap c R θ)).re)
      MeasureTheory.volume 0 (2 * π) := hcontL.intervalIntegrable 0 (2 * π)
  -- compute the circle integral of `log ‖f‖`
  have hint : (∫ θ in (0 : ℝ)..(2 * π), Real.log ‖f (c + R * exp (θ * I))‖)
      = 2 * π * (∑ k ∈ s, (m k : ℝ) * Real.log R) + 2 * π * (L c).re := by
    show (∫ θ in (0 : ℝ)..(2 * π), Real.log ‖f (circleMap c R θ)‖) = _
    simp only [hcirc]
    rw [intervalIntegral.integral_add hintsum hintL, hmean,
      intervalIntegral.integral_finset_sum hintk, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [intervalIntegral.integral_const_mul, integral_log_norm_circleMap_sub_of_mem_ball hR (ha k hk)]
    ring
  have hsumlog : ∑ k ∈ s, (m k : ℝ) * Real.log (R / ‖a k - c‖)
      = ∑ k ∈ s, (m k : ℝ) * Real.log R - ∑ k ∈ s, (m k : ℝ) * Real.log ‖c - a k‖ := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [Real.log_div hR.ne' (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hac k hk))), norm_sub_rev]
    ring
  rw [hint, hcenter, hsumlog]
  have hπ' : (2 * π) ≠ 0 := by positivity
  field_simp
  have hcomm : ∑ x ∈ s, Real.log R * (m x : ℝ) = ∑ x ∈ s, (m x : ℝ) * Real.log R :=
    Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [hcomm]
  ring

/-- **S4 (Jensen's formula).** Let `R > 0`, let `a : Fin n → ℂ` be points of the open disc
`ball c R` (the zeros of `f` inside the disc, listed with multiplicity), none equal to `c`, and
suppose `f z = (∏ k, (z - a k)) * g z` on `closedBall c R`, where `g` is complex differentiable and
nonvanishing on a slightly larger open disc `ball c R'` (`R < R'`). Then
`log ‖f c‖ = (1/2π) ∫ θ in 0..2π, log ‖f (c + R e^{iθ})‖ - ∑ k, log (R / ‖a k - c‖)`. -/
theorem jensen_formula {c : ℂ} {R R' : ℝ} (hR : 0 < R) (hRR' : R < R') {n : ℕ} {a : Fin n → ℂ}
    (ha : ∀ k, a k ∈ ball c R) (hac : ∀ k, a k ≠ c) {f g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball c R')) (hg0 : ∀ z ∈ ball c R', g z ≠ 0)
    (hfg : ∀ z ∈ closedBall c R, f z = (∏ k, (z - a k)) * g z) :
    Real.log ‖f c‖ = (2 * π)⁻¹ * (∫ θ in (0 : ℝ)..(2 * π), Real.log ‖f (c + R * exp (θ * I))‖)
      - ∑ k, Real.log (R / ‖a k - c‖) := by
  have := jensen_formula_multiplicity hR hRR' (s := Finset.univ) (a := a) (m := fun _ => 1)
    (fun k _ => ha k) (fun k _ => hac k) hg hg0 (by simpa only [pow_one] using hfg)
  simpa only [Nat.cast_one, one_mul] using this

/-! ## S5: counting zeros in the half disc -/

/-- **S5 (zero counting with multiplicities).** In the setting of `jensen_formula_multiplicity`,
if `‖f‖ ≤ M` on the circle `‖z - c‖ = R` and `‖f c‖ ≥ 1`, then for any `S ⊆ s` of indices `k`
with `a k` in the half disc `ball c (R/2)`, `(∑ k ∈ S, m k) · log 2 ≤ log M`. -/
theorem sum_mult_mul_log_two_le_log {ι : Type*} {c : ℂ} {R R' M : ℝ} (hR : 0 < R) (hRR' : R < R')
    {s : Finset ι} {a : ι → ℂ} {m : ι → ℕ} (ha : ∀ k ∈ s, a k ∈ ball c R)
    (hac : ∀ k ∈ s, a k ≠ c) {f g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball c R')) (hg0 : ∀ z ∈ ball c R', g z ≠ 0)
    (hfg : ∀ z ∈ closedBall c R, f z = (∏ k ∈ s, (z - a k) ^ m k) * g z)
    (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (hfc : 1 ≤ ‖f c‖)
    (S : Finset ι) (hSs : S ⊆ s) (hS : ∀ k ∈ S, a k ∈ ball c (R / 2)) :
    ((∑ k ∈ S, m k : ℕ) : ℝ) * Real.log 2 ≤ Real.log M := by
  have hJ := jensen_formula_multiplicity hR hRR' ha hac hg hg0 hfg
  have hsub : closedBall c R ⊆ ball c R' := closedBall_subset_ball hRR'
  -- `log ‖f c‖ ≥ 0`
  have h0 : 0 ≤ Real.log ‖f c‖ := Real.log_nonneg hfc
  -- the circle average is at most `log M`
  have hfpos : ∀ θ : ℝ, 0 < ‖f (circleMap c R θ)‖ := by
    intro θ
    have hmem := circleMap_mem_closedBall c hR.le θ
    rw [hfg _ hmem]
    apply norm_pos_iff.mpr
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun k hk => ?_)) (hg0 _ (hsub hmem))
    exact pow_ne_zero _ (sub_ne_zero.mpr (circleMap_ne_mem_ball (ha k hk) θ))
  have hcont : Continuous (fun θ : ℝ => Real.log ‖f (circleMap c R θ)‖) := by
    have hfc' : Continuous (fun θ : ℝ => f (circleMap c R θ)) := by
      have hfd : ContinuousOn f (closedBall c R) := by
        have : DifferentiableOn ℂ (fun z => (∏ k ∈ s, (z - a k) ^ m k) * g z) (closedBall c R) :=
          (DifferentiableOn.fun_finsetProd (fun k _ => (differentiableOn_id.sub_const _).pow _)
            |>.mul (hg.mono hsub))
        exact (this.congr hfg).continuousOn
      exact hfd.comp_continuous (continuous_circleMap c R)
        (fun θ => circleMap_mem_closedBall c hR.le θ)
    exact (continuous_norm.comp hfc').log (fun θ => (hfpos θ).ne')
  have havg : (2 * π)⁻¹ * (∫ θ in (0 : ℝ)..(2 * π), Real.log ‖f (c + R * exp (θ * I))‖)
      ≤ Real.log M := by
    have hle : (∫ θ in (0 : ℝ)..(2 * π), Real.log ‖f (circleMap c R θ)‖)
        ≤ ∫ _ in (0 : ℝ)..(2 * π), Real.log M := by
      apply intervalIntegral.integral_mono_on Real.two_pi_pos.le
        (hcont.intervalIntegrable 0 (2 * π)) intervalIntegrable_const
      intro θ _
      exact Real.log_le_log (hfpos θ) (hM _ (circleMap_mem_sphere c hR.le θ))
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hle
    have h2π : 0 < (2 * π)⁻¹ := by positivity
    calc (2 * π)⁻¹ * (∫ θ in (0 : ℝ)..(2 * π), Real.log ‖f (c + R * exp (θ * I))‖)
        ≤ (2 * π)⁻¹ * (2 * π * Real.log M) := by
          apply mul_le_mul_of_nonneg_left _ h2π.le
          exact hle
      _ = Real.log M := by field_simp
  -- each Jensen term is `≥ 0`, and `≥ log 2` on the half disc
  have hterm_nonneg : ∀ k ∈ s, 0 ≤ (m k : ℝ) * Real.log (R / ‖a k - c‖) := by
    intro k hk
    apply mul_nonneg (Nat.cast_nonneg _)
    apply Real.log_nonneg
    rw [one_le_div (norm_pos_iff.mpr (sub_ne_zero.mpr (hac k hk)))]
    exact (mem_ball_iff_norm.mp (ha k hk)).le
  have hterm_half : ∀ k ∈ S, (m k : ℝ) * Real.log 2 ≤ (m k : ℝ) * Real.log (R / ‖a k - c‖) := by
    intro k hk
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Real.log_le_log two_pos
    rw [le_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr (hac k (hSs hk))))]
    have := mem_ball_iff_norm.mp (hS k hk)
    linarith
  have hsum : ((∑ k ∈ S, m k : ℕ) : ℝ) * Real.log 2
      ≤ ∑ k ∈ s, (m k : ℝ) * Real.log (R / ‖a k - c‖) := by
    calc ((∑ k ∈ S, m k : ℕ) : ℝ) * Real.log 2 = ∑ k ∈ S, (m k : ℝ) * Real.log 2 := by
          rw [Nat.cast_sum, Finset.sum_mul]
      _ ≤ ∑ k ∈ S, (m k : ℝ) * Real.log (R / ‖a k - c‖) := Finset.sum_le_sum hterm_half
      _ ≤ ∑ k ∈ s, (m k : ℝ) * Real.log (R / ‖a k - c‖) :=
          Finset.sum_le_sum_of_subset_of_nonneg hSs (fun k hk _ => hterm_nonneg k hk)
  linarith

/-- **S5 (zero counting).** In the setting of `jensen_formula`, if `‖f‖ ≤ M` on the circle
`‖z - c‖ = R` and `‖f c‖ ≥ 1`, then for any set `S` of indices `k` with `a k` in the half disc
`ball c (R/2)`, `|S| · log 2 ≤ log M`. -/
theorem card_mul_log_two_le_log {c : ℂ} {R R' M : ℝ} (hR : 0 < R) (hRR' : R < R') {n : ℕ}
    {a : Fin n → ℂ} (ha : ∀ k, a k ∈ ball c R) (hac : ∀ k, a k ≠ c) {f g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball c R')) (hg0 : ∀ z ∈ ball c R', g z ≠ 0)
    (hfg : ∀ z ∈ closedBall c R, f z = (∏ k, (z - a k)) * g z)
    (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (hfc : 1 ≤ ‖f c‖)
    (S : Finset (Fin n)) (hS : ∀ k ∈ S, a k ∈ ball c (R / 2)) :
    (S.card : ℝ) * Real.log 2 ≤ Real.log M := by
  have := sum_mult_mul_log_two_le_log hR hRR' (s := Finset.univ) (a := a) (m := fun _ => 1)
    (fun k _ => ha k) (fun k _ => hac k) hg hg0 (by simpa only [pow_one] using hfg) hM hfc S
    (Finset.subset_univ S) hS
  simpa only [Finset.sum_const, smul_eq_mul, mul_one] using this

open scoped Classical in
/-- **S5 (zero counting, ratio form).** In the setting of `jensen_formula`, if `‖f‖ ≤ M` on the
circle `‖z - c‖ = R` and `‖f c‖ ≥ 1`, then the number of the points `a k` lying in the half disc
`ball c (R/2)` is at most `log M / log 2`. -/
theorem card_zeros_le_log_div_log_two {c : ℂ} {R R' M : ℝ} (hR : 0 < R) (hRR' : R < R') {n : ℕ}
    {a : Fin n → ℂ} (ha : ∀ k, a k ∈ ball c R) (hac : ∀ k, a k ≠ c) {f g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball c R')) (hg0 : ∀ z ∈ ball c R', g z ≠ 0)
    (hfg : ∀ z ∈ closedBall c R, f z = (∏ k, (z - a k)) * g z)
    (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (hfc : 1 ≤ ‖f c‖) :
    ((Finset.univ.filter fun k => a k ∈ ball c (R / 2)).card : ℝ) ≤ Real.log M / Real.log 2 := by
  rw [le_div_iff₀ (Real.log_pos one_lt_two)]
  exact card_mul_log_two_le_log hR hRR' ha hac hg hg0 hfg hM hfc _
    (fun k hk => (Finset.mem_filter.mp hk).2)

/-! ## Factorisation of a function with finitely many zeros -/

/-- **Factorisation at finitely many zeros.** Let `f` be complex differentiable on `ball c R'` and
let `Z` be a finite set of points of the smaller disc `ball c R` (`R < R'`) which is exactly the
zero set of `f` in `ball c R'` (so `f` has no zeros in the annulus `R ≤ ‖z - c‖ < R'`). Then
`f z = (∏ b ∈ Z, (z - b) ^ m b) * g z` on `ball c R'` for multiplicities `m b ≥ 1` and a function
`g` complex differentiable and nonvanishing on `ball c R'`. -/
theorem exists_factorization_of_finite_zeros {c : ℂ} {R R' : ℝ} (hR : 0 < R) (hRR' : R < R')
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball c R')) (Z : Finset ℂ)
    (hZR : ∀ b ∈ Z, b ∈ ball c R) (hZ : ∀ z ∈ ball c R', f z = 0 ↔ z ∈ Z) :
    ∃ (m : ℂ → ℕ) (g : ℂ → ℂ), DifferentiableOn ℂ g (ball c R') ∧ (∀ z ∈ ball c R', g z ≠ 0) ∧
      (∀ z ∈ ball c R', f z = (∏ b ∈ Z, (z - b) ^ m b) * g z) ∧ (∀ b ∈ Z, 1 ≤ m b) := by
  classical
  have hfan : AnalyticOnNhd ℂ f (ball c R') := hf.analyticOnNhd isOpen_ball
  have hZ' : ∀ b ∈ Z, b ∈ ball c R' := fun b hb => ball_subset_ball hRR'.le (hZR b hb)
  -- a point where `f ≠ 0`
  have hnorm : ‖(c + R) - c‖ = R := by
    rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hpt : c + R ∈ ball c R' := by rw [mem_ball_iff_norm, hnorm]; exact hRR'
  have hfpt : f (c + R) ≠ 0 := by
    intro h
    have := mem_ball_iff_norm.mp (hZR _ ((hZ _ hpt).mp h))
    rw [hnorm] at this
    exact lt_irrefl _ this
  -- local factorisation at each point of `Z`
  have key : ∀ b ∈ Z, ∃ (n : ℕ) (G : ℂ → ℂ), AnalyticAt ℂ G b ∧ G b ≠ 0 ∧
      ∀ᶠ z in nhds b, f z = (z - b) ^ n * G z := by
    intro b hb
    have hfb : AnalyticAt ℂ f b := hfan b (hZ' b hb)
    have hne : analyticOrderAt f b ≠ ⊤ := by
      intro htop
      rw [analyticOrderAt_eq_top] at htop
      have := hfan.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball c R').isPreconnected (hZ' b hb) htop
      exact hfpt (this hpt)
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
    obtain ⟨G, hG, hG0, hfG⟩ := hfb.analyticOrderAt_eq_natCast.mp hn.symm
    exact ⟨n, G, hG, hG0, by simpa only [smul_eq_mul] using hfG⟩
  choose! m G hG using key
  -- the polynomial part `P`, and the reduced products `Q b`
  set P : ℂ → ℂ := fun z => ∏ b ∈ Z, (z - b) ^ m b with hP
  set Q : ℂ → ℂ → ℂ := fun b z => ∏ b' ∈ Z.erase b, (z - b') ^ m b' with hQ
  set g : ℂ → ℂ := fun z => if z ∈ Z then G z z / Q z z else f z / P z with hg
  have hPQ : ∀ b ∈ Z, ∀ z, P z = (z - b) ^ m b * Q b z := by
    intro b hb z
    exact (Finset.mul_prod_erase Z (fun b' => (z - b') ^ m b') hb).symm
  have hQne : ∀ b ∈ Z, Q b b ≠ 0 := by
    intro b hb
    apply Finset.prod_ne_zero_iff.mpr
    intro b' hb'
    exact pow_ne_zero _ (sub_ne_zero.mpr (Finset.ne_of_mem_erase hb').symm)
  have hPne : ∀ z, z ∉ Z → P z ≠ 0 := by
    intro z hz
    apply Finset.prod_ne_zero_iff.mpr
    intro b hb
    apply pow_ne_zero
    apply sub_ne_zero.mpr
    intro h
    exact hz (h ▸ hb)
  -- eventually near `b ∈ Z`, `g = G b / Q b`
  have hgev : ∀ b ∈ Z, g =ᶠ[nhds b] fun z => G b z / Q b z := by
    intro b hb
    have h1 : ∀ᶠ z in nhds b, z ∉ Z.erase b := by
      have : IsOpen ((Z.erase b : Set ℂ)ᶜ) := (Z.erase b).finite_toSet.isClosed.isOpen_compl
      apply this.mem_nhds
      simp
    filter_upwards [h1, (hG b hb).2.2] with z hz hfz
    by_cases hzb : z = b
    · rw [hzb]; simp only [hg, if_pos hb]
    · have hzZ : z ∉ Z := fun h => hz (Finset.mem_erase.mpr ⟨hzb, h⟩)
      simp only [hg, if_neg hzZ]
      rw [hfz, hPQ b hb z, mul_div_mul_left _ _ (pow_ne_zero _ (sub_ne_zero.mpr hzb))]
  refine ⟨m, g, ?_, ?_, ?_, ?_⟩
  · -- `g` is differentiable
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    by_cases hzZ : z ∈ Z
    · have hQd : DifferentiableAt ℂ (Q z) z :=
        DifferentiableAt.fun_finsetProd (fun b' _ => (differentiableAt_id.sub_const _).pow _)
      have : DifferentiableAt ℂ (fun w => G z w / Q z w) z :=
        (hG z hzZ).1.differentiableAt.div hQd (hQne z hzZ)
      exact this.congr_of_eventuallyEq (hgev z hzZ)
    · have h1 : ∀ᶠ w in nhds z, w ∉ Z := by
        have : IsOpen ((Z : Set ℂ)ᶜ) := Z.finite_toSet.isClosed.isOpen_compl
        exact this.mem_nhds hzZ
      have hev : g =ᶠ[nhds z] fun w => f w / P w := by
        filter_upwards [h1] with w hw
        simp only [hg, if_neg hw]
      have hPd : DifferentiableAt ℂ P z :=
        DifferentiableAt.fun_finsetProd (fun b _ => (differentiableAt_id.sub_const _).pow _)
      have hfd : DifferentiableAt ℂ f z := hf.differentiableAt (isOpen_ball.mem_nhds hz)
      exact (hfd.div hPd (hPne z hzZ)).congr_of_eventuallyEq hev
  · -- `g` does not vanish
    intro z hz
    by_cases hzZ : z ∈ Z
    · simp only [hg, if_pos hzZ]
      exact div_ne_zero (hG z hzZ).2.1 (hQne z hzZ)
    · simp only [hg, if_neg hzZ]
      exact div_ne_zero (fun h => hzZ ((hZ z hz).mp h)) (hPne z hzZ)
  · -- the factorisation
    intro z hz
    by_cases hzZ : z ∈ Z
    · simp only [hg, if_pos hzZ]
      have hfz : f z = (z - z) ^ m z * G z z := (hG z hzZ).2.2.self_of_nhds
      show f z = P z * (G z z / Q z z)
      rw [hfz, hPQ z hzZ z, mul_assoc, mul_div_cancel₀ _ (hQne z hzZ)]
    · simp only [hg, if_neg hzZ]
      show f z = P z * (f z / P z)
      rw [mul_comm, div_mul_cancel₀ _ (hPne z hzZ)]
  · -- every point of `Z` is a genuine zero, so its multiplicity is at least one
    intro b hb
    by_contra hlt
    have hm : m b = 0 := by omega
    have hfz : f b = (b - b) ^ m b * G b b := (hG b hb).2.2.self_of_nhds
    rw [hm, pow_zero, one_mul] at hfz
    exact (hG b hb).2.1 (hfz ▸ (hZ b (hZ' b hb)).mpr hb)

/-- **Jensen's formula for a function with finitely many zeros.** Let `f` be complex
differentiable on `ball c R'` (`0 < R < R'`), let `Z ⊆ ball c R` be exactly the zero set of `f` in
`ball c R'`, and assume `f c ≠ 0`. Then there are multiplicities `m b ≥ 1` (`b ∈ Z`) with
`log ‖f c‖ = (1/2π) ∫ θ in 0..2π, log ‖f (c + R e^{iθ})‖ - ∑ b ∈ Z, m b · log (R / ‖b - c‖)`. -/
theorem jensen_formula_of_finite_zeros {c : ℂ} {R R' : ℝ} (hR : 0 < R) (hRR' : R < R')
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball c R')) (Z : Finset ℂ)
    (hZR : ∀ b ∈ Z, b ∈ ball c R) (hZ : ∀ z ∈ ball c R', f z = 0 ↔ z ∈ Z) (hfc : f c ≠ 0) :
    ∃ m : ℂ → ℕ, (∀ b ∈ Z, 1 ≤ m b) ∧
      Real.log ‖f c‖ = (2 * π)⁻¹ * (∫ θ in (0 : ℝ)..(2 * π), Real.log ‖f (c + R * exp (θ * I))‖)
        - ∑ b ∈ Z, m b * Real.log (R / ‖b - c‖) := by
  obtain ⟨m, g, hg, hg0, hfg, hm⟩ := exists_factorization_of_finite_zeros hR hRR' hf Z hZR hZ
  have hcZ : ∀ b ∈ Z, b ≠ c := by
    intro b hb h
    exact hfc ((hZ c (mem_ball_self (hR.trans hRR'))).mpr (h ▸ hb))
  refine ⟨m, hm, ?_⟩
  exact jensen_formula_multiplicity hR hRR' (s := Z) (a := id) (m := m) hZR hcZ hg hg0
    (fun z hz => hfg z (closedBall_subset_ball hRR' hz))

open scoped Classical in
/-- **Zero counting for a function with finitely many zeros.** Let `f` be complex differentiable
on `ball c R'` (`0 < R < R'`), let `Z ⊆ ball c R` be exactly the zero set of `f` in `ball c R'`,
and assume `‖f‖ ≤ M` on the circle `‖z - c‖ = R` and `‖f c‖ ≥ 1`. Then the number of zeros of `f`
in the half disc `ball c (R/2)` (even counted with multiplicity) is at most `log M / log 2`. -/
theorem card_zeros_le_log_div_log_two_of_finite_zeros {c : ℂ} {R R' M : ℝ} (hR : 0 < R)
    (hRR' : R < R') {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball c R')) (Z : Finset ℂ)
    (hZR : ∀ b ∈ Z, b ∈ ball c R) (hZ : ∀ z ∈ ball c R', f z = 0 ↔ z ∈ Z)
    (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (hfc : 1 ≤ ‖f c‖) :
    ((Z.filter fun b => b ∈ ball c (R / 2)).card : ℝ) ≤ Real.log M / Real.log 2 := by
  have hfc0 : f c ≠ 0 := by
    intro h; rw [h, norm_zero] at hfc; exact absurd hfc (by norm_num)
  obtain ⟨m, g, hg, hg0, hfg, hm⟩ := exists_factorization_of_finite_zeros hR hRR' hf Z hZR hZ
  have hcZ : ∀ b ∈ Z, b ≠ c := by
    intro b hb h
    exact hfc0 ((hZ c (mem_ball_self (hR.trans hRR'))).mpr (h ▸ hb))
  have hS := sum_mult_mul_log_two_le_log hR hRR' (s := Z) (a := id) (m := m) hZR hcZ hg hg0
    (fun z hz => hfg z (closedBall_subset_ball hRR' hz)) hM hfc
    (Z.filter fun b => b ∈ ball c (R / 2)) (Finset.filter_subset _ _)
    (fun b hb => (Finset.mem_filter.mp hb).2)
  rw [le_div_iff₀ (Real.log_pos one_lt_two)]
  refine le_trans ?_ hS
  apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg one_le_two)
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro b hb
  exact_mod_cast hm b (Finset.mem_filter.mp hb).1

end Jensen
