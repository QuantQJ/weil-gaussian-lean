import LogDerivSegmentBound
import PartialFractions
import ZeroDensityUnconditional
import ZetaGrowthEM3
import ZetaLowerBound
import ZetaStrip
import FiniteZeros
import Jensen
import Reduction
import TestFunctions
import Mathlib

/-!
# `ζ'/ζ` on the left vertical line `Re s = −1/2`: a bound at every height, and integrability

The contour of the explicit formula has the vertical edges `Re s = −1/2` and `Re s = 3/2`.
On the right edge `ζ'/ζ` is bounded by the Dirichlet series `Σ Λ(n) n^{−3/2}`; on the left edge
no zero-avoidance is needed either, because every nontrivial zero `ρ` has `Re ρ > 0`
(`ZetaStrip`), hence lies at distance `≥ 1/2` from the line.

**Proven unconditionally (no `sorry`, no custom axioms, no hypotheses):**

* `riemannZeta_ne_zero_of_re_eq_neg_half` — `ζ s ≠ 0` whenever `Re s = −1/2`.
* `norm_logDeriv_zeta_left_line_logSize` — for `|t| ≥ 6`,
  `‖ζ'/ζ(−1/2 + it)‖ ≤ (5627/9) · logSize 12 4 (11/10) (18/5) t`: the partial-fraction
  decomposition of `LogDerivSegmentBound` about the centre `11/10 + it` (disc radius `18/5`,
  reaching `Re = −5/2` where `ZetaGrowthEM3` gives `‖ζ‖ ≤ 12|Im|⁴`; `ρ = 7/4`, coverage `r = 8/5`),
  with the pole sum `Σ m_b/(z − b)` bounded by `2 Σ m_b ≤ 3 logSize` via `|z − b| ≥ Re b + 1/2`.
* `norm_logDeriv_zeta_left_line` — for `|t| ≥ 6`, `‖ζ'/ζ(−1/2 + it)‖ ≤ 8000 log |t|`.
* `norm_logDeriv_zeta_left_line_all` — `∃ B, ∀ t, ‖ζ'/ζ(−1/2 + it)‖ ≤ B log (|t| + 2)`
  (the segment `|t| ≤ 6` by compactness and continuity).
* `integrable_log_div_one_add_sq` — `t ↦ log(|t| + 2)/(1 + t²)` is integrable on `ℝ`
  (dominated by `6 (1 + |t|)^{−3/2}`).
* `integrable_logDeriv_mul_Gt_left` — `t ↦ ζ'/ζ(−1/2 + it) · Gt a g (−1/2 + it)` is integrable
  for every test function (`IsTestFn a g`).
* `integrable_logDeriv_mul_Gt_right` — the same on the line `Re s = 3/2`.

**Hypothesis-dependent:** nothing. **Not proven:** nothing that was asked; the constant `8000`
is clean rather than sharp (`626 · (log 195 + 7) < 7860` would do).
-/

set_option autoImplicit false

noncomputable section

open Complex Metric Set Filter Topology Reduction MeasureTheory

namespace LeftLineBound

/-! ## 1. `ζ` has no zeros on the line `Re s = −1/2` -/

/-- **No zeros on the left line.** If `Re s = −1/2` then `ζ s ≠ 0`: such an `s` is neither the
pole nor a trivial zero, so a zero there would be a nontrivial zero, contradicting `Re ρ > 0`
(`ZetaStrip.re_pos_of_isNontrivialZero`). -/
theorem riemannZeta_ne_zero_of_re_eq_neg_half {s : ℂ} (hs : s.re = -1/2) :
    riemannZeta s ≠ 0 := by
  intro h0
  have hnt : IsNontrivialZero s := by
    refine ⟨h0, ?_, ?_⟩
    · rintro ⟨n, hn⟩
      have h : s.re = (-2 * ((n : ℂ) + 1)).re := congrArg Complex.re hn
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [hs] at h
      simp at h
      linarith
    · intro h1
      rw [h1] at hs
      norm_num at hs
  have := ZetaStrip.re_pos_of_isNontrivialZero hnt
  linarith

/-- The points of the left line are not the pole. -/
theorem neg_half_add_mul_I_ne_one (t : ℝ) : (-1/2 + t * I : ℂ) ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  norm_num at this

/-- `ζ(−1/2 + it) ≠ 0` for every real `t`. -/
theorem riemannZeta_left_line_ne_zero (t : ℝ) : riemannZeta (-1/2 + t * I) ≠ 0 :=
  riemannZeta_ne_zero_of_re_eq_neg_half (by simp)

/-! ## 2. The partial-fraction bound at heights `|t| ≥ 6` -/

/-- **Left-line bound via partial fractions, `logSize` form.** For `|t| ≥ 6`,
`‖ζ'/ζ(−1/2 + it)‖ ≤ (5627/9) · logSize 12 4 (11/10) (18/5) t`, where `logSize` is the
logarithmic size of `ζ` on the disc `ball (11/10 + it) (18/5)` of `LogDerivSegmentBound`.
The non-polar part is `8ρ logSize/(ρ − r)² = (5600/9) logSize` (`ρ = 7/4`, `r = 8/5`); the polar
part `Σ m_b/(z − b)` is at most `2 Σ m_b ≤ 3 logSize`, since every zero `b` of the disc has
`Re b > 0`, so `|z − b| ≥ 1/2 + Re b ≥ 1/2`. -/
theorem norm_logDeriv_zeta_left_line_logSize (t : ℝ) (ht : 6 ≤ |t|) :
    ‖deriv riemannZeta (-1/2 + t * I) / riemannZeta (-1/2 + t * I)‖
      ≤ 5627 / 9 * LogDerivSegmentBound.logSize 12 4 (11/10) (18/5) t := by
  have hT : (18/5 : ℝ) + 2 ≤ |t| := by linarith
  obtain ⟨Z, m, hZρ, hZ, -, hmult, hbound⟩ :=
    LogDerivSegmentBound.exists_partialFraction_zeta_of_growth (a := -5/2) (C₃ := 12) (A := 4)
      (by norm_num) (by norm_num)
      (fun s h₁ h₂ ht => ZetaGrowthEM3.zeta_growth_left_rpow h₁ h₂ ht)
      (σ₀ := 11/10) (R' := 18/5) (ρ := 7/4) (r := 8/5) (T := t)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hT
  set z : ℂ := -1/2 + t * I with hz
  set L : ℝ := LogDerivSegmentBound.logSize 12 4 (11/10) (18/5) t with hL
  have hzre : z.re = -1/2 := by simp [hz]
  -- the point lies in the coverage disc
  have hzmem : z ∈ closedBall (((11/10 : ℝ) : ℂ) + t * I) (8/5) := by
    rw [mem_closedBall_iff_norm]
    have : z - (((11/10 : ℝ) : ℂ) + t * I) = ((-8/5 : ℝ) : ℂ) := by
      rw [hz]; push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> norm_num
  have hζz : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_re_eq_neg_half hzre
  have hpf := hbound z hzmem hζz
  -- the pole sum: every zero of the disc is at distance `≥ 1/2` from `z`
  have hlog2 : (2/3 : ℝ) ≤ Real.log 2 := LogDerivSegmentBound.two_thirds_le_log_two
  have hsum : ‖∑ b ∈ Z, (m b : ℂ) / (z - b)‖ ≤ 3 * L := by
    have hterm : ∀ b ∈ Z, ‖(m b : ℂ) / (z - b)‖ ≤ 2 * (m b : ℝ) := by
      intro b hb
      have hbρ := hZρ b hb
      have hbR' : b ∈ ball (((11/10 : ℝ) : ℂ) + t * I) (18/5) :=
        ball_subset_ball (by norm_num) hbρ
      have hb2 := (LogDerivSegmentBound.two_le_abs_im_of_mem_ball hT hbR').1
      have hb0 : riemannZeta b = 0 := (hZ b hbρ).mpr hb
      have hbnt : IsNontrivialZero b :=
        LogDerivSegmentBound.isNontrivialZero_of_im_ne_zero hb0
          (fun h => by rw [h, abs_zero] at hb2; linarith)
      have hbre : 0 < b.re := ZetaStrip.re_pos_of_isNontrivialZero hbnt
      have hdist : (1/2 : ℝ) ≤ ‖z - b‖ := by
        have hre : (z - b).re = -1/2 - b.re := by rw [Complex.sub_re, hzre]
        calc (1/2 : ℝ) ≤ |(z - b).re| := by
              rw [hre, abs_of_neg (by linarith)]; linarith
          _ ≤ ‖z - b‖ := by skip; exact Complex.abs_re_le_norm _
      rw [norm_div, Complex.norm_natCast, div_le_iff₀ (by linarith)]
      have := mul_le_mul_of_nonneg_left hdist (by positivity : (0 : ℝ) ≤ 2 * (m b : ℝ))
      linarith
    calc ‖∑ b ∈ Z, (m b : ℂ) / (z - b)‖
        ≤ ∑ b ∈ Z, ‖(m b : ℂ) / (z - b)‖ := norm_sum_le _ _
      _ ≤ ∑ b ∈ Z, 2 * (m b : ℝ) := Finset.sum_le_sum hterm
      _ = 2 * ((∑ b ∈ Z, m b : ℕ) : ℝ) := by rw [Nat.cast_sum, Finset.mul_sum]
      _ ≤ 3 * L := by
          have hS0 : (0 : ℝ) ≤ ((∑ b ∈ Z, m b : ℕ) : ℝ) := Nat.cast_nonneg _
          nlinarith [mul_le_mul_of_nonneg_left hlog2 hS0]
  calc ‖deriv riemannZeta z / riemannZeta z‖
      = ‖(deriv riemannZeta z / riemannZeta z - ∑ b ∈ Z, (m b : ℂ) / (z - b))
          + ∑ b ∈ Z, (m b : ℂ) / (z - b)‖ := by rw [sub_add_cancel]
    _ ≤ ‖deriv riemannZeta z / riemannZeta z - ∑ b ∈ Z, (m b : ℂ) / (z - b)‖
          + ‖∑ b ∈ Z, (m b : ℂ) / (z - b)‖ := norm_add_le _ _
    _ ≤ 8 * (7/4) * L / (7/4 - 8/5) ^ 2 + 3 * L := add_le_add hpf hsum
    _ = 5627 / 9 * L := by ring

/-- `2^4 = 16` with a real exponent. -/
theorem two_rpow_four : (2 : ℝ) ^ (4 : ℝ) = 16 := by
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

/-- The constant `log (3 + 12·2⁴) + 4 + 3 = log 195 + 7` of `logSize_general_le` is at most
`251/20 = 12.55` (`log 195 ≤ 8 log 2 < 5.546`). -/
theorem log_const_le : Real.log (3 + 12 * (2 : ℝ) ^ (4 : ℝ)) + 4 + 3 ≤ 251 / 20 := by
  have h195 : Real.log (3 + 12 * (2 : ℝ) ^ (4 : ℝ)) ≤ 8 * Real.log 2 := by
    rw [two_rpow_four, show (3 + 12 * 16 : ℝ) = 195 by norm_num]
    calc Real.log 195 ≤ Real.log (2 ^ 8) := Real.log_le_log (by norm_num) (by norm_num)
      _ = 8 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have := Real.log_two_lt_d9
  generalize Real.log (3 + 12 * (2 : ℝ) ^ (4 : ℝ)) = x at h195 ⊢
  linarith

/-- **(1) Left-line bound, explicit constant.** For `|t| ≥ 6`,
`‖ζ'/ζ(−1/2 + it)‖ ≤ 8000 log |t|`. -/
theorem norm_logDeriv_zeta_left_line (t : ℝ) (ht : 6 ≤ |t|) :
    ‖deriv riemannZeta (-1/2 + t * I) / riemannZeta (-1/2 + t * I)‖ ≤ 8000 * Real.log |t| := by
  have h := norm_logDeriv_zeta_left_line_logSize t ht
  have hL : LogDerivSegmentBound.logSize 12 4 (11/10) (18/5) t
      ≤ (Real.log (3 + 12 * (2 : ℝ) ^ (4 : ℝ)) + 4 + 3) * Real.log |t| :=
    LogDerivSegmentBound.logSize_general_le (by norm_num) (by norm_num) ht
  have hlogt : 0 ≤ Real.log |t| := Real.log_nonneg (by linarith)
  have hΛ := log_const_le
  calc ‖deriv riemannZeta (-1/2 + t * I) / riemannZeta (-1/2 + t * I)‖
      ≤ 5627 / 9 * LogDerivSegmentBound.logSize 12 4 (11/10) (18/5) t := h
    _ ≤ 5627 / 9 * ((Real.log (3 + 12 * (2 : ℝ) ^ (4 : ℝ)) + 4 + 3) * Real.log |t|) :=
        mul_le_mul_of_nonneg_left hL (by norm_num)
    _ ≤ 5627 / 9 * (251 / 20 * Real.log |t|) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hΛ hlogt) (by norm_num)
    _ ≤ 8000 * Real.log |t| := by nlinarith

/-! ## 3. Continuity along vertical lines, and the bound at every height -/

/-- `t ↦ ζ'/ζ(c + it)` is continuous on `ℝ` whenever the line avoids the pole and the zeros. -/
theorem continuous_logDeriv_line (c : ℂ) (h1 : ∀ t : ℝ, c + t * I ≠ 1)
    (hnz : ∀ t : ℝ, riemannZeta (c + t * I) ≠ 0) :
    Continuous (fun t : ℝ => deriv riemannZeta (c + t * I) / riemannZeta (c + t * I)) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hc : ContinuousAt (fun s : ℂ => deriv riemannZeta s / riemannZeta s) (c + t * I) :=
    ((ZerosCountable.analyticOnNhd_riemannZeta.deriv _
      (Set.mem_compl_singleton_iff.mpr (h1 t))).continuousAt).div
      (differentiableAt_riemannZeta (h1 t)).continuousAt (hnz t)
  have hφ : Continuous fun t : ℝ => c + t * I := by fun_prop
  exact ContinuousAt.comp (g := fun s : ℂ => deriv riemannZeta s / riemannZeta s)
    (f := fun t : ℝ => c + t * I) hc hφ.continuousAt

/-- `t ↦ ζ'/ζ(−1/2 + it)` is continuous on `ℝ`. -/
theorem continuous_logDeriv_left_line :
    Continuous (fun t : ℝ => deriv riemannZeta (-1/2 + t * I) / riemannZeta (-1/2 + t * I)) :=
  continuous_logDeriv_line (-1/2) neg_half_add_mul_I_ne_one riemannZeta_left_line_ne_zero

/-- **(1′) Left-line bound at every height.** There is `B` with
`‖ζ'/ζ(−1/2 + it)‖ ≤ B log (|t| + 2)` for every real `t`: the bound `8000 log |t|` for
`|t| ≥ 6`, and a compactness bound on the segment `|t| ≤ 6`. -/
theorem norm_logDeriv_zeta_left_line_all :
    ∃ B : ℝ, ∀ t : ℝ,
      ‖deriv riemannZeta (-1/2 + t * I) / riemannZeta (-1/2 + t * I)‖
        ≤ B * Real.log (|t| + 2) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-6 : ℝ)) (b := 6)).exists_bound_of_continuousOn
    continuous_logDeriv_left_line.continuousOn
  refine ⟨3/2 * (|C| + 8000), fun t => ?_⟩
  have hlog2 : (2/3 : ℝ) ≤ Real.log 2 := LogDerivSegmentBound.two_thirds_le_log_two
  have hlogt2 : Real.log 2 ≤ Real.log (|t| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hB0 : (0 : ℝ) ≤ 3/2 * (|C| + 8000) := by positivity
  have hprod : 3/2 * (|C| + 8000) * (2/3) ≤ 3/2 * (|C| + 8000) * Real.log (|t| + 2) :=
    mul_le_mul_of_nonneg_left (hlog2.trans hlogt2) hB0
  by_cases ht : 6 ≤ |t|
  · have h := norm_logDeriv_zeta_left_line t ht
    have h2 : Real.log |t| ≤ Real.log (|t| + 2) := Real.log_le_log (by linarith) (by linarith)
    have hl0 : 0 ≤ Real.log |t| := Real.log_nonneg (by linarith)
    calc ‖deriv riemannZeta (-1/2 + t * I) / riemannZeta (-1/2 + t * I)‖
        ≤ 8000 * Real.log |t| := h
      _ ≤ 8000 * Real.log (|t| + 2) := by gcongr
      _ ≤ 3/2 * (|C| + 8000) * Real.log (|t| + 2) := by
          apply mul_le_mul_of_nonneg_right _ (hl0.trans h2)
          linarith [abs_nonneg C]
  · push_neg at ht
    have hmem : t ∈ Icc (-6 : ℝ) 6 := Set.mem_Icc.mpr (abs_le.mp ht.le)
    calc ‖deriv riemannZeta (-1/2 + t * I) / riemannZeta (-1/2 + t * I)‖
        ≤ C := hC t hmem
      _ ≤ |C| := le_abs_self C
      _ ≤ 3/2 * (|C| + 8000) * Real.log (|t| + 2) := by linarith

/-! ## 4. The integrable majorant `log(|t| + 2)/(1 + t²)` -/

/-- `t ↦ log(|t| + 2)/(1 + t²)` is integrable on `ℝ`: with `u = 1 + |t|`,
`log(|t| + 2) ≤ 2 (|t| + 2)^{1/2} ≤ 3 u^{1/2}` and `1 + t² ≥ u²/2`, so the function is at most
`6 u^{−3/2}`, and `(1 + |t|)^{−3/2}` is integrable (`integrable_one_add_norm`). -/
theorem integrable_log_div_one_add_sq :
    Integrable (fun t : ℝ => Real.log (|t| + 2) / (1 + t ^ 2)) := by
  have hint : Integrable (fun t : ℝ => (1 + ‖t‖) ^ (-(3/2 : ℝ))) :=
    integrable_one_add_norm (by simp; norm_num)
  have hmeas : Measurable (fun t : ℝ => Real.log (|t| + 2) / (1 + t ^ 2)) := by fun_prop
  refine (hint.const_mul 6).mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  show ‖Real.log (|t| + 2) / (1 + t ^ 2)‖ ≤ 6 * (1 + ‖t‖) ^ (-(3/2 : ℝ))
  have ht0 : 0 ≤ |t| := abs_nonneg t
  have hlog0 : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith)
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 1 + |t| := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; linarith
  have hu2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu0.ne'
  have hu12 : 0 ≤ u ^ (1/2 : ℝ) := Real.rpow_nonneg hu0.le _
  -- `log (|t| + 2) ≤ 3 u^{1/2}`
  have h1 : Real.log (|t| + 2) ≤ 3 * u ^ (1/2 : ℝ) := by
    have hA := Real.log_le_rpow_div (x := |t| + 2) (ε := 1/2) (by linarith) (by norm_num)
    have h2 : (|t| + 2) ^ (1/2 : ℝ) ≤ (2 * u) ^ (1/2 : ℝ) :=
      Real.rpow_le_rpow (by linarith) (by rw [hu]; linarith) (by norm_num)
    have h3 : (2 * u) ^ (1/2 : ℝ) = 2 ^ (1/2 : ℝ) * u ^ (1/2 : ℝ) :=
      Real.mul_rpow (by norm_num) hu0.le
    have h4 : (2 : ℝ) ^ (1/2 : ℝ) ≤ 3/2 := by
      rw [← Real.sqrt_eq_rpow]
      calc Real.sqrt 2 ≤ Real.sqrt ((3/2) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
        _ = 3/2 := Real.sqrt_sq (by norm_num)
    calc Real.log (|t| + 2) ≤ (|t| + 2) ^ (1/2 : ℝ) / (1/2) := hA
      _ = 2 * (|t| + 2) ^ (1/2 : ℝ) := by ring
      _ ≤ 2 * (2 ^ (1/2 : ℝ) * u ^ (1/2 : ℝ)) := by rw [← h3]; linarith
      _ ≤ 2 * (3/2 * u ^ (1/2 : ℝ)) := by nlinarith
      _ = 3 * u ^ (1/2 : ℝ) := by ring
  -- `u² ≤ 2 (1 + t²)`
  have h5 : u ^ 2 ≤ 2 * (1 + t ^ 2) := by
    rw [hu]; nlinarith [_root_.sq_abs t, sq_nonneg (|t| - 1)]
  -- `u^{−3/2} = u^{1/2} / u²`
  have h6 : u ^ (-(3/2 : ℝ)) = u ^ (1/2 : ℝ) / u ^ 2 := by
    rw [← Real.rpow_two, ← Real.rpow_sub hu0]
    congr 1
    norm_num
  have hnorm : (1 : ℝ) + ‖t‖ = u := by rw [hu, Real.norm_eq_abs]
  rw [Real.norm_eq_abs, _root_.abs_of_nonneg (div_nonneg hlog0 (by positivity)), hnorm, h6,
    div_le_iff₀ (by positivity)]
  calc Real.log (|t| + 2) ≤ 3 * u ^ (1/2 : ℝ) := h1
    _ = 6 * (u ^ (1/2 : ℝ) / u ^ 2) * (u ^ 2 / 2) := by field_simp; ring
    _ ≤ 6 * (u ^ (1/2 : ℝ) / u ^ 2) * (1 + t ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith

/-! ## 5. Integrability of `ζ'/ζ · Gt` on the vertical lines -/

/-- **Generic integrability.** If `f` is continuous with `‖f t‖ ≤ B log(|t| + 2)` and `G` is
continuous with `‖G t‖ ≤ M/(1 + t²)`, then `f · G` is integrable on `ℝ`. -/
theorem integrable_mul_of_log_bound {f G : ℝ → ℂ} (hf : Continuous f) (hG : Continuous G)
    {B M : ℝ} (hB : ∀ t, ‖f t‖ ≤ B * Real.log (|t| + 2))
    (hM : ∀ t, ‖G t‖ ≤ M / (1 + t ^ 2)) :
    Integrable (fun t : ℝ => f t * G t) := by
  refine (integrable_log_div_one_add_sq.const_mul (B * M)).mono' (hf.mul hG).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  show ‖f t * G t‖ ≤ B * M * (Real.log (|t| + 2) / (1 + t ^ 2))
  rw [norm_mul]
  calc ‖f t‖ * ‖G t‖ ≤ (B * Real.log (|t| + 2)) * (M / (1 + t ^ 2)) :=
        mul_le_mul (hB t) (hM t) (norm_nonneg _) ((norm_nonneg _).trans (hB t))
    _ = B * M * (Real.log (|t| + 2) / (1 + t ^ 2)) := by ring

/-- **(2) Integrability on the left line.** For every test function `g` on `[−a, a]`,
`t ↦ ζ'/ζ(−1/2 + it) · Gt a g (−1/2 + it)` is integrable on `ℝ`
(`‖ζ'/ζ‖ ≤ B log(|t| + 2)` and `‖Gt‖ ≤ M/(1 + t²)`). -/
theorem integrable_logDeriv_mul_Gt_left {a : ℝ} {g : ℝ → ℂ} (h : TestFunctions.IsTestFn a g) :
    Integrable (fun t : ℝ =>
      deriv riemannZeta (-1/2 + t * I) / riemannZeta (-1/2 + t * I)
        * TestFunctions.Gt a g (-1/2 + t * I)) := by
  obtain ⟨B, hB⟩ := norm_logDeriv_zeta_left_line_all
  obtain ⟨M, -, hM⟩ := TestFunctions.Gt_norm_le_div_one_add_sq h (-1/2)
  have hM' : ∀ t : ℝ, ‖TestFunctions.Gt a g (-1/2 + t * I)‖ ≤ M / (1 + t ^ 2) := fun t => by
    have := hM t
    rwa [show ((-1/2 : ℝ) : ℂ) + t * I = -1/2 + t * I by push_cast; ring] at this
  have hG : Continuous (fun t : ℝ => TestFunctions.Gt a g (-1/2 + t * I)) :=
    (TestFunctions.Gt_continuous h.continuous).comp (by fun_prop)
  exact integrable_mul_of_log_bound continuous_logDeriv_left_line hG hB hM'

/-- The same, with the logarithmic derivative written as the function `deriv ζ / ζ`. -/
theorem integrable_logDeriv_mul_Gt_left' {a : ℝ} {g : ℝ → ℂ} (h : TestFunctions.IsTestFn a g) :
    Integrable (fun t : ℝ =>
      (deriv riemannZeta / riemannZeta) (-1/2 + t * I) * TestFunctions.Gt a g (-1/2 + t * I)) :=
  integrable_logDeriv_mul_Gt_left h

/-- The points of the right line `Re s = 3/2` are not the pole. -/
theorem three_halves_add_mul_I_ne_one (t : ℝ) : (3/2 + t * I : ℂ) ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  norm_num at this

/-- `ζ(3/2 + it) ≠ 0` (nonvanishing on `Re s ≥ 1`). -/
theorem riemannZeta_right_line_ne_zero (t : ℝ) : riemannZeta (3/2 + t * I) ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re (by simp; norm_num)

/-- `t ↦ ζ'/ζ(3/2 + it)` is continuous on `ℝ`. -/
theorem continuous_logDeriv_right_line :
    Continuous (fun t : ℝ => deriv riemannZeta (3/2 + t * I) / riemannZeta (3/2 + t * I)) :=
  continuous_logDeriv_line (3/2) three_halves_add_mul_I_ne_one riemannZeta_right_line_ne_zero

/-- **(3) Integrability on the right line.** For every test function `g` on `[−a, a]`,
`t ↦ ζ'/ζ(3/2 + it) · Gt a g (3/2 + it)` is integrable on `ℝ`: `ζ'/ζ` is bounded by
`Σ Λ(n) n^{−3/2}` there and `Gt` is integrable on every vertical line. -/
theorem integrable_logDeriv_mul_Gt_right {a : ℝ} {g : ℝ → ℂ} (h : TestFunctions.IsTestFn a g) :
    Integrable (fun t : ℝ =>
      deriv riemannZeta (3/2 + t * I) / riemannZeta (3/2 + t * I)
        * TestFunctions.Gt a g (3/2 + t * I)) := by
  have hG : Integrable (fun t : ℝ => TestFunctions.Gt a g (3/2 + t * I)) := by
    have := TestFunctions.integrable_on_vertical_line h (3/2)
    have e : ∀ t : ℝ, ((3/2 : ℝ) : ℂ) + t * I = 3/2 + t * I := fun t => by push_cast; ring
    simpa only [e] using this
  refine hG.bdd_mul (c := ∑' n : ℕ, ExplicitFormula.coeff (3/2) n)
    continuous_logDeriv_right_line.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  exact LogDerivSegmentBound.norm_logDeriv_zeta_le_on_line_three_halves t

/-- The same, with the logarithmic derivative written as the function `deriv ζ / ζ`. -/
theorem integrable_logDeriv_mul_Gt_right' {a : ℝ} {g : ℝ → ℂ} (h : TestFunctions.IsTestFn a g) :
    Integrable (fun t : ℝ =>
      (deriv riemannZeta / riemannZeta) (3/2 + t * I) * TestFunctions.Gt a g (3/2 + t * I)) :=
  integrable_logDeriv_mul_Gt_right h

end LeftLineBound

end
