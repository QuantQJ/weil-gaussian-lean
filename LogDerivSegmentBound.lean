import PartialFractions
import ZeroDensityUnconditional
import ZeroDensity
import ZetaGrowth
import ZetaGrowthNeg
import ZetaLowerBound
import FiniteZeros
import ZetaStrip
import Reduction
import Mathlib

/-!
# Bounds for `ζ'/ζ` on horizontal segments `σ + iT` (the contour-closing input)

Everything below is proven with Lean's standard axioms only, except where a hypothesis is
named explicitly in the theorem statement.

**Mechanism (general holomorphic `f`, unconditional).**
* `norm_logDeriv_le_of_norm_le_general` — Borel–Carathéodory + Cauchy with an *arbitrary*
  coverage radius `r < R`: `‖h'/h‖ ≤ 8 R log M / (R − r)²` on `closedBall c r` (the version in
  `PartialFractions` only covers `closedBall c (R/4)`; that loss is what made the target
  unreachable, see the task discussion).
* `norm_logDeriv_sub_sum_le_of_factorization_general` — the partial-fraction bound
  `‖f'/f − Σ m_k/(z − a_k)‖ ≤ 8 ρ log M / (ρ − r)²` on `closedBall c r`, any `r < ρ`.
* `exists_partialFraction_bound_of_finite_zeros` — the zero-set form **together with the
  multiplicity bound** `(Σ_{b∈Z} m b) log 2 ≤ log M₀ − log ‖f c‖` (Jensen), for the *same*
  multiplicities `m` (one factorisation over the whole disc, split at radius `ρ`).

**`ζ` (growth region as a parameter; unconditional once a growth bound is supplied).**
* `exists_partialFraction_zeta_of_growth`, `norm_logDeriv_zeta_le_of_growth` — for a centre
  `σ₀ + iT` (`σ₀ > 1`, where the Euler product gives `‖ζ‖ ≥ (σ₀−1)/σ₀`) and a disc of radius
  `R'` inside the growth region `Re s ≥ a`, with `|T| ≥ R' + 2` and zero-avoidance
  `δ ≤ |Im ρ − T|`: on `σ ∈ [σ₀ − r, σ₀ + r]` (any `r < ρ < R'/2`)
  `‖ζ'/ζ(σ + iT)‖ ≤ 8ρ·logSize/(ρ − r)² + logSize/(δ log 2)`.
* **(b) Unconditional, `σ ∈ [1/2, 3/2]`** (`norm_logDeriv_zeta_le_on_segment`): with the
  available growth `‖ζ s‖ ≤ 7|Im s|^{3/2}` on `Re s ≥ −1/2` (`ZetaGrowthNeg`), centre
  `11/10 + iT`, `R' = 8/5`, `ρ = 3/4`, `r = 3/5`: for `|T| ≥ 4`,
  `‖ζ'/ζ(σ + iT)‖ ≤ 1600 log|T| + 9 log|T|/δ`.
* **(c) Hypothesis-dependent, `σ ∈ [−1/2, 3/2]`**
  (`norm_logDeriv_zeta_le_on_full_segment_of_growth`): the same with a growth bound on
  `Re s ≥ −5/2` taken as the explicit hypothesis `hgrowth3` (the statement of the not-yet-existing
  `ZetaGrowthEM3`; a third Euler–Maclaurin step, mechanical), centre `11/10 + iT`, `R' = 18/5`,
  `ρ = 7/4`, `r = 8/5`, `|T| ≥ 6`. Reaching `σ = −1/2` from a centre with `Re > 1` needs the disc
  to reach `Re ≈ −5/2`; no lower bound for `|ζ|` at a centre with `Re ≤ 1` is available
  (Davenport bootstraps one from this very partial-fraction bound — not done here).
* **(2) The prime side** (`norm_logDeriv_zeta_le_on_line_three_halves`):
  `‖ζ'/ζ(3/2 + it)‖ ≤ Σ Λ(n) n^{−3/2}` (reusing `ZetaGrowth.norm_logDeriv_zeta_le_of_re_ge`).

**Not proven:** the segment bound down to `σ = −1/2` without a hypothesis (needs the
`Re s ≥ −5/2` growth bound), and the existence of zero-avoiding heights (taken as `hδ`).
-/

noncomputable section

open Complex Metric Set Filter Topology Reduction

namespace LogDerivSegmentBound

/-! ## 1. Borel–Carathéodory with a general coverage radius -/

/-- **Log-derivative bound, general coverage radius.** `h` holomorphic and nonvanishing on
`ball c R` with `‖h z‖ ≤ M ‖h c‖` there; then for `0 ≤ r < R` and `z ∈ closedBall c r`,
`‖h' z / h z‖ ≤ 8 R log M / (R − r)²`. (Borel–Carathéodory on the disc of radius `(R + r)/2`,
Cauchy's estimate with radius `(R − r)/2`.) -/
theorem norm_logDeriv_le_of_norm_le_general {c : ℂ} {R r M : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (ball c R)) (hh0 : ∀ z ∈ ball c R, h z ≠ 0)
    (hbd : ∀ z ∈ ball c R, ‖h z‖ ≤ M * ‖h c‖) {z : ℂ} (hz : z ∈ closedBall c r) :
    ‖deriv h z / h z‖ ≤ 8 * R * Real.log M / (R - r) ^ 2 := by
  have hR : 0 < R := hr.trans_lt hrR
  have hc0 : h c ≠ 0 := hh0 c (mem_ball_self hR)
  have hcpos : 0 < ‖h c‖ := norm_pos_iff.mpr hc0
  have hM : 1 ≤ M := by
    have h1 : 1 * ‖h c‖ ≤ M * ‖h c‖ := by rw [one_mul]; exact hbd c (mem_ball_self hR)
    exact le_of_mul_le_mul_right h1 hcpos
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  obtain ⟨L, hL, hLc, hexp⟩ := PartialFractions.exists_log_normalized hR hh hh0
  -- `Re L = log (‖h‖ / ‖h c‖) ≤ log M`
  have hre : ∀ w ∈ ball c R, (L w).re ≤ Real.log M := by
    intro w hw
    have h1 : Real.exp (L w).re = ‖h w‖ / ‖h c‖ := by
      rw [← Complex.norm_exp, hexp w hw, norm_div]
    have hpos : 0 < ‖h w‖ / ‖h c‖ := div_pos (norm_pos_iff.mpr (hh0 w hw)) hcpos
    have h2 : ‖h w‖ / ‖h c‖ ≤ M := by
      rw [div_le_iff₀ hcpos]; exact hbd w hw
    calc (L w).re = Real.log (Real.exp (L w).re) := (Real.log_exp _).symm
      _ = Real.log (‖h w‖ / ‖h c‖) := by rw [h1]
      _ ≤ Real.log M := Real.log_le_log hpos h2
  -- Borel–Carathéodory on the disc of radius `r₁ = (R + r)/2`
  have hr₁pos : 0 < (R + r) / 2 := by linarith
  have hr₁R : (R + r) / 2 < R := by linarith
  have hdpos : 0 < (R - r) / 2 := by linarith
  have hRr0 : R - r ≠ 0 := by linarith
  have hBC : ∀ w ∈ closedBall c ((R + r) / 2), ‖L w‖ ≤ 4 * ((R + r) / 2) * Real.log M / (R - r) := by
    intro w hw
    have := PartialFractions.borel_caratheodory hr₁pos hr₁R hlogM hL hLc hre hw
    have hRr : R - (R + r) / 2 = (R - r) / 2 := by ring
    calc ‖L w‖ ≤ 2 * ((R + r) / 2) * Real.log M / (R - (R + r) / 2) := this
      _ = 4 * ((R + r) / 2) * Real.log M / (R - r) := by rw [hRr]; field_simp; ring
  -- Cauchy's estimate on `closedBall z ((R - r)/2) ⊆ closedBall c ((R + r)/2)`
  have hsub : closedBall z ((R - r) / 2) ⊆ closedBall c ((R + r) / 2) := by
    apply closedBall_subset_closedBall'
    have := mem_closedBall.mp hz
    linarith
  have hsub' : closedBall c ((R + r) / 2) ⊆ ball c R := closedBall_subset_ball hr₁R
  have hderiv : ‖deriv L z‖ ≤ 4 * ((R + r) / 2) * Real.log M / (R - r) / ((R - r) / 2) :=
    PartialFractions.norm_deriv_le_of_forall_mem_closedBall_norm_le hdpos
      (hL.mono (hsub.trans hsub')) (fun w hw => hBC w (hsub hw))
  -- `L' = h'/h`
  have hzR : z ∈ ball c R := hsub' (hsub (mem_closedBall_self hdpos.le))
  have hhz : h z ≠ 0 := hh0 z hzR
  have hLderiv : deriv L z = deriv h z / h z := by
    have hLd : HasDerivAt L (deriv L z) z :=
      (hL.differentiableAt (isOpen_ball.mem_nhds hzR)).hasDerivAt
    have hhd : HasDerivAt h (deriv h z) z :=
      (hh.differentiableAt (isOpen_ball.mem_nhds hzR)).hasDerivAt
    have h1 : HasDerivAt (fun w => exp (L w)) (exp (L z) * deriv L z) z := hLd.cexp
    have h2 : HasDerivAt (fun w => h w / h c) (deriv h z / h c) z := hhd.div_const (h c)
    have h3 : HasDerivAt (fun w => exp (L w)) (deriv h z / h c) z := by
      refine h2.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ball.mem_nhds hzR] with w hw
      exact hexp w hw
    have h4 : exp (L z) * deriv L z = deriv h z / h c := h1.unique h3
    rw [hexp z hzR] at h4
    have h5 : h z * deriv L z = deriv h z := by
      have h6 : h z / h c * deriv L z * h c = deriv h z / h c * h c := by rw [h4]
      rwa [div_mul_eq_mul_div, div_mul_cancel₀ _ hc0, div_mul_cancel₀ _ hc0] at h6
    rw [eq_div_iff hhz]
    linear_combination h5
  rw [← hLderiv]
  have hRr : 0 < R - r := by linarith
  calc ‖deriv L z‖ ≤ 4 * ((R + r) / 2) * Real.log M / (R - r) / ((R - r) / 2) := hderiv
    _ = 8 * ((R + r) / 2) * Real.log M / (R - r) ^ 2 := by field_simp; ring
    _ ≤ 8 * R * Real.log M / (R - r) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have : (R + r) / 2 ≤ R := hr₁R.le
        nlinarith [hlogM]

/-! ## 2. Partial fractions with a general coverage radius -/

/-- **Partial-fraction bound, factorised form, general coverage radius.** With
`0 ≤ r < ρ ≤ R < R'`, `f = (∏ (z − a_k)^{m_k}) · g` on `ball c R'`, all `a_k ∈ closedBall c (R/2)`,
`g` holomorphic on `ball c R'` and nonvanishing on `ball c ρ`, `f c ≠ 0`, `‖f‖ ≤ M ‖f c‖` on
the circle `‖z − c‖ = R`: for `z ∈ closedBall c r` with `f z ≠ 0`,
`‖f' z / f z − Σ_k m_k/(z − a_k)‖ ≤ 8 ρ log M / (ρ − r)²`.
Same proof as `PartialFractions.norm_logDeriv_sub_sum_le_of_factorization`, with the inner
Borel–Carathéodory step replaced by `norm_logDeriv_le_of_norm_le_general`. -/
theorem norm_logDeriv_sub_sum_le_of_factorization_general {c : ℂ} {R R' ρ r M : ℝ}
    (hr : 0 ≤ r) (hrρ : r < ρ) (hρR : ρ ≤ R) (hRR' : R < R') {ι : Type*} {s : Finset ι}
    {a : ι → ℂ} {m : ι → ℕ} (ha : ∀ k ∈ s, a k ∈ closedBall c (R / 2)) {f g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball c R')) (hg0 : ∀ z ∈ ball c ρ, g z ≠ 0)
    (hfg : ∀ z ∈ ball c R', f z = (∏ k ∈ s, (z - a k) ^ m k) * g z) (hfc : f c ≠ 0)
    (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M * ‖f c‖) {z : ℂ} (hz : z ∈ closedBall c r)
    (hfz : f z ≠ 0) :
    ‖deriv f z / f z - ∑ k ∈ s, (m k : ℂ) / (z - a k)‖ ≤ 8 * ρ * Real.log M / (ρ - r) ^ 2 := by
  have hρ : 0 < ρ := hr.trans_lt hrρ
  have hR : 0 < R := hρ.trans_le hρR
  have hR' : 0 < R' := hR.trans hRR'
  set P : ℂ → ℂ := fun w => ∏ k ∈ s, (w - a k) ^ m k with hP
  have hfg' : ∀ w ∈ ball c R', f w = P w * g w := fun w hw => hfg w hw
  have hcR' : c ∈ ball c R' := mem_ball_self hR'
  have hPc : P c ≠ 0 := by
    have h := hfc; rw [hfg' c hcR'] at h; exact left_ne_zero_of_mul h
  have hgc : g c ≠ 0 := by
    have h := hfc; rw [hfg' c hcR'] at h; exact right_ne_zero_of_mul h
  -- `M ≥ 0` (the circle is nonempty)
  have hM0 : 0 ≤ M := by
    have hpt : c + R ∈ sphere c R := by
      rw [mem_sphere_iff_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hR]
    have h1 := hM _ hpt
    have h2 := norm_nonneg (f (c + R))
    have h3 := norm_pos_iff.mpr hfc
    by_contra hneg
    push_neg at hneg
    nlinarith
  -- on the circle, `‖P c‖ ≤ ‖P z‖`
  have hPle : ∀ w ∈ sphere c R, ‖P c‖ ≤ ‖P w‖ := by
    intro w hw
    have hwc : ‖w - c‖ = R := mem_sphere_iff_norm.mp hw
    simp only [hP, norm_prod, norm_pow]
    apply Finset.prod_le_prod₀ (fun k _ => by positivity)
    intro k hk
    apply pow_le_pow_left₀ (norm_nonneg _)
    have h1 : ‖a k - c‖ ≤ R / 2 := mem_closedBall_iff_norm.mp (ha k hk)
    have h2 := norm_sub_norm_le (w - c) (a k - c)
    rw [sub_sub_sub_cancel_right] at h2
    rw [norm_sub_rev c (a k)]
    linarith
  -- `‖g‖ ≤ M ‖g c‖` on the circle ...
  have hsphere : ∀ w ∈ sphere c R, ‖g w‖ ≤ M * ‖g c‖ := by
    intro w hw
    have hwR' : w ∈ ball c R' := closedBall_subset_ball hRR' (sphere_subset_closedBall hw)
    have hPw : 0 < ‖P w‖ := lt_of_lt_of_le (norm_pos_iff.mpr hPc) (hPle w hw)
    have h1 : ‖g w‖ * ‖P w‖ = ‖f w‖ := by rw [hfg' w hwR', norm_mul, mul_comm]
    have h2 : ‖f c‖ = ‖P c‖ * ‖g c‖ := by rw [hfg' c hcR', norm_mul]
    have h3 : ‖g w‖ * ‖P w‖ ≤ M * ‖g c‖ * ‖P w‖ := by
      calc ‖g w‖ * ‖P w‖ = ‖f w‖ := h1
        _ ≤ M * ‖f c‖ := hM w hw
        _ = M * ‖g c‖ * ‖P c‖ := by rw [h2]; ring
        _ ≤ M * ‖g c‖ * ‖P w‖ :=
          mul_le_mul_of_nonneg_left (hPle w hw) (mul_nonneg hM0 (norm_nonneg _))
    exact le_of_mul_le_mul_right h3 hPw
  -- ... hence on the closed disc (maximum modulus principle)
  have hdisc : ∀ w ∈ closedBall c R, ‖g w‖ ≤ M * ‖g c‖ := by
    intro w hw
    have hd : DiffContOnCl ℂ g (ball c R) := hg.diffContOnCl_ball (closedBall_subset_ball hRR')
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd ?_ ?_
    · rw [frontier_ball c hR.ne']; exact hsphere
    · rw [closure_ball c hR.ne']; exact hw
  have hbdρ : ∀ w ∈ ball c ρ, ‖g w‖ ≤ M * ‖g c‖ :=
    fun w hw => hdisc w (ball_subset_closedBall (ball_subset_ball hρR hw))
  -- the log-derivative bound for `g`, general coverage radius
  have hgbound : ‖deriv g z / g z‖ ≤ 8 * ρ * Real.log M / (ρ - r) ^ 2 :=
    norm_logDeriv_le_of_norm_le_general hr hrρ (hg.mono (ball_subset_ball (by linarith))) hg0
      hbdρ hz
  -- the identity `f'/f = ∑ m k / (z - a k) + g'/g` at `z`
  have hzR' : z ∈ ball c R' := closedBall_subset_ball (by linarith) hz
  have hPz : P z ≠ 0 := by
    have h := hfz; rw [hfg' z hzR'] at h; exact left_ne_zero_of_mul h
  have hgz : g z ≠ 0 := by
    have h := hfz; rw [hfg' z hzR'] at h; exact right_ne_zero_of_mul h
  have hPz' : (∏ k ∈ s, (z - a k) ^ m k) ≠ 0 := hPz
  have hPd : DifferentiableAt ℂ P z := by
    show DifferentiableAt ℂ (fun w => ∏ k ∈ s, (w - a k) ^ m k) z
    exact DifferentiableAt.fun_finsetProd (fun k _ => (differentiableAt_id.sub_const _).pow _)
  have hgd : DifferentiableAt ℂ g z := hg.differentiableAt (isOpen_ball.mem_nhds hzR')
  have hfP : f =ᶠ[𝓝 z] fun w => P w * g w := by
    filter_upwards [isOpen_ball.mem_nhds hzR'] with w hw
    exact hfg' w hw
  have hlogf : logDeriv f z = logDeriv (fun w => P w * g w) z := by
    simp only [logDeriv_apply]
    rw [hfP.deriv_eq, hfg' z hzR']
  have hlogP : logDeriv P z = ∑ k ∈ s, (m k : ℂ) / (z - a k) := by
    have hne : ∀ k ∈ s, (fun k w => (w - a k) ^ m k) k z ≠ 0 :=
      fun k hk => Finset.prod_ne_zero_iff.mp hPz' k hk
    have hd : ∀ k ∈ s, DifferentiableAt ℂ ((fun k w => (w - a k) ^ m k) k) z :=
      fun k _ => (differentiableAt_id.sub_const _).pow _
    have hprod := logDeriv_fun_prod (s := s) (f := fun k w => (w - a k) ^ m k) (x := z) hne hd
    rw [hP, hprod]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hdk : DifferentiableAt ℂ (fun w => w - a k) z := differentiableAt_id.sub_const _
    rw [logDeriv_fun_pow hdk (m k)]
    have h1 : logDeriv (fun w => w - a k) z = 1 / (z - a k) := by
      rw [logDeriv_apply, deriv_sub_const, deriv_id'']
    rw [h1]; ring
  have hid : deriv f z / f z - ∑ k ∈ s, (m k : ℂ) / (z - a k) = deriv g z / g z := by
    rw [← logDeriv_apply, hlogf, logDeriv_fun_mul z hPz hgz hPd hgd, hlogP, logDeriv_apply]; ring
  rw [hid]
  exact hgbound

/-- **Partial fractions + multiplicity count from one factorisation (zero-set form).**
Let `0 ≤ r < ρ`, `2ρ < R'`, `f` holomorphic on `ball c R'` with finitely many zeros there,
`‖f‖ ≤ M₀` on `ball c R'`, `f c ≠ 0`. Then there are a finite set `Z` — exactly the zeros of `f`
in `ball c ρ` — and multiplicities `m b ≥ 1` on `Z` with
* `(Σ_{b∈Z} m b) · log 2 ≤ log M₀ − log ‖f c‖` (Jensen's formula on a circle of radius
  `R ∈ [2ρ, R')` chosen free of zeros), and
* `‖f' z / f z − Σ_{b∈Z} m b/(z − b)‖ ≤ 8 ρ (log M₀ − log ‖f c‖)/(ρ − r)²` for every
  `z ∈ closedBall c r` with `f z ≠ 0`.
Both statements use the *same* `m`: `f` is factorised once over all its zeros in `ball c R'`
(`Jensen.exists_factorization_of_finite_zeros`) and the product is split at radius `ρ`. -/
theorem exists_partialFraction_bound_of_finite_zeros {c : ℂ} {R' ρ r M₀ : ℝ}
    (hr : 0 ≤ r) (hrρ : r < ρ) (hρR' : 2 * ρ < R')
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball c R'))
    (hfin : {z ∈ ball c R' | f z = 0}.Finite)
    (hM : ∀ z ∈ ball c R', ‖f z‖ ≤ M₀) (hfc : f c ≠ 0) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ b ∈ Z, b ∈ ball c ρ) ∧ (∀ z ∈ ball c ρ, f z = 0 ↔ z ∈ Z) ∧ (∀ b ∈ Z, 1 ≤ m b) ∧
      ((∑ b ∈ Z, m b : ℕ) : ℝ) * Real.log 2 ≤ Real.log M₀ - Real.log ‖f c‖ ∧
      ∀ z ∈ closedBall c r, f z ≠ 0 →
        ‖deriv f z / f z - ∑ b ∈ Z, (m b : ℂ) / (z - b)‖
          ≤ 8 * ρ * (Real.log M₀ - Real.log ‖f c‖) / (ρ - r) ^ 2 := by
  classical
  have hρ : 0 < ρ := hr.trans_lt hrρ
  have hR' : 0 < R' := by linarith
  have hcR' : c ∈ ball c R' := mem_ball_self hR'
  have hfcpos : 0 < ‖f c‖ := norm_pos_iff.mpr hfc
  have hM₀ : 0 < M₀ := hfcpos.trans_le (hM c hcR')
  -- all zeros of `f` in the big disc
  set Z' : Finset ℂ := hfin.toFinset with hZ'def
  have hZ'mem : ∀ b, b ∈ Z' ↔ b ∈ ball c R' ∧ f b = 0 := fun b => hfin.mem_toFinset
  have hZ' : ∀ z ∈ ball c R', f z = 0 ↔ z ∈ Z' := fun z hz =>
    ⟨fun h => (hZ'mem z).mpr ⟨hz, h⟩, fun h => ((hZ'mem z).mp h).2⟩
  -- a Jensen radius `R ∈ [2ρ, R')` with `Z' ⊆ ball c R`
  obtain ⟨R, hρR, hRR', hZ'R⟩ : ∃ R : ℝ, 2 * ρ ≤ R ∧ R < R' ∧ ∀ b ∈ Z', b ∈ ball c R := by
    rcases Z'.eq_empty_or_nonempty with hZe | hZne
    · exact ⟨2 * ρ, le_rfl, hρR', fun b hb => by simp [hZe] at hb⟩
    · obtain ⟨b₀, hb₀, hmax⟩ := Finset.exists_max_image Z' (fun b => dist b c) hZne
      have hd : dist b₀ c < R' := mem_ball.mp ((hZ'mem b₀).mp hb₀).1
      refine ⟨max (2 * ρ) ((dist b₀ c + R') / 2), le_max_left _ _,
        max_lt hρR' (by linarith), fun b hb => ?_⟩
      rw [mem_ball]
      calc dist b c ≤ dist b₀ c := hmax b hb
        _ < (dist b₀ c + R') / 2 := by linarith
        _ ≤ max (2 * ρ) ((dist b₀ c + R') / 2) := le_max_right _ _
  have hR : 0 < R := by linarith
  -- one factorisation over all zeros of the big disc
  obtain ⟨m, g', hg', hg'0, hfg', hm⟩ :=
    Jensen.exists_factorization_of_finite_zeros hR hRR' hf Z' hZ'R hZ'
  have hcZ' : ∀ b ∈ Z', b ≠ c := fun b hb h => hfc ((hZ' c hcR').mpr (h ▸ hb))
  -- the zeros of the small disc
  obtain ⟨Z, hZdef⟩ : ∃ Z : Finset ℂ, Z = Z'.filter (fun b => b ∈ ball c ρ) := ⟨_, rfl⟩
  have hZsub : Z ⊆ Z' := by rw [hZdef]; exact Finset.filter_subset _ _
  have hZmem : ∀ b, b ∈ Z ↔ b ∈ Z' ∧ b ∈ ball c ρ := fun b => by
    rw [hZdef]; exact Finset.mem_filter
  have hρR'' : ball c ρ ⊆ ball c R' := ball_subset_ball (by linarith)
  have hZρ : ∀ b ∈ Z, b ∈ ball c ρ := fun b hb => ((hZmem b).mp hb).2
  have hZ : ∀ z ∈ ball c ρ, f z = 0 ↔ z ∈ Z := by
    intro z hz
    rw [hZmem, ← hZ' z (hρR'' hz)]
    exact ⟨fun h => ⟨h, hz⟩, fun h => h.1⟩
  -- Jensen's multiplicity bound, applied to the normalised function `f / f c`
  have hmult : ((∑ b ∈ Z, m b : ℕ) : ℝ) * Real.log 2 ≤ Real.log M₀ - Real.log ‖f c‖ := by
    have hg'' : DifferentiableOn ℂ (fun z => g' z / f c) (ball c R') := hg'.div_const _
    have hg0'' : ∀ z ∈ ball c R', g' z / f c ≠ 0 := fun z hz => div_ne_zero (hg'0 z hz) hfc
    have hfg'' : ∀ z ∈ closedBall c R, f z / f c = (∏ b ∈ Z', (z - b) ^ m b) * (g' z / f c) := by
      intro z hz
      rw [hfg' z (closedBall_subset_ball hRR' hz)]; ring
    have hM'' : ∀ z ∈ sphere c R, ‖f z / f c‖ ≤ M₀ / ‖f c‖ := by
      intro z hz
      rw [norm_div]
      exact div_le_div_of_nonneg_right
        (hM z (closedBall_subset_ball hRR' (sphere_subset_closedBall hz))) hfcpos.le
    have hfc'' : 1 ≤ ‖f c / f c‖ := by rw [div_self hfc, norm_one]
    have hS := Jensen.sum_mult_mul_log_two_le_log hR hRR' (s := Z') (a := id) (m := m) hZ'R hcZ'
      (f := fun z => f z / f c) (g := fun z => g' z / f c) hg'' hg0'' hfg'' hM'' hfc''
      Z hZsub (fun b hb => ball_subset_ball (by linarith) (hZρ b hb))
    rwa [Real.log_div hM₀.ne' hfcpos.ne'] at hS
  -- split the product at radius `ρ`: `f = (∏_{b ∈ Z}) · g` with `g ≠ 0` on `ball c ρ`
  obtain ⟨g, hgdef⟩ : ∃ g : ℂ → ℂ,
      g = fun z => (∏ b ∈ Z'.filter (fun b => b ∉ ball c ρ), (z - b) ^ m b) * g' z := ⟨_, rfl⟩
  have hg : DifferentiableOn ℂ g (ball c R') := by
    rw [hgdef]
    exact (DifferentiableOn.fun_finsetProd
      (fun b _ => (differentiableOn_id.sub_const _).pow _)).mul hg'
  have hg0 : ∀ z ∈ ball c ρ, g z ≠ 0 := by
    intro z hz
    rw [hgdef]
    apply mul_ne_zero
    · apply Finset.prod_ne_zero_iff.mpr
      intro b hb
      have hbρ : b ∉ ball c ρ := (Finset.mem_filter.mp hb).2
      exact pow_ne_zero _ (sub_ne_zero.mpr (fun h => hbρ (h ▸ hz)))
    · exact hg'0 z (hρR'' hz)
  have hfg : ∀ z ∈ ball c R', f z = (∏ b ∈ Z, (z - b) ^ m b) * g z := by
    intro z hz
    have hsplit := Finset.prod_filter_mul_prod_filter_not Z' (fun b => b ∈ ball c ρ)
      (fun b => (z - b) ^ m b)
    rw [hfg' z hz, ← hsplit, hgdef, hZdef]
    ring
  refine ⟨Z, m, hZρ, hZ, fun b hb => hm b (hZsub hb), hmult, fun z hz hfz => ?_⟩
  have hMs : ∀ w ∈ sphere c R, ‖f w‖ ≤ (M₀ / ‖f c‖) * ‖f c‖ := by
    intro w hw
    rw [div_mul_cancel₀ _ hfcpos.ne']
    exact hM w (closedBall_subset_ball hRR' (sphere_subset_closedBall hw))
  have hb := norm_logDeriv_sub_sum_le_of_factorization_general hr hrρ (by linarith : ρ ≤ R) hRR'
    (s := Z) (a := fun b => b) (m := m)
    (fun b hb => ball_subset_closedBall (ball_subset_ball (by linarith) (hZρ b hb)))
    hg hg0 hfg hfc hMs hz hfz
  rwa [Real.log_div hM₀.ne' hfcpos.ne'] at hb

/-! ## 3. The geometry of the disc `ball (σ₀ + iT) R'` -/

/-- Points of `ball (σ₀ + iT) R'` satisfy `|Re z − σ₀| < R'` and `|Im z − T| < R'`. -/
theorem abs_re_sub_lt_and_abs_im_sub_lt_of_mem_ball {σ₀ T R' : ℝ} {z : ℂ}
    (hz : z ∈ ball (σ₀ + T * I) R') : |z.re - σ₀| < R' ∧ |z.im - T| < R' := by
  have hz' : ‖z - (σ₀ + T * I)‖ < R' := mem_ball_iff_norm.mp hz
  have hre : (z - (σ₀ + T * I)).re = z.re - σ₀ := by simp
  have him : (z - (σ₀ + T * I)).im = z.im - T := by simp
  constructor
  · calc |z.re - σ₀| = |(z - (σ₀ + T * I)).re| := by rw [hre]
      _ ≤ ‖z - (σ₀ + T * I)‖ := by skip; exact Complex.abs_re_le_norm _
      _ < R' := hz'
  · calc |z.im - T| = |(z - (σ₀ + T * I)).im| := by rw [him]
      _ ≤ ‖z - (σ₀ + T * I)‖ := by skip; exact Complex.abs_im_le_norm _
      _ < R' := hz'

/-- On `ball (σ₀ + iT) R'` with `|T| ≥ R' + 2`: `2 ≤ |Im z| ≤ |T| + R'`. -/
theorem two_le_abs_im_of_mem_ball {σ₀ T R' : ℝ} (hT : R' + 2 ≤ |T|) {z : ℂ}
    (hz : z ∈ ball (σ₀ + T * I) R') : 2 ≤ |z.im| ∧ |z.im| ≤ |T| + R' := by
  have him := (abs_re_sub_lt_and_abs_im_sub_lt_of_mem_ball hz).2
  constructor
  · have h1 := abs_sub_abs_le_abs_sub T z.im
    rw [abs_sub_comm] at h1
    linarith
  · have h1 := abs_sub_abs_le_abs_sub z.im T
    linarith

/-- The pole `1` lies outside `closedBall (σ₀ + iT) R'` when `|T| ≥ R' + 2`. -/
theorem one_not_mem_closedBall {σ₀ T R' : ℝ} (hT : R' + 2 ≤ |T|) :
    (1 : ℂ) ∉ closedBall (σ₀ + T * I) R' := by
  intro h
  have h' : ‖(1 : ℂ) - (σ₀ + T * I)‖ ≤ R' := mem_closedBall_iff_norm.mp h
  have him : ((1 : ℂ) - (σ₀ + T * I)).im = -T := by simp
  have : |T| ≤ R' := by
    calc |T| = |((1 : ℂ) - (σ₀ + T * I)).im| := by rw [him, abs_neg]
      _ ≤ ‖(1 : ℂ) - (σ₀ + T * I)‖ := by skip; exact Complex.abs_im_le_norm _
      _ ≤ R' := h'
  linarith

/-- A zero of `ζ` with nonzero imaginary part is a nontrivial zero (the trivial zeros and the
pole are real). -/
theorem isNontrivialZero_of_im_ne_zero {z : ℂ} (h0 : riemannZeta z = 0) (hz : z.im ≠ 0) :
    IsNontrivialZero z := by
  refine ⟨h0, ?_, ?_⟩
  · rintro ⟨n, rfl⟩
    apply hz
    simp
  · rintro rfl
    apply hz
    simp

/-! ## 4. `ζ` on the disc: upper bound from growth, lower bound at the centre -/

/-- `ζ(x) ≤ x/(x − 1)` for real `x > 1` (`Σ_{n≥1} n^{−x} ≤ 1 + 1/(x−1)`, telescoping bound
`ZetaGrowth.tsum_add_one_rpow_le`). -/
theorem norm_zeta_real_le {x : ℝ} (hx : 1 < x) : ‖riemannZeta (x : ℂ)‖ ≤ x / (x - 1) := by
  rw [ZetaGrowth.norm_zeta_real_eq hx]
  have hs : Summable fun n : ℕ => 1 / (n : ℝ) ^ x := Real.summable_one_div_nat_rpow.mpr hx
  rw [hs.tsum_eq_zero_add]
  have h0 : (1 : ℝ) / ((0 : ℕ) : ℝ) ^ x = 0 := by
    rw [Nat.cast_zero, Real.zero_rpow (by linarith), div_zero]
  have hshift : ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ)) ^ x
      = ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + (x - 1))) := by
    refine tsum_congr fun n => ?_
    rw [show -(1 + (x - 1)) = -x by ring, Real.rpow_neg (by positivity), one_div]
    push_cast
    rfl
  have hK := ZetaGrowth.tsum_add_one_rpow_le (p := x - 1) (by linarith)
  rw [h0, zero_add, hshift]
  have hx1 : x - 1 ≠ 0 := (by linarith : (0 : ℝ) < x - 1).ne'
  have : 1 + 1 / (x - 1) = x / (x - 1) := by field_simp; ring
  linarith

/-- **Lower bound at the centre:** `(σ₀ − 1)/σ₀ ≤ ‖ζ(σ₀ + iT)‖` for `σ₀ > 1`
(from `ZetaLowerBound.inv_norm_zeta_re_le_norm_zeta` and `norm_zeta_real_le`). -/
theorem norm_zeta_centre_ge {σ₀ : ℝ} (hσ₀ : 1 < σ₀) (T : ℝ) :
    (σ₀ - 1) / σ₀ ≤ ‖riemannZeta (σ₀ + T * I)‖ := by
  have hre : (σ₀ + T * I : ℂ).re = σ₀ := by simp
  have hs : 1 < (σ₀ + T * I : ℂ).re := by rw [hre]; exact hσ₀
  have h := ZetaLowerBound.inv_norm_zeta_re_le_norm_zeta hs
  rw [hre] at h
  refine le_trans ?_ h
  have hpos := ZetaLowerBound.norm_zeta_real_pos hσ₀
  rw [div_le_div_iff₀ (by linarith) hpos]
  have := norm_zeta_real_le hσ₀
  rw [le_div_iff₀ (by linarith)] at this
  linarith

/-- **Upper bound on the disc from a growth hypothesis.** If `‖ζ s‖ ≤ C₃ |Im s|^A` on
`a ≤ Re s ≤ 2`, `|Im s| ≥ 2`, then on `ball (σ₀ + iT) R'` with `σ₀ − R' ≥ a` and `|T| ≥ R' + 2`,
`‖ζ z‖ ≤ 3 + C₃ (|T| + R')^A` (for `Re z > 2` the trivial bound `‖ζ z‖ ≤ ζ(2) ≤ 3`). -/
theorem norm_zeta_le_on_disc_of_growth {a C₃ A : ℝ} (hC₃ : 0 ≤ C₃) (hA : 0 ≤ A)
    (hgrowth : ∀ s : ℂ, a ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| → ‖riemannZeta s‖ ≤ C₃ * |s.im| ^ A)
    {σ₀ R' T : ℝ} (haR' : a ≤ σ₀ - R') (hT : R' + 2 ≤ |T|) :
    ∀ z ∈ ball (σ₀ + T * I) R', ‖riemannZeta z‖ ≤ 3 + C₃ * (|T| + R') ^ A := by
  intro z hz
  have hre := abs_lt.mp (abs_re_sub_lt_and_abs_im_sub_lt_of_mem_ball hz).1
  obtain ⟨hzim2, hzimT⟩ := two_le_abs_im_of_mem_ball hT hz
  have hpow0 : 0 ≤ C₃ * (|T| + R') ^ A := mul_nonneg hC₃ (Real.rpow_nonneg (by linarith) _)
  by_cases hre2 : z.re ≤ 2
  · calc ‖riemannZeta z‖ ≤ C₃ * |z.im| ^ A := hgrowth z (by linarith) hre2 hzim2
      _ ≤ C₃ * (|T| + R') ^ A := by
          apply mul_le_mul_of_nonneg_left _ hC₃
          exact Real.rpow_le_rpow (abs_nonneg _) hzimT hA
      _ ≤ 3 + C₃ * (|T| + R') ^ A := by linarith
  · push_neg at hre2
    calc ‖riemannZeta z‖ ≤ ‖riemannZeta ((1 + 1 : ℝ) : ℂ)‖ :=
          ZetaGrowth.norm_zeta_le_of_re_ge one_pos (by linarith)
      _ = ‖riemannZeta 2‖ := by norm_num
      _ ≤ 3 := ZeroDensity.norm_riemannZeta_two_le
      _ ≤ 3 + C₃ * (|T| + R') ^ A := by linarith

/-! ## 5. The partial-fraction decomposition of `ζ'/ζ` near height `T` -/

/-- The logarithmic size of `ζ` on `ball (σ₀ + iT) R'` relative to its value at the centre:
`log (3 + C₃ (|T| + R')^A) + log (σ₀/(σ₀ − 1))`, an upper bound for `log M₀ − log ‖ζ(σ₀ + iT)‖`. -/
def logSize (C₃ A σ₀ R' T : ℝ) : ℝ :=
  Real.log (3 + C₃ * (|T| + R') ^ A) + Real.log (σ₀ / (σ₀ - 1))

/-- **Partial fractions for `ζ'/ζ` on a disc about `σ₀ + iT` (growth region as a parameter).**
Under `hgrowth` (`‖ζ s‖ ≤ C₃ |Im s|^A` on `a ≤ Re s ≤ 2`, `|Im s| ≥ 2`), for a centre
`c = σ₀ + iT` with `σ₀ > 1`, a disc radius `R'` with `σ₀ − R' ≥ a`, radii `0 ≤ r < ρ`, `2ρ < R'`,
and `|T| ≥ R' + 2`: there are `Z` = the zeros of `ζ` in `ball c ρ` and multiplicities
`m b ≥ 1` with `(Σ m b) log 2 ≤ logSize` and, for `z ∈ closedBall c r` with `ζ z ≠ 0`,
`‖ζ'/ζ(z) − Σ_{b∈Z} m b/(z − b)‖ ≤ 8 ρ logSize/(ρ − r)²`. -/
theorem exists_partialFraction_zeta_of_growth {a C₃ A : ℝ} (hC₃ : 0 ≤ C₃) (hA : 0 ≤ A)
    (hgrowth : ∀ s : ℂ, a ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| → ‖riemannZeta s‖ ≤ C₃ * |s.im| ^ A)
    {σ₀ R' ρ r T : ℝ} (hσ₀ : 1 < σ₀) (haR' : a ≤ σ₀ - R') (hr : 0 ≤ r) (hrρ : r < ρ)
    (hρR' : 2 * ρ < R') (hT : R' + 2 ≤ |T|) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ b ∈ Z, b ∈ ball (σ₀ + T * I) ρ) ∧
      (∀ z ∈ ball (σ₀ + T * I) ρ, riemannZeta z = 0 ↔ z ∈ Z) ∧
      (∀ b ∈ Z, 1 ≤ m b) ∧
      ((∑ b ∈ Z, m b : ℕ) : ℝ) * Real.log 2 ≤ logSize C₃ A σ₀ R' T ∧
      ∀ z ∈ closedBall (σ₀ + T * I) r, riemannZeta z ≠ 0 →
        ‖deriv riemannZeta z / riemannZeta z - ∑ b ∈ Z, (m b : ℂ) / (z - b)‖
          ≤ 8 * ρ * logSize C₃ A σ₀ R' T / (ρ - r) ^ 2 := by
  have hρ : 0 < ρ := hr.trans_lt hrρ
  have hR' : 0 < R' := by linarith
  -- `ζ` is holomorphic on the disc (the pole is outside)
  have hne1 : ∀ z ∈ ball (σ₀ + T * I) R', z ≠ 1 := by
    intro z hz h1
    have := (two_le_abs_im_of_mem_ball hT hz).1
    rw [h1, Complex.one_im, abs_zero] at this
    linarith
  have hf : DifferentiableOn ℂ riemannZeta (ball (σ₀ + T * I) R') := fun z hz =>
    (differentiableAt_riemannZeta (hne1 z hz)).differentiableWithinAt
  have hfin : {z ∈ ball (σ₀ + T * I) R' | riemannZeta z = 0}.Finite :=
    (FiniteZeros.finite_zeros_of_isCompact (isCompact_closedBall _ R')
      (one_not_mem_closedBall hT)).subset (fun z hz => ⟨ball_subset_closedBall hz.1, hz.2⟩)
  have hM := norm_zeta_le_on_disc_of_growth hC₃ hA hgrowth haR' hT
  -- the centre
  have hlow := norm_zeta_centre_ge hσ₀ T
  have hlowpos : 0 < (σ₀ - 1) / σ₀ := div_pos (by linarith) (by linarith)
  have hfc : riemannZeta (σ₀ + T * I) ≠ 0 := by
    intro h; rw [h, norm_zero] at hlow; linarith
  obtain ⟨Z, m, hZρ, hZ, hm, hmult, hbound⟩ :=
    exists_partialFraction_bound_of_finite_zeros hr hrρ hρR' hf hfin hM hfc
  -- `log M₀ − log ‖ζ c‖ ≤ logSize`
  have hL : Real.log (3 + C₃ * (|T| + R') ^ A) - Real.log ‖riemannZeta (σ₀ + T * I)‖
      ≤ logSize C₃ A σ₀ R' T := by
    unfold logSize
    have h1 : Real.log ((σ₀ - 1) / σ₀) ≤ Real.log ‖riemannZeta (σ₀ + T * I)‖ :=
      Real.log_le_log hlowpos hlow
    have h2 : Real.log ((σ₀ - 1) / σ₀) = -Real.log (σ₀ / (σ₀ - 1)) := by
      rw [← Real.log_inv, inv_div]
    linarith
  refine ⟨Z, m, hZρ, hZ, hm, hmult.trans hL, fun z hz hfz => ?_⟩
  calc ‖deriv riemannZeta z / riemannZeta z - ∑ b ∈ Z, (m b : ℂ) / (z - b)‖
      ≤ 8 * ρ * (Real.log (3 + C₃ * (|T| + R') ^ A)
          - Real.log ‖riemannZeta (σ₀ + T * I)‖) / (ρ - r) ^ 2 := hbound z hz hfz
    _ ≤ 8 * ρ * logSize C₃ A σ₀ R' T / (ρ - r) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hL (by positivity)

/-- **(a) The mechanism: `ζ'/ζ` on the segment `σ + iT`, growth region as a parameter.**
Under `hgrowth` on `Re s ≥ a`, a centre `σ₀ > 1`, a disc `R'` with `σ₀ − R' ≥ a`, radii
`0 ≤ r < ρ`, `2ρ < R'`, height `|T| ≥ R' + 2`, and zero-avoidance `δ ≤ |Im ρ − T|` for every
nontrivial zero `ρ` (`δ > 0`): for every `σ ∈ [σ₀ − r, σ₀ + r]`,
`‖ζ'/ζ(σ + iT)‖ ≤ 8 ρ logSize/(ρ − r)² + logSize/(δ log 2)`.
The pole term `Σ m b/(z − b)` is bounded by `(Σ m b)/δ` since `|z − b| ≥ |Im b − T| ≥ δ`,
and `Σ m b ≤ logSize / log 2` by Jensen. -/
theorem norm_logDeriv_zeta_le_of_growth {a C₃ A : ℝ} (hC₃ : 0 ≤ C₃) (hA : 0 ≤ A)
    (hgrowth : ∀ s : ℂ, a ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| → ‖riemannZeta s‖ ≤ C₃ * |s.im| ^ A)
    {σ₀ R' ρ r T δ : ℝ} (hσ₀ : 1 < σ₀) (haR' : a ≤ σ₀ - R') (hr : 0 ≤ r) (hrρ : r < ρ)
    (hρR' : 2 * ρ < R') (hT : R' + 2 ≤ |T|) (hδpos : 0 < δ)
    (hδ : ∀ ρ', IsNontrivialZero ρ' → δ ≤ |ρ'.im - T|) :
    ∀ σ ∈ Set.Icc (σ₀ - r) (σ₀ + r),
      ‖deriv riemannZeta (σ + T * I) / riemannZeta (σ + T * I)‖
        ≤ 8 * ρ * logSize C₃ A σ₀ R' T / (ρ - r) ^ 2
          + logSize C₃ A σ₀ R' T / (δ * Real.log 2) := by
  obtain ⟨Z, m, hZρ, hZ, hm, hmult, hbound⟩ :=
    exists_partialFraction_zeta_of_growth hC₃ hA hgrowth hσ₀ haR' hr hrρ hρR' hT
  have hρ : 0 < ρ := hr.trans_lt hrρ
  have hR' : 0 < R' := by linarith
  have hT2 : 2 ≤ |T| := by linarith
  intro σ hσ
  have hzim : (σ + T * I : ℂ).im = T := by simp
  -- the point lies in the coverage disc
  have hz : (σ + T * I : ℂ) ∈ closedBall (σ₀ + T * I) r := by
    rw [mem_closedBall_iff_norm]
    have : (σ : ℂ) + T * I - (σ₀ + T * I) = ((σ - σ₀ : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  -- `ζ(σ + iT) ≠ 0` by the avoidance hypothesis
  have hζz : riemannZeta (σ + T * I) ≠ 0 := by
    intro h0
    have hnt : IsNontrivialZero (σ + T * I) :=
      isNontrivialZero_of_im_ne_zero h0 (by rw [hzim]; intro h; rw [h, abs_zero] at hT2; linarith)
    have := hδ _ hnt
    rw [hzim, sub_self, abs_zero] at this
    linarith
  -- the pole sum
  have hsum : ‖∑ b ∈ Z, (m b : ℂ) / (σ + T * I - b)‖
      ≤ logSize C₃ A σ₀ R' T / (δ * Real.log 2) := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    calc ‖∑ b ∈ Z, (m b : ℂ) / (σ + T * I - b)‖
        ≤ ∑ b ∈ Z, ‖(m b : ℂ) / (σ + T * I - b)‖ := norm_sum_le _ _
      _ ≤ ∑ b ∈ Z, (m b : ℝ) / δ := by
          apply Finset.sum_le_sum
          intro b hb
          rw [norm_div, Complex.norm_natCast]
          apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδpos
          have hbρ := hZρ b hb
          have hbR' : b ∈ ball (σ₀ + T * I) R' := ball_subset_ball (by linarith) hbρ
          have hb2 := (two_le_abs_im_of_mem_ball hT hbR').1
          have hb0 : riemannZeta b = 0 := (hZ b hbρ).mpr hb
          have hbnt : IsNontrivialZero b :=
            isNontrivialZero_of_im_ne_zero hb0 (fun h => by rw [h, abs_zero] at hb2; linarith)
          calc δ ≤ |b.im - T| := hδ b hbnt
            _ = |(σ + T * I - b : ℂ).im| := by rw [Complex.sub_im, hzim, abs_sub_comm]
            _ ≤ ‖(σ + T * I - b : ℂ)‖ := by
                skip; exact Complex.abs_im_le_norm _
      _ = ((∑ b ∈ Z, m b : ℕ) : ℝ) / δ := by rw [Nat.cast_sum, Finset.sum_div]
      _ ≤ logSize C₃ A σ₀ R' T / (δ * Real.log 2) := by
          rw [div_le_div_iff₀ hδpos (by positivity)]
          have := mul_le_mul_of_nonneg_right hmult hδpos.le
          linarith
  have hb := hbound _ hz hζz
  calc ‖deriv riemannZeta (σ + T * I) / riemannZeta (σ + T * I)‖
      = ‖(deriv riemannZeta (σ + T * I) / riemannZeta (σ + T * I)
            - ∑ b ∈ Z, (m b : ℂ) / (σ + T * I - b))
          + ∑ b ∈ Z, (m b : ℂ) / (σ + T * I - b)‖ := by rw [sub_add_cancel]
    _ ≤ ‖deriv riemannZeta (σ + T * I) / riemannZeta (σ + T * I)
            - ∑ b ∈ Z, (m b : ℂ) / (σ + T * I - b)‖
          + ‖∑ b ∈ Z, (m b : ℂ) / (σ + T * I - b)‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hb hsum

/-! ## 6. Numerics -/

/-- `2/3 ≤ log 2`. -/
theorem two_thirds_le_log_two : (2 / 3 : ℝ) ≤ Real.log 2 := by
  linarith [Real.log_two_gt_d9]

/-- `log 11 ≤ 3` (via `11 ≤ 16 = 2⁴` and `log 2 < 0.7`). -/
theorem log_eleven_le_three : Real.log 11 ≤ 3 := by
  have h1 : Real.log 11 ≤ Real.log 16 := Real.log_le_log (by norm_num) (by norm_num)
  have h2 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  linarith [Real.log_two_lt_d9]

/-- The concrete `logSize` with `C₃ = 7`, `A = 3/2`, `σ₀ = 11/10`, `R' = 8/5` is at most
`6 log |T|` for `|T| ≥ 4`. -/
theorem logSize_concrete_le {T : ℝ} (hT : 4 ≤ |T|) :
    logSize 7 (3/2) (11/10) (8/5) T ≤ 6 * Real.log |T| := by
  unfold logSize
  have hT0 : 0 < |T| := by linarith
  have hx0 : 0 < |T| + 8/5 := by linarith
  have hx1 : 1 ≤ (|T| + 8/5) ^ (3/2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hlogx : Real.log ((|T| + 8/5) ^ (3/2 : ℝ)) = 3/2 * Real.log (|T| + 8/5) :=
    Real.log_rpow hx0 _
  have h1 : Real.log (3 + 7 * (|T| + 8/5) ^ (3/2 : ℝ))
      ≤ Real.log 10 + Real.log ((|T| + 8/5) ^ (3/2 : ℝ)) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) (by linarith)
  have h2 : Real.log (|T| + 8/5) ≤ Real.log 2 + Real.log |T| := by
    rw [← Real.log_mul (by norm_num) hT0.ne']
    exact Real.log_le_log hx0 (by linarith)
  have h3 : (11/10 : ℝ) / (11/10 - 1) = 11 := by norm_num
  have h4 : Real.log 10 + Real.log 11 ≤ 7 * Real.log 2 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    have : Real.log (10 * 11) ≤ Real.log (2 ^ 7) := Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at this
    norm_num at this ⊢
    linarith
  have h5 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h6 : Real.log 4 ≤ Real.log |T| := Real.log_le_log (by norm_num) hT
  have h7 : 0 ≤ Real.log |T| := Real.log_nonneg (by linarith)
  rw [h3]
  linarith

/-- The `logSize` with general `C₃`, `A` and `σ₀ = 11/10`, `R' = 18/5` is at most
`(log (3 + C₃ 2^A) + A + 3) log |T|` for `|T| ≥ 6`. -/
theorem logSize_general_le {C₃ A T : ℝ} (hC₃ : 0 ≤ C₃) (hA : 0 ≤ A) (hT : 6 ≤ |T|) :
    logSize C₃ A (11/10) (18/5) T ≤ (Real.log (3 + C₃ * 2 ^ A) + A + 3) * Real.log |T| := by
  unfold logSize
  have hT0 : 0 < |T| := by linarith
  have hT1 : 1 ≤ |T| := by linarith
  have hlogT : 1 ≤ Real.log |T| := by
    rw [Real.le_log_iff_exp_le hT0]; linarith [Real.exp_one_lt_d9]
  have h3 : (11/10 : ℝ) / (11/10 - 1) = 11 := by norm_num
  rw [h3]
  have h2A : 0 ≤ (2 : ℝ) ^ A := Real.rpow_nonneg (by norm_num) _
  have hpow : (|T| + 18/5) ^ A ≤ 2 ^ A * |T| ^ A := by
    rw [← Real.mul_rpow (by norm_num) (abs_nonneg _)]
    exact Real.rpow_le_rpow (by linarith) (by linarith) hA
  have hTA : 1 ≤ |T| ^ A := Real.one_le_rpow hT1 hA
  have hC2 : 0 ≤ C₃ * 2 ^ A := mul_nonneg hC₃ h2A
  have hM : 3 + C₃ * (|T| + 18/5) ^ A ≤ (3 + C₃ * 2 ^ A) * |T| ^ A := by
    have : C₃ * (|T| + 18/5) ^ A ≤ C₃ * (2 ^ A * |T| ^ A) :=
      mul_le_mul_of_nonneg_left hpow hC₃
    nlinarith
  have hpos : 0 < 3 + C₃ * (|T| + 18/5) ^ A := by
    have := mul_nonneg hC₃ (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ |T| + 18/5) A)
    linarith
  have hpos' : 0 < 3 + C₃ * 2 ^ A := by linarith
  have hlog1 : Real.log (3 + C₃ * (|T| + 18/5) ^ A)
      ≤ Real.log (3 + C₃ * 2 ^ A) + A * Real.log |T| := by
    calc Real.log (3 + C₃ * (|T| + 18/5) ^ A)
        ≤ Real.log ((3 + C₃ * 2 ^ A) * |T| ^ A) := Real.log_le_log hpos hM
      _ = Real.log (3 + C₃ * 2 ^ A) + A * Real.log |T| := by
          rw [Real.log_mul hpos'.ne' (by positivity), Real.log_rpow hT0]
  have hL0 : 0 ≤ Real.log (3 + C₃ * 2 ^ A) := Real.log_nonneg (by linarith)
  have hL1 : Real.log (3 + C₃ * 2 ^ A) ≤ Real.log (3 + C₃ * 2 ^ A) * Real.log |T| :=
    le_mul_of_one_le_right hL0 hlogT
  have h11 := log_eleven_le_three
  nlinarith

/-! ## 7. The deliverables -/

/-- **(b) Unconditional segment bound on `σ ∈ [1/2, 3/2]`.** For `|T| ≥ 4` and a zero-avoiding
height `T` (`δ ≤ |Im ρ − T|` for every nontrivial zero `ρ`, `δ > 0`),
`‖ζ'/ζ(σ + iT)‖ ≤ 1600 log |T| + 9 log |T| / δ` for every `σ ∈ [1/2, 3/2]`.
Inputs: growth `‖ζ s‖ ≤ 7|Im s|^{3/2}` on `Re s ≥ −1/2` (`ZetaGrowthNeg`), centre `11/10 + iT`,
`R' = 8/5`, `ρ = 3/4`, coverage radius `r = 3/5`, so the disc reaches exactly `Re = −1/2` and
the covered segment is `[1/2, 17/10] ⊇ [1/2, 3/2]`. -/
theorem norm_logDeriv_zeta_le_on_segment (T : ℝ) (hT : 4 ≤ |T|) (δ : ℝ) (hδpos : 0 < δ)
    (hδ : ∀ ρ, IsNontrivialZero ρ → δ ≤ |ρ.im - T|) :
    ∀ σ ∈ Set.Icc (1/2 : ℝ) (3/2),
      ‖deriv riemannZeta (σ + T * I) / riemannZeta (σ + T * I)‖
        ≤ 1600 * Real.log |T| + 9 * Real.log |T| / δ := by
  intro σ hσ
  have h := norm_logDeriv_zeta_le_of_growth (a := -1/2) (C₃ := 7) (A := 3/2) (by norm_num)
    (by norm_num) ZeroDensityUnconditional.hgrowth (σ₀ := 11/10) (R' := 8/5) (ρ := 3/4)
    (r := 3/5) (T := T) (δ := δ) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by linarith) hδpos hδ σ ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have hL := logSize_concrete_le hT
  have hlogT : 0 ≤ Real.log |T| := Real.log_nonneg (by linarith)
  have hlog2 := two_thirds_le_log_two
  have hδ23 : 0 < δ * (2 / 3) := by positivity
  calc ‖deriv riemannZeta (σ + T * I) / riemannZeta (σ + T * I)‖
      ≤ 8 * (3/4) * logSize 7 (3/2) (11/10) (8/5) T / (3/4 - 3/5) ^ 2
          + logSize 7 (3/2) (11/10) (8/5) T / (δ * Real.log 2) := h
    _ = 2400 / 9 * logSize 7 (3/2) (11/10) (8/5) T
          + logSize 7 (3/2) (11/10) (8/5) T / (δ * Real.log 2) := by ring
    _ ≤ 2400 / 9 * (6 * Real.log |T|) + (6 * Real.log |T|) / (δ * (2 / 3)) := by
        gcongr
    _ = 1600 * Real.log |T| + 9 * Real.log |T| / δ := by field_simp; ring

/-- **(c) Segment bound on the full `σ ∈ [−1/2, 3/2]`, hypothesis-dependent.** The unproven
input is `hgrowth3`: `‖ζ s‖ ≤ C₃ |Im s|^A` on `−5/2 ≤ Re s ≤ 2`, `|Im s| ≥ 2` (the statement of
the not-yet-existing module `ZetaGrowthEM3`, a third Euler–Maclaurin step). With it, for
`|T| ≥ 6` and a zero-avoiding height (`δ ≤ |Im ρ − T|`, `δ > 0`): for every `σ ∈ [−1/2, 3/2]`,
`‖ζ'/ζ(σ + iT)‖ ≤ 623 Λ log |T| + 2 Λ log |T| / δ` with `Λ = log (3 + C₃ 2^A) + A + 3`.
Parameters: centre `11/10 + iT`, `R' = 18/5` (the disc reaches `Re = −5/2`), `ρ = 7/4`,
`r = 8/5`, covered segment `[−1/2, 27/10]`. -/
theorem norm_logDeriv_zeta_le_on_full_segment_of_growth {C₃ A : ℝ} (hC₃ : 0 ≤ C₃) (hA : 0 ≤ A)
    (hgrowth3 : ∀ s : ℂ, -5/2 ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C₃ * |s.im| ^ A)
    (T : ℝ) (hT : 6 ≤ |T|) (δ : ℝ) (hδpos : 0 < δ)
    (hδ : ∀ ρ, IsNontrivialZero ρ → δ ≤ |ρ.im - T|) :
    ∀ σ ∈ Set.Icc (-1/2 : ℝ) (3/2),
      ‖deriv riemannZeta (σ + T * I) / riemannZeta (σ + T * I)‖
        ≤ 623 * (Real.log (3 + C₃ * 2 ^ A) + A + 3) * Real.log |T|
          + 2 * (Real.log (3 + C₃ * 2 ^ A) + A + 3) * Real.log |T| / δ := by
  intro σ hσ
  have h := norm_logDeriv_zeta_le_of_growth (a := -5/2) hC₃ hA hgrowth3 (σ₀ := 11/10)
    (R' := 18/5) (ρ := 7/4) (r := 8/5) (T := T) (δ := δ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by linarith) hδpos hδ σ
    ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have hL := logSize_general_le hC₃ hA hT
  have hT0 : 0 < |T| := by linarith
  have hlogT : 1 ≤ Real.log |T| := by
    rw [Real.le_log_iff_exp_le hT0]; linarith [Real.exp_one_lt_d9]
  have hΛ0 : 0 ≤ Real.log (3 + C₃ * 2 ^ A) + A + 3 := by
    have h2A : 0 ≤ (2 : ℝ) ^ A := Real.rpow_nonneg (by norm_num) _
    have := Real.log_nonneg (by nlinarith [mul_nonneg hC₃ h2A] : (1 : ℝ) ≤ 3 + C₃ * 2 ^ A)
    linarith
  have hΛT : 0 ≤ (Real.log (3 + C₃ * 2 ^ A) + A + 3) * Real.log |T| := by positivity
  have hlog2 := two_thirds_le_log_two
  have hδ23 : 0 < δ * (2 / 3) := by positivity
  calc ‖deriv riemannZeta (σ + T * I) / riemannZeta (σ + T * I)‖
      ≤ 8 * (7/4) * logSize C₃ A (11/10) (18/5) T / (7/4 - 8/5) ^ 2
          + logSize C₃ A (11/10) (18/5) T / (δ * Real.log 2) := h
    _ = 5600 / 9 * logSize C₃ A (11/10) (18/5) T
          + logSize C₃ A (11/10) (18/5) T / (δ * Real.log 2) := by ring
    _ ≤ 5600 / 9 * ((Real.log (3 + C₃ * 2 ^ A) + A + 3) * Real.log |T|)
          + ((Real.log (3 + C₃ * 2 ^ A) + A + 3) * Real.log |T|) / (δ * (2 / 3)) := by
        gcongr
    _ = 5600 / 9 * ((Real.log (3 + C₃ * 2 ^ A) + A + 3) * Real.log |T|)
          + 3 / 2 * ((Real.log (3 + C₃ * 2 ^ A) + A + 3) * Real.log |T|) / δ := by
        field_simp
    _ ≤ 623 * (Real.log (3 + C₃ * 2 ^ A) + A + 3) * Real.log |T|
          + 2 * (Real.log (3 + C₃ * 2 ^ A) + A + 3) * Real.log |T| / δ := by
        have h1 : 5600 / 9 * ((Real.log (3 + C₃ * 2 ^ A) + A + 3) * Real.log |T|)
            ≤ 623 * (Real.log (3 + C₃ * 2 ^ A) + A + 3) * Real.log |T| := by
          nlinarith
        have h2 : 3 / 2 * ((Real.log (3 + C₃ * 2 ^ A) + A + 3) * Real.log |T|) / δ
            ≤ 2 * (Real.log (3 + C₃ * 2 ^ A) + A + 3) * Real.log |T| / δ := by
          apply div_le_div_of_nonneg_right _ hδpos.le
          nlinarith
        linarith

/-! ## 8. The prime side: the line `Re s = 3/2` -/

/-- **(2) Trivial bound on the prime side.** On the line `Re s = 3/2`,
`‖ζ'/ζ(3/2 + it)‖ ≤ Σ_n Λ(n) n^{−3/2}` (the coefficients `ExplicitFormula.coeff (3/2)`), for
every real `t`; this is `ZetaGrowth.norm_logDeriv_zeta_le_of_re_ge` with `ε = 1/2`. -/
theorem norm_logDeriv_zeta_le_on_line_three_halves (t : ℝ) :
    ‖deriv riemannZeta (3/2 + t * I) / riemannZeta (3/2 + t * I)‖
      ≤ ∑' n : ℕ, ExplicitFormula.coeff (3/2) n := by
  have hre : (3/2 + t * I : ℂ).re = 3/2 := by simp
  have h := ZetaGrowth.norm_logDeriv_zeta_le_of_re_ge (ε := 1/2) (by norm_num)
    (s := 3/2 + t * I) (by rw [hre]; norm_num)
  have h32 : (1 + 1/2 : ℝ) = 3/2 := by norm_num
  rw [h32] at h
  exact h

/-- The same on the whole half-plane `Re s ≥ 3/2`. -/
theorem norm_logDeriv_zeta_le_of_three_halves_le_re {s : ℂ} (hs : 3/2 ≤ s.re) :
    ‖deriv riemannZeta s / riemannZeta s‖ ≤ ∑' n : ℕ, ExplicitFormula.coeff (3/2) n := by
  have h := ZetaGrowth.norm_logDeriv_zeta_le_of_re_ge (ε := 1/2) (by norm_num) (s := s)
    (by norm_num; exact hs)
  have h32 : (1 + 1/2 : ℝ) = 3/2 := by norm_num
  rw [h32] at h
  exact h

end LogDerivSegmentBound

end
