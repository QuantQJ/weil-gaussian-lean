import Jensen
import Mathlib

/-!
# Borel–Carathéodory and the partial-fraction bound for `f'/f`

Everything in this file is PROVEN unconditionally (standard axioms only). Contents:

* **Borel–Carathéodory** `borel_caratheodory` (open-disc hypotheses) and
  `borel_caratheodory_closedBall`: if `g` is holomorphic on `ball c R`, `g c = 0` and
  `Re g ≤ A` (`A ≥ 0`) on the disc, then `‖g z‖ ≤ 2 r A / (R - r)` on `closedBall c r`, `r < R`.
  Route: for every `ε > 0` the map `φ = g / (2(A+ε) - g)` sends the disc into the open unit disc
  with `φ c = 0`; Mathlib's Schwarz lemma (`Complex.dist_le_div_mul_dist_of_mapsTo_ball`) bounds
  `φ`, one solves for `‖g‖`, and `ε → 0` (so the case `A = 0` needs no separate treatment).
* **Cauchy estimate** `norm_deriv_le_of_forall_mem_closedBall_norm_le` (wrapper around
  `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`).
* **Log-derivative bound** `norm_logDeriv_le_of_norm_le`: `h` holomorphic, nonvanishing on
  `ball c R` with `‖h‖ ≤ M ‖h c‖` there gives `‖h'/h‖ ≤ 8 log M / R` on `closedBall c (R/4)`
  (holomorphic logarithm from `Jensen`, Borel–Carathéodory, Cauchy).
* **Partial fractions, factorised form** `norm_logDeriv_sub_sum_le_of_factorization`:
  `f = ∏ (z - aₖ)^{mₖ} · g` on `ball c R'` with `aₖ ∈ closedBall c (R/2)`, `g ≠ 0` on `ball c ρ`
  (`ρ ≤ R < R'`), `‖f‖ ≤ M ‖f c‖` on the circle `‖z - c‖ = R`; then on `closedBall c (ρ/4)`,
  at non-zeros, `‖f'/f - ∑ mₖ/(z - aₖ)‖ ≤ 8 log M / ρ` (maximum modulus principle for `g`).
* **Partial fractions, zero-set form** `norm_logDeriv_sub_sum_le_of_finite_zeros`: same bound for
  `f` holomorphic on `ball c R'`, `f c ≠ 0`, whose zero set in `ball c ρ` (`2ρ ≤ R`) is a finite
  set `Z`, with multiplicities `m b ≥ 1` supplied by `Jensen.exists_factorization_of_finite_zeros`
  (the quotient is extended across the zeros by `exists_extension_of_factorization`).
  `norm_logDeriv_sub_sum_le_of_finite_zeros'` is the classical instance `ρ = R/2`:
  `‖f'/f - ∑ m_b/(z - b)‖ ≤ 16 log M / R` on `closedBall c (R/8)`, zeros counted in `ball c (R/2)`.

Not proven / not needed: nothing from the target list is hypothesis-dependent.
-/

noncomputable section

open Complex Metric Set Filter Topology

namespace PartialFractions

/-! ## Borel–Carathéodory -/

/-- Algebraic input to Borel–Carathéodory: if `Re w < B` with `B > 0`, then `‖w‖ < ‖2B - w‖`. -/
theorem norm_lt_norm_two_mul_sub_of_re_lt {w : ℂ} {B : ℝ} (hB : 0 < B) (hw : w.re < B) :
    ‖w‖ < ‖((2 * B : ℝ) : ℂ) - w‖ := by
  refine lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) ?_
  rw [Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, zero_sub]
  nlinarith [mul_pos hB (sub_pos.mpr hw)]

/-- **Borel–Carathéodory, strict form.** If `g` is holomorphic on `ball c R`, `g c = 0` and
`Re g < B` on the disc (`B > 0`), then `‖g z‖ ≤ 2 r B / (R - r)` for `z ∈ closedBall c r`,
`0 < r < R`. Proof: Schwarz's lemma applied to `φ = g / (2B - g)`. -/
theorem norm_le_of_re_lt {c : ℂ} {R r B : ℝ} (hr : 0 < r) (hrR : r < R) (hB : 0 < B)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball c R)) (hgc : g c = 0)
    (hre : ∀ z ∈ ball c R, (g z).re < B) {z : ℂ} (hz : z ∈ closedBall c r) :
    ‖g z‖ ≤ 2 * r * B / (R - r) := by
  have hR : 0 < R := hr.trans hrR
  have hzR : z ∈ ball c R := closedBall_subset_ball hrR hz
  have hzr : dist z c ≤ r := mem_closedBall.mp hz
  have hden : ∀ w ∈ ball c R, ((2 * B : ℝ) : ℂ) - g w ≠ 0 := by
    intro w hw h0
    have h1 := hre w hw
    have h2 : (((2 * B : ℝ) : ℂ) - g w).re = 0 := by rw [h0, Complex.zero_re]
    rw [Complex.sub_re, Complex.ofReal_re] at h2
    linarith
  set φ : ℂ → ℂ := fun w => g w / (((2 * B : ℝ) : ℂ) - g w) with hφ
  have hφd : DifferentiableOn ℂ φ (ball c R) :=
    hg.div ((differentiableOn_const _).sub hg) hden
  have hφc : φ c = 0 := by simp [hφ, hgc]
  have hmaps : MapsTo φ (ball c R) (ball (φ c) 1) := by
    intro w hw
    rw [hφc, mem_ball_zero_iff]
    show ‖g w / (((2 * B : ℝ) : ℂ) - g w)‖ < 1
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (hden w hw))]
    exact norm_lt_norm_two_mul_sub_of_re_lt hB (hre w hw)
  have hS := Complex.dist_le_div_mul_dist_of_mapsTo_ball hφd
    (hmaps.mono_right ball_subset_closedBall) hzR
  rw [hφc, dist_zero_right] at hS
  have hφz : ‖φ z‖ ≤ r / R := by
    calc ‖φ z‖ ≤ 1 / R * dist z c := hS
      _ ≤ 1 / R * r := by gcongr
      _ = r / R := by ring
  have hgz : ‖g z‖ = ‖φ z‖ * ‖((2 * B : ℝ) : ℂ) - g z‖ := by
    show ‖g z‖ = ‖g z / (((2 * B : ℝ) : ℂ) - g z)‖ * ‖((2 * B : ℝ) : ℂ) - g z‖
    rw [norm_div, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr (hden z hzR))]
  have hnorm2B : ‖((2 * B : ℝ) : ℂ)‖ = 2 * B := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have h3 : ‖((2 * B : ℝ) : ℂ) - g z‖ ≤ 2 * B + ‖g z‖ := by
    calc ‖((2 * B : ℝ) : ℂ) - g z‖ ≤ ‖((2 * B : ℝ) : ℂ)‖ + ‖g z‖ := norm_sub_le _ _
      _ = 2 * B + ‖g z‖ := by rw [hnorm2B]
  have h4 : ‖g z‖ ≤ r / R * (2 * B + ‖g z‖) := by
    calc ‖g z‖ = ‖φ z‖ * ‖((2 * B : ℝ) : ℂ) - g z‖ := hgz
      _ ≤ r / R * (2 * B + ‖g z‖) :=
        mul_le_mul hφz h3 (norm_nonneg _) (by positivity)
  rw [div_mul_eq_mul_div, le_div_iff₀ hR] at h4
  have hRr : 0 < R - r := by linarith
  rw [le_div_iff₀ hRr]
  nlinarith [h4]

/-- **Borel–Carathéodory.** Let `g` be holomorphic on the open disc `ball c R` with `g c = 0` and
`Re (g z) ≤ A` on the disc, where `A ≥ 0`. Then for `0 < r < R` and `z ∈ closedBall c r`,
`‖g z‖ ≤ 2 r A / (R - r)`. (For `A = 0` this forces `g ≡ 0` on the open disc.) -/
theorem borel_caratheodory {c : ℂ} {R r A : ℝ} (hr : 0 < r) (hrR : r < R) (hA : 0 ≤ A)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball c R)) (hgc : g c = 0)
    (hre : ∀ z ∈ ball c R, (g z).re ≤ A) {z : ℂ} (hz : z ∈ closedBall c r) :
    ‖g z‖ ≤ 2 * r * A / (R - r) := by
  have hRr : 0 < R - r := by linarith
  have hRr' : R - r ≠ 0 := hRr.ne'
  have hr' : r ≠ 0 := hr.ne'
  apply le_of_forall_pos_le_add
  intro ε hε
  have hδ : 0 < ε * (R - r) / (2 * r) := by positivity
  have hB : 0 < A + ε * (R - r) / (2 * r) := by linarith
  have key := norm_le_of_re_lt hr hrR hB hg hgc
    (fun w hw => lt_of_le_of_lt (hre w hw) (by linarith)) hz
  calc ‖g z‖ ≤ 2 * r * (A + ε * (R - r) / (2 * r)) / (R - r) := key
    _ = 2 * r * A / (R - r) + ε := by field_simp

/-- **Borel–Carathéodory, closed-disc form.** `g` holomorphic on `closedBall c R`, `g c = 0`,
`Re g ≤ A` on the closed disc (`A ≥ 0`): then `‖g z‖ ≤ 2 r A / (R - r)` on `closedBall c r`,
`0 < r < R`. -/
theorem borel_caratheodory_closedBall {c : ℂ} {R r A : ℝ} (hr : 0 < r) (hrR : r < R)
    (hA : 0 ≤ A) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (closedBall c R)) (hgc : g c = 0)
    (hre : ∀ z ∈ closedBall c R, (g z).re ≤ A) {z : ℂ} (hz : z ∈ closedBall c r) :
    ‖g z‖ ≤ 2 * r * A / (R - r) :=
  borel_caratheodory hr hrR hA (hg.mono ball_subset_closedBall) hgc
    (fun w hw => hre w (ball_subset_closedBall hw)) hz

/-! ## Cauchy's estimate for the derivative -/

/-- **Cauchy's estimate.** If `L` is holomorphic on `closedBall z r` (`r > 0`) and `‖L‖ ≤ B`
there, then `‖L' z‖ ≤ B / r`. -/
theorem norm_deriv_le_of_forall_mem_closedBall_norm_le {L : ℂ → ℂ} {z : ℂ} {r B : ℝ}
    (hr : 0 < r) (hL : DifferentiableOn ℂ L (closedBall z r))
    (hB : ∀ w ∈ closedBall z r, ‖L w‖ ≤ B) : ‖deriv L z‖ ≤ B / r :=
  Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr (hL.diffContOnCl_ball subset_rfl)
    (fun w hw => hB w (sphere_subset_closedBall hw))

/-! ## Holomorphic logarithm normalised at the centre -/

/-- A holomorphic logarithm of `h / h c` on `ball c R` vanishing at `c`: `L` holomorphic on the
disc with `L c = 0` and `exp (L z) = h z / h c`. Built from `Jensen.exists_differentiableOn_exp_eq_of_ne_zero`. -/
theorem exists_log_normalized {c : ℂ} {R : ℝ} (hR : 0 < R) {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (ball c R)) (hh0 : ∀ z ∈ ball c R, h z ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L (ball c R) ∧ L c = 0 ∧
      ∀ z ∈ ball c R, exp (L z) = h z / h c := by
  obtain ⟨L₀, hL₀, hexp⟩ := Jensen.exists_differentiableOn_exp_eq_of_ne_zero hR hh hh0
  refine ⟨fun z => L₀ z - L₀ c, hL₀.sub_const _, sub_self _, fun z hz => ?_⟩
  rw [Complex.exp_sub, hexp z hz, hexp c (mem_ball_self hR)]

/-! ## The log-derivative bound for a nonvanishing function -/

/-- **Log-derivative bound.** Let `h` be holomorphic and nonvanishing on `ball c R` (`R > 0`) with
`‖h z‖ ≤ M ‖h c‖` on the disc. Then for `z ∈ closedBall c (R/4)`,
`‖h' z / h z‖ ≤ 8 log M / R`. Proof: `L = log (h / h c)` with `L c = 0`, `Re L ≤ log M`;
Borel–Carathéodory gives `‖L‖ ≤ 2 log M` on `closedBall c (R/2)`; Cauchy's estimate on the disc of
radius `R/4` about `z` gives `‖L' z‖ ≤ 8 log M / R`; and `L' = h'/h`. -/
theorem norm_logDeriv_le_of_norm_le {c : ℂ} {R M : ℝ} (hR : 0 < R) {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (ball c R)) (hh0 : ∀ z ∈ ball c R, h z ≠ 0)
    (hbd : ∀ z ∈ ball c R, ‖h z‖ ≤ M * ‖h c‖) {z : ℂ} (hz : z ∈ closedBall c (R / 4)) :
    ‖deriv h z / h z‖ ≤ 8 * Real.log M / R := by
  have hc0 : h c ≠ 0 := hh0 c (mem_ball_self hR)
  have hcpos : 0 < ‖h c‖ := norm_pos_iff.mpr hc0
  have hM : 1 ≤ M := by
    have h1 : 1 * ‖h c‖ ≤ M * ‖h c‖ := by rw [one_mul]; exact hbd c (mem_ball_self hR)
    exact le_of_mul_le_mul_right h1 hcpos
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  obtain ⟨L, hL, hLc, hexp⟩ := exists_log_normalized hR hh hh0
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
  -- Borel–Carathéodory on the half disc
  have hBC : ∀ w ∈ closedBall c (R / 2), ‖L w‖ ≤ 2 * Real.log M := by
    intro w hw
    have := borel_caratheodory (by positivity : 0 < R / 2) (by linarith : R / 2 < R) hlogM
      hL hLc hre hw
    have hR0 : R ≠ 0 := hR.ne'
    have hhalf : R - R / 2 = R / 2 := by ring
    calc ‖L w‖ ≤ 2 * (R / 2) * Real.log M / (R - R / 2) := this
      _ = 2 * Real.log M := by rw [hhalf]; field_simp
  -- Cauchy's estimate on `closedBall z (R/4) ⊆ closedBall c (R/2)`
  have hsub : closedBall z (R / 4) ⊆ closedBall c (R / 2) := by
    apply closedBall_subset_closedBall'
    have := mem_closedBall.mp hz
    linarith
  have hsub' : closedBall c (R / 2) ⊆ ball c R := closedBall_subset_ball (by linarith)
  have hderiv : ‖deriv L z‖ ≤ 2 * Real.log M / (R / 4) :=
    norm_deriv_le_of_forall_mem_closedBall_norm_le (by positivity) (hL.mono (hsub.trans hsub'))
      (fun w hw => hBC w (hsub hw))
  -- `L' = h'/h`
  have hzR : z ∈ ball c R := hsub' (hsub (mem_closedBall_self (by positivity)))
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
  calc ‖deriv L z‖ ≤ 2 * Real.log M / (R / 4) := hderiv
    _ = 8 * Real.log M / R := by field_simp; ring

/-! ## Partial fractions: factorised form -/

/-- **Partial-fraction bound, factorised form.** Let `0 < ρ ≤ R < R'`, let `f = P · g` on
`ball c R'` where `P z = ∏ k ∈ s, (z - a k) ^ m k` with all `a k ∈ closedBall c (R/2)`, `g`
holomorphic on `ball c R'` and nonvanishing on `ball c ρ`; assume `f c ≠ 0` and
`‖f z‖ ≤ M ‖f c‖` on the circle `‖z - c‖ = R`. Then for every `z ∈ closedBall c (ρ/4)` with
`f z ≠ 0`, `‖f' z / f z - ∑ k ∈ s, m k / (z - a k)‖ ≤ 8 log M / ρ`.
Proof: on the circle `‖z - a k‖ ≥ ‖c - a k‖`, so `‖g‖ ≤ M ‖g c‖` there, hence on the whole disc by
the maximum modulus principle; then `norm_logDeriv_le_of_norm_le` for `g` on `ball c ρ`, and
`f'/f = ∑ m k/(z - a k) + g'/g`. -/
theorem norm_logDeriv_sub_sum_le_of_factorization {c : ℂ} {R R' ρ M : ℝ} (hρ : 0 < ρ)
    (hρR : ρ ≤ R) (hRR' : R < R') {ι : Type*} {s : Finset ι} {a : ι → ℂ} {m : ι → ℕ}
    (ha : ∀ k ∈ s, a k ∈ closedBall c (R / 2)) {f g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball c R')) (hg0 : ∀ z ∈ ball c ρ, g z ≠ 0)
    (hfg : ∀ z ∈ ball c R', f z = (∏ k ∈ s, (z - a k) ^ m k) * g z) (hfc : f c ≠ 0)
    (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M * ‖f c‖) {z : ℂ} (hz : z ∈ closedBall c (ρ / 4))
    (hfz : f z ≠ 0) :
    ‖deriv f z / f z - ∑ k ∈ s, (m k : ℂ) / (z - a k)‖ ≤ 8 * Real.log M / ρ := by
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
  -- the log-derivative bound for `g`
  have hgbound : ‖deriv g z / g z‖ ≤ 8 * Real.log M / ρ :=
    norm_logDeriv_le_of_norm_le hρ (hg.mono (ball_subset_ball (by linarith))) hg0 hbdρ hz
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

/-- **Partial-fraction bound, simple zeros listed with multiplicity.** The factorised form for
`f = ∏ k, (z - a k) · g` with `a : Fin n → ℂ`: `‖f'/f - ∑ k, 1/(z - a k)‖ ≤ 8 log M / ρ` on
`closedBall c (ρ/4)` at non-zeros. -/
theorem norm_logDeriv_sub_sum_le_of_factorization' {c : ℂ} {R R' ρ M : ℝ} (hρ : 0 < ρ)
    (hρR : ρ ≤ R) (hRR' : R < R') {n : ℕ} {a : Fin n → ℂ}
    (ha : ∀ k, a k ∈ closedBall c (R / 2)) {f g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball c R')) (hg0 : ∀ z ∈ ball c ρ, g z ≠ 0)
    (hfg : ∀ z ∈ ball c R', f z = (∏ k, (z - a k)) * g z) (hfc : f c ≠ 0)
    (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M * ‖f c‖) {z : ℂ} (hz : z ∈ closedBall c (ρ / 4))
    (hfz : f z ≠ 0) :
    ‖deriv f z / f z - ∑ k, 1 / (z - a k)‖ ≤ 8 * Real.log M / ρ := by
  have := norm_logDeriv_sub_sum_le_of_factorization hρ hρR hRR' (s := Finset.univ) (a := a)
    (m := fun _ => 1) (fun k _ => ha k) hg hg0 (by simpa only [pow_one] using hfg) hfc hM hz hfz
  simpa only [Nat.cast_one] using this

/-! ## Partial fractions: zero-set form -/

/-- A finite set of points of the open disc `ball c ρ` lies in a strictly smaller open disc. -/
theorem exists_radius_lt_of_forall_mem_ball {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (Z : Finset ℂ)
    (hZ : ∀ b ∈ Z, b ∈ ball c ρ) : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ < ρ ∧ ∀ b ∈ Z, b ∈ ball c ρ₀ := by
  rcases Z.eq_empty_or_nonempty with hZe | hne
  · exact ⟨ρ / 2, by positivity, by linarith, fun b hb => by simp [hZe] at hb⟩
  · obtain ⟨b₀, hb₀, hmax⟩ := Finset.exists_max_image Z (fun b => dist b c) hne
    have h0 : dist b₀ c < ρ := mem_ball.mp (hZ b₀ hb₀)
    have h0' : 0 ≤ dist b₀ c := dist_nonneg
    refine ⟨(dist b₀ c + ρ) / 2, by linarith, by linarith, fun b hb => ?_⟩
    rw [mem_ball]
    have := hmax b hb
    linarith

/-- **Extension of the factor `g` across the zeros.** Suppose `f` is holomorphic on `ball c R'`,
`Z ⊆ ball c ρ`, and `f = P · g` on `ball c ρ` with `P z = ∏ b ∈ Z, (z - b) ^ m b` and
`g` holomorphic, nonvanishing on `ball c ρ`. Then there is `G` holomorphic on `ball c R'`,
nonvanishing on `ball c ρ`, with `f = P · G` on all of `ball c R'` (namely `G = g` on `ball c ρ`
and `G = f / P` away from `Z`). -/
theorem exists_extension_of_factorization {c : ℂ} {R' ρ : ℝ}
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball c R')) (Z : Finset ℂ) (m : ℂ → ℕ)
    (hZρ : ∀ b ∈ Z, b ∈ ball c ρ) (hg : DifferentiableOn ℂ g (ball c ρ))
    (hg0 : ∀ z ∈ ball c ρ, g z ≠ 0)
    (hfg : ∀ z ∈ ball c ρ, f z = (∏ b ∈ Z, (z - b) ^ m b) * g z) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball c R') ∧ (∀ z ∈ ball c ρ, G z ≠ 0) ∧
      ∀ z ∈ ball c R', f z = (∏ b ∈ Z, (z - b) ^ m b) * G z := by
  classical
  set P : ℂ → ℂ := fun w => ∏ b ∈ Z, (w - b) ^ m b with hP
  have hfg' : ∀ w ∈ ball c ρ, f w = P w * g w := fun w hw => hfg w hw
  have hPne : ∀ w, w ∉ Z → P w ≠ 0 := by
    intro w hw
    apply Finset.prod_ne_zero_iff.mpr
    intro b hb
    exact pow_ne_zero _ (sub_ne_zero.mpr (fun h => hw (h ▸ hb)))
  have hPd : ∀ w, DifferentiableAt ℂ P w := by
    intro w
    show DifferentiableAt ℂ (fun w => ∏ b ∈ Z, (w - b) ^ m b) w
    exact DifferentiableAt.fun_finsetProd (fun b _ => (differentiableAt_id.sub_const _).pow _)
  set G : ℂ → ℂ := fun w => if w ∈ Z then g w else f w / P w with hG
  -- `G = g` on the small disc
  have hGg : ∀ w ∈ ball c ρ, G w = g w := by
    intro w hw
    by_cases hwZ : w ∈ Z
    · simp only [hG, if_pos hwZ]
    · simp only [hG, if_neg hwZ]
      rw [hfg' w hw, mul_div_cancel_left₀ _ (hPne w hwZ)]
  refine ⟨G, ?_, ?_, ?_⟩
  · -- differentiable on the big disc
    intro w hw
    apply DifferentiableAt.differentiableWithinAt
    by_cases hwρ : w ∈ ball c ρ
    · have hev : G =ᶠ[𝓝 w] g := by
        filter_upwards [isOpen_ball.mem_nhds hwρ] with v hv
        exact hGg v hv
      exact (hg.differentiableAt (isOpen_ball.mem_nhds hwρ)).congr_of_eventuallyEq hev
    · have hwZ : w ∉ Z := fun h => hwρ (hZρ w h)
      have hev : G =ᶠ[𝓝 w] fun v => f v / P v := by
        have hopen : IsOpen ((Z : Set ℂ)ᶜ) := Z.finite_toSet.isClosed.isOpen_compl
        filter_upwards [hopen.mem_nhds hwZ] with v hv
        have hvZ : v ∉ Z := hv
        simp only [hG, if_neg hvZ]
      exact ((hf.differentiableAt (isOpen_ball.mem_nhds hw)).div (hPd w) (hPne w hwZ))
        |>.congr_of_eventuallyEq hev
  · -- nonvanishing on the small disc
    intro w hw
    rw [hGg w hw]
    exact hg0 w hw
  · -- the factorisation on the big disc
    intro w hw
    by_cases hwZ : w ∈ Z
    · rw [hGg w (hZρ w hwZ)]
      exact hfg w (hZρ w hwZ)
    · show f w = P w * G w
      simp only [hG, if_neg hwZ]
      rw [mul_div_cancel₀ _ (hPne w hwZ)]

/-- **Partial-fraction bound for `f'/f` (zero-set form).** Let `0 < ρ`, `2ρ ≤ R < R'`, let `f`
be holomorphic on `ball c R'` with `f c ≠ 0`, let the finite set `Z` be exactly the zero set of `f`
in the disc `ball c ρ`, and assume `‖f z‖ ≤ M ‖f c‖` on the circle `‖z - c‖ = R`. Then there are
multiplicities `m b ≥ 1` (`b ∈ Z`) such that for every `z ∈ closedBall c (ρ/4)` with `f z ≠ 0`,
`‖f' z / f z - ∑ b ∈ Z, m b / (z - b)‖ ≤ 8 log M / ρ`.
The factorisation comes from `Jensen.exists_factorization_of_finite_zeros` (on a disc
`ball c ρ₀ ⊂ ball c ρ` containing `Z`), extended across `Z` by `exists_extension_of_factorization`. -/
theorem norm_logDeriv_sub_sum_le_of_finite_zeros {c : ℂ} {R R' ρ M : ℝ} (hρ : 0 < ρ)
    (hρR : 2 * ρ ≤ R) (hRR' : R < R') {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball c R'))
    (Z : Finset ℂ) (hZρ : ∀ b ∈ Z, b ∈ ball c ρ) (hZ : ∀ z ∈ ball c ρ, f z = 0 ↔ z ∈ Z)
    (hfc : f c ≠ 0) (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M * ‖f c‖) :
    ∃ m : ℂ → ℕ, (∀ b ∈ Z, 1 ≤ m b) ∧
      ∀ z ∈ closedBall c (ρ / 4), f z ≠ 0 →
        ‖deriv f z / f z - ∑ b ∈ Z, (m b : ℂ) / (z - b)‖ ≤ 8 * Real.log M / ρ := by
  have hρR' : ρ ≤ R' := by linarith
  obtain ⟨ρ₀, hρ₀, hρ₀ρ, hZρ₀⟩ := exists_radius_lt_of_forall_mem_ball hρ Z hZρ
  obtain ⟨m, g, hg, hg0, hfg, hm⟩ := Jensen.exists_factorization_of_finite_zeros hρ₀ hρ₀ρ
    (hf.mono (ball_subset_ball hρR')) Z hZρ₀ hZ
  obtain ⟨G, hG, hG0, hfG⟩ := exists_extension_of_factorization hf Z m hZρ hg hg0 hfg
  refine ⟨m, hm, fun z hz hfz => ?_⟩
  have ha : ∀ b ∈ Z, (fun b => b) b ∈ closedBall c (R / 2) := fun b hb =>
    ball_subset_closedBall (ball_subset_ball (by linarith) (hZρ b hb))
  exact norm_logDeriv_sub_sum_le_of_factorization hρ (by linarith) hRR' (s := Z) (a := fun b => b)
    (m := m) ha hG hG0 hfG hfc hM hz hfz

/-- **Partial-fraction bound, classical radii.** For `f` holomorphic on `ball c R'` (`R < R'`),
`f c ≠ 0`, with zero set `Z` in the half disc `ball c (R/2)` and `‖f‖ ≤ M ‖f c‖` on the circle
`‖z - c‖ = R`: there are multiplicities `m b ≥ 1` with
`‖f' z / f z - ∑ b ∈ Z, m b / (z - b)‖ ≤ 16 log M / R` for all `z ∈ closedBall c (R/8)`, `f z ≠ 0`. -/
theorem norm_logDeriv_sub_sum_le_of_finite_zeros' {c : ℂ} {R R' M : ℝ} (hR : 0 < R)
    (hRR' : R < R') {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball c R'))
    (Z : Finset ℂ) (hZρ : ∀ b ∈ Z, b ∈ ball c (R / 2))
    (hZ : ∀ z ∈ ball c (R / 2), f z = 0 ↔ z ∈ Z)
    (hfc : f c ≠ 0) (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M * ‖f c‖) :
    ∃ m : ℂ → ℕ, (∀ b ∈ Z, 1 ≤ m b) ∧
      ∀ z ∈ closedBall c (R / 8), f z ≠ 0 →
        ‖deriv f z / f z - ∑ b ∈ Z, (m b : ℂ) / (z - b)‖ ≤ 16 * Real.log M / R := by
  obtain ⟨m, hm, hbound⟩ := norm_logDeriv_sub_sum_le_of_finite_zeros (by positivity : 0 < R / 2)
    (by linarith) hRR' hf Z hZρ hZ hfc hM
  refine ⟨m, hm, fun z hz hfz => ?_⟩
  have hz' : z ∈ closedBall c (R / 2 / 4) := by
    rw [mem_closedBall] at hz ⊢; linarith
  calc ‖deriv f z / f z - ∑ b ∈ Z, (m b : ℂ) / (z - b)‖ ≤ 8 * Real.log M / (R / 2) :=
        hbound z hz' hfz
    _ = 16 * Real.log M / R := by field_simp; ring

end PartialFractions
