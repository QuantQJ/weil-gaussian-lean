import Mathlib
import ZetaGrowth
import FleetHeadContourZeta

/-!
# Littlewood's bound for `1/ζ` to the right of a zero-free half-plane

Adapted from kerr-lean `Kerr/Zeta/Littlewood.lean` (James C. Kerr, Apache-2.0), sections 1–4 and 6.
Changes from the source: the hypothesis RH is replaced by a zero-free half-plane `Re s > 1/2 + δ₀`
(`δ₀ ≥ 0`), and the disc centre `4 + it` by `4 + δ₀ + it`, so every estimate moves right by `δ₀`;
the crude bound `‖ζ s‖ ≤ 9 |Im s|` is taken on `Re s ≥ 1/2` from hp-proof's `ZetaGrowth.zeta_growth_strip`
(the source used `Re s ≥ 1/4` and copied PrimeNumberTheoremAnd lemmas); `1/ζ` is completed at `s = 1`
as `(s−1)/((s−1)·zetaReg s + 1)` with hp-proof's `FleetHeadContour.zetaReg`.

* `three_circles` (verbatim): Hadamard three circles, from Mathlib's three-lines theorem.
* `exists_log_ball`, `log_ball_eq_log` (verbatim): holomorphic logarithm on a zero-free disc.
* `littlewood_aux`, `littlewood_bound`: if `ζ ≠ 0` on `Re s > 1/2 + δ₀`, then for every `δ, η > 0`,
  `‖ζ(σ+it)‖, ‖ζ(σ+it)‖⁻¹ ≤ C |t|^η` for `σ ≥ 1/2 + δ₀ + δ`, `|t| ≥ 8`
  (Borel–Carathéodory + three circles; for `δ₀ = 0` this is Littlewood's theorem under RH).
* `invZeta_bound`: the same hypothesis gives `‖1/ζ(s)‖ ≤ C (1 + |Im s|)^η` on `Re s ≥ σ₀ > 1/2 + δ₀`.
-/

noncomputable section
open Complex Metric Set Filter Topology
open scoped ArithmeticFunction.Moebius

namespace FleetLandauTransfer

open HadamardThreeLines in
/-- **Hadamard three-circles theorem**, derived from Mathlib's three-lines theorem via
`w ↦ c + exp w`. -/
theorem three_circles {f : ℂ → ℂ} {c : ℂ} {r₁ r₃ a b : ℝ} (hr₁ : 0 < r₁) (h13 : r₁ < r₃)
    (hf : ∀ z ∈ closedBall c r₃, DifferentiableAt ℂ f z)
    (ha : ∀ z, ‖z - c‖ = r₁ → ‖f z‖ ≤ a) (hb : ∀ z, ‖z - c‖ = r₃ → ‖f z‖ ≤ b)
    {z : ℂ} (hz1 : r₁ ≤ ‖z - c‖) (hz3 : ‖z - c‖ ≤ r₃) :
    ‖f z‖ ≤ a ^ (1 - Real.log (‖z - c‖ / r₁) / Real.log (r₃ / r₁)) *
      b ^ (Real.log (‖z - c‖ / r₁) / Real.log (r₃ / r₁)) := by
  set l := Real.log r₁ with hl
  set u := Real.log r₃ with hu
  have hr₃ : 0 < r₃ := hr₁.trans h13
  have hlu : l < u := Real.log_lt_log hr₁ h13
  set F : ℂ → ℂ := fun w => f (c + exp w) with hF
  have hzc : z - c ≠ 0 := by
    intro h; rw [h, norm_zero] at hz1; linarith
  set w := Complex.log (z - c) with hwdef
  have hw : exp w = z - c := exp_log hzc
  have hwre : w.re = Real.log ‖z - c‖ := log_re _
  have hmem : ∀ v ∈ verticalClosedStrip l u, c + exp v ∈ closedBall c r₃ := by
    intro v hv
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_exp]
    have : v.re ≤ u := hv.2
    calc Real.exp v.re ≤ Real.exp u := Real.exp_le_exp.mpr this
      _ = r₃ := Real.exp_log hr₃
  have hdiffF : ∀ v ∈ verticalClosedStrip l u, DifferentiableAt ℂ F v := by
    intro v hv
    have h1 : DifferentiableAt ℂ (fun v : ℂ => c + exp v) v :=
      (differentiableAt_exp).const_add c
    exact (hf _ (hmem v hv)).comp v h1
  have hd : DiffContOnCl ℂ F (verticalStrip l u) := by
    apply DifferentiableOn.diffContOnCl
    intro v hv
    have hv' : v ∈ verticalClosedStrip l u := by
      rw [verticalStrip, closure_preimage_re, closure_Ioo hlu.ne] at hv
      exact hv
    exact (hdiffF v hv').differentiableWithinAt
  have hB : BddAbove ((norm ∘ F) '' verticalClosedStrip l u) := by
    have hcont : ContinuousOn f (closedBall c r₃) :=
      fun z hz => (hf z hz).continuousAt.continuousWithinAt
    obtain ⟨M, hM⟩ := (isCompact_closedBall c r₃).exists_bound_of_continuousOn hcont
    refine ⟨M, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact hM _ (hmem v hv)
  have ha' : ∀ v ∈ re ⁻¹' {l}, ‖F v‖ ≤ a := by
    intro v hv
    apply ha
    simp only [mem_preimage, mem_singleton_iff] at hv
    rw [add_sub_cancel_left, norm_exp, hv, hl, Real.exp_log hr₁]
  have hb' : ∀ v ∈ re ⁻¹' {u}, ‖F v‖ ≤ b := by
    intro v hv
    apply hb
    simp only [mem_preimage, mem_singleton_iff] at hv
    rw [add_sub_cancel_left, norm_exp, hv, hu, Real.exp_log hr₃]
  have hzpos : 0 < ‖z - c‖ := by linarith
  have hzmem : w ∈ verticalClosedStrip l u :=
    ⟨by rw [hwre]; exact Real.log_le_log hr₁ hz1, by rw [hwre]; exact Real.log_le_log hzpos hz3⟩
  have key := norm_le_interp_of_mem_verticalClosedStrip' hlu hzmem hd hB ha' hb'
  have hFw : F w = f z := by simp only [hF, hw, add_sub_cancel]
  rw [hFw, hwre] at key
  have e : (Real.log ‖z - c‖ - l) / (u - l) =
      Real.log (‖z - c‖ / r₁) / Real.log (r₃ / r₁) := by
    rw [Real.log_div hzpos.ne' hr₁.ne', Real.log_div hr₃.ne' hr₁.ne']
  rw [e] at key
  exact key

/-! ## 2. Elementary bounds for `ζ` -/

local notation "ζ" => riemannZeta

lemma hasSum_inv_sq_from_two :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
  have h := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_add, Nat.cast_ofNat,
    CharP.cast_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero,
    zero_add, Nat.cast_one, one_pow, div_one] at h
  simpa using h

lemma pi_sq_div_six_sub_one_lt : Real.pi ^ 2 / 6 - 1 < 2 / 3 := by
  have h1 := Real.pi_lt_d2
  have h0 := Real.pi_pos
  nlinarith

/-- For `Re s ≥ 2`, `‖ζ(s) − 1‖ ≤ π²/6 − 1 < 2/3`. -/
lemma zeta_sub_one_norm_le {s : ℂ} (hs : 2 ≤ s.re) : ‖ζ s - 1‖ ≤ Real.pi ^ 2 / 6 - 1 := by
  have hs1 : 1 < s.re := by linarith
  have hterm : ∀ n : ℕ, ‖1 / ((n : ℂ) + 1 + 1) ^ s‖ ≤ 1 / ((n : ℝ) + 2) ^ 2 := by
    intro n
    have e : ((n : ℂ) + 1 + 1) = (((n + 2 : ℕ) : ℕ) : ℂ) := by push_cast; ring
    rw [e, norm_div, norm_one, norm_natCast_cpow_of_pos (by omega)]
    push_cast
    have h2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have : ((n : ℝ) + 2) ^ (2 : ℝ) ≤ ((n : ℝ) + 2) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hs
    rw [← Real.rpow_natCast]
    push_cast
    gcongr
  have hsum2 : Summable (fun n : ℕ => ‖1 / ((n : ℂ) + 1 + 1) ^ s‖) :=
    hasSum_inv_sq_from_two.summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  have hsum : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) := by
    rw [← summable_nat_add_iff 1]
    push_cast
    exact hsum2.of_norm
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs1, hsum.tsum_eq_zero_add]
  simp only [CharP.cast_eq_zero, zero_add, one_cpow, div_one, add_sub_cancel_left, Nat.cast_add,
    Nat.cast_one]
  calc ‖∑' n : ℕ, 1 / ((n : ℂ) + 1 + 1) ^ s‖ ≤ ∑' n : ℕ, ‖1 / ((n : ℂ) + 1 + 1) ^ s‖ :=
        norm_tsum_le_tsum_norm hsum2
    _ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ 2 :=
        hsum2.tsum_le_tsum hterm hasSum_inv_sq_from_two.summable
    _ = Real.pi ^ 2 / 6 - 1 := hasSum_inv_sq_from_two.tsum_eq

lemma zeta_norm_le_two {s : ℂ} (hs : 2 ≤ s.re) : ‖ζ s‖ ≤ 2 := by
  have h := zeta_sub_one_norm_le hs
  have h2 := pi_sq_div_six_sub_one_lt
  calc ‖ζ s‖ = ‖(ζ s - 1) + 1‖ := by ring_nf
    _ ≤ ‖ζ s - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ 2 := by rw [norm_one]; linarith

lemma zeta_norm_ge_third {s : ℂ} (hs : 2 ≤ s.re) : 1 / 3 ≤ ‖ζ s‖ := by
  have h := zeta_sub_one_norm_le hs
  have h2 := pi_sq_div_six_sub_one_lt
  have : ‖(1 : ℂ)‖ ≤ ‖ζ s‖ + ‖ζ s - 1‖ := by
    calc ‖(1 : ℂ)‖ = ‖ζ s - (ζ s - 1)‖ := by ring_nf
      _ ≤ ‖ζ s‖ + ‖ζ s - 1‖ := norm_sub_le _ _
  rw [norm_one] at this
  linarith

lemma zeta_re_pos {s : ℂ} (hs : 2 ≤ s.re) : 0 < (ζ s).re := by
  have h := zeta_sub_one_norm_le hs
  have h2 := pi_sq_div_six_sub_one_lt
  have h3 : |(ζ s - 1).re| ≤ ‖ζ s - 1‖ := abs_re_le_norm _
  have h4 : (ζ s - 1).re = (ζ s).re - 1 := by simp
  rw [h4] at h3
  have := (abs_le.mp h3).1
  linarith

lemma log_zeta_norm_le {s : ℂ} (hs : 2 ≤ s.re) : ‖Complex.log (ζ s)‖ ≤ 3 := by
  have hlo := zeta_norm_ge_third hs
  have hhi := zeta_norm_le_two hs
  have hpos : 0 < ‖ζ s‖ := by linarith
  have harg : |arg (ζ s)| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl (zeta_re_pos hs))
  have hlog : |Real.log ‖ζ s‖| ≤ Real.log 3 := by
    rw [abs_le]
    constructor
    · have : Real.log (1 / 3) ≤ Real.log ‖ζ s‖ := Real.log_le_log (by norm_num) hlo
      rw [one_div, Real.log_inv] at this
      linarith
    · exact Real.log_le_log hpos (by linarith)
  have hl3 : Real.log 3 < 1.2 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have e1 := Real.exp_one_gt_d9
    have : Real.exp 1.2 = Real.exp 1 * Real.exp 0.2 := by rw [← Real.exp_add]; norm_num
    have e2 := Real.add_one_le_exp (0.2 : ℝ)
    rw [this]; nlinarith [Real.exp_pos 1, Real.exp_pos 0.2]
  have hpi := Real.pi_lt_d2
  calc ‖Complex.log (ζ s)‖ ≤ |(Complex.log (ζ s)).re| + |(Complex.log (ζ s)).im| :=
        norm_le_abs_re_add_abs_im _
    _ = |Real.log ‖ζ s‖| + |arg (ζ s)| := by rw [log_re, log_im]
    _ ≤ 3 := by linarith

/-- Crude polynomial bound: `‖ζ(s)‖ ≤ 9 |Im s|` for `Re s ≥ 1/2`, `|Im s| ≥ 2`
(`ZetaGrowth.zeta_growth_strip` for `Re s ≤ 2`, `zeta_norm_le_two` beyond). -/
lemma zeta_norm_le_poly {s : ℂ} (hs : 1 / 2 ≤ s.re) (ht : 2 ≤ |s.im|) : ‖ζ s‖ ≤ 9 * |s.im| := by
  by_cases h2 : 2 ≤ s.re
  · have := zeta_norm_le_two h2; linarith
  · push Not at h2
    have := ZetaGrowth.zeta_growth_strip hs h2.le ht
    linarith [abs_nonneg s.im]


/-! ## 3. Holomorphic logarithms on discs -/

/-- A nonvanishing holomorphic function on a disc has a holomorphic logarithm (a primitive of
`f'/f`, Mathlib's `DifferentiableOn.isExactOn_ball`), normalised by `L c = log (f c)`. -/
theorem exists_log_ball {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hd : ∀ z ∈ ball c R, DifferentiableAt ℂ f z) (hne : ∀ z ∈ ball c R, f z ≠ 0) (hR : 0 < R) :
    ∃ L : ℂ → ℂ, (∀ z ∈ ball c R, HasDerivAt L (deriv f z / f z) z) ∧
      (∀ z ∈ ball c R, exp (L z) = f z) ∧ L c = Complex.log (f c) := by
  have hdo : DifferentiableOn ℂ f (ball c R) := fun z hz => (hd z hz).differentiableWithinAt
  have hg : DifferentiableOn ℂ (fun z => deriv f z / f z) (ball c R) :=
    (hdo.deriv isOpen_ball).div hdo hne
  obtain ⟨G, hG⟩ := hg.isExactOn_ball
  set L : ℂ → ℂ := fun z => G z - G c + Complex.log (f c) with hL
  have hLd : ∀ z ∈ ball c R, HasDerivAt L (deriv f z / f z) z := by
    intro z hz
    have := ((hG z hz).sub_const (G c)).add_const (Complex.log (f c))
    simpa [hL] using this
  have hc : c ∈ ball c R := mem_ball_self hR
  refine ⟨L, hLd, ?_, by simp [hL]⟩
  set h : ℂ → ℂ := fun z => f z * exp (-L z) with hh
  have hhd : ∀ z ∈ ball c R, HasDerivAt h 0 z := by
    intro z hz
    have h1 := (hd z hz).hasDerivAt
    have h2 := ((hLd z hz).neg).cexp
    have := h1.mul h2
    convert this using 1
    have := hne z hz
    field_simp
    ring
  have hconst : ∀ z ∈ ball c R, h z = h c := fun z hz =>
    isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c R).isPreconnected
      (fun w hw => (hhd w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hhd w hw).deriv) hz hc
  have hhc : h c = 1 := by
    simp only [hh, hL, sub_self, zero_add, exp_neg, exp_log (hne c hc)]
    exact mul_inv_cancel₀ (hne c hc)
  intro z hz
  have h1 := hconst z hz
  rw [hhc] at h1
  simp only [hh, exp_neg] at h1
  have hexp : exp (L z) ≠ 0 := exp_ne_zero _
  rw [mul_inv_eq_one₀ hexp] at h1
  exact h1.symm

/-- On a sub-disc where `Re f > 0`, the logarithm of `exists_log_ball` is the principal one. -/
theorem log_ball_eq_log {f L : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hd : ∀ z ∈ ball c r, DifferentiableAt ℂ f z)
    (hL : ∀ z ∈ ball c r, HasDerivAt L (deriv f z / f z) z) (hLc : L c = Complex.log (f c))
    (hpos : ∀ z ∈ ball c r, 0 < (f z).re) : ∀ z ∈ ball c r, L z = Complex.log (f z) := by
  have hlog : ∀ z ∈ ball c r, HasDerivAt (fun w => Complex.log (f w)) (deriv f z / f z) z :=
    fun z hz => (hd z hz).hasDerivAt.clog (mem_slitPlane_iff.mpr (Or.inl (hpos z hz)))
  intro z hz
  exact isOpen_ball.eqOn_of_deriv_eq (convex_ball c r).isPreconnected
    (fun w hw => (hL w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hlog w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => by rw [(hL w hw).deriv, (hlog w hw).deriv]) (mem_ball_self hr) hLc hz

/-! ## 4. Under RH: Littlewood's bounds for `ζ` and `1/ζ` -/


/-! ## 4. Under a zero-free half-plane: Littlewood's bounds for `ζ` and `1/ζ` -/

/-- `x^θ ≤ λ x + λ^{-θ/(1-θ)}` for `0 ≤ θ < 1`, `x ≥ 0`, `λ > 0`. -/
lemma rpow_le_mul_add {θ x lam : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hx : 0 ≤ x) (hlam : 0 < lam) :
    x ^ θ ≤ lam * x + lam ^ (-θ / (1 - θ)) := by
  set x0 := lam ^ (-1 / (1 - θ)) with hx0
  have hx0pos : 0 < x0 := Real.rpow_pos_of_pos hlam _
  have h1θ : 0 < 1 - θ := by linarith
  by_cases hxx : x ≤ x0
  · have : x ^ θ ≤ x0 ^ θ := Real.rpow_le_rpow hx hxx hθ0
    have e : x0 ^ θ = lam ^ (-θ / (1 - θ)) := by
      rw [hx0, ← Real.rpow_mul hlam.le]; congr 1; ring
    have : 0 ≤ lam * x := by positivity
    linarith
  · push Not at hxx
    have hxpos : 0 < x := hx0pos.trans hxx
    have h2 : x ^ (θ - 1) ≤ x0 ^ (θ - 1) := Real.rpow_le_rpow_of_nonpos hx0pos hxx.le (by linarith)
    have e : x0 ^ (θ - 1) = lam := by
      rw [hx0, ← Real.rpow_mul hlam.le]
      have : -1 / (1 - θ) * (θ - 1) = 1 := by field_simp; ring
      rw [this, Real.rpow_one]
    rw [Real.rpow_sub_one hxpos.ne', e, div_le_iff₀ hxpos] at h2
    have : 0 ≤ lam ^ (-θ / (1 - θ)) := Real.rpow_nonneg hlam.le _
    linarith

/-- The three-circles exponent used below: circles of radii `1 < 4 + δ₀ - σ ≤ 7/2 - 2δ < 7/2 - δ`
around `4 + δ₀ + it`. -/
def thetaD (δ : ℝ) : ℝ := Real.log (7 / 2 - 2 * δ) / Real.log (7 / 2 - δ)

lemma thetaD_mem {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) : 0 ≤ thetaD δ ∧ thetaD δ < 1 := by
  have h1 : 0 < Real.log (7 / 2 - 2 * δ) := Real.log_pos (by linarith)
  have h2 : Real.log (7 / 2 - 2 * δ) < Real.log (7 / 2 - δ) :=
    Real.log_lt_log (by linarith) (by linarith)
  exact ⟨div_nonneg h1.le (h1.trans h2).le, (div_lt_one (h1.trans h2)).mpr h2⟩

/-- **Littlewood's bound, explicit form.** If `ζ ≠ 0` on `Re s > 1/2 + δ₀` (`δ₀ ≥ 0`), then for
`1/2 + δ₀ + 2δ ≤ σ ≤ 3 + δ₀` and `|t| ≥ 8`, both `‖ζ(σ+it)‖` and `‖ζ(σ+it)‖⁻¹` are at most
`exp (3 b^θ)`, `b = (14 log(9(|t|+4)) + 42)/δ`, `θ = thetaD δ < 1`. Proof: a holomorphic `log ζ` on
the disc `|s − (4+δ₀+it)| < 7/2 − δ/2` (zero-free by hypothesis), Borel–Carathéodory on that disc
(with `log|ζ| ≤ log(9(|t|+4))`), and the three-circles theorem with radii `1`, `4 + δ₀ − σ`, `7/2 − δ`
(on the radius-`1` circle `|log ζ| ≤ 3`). -/
theorem littlewood_aux {δ₀ : ℝ} (hδ₀ : 0 ≤ δ₀) (hZ : ∀ s : ℂ, 1 / 2 + δ₀ < s.re → ζ s ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    {σ t : ℝ} (hσ1 : 1 / 2 + δ₀ + 2 * δ ≤ σ) (hσ2 : σ ≤ 3 + δ₀) (ht : 8 ≤ |t|) :
    ‖ζ (σ + t * I)‖ ≤ Real.exp (3 * ((14 * Real.log (9 * (|t| + 4)) + 42) / δ) ^ thetaD δ) ∧
    ‖ζ (σ + t * I)‖⁻¹ ≤ Real.exp (3 * ((14 * Real.log (9 * (|t| + 4)) + 42) / δ) ^ thetaD δ) := by
  set c : ℂ := (4 + δ₀ : ℝ) + t * I with hc
  set R : ℝ := 7 / 2 - δ / 2 with hR
  set r₃ : ℝ := 7 / 2 - δ with hr₃
  have hRpos : 0 < R := by linarith
  have hball : ∀ z ∈ ball c R, 1 / 2 + δ₀ + δ / 2 < z.re ∧ |t| - 4 ≤ |z.im| ∧ |z.im| ≤ |t| + 4 := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have h1 := abs_re_le_norm (z - c)
    have h2 := abs_im_le_norm (z - c)
    have e1 : (z - c).re = z.re - (4 + δ₀) := by simp [hc]
    have e2 : (z - c).im = z.im - t := by simp [hc]
    rw [e1] at h1
    rw [e2] at h2
    have a1 := (abs_lt.mp (h1.trans_lt hz)).1
    have a2 := abs_sub_abs_le_abs_sub z.im t
    have a3 := abs_sub_abs_le_abs_sub t z.im
    rw [abs_sub_comm] at a3
    refine ⟨by linarith, by linarith, by linarith⟩
  have hne1 : ∀ z ∈ ball c R, z ≠ 1 := by
    intro z hz h
    have := (hball z hz).2.1
    rw [h] at this; simp at this; linarith
  have hd : ∀ z ∈ ball c R, DifferentiableAt ℂ ζ z :=
    fun z hz => differentiableAt_riemannZeta (hne1 z hz)
  have hnz : ∀ z ∈ ball c R, ζ z ≠ 0 :=
    fun z hz => hZ z (by linarith [(hball z hz).1])
  obtain ⟨L, hLd, hLexp, hLc⟩ := exists_log_ball hd hnz hRpos
  have hsub2 : ball c 2 ⊆ ball c R := ball_subset_ball (by linarith)
  have hre2 : ∀ z ∈ ball c 2, 2 < z.re := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have h1 := abs_re_le_norm (z - c)
    have e1 : (z - c).re = z.re - (4 + δ₀) := by simp [hc]
    rw [e1] at h1
    linarith [(abs_lt.mp (h1.trans_lt hz)).1]
  have hLlog : ∀ z ∈ ball c 2, L z = Complex.log (ζ z) :=
    log_ball_eq_log two_pos (fun z hz => hd z (hsub2 hz)) (fun z hz => hLd z (hsub2 hz)) hLc
      (fun z hz => zeta_re_pos (hre2 z hz).le)
  have hcre : c.re = 4 + δ₀ := by simp [hc]
  have hLc3 : ‖L c‖ ≤ 3 := by rw [hLc]; exact log_zeta_norm_le (by rw [hcre]; linarith)
  -- Borel–Carathéodory
  set M := Real.log (9 * (|t| + 4)) with hM
  have hMpos : 0 < M := Real.log_pos (by linarith [abs_nonneg t])
  set g : ℂ → ℂ := fun z => L (c + z) with hg
  have hmemc : ∀ z ∈ ball (0 : ℂ) R, c + z ∈ ball c R := by
    intro z hz
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    simpa using hz
  have hgd : DifferentiableOn ℂ g (ball 0 R) := by
    intro z hz
    have h1 : DifferentiableAt ℂ (fun z : ℂ => c + z) z := (differentiableAt_id).const_add c
    exact ((hLd _ (hmemc z hz)).differentiableAt.comp z h1).differentiableWithinAt
  have hgM : MapsTo g (ball 0 R) {z | z.re ≤ M} := by
    intro z hz
    have hw := hmemc z hz
    simp only [mem_ofPred_eq, hg]
    have hre : (L (c + z)).re = Real.log ‖ζ (c + z)‖ := by
      rw [← hLexp _ hw, norm_exp, Real.log_exp]
    rw [hre]
    obtain ⟨h1, h2, h3⟩ := hball _ hw
    have hz9 := zeta_norm_le_poly (s := c + z) (by linarith) (by linarith)
    apply Real.log_le_log (norm_pos_iff.mpr (hnz _ hw))
    linarith
  have hBC : ∀ w, ‖w - c‖ = r₃ → ‖L w‖ ≤ (14 * M + 42) / δ := by
    intro w hw
    have hz : w - c ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff, hw]; linarith
    have key := borelCaratheodory hMpos hgd hgM hRpos hz
    simp only [hg, add_sub_cancel, add_zero] at key
    rw [hw] at key
    have e : R - r₃ = δ / 2 := by rw [hR, hr₃]; ring
    rw [e] at key
    refine key.trans ?_
    have hLc0 : 0 ≤ ‖L c‖ := norm_nonneg _
    have e2 : 2 * M * r₃ / (δ / 2) + ‖L c‖ * (R + r₃) / (δ / 2) =
        (4 * M * r₃ + 2 * ‖L c‖ * (R + r₃)) / δ := by field_simp; ring
    rw [e2]
    apply div_le_div_of_nonneg_right _ hδ.le
    have hr3 : r₃ ≤ 7 / 2 := by linarith
    have hRr : R + r₃ ≤ 7 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hr3 hMpos.le, mul_le_mul_of_nonneg_left hRr hLc0]
  -- three circles
  have hcl : closedBall c r₃ ⊆ ball c R := closedBall_subset_ball (by linarith)
  have hf3 : ∀ z ∈ closedBall c r₃, DifferentiableAt ℂ L z :=
    fun z hz => (hLd z (hcl hz)).differentiableAt
  have ha : ∀ z, ‖z - c‖ = 1 → ‖L z‖ ≤ 3 := by
    intro z hz
    have hz2 : z ∈ ball c 2 := by rw [mem_ball, dist_eq_norm, hz]; norm_num
    rw [hLlog z hz2]
    exact log_zeta_norm_le (hre2 z hz2).le
  have hzc : ‖((σ : ℂ) + t * I) - c‖ = 4 + δ₀ - σ := by
    have : ((σ : ℂ) + t * I) - c = ((σ - (4 + δ₀) : ℝ) : ℂ) := by rw [hc]; push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have key := three_circles one_pos (by linarith : (1 : ℝ) < r₃) hf3 ha hBC
    (by rw [hzc]; linarith) (by rw [hzc]; linarith)
  rw [hzc, div_one, div_one] at key
  obtain ⟨hθ0, hθ1⟩ := thetaD_mem hδ hδ1
  set θ := Real.log (4 + δ₀ - σ) / Real.log r₃ with hθ
  have hlogr3 : 0 < Real.log r₃ := Real.log_pos (by linarith)
  have hθnn : 0 ≤ θ := div_nonneg (Real.log_nonneg (by linarith)) hlogr3.le
  have hθle : θ ≤ thetaD δ := by
    rw [hθ, thetaD]
    exact div_le_div_of_nonneg_right (Real.log_le_log (by linarith) (by linarith)) hlogr3.le
  set b := (14 * M + 42) / δ with hb
  have hb1 : 1 ≤ b := by
    rw [hb, le_div_iff₀ hδ]; linarith
  have hLz : ‖L (σ + t * I)‖ ≤ 3 * b ^ thetaD δ := by
    refine key.trans ?_
    have h3 : (3 : ℝ) ^ (1 - θ) ≤ 3 := by
      calc (3 : ℝ) ^ (1 - θ) ≤ 3 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 3 := Real.rpow_one 3
    have hbθ : b ^ θ ≤ b ^ thetaD δ := Real.rpow_le_rpow_of_exponent_le hb1 hθle
    exact mul_le_mul h3 hbθ (Real.rpow_nonneg (by linarith) _) (by norm_num)
  have hzR : ((σ : ℂ) + t * I) ∈ ball c R := hcl (by rw [mem_closedBall, dist_eq_norm, hzc]; linarith)
  have hn : ‖ζ (σ + t * I)‖ = Real.exp (L (σ + t * I)).re := by
    rw [← hLexp _ hzR, norm_exp]
  constructor
  · rw [hn]; exact Real.exp_le_exp.mpr ((re_le_norm _).trans hLz)
  · rw [hn, ← Real.exp_neg]
    refine Real.exp_le_exp.mpr ?_
    have := abs_re_le_norm (L (σ + t * I))
    have := neg_le_abs (L (σ + t * I)).re
    linarith

/-- **Littlewood's bound to the right of a zero-free half-plane.** If `ζ ≠ 0` on `Re s > 1/2 + δ₀`
(`δ₀ ≥ 0`), then for every `δ > 0` and `η > 0` there is `C` with `‖ζ(σ+it)‖ ≤ C|t|^η` and
`‖ζ(σ+it)‖⁻¹ ≤ C|t|^η` for all `σ ≥ 1/2 + δ₀ + δ`, `|t| ≥ 8` (`δ₀ = 0`: Littlewood under RH). -/
theorem littlewood_bound {δ₀ : ℝ} (hδ₀ : 0 ≤ δ₀) (hZ : ∀ s : ℂ, 1 / 2 + δ₀ < s.re → ζ s ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) {η : ℝ} (hη : 0 < η) :
    ∃ C > 0, ∀ σ t : ℝ, 1 / 2 + δ₀ + δ ≤ σ → 8 ≤ |t| →
      ‖ζ (σ + t * I)‖ ≤ C * |t| ^ η ∧ ‖ζ (σ + t * I)‖⁻¹ ≤ C * |t| ^ η := by
  set δ' := min (δ / 2) (1 / 2) with hδ'
  have hδ'0 : 0 < δ' := lt_min (by linarith) (by norm_num)
  have hδ'1 : δ' ≤ 1 / 2 := min_le_right _ _
  have hδ'2 : 2 * δ' ≤ δ := by have := min_le_left (δ / 2) (1 / 2); linarith
  obtain ⟨hθ0, hθ1⟩ := thetaD_mem hδ'0 hδ'1
  set θ := thetaD δ' with hθ
  set lam := η * δ' / 42 with hlam
  have hlam0 : 0 < lam := by positivity
  set K0 := lam ^ (-θ / (1 - θ)) with hK0
  set K := η * (Real.log 9 + 3) + 3 * K0 with hK
  set C := max 3 (Real.exp K * 2 ^ η) with hC
  refine ⟨C, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro σ t hσ ht
  have ht1 : 1 ≤ |t| := by linarith
  have htη : 1 ≤ |t| ^ η := Real.one_le_rpow ht1 hη.le
  by_cases hσ2 : 2 ≤ σ
  · have hre : 2 ≤ ((σ : ℂ) + t * I).re := by simpa using hσ2
    have h1 := zeta_norm_le_two hre
    have h2 := zeta_norm_ge_third hre
    have hC3 : 3 ≤ C := le_max_left _ _
    constructor
    · nlinarith
    · have : ‖ζ (σ + t * I)‖⁻¹ ≤ 3 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
      nlinarith
  push Not at hσ2
  have hσ' : 1 / 2 + δ₀ + 2 * δ' ≤ σ := by linarith
  obtain ⟨hA, hB⟩ := littlewood_aux hδ₀ hZ hδ'0 hδ'1 hσ' (by linarith) ht
  -- bound the exponent
  set u := Real.log (|t| + 4) with hu
  have hu0 : 0 ≤ u := Real.log_nonneg (by linarith [abs_nonneg t])
  have hlog9 : Real.log (9 * (|t| + 4)) = Real.log 9 + u :=
    Real.log_mul (by norm_num) (by linarith [abs_nonneg t])
  set b := (14 * Real.log (9 * (|t| + 4)) + 42) / δ' with hb
  have hb0 : 0 ≤ b := by
    rw [hb]; apply div_nonneg _ hδ'0.le
    have : 0 ≤ Real.log (9 * (|t| + 4)) := Real.log_nonneg (by linarith [abs_nonneg t])
    linarith
  have hbθ := rpow_le_mul_add hθ0 hθ1 hb0 hlam0
  have hlog9pos : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  have hexpo : 3 * b ^ θ ≤ η * u + K := by
    have e : 3 * (lam * b) = η * u + η * (Real.log 9 + 3) := by
      rw [hlam, hb, hlog9]; field_simp; ring
    rw [hK]
    linarith
  have hE : Real.exp (3 * b ^ θ) ≤ Real.exp K * 2 ^ η * |t| ^ η := by
    calc Real.exp (3 * b ^ θ) ≤ Real.exp (η * u + K) := Real.exp_le_exp.mpr hexpo
      _ = Real.exp K * (|t| + 4) ^ η := by
          rw [Real.exp_add, Real.rpow_def_of_pos (by linarith [abs_nonneg t]), hu]; ring_nf
      _ ≤ Real.exp K * (2 * |t|) ^ η := by
          gcongr; linarith
      _ = Real.exp K * 2 ^ η * |t| ^ η := by
          rw [Real.mul_rpow (by norm_num) (abs_nonneg t)]; ring
  have hCK : Real.exp K * 2 ^ η * |t| ^ η ≤ C * |t| ^ η := by
    gcongr; exact le_max_right _ _
  exact ⟨hA.trans (hE.trans hCK), hB.trans (hE.trans hCK)⟩

/-! ## 5. RH ⇒ Lindelöf -/


/-! ## 6. `1/ζ` on half-planes to the right of the zero-free region -/

/-- `1/ζ`, completed at `s = 1`: `(s − 1)/((s − 1)·zetaReg s + 1)` (`= (ζ s)⁻¹` for `s ≠ 1`, `= 0` at `1`). -/
def invZeta (s : ℂ) : ℂ := (s - 1) / ((s - 1) * FleetHeadContour.zetaReg s + 1)

lemma sub_one_mul_zeta {s : ℂ} (hs : s ≠ 1) :
    (s - 1) * FleetHeadContour.zetaReg s + 1 = (s - 1) * ζ s := by
  rw [FleetHeadContour.riemannZeta_eq_zetaReg hs]
  have : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field_simp

lemma invZeta_of_ne {s : ℂ} (hs : s ≠ 1) : invZeta s = (ζ s)⁻¹ := by
  rw [invZeta, sub_one_mul_zeta hs]
  have : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  by_cases hz : ζ s = 0
  · simp [hz]
  · field_simp

lemma invZeta_differentiableAt {s : ℂ} (hs : s = 1 ∨ ζ s ≠ 0) : DifferentiableAt ℂ invZeta s := by
  have hden : (s - 1) * FleetHeadContour.zetaReg s + 1 ≠ 0 := by
    rcases hs with h | h
    · simp [h]
    · by_cases h1 : s = 1
      · simp [h1]
      · rw [sub_one_mul_zeta h1]; exact mul_ne_zero (sub_ne_zero.mpr h1) h
  have hd : DifferentiableAt ℂ FleetHeadContour.zetaReg s :=
    FleetHeadContour.differentiable_zetaReg s
  exact (differentiableAt_id.sub_const 1).div
    (((differentiableAt_id.sub_const 1).mul hd).add_const 1) hden

lemma invZeta_eq_LSeries {s : ℂ} (hs : 1 < s.re) : invZeta s = LSeries (fun n ↦ (μ n : ℂ)) s := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
  rw [invZeta_of_ne hs1, ← LSeries_one_eq_riemannZeta hs]
  exact inv_eq_of_mul_eq_one_right (LSeries_one_mul_Lseries_moebius hs)

theorem invZeta_differentiableAt_of_zeroFree {δ₀ : ℝ}
    (hZ : ∀ s : ℂ, 1 / 2 + δ₀ < s.re → ζ s ≠ 0) {s : ℂ} (hs : 1 / 2 + δ₀ < s.re) :
    DifferentiableAt ℂ invZeta s :=
  invZeta_differentiableAt (Or.inr (hZ s hs))

/-- If `ζ ≠ 0` on `Re s > 1/2 + δ₀` (`δ₀ ≥ 0`), then for `σ₀ > 1/2 + δ₀` and `η > 0`:
`‖1/ζ(s)‖ ≤ C (1 + |Im s|)^η` on `Re s ≥ σ₀`. -/
theorem invZeta_bound {δ₀ : ℝ} (hδ₀ : 0 ≤ δ₀) (hZ : ∀ s : ℂ, 1 / 2 + δ₀ < s.re → ζ s ≠ 0)
    {σ₀ : ℝ} (hσ₀ : 1 / 2 + δ₀ < σ₀) {η : ℝ}
    (hη : 0 < η) : ∃ C > 0, ∀ s : ℂ, σ₀ ≤ s.re → ‖invZeta s‖ ≤ C * (1 + |s.im|) ^ η := by
  obtain ⟨C₁, hC₁, hL⟩ := littlewood_bound hδ₀ hZ (δ := σ₀ - (1 / 2 + δ₀)) (by linarith) hη
  have hK : IsCompact ((Icc σ₀ 2) ×ℂ (Icc (-8) 8)) := isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn invZeta ((Icc σ₀ 2) ×ℂ (Icc (-8) 8)) := by
    intro z hz
    rw [mem_reProdIm] at hz
    exact (invZeta_differentiableAt_of_zeroFree hZ
      (by linarith [hz.1.1])).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max (max C₁ M) 3, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro s hs
  have h1 : 1 ≤ (1 + |s.im|) ^ η := Real.one_le_rpow (by linarith [abs_nonneg s.im]) hη.le
  have hCpos : 0 ≤ max (max C₁ M) 3 := le_trans (by norm_num) (le_max_right _ _)
  by_cases h2 : 2 ≤ s.re
  · have hs1 : s ≠ 1 := by intro h; rw [h] at h2; norm_num at h2
    rw [invZeta_of_ne hs1]
    have h3 := zeta_norm_ge_third h2
    have : ‖(ζ s)⁻¹‖ ≤ 3 := by
      rw [norm_inv, inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    calc ‖(ζ s)⁻¹‖ ≤ 3 := this
      _ ≤ max (max C₁ M) 3 := le_max_right _ _
      _ ≤ _ := le_mul_of_one_le_right hCpos h1
  push Not at h2
  by_cases h8 : |s.im| ≤ 8
  · have := hM s (by rw [mem_reProdIm]; exact ⟨⟨hs, h2.le⟩, abs_le.mp h8⟩)
    calc ‖invZeta s‖ ≤ M := this
      _ ≤ max (max C₁ M) 3 := le_trans (le_max_right _ _) (le_max_left _ _)
      _ ≤ _ := le_mul_of_one_le_right hCpos h1
  push Not at h8
  have hs1 : s ≠ 1 := by intro h; rw [h] at h8; norm_num at h8
  rw [invZeta_of_ne hs1, norm_inv]
  have e : s = (s.re : ℂ) + (s.im : ℂ) * I := (re_add_im s).symm
  have := (hL s.re s.im (by linarith) h8.le).2
  rw [← e] at this
  calc ‖ζ s‖⁻¹ ≤ C₁ * |s.im| ^ η := this
    _ ≤ max (max C₁ M) 3 * (1 + |s.im|) ^ η := by
        gcongr
        · exact le_trans (le_max_left _ _) (le_max_left _ _)
        · linarith

end FleetLandauTransfer
