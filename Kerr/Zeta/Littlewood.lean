import Kerr.Zeta.ClassicalResults
import Kerr.PNT.MobiusPNT

/-!
# Littlewood: RH ⇒ Lindelöf, RH ⇒ `M(x), L(x) = O(x^{1/2+ε})`

New file (written for this repo, not copied). Proves the targets of `Kerr.Zeta.ClassicalResults`
* `RH_implies_Lindelof_statement` (`RH_implies_Lindelof`, `RH_implies_Lindelof_statement_proved`),
* `RH_implies_Mertens_growth_statement` (`RH_implies_Mertens_growth`),
* `RH_implies_Liouville_growth_statement` (`RH_implies_Liouville_growth`),
and hence the unconditional equivalences `RH_iff_Mertens_Growth'`, `RH_iff_Liouville_Growth'`
(the versions in `ClassicalResults` take the hard direction as a hypothesis).

Not proved here: `Mertens_bound_under_RH_statement` (`|M(x)| ≤ C √x log x`) and
`Liouville_bound_under_RH_statement` (`|L(x)| ≤ C √x (log x)^{5/4+ε}`). Both are marked in
`ClassicalResults` as open problems; no proof of either from RH is known.

## Plan (route from the task statement; the specific radii, centres and kernels are my choices)

1. **Three circles** (`three_circles`): from Mathlib's Hadamard three-lines theorem
   (`Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'`) applied to
   `w ↦ f (c + exp w)` on the strip `log r₁ ≤ Re w ≤ log r₃`.
2. **Elementary bounds for ζ** (`zeta_sub_one_norm_le`, …, `zeta_norm_le_poly`): for `Re s ≥ 2`,
   `‖ζ s − 1‖ ≤ π²/6 − 1 < 2/3`, hence `|log ζ s| ≤ 3`; for `Re s ≥ 1/4`, `|Im s| ≥ 2`,
   `‖ζ s‖ ≤ 9 |Im s|` (from the copied PrimeNumberTheoremAnd representation `ζ = ζ₀ 1`,
   `ZetaBnd_aux1`).
3. **Logarithm on a disc** (`exists_log_ball`): a primitive of `ζ'/ζ` (Mathlib's
   `DifferentiableOn.isExactOn_ball`), normalised at the centre; it is the principal logarithm
   where `Re ζ > 0` (`log_ball_eq_log`).
4. **Littlewood's bound** (`littlewood_aux`, `littlewood_bound`): under RH, `ζ` has no zeros in
   the disc `|s − (4+it)| < 7/2 − δ/2` (`|t| ≥ 8`). Borel–Carathéodory (Mathlib's
   `Complex.borelCaratheodory`) with `log|ζ| ≤ log(9(|t|+4))` bounds `|log ζ|` by
   `(14 log(9(|t|+4)) + 42)/δ` on radius `7/2 − δ`; three circles with radii `1`, `4 − σ`,
   `7/2 − δ` gives `|log ζ(σ+it)| ≤ 3 b^θ` with `θ = thetaD δ < 1`, i.e. `o(log |t|)`. Hence
   `‖ζ(σ+it)‖, ‖ζ(σ+it)‖⁻¹ ≤ C |t|^η` for `σ ≥ 1/2 + δ`, `|t| ≥ 8`, every `η > 0`.
5. **Lindelöf** (`RH_implies_Lindelof`): three circles for `ζ` itself around `3/2 + it`, radii
   `1 − δ₀` (inside `Re s ≥ 1/2 + δ₀`), `1` (the point `1/2 + it`), `5/4` (crude bound); the
   exponent is `≤ ε/2` for `δ₀` small. Small `|t|` by compactness.
6. **`1/ζ` bound** (`invZeta_bound_RH`): `‖1/ζ(s)‖ ≤ C (1 + |Im s|)^η` on `Re s ≥ σ₀ > 1/2`
   (step 4 for `|t| ≥ 8`, compactness on `[σ₀, 2] × [−8, 8]`, step 2 for `Re s ≥ 2`).
7. **Perron and contour shift, for general coefficients** (`perron_general`, adapted from
   `KerrPNT.Mobius.perron_moebius`; `vertical_shift`, using the copied PrimeNumberTheoremAnd
   `verticalIntegral_eq_verticalIntegral`): `S(x) = ∑_{n ≤ x} a(n)(x − n)` satisfies
   `2πi S(x) = x ∫_{(2)} x^s G(s)/(s(s+1)) ds = x ∫_{(σ₀)} …`.
8. **Differences** (`kernel_bound`, `Ssum_diff_bound`): on `Re s = σ₀`,
   `‖(y^{s+1} − x^{s+1})/(s(s+1))‖ ≤ min(16 y^{σ+1}(1+|t|)^{−2}, 16 y^σ (y−x)(1+|t|)^{−1})
   ≤ 16 y^{σ+θ}(y−x)^{1−θ}(1+|t|)^{−1−θ}`; with `‖G‖ ≤ C(1+|t|)^{θ/2}` the integral converges and
   `‖S(y) − S(x)‖ ≤ 16 C I_θ y^{σ₀+θ}(y−x)^{1−θ}`.
9. **Unsmoothing** (`Ssum_diff`, `partial_sum_bound`): `h ∑_{n≤N} a(n) = S(N+½+h) − S(N+½) + O(h²)`
   with `h = ⌈√x⌉` gives `‖∑_{n ≤ x} a(n)‖ ≤ K x^{σ₀+θ}`.
10. **Mertens** (`a = μ`, `G = 1/ζ`) and **Liouville** (`a = λ`, `G(s) = ζ(2s)/ζ(s)`, from
    `Kerr.File14RHExtra.liouville_mul_zeta`) with `σ₀ = 1/2 + ε'/2`, `θ = ε'/2`, `ε' = min ε ½`.
-/

noncomputable section
open Complex Metric Set Filter Topology
open scoped ArithmeticFunction.Moebius

namespace Kerr.Littlewood

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

/-- Crude bound in the strip: `‖ζ(σ+it)‖ ≤ 2 + 2|t|/σ` for `0 < σ ≤ 2`, `|t| ≥ 2`. -/
lemma zeta_norm_le_strip {σ t : ℝ} (hσ : σ ∈ Ioc 0 2) (ht : 2 ≤ |t|) :
    ‖ζ (σ + t * I)‖ ≤ 2 + 2 * |t| / σ := by
  set s : ℂ := σ + t * I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hsim : s.im = t := by simp [hsdef]
  have ht0 : t ≠ 0 := by intro h; rw [h] at ht; simp at ht; linarith
  have hs0 : s ≠ 0 := by
    intro h; have := congrArg Complex.im h; rw [hsim] at this; exact ht0 (by simpa using this)
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.im h; rw [hsim] at this; exact ht0 (by simpa using this)
  rw [← Zeta0EqZeta (N := 1) one_pos (by rw [hsre]; exact hσ.1) hs1, riemannZeta0]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
    zero_add, one_cpow, div_one]
  rw [zero_cpow hs0, div_zero, zero_add]
  have hint := ZetaBnd_aux1 1 le_rfl hσ ht
  simp only [Nat.cast_one, Real.one_rpow, mul_one] at hint
  have h1s : ‖(-1 : ℂ) / (1 - s)‖ ≤ 1 / 2 := by
    rw [norm_div, norm_neg, norm_one]
    have : |t| ≤ ‖1 - s‖ := by
      have := abs_im_le_norm (1 - s); simpa [hsim] using this
    rw [div_le_iff₀ (by linarith)]; linarith
  have h2 : ‖(-1 : ℂ) / 2‖ = 1 / 2 := by simp
  calc ‖1 + -1 / (1 - s) + -1 / 2 + s * ∫ x in Ioi (1 : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
      ≤ ‖(1 : ℂ)‖ + ‖-1 / (1 - s)‖ + ‖(-1 : ℂ) / 2‖ +
          ‖s * ∫ x in Ioi (1 : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ 1 + 1 / 2 + 1 / 2 + 2 * |t| / σ := by
        rw [norm_one, h2]; gcongr
    _ = 2 + 2 * |t| / σ := by ring

/-- Crude polynomial bound: `‖ζ(s)‖ ≤ 9 |Im s|` for `Re s ≥ 1/4`, `|Im s| ≥ 2`. -/
lemma zeta_norm_le_poly {s : ℂ} (hs : 1 / 4 ≤ s.re) (ht : 2 ≤ |s.im|) : ‖ζ s‖ ≤ 9 * |s.im| := by
  by_cases h2 : 2 ≤ s.re
  · have := zeta_norm_le_two h2; linarith
  · push Not at h2
    have e : s = (s.re : ℂ) + (s.im : ℂ) * I := (re_add_im s).symm
    have hb := zeta_norm_le_strip (σ := s.re) (t := s.im) ⟨by linarith, h2.le⟩ ht
    rw [← e] at hb
    have : 2 * |s.im| / s.re ≤ 8 * |s.im| := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [abs_nonneg s.im]
    linarith

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

open Kerr.File14RH

theorem zeta_ne_zero_of_RH (hRH : RiemannHypothesis') {s : ℂ} (hs : 1 / 2 < s.re) :
    ζ s ≠ 0 := by
  intro h
  by_cases h1 : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h1 h
  · push Not at h1
    have := hRH s ⟨h, by linarith, h1⟩
    unfold IsOnCriticalLine at this
    linarith

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

/-- The three-circles exponent used below: circles of radii `1 < 4 - σ ≤ 7/2 - 2δ < 7/2 - δ`
around `4 + it`. -/
def thetaD (δ : ℝ) : ℝ := Real.log (7 / 2 - 2 * δ) / Real.log (7 / 2 - δ)

lemma thetaD_mem {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) : 0 ≤ thetaD δ ∧ thetaD δ < 1 := by
  have h1 : 0 < Real.log (7 / 2 - 2 * δ) := Real.log_pos (by linarith)
  have h2 : Real.log (7 / 2 - 2 * δ) < Real.log (7 / 2 - δ) :=
    Real.log_lt_log (by linarith) (by linarith)
  exact ⟨div_nonneg h1.le (h1.trans h2).le, (div_lt_one (h1.trans h2)).mpr h2⟩

/-- **Littlewood's bound, explicit form.** Under RH, for `1/2 + 2δ ≤ σ ≤ 3` and `|t| ≥ 8`,
both `‖ζ(σ+it)‖` and `‖ζ(σ+it)‖⁻¹` are at most `exp (3 b^θ)`, `b = (14 log(9(|t|+4)) + 42)/δ`,
`θ = thetaD δ < 1`. Proof: a holomorphic `log ζ` on the disc `|s − (4+it)| < 7/2 − δ/2`
(zero-free by RH), Borel–Carathéodory on that disc (with `log|ζ| ≤ log(9(|t|+4))`), and the
three-circles theorem with radii `1`, `4 − σ`, `7/2 − δ` (on the radius-`1` circle `|log ζ| ≤ 3`). -/
theorem littlewood_aux (hRH : RiemannHypothesis') {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    {σ t : ℝ} (hσ1 : 1 / 2 + 2 * δ ≤ σ) (hσ2 : σ ≤ 3) (ht : 8 ≤ |t|) :
    ‖ζ (σ + t * I)‖ ≤ Real.exp (3 * ((14 * Real.log (9 * (|t| + 4)) + 42) / δ) ^ thetaD δ) ∧
    ‖ζ (σ + t * I)‖⁻¹ ≤ Real.exp (3 * ((14 * Real.log (9 * (|t| + 4)) + 42) / δ) ^ thetaD δ) := by
  set c : ℂ := 4 + t * I with hc
  set R : ℝ := 7 / 2 - δ / 2 with hR
  set r₃ : ℝ := 7 / 2 - δ with hr₃
  have hRpos : 0 < R := by linarith
  have hball : ∀ z ∈ ball c R, 1 / 2 + δ / 2 < z.re ∧ |t| - 4 ≤ |z.im| ∧ |z.im| ≤ |t| + 4 := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have h1 := abs_re_le_norm (z - c)
    have h2 := abs_im_le_norm (z - c)
    have e1 : (z - c).re = z.re - 4 := by simp [hc]
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
    fun z hz => zeta_ne_zero_of_RH hRH (by linarith [(hball z hz).1])
  obtain ⟨L, hLd, hLexp, hLc⟩ := exists_log_ball hd hnz hRpos
  have hsub2 : ball c 2 ⊆ ball c R := ball_subset_ball (by linarith)
  have hre2 : ∀ z ∈ ball c 2, 2 < z.re := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have h1 := abs_re_le_norm (z - c)
    have e1 : (z - c).re = z.re - 4 := by simp [hc]
    rw [e1] at h1
    linarith [(abs_lt.mp (h1.trans_lt hz)).1]
  have hLlog : ∀ z ∈ ball c 2, L z = Complex.log (ζ z) :=
    log_ball_eq_log two_pos (fun z hz => hd z (hsub2 hz)) (fun z hz => hLd z (hsub2 hz)) hLc
      (fun z hz => zeta_re_pos (hre2 z hz).le)
  have hcre : c.re = 4 := by simp [hc]
  have hLc3 : ‖L c‖ ≤ 3 := by rw [hLc]; exact log_zeta_norm_le (by rw [hcre]; norm_num)
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
  have hzc : ‖((σ : ℂ) + t * I) - c‖ = 4 - σ := by
    have : ((σ : ℂ) + t * I) - c = ((σ - 4 : ℝ) : ℂ) := by rw [hc]; push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have key := three_circles one_pos (by linarith : (1 : ℝ) < r₃) hf3 ha hBC
    (by rw [hzc]; linarith) (by rw [hzc]; linarith)
  rw [hzc, div_one, div_one] at key
  obtain ⟨hθ0, hθ1⟩ := thetaD_mem hδ hδ1
  set θ := Real.log (4 - σ) / Real.log r₃ with hθ
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

/-- **Littlewood (RH ⇒ `ζ(s)`, `1/ζ(s)` are `O(|t|^η)` on `Re s ≥ 1/2 + δ`).** Under RH, for every
`δ > 0` and `η > 0` there is `C` with `‖ζ(σ+it)‖ ≤ C|t|^η` and `‖ζ(σ+it)‖⁻¹ ≤ C|t|^η` for all
`σ ≥ 1/2 + δ`, `|t| ≥ 8`. -/
theorem littlewood_bound (hRH : RiemannHypothesis') {δ : ℝ} (hδ : 0 < δ) {η : ℝ} (hη : 0 < η) :
    ∃ C > 0, ∀ σ t : ℝ, 1 / 2 + δ ≤ σ → 8 ≤ |t| →
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
  have hσ' : 1 / 2 + 2 * δ' ≤ σ := by linarith
  obtain ⟨hA, hB⟩ := littlewood_aux hRH hδ'0 hδ'1 hσ' (by linarith) ht
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

/-- **RH ⇒ Lindelöf** (Littlewood), for the corrected `LindelofHypothesis'` (`|t| ≥ 1`).
Three circles for `ζ` itself around `3/2 + it` with radii `1 − δ₀` (inside `Re s ≥ 1/2 + δ₀`, where
`littlewood_bound` gives `O(|t|^{ε/2})`), `1` (the point `1/2 + it`) and `5/4` (crude bound
`‖ζ‖ ≤ 9|Im s|`); the exponent `log(1/(1−δ₀))/log(5/(4(1−δ₀)))` is `≤ ε/2` for small `δ₀`. -/
theorem RH_implies_Lindelof (hRH : RiemannHypothesis') : Kerr.File14RHExtra.LindelofHypothesis' := by
  intro ε hε
  have hl54 : 0 < Real.log (5 / 4) := Real.log_pos (by norm_num)
  set δ₀ := min (1 / 2) (ε * Real.log (5 / 4) / 4) with hδ₀
  have hδ₀0 : 0 < δ₀ := lt_min (by norm_num) (by positivity)
  have hδ₀1 : δ₀ ≤ 1 / 2 := min_le_left _ _
  have hδ₀2 : δ₀ ≤ ε * Real.log (5 / 4) / 4 := min_le_right _ _
  obtain ⟨C₁, hC₁, hL⟩ := littlewood_bound hRH hδ₀0 (η := ε / 2) (by positivity)
  set r₁ := 1 - δ₀ with hr₁
  have hr₁0 : 0 < r₁ := by linarith
  have hr₁1 : r₁ < 1 := by linarith
  set θ := Real.log (1 / r₁) / Real.log (5 / 4 / r₁) with hθ
  have hden : Real.log (5 / 4) ≤ Real.log (5 / 4 / r₁) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hr₁0]; nlinarith)
  have hnum0 : 0 ≤ Real.log (1 / r₁) := Real.log_nonneg (by rw [le_div_iff₀ hr₁0]; linarith)
  have hθ0 : 0 ≤ θ := div_nonneg hnum0 (hl54.le.trans hden)
  have hθε : θ ≤ ε / 2 := by
    have hnum : Real.log (1 / r₁) ≤ 2 * δ₀ := by
      have := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 / r₁)
      have e : 1 / r₁ - 1 = δ₀ / r₁ := by
        rw [div_sub_one hr₁0.ne']; congr 1; rw [hr₁]; ring
      rw [e] at this
      have : δ₀ / r₁ ≤ 2 * δ₀ := by rw [div_le_iff₀ hr₁0]; nlinarith
      linarith
    calc θ ≤ Real.log (1 / r₁) / Real.log (5 / 4) :=
          div_le_div_of_nonneg_left hnum0 hl54 hden
      _ ≤ 2 * δ₀ / Real.log (5 / 4) := div_le_div_of_nonneg_right hnum hl54.le
      _ ≤ ε / 2 := by rw [div_le_iff₀ hl54]; linarith
  -- small `|t|`: compactness
  have hcont : Continuous (fun t : ℝ => riemannZeta (1 / 2 + t * I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hne : (1 / 2 : ℂ) + t * I ≠ 1 := by
      intro h; have := congrArg Complex.re h; norm_num at this
    have hl : ContinuousAt (fun t : ℝ => (1 / 2 : ℂ) + t * I) t := by fun_prop
    exact ContinuousAt.comp (g := riemannZeta) (differentiableAt_riemannZeta hne).continuousAt hl
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := (-16 : ℝ)) (b := 16)).exists_bound_of_continuousOn
    hcont.continuousOn
  set C₂ := max 1 C₁ with hC₂
  set C' := C₂ * 2 ^ (ε / 2) * 18 with hC'
  refine ⟨max (max M₀ C') 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro t ht
  have htε : 1 ≤ |t| ^ ε := Real.one_le_rpow ht hε.le
  by_cases hsmall : |t| ≤ 16
  · have := hM₀ t ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
    calc ‖riemannZeta (1 / 2 + t * I)‖ ≤ M₀ := this
      _ ≤ max (max M₀ C') 1 := le_trans (le_max_left _ _) (le_max_left _ _)
      _ ≤ max (max M₀ C') 1 * |t| ^ ε := le_mul_of_one_le_right (by positivity) htε
  push Not at hsmall
  set c : ℂ := 3 / 2 + t * I with hc
  have hre : ∀ z : ℂ, |z.re - 3 / 2| ≤ ‖z - c‖ := by
    intro z; have := abs_re_le_norm (z - c); simpa [hc] using this
  have him : ∀ z : ℂ, |z.im - t| ≤ ‖z - c‖ := by
    intro z; have := abs_im_le_norm (z - c); simpa [hc] using this
  have himb : ∀ z : ℂ, ‖z - c‖ ≤ 5 / 4 → |t| - 5 / 4 ≤ |z.im| ∧ |z.im| ≤ 2 * |t| := by
    intro z hz
    have h1 := (him z).trans hz
    have a2 := abs_sub_abs_le_abs_sub z.im t
    have a3 := abs_sub_abs_le_abs_sub t z.im
    rw [abs_sub_comm] at a3
    constructor <;> linarith
  have hf : ∀ z ∈ closedBall c (5 / 4), DifferentiableAt ℂ riemannZeta z := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    apply differentiableAt_riemannZeta
    intro h
    have := (himb z hz).1
    rw [h] at this; simp at this; linarith
  set a := C₂ * 2 ^ (ε / 2) * |t| ^ (ε / 2) with ha
  have ha1 : ∀ z : ℂ, ‖z - c‖ = r₁ → ‖riemannZeta z‖ ≤ a := by
    intro z hz
    have hzb := himb z (by rw [hz]; linarith)
    have hzre : 1 / 2 + δ₀ ≤ z.re := by
      have := hre z; rw [hz] at this; linarith [(abs_le.mp this).1]
    have e : z = (z.re : ℂ) + (z.im : ℂ) * I := (re_add_im z).symm
    have := (hL z.re z.im hzre (by linarith)).1
    rw [← e] at this
    refine this.trans ?_
    rw [ha, mul_assoc C₂, ← Real.mul_rpow (by norm_num) (abs_nonneg t)]
    gcongr
    · exact le_max_right _ _
    · exact hzb.2
  have hb1 : ∀ z : ℂ, ‖z - c‖ = 5 / 4 → ‖riemannZeta z‖ ≤ 18 * |t| := by
    intro z hz
    have hzb := himb z hz.le
    have hzre : 1 / 4 ≤ z.re := by
      have := hre z; rw [hz] at this; linarith [(abs_le.mp this).1]
    have := zeta_norm_le_poly hzre (by linarith)
    linarith
  have hzc : ‖(1 / 2 + t * I : ℂ) - c‖ = 1 := by
    rw [hc]; ring_nf; simp
  have key := three_circles hr₁0 (by linarith : r₁ < 5 / 4) hf ha1 hb1
    (by rw [hzc]; linarith) (by rw [hzc]; norm_num)
  rw [hzc, ← hθ] at key
  have ha_ge : 1 ≤ a := by
    rw [ha]
    have h1 : 1 ≤ C₂ := le_max_left _ _
    have h2 : 1 ≤ (2 : ℝ) ^ (ε / 2) := Real.one_le_rpow (by norm_num) (by positivity)
    have h3 : 1 ≤ |t| ^ (ε / 2) := Real.one_le_rpow ht (by positivity)
    have h4 : 1 ≤ C₂ * 2 ^ (ε / 2) := by nlinarith
    nlinarith
  have hθ1 : θ ≤ 1 := by
    rw [hθ]
    apply div_le_one_of_le₀ _ (hl54.le.trans hden)
    exact Real.log_le_log (by positivity) (by gcongr; norm_num)
  have hpart1 : a ^ (1 - θ) ≤ a := by
    calc a ^ (1 - θ) ≤ a ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le ha_ge (by linarith)
      _ = a := Real.rpow_one a
  have hpart2 : (18 * |t|) ^ θ ≤ 18 * |t| ^ θ := by
    rw [Real.mul_rpow (by norm_num) (abs_nonneg t)]
    gcongr
    calc (18 : ℝ) ^ θ ≤ 18 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ1
      _ = 18 := Real.rpow_one 18
  have hfinal : a ^ (1 - θ) * (18 * |t|) ^ θ ≤ C' * |t| ^ ε := by
    calc a ^ (1 - θ) * (18 * |t|) ^ θ ≤ a * (18 * |t| ^ θ) :=
          mul_le_mul hpart1 hpart2 (Real.rpow_nonneg (by positivity) _) (by linarith)
      _ = C' * (|t| ^ (ε / 2) * |t| ^ θ) := by rw [ha, hC']; ring
      _ = C' * |t| ^ (ε / 2 + θ) := by rw [Real.rpow_add (by linarith)]
      _ ≤ C' * |t| ^ ε := by
          have hC'0 : 0 ≤ C' := by
            rw [hC']; have : 0 ≤ C₂ := le_trans zero_le_one (le_max_left _ _); positivity
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht (by linarith)) hC'0
  calc ‖riemannZeta (1 / 2 + t * I)‖ ≤ C' * |t| ^ ε := key.trans hfinal
    _ ≤ max (max M₀ C') 1 * |t| ^ ε := by
        gcongr; exact le_trans (le_max_right _ _) (le_max_left _ _)

/-- The target `RH_implies_Lindelof_statement` of `Kerr.Zeta.ClassicalResults`, proved. -/
theorem RH_implies_Lindelof_statement_proved : Kerr.File14RHExtra.RH_implies_Lindelof_statement :=
  RH_implies_Lindelof

/-! ## 6. `1/ζ` on half-planes `Re s ≥ σ₀ > 1/2` under RH -/

open KerrPNT.Mobius in
theorem invZeta_differentiableAt_RH (hRH : RiemannHypothesis') {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ invZeta s := by
  by_cases h : s = 1
  · subst h; exact invZeta_differentiableAt_one
  · exact invZeta_differentiableAt_of_ne h (zeta_ne_zero_of_RH hRH hs)

open KerrPNT.Mobius in
/-- Under RH, for `σ₀ > 1/2` and `η > 0`: `‖1/ζ(s)‖ ≤ C (1 + |Im s|)^η` on `Re s ≥ σ₀`. -/
theorem invZeta_bound_RH (hRH : RiemannHypothesis') {σ₀ : ℝ} (hσ₀ : 1 / 2 < σ₀) {η : ℝ}
    (hη : 0 < η) : ∃ C > 0, ∀ s : ℂ, σ₀ ≤ s.re → ‖invZeta s‖ ≤ C * (1 + |s.im|) ^ η := by
  obtain ⟨C₁, hC₁, hL⟩ := littlewood_bound hRH (δ := σ₀ - 1 / 2) (by linarith) hη
  have hK : IsCompact ((Icc σ₀ 2) ×ℂ (Icc (-8) 8)) := isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn invZeta ((Icc σ₀ 2) ×ℂ (Icc (-8) 8)) := by
    intro z hz
    rw [mem_reProdIm] at hz
    exact (invZeta_differentiableAt_RH hRH (by linarith [hz.1.1])).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max (max C₁ M) 3, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro s hs
  have h1 : 1 ≤ (1 + |s.im|) ^ η := Real.one_le_rpow (by linarith [abs_nonneg s.im]) hη.le
  have hCpos : 0 ≤ max (max C₁ M) 3 := le_trans (by norm_num) (le_max_right _ _)
  by_cases h2 : 2 ≤ s.re
  · have hs1 : s ≠ 1 := by intro h; rw [h] at h2; norm_num at h2
    rw [invZeta_of_ne hs1, norm_inv]
    have h3 := zeta_norm_ge_third h2
    have : ‖ζ s‖⁻¹ ≤ 3 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    calc ‖ζ s‖⁻¹ ≤ 3 := this
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

/-! ## 7. Perron's formula and the contour shift, for general coefficients -/

open KerrPNT.Mobius MeasureTheory in
/-- **Smoothed Perron identity**, for any coefficients `a` with `a 0 = 0`, `‖a n‖ ≤ 1`, and any
`G` equal to the `L`-series of `a` on `Re s > 1` (adapted from `KerrPNT.Mobius.perron_moebius`). -/
theorem perron_general {a : ℕ → ℂ} (ha0 : a 0 = 0) (ha : ∀ n, ‖a n‖ ≤ 1) {G : ℂ → ℂ}
    (hG : ∀ s : ℂ, 1 < s.re → G s = LSeries a s)
    {x b : ℝ} (hx : 0 < x) (hxn : ∀ n : ℕ, (n : ℝ) ≠ x) (hb : 1 < b) :
    VerticalIntegral (fun s ↦ Perron.f x s * G s) b =
      2 * Real.pi * I * ∑ n ∈ Finset.Iic ⌊x⌋₊, a n * (1 - n / x) := by
  set g : ℕ → ℝ → ℂ := fun n t ↦
    if n = 0 then 0 else a n * Perron.f (x / n) (b + t * I) with hg
  have hb0 : (b : ℝ) ≠ 0 := by linarith
  have hbm : (b : ℝ) ≠ -1 := by linarith
  -- pointwise expansion
  have hpt : ∀ t : ℝ, Perron.f x (b + t * I) * G (b + t * I) = ∑' n, g n t := by
    intro t
    have hre : 1 < ((b : ℂ) + t * I).re := by simpa using hb
    rw [hG _ hre, LSeries, ← tsum_mul_left]
    congr 1; funext n
    rw [LSeries.term_def]
    by_cases hn : n = 0
    · simp [hg, hn]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      simp only [hg, hn, ite_false]
      rw [← Perron.f_mul_eq_f hx hnpos, div_eq_mul_inv, ← cpow_neg]
      push_cast
      ring
  -- integrability of each term
  have hint : ∀ n, Integrable (g n) := by
    intro n
    by_cases hn : n = 0
    · simp [hg, hn]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      simp only [hg, hn, ite_false]
      exact (Perron.isIntegrable (div_pos hx hnpos) hb0 hbm).const_mul _
  set K : ℝ := ∫ t : ℝ, ‖Perron.f 1 (b + t * I)‖ with hK
  have hK1 : Integrable (fun t : ℝ ↦ ‖Perron.f 1 (b + t * I)‖) :=
    (Perron.isIntegrable one_pos hb0 hbm).norm
  have hbound : ∀ n, ∫ t, ‖g n t‖ ≤ x ^ b * K * (n : ℝ) ^ (-b) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp [hg, Real.zero_rpow (by linarith : -b ≠ 0)]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have e : ∀ t : ℝ, ‖g n t‖ ≤ x ^ b * (n : ℝ) ^ (-b) * ‖Perron.f 1 (b + t * I)‖ := by
        intro t
        simp only [hg, hn, ite_false, norm_mul]
        rw [norm_perron_f (div_pos hx hnpos)]
        have hμ : ‖a n‖ ≤ 1 := ha n
        have hre : ((b : ℂ) + t * I).re = b := by simp
        rw [hre, Real.div_rpow hx.le hnpos.le, div_eq_mul_inv, ← Real.rpow_neg hnpos.le]
        calc ‖a n‖ * (x ^ b * (n : ℝ) ^ (-b) * ‖Perron.f 1 (b + t * I)‖)
            ≤ 1 * (x ^ b * (n : ℝ) ^ (-b) * ‖Perron.f 1 (b + t * I)‖) := by gcongr
          _ = _ := one_mul _
      calc ∫ t, ‖g n t‖ ≤ ∫ t : ℝ, x ^ b * (n : ℝ) ^ (-b) * ‖Perron.f 1 (b + t * I)‖ :=
            integral_mono (hint n).norm (hK1.const_mul _) e
        _ = x ^ b * K * (n : ℝ) ^ (-b) := by rw [integral_const_mul]; ring
  have hsum : Summable fun n ↦ ∫ t, ‖g n t‖ := by
    refine Summable.of_nonneg_of_le (fun n ↦ integral_nonneg fun _ ↦ norm_nonneg _) hbound ?_
    exact (Real.summable_nat_rpow.mpr (by linarith)).mul_left _
  -- swap
  have hswap := integral_tsum_of_summable_integral_norm hint hsum
  have hterm : ∀ n, I * ∫ t, g n t =
      2 * Real.pi * I * (a n * (if (n : ℝ) ≤ x ∧ n ≠ 0 then (1 - (n : ℂ) / x) else 0)) := by
    intro n
    by_cases hn : n = 0
    · simp [hg, hn]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      simp only [hg, hn, ite_false, integral_const_mul]
      have hy : 0 < x / n := div_pos hx hnpos
      have hy1 : x / n ≠ 1 := by
        intro h; rw [div_eq_one_iff_eq hnpos.ne'] at h; exact hxn n h.symm
      have hv := vertInt_perron hy hy1 (by linarith : (0 : ℝ) < b)
      simp only [VerticalIntegral, smul_eq_mul] at hv
      have hiff : 1 < x / n ↔ (n : ℝ) ≤ x ∧ n ≠ 0 := by
        rw [one_lt_div hnpos]
        constructor
        · intro h; exact ⟨h.le, hn⟩
        · rintro ⟨h, -⟩; exact lt_of_le_of_ne h (hxn n)
      calc I * (a n * ∫ t : ℝ, Perron.f (x / n) (b + t * I))
          = a n * (I * ∫ t : ℝ, Perron.f (x / n) (b + t * I)) := by ring
        _ = _ := by
          rw [hv]
          by_cases h : 1 < x / n
          · have h' := hiff.mp h
            rw [ite_eq_left h, ite_eq_left h']
            have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
            have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
            have : (1 : ℂ) - 1 / ((x / n : ℝ) : ℂ) = 1 - n / x := by
              push_cast; field_simp
            rw [this]; ring
          · have h' : ¬ ((n : ℝ) ≤ x ∧ n ≠ 0) := fun hh ↦ h (hiff.mpr hh)
            rw [ite_eq_right h, ite_eq_right h']; ring
  calc VerticalIntegral (fun s ↦ Perron.f x s * G s) b
      = I * ∫ t : ℝ, ∑' n, g n t := by
        simp only [VerticalIntegral, smul_eq_mul]; congr 1; exact integral_congr_ae
          (Eventually.of_forall hpt)
    _ = ∑' n, I * ∫ t, g n t := by rw [← hswap, tsum_mul_left]
    _ = ∑' n, 2 * Real.pi * I * (a n * (if (n : ℝ) ≤ x ∧ n ≠ 0 then (1 - (n : ℂ) / x) else 0)) := by
        congr 1; funext n; exact hterm n
    _ = ∑ n ∈ Finset.Iic ⌊x⌋₊,
          2 * Real.pi * I * (a n * (if (n : ℝ) ≤ x ∧ n ≠ 0 then (1 - (n : ℂ) / x) else 0)) := by
        apply tsum_eq_sum
        intro n hn
        rw [Finset.mem_Iic, Nat.le_floor_iff hx.le] at hn
        rw [ite_eq_right (fun h ↦ hn h.1)]; ring
    _ = 2 * Real.pi * I * ∑ n ∈ Finset.Iic ⌊x⌋₊, a n * (1 - n / x) := by
        rw [← Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.mem_Iic, Nat.le_floor_iff hx.le] at hn
        by_cases h0 : n = 0
        · subst h0; simp [ha0]
        · rw [ite_eq_left ⟨hn, h0⟩]


lemma one_add_abs_im_le_norm {s : ℂ} (hs : 1 / 2 ≤ s.re) : (1 + |s.im|) / 4 ≤ ‖s‖ := by
  have h1 := re_le_norm s
  have h2 := abs_im_le_norm s
  linarith [abs_nonneg s.im]

lemma one_add_abs_im_le_norm_add_one {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    (1 + |s.im|) / 2 ≤ ‖s + 1‖ := by
  have h1 := re_le_norm (s + 1)
  have h2 := abs_im_le_norm (s + 1)
  simp only [add_re, one_re, add_im, one_im, add_zero] at h1 h2
  linarith [abs_nonneg s.im]

/-- `‖x^s/(s(s+1))‖ ≤ 8 x^σ (1+|t|)^{-2}` for `σ ≥ 1/2`. -/
lemma norm_perron_f_le {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖Perron.f x s‖ ≤ 8 * x ^ s.re * (1 + |s.im|) ^ (-2 : ℝ) := by
  have h1 := one_add_abs_im_le_norm hs
  have h2 := one_add_abs_im_le_norm_add_one hs
  have hp : 0 < 1 + |s.im| := by linarith [abs_nonneg s.im]
  have hprod : (1 + |s.im|) ^ 2 / 8 ≤ ‖s * (s + 1)‖ := by
    rw [norm_mul]
    have := mul_le_mul h1 h2 (by positivity) (norm_nonneg _)
    nlinarith
  simp only [Perron.f, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  rw [Real.rpow_neg hp.le, Real.rpow_two, div_le_iff₀ (lt_of_lt_of_le (by positivity) hprod)]
  have hxs : 0 ≤ x ^ s.re := Real.rpow_nonneg hx.le _
  calc x ^ s.re = 8 * x ^ s.re * ((1 + |s.im|) ^ 2)⁻¹ * ((1 + |s.im|) ^ 2 / 8) := by
        field_simp
    _ ≤ 8 * x ^ s.re * ((1 + |s.im|) ^ 2)⁻¹ * ‖s * (s + 1)‖ := by gcongr

lemma norm_perron_mul_le {x C η : ℝ} (hx : 0 < x) {G : ℂ → ℂ} {s : ℂ} (hs : 1 / 2 ≤ s.re)
    (hG : ‖G s‖ ≤ C * (1 + |s.im|) ^ η) :
    ‖Perron.f x s * G s‖ ≤ 8 * C * x ^ s.re * (1 + |s.im|) ^ (η - 2) := by
  have hp : 0 < 1 + |s.im| := by linarith [abs_nonneg s.im]
  rw [norm_mul]
  have hC : 0 ≤ C * (1 + |s.im|) ^ η := (norm_nonneg _).trans hG
  calc ‖Perron.f x s‖ * ‖G s‖ ≤ (8 * x ^ s.re * (1 + |s.im|) ^ (-2 : ℝ)) *
        (C * (1 + |s.im|) ^ η) := mul_le_mul (norm_perron_f_le hx hs) hG (norm_nonneg _)
          (by positivity)
    _ = 8 * C * x ^ s.re * ((1 + |s.im|) ^ (-2 : ℝ) * (1 + |s.im|) ^ η) := by ring
    _ = 8 * C * x ^ s.re * (1 + |s.im|) ^ (η - 2) := by
        rw [← Real.rpow_add hp]; ring_nf

lemma perron_differentiableAt {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (Perron.f x) s := by
  apply (Perron.isHolomorphicOn hx).differentiableAt
  apply IsOpen.mem_nhds
  · exact (Set.toFinite ({0, -1} : Set ℂ)).isClosed.isOpen_compl
  · simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    constructor
    · intro h; have := congrArg Complex.re h; simp at this; linarith
    · intro h; have := congrArg Complex.re h; simp at this; linarith

open MeasureTheory in
lemma integrable_perron_line {G : ℂ → ℂ} {σ C η x : ℝ} (hσ : 1 / 2 ≤ σ) (hη : η < 1)
    (hx : 0 < x)
    (hcont : Continuous fun y : ℝ => G (σ + y * I))
    (hGb : ∀ y : ℝ, ‖G (σ + y * I)‖ ≤ C * (1 + |y|) ^ η) :
    Integrable (fun y : ℝ => Perron.f x (σ + y * I) * G (σ + y * I)) := by
  have hmaj : Integrable (fun y : ℝ => 8 * C * x ^ σ * (1 + ‖y‖) ^ (-(2 - η))) :=
    (integrable_one_add_norm (E := ℝ) (r := 2 - η) (by simp; linarith)).const_mul _
  have hcontF : Continuous fun y : ℝ => Perron.f x (σ + y * I) * G (σ + y * I) := by
    refine Continuous.mul ?_ hcont
    rw [continuous_iff_continuousAt]
    intro y
    have h1 : ContinuousAt (fun y : ℝ => (σ : ℂ) + y * I) y := by fun_prop
    exact ContinuousAt.comp (g := Perron.f x)
      (perron_differentiableAt hx (by simp; linarith)).continuousAt h1
  refine Integrable.mono' hmaj hcontF.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  have hs : 1 / 2 ≤ ((σ : ℂ) + y * I).re := by simpa using hσ
  have := norm_perron_mul_le hx hs (G := G) (C := C) (η := η) (by simpa using hGb y)
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add] at this
  rw [Real.norm_eq_abs, show -(2 - η) = η - 2 by ring]
  exact this

open MeasureTheory in
/-- **Contour shift** `∫_{(2)} = ∫_{(σ₀)}` for `x^s/(s(s+1)) · G(s)`, when `G` is holomorphic on
`Re s ≥ σ₀ ≥ 1/2` with `‖G(s)‖ ≤ C (1+|Im s|)^η`, `η < 1`. -/
theorem vertical_shift {G : ℂ → ℂ} {σ₀ C η x : ℝ} (hσ₀ : 1 / 2 ≤ σ₀) (hσ₀2 : σ₀ ≤ 2)
    (hη : η < 1) (hx : 1 ≤ x) (hC : 0 ≤ C)
    (hGd : ∀ s : ℂ, σ₀ ≤ s.re → DifferentiableAt ℂ G s)
    (hGb : ∀ s : ℂ, σ₀ ≤ s.re → ‖G s‖ ≤ C * (1 + |s.im|) ^ η) :
    VerticalIntegral (fun s ↦ Perron.f x s * G s) σ₀ =
      VerticalIntegral (fun s ↦ Perron.f x s * G s) 2 := by
  have hx0 : 0 < x := by linarith
  have hlineG : ∀ σ, σ₀ ≤ σ → Continuous fun y : ℝ => G (σ + y * I) := by
    intro σ hσ
    rw [continuous_iff_continuousAt]
    intro y
    have h1 : ContinuousAt (fun y : ℝ => (σ : ℂ) + y * I) y := by fun_prop
    exact ContinuousAt.comp (g := G) (hGd _ (by simpa using hσ)).continuousAt h1
  have hlineB : ∀ σ, σ₀ ≤ σ → ∀ y : ℝ, ‖G (σ + y * I)‖ ≤ C * (1 + |y|) ^ η := by
    intro σ hσ y
    have := hGb ((σ : ℂ) + y * I) (by simpa using hσ)
    simpa using this
  -- horizontal integrals
  have hhor : ∀ y : ℝ, ‖∫ u in σ₀..2, Perron.f x (u + y * I) * G (u + y * I)‖ ≤
      (2 - σ₀) * (8 * C * x ^ (2 : ℝ)) * (1 + |y|) ^ (η - 2) := by
    intro y
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := σ₀) (b := 2)
      (C := 8 * C * x ^ (2 : ℝ) * (1 + |y|) ^ (η - 2))
      (f := fun u : ℝ => Perron.f x (u + y * I) * G (u + y * I)) (by
        intro u hu
        rw [uIoc_of_le hσ₀2] at hu
        have hs : 1 / 2 ≤ ((u : ℂ) + y * I).re := by simp; linarith [hu.1]
        have h1 := norm_perron_mul_le hx0 hs (hGb _ (by simp; linarith [hu.1]))
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero, add_im, mul_im, zero_add] at h1
        refine h1.trans ?_
        have hxu : x ^ u ≤ x ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hu.2
        have hp : 0 ≤ (1 + |y|) ^ (η - 2) := Real.rpow_nonneg (by positivity) _
        have hC8 : 0 ≤ 8 * C := by positivity
        gcongr)
    calc _ ≤ 8 * C * x ^ (2 : ℝ) * (1 + |y|) ^ (η - 2) * |2 - σ₀| := this
      _ = _ := by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 - σ₀)]; ring
  have hdecay : Tendsto (fun y : ℝ => (2 - σ₀) * (8 * C * x ^ (2 : ℝ)) * (1 + |y|) ^ (η - 2))
      (atTop ⊔ atBot) (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => 1 + |y|) (atTop ⊔ atBot) atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_abs_atTop_atTop.sup tendsto_abs_atBot_atTop)
    have h2 := (tendsto_rpow_neg_atTop (y := 2 - η) (by linarith)).comp h1
    have h3 := h2.const_mul ((2 - σ₀) * (8 * C * x ^ (2 : ℝ)))
    rw [mul_zero] at h3
    refine h3.congr fun y => ?_
    simp only [Function.comp, neg_sub]
  have hT := squeeze_zero_norm hhor hdecay
  refine verticalIntegral_eq_verticalIntegral ?_ (hT.mono_left le_sup_right)
    (hT.mono_left le_sup_left)
    (integrable_perron_line hσ₀ hη hx0 (hlineG σ₀ le_rfl) (hlineB σ₀ le_rfl))
    (integrable_perron_line (by norm_num) hη hx0 (hlineG 2 hσ₀2) (hlineB 2 hσ₀2))
  intro z hz
  rw [mem_reProdIm, uIcc_of_le hσ₀2] at hz
  exact ((perron_differentiableAt hx0 (by linarith [hz.1.1])).mul
    (hGd z hz.1.1)).differentiableWithinAt

/-! ## 8. The difference kernel `(y^{s+1} − x^{s+1})/(s(s+1))` -/

/-- Mean-value bound: `‖y·y^s − x·x^s‖ ≤ ‖s+1‖ · y^σ · (y − x)` for `0 < x ≤ y`, `σ ≥ 0`. -/
lemma norm_mul_cpow_sub_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(y : ℂ) * (y : ℂ) ^ s - (x : ℂ) * (x : ℂ) ^ s‖ ≤ ‖s + 1‖ * y ^ s.re * (y - x) := by
  set f : ℝ → ℂ := fun u => (u : ℂ) * (u : ℂ) ^ s with hf
  have hderiv : ∀ u : ℝ, 0 < u → HasDerivAt f ((s + 1) * (u : ℂ) ^ s) u := by
    intro u hu
    have hslit : (u : ℂ) ∈ slitPlane := by
      rw [mem_slitPlane_iff]; left; simpa using hu
    have h1 : HasDerivAt (fun v : ℝ => (v : ℂ) ^ s) (s * (u : ℂ) ^ (s - 1)) u :=
      (Complex.hasStrictDerivAt_cpow_const hslit).hasDerivAt.comp_ofReal
    have h2 : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 u := hasDerivAt_id u |>.ofReal_comp
    have h3 := h2.mul h1
    convert h3 using 1
    have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
    rw [cpow_sub _ _ hu0, cpow_one]
    field_simp
    ring
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := f) (a := x) (b := y)
    (f' := fun u => (s + 1) * (u : ℂ) ^ s) (C := ‖s + 1‖ * y ^ s.re)
    (fun u hu => (hderiv u (by linarith [hu.1])).hasDerivWithinAt)
    (fun u hu => by
      have hu0 : 0 < u := by linarith [hu.1]
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
      gcongr
      exact hu.2.le) y ⟨hxy, le_rfl⟩
  simpa [hf] using hmv

lemma perron_mul_sub_eq {x y : ℝ} {s : ℂ} :
    (y : ℂ) * Perron.f y s - (x : ℂ) * Perron.f x s =
      ((y : ℂ) * (y : ℂ) ^ s - (x : ℂ) * (x : ℂ) ^ s) / (s * (s + 1)) := by
  simp only [Perron.f]; ring

/-- `p ≤ Q u w^{-2}` and `p ≤ Q v w^{-1}` give `p ≤ Q u^θ v^{1−θ} w^{−(1+θ)}`. -/
lemma le_interp_of_le_two {p Q u v w θ : ℝ} (hp : 0 ≤ p) (hQ : 0 ≤ Q) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hw : 0 < w) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hA : p ≤ Q * u * w ^ (-2 : ℝ)) (hB : p ≤ Q * v * w ^ (-1 : ℝ)) :
    p ≤ Q * u ^ θ * v ^ (1 - θ) * w ^ (-(1 + θ)) := by
  rcases hp.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  have hw2 : 0 < w ^ (-2 : ℝ) := Real.rpow_pos_of_pos hw _
  have hw1 : 0 < w ^ (-1 : ℝ) := Real.rpow_pos_of_pos hw _
  have hQu : 0 < Q * u := by
    by_contra h; push Not at h
    have : Q * u * w ^ (-2 : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hw2.le
    linarith
  have hQv : 0 < Q * v := by
    by_contra h; push Not at h
    have : Q * v * w ^ (-1 : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hw1.le
    linarith
  have hQ0 : 0 < Q := by
    rcases hQ.eq_or_lt with h | h
    · rw [← h, zero_mul] at hQu; exact absurd hQu (lt_irrefl 0)
    · exact h
  have hu0 : 0 < u := pos_of_mul_pos_right hQu hQ0.le
  have hv0 : 0 < v := pos_of_mul_pos_right hQv hQ0.le
  have hsplit : p = p ^ θ * p ^ (1 - θ) := by
    rw [← Real.rpow_add hpos]; simp
  have h1 : p ^ θ ≤ (Q * u * w ^ (-2 : ℝ)) ^ θ := Real.rpow_le_rpow hp hA hθ0
  have h2 : p ^ (1 - θ) ≤ (Q * v * w ^ (-1 : ℝ)) ^ (1 - θ) :=
    Real.rpow_le_rpow hp hB (by linarith)
  have hprod := mul_le_mul h1 h2 (Real.rpow_nonneg hp _) (Real.rpow_nonneg (by positivity) _)
  rw [← hsplit] at hprod
  refine hprod.trans (le_of_eq ?_)
  rw [Real.mul_rpow (by positivity) hw2.le, Real.mul_rpow hQ0.le hu0.le,
    Real.mul_rpow (by positivity) hw1.le, Real.mul_rpow hQ0.le hv0.le,
    ← Real.rpow_mul hw.le, ← Real.rpow_mul hw.le]
  have eQ : Q ^ θ * Q ^ (1 - θ) = Q := by rw [← Real.rpow_add hQ0]; simp
  have ew : w ^ (-2 * θ) * w ^ (-1 * (1 - θ)) = w ^ (-(1 + θ)) := by
    rw [← Real.rpow_add hw]; ring_nf
  calc Q ^ θ * u ^ θ * w ^ (-2 * θ) * (Q ^ (1 - θ) * v ^ (1 - θ) * w ^ (-1 * (1 - θ)))
      = (Q ^ θ * Q ^ (1 - θ)) * u ^ θ * v ^ (1 - θ) * (w ^ (-2 * θ) * w ^ (-1 * (1 - θ))) := by
        ring
    _ = Q * u ^ θ * v ^ (1 - θ) * w ^ (-(1 + θ)) := by rw [eQ, ew]

/-- **Kernel bound**: `‖y f_y(s) − x f_x(s)‖ ≤ 16 y^{σ+θ} (y−x)^{1−θ} (1+|t|)^{−(1+θ)}`. -/
lemma kernel_bound {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) {s : ℂ} (hs : 1 / 2 ≤ s.re)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ‖(y : ℂ) * Perron.f y s - (x : ℂ) * Perron.f x s‖ ≤
      16 * y ^ s.re * y ^ θ * (y - x) ^ (1 - θ) * (1 + |s.im|) ^ (-(1 + θ)) := by
  have hy : 0 < y := hx.trans_le hxy
  set w := 1 + |s.im| with hw
  have hw0 : 0 < w := by rw [hw]; linarith [abs_nonneg s.im]
  have h1 := one_add_abs_im_le_norm hs
  have h2 := one_add_abs_im_le_norm_add_one hs
  have hsn : 0 < ‖s‖ := lt_of_lt_of_le (by positivity) h1
  have hs1n : 0 < ‖s + 1‖ := lt_of_lt_of_le (by positivity) h2
  rw [perron_mul_sub_eq, norm_div, norm_mul]
  set D := ‖(y : ℂ) * (y : ℂ) ^ s - (x : ℂ) * (x : ℂ) ^ s‖ with hD
  -- bound A
  have hDA : D ≤ 2 * y ^ s.re * y := by
    have e1 : ‖(y : ℂ) * (y : ℂ) ^ s‖ = y ^ s.re * y := by
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hy]; ring
    have e2 : ‖(x : ℂ) * (x : ℂ) ^ s‖ = x ^ s.re * x := by
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hx]; ring
    have e3 : x ^ s.re * x ≤ y ^ s.re * y := by
      gcongr
    have := norm_sub_le ((y : ℂ) * (y : ℂ) ^ s) ((x : ℂ) * (x : ℂ) ^ s)
    rw [e1, e2] at this
    linarith
  have hDB := norm_mul_cpow_sub_le hx hxy (s := s) (by linarith)
  have hwm2 : w ^ (-2 : ℝ) = (w ^ 2)⁻¹ := by rw [Real.rpow_neg hw0.le, Real.rpow_two]
  have hwm1 : w ^ (-1 : ℝ) = w⁻¹ := Real.rpow_neg_one w
  have hA : D / (‖s‖ * ‖s + 1‖) ≤ 16 * y ^ s.re * y * w ^ (-2 : ℝ) := by
    rw [hwm2, div_le_iff₀ (by positivity)]
    have hprod : w ^ 2 / 8 ≤ ‖s‖ * ‖s + 1‖ := by
      have := mul_le_mul h1 h2 (by positivity) (norm_nonneg _); nlinarith
    calc D ≤ 2 * y ^ s.re * y := hDA
      _ = 16 * y ^ s.re * y * (w ^ 2)⁻¹ * (w ^ 2 / 8) := by field_simp; ring
      _ ≤ 16 * y ^ s.re * y * (w ^ 2)⁻¹ * (‖s‖ * ‖s + 1‖) := by gcongr
  have hB : D / (‖s‖ * ‖s + 1‖) ≤ 16 * y ^ s.re * (y - x) * w ^ (-1 : ℝ) := by
    rw [hwm1, div_le_iff₀ (by positivity)]
    calc D ≤ ‖s + 1‖ * y ^ s.re * (y - x) := hDB
      _ = 4 * y ^ s.re * (y - x) * w⁻¹ * (w / 4) * ‖s + 1‖ := by field_simp
      _ ≤ 16 * y ^ s.re * (y - x) * w⁻¹ * ‖s‖ * ‖s + 1‖ := by
          have hyx : 0 ≤ y - x := by linarith
          have : 0 ≤ y ^ s.re := Real.rpow_nonneg hy.le _
          gcongr
          norm_num
      _ = 16 * y ^ s.re * (y - x) * w⁻¹ * (‖s‖ * ‖s + 1‖) := by ring
  have key := le_interp_of_le_two (p := D / (‖s‖ * ‖s + 1‖)) (Q := 16 * y ^ s.re) (u := y)
    (v := y - x) (w := w) (θ := θ) (by positivity) (by positivity) hy.le (by linarith) hw0 hθ0 hθ1
    hA hB
  calc D / (‖s‖ * ‖s + 1‖) ≤ 16 * y ^ s.re * y ^ θ * (y - x) ^ (1 - θ) * w ^ (-(1 + θ)) := key
    _ = _ := rfl

/-! ## 9. Smoothed sums and their differences -/

/-- Smoothed partial sum `∑_{n ≤ x} a(n) (x − n)`. -/
def Ssum (a : ℕ → ℂ) (x : ℝ) : ℂ := ∑ n ∈ Finset.Iic ⌊x⌋₊, a n * ((x : ℂ) - n)

lemma two_pi_I_Ssum {a : ℕ → ℂ} (ha0 : a 0 = 0) (ha : ∀ n, ‖a n‖ ≤ 1) {G : ℂ → ℂ}
    (hG : ∀ s : ℂ, 1 < s.re → G s = LSeries a s) {x : ℝ} (hx : 0 < x)
    (hxn : ∀ n : ℕ, (n : ℝ) ≠ x) :
    2 * Real.pi * I * Ssum a x = x * VerticalIntegral (fun s ↦ Perron.f x s * G s) 2 := by
  rw [perron_general ha0 ha hG hx hxn (by norm_num : (1 : ℝ) < 2), Ssum, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  field_simp

lemma line_continuous {G : ℂ → ℂ} {σ₀ σ : ℝ} (hGd : ∀ s : ℂ, σ₀ ≤ s.re → DifferentiableAt ℂ G s)
    (hσ : σ₀ ≤ σ) : Continuous fun y : ℝ => G (σ + y * I) := by
  rw [continuous_iff_continuousAt]
  intro y
  have h1 : ContinuousAt (fun y : ℝ => (σ : ℂ) + y * I) y := by fun_prop
  exact ContinuousAt.comp (g := G) (hGd _ (by simpa using hσ)).continuousAt h1

lemma line_bound {G : ℂ → ℂ} {σ₀ σ C η : ℝ}
    (hGb : ∀ s : ℂ, σ₀ ≤ s.re → ‖G s‖ ≤ C * (1 + |s.im|) ^ η) (hσ : σ₀ ≤ σ) (y : ℝ) :
    ‖G (σ + y * I)‖ ≤ C * (1 + |y|) ^ η := by
  have := hGb ((σ : ℂ) + y * I) (by simpa using hσ)
  simpa using this

open MeasureTheory in
/-- **Difference bound for the smoothed sums.** If `G = L(a, ·)` on `Re s > 1`, `G` is
holomorphic on `Re s ≥ σ₀` with `‖G(s)‖ ≤ C (1+|t|)^{θ/2}` there (`0 < θ ≤ 1`), then for
non-integers `1 ≤ x ≤ y`:
`‖S(y) − S(x)‖ ≤ 16 C I_θ · y^{σ₀+θ} (y−x)^{1−θ}`, `I_θ = ∫ (1+|t|)^{−(1+θ/2)} dt`. -/
theorem Ssum_diff_bound {a : ℕ → ℂ} (ha0 : a 0 = 0) (ha : ∀ n, ‖a n‖ ≤ 1) {G : ℂ → ℂ}
    (hG : ∀ s : ℂ, 1 < s.re → G s = LSeries a s) {σ₀ θ C : ℝ} (hσ₀ : 1 / 2 ≤ σ₀)
    (hσ₀2 : σ₀ ≤ 2) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hC : 0 ≤ C)
    (hGd : ∀ s : ℂ, σ₀ ≤ s.re → DifferentiableAt ℂ G s)
    (hGb : ∀ s : ℂ, σ₀ ≤ s.re → ‖G s‖ ≤ C * (1 + |s.im|) ^ (θ / 2))
    {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) (hxn : ∀ n : ℕ, (n : ℝ) ≠ x)
    (hyn : ∀ n : ℕ, (n : ℝ) ≠ y) :
    ‖Ssum a y - Ssum a x‖ ≤
      16 * C * (∫ t : ℝ, (1 + ‖t‖) ^ (-(1 + θ / 2))) * y ^ (σ₀ + θ) * (y - x) ^ (1 - θ) := by
  have hx0 : 0 < x := by linarith
  have hy1 : 1 ≤ y := hx.trans hxy
  have hy0 : 0 < y := by linarith
  have hη : θ / 2 < 1 := by linarith
  set F : ℝ → ℂ → ℂ := fun z s => Perron.f z s * G s with hF
  have hshift : ∀ z : ℝ, 1 ≤ z → VerticalIntegral (F z) 2 = VerticalIntegral (F z) σ₀ :=
    fun z hz => (vertical_shift hσ₀ hσ₀2 hη hz hC hGd hGb).symm
  have hint : ∀ z : ℝ, 0 < z → Integrable (fun t : ℝ => F z (σ₀ + t * I)) := fun z hz =>
    integrable_perron_line hσ₀ hη hz (line_continuous hGd le_rfl) (line_bound hGb le_rfl)
  have hsx := two_pi_I_Ssum ha0 ha hG hx0 hxn
  have hsy := two_pi_I_Ssum ha0 ha hG hy0 hyn
  have e : 2 * Real.pi * I * (Ssum a y - Ssum a x) =
      I * ∫ t : ℝ, ((y : ℂ) * F y (σ₀ + t * I) - (x : ℂ) * F x (σ₀ + t * I)) := by
    rw [mul_sub, hsy, hsx, hshift y hy1, hshift x hx, VerticalIntegral, VerticalIntegral,
      integral_sub ((hint y hy0).const_mul _) ((hint x hx0).const_mul _), integral_const_mul,
      integral_const_mul]
    simp only [smul_eq_mul]
    ring
  set K0 := 16 * C * y ^ σ₀ * y ^ θ * (y - x) ^ (1 - θ) with hK0
  have hK0nn : 0 ≤ K0 := by
    have : 0 ≤ (y - x) ^ (1 - θ) := Real.rpow_nonneg (by linarith) _
    positivity
  have hgint : Integrable (fun t : ℝ => K0 * (1 + ‖t‖) ^ (-(1 + θ / 2))) :=
    (integrable_one_add_norm (E := ℝ) (r := 1 + θ / 2) (by simp; linarith)).const_mul _
  have hpt : ∀ t : ℝ, ‖(y : ℂ) * F y (σ₀ + t * I) - (x : ℂ) * F x (σ₀ + t * I)‖ ≤
      K0 * (1 + ‖t‖) ^ (-(1 + θ / 2)) := by
    intro t
    have hs : 1 / 2 ≤ ((σ₀ : ℂ) + t * I).re := by simpa using hσ₀
    have hk := kernel_bound hx0 hxy hs hθ0.le hθ1
    have hG' := line_bound hGb le_rfl t (σ := σ₀)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add] at hk
    have e2 : (y : ℂ) * F y (σ₀ + t * I) - (x : ℂ) * F x (σ₀ + t * I) =
        ((y : ℂ) * Perron.f y (σ₀ + t * I) - (x : ℂ) * Perron.f x (σ₀ + t * I)) *
          G (σ₀ + t * I) := by simp only [hF]; ring
    rw [e2, norm_mul, Real.norm_eq_abs]
    have hw : 0 < 1 + |t| := by linarith [abs_nonneg t]
    have hk0 : 0 ≤ 16 * y ^ σ₀ * y ^ θ * (y - x) ^ (1 - θ) := by
      have : 0 ≤ (y - x) ^ (1 - θ) := Real.rpow_nonneg (by linarith) _
      positivity
    calc ‖(y : ℂ) * Perron.f y (σ₀ + t * I) - (x : ℂ) * Perron.f x (σ₀ + t * I)‖ *
          ‖G (σ₀ + t * I)‖
        ≤ (16 * y ^ σ₀ * y ^ θ * (y - x) ^ (1 - θ) * (1 + |t|) ^ (-(1 + θ))) *
            (C * (1 + |t|) ^ (θ / 2)) :=
          mul_le_mul hk hG' (norm_nonneg _) (by positivity)
      _ = K0 * ((1 + |t|) ^ (-(1 + θ)) * (1 + |t|) ^ (θ / 2)) := by rw [hK0]; ring
      _ = K0 * (1 + |t|) ^ (-(1 + θ / 2)) := by rw [← Real.rpow_add hw]; ring_nf
  have hnorm := norm_integral_le_of_norm_le hgint (Eventually.of_forall hpt)
  rw [integral_const_mul] at hnorm
  have h2pi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hlhs : ‖2 * Real.pi * I * (Ssum a y - Ssum a x)‖ = 2 * Real.pi * ‖Ssum a y - Ssum a x‖ := by
    rw [norm_mul, norm_mul, norm_I, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    simp
  have hrhs : ‖I * ∫ t : ℝ, ((y : ℂ) * F y (σ₀ + t * I) - (x : ℂ) * F x (σ₀ + t * I))‖ =
      ‖∫ t : ℝ, ((y : ℂ) * F y (σ₀ + t * I) - (x : ℂ) * F x (σ₀ + t * I))‖ := by
    rw [norm_mul, norm_I, one_mul]
  have hmain : 2 * Real.pi * ‖Ssum a y - Ssum a x‖ ≤ K0 * ∫ t : ℝ, (1 + ‖t‖) ^ (-(1 + θ / 2)) := by
    rw [← hlhs, e, hrhs]; exact hnorm
  have hI0 : 0 ≤ ∫ t : ℝ, (1 + ‖t‖) ^ (-(1 + θ / 2)) :=
    integral_nonneg fun t => Real.rpow_nonneg (by positivity) _
  have hfin : ‖Ssum a y - Ssum a x‖ ≤ K0 * ∫ t : ℝ, (1 + ‖t‖) ^ (-(1 + θ / 2)) := by
    have h0 := norm_nonneg (Ssum a y - Ssum a x)
    nlinarith
  refine hfin.trans (le_of_eq ?_)
  rw [hK0, Real.rpow_add hy0]
  ring

/-- Unsmoothing identity (adapted from `KerrPNT.Mobius.S_diff`): differences of `Ssum` recover
the partial sum up to `h²`. -/
lemma Ssum_diff {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1) (N h : ℕ) :
    ‖Ssum a (N + 1 / 2 + h) - Ssum a (N + 1 / 2) - h * ∑ n ∈ Finset.Iic N, a n‖ ≤ (h : ℝ) ^ 2 := by
  have hf1 : ⌊(N : ℝ) + 1 / 2⌋₊ = N := by
    rw [Nat.floor_eq_iff (by positivity)]; constructor <;> linarith
  have hf2 : ⌊(N : ℝ) + 1 / 2 + h⌋₊ = N + h := by
    rw [Nat.floor_eq_iff (by positivity)]; push_cast; constructor <;> linarith
  have hsplit : Finset.Iic (N + h) = Finset.Iic N ∪ Finset.Ioc N (N + h) := by
    ext n; simp only [Finset.mem_Iic, Finset.mem_union, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Iic N) (Finset.Ioc N (N + h)) := by
    rw [Finset.disjoint_left]; intro n h1 h2
    simp only [Finset.mem_Iic, Finset.mem_Ioc] at h1 h2; omega
  rw [Ssum, Ssum, hf1, hf2, hsplit, Finset.sum_union hdisj, Finset.mul_sum]
  have e : ∑ n ∈ Finset.Iic N, a n * ((((N : ℝ) + 1 / 2 + h : ℝ) : ℂ) - n) -
      ∑ n ∈ Finset.Iic N, a n * ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) - n) -
      ∑ n ∈ Finset.Iic N, (h : ℂ) * a n = 0 := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero; intro n _; push_cast; ring
  have : ∑ n ∈ Finset.Iic N, a n * ((((N : ℝ) + 1 / 2 + h : ℝ) : ℂ) - n) +
      ∑ n ∈ Finset.Ioc N (N + h), a n * ((((N : ℝ) + 1 / 2 + h : ℝ) : ℂ) - n) -
      ∑ n ∈ Finset.Iic N, a n * ((((N : ℝ) + 1 / 2 : ℝ) : ℂ) - n) -
      ∑ n ∈ Finset.Iic N, (h : ℂ) * a n =
      ∑ n ∈ Finset.Ioc N (N + h), a n * ((((N : ℝ) + 1 / 2 + h : ℝ) : ℂ) - n) := by
    linear_combination e
  rw [this]
  calc ‖∑ n ∈ Finset.Ioc N (N + h), a n * ((((N : ℝ) + 1 / 2 + h : ℝ) : ℂ) - n)‖
      ≤ ∑ n ∈ Finset.Ioc N (N + h), ‖a n * ((((N : ℝ) + 1 / 2 + h : ℝ) : ℂ) - n)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Ioc N (N + h), (h : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        simp only [Finset.mem_Ioc] at hn
        have h1 : (N : ℝ) + 1 ≤ n := by exact_mod_cast hn.1
        have h2 : (n : ℝ) ≤ N + h := by exact_mod_cast hn.2
        rw [norm_mul]
        have e2 : ((((N : ℝ) + 1 / 2 + h : ℝ) : ℂ) - n) = (((N : ℝ) + 1 / 2 + h - n : ℝ) : ℂ) := by
          push_cast; ring
        rw [e2, Complex.norm_real, Real.norm_eq_abs]
        have hb : |(N : ℝ) + 1 / 2 + h - n| ≤ h := by
          rw [abs_le]; constructor <;> linarith
        calc ‖a n‖ * |(N : ℝ) + 1 / 2 + h - n| ≤ 1 * h :=
              mul_le_mul (ha n) hb (abs_nonneg _) zero_le_one
          _ = h := one_mul _
    _ = (h : ℝ) ^ 2 := by simp; ring

/-- **Partial sums from the smoothed bound.** Under the hypotheses of `Ssum_diff_bound`,
`‖∑_{n ≤ x} a(n)‖ ≤ (64 · 16 C I_θ + 2) x^{σ₀+θ}` for all `x ≥ 1` (with `h = ⌈√x⌉`). -/
theorem partial_sum_bound {a : ℕ → ℂ} (ha0 : a 0 = 0) (ha : ∀ n, ‖a n‖ ≤ 1) {G : ℂ → ℂ}
    (hG : ∀ s : ℂ, 1 < s.re → G s = LSeries a s) {σ₀ θ C : ℝ} (hσ₀ : 1 / 2 ≤ σ₀)
    (hσ₀2 : σ₀ ≤ 2) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hC : 0 ≤ C)
    (hGd : ∀ s : ℂ, σ₀ ≤ s.re → DifferentiableAt ℂ G s)
    (hGb : ∀ s : ℂ, σ₀ ≤ s.re → ‖G s‖ ≤ C * (1 + |s.im|) ^ (θ / 2)) {x : ℝ} (hx : 1 ≤ x) :
    ‖∑ n ∈ Finset.Iic ⌊x⌋₊, a n‖ ≤
      (64 * (16 * C * ∫ t : ℝ, (1 + ‖t‖) ^ (-(1 + θ / 2))) + 2) * x ^ (σ₀ + θ) := by
  set K' := 16 * C * ∫ t : ℝ, (1 + ‖t‖) ^ (-(1 + θ / 2)) with hK'
  have hI0 : 0 ≤ ∫ t : ℝ, (1 + ‖t‖) ^ (-(1 + θ / 2)) :=
    MeasureTheory.integral_nonneg fun t => Real.rpow_nonneg (by positivity) _
  have hK'0 : 0 ≤ K' := by positivity
  have hx0 : 0 < x := by linarith
  set N := ⌊x⌋₊ with hN
  set h := ⌈Real.sqrt x⌉₊ with hh
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0.le
  have hN1 : (1 : ℝ) ≤ N := by
    have : 1 ≤ N := Nat.le_floor (by simpa using hx)
    exact_mod_cast this
  have hsq1 : 1 ≤ Real.sqrt x := by rw [Real.one_le_sqrt]; exact hx
  have hsqx : Real.sqrt x ≤ x := by
    have := Real.sqrt_le_sqrt (show x ≤ x ^ 2 by nlinarith)
    rwa [Real.sqrt_sq hx0.le] at this
  have hh1 : (1 : ℝ) ≤ h := by
    have : Real.sqrt x ≤ h := Nat.le_ceil _
    linarith
  have hhup : (h : ℝ) < Real.sqrt x + 1 := Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
  have hnot : ∀ k : ℕ, ∀ n : ℕ, (n : ℝ) ≠ (N : ℝ) + 1 / 2 + k := by
    intro k n hn
    have : (2 : ℝ) * n = 2 * N + 1 + 2 * k := by linarith
    have : 2 * n = 2 * N + 1 + 2 * k := by exact_mod_cast this
    omega
  set z₁ : ℝ := N + 1 / 2 with hz₁
  set z₂ : ℝ := N + 1 / 2 + h with hz₂
  have hz₁1 : 1 ≤ z₁ := by linarith
  have hz12 : z₁ ≤ z₂ := by linarith
  have hd := Ssum_diff_bound ha0 ha hG hσ₀ hσ₀2 hθ0 hθ1 hC hGd hGb hz₁1 hz12
    (by simpa [hz₁] using hnot 0) (hnot h)
  rw [← hK'] at hd
  have hdiff := Ssum_diff ha N h
  have hz2x : z₂ ≤ 4 * x := by linarith
  have hexp0 : 0 ≤ σ₀ + θ := by linarith
  have hpow : z₂ ^ (σ₀ + θ) ≤ 64 * x ^ (σ₀ + θ) := by
    calc z₂ ^ (σ₀ + θ) ≤ (4 * x) ^ (σ₀ + θ) := Real.rpow_le_rpow (by linarith) hz2x hexp0
      _ = 4 ^ (σ₀ + θ) * x ^ (σ₀ + θ) := Real.mul_rpow (by norm_num) hx0.le
      _ ≤ 4 ^ (3 : ℝ) * x ^ (σ₀ + θ) := by
          gcongr
          · norm_num
          · linarith
      _ = 64 * x ^ (σ₀ + θ) := by norm_num
  have hhpow : (z₂ - z₁) ^ (1 - θ) ≤ h := by
    have e : z₂ - z₁ = h := by rw [hz₂, hz₁]; ring
    rw [e]
    calc (h : ℝ) ^ (1 - θ) ≤ (h : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hh1 (by linarith)
      _ = h := Real.rpow_one _
  have hd2 : ‖Ssum a z₂ - Ssum a z₁‖ ≤ K' * (64 * x ^ (σ₀ + θ)) * h := by
    refine hd.trans ?_
    have : 0 ≤ (z₂ - z₁) ^ (1 - θ) := Real.rpow_nonneg (by linarith) _
    have : 0 ≤ z₂ ^ (σ₀ + θ) := Real.rpow_nonneg (by linarith) _
    gcongr
  -- `h ‖A‖ ≤ ‖ΔS‖ + h²`
  set A : ℂ := ∑ n ∈ Finset.Iic N, a n with hAdef
  set D : ℂ := Ssum a z₂ - Ssum a z₁ with hDdef
  have hdiff' : ‖D - (h : ℂ) * A‖ ≤ (h : ℝ) ^ 2 := by
    simpa [hz₁, hz₂, hDdef, hAdef] using hdiff
  have hA : (h : ℝ) * ‖A‖ ≤ K' * (64 * x ^ (σ₀ + θ)) * h + (h : ℝ) ^ 2 := by
    have e1 : (h : ℝ) * ‖A‖ = ‖(h : ℂ) * A‖ := by
      rw [norm_mul, Complex.norm_natCast]
    rw [e1]
    have t1 := norm_sub_le D (D - (h : ℂ) * A)
    have e2 : D - (D - (h : ℂ) * A) = (h : ℂ) * A := by ring
    rw [e2] at t1
    linarith
  have hA2 : ‖A‖ ≤ K' * (64 * x ^ (σ₀ + θ)) + h := by
    have hhpos : (0 : ℝ) < h := by linarith
    have : (h : ℝ) * ‖A‖ ≤ (h : ℝ) * (K' * (64 * x ^ (σ₀ + θ)) + h) := by
      nlinarith
    exact le_of_mul_le_mul_left this hhpos
  have hsqpow : Real.sqrt x ≤ x ^ (σ₀ + θ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hxpow : 1 ≤ x ^ (σ₀ + θ) := Real.one_le_rpow hx hexp0
  have h3 : (h : ℝ) ≤ 2 * x ^ (σ₀ + θ) := by linarith
  have e : K' * (64 * x ^ (σ₀ + θ)) + 2 * x ^ (σ₀ + θ) = (64 * K' + 2) * x ^ (σ₀ + θ) := by ring
  linarith

/-! ## 10. RH ⇒ Mertens and Liouville growth -/

open KerrPNT.Mobius in
/-- **RH ⇒ `M(x) = O(x^{1/2+ε})`** (Littlewood). -/
theorem RH_implies_Mertens_growth : Kerr.File14RHExtra.RH_implies_Mertens_growth_statement := by
  intro hRH ε hε
  set ε' := min ε (1 / 2) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by norm_num)
  have hε'1 : ε' ≤ 1 / 2 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  obtain ⟨C, hC, hb⟩ := invZeta_bound_RH hRH (σ₀ := 1 / 2 + ε' / 2) (by linarith)
    (η := ε' / 2 / 2) (by positivity)
  set K := 64 * (16 * C * ∫ t : ℝ, (1 + ‖t‖) ^ (-(1 + ε' / 2 / 2))) + 2 with hK
  have hI0 : 0 ≤ ∫ t : ℝ, (1 + ‖t‖) ^ (-(1 + ε' / 2 / 2)) :=
    MeasureTheory.integral_nonneg fun t => Real.rpow_nonneg (by positivity) _
  refine ⟨K, by positivity, fun x hx => ?_⟩
  have key := partial_sum_bound (a := fun n => (μ n : ℂ)) (by simp)
    (fun n => by rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one)
    (G := invZeta) (fun s hs => invZeta_eq_LSeries hs) (σ₀ := 1 / 2 + ε' / 2) (θ := ε' / 2)
    (by linarith) (by linarith) (by positivity) (by linarith) hC.le
    (fun s hs => invZeta_differentiableAt_RH hRH (by linarith)) hb hx
  rw [← hK] at key
  have hset : Finset.range (⌊x⌋.toNat + 1) = Finset.Iic ⌊x⌋₊ := by
    rw [Int.floor_toNat]; ext n; simp
  have hM : |Kerr.File14RHExtra.Mertens x| = ‖∑ n ∈ Finset.Iic ⌊x⌋₊, (μ n : ℂ)‖ := by
    have e : ((Kerr.File14RHExtra.Mertens x : ℝ) : ℂ) = ∑ n ∈ Finset.Iic ⌊x⌋₊, (μ n : ℂ) := by
      rw [Kerr.File14RHExtra.Mertens, hset]; push_cast; rfl
    rw [← e, Complex.norm_real, Real.norm_eq_abs]
  rw [hM]
  refine key.trans ?_
  have : x ^ (1 / 2 + ε' / 2 + ε' / 2) ≤ x ^ (1 / 2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  gcongr

/-- `‖ζ(w)‖ ≤ ∑ (n+1)^{-(1+κ)}` for `Re w ≥ 1 + κ`. -/
lemma zeta_norm_le_of_re {κ : ℝ} (hκ : 0 < κ) {w : ℂ} (hw : 1 + κ ≤ w.re) :
    ‖ζ w‖ ≤ ∑' n : ℕ, 1 / |(n : ℝ) + 1| ^ (1 + κ) := by
  have hsum : Summable (fun n : ℕ => 1 / |(n : ℝ) + 1| ^ (1 + κ)) :=
    (Real.summable_one_div_nat_add_rpow 1 (1 + κ)).mpr (by linarith)
  have hterm : ∀ n : ℕ, ‖1 / ((n : ℂ) + 1) ^ w‖ ≤ 1 / |(n : ℝ) + 1| ^ (1 + κ) := by
    intro n
    have e : ((n : ℂ) + 1) = (((n + 1 : ℕ) : ℕ) : ℂ) := by push_cast; ring
    rw [e, norm_div, norm_one, norm_natCast_cpow_of_pos (by omega)]
    push_cast
    rw [abs_of_pos (by positivity)]
    have : ((n : ℝ) + 1) ^ (1 + κ) ≤ ((n : ℝ) + 1) ^ w.re :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) hw
    gcongr
  have hsum2 : Summable (fun n : ℕ => ‖1 / ((n : ℂ) + 1) ^ w‖) :=
    hsum.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by linarith)]
  exact (norm_tsum_le_tsum_norm hsum2).trans (hsum2.tsum_le_tsum hterm hsum)

open KerrPNT.Mobius Kerr.File14RHExtra in
/-- For `Re s > 1`, `L(λ, s) = ζ(2s)/ζ(s)`. -/
lemma LSeries_liouville {s : ℂ} (hs : 1 < s.re) :
    riemannZeta (2 * s) * invZeta s = LSeries (fun n => (Liouville n : ℂ)) s := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
  have hz : ζ s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hL : LSeries (fun n => (Liouville n : ℂ)) s =
      ∑' n, liouHom s (ne_zero_of_one_lt_re hs) n := by
    rw [LSeries]
    refine tsum_congr fun n => ?_
    rw [LSeries.term_def]
    simp only [liouHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
    by_cases hn : n = 0
    · subst hn; simp [Kerr.File14RHExtra.Liouville]
    · rw [ite_eq_right hn, cpow_neg, div_eq_mul_inv]
  rw [hL, invZeta_of_ne hs1, ← liouville_mul_zeta hs]
  field_simp

open KerrPNT.Mobius Kerr.File14RHExtra in
/-- **RH ⇒ `L(x) = O(x^{1/2+ε})`** for the Liouville summatory function, via `L(s) = ζ(2s)/ζ(s)`. -/
theorem RH_implies_Liouville_growth :
    Kerr.File14RHExtra.RH_implies_Liouville_growth_statement := by
  intro hRH ε hε
  set ε' := min ε (1 / 2) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by norm_num)
  have hε'1 : ε' ≤ 1 / 2 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  obtain ⟨C, hC, hb⟩ := invZeta_bound_RH hRH (σ₀ := 1 / 2 + ε' / 2) (by linarith)
    (η := ε' / 2 / 2) (by positivity)
  set Z := ∑' n : ℕ, 1 / |(n : ℝ) + 1| ^ (1 + ε') with hZ
  have hZ0 : 0 ≤ Z := tsum_nonneg fun n => by positivity
  set K := 64 * (16 * (Z * C) * ∫ t : ℝ, (1 + ‖t‖) ^ (-(1 + ε' / 2 / 2))) + 2 with hK
  have hI0 : 0 ≤ ∫ t : ℝ, (1 + ‖t‖) ^ (-(1 + ε' / 2 / 2)) :=
    MeasureTheory.integral_nonneg fun t => Real.rpow_nonneg (by positivity) _
  refine ⟨K, by positivity, fun x hx => ?_⟩
  have h2s : ∀ s : ℂ, 1 / 2 + ε' / 2 ≤ s.re → 1 + ε' ≤ (2 * s).re := by
    intro s hs; simp; linarith
  have key := partial_sum_bound (a := fun n => (Liouville n : ℂ)) (by simp [Kerr.File14RHExtra.Liouville])
    (fun n => by rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_Liouville_le n)
    (G := fun s => riemannZeta (2 * s) * invZeta s) (fun s hs => LSeries_liouville hs)
    (σ₀ := 1 / 2 + ε' / 2) (θ := ε' / 2) (C := Z * C)
    (by linarith) (by linarith) (by positivity) (by linarith) (by positivity)
    (fun s hs => by
      have h2 : 2 * s ≠ 1 := by
        intro h; have := h2s s hs; rw [h] at this; simp at this; linarith
      exact ((differentiableAt_riemannZeta h2).comp s
        ((differentiableAt_id).const_mul (2 : ℂ))).mul
        (invZeta_differentiableAt_RH hRH (by linarith)))
    (fun s hs => by
      rw [norm_mul, mul_assoc]
      exact mul_le_mul (zeta_norm_le_of_re hε'0 (h2s s hs)) (hb s hs) (norm_nonneg _) hZ0)
    hx
  rw [← hK] at key
  have hset : Finset.range (⌊x⌋.toNat + 1) = Finset.Iic ⌊x⌋₊ := by
    rw [Int.floor_toNat]; ext n; simp
  have hM : |LiouvilleSum x| = ‖∑ n ∈ Finset.Iic ⌊x⌋₊, (Liouville n : ℂ)‖ := by
    have e : ((LiouvilleSum x : ℝ) : ℂ) = ∑ n ∈ Finset.Iic ⌊x⌋₊, (Liouville n : ℂ) := by
      rw [LiouvilleSum, hset]; push_cast; rfl
    rw [← e, Complex.norm_real, Real.norm_eq_abs]
  rw [hM]
  refine key.trans ?_
  have : x ^ (1 / 2 + ε' / 2 + ε' / 2) ≤ x ^ (1 / 2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  gcongr

/-- Source `RH_iff_Mertens_Growth`, unconditional. -/
theorem RH_iff_Mertens_Growth' :
    RiemannHypothesis' ↔
      ∀ ε : ℝ, ε > 0 → ∃ C > 0, ∀ x ≥ 1, |Kerr.File14RHExtra.Mertens x| ≤ C * x ^ (1 / 2 + ε) :=
  Kerr.File14RHExtra.RH_iff_Mertens_Growth RH_implies_Mertens_growth

/-- Source `RH_iff_Liouville_Growth`, unconditional. -/
theorem RH_iff_Liouville_Growth' :
    RiemannHypothesis' ↔
      ∀ ε : ℝ, ε > 0 → ∃ C > 0, ∀ x ≥ 1,
        |Kerr.File14RHExtra.LiouvilleSum x| ≤ C * x ^ (1 / 2 + ε) :=
  Kerr.File14RHExtra.RH_iff_Liouville_Growth RH_implies_Liouville_growth

end Kerr.Littlewood
