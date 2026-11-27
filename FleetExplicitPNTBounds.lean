import FleetExplicitPNTKernel
import HorizontalVanishingSeq
import LeftLineBound
import ZeroSumLimit
import FleetLowZeroFree
import FleetGammaGrowth
import FleetTangentBound
import FunctionalEqLogDeriv
import ZetaGrowthEM3

/-!
# Explicit numerical inputs for the explicit-constant prime number theorem

All unconditional (no hypothesis on the zeros).

* `B_le`: the horizontal-segment constant `HorizontalVanishingSeq.B` is `≤ 26000`.
* `norm_logDeriv_zeta_left_le`: `‖ζ'/ζ(−1/2 + it)‖ ≤ 30 + 2 log(5/2 + |t|)` for **every** real `t`
  (functional equation `FunctionalEqLogDeriv.logDeriv_zeta_one_sub` at `s = 3/2 − it`, the digamma
  bound `FleetGammaGrowth.norm_digamma_le`, `|tan(3π/4 + iy)| ≤ 2`, `∑ Λ(n) n^{-3/2} ≤ 20`).
* `sum_zetaOrder_low_le`: at most `35` zeros (with multiplicity) with `|Im ρ − T₀| ≤ 3/2`,
  `|T₀| = 3` (Jensen on the disc of centre `3/2 + T₀ i`, radius `29/10`, with the growth bound
  `ZetaGrowthEM3.norm_zeta_le_split₄` at `N = 1`).
* `sum_inv_Icc_le_log`: `∑_{k=4}^{K} 1/k ≤ log K`.
* `sum_zetaOrder_div_norm_le`: `∑_{|Im ρ| ≤ T} m(ρ)/|ρ| ≤ 47 + 600 log² T` for `T ≥ 4`.
-/

noncomputable section
open Complex Filter Topology Set Metric Reduction PrincipalPartDischarge
open scoped Real

namespace FleetExplicitPNTBounds

/-! ## The horizontal constant -/

theorem B_le : HorizontalVanishingSeq.B ≤ 26000 := by
  have hΛ := LeftLineBound.log_const_le
  have hΛ0 := HorizontalVanishingSeq.Λ₀_nonneg
  have hK : ZeroDensity.K 7 ≤ 44 := by
    unfold ZeroDensity.K
    have h10 : Real.log (7 + 3) ≤ 4 * Real.log 2 := by
      calc Real.log (7 + 3) ≤ Real.log (2 ^ 4) := Real.log_le_log (by norm_num) (by norm_num)
        _ = 4 * Real.log 2 := by rw [Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  have hK0 := ZeroAvoidingHeights.K7_nonneg
  unfold HorizontalVanishingSeq.B
  unfold SegmentBoundUnconditional.Λ₀ at hΛ0 ⊢
  generalize Real.log (3 + 12 * (2 : ℝ) ^ (4 : ℝ)) + 4 + 3 = L at hΛ hΛ0 ⊢
  generalize ZeroDensity.K 7 = K at hK hK0 ⊢
  nlinarith

/-! ## `ζ'/ζ` on the left line `Re s = −1/2`, every height -/

lemma norm_tan_three_halves (t : ℝ) :
    Complex.cos (π * ((3 / 2 : ℂ) + (-t : ℝ) * I) / 2) ≠ 0 ∧
      ‖Complex.tan (π * ((3 / 2 : ℂ) + (-t : ℝ) * I) / 2)‖ ≤ 2 := by
  set z : ℂ := π * ((3 / 2 : ℂ) + (-t : ℝ) * I) / 2 with hz
  have hre : z.re = 3 * π / 4 := by simp [hz]; ring
  have hcos2 : Real.cos z.re ^ 2 = 1 / 2 := by
    rw [hre, show 3 * π / 4 = π - π / 4 by ring, Real.cos_pi_sub, neg_sq, Real.cos_pi_div_four,
      div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hc := FleetTangentBound.norm_cos_sq z
  have hs := FleetTangentBound.norm_sin_sq z
  have hsin1 : Real.sin z.re ^ 2 ≤ 1 := Real.sin_sq_le_one _
  have hcpos : 0 < ‖Complex.cos z‖ := by
    have : 0 < ‖Complex.cos z‖ ^ 2 := by rw [hc, hcos2]; positivity
    exact lt_of_le_of_ne (norm_nonneg _) (fun h => by rw [← h] at this; simp at this)
  refine ⟨fun h => by rw [h, norm_zero] at hcpos; exact lt_irrefl _ hcpos, ?_⟩
  have hb : ‖Complex.sin z‖ ≤ 2 * ‖Complex.cos z‖ := by
    have hsq : ‖Complex.sin z‖ ^ 2 ≤ (2 * ‖Complex.cos z‖) ^ 2 := by
      rw [mul_pow, hc, hs, hcos2]; nlinarith [sq_nonneg (Real.sinh z.im)]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
  rw [Complex.tan, norm_div]
  exact (div_le_iff₀ hcpos).mpr hb

/-- **Left line, every height.** `‖ζ'/ζ(−1/2 + it)‖ ≤ 30 + 2 log(5/2 + |t|)` for every real `t`. -/
theorem norm_logDeriv_zeta_left_le (t : ℝ) :
    ‖deriv riemannZeta (-1 / 2 + t * I) / riemannZeta (-1 / 2 + t * I)‖ ≤
      30 + 2 * Real.log (5 / 2 + |t|) := by
  set s : ℂ := (3 / 2 : ℂ) + (-t : ℝ) * I with hs
  have hsre : s.re = 3 / 2 := by simp [hs]
  have h1s : 1 - s = -1 / 2 + t * I := by rw [hs]; push_cast; ring
  have hsn : ∀ n : ℕ, s ≠ -n := by
    intro n h; have := congrArg Complex.re h; rw [hsre] at this; simp at this
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hs0 : s ≠ 0 := by intro h; have := congrArg Complex.re h; rw [hsre] at this; simp at this
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hsre] at this; norm_num at this
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by rw [hsre]; norm_num)
  obtain ⟨hcos, htan⟩ := norm_tan_three_halves t
  have key := FunctionalEqLogDeriv.logDeriv_zeta_one_sub hsn hs0 hs1 hζ hcos
  rw [h1s] at key
  have e : deriv riemannZeta (-1 / 2 + t * I) / riemannZeta (-1 / 2 + t * I) =
      -(-(Real.log (2 * π) : ℂ) + deriv Complex.Gamma s / Complex.Gamma s
        - ((π : ℂ) / 2) * Complex.tan (π * s / 2) + deriv riemannZeta s / riemannZeta s) := by
    rw [← key, neg_neg]
  rw [e, norm_neg]
  -- the four pieces
  have hlog2pi : ‖(Real.log (2 * π) : ℂ)‖ ≤ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by
      nlinarith [Real.pi_gt_three]))]
    rw [Real.log_le_iff_le_exp (by positivity)]
    have he := Real.exp_one_gt_d9
    have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h2]
    nlinarith [Real.pi_lt_d2]
  have hγ : |Real.eulerMascheroniConstant| ≤ 1 := by
    rw [abs_le]
    constructor
    · linarith [Real.one_half_lt_eulerMascheroniConstant]
    · linarith [Real.eulerMascheroniConstant_lt_two_thirds]
  have hdg := FleetGammaGrowth.norm_digamma_le (z := s) (δ := 1) one_pos le_rfl
    (by rw [hsre]; norm_num)
  have hs1n : ‖s - 1‖ ≤ 1 / 2 + |t| := by
    have : s - 1 = ((1 / 2 : ℝ) : ℂ) + (-t : ℝ) * I := by rw [hs]; push_cast; ring
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, norm_mul, Complex.norm_real, norm_I, mul_one, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hlogs : Real.log (2 + ‖s - 1‖) ≤ Real.log (5 / 2 + |t|) :=
    Real.log_le_log (by positivity) (by linarith)
  have hdg' : ‖deriv Complex.Gamma s / Complex.Gamma s‖ ≤ 4 + 2 * Real.log (5 / 2 + |t|) := by
    refine hdg.trans ?_
    norm_num
    linarith
  have hzt : ‖deriv riemannZeta s / riemannZeta s‖ ≤ 20 := by
    have := ZetaGrowth.norm_logDeriv_zeta_le_of_re_ge (ε := 1 / 2) (by norm_num) (s := s)
      (by rw [hsre]; norm_num)
    rw [show (1 + 1 / 2 : ℝ) = 3 / 2 by norm_num] at this
    exact this.trans FleetExplicitPNTKernel.S32_le
  have htn : ‖((π : ℂ) / 2) * Complex.tan (π * s / 2)‖ ≤ 4 := by
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Complex.norm_two]
    have hp := Real.pi_lt_d2
    calc π / 2 * ‖Complex.tan (π * s / 2)‖ ≤ π / 2 * 2 := by gcongr
      _ ≤ 4 := by linarith
  calc ‖-(Real.log (2 * π) : ℂ) + deriv Complex.Gamma s / Complex.Gamma s
        - ((π : ℂ) / 2) * Complex.tan (π * s / 2) + deriv riemannZeta s / riemannZeta s‖
      ≤ ‖(Real.log (2 * π) : ℂ)‖ + ‖deriv Complex.Gamma s / Complex.Gamma s‖
        + ‖((π : ℂ) / 2) * Complex.tan (π * s / 2)‖ + ‖deriv riemannZeta s / riemannZeta s‖ := by
        refine (norm_add_le _ _).trans ?_
        refine add_le_add_left ((norm_sub_le _ _).trans ?_) _
        refine add_le_add_left ((norm_add_le _ _).trans ?_) _
        rw [norm_neg]
    _ ≤ 2 + (4 + 2 * Real.log (5 / 2 + |t|)) + 4 + 20 := by gcongr
    _ = 30 + 2 * Real.log (5 / 2 + |t|) := by ring

/-! ## Low zeros: `|Im ρ| < 4` -/

open scoped Classical in
/-- **Low zero count.** For `|T₀| = 3` and any finite set `Z` of nontrivial zeros with
`|Im ρ − T₀| ≤ 3/2`, `∑ ρ ∈ Z, zetaOrder ρ ≤ 35`. -/
theorem sum_zetaOrder_low_le (T₀ : ℝ) (hT₀ : |T₀| = 3) (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, IsNontrivialZero ρ ∧ |ρ.im - T₀| ≤ 3 / 2) :
    ∑ ρ ∈ Z, (zetaOrder ρ : ℝ) ≤ 35 := by
  set c : ℂ := 3 / 2 + T₀ * I with hc
  have hcre : c.re = 3 / 2 := by simp [hc]
  have hcim : c.im = T₀ := by simp [hc]
  have hmem : ∀ z ∈ ball c (29 / 10), |z.re - 3 / 2| < 29 / 10 ∧ |z.im - T₀| < 29 / 10 := by
    intro z hz
    have hz' : ‖z - c‖ < 29 / 10 := mem_ball_iff_norm.mp hz
    constructor
    · calc |z.re - 3 / 2| = |(z - c).re| := by rw [Complex.sub_re, hcre]
        _ ≤ ‖z - c‖ := Complex.abs_re_le_norm _
        _ < 29 / 10 := hz'
    · calc |z.im - T₀| = |(z - c).im| := by rw [Complex.sub_im, hcim]
        _ ≤ ‖z - c‖ := Complex.abs_im_le_norm _
        _ < 29 / 10 := hz'
  have him : ∀ z ∈ ball c (29 / 10), 1 / 10 < |z.im| := by
    intro z hz
    have h1 := (hmem z hz).2
    have h2 := abs_sub_abs_le_abs_sub T₀ z.im
    rw [abs_sub_comm T₀ z.im] at h2
    linarith
  have hne1 : ∀ z ∈ ball c (29 / 10), z ≠ 1 := by
    intro z hz h1
    have := him z hz
    rw [h1, Complex.one_im, abs_zero] at this
    linarith
  have hf : DifferentiableOn ℂ riemannZeta (ball c (29 / 10)) := fun z hz =>
    (differentiableAt_riemannZeta (hne1 z hz)).differentiableWithinAt
  have h1K : (1 : ℂ) ∉ closedBall c (29 / 10) := by
    intro h
    have h' : ‖(1 : ℂ) - c‖ ≤ 29 / 10 := mem_closedBall_iff_norm.mp h
    have : |T₀| ≤ 29 / 10 := by
      calc |T₀| = |((1 : ℂ) - c).im| := by
            rw [Complex.sub_im, Complex.one_im, hcim, zero_sub, abs_neg]
        _ ≤ ‖(1 : ℂ) - c‖ := Complex.abs_im_le_norm _
        _ ≤ 29 / 10 := h'
    linarith
  have hfin : {z ∈ ball c (29 / 10) | riemannZeta z = 0}.Finite :=
    (FiniteZeros.finite_zeros_of_isCompact (isCompact_closedBall c (29 / 10)) h1K).subset
      (fun z hz => ⟨ball_subset_closedBall hz.1, hz.2⟩)
  have hM : ∀ z ∈ ball c (29 / 10), ‖riemannZeta z‖ ≤ 200 := by
    intro z hz
    obtain ⟨hzre, hzim⟩ := hmem z hz
    have hzre' := abs_lt.mp hzre
    have h := ZetaGrowthEM3.norm_zeta_le_split₄ (s := z) (by linarith) (hne1 z hz) (N := 1) le_rfl
    norm_num at h
    have hz1 : 1 / 10 ≤ ‖z - 1‖ := by
      have := Complex.abs_im_le_norm (z - 1)
      rw [Complex.sub_im, Complex.one_im, sub_zero] at this
      linarith [him z hz]
    have hzn : ‖z‖ ≤ 8 := by
      have h1 : ‖c‖ ≤ 9 / 2 := by
        refine (Complex.norm_le_abs_re_add_abs_im c).trans ?_
        rw [hcre, hcim, hT₀]; norm_num
      have h2 : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by
        have := norm_add_le (z - c) c; rwa [sub_add_cancel] at this
      have h3 : ‖z - c‖ < 29 / 10 := mem_ball_iff_norm.mp hz
      linarith
    have hn1 : ‖z + 1‖ ≤ 9 := by
      have := norm_add_le z 1; rw [norm_one] at this; linarith
    have hn2 : ‖z + 2‖ ≤ 10 := by
      have := norm_add_le z 2; rw [Complex.norm_two] at this; linarith
    have hn3 : ‖z + 3‖ ≤ 11 := by
      have := norm_add_le z 3
      rw [show ‖(3 : ℂ)‖ = 3 by simp] at this; linarith
    have hinv : 16 / ‖z - 1‖ ≤ 160 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hp3 : ‖z‖ * ‖z + 1‖ * ‖z + 2‖ ≤ 720 := by
      have := mul_le_mul (mul_le_mul hzn hn1 (norm_nonneg _) (by norm_num)) hn2 (norm_nonneg _)
        (by norm_num)
      linarith
    have hp4 : ‖z‖ * ‖z + 1‖ * ‖z + 2‖ * ‖z + 3‖ ≤ 7920 := by
      have := mul_le_mul hp3 hn3 (norm_nonneg _) (by norm_num)
      linarith
    have hn0 := norm_nonneg z
    linarith
  have hζc : 1 / 3 ≤ ‖riemannZeta c‖ := ZeroDensityUnconditional.hlow T₀
  have hfc : riemannZeta c ≠ 0 := by
    intro h; rw [h, norm_zero] at hζc; norm_num at hζc
  have hlogc : -Real.log 3 ≤ Real.log ‖riemannZeta c‖ := by
    have := Real.log_le_log (by norm_num) hζc
    rwa [one_div, Real.log_inv] at this
  have hord : ∀ b ∈ ball c (29 / 10), riemannZeta b = 0 → ∃ G : ℂ → ℂ, AnalyticAt ℂ G b ∧
      G b ≠ 0 ∧ ∀ᶠ z in 𝓝 b, riemannZeta z = (z - b) ^ zetaOrder b * G z :=
    fun b hb _ => exists_factorization (hne1 b hb)
  have hJ := ZeroSumLimit.sum_order_mul_log_le_of_jensen' (c := c) (R₀ := 11 / 4)
    (R' := 29 / 10) (r := 11 / 5) (M := 200) (by norm_num) (by norm_num) (by norm_num) hf hfin
    hM hfc zetaOrder hord
  have hsub : Z ⊆ hfin.toFinset.filter (fun b => b ∈ closedBall c (11 / 5)) := by
    intro ρ hρ
    obtain ⟨hρz, hρim⟩ := hZ ρ hρ
    obtain ⟨hre0, hre1⟩ := ZetaStrip.mem_strip_of_isNontrivialZero hρz
    have hnorm : ‖ρ - c‖ ≤ 11 / 5 := by
      apply ZeroDensity.norm_le_of_re_im (by norm_num)
      rw [Complex.sub_re, Complex.sub_im, hcre, hcim]
      have h1 : (ρ.re - 3 / 2) ^ 2 ≤ 9 / 4 := by
        nlinarith [mul_pos hre0 (by linarith : (0 : ℝ) < 3 - ρ.re)]
      have h2 : (ρ.im - T₀) ^ 2 ≤ 9 / 4 := by
        have := abs_le.mp hρim
        nlinarith
      nlinarith [h1, h2]
    rw [Finset.mem_filter, Set.Finite.mem_toFinset]
    refine ⟨⟨?_, hρz.1⟩, ?_⟩
    · rw [mem_ball_iff_norm]; linarith
    · exact mem_closedBall_iff_norm.mpr hnorm
  have hsum_le : ∑ ρ ∈ Z, (zetaOrder ρ : ℝ)
      ≤ ∑ ρ ∈ hfin.toFinset.filter (fun b => b ∈ closedBall c (11 / 5)), (zetaOrder ρ : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
  have hlogr : (1 : ℝ) / 5 ≤ Real.log (11 / 4 / (11 / 5)) := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 11 / 4 / (11 / 5))
    norm_num at this ⊢
    linarith
  have hlog600 : Real.log 200 + Real.log 3 ≤ 7 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    calc Real.log (200 * 3) ≤ Real.log (2 ^ 10) := Real.log_le_log (by norm_num) (by norm_num)
      _ = 10 * Real.log 2 := by rw [Real.log_pow]; norm_num
      _ ≤ 7 := by linarith [Real.log_two_lt_d9]
  set S : ℝ := ∑ ρ ∈ hfin.toFinset.filter (fun b => b ∈ closedBall c (11 / 5)), (zetaOrder ρ : ℝ)
    with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hS1 : S * (1 / 5) ≤ S * Real.log (11 / 4 / (11 / 5)) :=
    mul_le_mul_of_nonneg_left hlogr hS0
  linarith

/-! ## `∑_{k=4}^{K} 1/k ≤ log K` -/

theorem sum_inv_Icc_le_log (K : ℕ) (hK : 3 ≤ K) :
    ∑ k ∈ Finset.Icc 4 K, (1 / (k : ℝ)) ≤ Real.log K := by
  induction K, hK using Nat.le_induction with
  | base =>
    rw [Finset.Icc_eq_empty (by norm_num), Finset.sum_empty]
    exact Real.log_nonneg (by norm_num)
  | succ K hK ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    have h1 := Real.one_sub_inv_le_log_of_pos (x := ((K : ℝ) + 1) / K) (by positivity)
    rw [Real.log_div (by positivity) hK0.ne', inv_div] at h1
    have h2 : 1 - (K : ℝ) / (K + 1) = 1 / ((K : ℝ) + 1) := by field_simp; ring
    push_cast
    linarith

/-! ## The zero sum `∑ m(ρ)/|ρ|` -/

open scoped Classical in
/-- **Zero sum.** For `T ≥ 4`, `∑_{ρ ∈ zeroFinset (3/2) T} m(ρ)/|ρ| ≤ 47 + 600 log² T`. -/
theorem sum_zetaOrder_div_norm_le {T : ℝ} (hT : 4 ≤ T) :
    ∑ ρ ∈ zeroFinset (3 / 2) T, (zetaOrder ρ : ℝ) / ‖ρ‖ ≤ 47 + 600 * Real.log T ^ 2 := by
  set Z := zeroFinset (3 / 2) T with hZdef
  have hZ : ∀ ρ ∈ Z, IsNontrivialZero ρ ∧ |ρ.im| ≤ T := fun ρ hρ =>
    (ZeroSumLimit.mem_zeroFinset_three_halves (by linarith)).mp hρ
  have hlow : ∀ ρ ∈ Z, 3 / 2 < |ρ.im| := by
    intro ρ hρ
    by_contra h
    push Not at h
    obtain ⟨h0, h1⟩ := ZetaStrip.mem_strip_of_isNontrivialZero (hZ ρ hρ).1
    exact FleetLowZeroFree.zeta_ne_zero_low h0 h1 h (hZ ρ hρ).1.1
  have hnorm : ∀ ρ : ℂ, |ρ.im| ≤ ‖ρ‖ := fun ρ => Complex.abs_im_le_norm ρ
  rw [← Finset.sum_filter_add_sum_filter_not Z (fun ρ => |ρ.im| < 4)]
  have hA : ∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < 4), (zetaOrder ρ : ℝ) / ‖ρ‖ ≤ 47 := by
    have hterm : ∀ ρ ∈ Z.filter (fun ρ => |ρ.im| < 4),
        (zetaOrder ρ : ℝ) / ‖ρ‖ ≤ 2 / 3 * (zetaOrder ρ : ℝ) := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      have h1 := hlow ρ hρ.1
      have h2 := hnorm ρ
      rw [div_le_iff₀ (by linarith)]
      have := Nat.cast_nonneg (α := ℝ) (zetaOrder ρ)
      nlinarith
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    set W := Z.filter (fun ρ => |ρ.im| < 4)
    rw [← Finset.sum_filter_add_sum_filter_not W (fun ρ => 0 ≤ ρ.im)]
    have hP := sum_zetaOrder_low_le 3 (by norm_num) (W.filter (fun ρ => 0 ≤ ρ.im)) (by
      intro ρ hρ
      rw [Finset.mem_filter, Finset.mem_filter] at hρ
      obtain ⟨⟨hρZ, h4⟩, hpos⟩ := hρ
      refine ⟨(hZ ρ hρZ).1, ?_⟩
      have h1 := hlow ρ hρZ
      rw [abs_of_nonneg hpos] at h1 h4
      rw [abs_le]; constructor <;> linarith)
    have hN := sum_zetaOrder_low_le (-3) (by norm_num) (W.filter (fun ρ => ¬ 0 ≤ ρ.im)) (by
      intro ρ hρ
      rw [Finset.mem_filter, Finset.mem_filter] at hρ
      obtain ⟨⟨hρZ, h4⟩, hneg⟩ := hρ
      push Not at hneg
      refine ⟨(hZ ρ hρZ).1, ?_⟩
      have h1 := hlow ρ hρZ
      rw [abs_of_neg hneg] at h1 h4
      rw [abs_le]; constructor <;> linarith)
    linarith
  have hB : ∑ ρ ∈ Z.filter (fun ρ => ¬ |ρ.im| < 4), (zetaOrder ρ : ℝ) / ‖ρ‖ ≤
      600 * Real.log T ^ 2 := by
    set K := ⌊T⌋₊ with hKdef
    have hT0 : 0 ≤ T := by linarith
    have hK4 : 4 ≤ K := by rw [hKdef]; exact Nat.le_floor (by exact_mod_cast hT)
    have hKT : (K : ℝ) ≤ T := Nat.floor_le hT0
    set W := Z.filter (fun ρ => ¬ |ρ.im| < 4) with hW
    have hmaps : ∀ ρ ∈ W, ⌊|ρ.im|⌋₊ ∈ Finset.Icc 4 K := by
      intro ρ hρ
      rw [hW, Finset.mem_filter] at hρ
      push Not at hρ
      rw [Finset.mem_Icc]
      exact ⟨Nat.le_floor (by exact_mod_cast hρ.2), Nat.floor_le_floor (hZ ρ hρ.1).2⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    have hlogK : Real.log K ≤ Real.log T :=
      Real.log_le_log (by exact_mod_cast (show 0 < K by omega)) hKT
    have hlogK0 : 0 ≤ Real.log K := Real.log_nonneg (by exact_mod_cast (show 1 ≤ K by omega))
    have hfib : ∀ k ∈ Finset.Icc 4 K,
        ∑ ρ ∈ W.filter (fun ρ => ⌊|ρ.im|⌋₊ = k), (zetaOrder ρ : ℝ) / ‖ρ‖ ≤
          600 * Real.log K * (1 / (k : ℝ)) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hmem : ∀ ρ ∈ W.filter (fun ρ => ⌊|ρ.im|⌋₊ = k),
          IsNontrivialZero ρ ∧ (k : ℝ) ≤ |ρ.im| ∧ |ρ.im| < k + 1 := by
        intro ρ hρ
        rw [Finset.mem_filter, hW, Finset.mem_filter] at hρ
        obtain ⟨⟨hρZ, -⟩, hfl⟩ := hρ
        refine ⟨(hZ ρ hρZ).1, ?_, ?_⟩
        · rw [← hfl]; exact Nat.floor_le (abs_nonneg _)
        · rw [← hfl]; exact Nat.lt_floor_add_one _
      have hterm : ∀ ρ ∈ W.filter (fun ρ => ⌊|ρ.im|⌋₊ = k),
          (zetaOrder ρ : ℝ) / ‖ρ‖ ≤ (zetaOrder ρ : ℝ) * (1 / (k : ℝ)) := by
        intro ρ hρ
        have h1 := (hmem ρ hρ).2.1
        have h2 := hnorm ρ
        rw [mul_one_div]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hk0 (by linarith)
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.sum_mul]
      have hband := ZeroSumLimit.sum_zetaOrder_band_le k hk.1 _ hmem
      have hlk : Real.log k ≤ Real.log K :=
        Real.log_le_log hk0 (by exact_mod_cast hk.2)
      have hk1 : 0 ≤ 1 / (k : ℝ) := by positivity
      calc (∑ ρ ∈ W.filter (fun ρ => ⌊|ρ.im|⌋₊ = k), (zetaOrder ρ : ℝ)) * (1 / (k : ℝ))
          ≤ (600 * Real.log k) * (1 / (k : ℝ)) := by gcongr
        _ ≤ 600 * Real.log K * (1 / (k : ℝ)) := by gcongr
    refine (Finset.sum_le_sum hfib).trans ?_
    rw [← Finset.mul_sum]
    have hH := sum_inv_Icc_le_log K (by omega)
    calc 600 * Real.log K * ∑ k ∈ Finset.Icc 4 K, (1 / (k : ℝ))
        ≤ 600 * Real.log K * Real.log K := by gcongr
      _ ≤ 600 * Real.log T * Real.log T := by
          have : 0 ≤ 600 * Real.log T := by linarith
          gcongr
      _ = 600 * Real.log T ^ 2 := by ring
  linarith

end FleetExplicitPNTBounds
