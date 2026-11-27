import OffLineDetection
import ZeroSymmetry

/-!
# Danesh's two-interval criterion for RH

Source: Payam Danesh, *A quantitative two-interval criterion for the Riemann hypothesis*,
arXiv:2611.10726 (7 Nov 2026). Section and equation numbers below refer to that paper.

## The paper's statement

For `f ∈ C_c^∞(ℝ; ℂ)` put `H f (z) = ∫ f(x) e^{zx} dx` and `z_ρ = ρ - 1/2` (eq. (1)), and let
`B(f, g) = ∑_ρ H f (z_ρ) · conj (H g (-conj z_ρ))`, `Q f = B(f, f)` (eq. (2)), zeros with
multiplicity. Fix a width function `w` with `w(L) → 0` and `log (1/w(L)) = o(L)` (eq. (12)), and call
`(f, g)` admissible at span `L` if they are nonzero and supported in `[0, w(L)]` and
`[L - w(L), L]` (eq. (13)); `R(f, g) = |B(f, g)| / √(Q f · Q g)` (eq. (14)). Theorem 4:
"If the Riemann hypothesis (RH) holds, then R(f, g) ≤ 1 for every admissible complex pair at every
sufficiently large L", and if `ρ₀ = β + iγ` is a zero with `β > 1/2`, then for every
`0 < η < β - 1/2` and every `L₀` there are `L > L₀` and a real admissible pair with
`R(f, g) > e^{ηL}`; "Consequently the RH is equivalent to R(f, g) ≤ 1 for all real admissible pairs
at all sufficiently large L."

## What is formalized here

The bound is stated multiplicatively (`TwoIntervalBound w η`):
`‖B(φ, ψ)‖² ≤ e^{2ηL} ‖Q φ‖ ‖Q ψ‖` for all real admissible pairs at all large spans. Where
`Q φ, Q ψ > 0` this is `R(φ, ψ) ≤ e^{ηL}`; the paper's Lemma 1 (positivity of `Q` on short supports)
is what makes `R` defined, and the multiplicative form does not need it.

* `twoIntervalBound_of_RH` : RH ⇒ the bound with `η = 0`, for every `w` (Theorem 4(1));
  `cs_of_RH` gives `‖B f g‖² ≤ Re Q f · Re Q g` under RH for every pair with decaying transforms.
* `abs_re_sub_half_le_of_twoInterval` : the bound with allowance `e^{ηL}` (`η ≥ 0`) confines every
  zero to `|Re ρ - 1/2| ≤ η` (quantitative form of Theorem 4(2)).
* `violation_of_offline_zero` : Theorem 4(2) as stated in the paper (with `0 ≤ η`).
* `RH_iff_twoInterval` : RH ⇔ `TwoIntervalBound w 0`, for every width function (Theorem 4).
* `widthFn_inv`, `RH_iff_twoInterval_inv` : the reciprocal width `w(L) = 1/L`.

## Route

* Lemma 2 (localization): `growth_of_twoInterval`. The paper's smooth partition is used, with a
  coarser cost: each piece `u_j` has `|Q u_j| ≤ K m²` from one integration by parts and the zero-count
  input `∑_ρ 1/(1+γ²) < ∞` (`OffLineDetection.summable_inv_one_add_sq_re`), instead of the paper's
  `log m / m`; the total cost `O(m⁴)` is still `e^{o(t)}` under `log (1/w) = o(L)`.
* Lemma 3 (pole obstruction): replaced by `fiber_sum_eq_zero_of_growth`, proved with Laplace moments
  `∫₀^∞ t^n e^{-pt} G(t) dt = n! ∑ c_i (p - w_i)^{-n-1}` at a point `p` to the right of the strip,
  and a Cesàro argument on the finitely many nearest frequencies. No meromorphic continuation is used.
* The explicit formula is not used: both directions of Theorem 4 concern the zero side only.

Not formalized: Lemma 1, Corollary 5, the explicit formula (7) and the arithmetic form (36).
-/

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Filter Topology Set
open scoped Real ContDiff
open Reduction ZeroSumLimit

namespace FleetDaneshCriterion

/-! ## Part I: pure analysis — Laplace moments and the exponential-sum obstruction -/

/-- `t^k e^{-b t}` is integrable on `(0, ∞)` for `b > 0`. -/
lemma integrableOn_pow_mul_exp_neg (k : ℕ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-(b * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (k : ℝ)) (b := b)
    (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith) one_pos hb
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only [Real.rpow_one, Real.rpow_natCast, neg_mul]

/-- The complex version: `t^k e^{-λ t}` is integrable on `(0, ∞)` for `Re λ > 0`. -/
lemma integrableOn_cpow_mul_cexp_neg (k : ℕ) {l : ℂ} (hl : 0 < l.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ k * cexp (-(l * t))) (Ioi 0) := by
  refine (integrableOn_pow_mul_exp_neg k hl).mono' ?_ ?_
  · exact (by fun_prop : Continuous (fun t : ℝ => (t : ℂ) ^ k * cexp (-(l * t)))).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, Complex.norm_exp]
    simp

/-- **Real moments.** `∫₀^∞ t^n e^{-b t} dt = n! / b^{n+1}` for `b > 0`. -/
lemma integral_pow_mul_exp_neg (n : ℕ) {b : ℝ} (hb : 0 < b) :
    ∫ t in Ioi (0 : ℝ), t ^ n * Real.exp (-(b * t)) = n.factorial / b ^ (n + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ) + 1) (r := b)
    (by positivity) hb
  have e1 : ∫ t in Ioi (0 : ℝ), t ^ n * Real.exp (-(b * t))
      = ∫ t in Ioi (0 : ℝ), t ^ ((n : ℝ) + 1 - 1) * Real.exp (-(b * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [add_sub_cancel_right, Real.rpow_natCast]
  rw [e1, h, Real.Gamma_nat_eq_factorial]
  rw [show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, one_div,
    inv_pow]
  ring

/-- **Complex moments.** `∫₀^∞ t^n e^{-λ t} dt = n! / λ^{n+1}` for `Re λ > 0`. -/
lemma integral_cpow_mul_cexp_neg (n : ℕ) {l : ℂ} (hl : 0 < l.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * cexp (-(l * t)) = n.factorial / l ^ (n + 1) := by
  have hl0 : l ≠ 0 := by intro h; rw [h] at hl; simp at hl
  induction n with
  | zero =>
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
    have h := integral_exp_mul_complex_Ioi (a := -l) (by simpa using hl) 0
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at h
    rw [show (fun t : ℝ => cexp (-(l * t))) = fun t : ℝ => cexp (-l * t) by
      funext t; ring_nf]
    rw [h]; field_simp
  | succ n ih =>
    -- integration by parts with `u = t^{n+1}`, `v = -e^{-λt}/λ`
    have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => (t : ℂ) ^ (n + 1))
        (((n + 1 : ℕ) : ℂ) * (x : ℂ) ^ n) x := by
      intro x _
      have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
        simpa using (hasDerivAt_id (x : ℝ)).ofReal_comp
      have := h0.pow (n + 1)
      convert this using 1
      push_cast
      simp
    have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => -cexp (-(l * t)) / l)
        (cexp (-(l * x))) x := by
      intro x _
      have h1 : HasDerivAt (fun t : ℝ => -(l * (t : ℂ))) (-(l * 1)) x :=
        ((hasDerivAt_id (x : ℝ)).ofReal_comp.const_mul l).neg
      have h2 := (h1.cexp).neg.div_const l
      convert h2 using 1
      field_simp
    have hI1 := integrableOn_cpow_mul_cexp_neg (n + 1) hl
    have hI0 := integrableOn_cpow_mul_cexp_neg n hl
    have huv' : IntegrableOn ((fun t : ℝ => (t : ℂ) ^ (n + 1)) * fun t : ℝ => cexp (-(l * t)))
        (Ioi 0) := hI1
    have hu'v : IntegrableOn ((fun t : ℝ => ((n + 1 : ℕ) : ℂ) * (t : ℂ) ^ n) *
        fun t : ℝ => -cexp (-(l * t)) / l) (Ioi 0) := by
      have := (hI0.const_mul (-(((n + 1 : ℕ) : ℂ)) / l))
      refine IntegrableOn.congr_fun this (fun t _ => ?_) measurableSet_Ioi
      simp only [Pi.mul_apply]
      field_simp
    have hzero : Tendsto ((fun t : ℝ => (t : ℂ) ^ (n + 1)) * fun t : ℝ => -cexp (-(l * t)) / l)
        (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous ((fun t : ℝ => (t : ℂ) ^ (n + 1)) * fun t : ℝ => -cexp (-(l * t)) / l) := by
        fun_prop
      have := hc.tendsto 0
      simp only [Pi.mul_apply, Complex.ofReal_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero,
        and_false, not_false_eq_true, zero_pow, zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hinf : Tendsto ((fun t : ℝ => (t : ℂ) ^ (n + 1)) * fun t : ℝ => -cexp (-(l * t)) / l)
        atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hr := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((n + 1 : ℕ) : ℝ) l.re hl
      have hr' := hr.div_const ‖l‖
      rw [zero_div] at hr'
      refine hr'.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      simp only [Pi.mul_apply, norm_mul, norm_div, norm_neg, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos ht, Complex.norm_exp, Real.rpow_natCast]
      simp [Complex.mul_re]
      ring
    have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v hzero hinf
    rw [hibp]
    have e2 : ∫ x in Ioi (0 : ℝ), ((n + 1 : ℕ) : ℂ) * (x : ℂ) ^ n * (-cexp (-(l * x)) / l)
        = (-(((n + 1 : ℕ) : ℂ)) / l) * ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ n * cexp (-(l * x)) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
      field_simp
    rw [e2, ih, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- **Distinct unimodular frequencies cannot cancel.** If `∑_{a∈s} C a ω_a^n → 0` with the `ω_a`
distinct and of modulus one, every coefficient vanishes (Cesàro mean against `conj ω_{a₀}^n`). -/
lemma coeff_eq_zero_of_tendsto {α : Type*} [DecidableEq α] (s : Finset α) (om C : α → ℂ)
    (hinj : Set.InjOn om s) (hn : ∀ a ∈ s, ‖om a‖ = 1)
    (h : Tendsto (fun n : ℕ => ∑ a ∈ s, C a * om a ^ n) atTop (𝓝 0)) :
    ∀ a ∈ s, C a = 0 := by
  intro a0 ha0
  set u := om a0 with hu
  have hu1 : ‖u‖ = 1 := hn a0 ha0
  have huu : om a0 * (starRingEnd ℂ) u = 1 := by
    rw [← hu, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu1]; simp
  -- `b n = (∑ C a ω_a^n) · conj(u)^n → 0`
  set b : ℕ → ℂ := fun n => (∑ a ∈ s, C a * om a ^ n) * (starRingEnd ℂ) u ^ n with hb
  have hb0 : Tendsto b atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h' := (tendsto_zero_iff_norm_tendsto_zero.mp h)
    refine h'.congr (fun n => ?_)
    simp only [hb, norm_mul, norm_pow, Complex.norm_conj, hu1, one_pow, mul_one]
  have hces := hb0.cesaro_smul
  -- the Cesàro means, coefficientwise
  set m : α → ℕ → ℂ := fun a N => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, (om a * (starRingEnd ℂ) u) ^ n
    with hm
  have hsplit : ∀ N : ℕ, ((N : ℝ)⁻¹ • ∑ n ∈ Finset.range N, b n) = ∑ a ∈ s, C a * m a N := by
    intro N
    simp only [hb, hm, Complex.real_smul, Finset.sum_mul, Finset.mul_sum, mul_pow]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun n _ => by push_cast; ring))
  have hlim : ∀ a ∈ s, Tendsto (m a) atTop (𝓝 (if a = a0 then 1 else 0)) := by
    intro a ha
    by_cases hae : a = a0
    · rw [ite_eq_left_iff.mpr (fun h => absurd hae h)]
      subst hae
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      simp only [hm]
      rw [huu]
      simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
      field_simp
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hae)]
      set ζ := om a * (starRingEnd ℂ) u with hζ
      have hζ1 : ζ ≠ 1 := by
        intro h1
        apply hae
        apply hinj ha ha0
        have : om a * ((starRingEnd ℂ) u * u) = u := by rw [← mul_assoc, ← hζ, h1, one_mul]
        rw [mul_comm ((starRingEnd ℂ) u) u, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu1] at this
        simpa using this
      have hζn : ‖ζ‖ = 1 := by
        rw [hζ, norm_mul, Complex.norm_conj, hn a ha, hu1, one_mul]
      have hne : 0 < ‖ζ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hζ1)
      have hbd : ∀ N : ℕ, ‖m a N‖ ≤ (2 / ‖ζ - 1‖) * (N : ℝ)⁻¹ := by
        intro N
        simp only [hm]
        rw [geom_sum_eq hζ1, norm_mul, norm_div]
        have h2 : ‖ζ ^ N - 1‖ ≤ 2 := by
          calc ‖ζ ^ N - 1‖ ≤ ‖ζ ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ = 2 := by rw [norm_pow, hζn]; norm_num
        have hNn : ‖(N : ℂ)⁻¹‖ = (N : ℝ)⁻¹ := by
          rw [norm_inv, Complex.norm_natCast]
        rw [hNn]
        calc (N : ℝ)⁻¹ * (‖ζ ^ N - 1‖ / ‖ζ - 1‖) ≤ (N : ℝ)⁻¹ * (2 / ‖ζ - 1‖) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact div_le_div_of_nonneg_right h2 hne.le
          _ = _ := by ring
      have ht : Tendsto (fun N : ℕ => (2 / ‖ζ - 1‖) * (N : ℝ)⁻¹) atTop (𝓝 0) := by
        have := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (2 / ‖ζ - 1‖)
        simpa using this
      exact squeeze_zero_norm hbd ht
  have hsum : Tendsto (fun N => ∑ a ∈ s, C a * m a N) atTop
      (𝓝 (∑ a ∈ s, C a * (if a = a0 then 1 else 0))) :=
    tendsto_finsetSum s (fun a ha => (hlim a ha).const_mul (C a))
  rw [show (∑ a ∈ s, C a * (if a = a0 then (1 : ℂ) else 0)) = C a0 by
    simp [Finset.sum_ite_eq', ha0]] at hsum
  have hces' : Tendsto (fun N => ∑ a ∈ s, C a * m a N) atTop (𝓝 0) :=
    hces.congr (fun N => hsplit N)
  exact tendsto_nhds_unique hsum hces'

/-- **Moment identity.** For an absolutely summable exponential series with `Re w_i ≤ σ₀`
and `Re p > σ₀`, the `n`-th Laplace moment is `n! ∑ c_i / (p - w_i)^{n+1}`. -/
lemma moment_identity {ι : Type*} [Countable ι] (w c : ι → ℂ) {σ₀ : ℝ}
    (hw : ∀ i, (w i).re ≤ σ₀) (hc : Summable (fun i => ‖c i‖)) {p : ℂ} (hp : σ₀ < p.re) (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * cexp (-(p * t)) * ∑' i, c i * cexp (t * w i)
      = n.factorial * ∑' i, c i / (p - w i) ^ (n + 1) := by
  have hpos : ∀ i, 0 < (p - w i).re := fun i => by
    simp only [Complex.sub_re]; linarith [hw i]
  set F : ι → ℝ → ℂ := fun i t => c i * ((t : ℂ) ^ n * cexp (-((p - w i) * t))) with hF
  have hint : ∀ i, Integrable (F i) (volume.restrict (Ioi 0)) := fun i =>
    (integrableOn_cpow_mul_cexp_neg n (hpos i)).const_mul (c i)
  have hnormF : ∀ i, ∫ t in Ioi (0 : ℝ), ‖F i t‖
      = ‖c i‖ * (n.factorial / ((p - w i).re) ^ (n + 1)) := by
    intro i
    rw [← integral_pow_mul_exp_neg n (hpos i), ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [hF, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (show (0 : ℝ) < t from ht), Complex.norm_exp]
    congr 2
    simp [Complex.mul_re]
  have hsum : Summable (fun i => ∫ t in Ioi (0 : ℝ), ‖F i t‖) := by
    refine Summable.of_nonneg_of_le (fun i => integral_nonneg (fun t => norm_nonneg _))
      (fun i => ?_) (hc.mul_right (n.factorial / (p.re - σ₀) ^ (n + 1)))
    rw [hnormF i]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply div_le_div_of_nonneg_left (by positivity) (by have := sub_pos.mpr hp; positivity)
    apply pow_le_pow_left₀ (by linarith [sub_pos.mpr hp]) _ _
    simp only [Complex.sub_re]; linarith [hw i]
  have hswap := integral_tsum_of_summable_integral_norm hint hsum
  have hval : ∀ i, ∫ t in Ioi (0 : ℝ), F i t = n.factorial * (c i / (p - w i) ^ (n + 1)) := by
    intro i
    simp only [hF]
    rw [integral_const_mul, integral_cpow_mul_cexp_neg n (hpos i)]
    ring
  have hlhs : (fun t : ℝ => (t : ℂ) ^ n * cexp (-(p * t)) * ∑' i, c i * cexp (t * w i))
      = fun t => ∑' i, F i t := by
    funext t
    rw [← tsum_mul_left]
    refine tsum_congr (fun i => ?_)
    simp only [hF]
    have : cexp (-(p * t)) * cexp (t * w i) = cexp (-((p - w i) * t)) := by
      rw [← Complex.exp_add]; ring_nf
    rw [← this]; ring
  rw [hlhs, ← hswap]
  simp_rw [hval]
  rw [tsum_mul_left]

/-- **Moment bound.** If `‖G t‖ ≤ K e^{α t}` for `t ≥ 0` and `Re p > α`, the `n`-th moment is
at most `K n! / (Re p - α)^{n+1}`. -/
lemma moment_bound (G : ℝ → ℂ) {K α : ℝ} (hG : ∀ t, 0 ≤ t → ‖G t‖ ≤ K * Real.exp (α * t))
    {p : ℂ} (hp : α < p.re) (n : ℕ) :
    ‖∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * cexp (-(p * t)) * G t‖
      ≤ K * (n.factorial / (p.re - α) ^ (n + 1)) := by
  have hb : 0 < p.re - α := sub_pos.mpr hp
  rw [← integral_pow_mul_exp_neg n hb, ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((integrableOn_pow_mul_exp_neg n hb).const_mul K) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht0 : (0 : ℝ) < t := ht
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0,
    Complex.norm_exp]
  have hre : (-(p * (t : ℂ))).re = -(p.re * t) := by simp [Complex.mul_re]
  rw [hre]
  have h1 := hG t ht0.le
  have hK : 0 ≤ K := by
    have := (norm_nonneg (G t)).trans h1
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  calc t ^ n * Real.exp (-(p.re * t)) * ‖G t‖
      ≤ t ^ n * Real.exp (-(p.re * t)) * (K * Real.exp (α * t)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = K * (t ^ n * Real.exp (-((p.re - α) * t))) := by
        rw [show -((p.re - α) * t) = -(p.re * t) + α * t by ring, Real.exp_add]; ring

/-- **Exponential-sum obstruction** (the role of Danesh's Lemma 3, proved here by Laplace moments
instead of meromorphic continuation). Let `G t = ∑ c_i e^{t w_i}` with `∑ ‖c_i‖ < ∞`,
`Re w_i ≤ σ₀`, and only finitely many `w_i` below each height. If `‖G t‖ ≤ K e^{α t}` for all large
`t`, then at every point `v` with `Re v > α` the coefficients sitting at `v` cancel:
`∑_{w_i = v} c_i = 0`. -/
theorem fiber_sum_eq_zero_of_growth {ι : Type*} [Countable ι] (w c : ι → ℂ) {σ₀ : ℝ}
    (hw : ∀ i, (w i).re ≤ σ₀) (hfin : ∀ T : ℝ, {i | |(w i).im| ≤ T}.Finite)
    (hc : Summable (fun i => ‖c i‖)) {α K T₀ : ℝ}
    (hG : ∀ t : ℝ, T₀ ≤ t → ‖∑' i, c i * cexp (t * w i)‖ ≤ K * Real.exp (α * t))
    (v : ℂ) (hv : α < v.re) :
    ∑' i, (if w i = v then c i else 0) = 0 := by
  classical
  by_contra hne
  set S := ∑' i, ‖c i‖ with hS
  have hS0 : 0 ≤ S := tsum_nonneg (fun i => norm_nonneg _)
  set σ := max σ₀ α + 1 with hσ
  have hσ0 : σ₀ < σ := by rw [hσ]; linarith [le_max_left σ₀ α]
  have hσα : α < σ := by rw [hσ]; linarith [le_max_right σ₀ α]
  have hσ1 : 1 ≤ σ - σ₀ := by rw [hσ]; linarith [le_max_left σ₀ α]
  set p : ℂ := (σ : ℂ) + (v.im : ℂ) * I with hp
  have hpre : p.re = σ := by simp [hp]
  have hpim : p.im = v.im := by simp [hp]
  -- a bound valid for every `t ≥ 0`
  set G : ℝ → ℂ := fun t => ∑' i, c i * cexp (t * w i) with hGdef
  set K' := |K| + S * Real.exp (|σ₀| * |T₀| + |α| * |T₀|) with hK'
  have hnorm_term : ∀ t : ℝ, ∀ i, ‖c i * cexp (t * w i)‖ = ‖c i‖ * Real.exp (t * (w i).re) := by
    intro t i
    rw [norm_mul, Complex.norm_exp]
    congr 2
    simp [Complex.mul_re]
  have hG' : ∀ t, 0 ≤ t → ‖G t‖ ≤ K' * Real.exp (α * t) := by
    intro t ht
    by_cases h : T₀ ≤ t
    · refine (hG t h).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
      have : 0 ≤ S * Real.exp (|σ₀| * |T₀| + |α| * |T₀|) := by positivity
      linarith [le_abs_self K]
    · push Not at h
      have htT : t ≤ |T₀| := h.le.trans (le_abs_self _)
      have hbd : ∀ i, ‖c i * cexp (t * w i)‖ ≤ ‖c i‖ * Real.exp (|σ₀| * |T₀|) := by
        intro i
        rw [hnorm_term]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply Real.exp_le_exp.mpr
        calc t * (w i).re ≤ t * σ₀ := mul_le_mul_of_nonneg_left (hw i) ht
          _ ≤ t * |σ₀| := mul_le_mul_of_nonneg_left (le_abs_self _) ht
          _ ≤ |T₀| * |σ₀| := mul_le_mul_of_nonneg_right htT (abs_nonneg _)
          _ = |σ₀| * |T₀| := by ring
      have hsm : Summable (fun i => ‖c i * cexp (t * w i)‖) :=
        Summable.of_nonneg_of_le (fun i => norm_nonneg _) hbd (hc.mul_right _)
      have h1 : ‖G t‖ ≤ S * Real.exp (|σ₀| * |T₀|) := by
        refine (norm_tsum_le_tsum_norm hsm).trans ?_
        rw [hS, ← tsum_mul_right]
        exact hsm.tsum_le_tsum hbd (hc.mul_right _)
      have h2 : Real.exp (|σ₀| * |T₀|) ≤ Real.exp (|σ₀| * |T₀| + |α| * |T₀|) * Real.exp (α * t) := by
        rw [← Real.exp_add, Real.exp_le_exp]
        have : -(|α| * |T₀|) ≤ α * t := by
          have h3 : -(|α| * t) ≤ α * t := by
            have := neg_abs_le α
            nlinarith
          have h4 : |α| * t ≤ |α| * |T₀| := mul_le_mul_of_nonneg_left htT (abs_nonneg _)
          linarith
        linarith
      calc ‖G t‖ ≤ S * Real.exp (|σ₀| * |T₀|) := h1
        _ ≤ S * (Real.exp (|σ₀| * |T₀| + |α| * |T₀|) * Real.exp (α * t)) :=
            mul_le_mul_of_nonneg_left h2 hS0
        _ ≤ K' * Real.exp (α * t) := by
            rw [hK', ← mul_assoc]
            apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
            linarith [abs_nonneg K]
  -- the moments
  have hmom : ∀ n : ℕ, ‖∑' i, c i / (p - w i) ^ (n + 1)‖ ≤ K' / (σ - α) ^ (n + 1) := by
    intro n
    have hid := moment_identity w c hw hc (p := p) (by rw [hpre]; exact hσ0) n
    have hbd := moment_bound G hG' (p := p) (by rw [hpre]; exact hσα) n
    rw [hGdef] at hbd
    rw [hid, norm_mul, Complex.norm_natCast, hpre] at hbd
    have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    rw [show K' * (n.factorial / (σ - α) ^ (n + 1)) = n.factorial * (K' / (σ - α) ^ (n + 1)) by
      ring] at hbd
    exact le_of_mul_le_mul_left hbd hf
  -- distances to `p`
  set D : ι → ℝ := fun i => ‖p - w i‖ with hD
  have hD1 : ∀ i, 1 ≤ D i := by
    intro i
    have h1 : (p - w i).re ≤ ‖p - w i‖ := Complex.re_le_norm _
    simp only [Complex.sub_re, hpre] at h1
    simp only [hD]
    linarith [hw i]
  have hDfin : ∀ R : ℝ, {i | D i ≤ R}.Finite := by
    intro R
    refine (hfin (|v.im| + R)).subset (fun i hi => ?_)
    simp only [mem_ofPred_eq] at hi ⊢
    have h1 : |(p - w i).im| ≤ ‖p - w i‖ := Complex.abs_im_le_norm _
    simp only [Complex.sub_im, hpim] at h1
    have h2 : |(w i).im| ≤ |v.im| + |v.im - (w i).im| := by
      have := abs_sub_abs_le_abs_sub v.im (v.im - (w i).im)
      rw [sub_sub_cancel] at this
      have := abs_sub_abs_le_abs_sub (w i).im v.im
      rw [abs_sub_comm (w i).im v.im] at this
      linarith [abs_sub_abs_le_abs_sub (v.im - (w i).im) v.im, abs_sub_comm v.im (v.im - (w i).im),
        abs_neg (w i).im, show v.im - (v.im - (w i).im) = (w i).im by ring]
    linarith
  -- grouped coefficients
  set grp : ℂ → ℂ := fun u => ∑' i, if w i = u then c i else 0 with hgrp
  have hgrp_fin : ∀ (u : ℂ) (R : ℝ) (hu : ‖p - u‖ ≤ R),
      grp u = ∑ i ∈ (hDfin R).toFinset, if w i = u then c i else 0 := by
    intro u R hu
    refine tsum_eq_sum (fun i hi => ?_)
    rw [Set.Finite.mem_toFinset, mem_ofPred_eq] at hi
    rw [ite_eq_right_iff]
    intro hwu
    exact absurd (by simp only [hD]; rw [hwu]; exact hu) hi
  have hne' : grp v ≠ 0 := hne
  obtain ⟨i0, hi0⟩ : ∃ i0, w i0 = v := by
    by_contra hno
    push Not at hno
    apply hne'
    simp only [hgrp]
    exact (tsum_congr (fun i => ite_eq_right_iff.mpr (fun h => absurd h (hno i)))).trans tsum_zero
  set d := ‖p - v‖ with hd
  have hvre : v.re ≤ σ₀ := hi0 ▸ hw i0
  have hpv : p - v = ((σ - v.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hp]
  have hdval : d = σ - v.re := by
    rw [hd, hpv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hdlt : d < σ - α := by rw [hdval]; linarith
  set F0s := (hDfin d).toFinset with hF0s
  set P' := (F0s.image w).filter (fun u => grp u ≠ 0) with hP'
  have hvP : v ∈ P' := by
    rw [hP', Finset.mem_filter]
    refine ⟨Finset.mem_image.mpr ⟨i0, ?_, hi0⟩, hne'⟩
    rw [hF0s, Set.Finite.mem_toFinset, mem_ofPred_eq]
    simp only [hD]; rw [hi0]
  set r₁ := P'.inf' ⟨v, hvP⟩ (fun u => ‖p - u‖) with hr₁
  have hr₁d : r₁ ≤ d := Finset.inf'_le _ hvP
  obtain ⟨u1, hu1P, hu1eq'⟩ := Finset.exists_mem_eq_inf' ⟨v, hvP⟩ (fun u => ‖p - u‖)
  have hu1eq : r₁ = ‖p - u1‖ := hu1eq'
  have hP'w : ∀ u ∈ P', ∃ j, w j = u := by
    intro u hu
    rw [hP', Finset.mem_filter, Finset.mem_image] at hu
    obtain ⟨⟨j, _, hj⟩, _⟩ := hu
    exact ⟨j, hj⟩
  have hr₁pos : 0 < r₁ := by
    obtain ⟨j, hj⟩ := hP'w u1 hu1P
    rw [hu1eq, ← hj]
    exact lt_of_lt_of_le one_pos (hD1 j)
  set V := P'.filter (fun u => ‖p - u‖ = r₁) with hV
  have hu1V : u1 ∈ V := by
    rw [hV, Finset.mem_filter]; exact ⟨hu1P, by rw [hu1eq]⟩
  set Fs := (hDfin r₁).toFinset with hFs
  have hmemFs : ∀ i, i ∈ Fs ↔ D i ≤ r₁ := by
    intro i; rw [hFs, Set.Finite.mem_toFinset, mem_ofPred_eq]
  -- the next distance `r₂ > r₁`
  set F1s := (hDfin (r₁ + 1)).toFinset with hF1s
  set s2 : Finset ℝ := insert (r₁ + 1) ((F1s.filter (fun i => r₁ < D i)).image D) with hs2
  set r₂ := s2.min' (Finset.insert_nonempty _ _) with hr₂
  have hr₁₂ : r₁ < r₂ := by
    rw [hr₂, Finset.lt_min'_iff]
    intro y hy
    rw [hs2, Finset.mem_insert, Finset.mem_image] at hy
    rcases hy with hy | ⟨i, hi, rfl⟩
    · rw [hy]; linarith
    · exact (Finset.mem_filter.mp hi).2
  have hr₂le : ∀ i, i ∉ Fs → r₂ ≤ D i := by
    intro i hi
    rw [hmemFs, not_le] at hi
    by_cases h1 : D i ≤ r₁ + 1
    · apply Finset.min'_le
      rw [hs2, Finset.mem_insert, Finset.mem_image]
      right
      refine ⟨i, Finset.mem_filter.mpr ⟨?_, hi⟩, rfl⟩
      rw [hF1s, Set.Finite.mem_toFinset, mem_ofPred_eq]; exact h1
    · push Not at h1
      exact ((Finset.min'_le _ _ (Finset.mem_insert_self _ _)).trans h1.le)
  have hr₂pos : 0 < r₂ := hr₁pos.trans hr₁₂
  -- splitting the moment series
  set f : ℕ → ι → ℂ := fun n i => c i / (p - w i) ^ (n + 1) with hf
  have hfnorm : ∀ n i, ‖f n i‖ = ‖c i‖ / D i ^ (n + 1) := by
    intro n i; simp only [hf, hD, norm_div, norm_pow]
  have hfle : ∀ n i, ‖f n i‖ ≤ ‖c i‖ := by
    intro n i
    rw [hfnorm]
    exact div_le_self (norm_nonneg _) (one_le_pow₀ (hD1 i))
  have hfsum : ∀ n, Summable (fun i => ‖f n i‖) := fun n =>
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) (hfle n) hc
  have htail : ∀ n, ‖∑' x : {x // x ∉ Fs}, f n x‖ ≤ S / r₂ ^ (n + 1) := by
    intro n
    have hs1 : Summable (fun x : {x // x ∉ Fs} => ‖f n x‖) := (hfsum n).subtype _
    have hb : ∀ x : {x // x ∉ Fs}, ‖f n x‖ ≤ ‖c x‖ / r₂ ^ (n + 1) := by
      intro x
      rw [hfnorm]
      exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
        (pow_le_pow_left₀ hr₂pos.le (hr₂le x x.2) _)
    have hs2' : Summable (fun x : {x // x ∉ Fs} => ‖c x‖ / r₂ ^ (n + 1)) :=
      (hc.subtype _).div_const _
    calc ‖∑' x : {x // x ∉ Fs}, f n x‖ ≤ ∑' x : {x // x ∉ Fs}, ‖f n x‖ := norm_tsum_le_tsum_norm hs1
      _ ≤ ∑' x : {x // x ∉ Fs}, ‖c x‖ / r₂ ^ (n + 1) := hs1.tsum_le_tsum hb hs2'
      _ = (∑' x : {x // x ∉ Fs}, ‖c x‖) / r₂ ^ (n + 1) := tsum_div_const
      _ ≤ S / r₂ ^ (n + 1) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact hc.tsum_subtype_le (fun i => ‖c i‖) _ (fun i => norm_nonneg _) |>.trans le_rfl
  -- the head regroups into the circle `‖p - u‖ = r₁`
  have himage : ∀ u ∈ Fs.image w, ‖p - u‖ ≤ r₁ := by
    intro u hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
    exact (hmemFs j).mp hj
  have hVsub : V ⊆ Fs.image w := by
    intro u hu
    rw [hV, Finset.mem_filter] at hu
    obtain ⟨j, hj⟩ := hP'w u hu.1
    refine Finset.mem_image.mpr ⟨j, (hmemFs j).mpr ?_, hj⟩
    simp only [hD]; rw [hj, hu.2]
  have hzero_off : ∀ u ∈ Fs.image w, u ∉ V → grp u = 0 := by
    intro u hu huV
    by_contra hgu
    apply huV
    have hu' := himage u hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
    have hP : w j ∈ P' := by
      rw [hP', Finset.mem_filter]
      refine ⟨Finset.mem_image.mpr ⟨j, ?_, rfl⟩, hgu⟩
      rw [hF0s, Set.Finite.mem_toFinset, mem_ofPred_eq]
      exact hu'.trans hr₁d
    rw [hV, Finset.mem_filter]
    exact ⟨hP, le_antisymm hu' (Finset.inf'_le _ hP)⟩
  have hhead : ∀ n, ∑ i ∈ Fs, f n i = ∑ u ∈ V, grp u / (p - u) ^ (n + 1) := by
    intro n
    rw [← Finset.sum_fiberwise_of_maps_to (s := Fs) (t := Fs.image w) (g := w)
      (fun i hi => Finset.mem_image_of_mem w hi)]
    have hin : ∀ u ∈ Fs.image w, ∑ i ∈ Fs with w i = u, f n i = grp u / (p - u) ^ (n + 1) := by
      intro u hu
      have e1 : ∑ i ∈ Fs with w i = u, f n i = ∑ i ∈ Fs with w i = u, c i / (p - u) ^ (n + 1) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        simp only [hf]
        rw [(Finset.mem_filter.mp hi).2]
      rw [e1, ← Finset.sum_div, hgrp_fin u r₁ (himage u hu), ← Finset.sum_filter]
    rw [Finset.sum_congr rfl hin]
    symm
    apply Finset.sum_subset hVsub
    intro u hu huV
    rw [hzero_off u hu huV, zero_div]
  -- the normalised dominant sum tends to zero
  set om : ℂ → ℂ := fun u => (r₁ : ℂ) / (p - u) with hom
  have homV : ∀ u ∈ V, ‖om u‖ = 1 := by
    intro u hu
    rw [hV, Finset.mem_filter] at hu
    rw [hom, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr₁pos, hu.2,
      div_self hr₁pos.ne']
  have hominj : Set.InjOn om V := by
    intro u hu u' hu' huu
    have hn1 := homV u hu
    have hpu : p - u ≠ 0 := by
      intro h0; rw [hom] at hn1; simp [h0] at hn1
    have hpu' : p - u' ≠ 0 := by
      intro h0; have := homV u' hu'; rw [hom] at this; simp [h0] at this
    have hr : (r₁ : ℂ) ≠ 0 := by exact_mod_cast hr₁pos.ne'
    simp only [hom] at huu
    rw [div_eq_div_iff hpu hpu'] at huu
    have := mul_left_cancel₀ hr huu
    linear_combination this
  have ha : Tendsto (fun n : ℕ => ∑ u ∈ V, grp u * om u ^ (n + 1)) atTop (𝓝 0) := by
    have hq1 : r₁ / (σ - α) < 1 := (div_lt_one (by linarith)).mpr (hr₁d.trans_lt hdlt)
    have hq2 : r₁ / r₂ < 1 := (div_lt_one hr₂pos).mpr hr₁₂
    have hlim : Tendsto (fun n : ℕ => K' * (r₁ / (σ - α)) ^ (n + 1) + S * (r₁ / r₂) ^ (n + 1))
        atTop (𝓝 0) := by
      have t1 := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hq1).comp
        (tendsto_add_atTop_nat 1)).const_mul K'
      have t2 := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hq2).comp
        (tendsto_add_atTop_nat 1)).const_mul S
      simpa using t1.add t2
    refine squeeze_zero_norm (fun n => ?_) hlim
    have e1 : ∑ u ∈ V, grp u * om u ^ (n + 1) = (r₁ : ℂ) ^ (n + 1) * ∑ i ∈ Fs, f n i := by
      rw [hhead, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      simp only [hom, div_pow]
      ring
    have hsplit := (Summable.of_norm (hfsum n)).sum_add_tsum_subtype_compl Fs
    have e2 : ∑ i ∈ Fs, f n i = ∑' i, f n i - ∑' x : {x // x ∉ Fs}, f n x := by
      rw [← hsplit]; ring
    rw [e1, e2, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr₁pos]
    have hb1 := hmom n
    have hb2 := htail n
    have hsub := norm_sub_le (∑' i, f n i) (∑' x : {x // x ∉ Fs}, f n x)
    calc r₁ ^ (n + 1) * ‖∑' i, f n i - ∑' x : {x // x ∉ Fs}, f n x‖
        ≤ r₁ ^ (n + 1) * (K' / (σ - α) ^ (n + 1) + S / r₂ ^ (n + 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          simp only [hf] at hb2 hsub ⊢
          linarith
      _ = K' * (r₁ / (σ - α)) ^ (n + 1) + S * (r₁ / r₂) ^ (n + 1) := by
          rw [div_pow, div_pow]; ring
  have ha' : Tendsto (fun n : ℕ => ∑ u ∈ V, grp u * om u ^ n) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mp ha
  have h0 := coeff_eq_zero_of_tendsto V om grp hominj homV ha' u1 hu1V
  have hu1ne : grp u1 ≠ 0 := by
    rw [hV, Finset.mem_filter, hP', Finset.mem_filter] at hu1V
    exact hu1V.1.2
  exact hu1ne h0

/-! ## Part II: the Weil form of the paper in hp-proof's zero enumeration -/


/-- Danesh's bilateral Laplace transform (paper, eq. (1)): `H f z = ∫ f(x) e^{zx} dx`. -/
def H (f : ℝ → ℂ) (z : ℂ) : ℂ := ∫ x : ℝ, f x * cexp (z * x)

/-- The centred zero `z_ρ = ρ - 1/2`, along the canonical enumeration with multiplicity. -/
def zc (x : Index) : ℂ := canonical x - 1 / 2

/-- The summand of the Weil form: `H f (z_ρ) · conj (H g (-conj z_ρ))`. -/
def term (f g : ℝ → ℂ) (x : Index) : ℂ := H f (zc x) * (starRingEnd ℂ) (H g (-(starRingEnd ℂ) (zc x)))

/-- **The centred Weil form** (paper, eq. (2)), linear in its first argument:
`B(f, g) = ∑_ρ H f (z_ρ) · conj (H g (-conj z_ρ))`, zeros counted with multiplicity. -/
def B (f g : ℝ → ℂ) : ℂ := ∑' x : Index, term f g x

/-- The Weil energy `Q f = B(f, f)`. -/
def Q (f : ℝ → ℂ) : ℂ := B f f

/-- Translation `τ_a f (x) = f (x - a)`. -/
def tr (a : ℝ) (f : ℝ → ℂ) : ℝ → ℂ := fun x => f (x - a)

/-- A real function viewed as a complex one. -/
def cpx (φ : ℝ → ℝ) : ℝ → ℂ := fun x => (φ x : ℂ)

/-! ## Elementary facts about the centred zeros -/

lemma zc_re (x : Index) : (zc x).re = (canonical x).re - 1 / 2 := by simp [zc]

lemma zc_im (x : Index) : (zc x).im = (canonical x).im := by simp [zc]

lemma abs_zc_re_lt (x : Index) : |(zc x).re| < 1 / 2 := by
  have h := OffLineDetection.abs_t_im_lt x
  rw [OffLineDetection.t_im] at h
  rw [zc_re, abs_sub_comm]
  convert h using 2

lemma summable_zc : Summable (fun x : Index => 1 / (1 + (zc x).im ^ 2)) := by
  have h := OffLineDetection.summable_inv_one_add_sq_re
  refine h.congr (fun x => ?_)
  rw [OffLineDetection.t_re, zc_im]

/-- `∑_ρ 1/(1 + γ²)` (finite, from the zero count). -/
def Sz : ℝ := ∑' x : Index, 1 / (1 + (zc x).im ^ 2)

lemma Sz_nonneg : 0 ≤ Sz := tsum_nonneg (fun _ => by positivity)

/-! ## Decay and absolute convergence -/

/-- A transform bound on the open strip `|Re z| < 1/2`: `‖H f z‖² (1 + (Im z)²) ≤ K`. -/
def Decay (f : ℝ → ℂ) (K : ℝ) : Prop :=
  ∀ z : ℂ, |z.re| < 1 / 2 → ‖H f z‖ ^ 2 * (1 + z.im ^ 2) ≤ K

lemma Decay.sq_le {f : ℝ → ℂ} {K : ℝ} (hf : Decay f K) {z : ℂ} (hz : |z.re| < 1 / 2) :
    ‖H f z‖ ^ 2 ≤ K * (1 / (1 + z.im ^ 2)) := by
  have h := hf z hz
  have hp : 0 < 1 + z.im ^ 2 := by positivity
  rw [mul_one_div, le_div_iff₀ hp]
  exact h

lemma norm_term_le {f g : ℝ → ℂ} {K K' : ℝ} (hf : Decay f K) (hg : Decay g K') (x : Index) :
    ‖term f g x‖ ≤ (K + K') / 2 * (1 / (1 + (zc x).im ^ 2)) := by
  have hz := abs_zc_re_lt x
  have hz' : |(-(starRingEnd ℂ) (zc x)).re| < 1 / 2 := by simpa using hz
  have h1 := hf.sq_le hz
  have h2 := hg.sq_le hz'
  have him : (-(starRingEnd ℂ) (zc x)).im = (zc x).im := by simp
  rw [him] at h2
  unfold term
  rw [norm_mul, Complex.norm_conj]
  set a := ‖H f (zc x)‖
  set b := ‖H g (-(starRingEnd ℂ) (zc x))‖
  have hab : a * b ≤ (a ^ 2 + b ^ 2) / 2 := by nlinarith [sq_nonneg (a - b)]
  linarith

lemma summable_term {f g : ℝ → ℂ} {K K' : ℝ} (hf : Decay f K) (hg : Decay g K') :
    Summable (term f g) :=
  Summable.of_norm_bounded (summable_zc.mul_left ((K + K') / 2)) (norm_term_le hf hg)

lemma summable_norm_term {f g : ℝ → ℂ} {K K' : ℝ} (hf : Decay f K) (hg : Decay g K') :
    Summable (fun x => ‖term f g x‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term_le hf hg)
    (summable_zc.mul_left ((K + K') / 2))

lemma norm_B_le {f g : ℝ → ℂ} {K K' : ℝ} (hf : Decay f K) (hg : Decay g K') :
    ‖B f g‖ ≤ (K + K') / 2 * Sz := by
  unfold B Sz
  rw [← tsum_mul_left]
  exact (norm_tsum_le_tsum_norm (summable_norm_term hf hg)).trans
    ((summable_norm_term hf hg).tsum_le_tsum (norm_term_le hf hg) (summable_zc.mul_left _))

lemma norm_Q_le {f : ℝ → ℂ} {K : ℝ} (hf : Decay f K) : ‖Q f‖ ≤ K * Sz := by
  have := norm_B_le hf hf
  unfold Q
  linarith [show (K + K) / 2 = K by ring]

/-! ## Translation -/

lemma H_tr (a : ℝ) (f : ℝ → ℂ) (z : ℂ) : H (tr a f) z = cexp (z * a) * H f z := by
  unfold H tr
  have h := integral_sub_right_eq_self (μ := volume) (fun y : ℝ => f y * cexp (z * ((y + a : ℝ) : ℂ))) a
  simp only [sub_add_cancel] at h
  rw [h, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [show z * ((y + a : ℝ) : ℂ) = z * y + z * a by push_cast; ring, Complex.exp_add]
  ring

lemma conj_cexp_neg_conj_mul (z : ℂ) (a : ℝ) :
    (starRingEnd ℂ) (cexp (-(starRingEnd ℂ) z * a)) = cexp (-(z * a)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp [map_mul, map_neg, Complex.conj_ofReal]

lemma term_tr (a : ℝ) (f g : ℝ → ℂ) (x : Index) :
    term (tr a f) (tr a g) x = term f g x := by
  unfold term
  rw [H_tr, H_tr, map_mul, conj_cexp_neg_conj_mul]
  have : cexp (zc x * a) * cexp (-(zc x * a)) = 1 := by
    rw [← Complex.exp_add]; simp
  linear_combination (H f (zc x) * (starRingEnd ℂ) (H g (-(starRingEnd ℂ) (zc x)))) * this

/-- Translation invariance (paper, eq. (5)): `B(τ_a f, τ_a g) = B(f, g)`. -/
theorem B_tr (a : ℝ) (f g : ℝ → ℂ) : B (tr a f) (tr a g) = B f g := by
  unfold B; exact tsum_congr (term_tr a f g)

theorem Q_tr (a : ℝ) (f : ℝ → ℂ) : Q (tr a f) = Q f := B_tr a f f

/-- The cross term of a test against its translate is an exponential series in the centred
zeros: `B(h, τ_t h) = ∑_ρ c_ρ e^{-t z_ρ}` with `c_ρ = H h (z_ρ) · conj (H h (-conj z_ρ))`. -/
lemma term_tr_right (t : ℝ) (h : ℝ → ℂ) (x : Index) :
    term h (tr t h) x = term h h x * cexp (t * -(zc x)) := by
  unfold term
  rw [H_tr, map_mul, conj_cexp_neg_conj_mul]
  rw [show (t : ℂ) * -(zc x) = -(zc x * t) by ring]
  ring

theorem B_tr_right (t : ℝ) (h : ℝ → ℂ) :
    B h (tr t h) = ∑' x : Index, term h h x * cexp (t * -(zc x)) := by
  unfold B; exact tsum_congr (term_tr_right t h)

lemma Decay.tr {f : ℝ → ℂ} {K : ℝ} (hf : Decay f K) (a : ℝ) :
    Decay (tr a f) (K * Real.exp |a|) := by
  intro z hz
  rw [H_tr, norm_mul, Complex.norm_exp, mul_pow]
  have hre : (z * (a : ℂ)).re = z.re * a := by simp [Complex.mul_re]
  rw [hre]
  have h1 : Real.exp (z.re * a) ^ 2 ≤ Real.exp |a| := by
    rw [← Real.exp_nat_mul, Real.exp_le_exp]
    have : |z.re * a| ≤ |a| / 2 := by
      rw [abs_mul]
      nlinarith [abs_nonneg a, abs_nonneg z.re]
    have := le_abs_self (z.re * a)
    push_cast
    linarith
  have h2 := hf z hz
  have hK : 0 ≤ K := le_trans (by positivity) h2
  calc Real.exp (z.re * a) ^ 2 * ‖H f z‖ ^ 2 * (1 + z.im ^ 2)
      = Real.exp (z.re * a) ^ 2 * (‖H f z‖ ^ 2 * (1 + z.im ^ 2)) := by ring
    _ ≤ Real.exp |a| * K := mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le
    _ = K * Real.exp |a| := by ring

/-! ## Under RH the form is an inner product: Cauchy–Schwarz -/

lemma neg_conj_zc_of_RH (hRH : RiemannHypothesis) (x : Index) :
    -(starRingEnd ℂ) (zc x) = zc x := by
  have hre : (canonical x).re = 1 / 2 :=
    (riemannHypothesis_iff.mp hRH) _ (multEnum_canonical.nontrivial x)
  apply Complex.ext
  · simp [zc_re, hre]
  · simp

/-- **Theorem 4(1) of the paper, for every pair of transforms with decay (no support condition).**
Under RH, `‖B(f, g)‖² ≤ Re Q(f) · Re Q(g)`. -/
theorem cs_of_RH (hRH : RiemannHypothesis) {f g : ℝ → ℂ} {K K' : ℝ}
    (hf : Decay f K) (hg : Decay g K') :
    ‖B f g‖ ^ 2 ≤ (Q f).re * (Q g).re := by
  set a : Index → ℝ := fun x => ‖H f (zc x)‖ with ha
  set b : Index → ℝ := fun x => ‖H g (zc x)‖ with hb
  have hzc := neg_conj_zc_of_RH hRH
  have hterm : ∀ x, ‖term f g x‖ = a x * b x := by
    intro x; unfold term; rw [hzc, norm_mul, Complex.norm_conj]
  have hQ : ∀ (k : ℝ → ℂ) (x : Index), term k k x = ((‖H k (zc x)‖ ^ 2 : ℝ) : ℂ) := by
    intro k x
    unfold term
    rw [hzc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hsqa : ∀ x, a x ^ 2 ≤ K * (1 / (1 + (zc x).im ^ 2)) := fun x => hf.sq_le (abs_zc_re_lt x)
  have hsqb : ∀ x, b x ^ 2 ≤ K' * (1 / (1 + (zc x).im ^ 2)) := fun x => hg.sq_le (abs_zc_re_lt x)
  have sa : Summable (fun x => a x ^ 2) :=
    Summable.of_nonneg_of_le (fun x => by positivity) hsqa (summable_zc.mul_left K)
  have sb : Summable (fun x => b x ^ 2) :=
    Summable.of_nonneg_of_le (fun x => by positivity) hsqb (summable_zc.mul_left K')
  have hQf : (Q f).re = ∑' x, a x ^ 2 := by
    unfold Q B
    simp_rw [hQ f]
    rw [← Complex.ofReal_tsum, Complex.ofReal_re]
  have hQg : (Q g).re = ∑' x, b x ^ 2 := by
    unfold Q B
    simp_rw [hQ g]
    rw [← Complex.ofReal_tsum, Complex.ofReal_re]
  have hab : Summable (fun x => a x * b x) := by
    refine Summable.of_nonneg_of_le (fun x => by positivity) (fun x => ?_) ((sa.add sb).div_const 2)
    nlinarith [sq_nonneg (a x - b x)]
  have h1 : ‖B f g‖ ≤ ∑' x, a x * b x := by
    unfold B
    refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr hterm))
    exact hab.congr (fun x => (hterm x).symm)
  have h2 := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    (fun x => norm_nonneg (H f (zc x))) (fun x => norm_nonneg (H g (zc x)))
    (by simpa [Real.rpow_two] using sa) (by simpa [Real.rpow_two] using sb)
  simp only [Real.rpow_two] at h2
  rw [hQf, hQg]
  have hA : 0 ≤ ∑' x, a x ^ 2 := tsum_nonneg (fun x => by positivity)
  have hB : 0 ≤ ∑' x, b x ^ 2 := tsum_nonneg (fun x => by positivity)
  have h3 : ‖B f g‖ ≤ Real.sqrt (∑' x, a x ^ 2) * Real.sqrt (∑' x, b x ^ 2) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    refine h1.trans ?_
    simpa [ha, hb] using h2
  calc ‖B f g‖ ^ 2 ≤ (Real.sqrt (∑' x, a x ^ 2) * Real.sqrt (∑' x, b x ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h3 2
    _ = (∑' x, a x ^ 2) * ∑' x, b x ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]

/-- Under RH the energy is real and nonnegative. -/
theorem Q_real_nonneg_of_RH (hRH : RiemannHypothesis) (f : ℝ → ℂ) :
    (Q f).im = 0 ∧ 0 ≤ (Q f).re := by
  have hzc := neg_conj_zc_of_RH hRH
  have hQ : ∀ x, term f f x = ((‖H f (zc x)‖ ^ 2 : ℝ) : ℂ) := by
    intro x; unfold term; rw [hzc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  unfold Q B
  simp_rw [hQ]
  rw [← Complex.ofReal_tsum, Complex.ofReal_im, Complex.ofReal_re]
  exact ⟨rfl, tsum_nonneg (fun x => by positivity)⟩


/-! ## Decay from smoothness and compact support -/

lemma le_abs_of_not_mem_Icc {x a : ℝ} (hx : x ∉ Set.Icc (-a) a) : a ≤ |x| := by
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rw [le_abs]
  rcases hx with hx | hx
  · right; linarith
  · left; linarith

lemma H_eq_interval {f : ℝ → ℂ} {a : ℝ} (ha : 0 ≤ a) (hsupp : ∀ x, a ≤ |x| → f x = 0) (z : ℂ) :
    H f z = ∫ x in (-a)..a, f x * cexp (z * x) := by
  unfold H
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro x hx
  rw [hsupp x (le_abs_of_not_mem_Icc hx), zero_mul]

/-- Two elementary estimates give the decay: `‖H u z‖ ≤ 2a M₀ e^{a/2}` and, after one
integration by parts, `‖z · H u z‖ ≤ 2a M₁ e^{a/2}`. -/
lemma decay_of_bounds {u : ℝ → ℝ} {a M₀ M₁ : ℝ} (ha : 0 ≤ a) (hu : Differentiable ℝ u)
    (hcont : Continuous (deriv u)) (hsupp : ∀ x, a ≤ |x| → u x = 0)
    (h0 : ∀ x, |u x| ≤ M₀) (h1 : ∀ x, |deriv u x| ≤ M₁) :
    Decay (cpx u) (4 * a ^ 2 * Real.exp a * (M₀ ^ 2 + M₁ ^ 2)) := by
  intro z hz
  have hM₀ : 0 ≤ M₀ := (abs_nonneg _).trans (h0 0)
  have hM₁ : 0 ≤ M₁ := (abs_nonneg _).trans (h1 0)
  have hsupp' : ∀ x, a ≤ |x| → cpx u x = 0 := fun x hx => by simp [cpx, hsupp x hx]
  have hH := H_eq_interval ha hsupp' z
  have hexp : ∀ x ∈ Set.uIoc (-a) a, ‖cexp (z * x)‖ ≤ Real.exp (a / 2) := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hxa : |x| ≤ a := abs_le.mpr ⟨hx.1.le, hx.2⟩
    rw [Complex.norm_exp, Real.exp_le_exp]
    have : (z * (x : ℂ)).re = z.re * x := by simp [Complex.mul_re]
    rw [this]
    calc z.re * x ≤ |z.re * x| := le_abs_self _
      _ = |z.re| * |x| := abs_mul _ _
      _ ≤ (1 / 2) * a := mul_le_mul hz.le hxa (abs_nonneg _) (by norm_num)
      _ = a / 2 := by ring
  have hb0 : ‖H (cpx u) z‖ ≤ M₀ * Real.exp (a / 2) * (2 * a) := by
    rw [hH]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (C := M₀ * Real.exp (a / 2))
      (a := -a) (b := a) (f := fun x => cpx u x * cexp (z * x)) (fun x hx => by
        rw [norm_mul]
        simp only [cpx, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul (h0 x) (hexp x hx) (norm_nonneg _) hM₀)
    rw [show |a - -a| = 2 * a by rw [abs_of_nonneg (by linarith)]; ring] at this
    exact this
  -- integration by parts
  have hderu : ∀ x ∈ Set.uIcc (-a) a, HasDerivAt (cpx u) (((deriv u x : ℝ) : ℂ)) x := fun x _ =>
    (hu x).hasDerivAt.ofReal_comp
  have hderv : ∀ x ∈ Set.uIcc (-a) a, HasDerivAt (fun y : ℝ => cexp (z * y)) (z * cexp (z * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => z * (y : ℂ)) z x := by
      simpa using ((hasDerivAt_id x).ofReal_comp.const_mul z)
    have := h1.cexp
    rw [mul_comm] at this
    exact this
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hderu hderv
    ((Complex.continuous_ofReal.comp hcont).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun x : ℝ => z * cexp (z * x))).intervalIntegrable _ _)
  have hua : cpx u a = 0 := hsupp' a (le_of_eq (abs_of_nonneg ha).symm)
  have hum : cpx u (-a) = 0 := hsupp' (-a) (le_of_eq (by rw [abs_neg, abs_of_nonneg ha]))
  rw [hua, hum, zero_mul, zero_mul, sub_zero, zero_sub] at hibp
  have hzH : z * H (cpx u) z = -∫ x in (-a)..a, ((deriv u x : ℝ) : ℂ) * cexp (z * x) := by
    rw [hH, ← intervalIntegral.integral_const_mul, ← hibp]
    congr 1; funext x; ring
  have hb1 : ‖z * H (cpx u) z‖ ≤ M₁ * Real.exp (a / 2) * (2 * a) := by
    rw [hzH, norm_neg]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (C := M₁ * Real.exp (a / 2))
      (a := -a) (b := a) (f := fun x => ((deriv u x : ℝ) : ℂ) * cexp (z * x)) (fun x hx => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul (h1 x) (hexp x hx) (norm_nonneg _) hM₁)
    rw [show |a - -a| = 2 * a by rw [abs_of_nonneg (by linarith)]; ring] at this
    exact this
  have him : z.im ^ 2 ≤ ‖z‖ ^ 2 := by
    have := Complex.abs_im_le_norm z
    nlinarith [abs_nonneg z.im, sq_abs z.im]
  have hX0 : 0 ≤ M₀ * Real.exp (a / 2) * (2 * a) := by positivity
  have hX1 : 0 ≤ M₁ * Real.exp (a / 2) * (2 * a) := by positivity
  have s0 := pow_le_pow_left₀ (norm_nonneg _) hb0 2
  have s1 := pow_le_pow_left₀ (norm_nonneg _) hb1 2
  rw [norm_mul, mul_pow] at s1
  have hea : Real.exp (a / 2) ^ 2 = Real.exp a := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  calc ‖H (cpx u) z‖ ^ 2 * (1 + z.im ^ 2)
      ≤ ‖H (cpx u) z‖ ^ 2 + ‖z‖ ^ 2 * ‖H (cpx u) z‖ ^ 2 := by nlinarith [sq_nonneg ‖H (cpx u) z‖]
    _ ≤ (M₀ * Real.exp (a / 2) * (2 * a)) ^ 2 + (M₁ * Real.exp (a / 2) * (2 * a)) ^ 2 := by
        linarith
    _ = 4 * a ^ 2 * Real.exp a * (M₀ ^ 2 + M₁ ^ 2) := by rw [← hea]; ring

lemma bounded_of_compact {u : ℝ → ℝ} (hc : Continuous u) {a : ℝ} (hsupp : ∀ x, a ≤ |x| → u x = 0) :
    ∃ M, ∀ x, |u x| ≤ M := by
  have hcs : HasCompactSupport u := HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a))
    (fun x hx => hsupp x (le_abs_of_not_mem_Icc hx))
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
  exact ⟨C, fun x => by simpa [Real.norm_eq_abs] using hC x⟩

lemma hasCompactSupport_of_supp {u : ℝ → ℝ} {a : ℝ} (hsupp : ∀ x, a ≤ |x| → u x = 0) :
    HasCompactSupport u :=
  HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a))
    (fun x hx => hsupp x (le_abs_of_not_mem_Icc hx))

/-- A `C¹` real function vanishing for `|x| ≥ a` has a decaying transform. -/
lemma decay_of_contDiff {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) {a : ℝ} (ha : 0 ≤ a)
    (hsupp : ∀ x, a ≤ |x| → u x = 0) : ∃ K, Decay (cpx u) K := by
  have hcs := hasCompactSupport_of_supp hsupp
  obtain ⟨M₀, h0⟩ := bounded_of_compact hu.continuous hsupp
  have hdc : Continuous (deriv u) := hu.continuous_deriv le_rfl
  obtain ⟨C₁, hC₁⟩ := hdc.bounded_above_of_compact_support hcs.deriv
  exact ⟨_, decay_of_bounds ha (hu.differentiable one_ne_zero) hdc hsupp h0
    (fun x => by simpa [Real.norm_eq_abs] using hC₁ x)⟩

/-! ## A narrow bump whose transform does not vanish at a given point -/

lemma exists_bump (z₀ : ℂ) : ∃ (h : ℝ → ℝ) (r : ℝ), 0 < r ∧ ContDiff ℝ ∞ h ∧
    (∀ x, r ≤ |x| → h x = 0) ∧ H (cpx h) z₀ ≠ 0 ∧ H (cpx h) (-(starRingEnd ℂ) z₀) ≠ 0 := by
  set r : ℝ := 1 / (4 * (‖z₀‖ + 1)) with hr
  have hr0 : 0 < r := by positivity
  let f : ContDiffBump (0 : ℝ) := ⟨r / 2, r, by positivity, by linarith⟩
  have hsupp : ∀ x, r ≤ |x| → f x = 0 := by
    intro x hx
    have : x ∉ Function.support f := by
      rw [f.support_eq, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, not_lt]; exact hx
    simpa using this
  have hI : 0 < ∫ x, f x := f.integral_pos
  have hfc : Continuous (fun x => (f x : ℂ)) := Complex.continuous_ofReal.comp f.continuous
  have hcs : HasCompactSupport (fun x : ℝ => (f x : ℂ)) :=
    f.hasCompactSupport.comp_left Complex.ofReal_zero
  have hfi : Integrable (fun x => (f x : ℂ)) := hfc.integrable_of_hasCompactSupport hcs
  -- the key estimate at any point of modulus `‖z₀‖`
  have key : ∀ u : ℂ, ‖u‖ = ‖z₀‖ → H (cpx f) u ≠ 0 := by
    intro u hu
    have hgi : Integrable (fun x : ℝ => (f x : ℂ) * cexp (u * x)) := by
      exact (hfc.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right
    have hdiff : H (cpx f) u - ((∫ x, f x : ℝ) : ℂ) = ∫ x, (f x : ℂ) * (cexp (u * x) - 1) := by
      unfold H cpx
      rw [← integral_complex_ofReal, ← integral_sub hgi hfi]
      congr 1; funext x; ring
    have hbound : ‖∫ x, (f x : ℂ) * (cexp (u * x) - 1)‖ ≤ ∫ x, f x * (1 / 2) := by
      refine norm_integral_le_of_norm_le (f.continuous.integrable_of_hasCompactSupport
        f.hasCompactSupport |>.mul_const _) (Eventually.of_forall fun x => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg f.nonneg]
      by_cases hx : r ≤ |x|
      · rw [hsupp x hx]; simp
      · push Not at hx
        apply mul_le_mul_of_nonneg_left _ f.nonneg
        have hux : ‖u * x‖ ≤ 1 / 4 := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hu]
          calc ‖z₀‖ * |x| ≤ (‖z₀‖ + 1) * r := mul_le_mul (by linarith) hx.le (abs_nonneg _)
                (by positivity)
            _ = 1 / 4 := by rw [hr]; field_simp
        have := Complex.norm_exp_sub_one_le (x := u * x) (by linarith)
        linarith
    rw [integral_mul_const] at hbound
    intro h0
    rw [h0, zero_sub] at hdiff
    have hn : ‖∫ x, (f x : ℂ) * (cexp (u * x) - 1)‖ = ∫ x, f x := by
      rw [← hdiff, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hI]
    rw [hn] at hbound
    linarith
  refine ⟨f, r, hr0, f.contDiff, hsupp, key z₀ rfl, key _ (by simp)⟩

/-! ## The smooth partition (paper, proof of Lemma 2) -/

/-- `χ(v) = S(v+1) - S(v)` with `S` Mathlib's smooth transition; `χ` lives on `(-1, 1)` and its
integer translates sum to one. -/
def chi (v : ℝ) : ℝ := Real.smoothTransition (v + 1) - Real.smoothTransition v

lemma chi_contDiff : ContDiff ℝ ∞ chi :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    Real.smoothTransition.contDiff

lemma chi_nonneg (v : ℝ) : 0 ≤ chi v :=
  sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith))

lemma chi_le_one (v : ℝ) : chi v ≤ 1 := by
  unfold chi
  linarith [Real.smoothTransition.le_one (v + 1), Real.smoothTransition.nonneg v]

lemma chi_eq_zero {v : ℝ} (hv : 1 ≤ |v|) : chi v = 0 := by
  unfold chi
  rcases le_abs'.mp hv with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]
  · rw [Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le (by linarith), sub_self]

lemma chi_sum (J : ℕ) {y : ℝ} (hy : |y| ≤ J) :
    ∑ k ∈ Finset.range (2 * J + 1), chi (y - ((k : ℝ) - J)) = 1 := by
  set g : ℕ → ℝ := fun k => Real.smoothTransition (y + J + 1 - k) with hg
  have e : ∀ k : ℕ, chi (y - ((k : ℝ) - J)) = g k - g (k + 1) := by
    intro k
    simp only [chi, hg]
    push_cast
    ring_nf
  simp_rw [e]
  rw [Finset.sum_range_sub']
  have hy' := abs_le.mp hy
  simp only [hg]
  push_cast
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring

lemma chi_supp : ∀ v, 1 ≤ |v| → chi v = 0 := fun _ hv => chi_eq_zero hv

lemma chi_deriv_bound : ∃ M, ∀ v, |deriv chi v| ≤ M := by
  have hcs := hasCompactSupport_of_supp chi_supp
  have hdc : Continuous (deriv chi) := chi_contDiff.continuous_deriv (by exact_mod_cast le_top)
  obtain ⟨M, hM⟩ := hdc.bounded_above_of_compact_support hcs.deriv
  exact ⟨M, fun v => by simpa [Real.norm_eq_abs] using hM v⟩

/-- The `k`-th piece `u_k(x) = h(x) χ(m x - (k - J))` (paper, eq. (18)). -/
def piece (h : ℝ → ℝ) (m : ℝ) (J k : ℕ) : ℝ → ℝ := fun x => h x * chi (m * x - ((k : ℝ) - J))

lemma piece_contDiff {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (m : ℝ) (J k : ℕ) :
    ContDiff ℝ ∞ (piece h m J k) :=
  hh.mul (chi_contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))

lemma piece_sum {h : ℝ → ℝ} {r m : ℝ} (hsupp : ∀ x, r ≤ |x| → h x = 0) (hm : 0 ≤ m) {J : ℕ}
    (hJ : m * r ≤ J) (x : ℝ) : ∑ k ∈ Finset.range (2 * J + 1), piece h m J k x = h x := by
  unfold piece
  rw [← Finset.mul_sum]
  by_cases hx : r ≤ |x|
  · rw [hsupp x hx, zero_mul]
  · push Not at hx
    rw [chi_sum J (y := m * x), mul_one]
    rw [abs_mul, abs_of_nonneg hm]
    exact (mul_le_mul_of_nonneg_left hx.le hm).trans hJ

lemma piece_supp {h : ℝ → ℝ} {r : ℝ} (hsupp : ∀ x, r ≤ |x| → h x = 0) (m : ℝ) (J k : ℕ) :
    ∀ x, r ≤ |x| → piece h m J k x = 0 := fun x hx => by simp [piece, hsupp x hx]

lemma piece_ne_zero {h : ℝ → ℝ} {m : ℝ} {J k : ℕ} {x : ℝ} (hx : piece h m J k x ≠ 0) :
    |m * x - ((k : ℝ) - J)| < 1 := by
  by_contra hc
  push Not at hc
  exact hx (by simp [piece, chi_eq_zero hc])

lemma piece_bounds {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) {M₀ M₁ Mχ m : ℝ} (hm : 0 ≤ m)
    (h0 : ∀ x, |h x| ≤ M₀) (h1 : ∀ x, |deriv h x| ≤ M₁) (hχ : ∀ v, |deriv chi v| ≤ Mχ)
    (J k : ℕ) :
    (∀ x, |piece h m J k x| ≤ M₀) ∧ (∀ x, |deriv (piece h m J k) x| ≤ M₁ + m * M₀ * Mχ) := by
  have hM₀ : 0 ≤ M₀ := (abs_nonneg _).trans (h0 0)
  have hMχ : 0 ≤ Mχ := (abs_nonneg _).trans (hχ 0)
  refine ⟨fun x => ?_, fun x => ?_⟩
  · simp only [piece, abs_mul, abs_of_nonneg (chi_nonneg _)]
    calc |h x| * chi (m * x - ((k : ℝ) - J)) ≤ |h x| * 1 :=
          mul_le_mul_of_nonneg_left (chi_le_one _) (abs_nonneg _)
      _ ≤ M₀ := by rw [mul_one]; exact h0 x
  · set c : ℝ := (k : ℝ) - J
    have hdh : HasDerivAt h (deriv h x) x :=
      (hh.differentiable (by simp)).differentiableAt.hasDerivAt
    have hin : HasDerivAt (fun y : ℝ => m * y - c) m x := by
      simpa using ((hasDerivAt_id x).const_mul m).sub_const c
    have hdχ : HasDerivAt chi (deriv chi (m * x - c)) (m * x - c) :=
      (chi_contDiff.differentiable (by simp)).differentiableAt.hasDerivAt
    have hcomp : HasDerivAt (fun y => chi (m * y - c)) (deriv chi (m * x - c) * m) x :=
      HasDerivAt.comp (h₂ := chi) x hdχ hin
    have hd := hdh.mul hcomp
    have hpd : deriv (piece h m J k) x = deriv h x * chi (m * x - c) + h x * (deriv chi (m * x - c) * m) :=
      hd.deriv
    rw [hpd]
    calc |deriv h x * chi (m * x - c) + h x * (deriv chi (m * x - c) * m)|
        ≤ |deriv h x * chi (m * x - c)| + |h x * (deriv chi (m * x - c) * m)| := abs_add_le _ _
      _ = |deriv h x| * chi (m * x - c) + |h x| * (|deriv chi (m * x - c)| * m) := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (chi_nonneg _), abs_of_nonneg hm]
      _ ≤ M₁ * 1 + M₀ * (Mχ * m) := by
          apply add_le_add
          · exact mul_le_mul (h1 x) (chi_le_one _) (chi_nonneg _) ((abs_nonneg _).trans (h1 x))
          · exact mul_le_mul (h0 x) (mul_le_mul_of_nonneg_right (hχ _) hm) (by positivity) hM₀
      _ = M₁ + m * M₀ * Mχ := by ring

/-! ## Finite sums -/

lemma integrable_cpx_mul_exp {u : ℝ → ℝ} (hu : Continuous u) {a : ℝ}
    (hsupp : ∀ x, a ≤ |x| → u x = 0) (z : ℂ) :
    Integrable (fun x : ℝ => cpx u x * cexp (z * x)) := by
  have hcs : HasCompactSupport (cpx u) :=
    (hasCompactSupport_of_supp hsupp).comp_left Complex.ofReal_zero
  exact ((Complex.continuous_ofReal.comp hu).mul (by fun_prop)).integrable_of_hasCompactSupport
    hcs.mul_right

lemma H_sum (s : Finset ℕ) (f : ℕ → ℝ → ℂ)
    (hf : ∀ k ∈ s, ∀ z : ℂ, Integrable (fun x : ℝ => f k x * cexp (z * x))) (z : ℂ) :
    H (fun x => ∑ k ∈ s, f k x) z = ∑ k ∈ s, H (f k) z := by
  unfold H
  rw [← integral_finsetSum s (fun k hk => hf k hk z)]
  congr 1; funext x; rw [Finset.sum_mul]

lemma B_sum (s t : Finset ℕ) (f g : ℕ → ℝ → ℂ) (F G : ℝ → ℂ)
    (hF : ∀ z, H F z = ∑ k ∈ s, H (f k) z) (hG : ∀ z, H G z = ∑ l ∈ t, H (g l) z)
    (hs : ∀ k ∈ s, ∀ l ∈ t, Summable (term (f k) (g l))) :
    B F G = ∑ k ∈ s, ∑ l ∈ t, B (f k) (g l) := by
  have hterm : ∀ x, term F G x = ∑ k ∈ s, ∑ l ∈ t, term (f k) (g l) x := by
    intro x
    unfold term
    rw [hF, hG, map_sum, Finset.sum_mul_sum]
  unfold B
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum (fun k hk => summable_sum (fun l hl => hs k hk l hl))]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Summable.tsum_finsetSum (fun l hl => hs k hk l hl)]

/-! ## The criterion -/

/-- **Width functions** (paper, eq. (12)): on `[L*, ∞)`, `w` takes values in `(0, 1]`, is
nonincreasing, tends to `0`, and `log (1 / w L) = o(L)`. -/
structure WidthFn (w : ℝ → ℝ) (Lstar : ℝ) : Prop where
  pos : ∀ L, Lstar ≤ L → 0 < w L
  le_one : ∀ L, Lstar ≤ L → w L ≤ 1
  anti : AntitoneOn w (Set.Ici Lstar)
  tendsto_zero : Tendsto w atTop (𝓝 0)
  subexp : Tendsto (fun L => Real.log (1 / w L) / L) atTop (𝓝 0)

/-- **Real admissible pairs at span `L`** (paper, after eq. (13)): smooth, nonzero, real
`φ` supported in `I = [0, w L]` and `ψ` supported in `J = [L - w L, L]`. -/
def Admissible (w : ℝ → ℝ) (L : ℝ) (φ ψ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ ContDiff ℝ ∞ ψ ∧ φ ≠ 0 ∧ ψ ≠ 0 ∧
    (∀ x, φ x ≠ 0 → x ∈ Set.Icc 0 (w L)) ∧ (∀ x, ψ x ≠ 0 → x ∈ Set.Icc (L - w L) L)

/-- **Danesh's two-interval inequality with allowance `e^{ηL}`**, in multiplicative form:
for all sufficiently large spans and all real admissible pairs,
`‖B(φ, ψ)‖² ≤ e^{2ηL} ‖Q φ‖ ‖Q ψ‖`. For `η = 0` this is the Cauchy–Schwarz inequality of the
paper's Theorem 4. Where `Q φ, Q ψ > 0` (the paper's Lemma 1, for large `L`) it is the statement
`R(φ, ψ) ≤ e^{ηL}` with `R = |B| / √(Q φ Q ψ)`. -/
def TwoIntervalBound (w : ℝ → ℝ) (η : ℝ) : Prop :=
  ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → ∀ φ ψ : ℝ → ℝ, Admissible w L φ ψ →
    ‖B (cpx φ) (cpx ψ)‖ ^ 2 ≤ Real.exp (2 * η * L) * (‖Q (cpx φ)‖ * ‖Q (cpx ψ)‖)

lemma decay_of_Icc {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {lo hi : ℝ}
    (hs : ∀ x, φ x ≠ 0 → x ∈ Set.Icc lo hi) : ∃ K, Decay (cpx φ) K := by
  refine decay_of_contDiff (hφ.of_le (by exact_mod_cast le_top)) (a := |lo| + |hi| + 1)
    (by positivity) (fun x hx => ?_)
  by_contra h0
  obtain ⟨h1, h2⟩ := hs x h0
  have : |x| ≤ |lo| + |hi| := by
    rw [abs_le]; constructor
    · linarith [neg_abs_le lo, abs_nonneg hi]
    · linarith [le_abs_self hi, abs_nonneg lo]
  linarith

/-- **RH ⇒ the two-interval Cauchy–Schwarz inequality** (paper, Theorem 4(1)), for every width
function and every span. -/
theorem twoIntervalBound_of_RH (hRH : RiemannHypothesis) (w : ℝ → ℝ) : TwoIntervalBound w 0 := by
  refine ⟨0, fun L _ φ ψ hadm => ?_⟩
  obtain ⟨hφ, hψ, -, -, hsφ, hsψ⟩ := hadm
  obtain ⟨K, hK⟩ := decay_of_Icc hφ hsφ
  obtain ⟨K', hK'⟩ := decay_of_Icc hψ hsψ
  have hcs := cs_of_RH hRH hK hK'
  have h1 := Q_real_nonneg_of_RH hRH (cpx φ)
  have h2 := Q_real_nonneg_of_RH hRH (cpx ψ)
  have e1 : (Q (cpx φ)).re ≤ ‖Q (cpx φ)‖ := Complex.re_le_norm _
  have e2 : (Q (cpx ψ)).re ≤ ‖Q (cpx ψ)‖ := Complex.re_le_norm _
  rw [mul_zero, zero_mul, Real.exp_zero, one_mul]
  exact hcs.trans (mul_le_mul e1 e2 h2.2 (norm_nonneg _))

/-! ## From the two-interval bound to a growth bound for a fixed test (paper, Lemma 2) -/

lemma H_zero_of_eq_zero {φ : ℝ → ℝ} (h : φ = 0) (z : ℂ) : H (cpx φ) z = 0 := by
  subst h; simp [H, cpx]

lemma B_eq_zero_left {φ : ℝ → ℝ} (h : φ = 0) (g : ℝ → ℂ) : B (cpx φ) g = 0 := by
  unfold B term; simp [H_zero_of_eq_zero h]

lemma B_eq_zero_right {ψ : ℝ → ℝ} (h : ψ = 0) (f : ℝ → ℂ) : B f (cpx ψ) = 0 := by
  unfold B term; simp [H_zero_of_eq_zero h]

/-- One pair of pieces is an admissible pair at its own span, so the two-interval bound applies. -/
lemma pair_bound {w : ℝ → ℝ} {Lstar η L₀ : ℝ} (hw : WidthFn w Lstar) (hη : 0 ≤ η)
    (hL₀ : ∀ L, L₀ ≤ L → ∀ φ ψ : ℝ → ℝ, Admissible w L φ ψ →
      ‖B (cpx φ) (cpx ψ)‖ ^ 2 ≤ Real.exp (2 * η * L) * (‖Q (cpx φ)‖ * ‖Q (cpx ψ)‖))
    {h : ℝ → ℝ} {r : ℝ} (hr : 0 < r) (hh : ContDiff ℝ ∞ h)
    {mR : ℝ} (hm1 : 1 ≤ mR) {J : ℕ} (hJ2 : (J : ℝ) ≤ mR * r + 1) {t C : ℝ}
    (hC : 2 * r + 4 ≤ C) (htL₀ : L₀ + C ≤ t) (htLs : Lstar + C ≤ t)
    (h2m : 2 / mR ≤ w (t + C)) {Km : ℝ} (hKm0 : 0 ≤ Km)
    (hQu : ∀ k, ‖Q (cpx (piece h mR J k))‖ ≤ Km * Sz) {k l : ℕ} (hk : k ≤ 2 * J) (hl : l ≤ 2 * J) :
    ‖B (cpx (piece h mR J k)) (tr t (cpx (piece h mR J l)))‖ ≤ Real.exp (η * (t + C)) * (Km * Sz) := by
  have hm0 : 0 < mR := by linarith
  have hk' : (k : ℝ) ≤ 2 * J := by exact_mod_cast hk
  have hl' : (l : ℝ) ≤ 2 * J := by exact_mod_cast hl
  have hSz := Sz_nonneg
  have hRHS : 0 ≤ Real.exp (η * (t + C)) * (Km * Sz) :=
    mul_nonneg (Real.exp_pos _).le (mul_nonneg hKm0 hSz)
  set s : ℝ := ((k : ℝ) - J - 1) / mR with hs
  set φ : ℝ → ℝ := fun x => piece h mR J k (x + s) with hφ
  set ψ : ℝ → ℝ := fun x => piece h mR J l (x - t + s) with hψ
  set L : ℝ := t + ((l : ℝ) - k + 2) / mR with hL
  have htrφ : tr (-s) (cpx (piece h mR J k)) = cpx φ := by
    funext x; simp [tr, cpx, hφ]
  have htrψ : tr (-s) (tr t (cpx (piece h mR J l))) = cpx ψ := by
    funext x; simp only [tr, cpx, hψ]; congr 2; ring
  have hBeq : B (cpx (piece h mR J k)) (tr t (cpx (piece h mR J l))) = B (cpx φ) (cpx ψ) := by
    rw [← htrφ, ← htrψ, B_tr]
  have hQφ : Q (cpx φ) = Q (cpx (piece h mR J k)) := by rw [← htrφ, Q_tr]
  have hQψ : Q (cpx ψ) = Q (cpx (piece h mR J l)) := by rw [← htrψ, Q_tr, Q_tr]
  -- the span is within `C` of `t`
  have hLt : |L - t| ≤ C := by
    have e : L - t = ((l : ℝ) - k + 2) / mR := by rw [hL]; ring
    rw [e, abs_div, abs_of_pos hm0, div_le_iff₀ hm0]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    have hab : |(l : ℝ) - k + 2| ≤ 2 * J + 2 := by
      rw [abs_le]; constructor <;> linarith
    have h4 : 4 ≤ (C - 2 * r) * mR := by nlinarith
    calc |(l : ℝ) - k + 2| ≤ 2 * J + 2 := hab
      _ ≤ 2 * (mR * r + 1) + 2 := by linarith
      _ ≤ C * mR := by nlinarith
  have hLlo : t - C ≤ L := by linarith [(abs_le.mp hLt).1]
  have hLhi : L ≤ t + C := by linarith [(abs_le.mp hLt).2]
  have hwL : 2 / mR ≤ w L :=
    h2m.trans (hw.anti (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith)) hLhi)
  by_cases hφ0 : φ = 0
  · rw [hBeq, B_eq_zero_left hφ0, norm_zero]; exact hRHS
  by_cases hψ0 : ψ = 0
  · rw [hBeq, B_eq_zero_right hψ0, norm_zero]; exact hRHS
  have hadm : Admissible w L φ ψ := by
    refine ⟨(piece_contDiff hh mR J k).comp (contDiff_id.add contDiff_const),
      (piece_contDiff hh mR J l).comp ((contDiff_id.sub contDiff_const).add contDiff_const),
      hφ0, hψ0, fun x hx => ?_, fun x hx => ?_⟩
    · have h1 := piece_ne_zero hx
      have e : mR * (x + s) - ((k : ℝ) - J) = mR * x - 1 := by
        rw [hs]; field_simp; ring
      rw [e, abs_lt] at h1
      have hx0 : 0 ≤ x := by
        by_contra hneg; push Not at hneg
        have : mR * x < 0 := mul_neg_of_pos_of_neg hm0 hneg
        linarith
      refine ⟨hx0, ?_⟩
      have : x ≤ 2 / mR := by rw [le_div_iff₀ hm0]; linarith
      linarith
    · have h1 := piece_ne_zero hx
      have e : mR * (x - t + s) - ((l : ℝ) - J) = mR * (x - L) + 1 := by
        rw [hs, hL]; field_simp; ring
      rw [e, abs_lt] at h1
      constructor
      · have : L - x ≤ 2 / mR := by
          rw [le_div_iff₀ hm0]; linarith
        linarith
      · by_contra hgt; push Not at hgt
        have : 0 < mR * (x - L) := mul_pos hm0 (by linarith)
        linarith
  have hmain := hL₀ L (by linarith) φ ψ hadm
  rw [hQφ, hQψ] at hmain
  have hq1 := hQu k
  have hq2 := hQu l
  have hsq : ‖B (cpx φ) (cpx ψ)‖ ^ 2 ≤ (Real.exp (η * L) * (Km * Sz)) ^ 2 := by
    calc ‖B (cpx φ) (cpx ψ)‖ ^ 2 ≤ Real.exp (2 * η * L) *
          (‖Q (cpx (piece h mR J k))‖ * ‖Q (cpx (piece h mR J l))‖) := hmain
      _ ≤ Real.exp (2 * η * L) * ((Km * Sz) * (Km * Sz)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          exact mul_le_mul hq1 hq2 (norm_nonneg _) (mul_nonneg hKm0 hSz)
      _ = (Real.exp (η * L) * (Km * Sz)) ^ 2 := by
          rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
  have hle := le_of_pow_le_pow_left₀ two_ne_zero
    (mul_nonneg (Real.exp_pos _).le (mul_nonneg hKm0 hSz)) hsq
  rw [hBeq]
  refine hle.trans (mul_le_mul_of_nonneg_right ?_ (mul_nonneg hKm0 hSz))
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hLhi hη)

/-- The cost of the partition at scale `m`: `n² K_m ≤ (2r+3)² A₁ m⁴`. -/
lemma partition_cost {r M₀ M₁ Mχ mR : ℝ} (hr : 0 < r) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hMχ : 0 ≤ Mχ) (hm1 : 1 ≤ mR) {J : ℕ} (hJ2 : (J : ℝ) ≤ mR * r + 1) :
    ((2 * J + 1 : ℕ) : ℝ) ^ 2 * (4 * r ^ 2 * Real.exp r * (M₀ ^ 2 + (M₁ + mR * M₀ * Mχ) ^ 2))
      ≤ (2 * r + 3) ^ 2 * (4 * r ^ 2 * Real.exp r * (M₀ ^ 2 + (M₁ + M₀ * Mχ) ^ 2)) * mR ^ 4 := by
  have hm0 : 0 < mR := by linarith
  have hn_le : ((2 * J + 1 : ℕ) : ℝ) ≤ (2 * r + 3) * mR := by push_cast; nlinarith
  have e1 : M₀ ^ 2 ≤ M₀ ^ 2 * mR ^ 2 := le_mul_of_one_le_right (by positivity) (by nlinarith)
  have e2 : M₁ + mR * M₀ * Mχ ≤ (M₁ + M₀ * Mχ) * mR := by nlinarith [mul_nonneg hM₀ hMχ]
  have e3 : (M₁ + mR * M₀ * Mχ) ^ 2 ≤ ((M₁ + M₀ * Mχ) * mR) ^ 2 :=
    pow_le_pow_left₀ (by positivity) e2 2
  have hK : M₀ ^ 2 + (M₁ + mR * M₀ * Mχ) ^ 2 ≤ (M₀ ^ 2 + (M₁ + M₀ * Mχ) ^ 2) * mR ^ 2 := by
    nlinarith
  have hn2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hn_le 2
  have hc : 0 ≤ 4 * r ^ 2 * Real.exp r := by positivity
  calc ((2 * J + 1 : ℕ) : ℝ) ^ 2 * (4 * r ^ 2 * Real.exp r * (M₀ ^ 2 + (M₁ + mR * M₀ * Mχ) ^ 2))
      ≤ ((2 * r + 3) * mR) ^ 2 * (4 * r ^ 2 * Real.exp r * ((M₀ ^ 2 + (M₁ + M₀ * Mχ) ^ 2) * mR ^ 2)) :=
        mul_le_mul hn2 (mul_le_mul_of_nonneg_left hK hc) (by positivity) (by positivity)
    _ = _ := by ring

/-- **Lemma 2 of the paper (with a polynomial partition cost).** Under the two-interval bound with
allowance `e^{ηL}`, every smooth real test of compact support satisfies
`‖B(h, τ_t h)‖ = O(e^{(η + ε) t})` for every `ε > 0`. -/
theorem growth_of_twoInterval {w : ℝ → ℝ} {Lstar η : ℝ} (hw : WidthFn w Lstar) (hη : 0 ≤ η)
    (hB : TwoIntervalBound w η) {h : ℝ → ℝ} {r : ℝ} (hr : 0 < r) (hh : ContDiff ℝ ∞ h)
    (hsupp : ∀ x, r ≤ |x| → h x = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ K T : ℝ, ∀ t, T ≤ t → ‖B (cpx h) (tr t (cpx h))‖ ≤ K * Real.exp ((η + ε) * t) := by
  obtain ⟨L₀, hL₀⟩ := hB
  obtain ⟨M₀, h0⟩ := bounded_of_compact hh.continuous hsupp
  have hdc : Continuous (deriv h) := hh.continuous_deriv (by exact_mod_cast le_top)
  obtain ⟨M₁, h1⟩ : ∃ M, ∀ x, |deriv h x| ≤ M := by
    obtain ⟨M, hM⟩ := hdc.bounded_above_of_compact_support (hasCompactSupport_of_supp hsupp).deriv
    exact ⟨M, fun x => by simpa [Real.norm_eq_abs] using hM x⟩
  obtain ⟨Mχ, hχ⟩ := chi_deriv_bound
  have hM₀ : 0 ≤ M₀ := (abs_nonneg _).trans (h0 0)
  have hM₁ : 0 ≤ M₁ := (abs_nonneg _).trans (h1 0)
  have hMχ : 0 ≤ Mχ := (abs_nonneg _).trans (hχ 0)
  have hSz := Sz_nonneg
  obtain ⟨L₁, hL₁⟩ : ∃ L₁, ∀ L, L₁ ≤ L → Real.log (1 / w L) / L < ε / 8 :=
    eventually_atTop.mp ((tendsto_order.1 hw.subexp).2 (ε / 8) (by positivity))
  set C : ℝ := 2 * r + 4 with hC
  have hC0 : 0 < C := by positivity
  set A₁ : ℝ := 4 * r ^ 2 * Real.exp r * (M₀ ^ 2 + (M₁ + M₀ * Mχ) ^ 2) with hA₁
  have hA₁0 : 0 ≤ A₁ := by positivity
  refine ⟨(2 * r + 3) ^ 2 * A₁ * 256 * Real.exp (η * C) * Sz,
    max (max (L₀ + C) (Lstar + C)) (max L₁ (C + 1)), fun t ht => ?_⟩
  have htL₀ : L₀ + C ≤ t := (le_max_left _ _).trans ((le_max_left _ _).trans ht)
  have htLs : Lstar + C ≤ t := (le_max_right _ _).trans ((le_max_left _ _).trans ht)
  have htL₁ : L₁ ≤ t := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have htC : C + 1 ≤ t := (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  have hW0 : 0 < w (t + C) := hw.pos _ (by linarith)
  have hW1 : w (t + C) ≤ 1 := hw.le_one _ (by linarith)
  -- the scale `m`, the number `2J + 1` of pieces
  obtain ⟨mR, hm1, h2m, hmW'⟩ : ∃ mR : ℝ, 1 ≤ mR ∧ 2 / mR ≤ w (t + C) ∧ mR ≤ 4 / w (t + C) := by
    refine ⟨(⌈2 / w (t + C)⌉₊ : ℝ) + 1, by linarith [Nat.cast_nonneg (α := ℝ) ⌈2 / w (t + C)⌉₊],
      ?_, ?_⟩
    · have hle := Nat.le_ceil (2 / w (t + C))
      have hpos : 0 < (⌈2 / w (t + C)⌉₊ : ℝ) + 1 := by positivity
      rw [div_le_iff₀ hpos]
      rw [div_le_iff₀ hW0] at hle
      nlinarith
    · have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 / w (t + C) by positivity)
      have h2 : 2 ≤ 2 / w (t + C) := by rw [le_div_iff₀ hW0]; linarith
      have e : 4 / w (t + C) = 2 * (2 / w (t + C)) := by ring
      linarith
  have hm0 : 0 < mR := by linarith
  set J : ℕ := ⌈mR * r⌉₊ with hJ
  have hJ1 : mR * r ≤ J := Nat.le_ceil _
  have hJ2 : (J : ℝ) ≤ mR * r + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  set Km : ℝ := 4 * r ^ 2 * Real.exp r * (M₀ ^ 2 + (M₁ + mR * M₀ * Mχ) ^ 2) with hKm
  have hKm0 : 0 ≤ Km := by positivity
  have hdec : ∀ k, Decay (cpx (piece h mR J k)) Km := fun k =>
    decay_of_bounds hr.le ((piece_contDiff hh mR J k).differentiable (by simp))
      ((piece_contDiff hh mR J k).continuous_deriv (by exact_mod_cast le_top))
      (piece_supp hsupp mR J k) (piece_bounds hh hm0.le h0 h1 hχ J k).1
      (piece_bounds hh hm0.le h0 h1 hχ J k).2
  have hQu : ∀ k, ‖Q (cpx (piece h mR J k))‖ ≤ Km * Sz := fun k => norm_Q_le (hdec k)
  -- expansion of `B(h, τ_t h)` over pairs of pieces
  have hint : ∀ k, ∀ z : ℂ, Integrable (fun x : ℝ => cpx (piece h mR J k) x * cexp (z * x)) :=
    fun k z => integrable_cpx_mul_exp (piece_contDiff hh mR J k).continuous
      (piece_supp hsupp mR J k) z
  have hHh : ∀ z, H (cpx h) z = ∑ k ∈ Finset.range (2 * J + 1), H (cpx (piece h mR J k)) z := by
    intro z
    rw [← H_sum (Finset.range (2 * J + 1)) (fun k => cpx (piece h mR J k)) (fun k _ => hint k) z]
    congr 1; funext x
    simp only [cpx]
    rw [← Complex.ofReal_sum, piece_sum hsupp hm0.le hJ1 x]
  have hHt : ∀ z, H (tr t (cpx h)) z
      = ∑ l ∈ Finset.range (2 * J + 1), H (tr t (cpx (piece h mR J l))) z := by
    intro z
    rw [H_tr, hHh, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun l _ => (H_tr t _ z).symm)
  have hexp := B_sum (Finset.range (2 * J + 1)) (Finset.range (2 * J + 1))
    (fun k => cpx (piece h mR J k)) (fun l => tr t (cpx (piece h mR J l))) (cpx h) (tr t (cpx h))
    hHh hHt (fun k _ l _ => summable_term (hdec k) ((hdec l).tr t))
  have hsum_le : ‖B (cpx h) (tr t (cpx h))‖
      ≤ ((2 * J + 1 : ℕ) : ℝ) ^ 2 * (Real.exp (η * (t + C)) * (Km * Sz)) := by
    rw [hexp]
    calc ‖∑ k ∈ Finset.range (2 * J + 1), ∑ l ∈ Finset.range (2 * J + 1),
          B (cpx (piece h mR J k)) (tr t (cpx (piece h mR J l)))‖
        ≤ ∑ k ∈ Finset.range (2 * J + 1), ∑ l ∈ Finset.range (2 * J + 1),
          ‖B (cpx (piece h mR J k)) (tr t (cpx (piece h mR J l)))‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => norm_sum_le _ _))
      _ ≤ ∑ k ∈ Finset.range (2 * J + 1), ∑ l ∈ Finset.range (2 * J + 1),
          Real.exp (η * (t + C)) * (Km * Sz) := by
          refine Finset.sum_le_sum (fun k hk => Finset.sum_le_sum (fun l hl => ?_))
          exact pair_bound hw hη hL₀ hr hh hm1 hJ2 le_rfl htL₀ htLs h2m hKm0 hQu
            (by have := Finset.mem_range.mp hk; omega) (by have := Finset.mem_range.mp hl; omega)
      _ = ((2 * J + 1 : ℕ) : ℝ) ^ 2 * (Real.exp (η * (t + C)) * (Km * Sz)) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hcost := partition_cost hr hM₀ hM₁ hMχ hm1 hJ2
  have hm4 : mR ^ 4 ≤ 256 * (1 / w (t + C)) ^ 4 := by
    have : mR ≤ 4 * (1 / w (t + C)) := by rw [mul_one_div]; exact hmW'
    calc mR ^ 4 ≤ (4 * (1 / w (t + C))) ^ 4 := pow_le_pow_left₀ hm0.le this 4
      _ = 256 * (1 / w (t + C)) ^ 4 := by ring
  have hW4 : (1 / w (t + C)) ^ 4 ≤ Real.exp (ε * t) := by
    have hlog : Real.log (1 / w (t + C)) ≤ ε / 4 * t := by
      have := hL₁ (t + C) (by linarith)
      rw [div_lt_iff₀ (by linarith)] at this
      nlinarith
    have h1W : 0 < 1 / w (t + C) := by positivity
    calc (1 / w (t + C)) ^ 4 = Real.exp (Real.log (1 / w (t + C))) ^ 4 := by rw [Real.exp_log h1W]
      _ ≤ Real.exp (ε / 4 * t) ^ 4 := pow_le_pow_left₀ (Real.exp_pos _).le
          (Real.exp_le_exp.mpr hlog) 4
      _ = Real.exp (ε * t) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have hE : 0 ≤ Real.exp (η * C) * Sz * Real.exp (η * t) := by positivity
  calc ‖B (cpx h) (tr t (cpx h))‖
      ≤ ((2 * J + 1 : ℕ) : ℝ) ^ 2 * (Real.exp (η * (t + C)) * (Km * Sz)) := hsum_le
    _ = (((2 * J + 1 : ℕ) : ℝ) ^ 2 * Km) * (Real.exp (η * C) * Sz * Real.exp (η * t)) := by
        rw [show η * (t + C) = η * C + η * t by ring, Real.exp_add]; ring
    _ ≤ ((2 * r + 3) ^ 2 * A₁ * (256 * Real.exp (ε * t))) *
          (Real.exp (η * C) * Sz * Real.exp (η * t)) := by
        apply mul_le_mul_of_nonneg_right _ hE
        refine hcost.trans ?_
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hm4.trans (by nlinarith)
    _ = (2 * r + 3) ^ 2 * A₁ * 256 * Real.exp (η * C) * Sz * Real.exp ((η + ε) * t) := by
        rw [show (η + ε) * t = ε * t + η * t by ring, Real.exp_add]; ring

/-! ## The criterion (paper, Theorem 4) -/

/-- The fibre sum of the coefficients at a centred zero is (multiplicity) × (coefficient). -/
lemma fiber_sum_ne_zero {h : ℝ → ℂ} (x0 : Index) (hc : term h h x0 ≠ 0) :
    ∑' x, (if -(zc x) = -(zc x0) then term h h x else 0) ≠ 0 := by
  classical
  have hfin := multEnum_canonical.fiber_finite (canonical x0)
  set s := hfin.toFinset with hs
  have hiff : ∀ x, -(zc x) = -(zc x0) ↔ canonical x = canonical x0 := by
    intro x; simp [zc]
  have hconst : ∀ x, canonical x = canonical x0 → term h h x = term h h x0 := by
    intro x hx; unfold term; rw [show zc x = zc x0 by simp [zc, hx]]
  have e : ∑' x, (if -(zc x) = -(zc x0) then term h h x else 0) = ∑ x ∈ s, term h h x0 := by
    rw [tsum_eq_sum (s := s)]
    · refine Finset.sum_congr rfl (fun x hx => ?_)
      have hx' : canonical x = canonical x0 := by
        rw [hs, Set.Finite.mem_toFinset] at hx; exact hx
      have hp := (hiff x).mpr hx'
      simp only [hp, ↓reduceIte]
      rw [hconst x hx']
    · intro x hx
      have hx' : ¬ canonical x = canonical x0 := by
        rw [hs, Set.Finite.mem_toFinset] at hx; exact hx
      have hp : ¬ -(zc x) = -(zc x0) := fun h => hx' ((hiff x).mp h)
      simp only [hp, ↓reduceIte]
  rw [e, Finset.sum_const, nsmul_eq_mul]
  have hmem : x0 ∈ s := by rw [hs, Set.Finite.mem_toFinset]; rfl
  have hcard : (s.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr ⟨x0, hmem⟩).ne'
  exact mul_ne_zero hcard hc

/-- **One side of Theorem 4(2).** Under the two-interval bound with allowance `e^{ηL}`, no zero
lies more than `η` to the left of the critical line. -/
theorem half_sub_re_le_of_twoInterval {w : ℝ → ℝ} {Lstar η : ℝ} (hw : WidthFn w Lstar)
    (hη : 0 ≤ η) (hB : TwoIntervalBound w η) (x0 : Index) :
    1 / 2 - (canonical x0).re ≤ η := by
  obtain ⟨h, r, hr, hh, hsupp, hz, hz'⟩ := exists_bump (zc x0)
  obtain ⟨K0, hdec⟩ := decay_of_contDiff (hh.of_le (by exact_mod_cast le_top)) hr.le hsupp
  set c : Index → ℂ := term (cpx h) (cpx h) with hcdef
  set wv : Index → ℂ := fun x => -(zc x) with hwv
  have hc : Summable (fun x => ‖c x‖) := summable_norm_term hdec hdec
  have hwre : ∀ x, (wv x).re ≤ 1 / 2 := by
    intro x
    have := abs_zc_re_lt x
    simp only [hwv, Complex.neg_re]
    linarith [neg_abs_le (zc x).re]
  have hfin : ∀ T : ℝ, {x | |(wv x).im| ≤ T}.Finite := by
    intro T
    refine (multEnum_canonical.finite T).subset (fun x hx => ?_)
    simp only [mem_ofPred_eq, hwv, Complex.neg_im, abs_neg, zc_im] at hx ⊢
    exact hx
  have hc0 : c x0 ≠ 0 := by
    simp only [hcdef, term]
    exact mul_ne_zero hz ((map_ne_zero _).mpr hz')
  have hne := fiber_sum_ne_zero (h := cpx h) x0 hc0
  by_contra hlt
  push Not at hlt
  set ε := (1 / 2 - (canonical x0).re - η) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨K, T, hKT⟩ := growth_of_twoInterval hw hη hB hr hh hsupp hε0
  have hG : ∀ t : ℝ, T ≤ t → ‖∑' x, c x * cexp (t * wv x)‖ ≤ K * Real.exp ((η + ε) * t) := by
    intro t ht
    rw [← B_tr_right]
    exact hKT t ht
  have hv : η + ε < (wv x0).re := by
    simp only [hwv, Complex.neg_re, zc_re]
    rw [hε]; linarith
  exact hne (fiber_sum_eq_zero_of_growth wv c hwre hfin hc hG (wv x0) hv)

/-- **Theorem 4(2), quantitative form.** If the two-interval bound holds with allowance `e^{ηL}`
(`η ≥ 0`), every nontrivial zero satisfies `|Re ρ - 1/2| ≤ η`. -/
theorem abs_re_sub_half_le_of_twoInterval {w : ℝ → ℝ} {Lstar η : ℝ} (hw : WidthFn w Lstar)
    (hη : 0 ≤ η) (hB : TwoIntervalBound w η) :
    ∀ ρ : ℂ, IsNontrivialZero ρ → |ρ.re - 1 / 2| ≤ η := by
  intro ρ hρ
  obtain ⟨x, hx⟩ := multEnum_canonical.exists_index hρ
  obtain ⟨x', hx'⟩ := multEnum_canonical.exists_index (ZeroSymmetry.isNontrivialZero_one_sub hρ)
  have h1 := half_sub_re_le_of_twoInterval hw hη hB x
  have h2 := half_sub_re_le_of_twoInterval hw hη hB x'
  rw [show canonical x = ρ from hx] at h1
  rw [show canonical x' = 1 - ρ from hx', Complex.sub_re, Complex.one_re] at h2
  rw [abs_le]; constructor <;> linarith

/-- **Theorem 4(2) of the paper.** A zero with `Re ρ > 1/2` forces, for every `0 ≤ η < Re ρ - 1/2`,
violations `‖B(φ, ψ)‖² > e^{2ηL} ‖Q φ‖ ‖Q ψ‖` by real admissible pairs at arbitrarily large spans. -/
theorem violation_of_offline_zero {w : ℝ → ℝ} {Lstar : ℝ} (hw : WidthFn w Lstar) {ρ : ℂ}
    (hρ : IsNontrivialZero ρ) {η : ℝ} (hη : 0 ≤ η) (hlt : η < ρ.re - 1 / 2) (L₀ : ℝ) :
    ∃ L, L₀ ≤ L ∧ ∃ φ ψ : ℝ → ℝ, Admissible w L φ ψ ∧
      Real.exp (2 * η * L) * (‖Q (cpx φ)‖ * ‖Q (cpx ψ)‖) < ‖B (cpx φ) (cpx ψ)‖ ^ 2 := by
  by_contra hno
  push Not at hno
  have hB : TwoIntervalBound w η := ⟨L₀, fun L hL φ ψ hadm => hno L hL φ ψ hadm⟩
  have := abs_re_sub_half_le_of_twoInterval hw hη hB ρ hρ
  have := le_abs_self (ρ.re - 1 / 2)
  linarith

/-- **The criterion (paper, Theorem 4, final assertion).** For every width function satisfying (12),
RH holds iff the two-interval Cauchy–Schwarz inequality holds for all real admissible pairs at all
sufficiently large spans. -/
theorem RH_iff_twoInterval {w : ℝ → ℝ} {Lstar : ℝ} (hw : WidthFn w Lstar) :
    RiemannHypothesis ↔ TwoIntervalBound w 0 := by
  refine ⟨fun hRH => twoIntervalBound_of_RH hRH w, fun hB => ?_⟩
  rw [riemannHypothesis_iff]
  intro ρ hρ
  have := abs_re_sub_half_le_of_twoInterval hw le_rfl hB ρ hρ
  have := abs_nonneg (ρ.re - 1 / 2)
  have h0 : |ρ.re - 1 / 2| = 0 := by linarith
  have := abs_eq_zero.mp h0
  linarith

/-- The reciprocal width `w(L) = 1/L` satisfies (12) on `[1, ∞)` (paper, end of Section 1). -/
theorem widthFn_inv : WidthFn (fun L => 1 / L) 1 where
  pos L hL := by positivity
  le_one L hL := by rw [div_le_one (by linarith)]; exact hL
  anti := by
    intro a ha b hb hab
    simp only [Set.mem_Ici] at ha hb
    exact one_div_le_one_div_of_le (by linarith) hab
  tendsto_zero := by simpa [one_div] using tendsto_inv_atTop_zero
  subexp := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with L hL
    simp

/-- **Reciprocal-width case.** RH iff the Cauchy–Schwarz inequality holds on all real pairs supported
in `[0, 1/L]` and `[L - 1/L, L]` for all large `L`. -/
theorem RH_iff_twoInterval_inv : RiemannHypothesis ↔ TwoIntervalBound (fun L => 1 / L) 0 :=
  RH_iff_twoInterval widthFn_inv

end FleetDaneshCriterion
