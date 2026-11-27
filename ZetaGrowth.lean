import Mathlib
import ExplicitFormula

/-!
# Polynomial growth of `ζ` in the critical strip

**What is proven (no hypotheses beyond Mathlib):**

* `zeta_eq_zetaAbel` — the Euler–Maclaurin / Abel-summation continuation
  `ζ(s) = 1/(s-1) + Σ_{n≥1} (n^{-s} - ∫_n^{n+1} t^{-s} dt)` for `Re s > 0`, `s ≠ 1`
  (the integral is evaluated in closed form as `((n+1)^{1-s} - n^{1-s})/(1-s)`).
  Proof: the series converges locally uniformly on `Re s > 0` by the mean-value bound
  `‖n^{-s} - ∫_n^{n+1} t^{-s} dt‖ ≤ ‖s‖ n^{-Re s - 1}` (`norm_emTerm_le`), so it is
  holomorphic there (`differentiableOn_tsum_of_summable_norm`); it agrees with the
  Dirichlet series for `Re s > 1`; the identity theorem on three convex pieces gives
  agreement with Mathlib's `riemannZeta` on all of `Re s > 0`, `s ≠ 1`.
* `norm_zeta_le_of_half_le_re` — the **linear growth bound**
  `‖ζ s‖ ≤ ‖s-1‖⁻¹ + 3‖s‖` on the whole half-plane `Re s ≥ 1/2`, `s ≠ 1`.
* `zeta_growth_strip` (target A, exponent 1): `‖ζ s‖ ≤ 7 |Im s|` for `1/2 ≤ Re s ≤ 2`,
  `|Im s| ≥ 2`; `zeta_growth_line` (target B) is the same on any line `Re s = c`, `1/2 < c < 1`.
* `zeta_growth_strip_sqrt` / `zeta_growth_strip_rpow` (target A, **sharp exponent 1/2**):
  `‖ζ s‖ ≤ 11 |Im s|^{1/2}` on the same strip, by splitting the representation at
  `N = ⌊|Im s|⌋` (`zeta_eq_sum_add_tail`, `norm_zeta_le_split`); `zeta_growth_line_rpow` (B).
* `norm_zeta_le_of_re_ge` (target C): `‖ζ s‖ ≤ ‖ζ(1+ε)‖` for `Re s ≥ 1+ε`.
* `norm_logDeriv_zeta_le_of_re_ge` (target D): `‖ζ'/ζ(s)‖ ≤ Σ Λ(n) n^{-(1+ε)}`.

**Not proven / not attempted:** anything beyond the convexity exponent `1/2` (e.g. Weyl or
subconvexity bounds), and bounds for `Re s < 1/2` (which need the functional equation).
Every theorem is unconditional: no `sorry`, no hypotheses, no axioms beyond Mathlib's
standard three.
-/

noncomputable section

open Complex Filter Topology
open scoped LSeries.notation ArithmeticFunction

namespace ZetaGrowth

/-! ## Target (C): the trivial bound on `Re s ≥ 1 + ε` -/

/-- On `Re s ≥ 1 + ε`, `‖ζ s‖` is bounded by the real `p`-series `Σ 1/n^{1+ε}`. -/
theorem norm_zeta_le_tsum_of_re_ge {ε : ℝ} (hε : 0 < ε) {s : ℂ} (hs : 1 + ε ≤ s.re) :
    ‖riemannZeta s‖ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + ε) := by
  have h1 : 1 < s.re := by linarith
  have hsum : Summable fun n : ℕ => ‖LSeries.term 1 s n‖ :=
    summable_norm_iff.mpr (LSeriesSummable_one_iff.mpr h1)
  have hp : Summable fun n : ℕ => 1 / (n : ℝ) ^ (1 + ε) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith)
  rw [← LSeries_one_eq_riemannZeta h1, LSeries]
  refine (norm_tsum_le_tsum_norm hsum).trans (Summable.tsum_le_tsum (fun n => ?_) hsum hp)
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · positivity
  · simp only [Pi.one_apply, norm_one]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    exact one_div_le_one_div_of_le (by positivity) (Real.rpow_le_rpow_of_exponent_le hn1 hs)

/-- For real `x > 1`, `‖ζ x‖ = Σ 1/n^x`. -/
theorem norm_zeta_real_eq {x : ℝ} (hx : 1 < x) :
    ‖riemannZeta x‖ = ∑' n : ℕ, 1 / (n : ℝ) ^ x := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by simpa using hx)]
  have : (∑' n : ℕ, 1 / (n : ℂ) ^ (x : ℂ)) = ((∑' n : ℕ, 1 / (n : ℝ) ^ x : ℝ) : ℂ) := by
    simp only [one_div, ofReal_tsum, ofReal_inv, ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast]
  rw [this, norm_real, Real.norm_of_nonneg]
  exact tsum_nonneg fun n => by positivity

/-- **Target (C).** On `Re s ≥ 1 + ε` (`ε > 0`), `‖ζ s‖ ≤ ‖ζ(1 + ε)‖`; the right-hand
side is the real number `ζ(1+ε) = Σ n^{-(1+ε)}`. -/
theorem norm_zeta_le_of_re_ge {ε : ℝ} (hε : 0 < ε) {s : ℂ} (hs : 1 + ε ≤ s.re) :
    ‖riemannZeta s‖ ≤ ‖riemannZeta ((1 + ε : ℝ) : ℂ)‖ := by
  rw [norm_zeta_real_eq (by linarith)]
  exact norm_zeta_le_tsum_of_re_ge hε hs

/-! ## Target (D): the logarithmic derivative on `Re s ≥ 1 + ε` -/

/-- **Target (D).** On `Re s ≥ 1 + ε` (`ε > 0`),
`‖ζ'(s)/ζ(s)‖ ≤ Σ_n Λ(n) n^{-(1+ε)}` (the coefficients `ExplicitFormula.coeff (1+ε)`). -/
theorem norm_logDeriv_zeta_le_of_re_ge {ε : ℝ} (hε : 0 < ε) {s : ℂ} (hs : 1 + ε ≤ s.re) :
    ‖deriv riemannZeta s / riemannZeta s‖ ≤ ∑' n : ℕ, ExplicitFormula.coeff (1 + ε) n := by
  have h1 : 1 < s.re := by linarith
  have hsum : Summable fun n : ℕ => ‖LSeries.term ↗Λ s n‖ :=
    summable_norm_iff.mpr (ArithmeticFunction.LSeriesSummable_vonMangoldt h1)
  have hc : Summable (ExplicitFormula.coeff (1 + ε)) :=
    ExplicitFormula.coeff_summable (by linarith)
  have : deriv riemannZeta s / riemannZeta s = -(L ↗Λ s) := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div h1, neg_div, neg_neg]
  rw [this, norm_neg, LSeries]
  refine (norm_tsum_le_tsum_norm hsum).trans (Summable.tsum_le_tsum (fun n => ?_) hsum hc)
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · exact ExplicitFormula.coeff_nonneg _ _
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    rw [ExplicitFormula.coeff, norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Real.rpow_neg (by linarith), div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left
      (inv_anti₀ (by positivity) (Real.rpow_le_rpow_of_exponent_le hn1 hs))
      ArithmeticFunction.vonMangoldt_nonneg

/-! ## The Euler–Maclaurin remainder terms -/

/-- The Euler–Maclaurin remainder `n^{-s} - ∫_n^{n+1} t^{-s} dt`, with the integral in
closed form `((n+1)^{1-s} - n^{1-s})/(1-s)`. -/
def emTerm (n : ℕ) (s : ℂ) : ℂ :=
  (n : ℂ) ^ (-s) - (((n : ℂ) + 1) ^ (1 - s) - (n : ℂ) ^ (1 - s)) / (1 - s)

/-- The continuation of `ζ` to `Re s > 0`: `1/(s-1) + Σ_{n ≥ 1} emTerm n s`. -/
def zetaAbel (s : ℂ) : ℂ := 1 / (s - 1) + ∑' n : ℕ, emTerm (n + 1) s

/-- `‖x^z‖ = x^{Re z}` for real `x > 0`. -/
theorem norm_ofReal_cpow {x : ℝ} (hx : 0 < x) (z : ℂ) : ‖(x : ℂ) ^ z‖ = x ^ z.re := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]

/-- **Mean-value bound** for the remainder: `‖emTerm n s‖ ≤ ‖s‖ · n^{-Re s - 1}` for `n ≥ 1`,
`Re s > 0`, `s ≠ 1`. -/
theorem norm_emTerm_le {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖emTerm n s‖ ≤ ‖s‖ * (n : ℝ) ^ (-s.re - 1) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs0' : s ≠ 0 := fun h => by rw [h] at hs0; simp at hs0
  set B : ℝ := ‖s‖ * (n : ℝ) ^ (-s.re - 1) with hB
  have hBnn : 0 ≤ B := by positivity
  -- Step 1: `‖t^{-s} - n^{-s}‖ ≤ B` on `[n, n+1]`, from `‖d/dt t^{-s}‖ = ‖s‖ t^{-Re s-1}`.
  have hψ : ∀ t ∈ Set.Icc (n : ℝ) (n + 1), ‖(t : ℂ) ^ (-s) - (n : ℂ) ^ (-s)‖ ≤ B := by
    intro t ht
    have key := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun t : ℝ => (t : ℂ) ^ (-s)) (f' := fun t : ℝ => (-s) * (t : ℂ) ^ (-s - 1))
      (a := (n : ℝ)) (b := n + 1) (C := B) ?_ ?_ t ht
    · calc ‖(t : ℂ) ^ (-s) - (n : ℂ) ^ (-s)‖ ≤ B * (t - n) := key
        _ ≤ B * 1 := by gcongr; linarith [ht.2]
        _ = B := mul_one B
    · intro x hx
      have hx0 : x ≠ 0 := by linarith [hx.1]
      exact (hasDerivAt_ofReal_cpow_const hx0 (neg_ne_zero.mpr hs0')).hasDerivWithinAt
    · intro x hx
      have hxpos : 0 < x := by linarith [hx.1]
      rw [norm_mul, norm_neg, norm_ofReal_cpow hxpos]
      simp only [sub_re, neg_re, one_re]
      rw [hB]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by linarith) hx.1 (by linarith)) (norm_nonneg _)
  -- Step 2: `φ(t) = t^{1-s}/(1-s) - t·n^{-s}` has `φ' = t^{-s} - n^{-s}`, bounded by `B`.
  have hφ := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun t : ℝ => (t : ℂ) ^ (-s + 1) / (-s + 1) - (t : ℂ) * (n : ℂ) ^ (-s))
    (f' := fun t : ℝ => (t : ℂ) ^ (-s) - (n : ℂ) ^ (-s))
    (a := (n : ℝ)) (b := n + 1) (C := B) ?_ ?_ (n + 1) ⟨by linarith, le_rfl⟩
  · have heq : emTerm n s = -((((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s + 1) / (-s + 1)
        - (((n : ℝ) + 1 : ℝ) : ℂ) * (n : ℂ) ^ (-s)
        - (((n : ℝ) : ℂ) ^ (-s + 1) / (-s + 1) - ((n : ℝ) : ℂ) * (n : ℂ) ^ (-s))) := by
      unfold emTerm
      rw [show (1 : ℂ) - s = -s + 1 by ring]
      push_cast
      ring
    rw [heq, norm_neg]
    simpa using hφ
  · intro x hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s + 1) / (-s + 1)) ((x : ℂ) ^ (-s)) x :=
      hasDerivAt_ofReal_cpow_const' hx0 (by
        intro h
        apply hs1
        linear_combination -h)
    have h2 : HasDerivAt (fun y : ℝ => (y : ℂ) * (n : ℂ) ^ (-s)) ((n : ℂ) ^ (-s)) x := by
      simpa using ((hasDerivAt_id x).ofReal_comp).mul_const ((n : ℂ) ^ (-s))
    exact (h1.sub h2).hasDerivWithinAt
  · intro x hx
    exact hψ x (Set.Ico_subset_Icc_self hx)

/-- The shifted `p`-series `Σ (n+1)^a` converges for `a < -1`. -/
theorem summable_add_one_rpow {a : ℝ} (ha : a < -1) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ a := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr ha)
  refine this.congr fun n => ?_
  push_cast
  rfl

/-- The remainder series converges absolutely on `Re s > 0`, `s ≠ 1`. -/
theorem summable_emTerm {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    Summable fun n : ℕ => emTerm (n + 1) s := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1))
    ((summable_add_one_rpow (by linarith)).mul_left _) fun n => ?_
  have := norm_emTerm_le hs0 hs1 (n := n + 1) (by omega)
  push_cast at this
  exact this

/-- Partial sums of the remainder series telescope:
`Σ_{i<N} emTerm (i+1) s = Σ_{i<N} (i+1)^{-s} - ((N+1)^{1-s} - 1)/(1-s)`. -/
theorem sum_emTerm (s : ℂ) (N : ℕ) :
    ∑ i ∈ Finset.range N, emTerm (i + 1) s
      = ∑ i ∈ Finset.range N, ((i : ℂ) + 1) ^ (-s) - (((N : ℂ) + 1) ^ (1 - s) - 1) / (1 - s) := by
  have h := Finset.sum_range_sub (fun i : ℕ => ((i : ℂ) + 1) ^ (1 - s)) N
  simp only [Nat.cast_zero, zero_add, one_cpow] at h
  rw [← h, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [emTerm]
  push_cast
  ring

/-- Each remainder term is holomorphic in `s` away from `s = 1` (for `n ≥ 1`). -/
theorem emTerm_differentiableAt {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (fun z => emTerm n z) s := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : (n : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  unfold emTerm
  apply DifferentiableAt.sub
  · exact (differentiableAt_id.neg).const_cpow (Or.inl hn0)
  · refine DifferentiableAt.div ?_ ((differentiableAt_const _).sub differentiableAt_id) h1s
    exact (((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl hn1)).sub
      (((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl hn0))

/-- The right half-plane with the pole removed. -/
def rightHalf : Set ℂ := {s : ℂ | 0 < s.re ∧ s ≠ 1}

/-- `zetaAbel` is holomorphic on `Re s > 0`, `s ≠ 1` (locally uniform convergence). -/
theorem zetaAbel_differentiableOn : DifferentiableOn ℂ zetaAbel rightHalf := by
  intro s₀ hs₀
  obtain ⟨h0, h1⟩ := hs₀
  set W : Set ℂ := ({s | s₀.re / 2 < s.re} ∩ {s | ‖s‖ < ‖s₀‖ + 1}) ∩ {1}ᶜ with hW
  have hWo : IsOpen W :=
    ((isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)).inter isOpen_compl_singleton
  have hs₀W : s₀ ∈ W := ⟨⟨by simp only [Set.mem_setOf_eq]; linarith, by simp⟩, h1⟩
  have hdiff : DifferentiableOn ℂ zetaAbel W := by
    show DifferentiableOn ℂ (fun s => 1 / (s - 1) + ∑' n : ℕ, emTerm (n + 1) s) W
    apply DifferentiableOn.add
    · intro s hs
      have hd : DifferentiableAt ℂ (fun z : ℂ => 1 / (z - 1)) s :=
        (differentiableAt_const (1 : ℂ)).div (differentiableAt_id.sub_const 1)
          (sub_ne_zero.mpr hs.2)
      exact hd.differentiableWithinAt
    · refine differentiableOn_tsum_of_summable_norm
        (u := fun n : ℕ => (‖s₀‖ + 1) * ((n : ℝ) + 1) ^ (-(s₀.re / 2) - 1)) ?_ ?_ hWo ?_
      · exact (summable_add_one_rpow (by linarith)).mul_left _
      · intro n s hs
        exact (emTerm_differentiableAt (by omega) hs.2).differentiableWithinAt
      · intro n s hs
        have hre : s₀.re / 2 < s.re := hs.1.1
        have hnorm : ‖s‖ < ‖s₀‖ + 1 := hs.1.2
        calc ‖emTerm (n + 1) s‖ ≤ ‖s‖ * ((n + 1 : ℕ) : ℝ) ^ (-s.re - 1) :=
              norm_emTerm_le (by linarith) hs.2 (by omega)
          _ ≤ (‖s₀‖ + 1) * ((n : ℝ) + 1) ^ (-(s₀.re / 2) - 1) := by
              push_cast
              apply mul_le_mul hnorm.le _ (by positivity) (by positivity)
              exact Real.rpow_le_rpow_of_exponent_le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
                (by linarith)
  exact (hdiff.differentiableAt (hWo.mem_nhds hs₀W)).differentiableWithinAt

/-- For `Re s > 1`, `zetaAbel s = ζ s` (the Dirichlet series, Abel-summed). -/
theorem zetaAbel_eq_zeta_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : zetaAbel s = riemannZeta s := by
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
  have hs0 : 0 < s.re := by linarith
  have hsum : Summable fun n : ℕ => emTerm (n + 1) s := summable_emTerm hs0 hs1
  -- the Dirichlet series
  have hζ : HasSum (fun n : ℕ => ((n : ℂ) + 1) ^ (-s)) (riemannZeta s) := by
    have hsm : Summable fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s := by
      have := (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs)
      refine this.congr fun n => ?_
      push_cast
      rfl
    have := hsm.hasSum
    rw [← zeta_eq_tsum_one_div_nat_add_one_cpow hs] at this
    refine this.congr_fun fun n => ?_
    rw [cpow_neg, one_div]
  -- the boundary term tends to zero
  have hpow : Tendsto (fun N : ℕ => ((N : ℂ) + 1) ^ (1 - s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h1 : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ (-(s.re - 1))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by linarith)).comp
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    refine h1.congr fun N => ?_
    have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    rw [show ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    congr 1
    simp only [sub_re, one_re]
    ring
  -- partial sums converge to `ζ s - (0 - 1)/(1 - s)`
  have hpart : Tendsto (fun N => ∑ i ∈ Finset.range N, emTerm (i + 1) s) atTop
      (𝓝 (riemannZeta s - (0 - 1) / (1 - s))) := by
    simp_rw [sum_emTerm]
    exact hζ.tendsto_sum_nat.sub ((hpow.sub_const 1).div_const (1 - s))
  have hS : HasSum (fun n : ℕ => emTerm (n + 1) s) (riemannZeta s - (0 - 1) / (1 - s)) :=
    hsum.hasSum_iff_tendsto_nat.mpr hpart
  rw [zetaAbel, hS.tsum_eq]
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp
  ring

/-- Identity-theorem step: on a convex open `V ⊆ rightHalf` containing a point of `Re s > 1`,
`ζ = zetaAbel`. -/
theorem eqOn_zeta_zetaAbel_of_convex {V : Set ℂ} (hV : Convex ℝ V) (hVo : IsOpen V)
    (hsub : V ⊆ rightHalf) {z₀ : ℂ} (hz₀ : z₀ ∈ V) (hz₀re : 1 < z₀.re) :
    Set.EqOn riemannZeta zetaAbel V := by
  have hζ : AnalyticOnNhd ℂ riemannZeta V :=
    DifferentiableOn.analyticOnNhd
      (fun s hs => (differentiableAt_riemannZeta (hsub hs).2).differentiableWithinAt) hVo
  have hA : AnalyticOnNhd ℂ zetaAbel V := (zetaAbel_differentiableOn.mono hsub).analyticOnNhd hVo
  refine hζ.eqOn_of_preconnected_of_eventuallyEq hA hV.isPreconnected hz₀ ?_
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  exact Filter.eventuallyEq_of_mem (hopen.mem_nhds hz₀re)
    fun s hs => (zetaAbel_eq_zeta_of_one_lt_re hs).symm

/-- **The continuation identity.** For `Re s > 0`, `s ≠ 1`:
`ζ(s) = 1/(s-1) + Σ_{n≥1} (n^{-s} - ((n+1)^{1-s} - n^{1-s})/(1-s))`. -/
theorem zeta_eq_zetaAbel {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) : riemannZeta s = zetaAbel s := by
  have hre : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  rcases lt_trichotomy s.im 0 with him | him | him
  · -- lower half-plane, `z₀ = 2 - I`
    refine eqOn_zeta_zetaAbel_of_convex (V := {z | 0 < z.re} ∩ {z | z.im < 0})
      ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0))
      (hre.inter (isOpen_lt continuous_im continuous_const))
      (fun z hz => ⟨hz.1, fun h => by rw [h] at hz; simp at hz⟩)
      (z₀ := 2 - I) ⟨by simp, by simp⟩ (by simp) ⟨hs, him⟩
  · -- real axis: either `Re s > 1` (Dirichlet series) or `0 < Re s < 1`
    have hre1 : s.re ≠ 1 := fun h => hs1 (Complex.ext h (by simpa using him))
    rcases lt_or_gt_of_ne hre1 with h | h
    · -- `0 < s < 1`: use the convex set `{Re > 0} ∩ {Re - 1 < Im}`, `z₀ = 2 + 2I`
      have hL : IsLinearMap ℝ (fun z : ℂ => z.im - z.re) :=
        ⟨fun x y => by simp only [add_im, add_re]; ring,
         fun c x => by simp only [smul_im, smul_re, smul_eq_mul]; ring⟩
      refine eqOn_zeta_zetaAbel_of_convex (V := {z | 0 < z.re} ∩ {z | -1 < z.im - z.re})
        ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_gt hL (-1)))
        (hre.inter (isOpen_lt continuous_const (continuous_im.sub continuous_re)))
        (fun z hz => ⟨hz.1, fun h => by rw [h] at hz; norm_num at hz⟩)
        (z₀ := 2 + 2 * I) ⟨by simp, by simp⟩ (by simp)
        ⟨hs, by simp only [Set.mem_setOf_eq]; linarith⟩
    · exact (zetaAbel_eq_zeta_of_one_lt_re h).symm
  · -- upper half-plane, `z₀ = 2 + I`
    refine eqOn_zeta_zetaAbel_of_convex (V := {z | 0 < z.re} ∩ {z | 0 < z.im})
      ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0))
      (hre.inter (isOpen_lt continuous_const continuous_im))
      (fun z hz => ⟨hz.1, fun h => by rw [h] at hz; simp at hz⟩)
      (z₀ := 2 + I) ⟨by simp, by simp⟩ (by simp) ⟨hs, him⟩

/-! ## The telescoping `p`-series bound `Σ (n+1)^{-(1+p)} ≤ 1 + 1/p` -/

/-- Mean-value step: `(x+1)^{-(1+p)} ≤ (x^{-p} - (x+1)^{-p})/p` for `x ≥ 1`, `p > 0`. -/
theorem rpow_add_one_le_telescope {p : ℝ} (hp : 0 < p) {x : ℝ} (hx : 1 ≤ x) :
    (x + 1) ^ (-(1 + p)) ≤ (x ^ (-p) - (x + 1) ^ (-p)) / p := by
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ (-p))
    (fun t => (-p) * t ^ (-p - 1)) (by linarith : x < x + 1)
    (fun t ht => (Real.hasDerivAt_rpow_const
      (Or.inl (by linarith [ht.1] : t ≠ 0))).continuousAt.continuousWithinAt)
    (fun t ht => Real.hasDerivAt_rpow_const (Or.inl (by linarith [ht.1] : t ≠ 0)))
  rw [add_sub_cancel_left, div_one] at hcd
  have hc1 : (x + 1) ^ (-p - 1) ≤ c ^ (-p - 1) :=
    Real.rpow_le_rpow_of_nonpos (by linarith [hc.1]) hc.2.le (by linarith)
  rw [show -(1 + p) = -p - 1 by ring, le_div_iff₀ hp]
  nlinarith [hcd, hc1]

/-- `Σ_{n ≥ 0} (n+1)^{-(1+p)} ≤ 1 + 1/p` for `p > 0`. -/
theorem tsum_add_one_rpow_le {p : ℝ} (hp : 0 < p) :
    ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + p)) ≤ 1 + 1 / p := by
  refine Real.tsum_le_of_sum_range_le (fun n => by positivity) fun N => ?_
  rcases N with _ | M
  · simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_add, Real.one_rpow]
  have htel := Finset.sum_range_sub' (fun i : ℕ => ((i : ℝ) + 1) ^ (-p)) M
  simp only [Nat.cast_zero, zero_add, Real.one_rpow] at htel
  have hsum : ∑ i ∈ Finset.range M, (((i + 1 : ℕ) : ℝ) + 1) ^ (-(1 + p))
      ≤ ∑ i ∈ Finset.range M, (((i : ℝ) + 1) ^ (-p) - (((i + 1 : ℕ) : ℝ) + 1) ^ (-p)) / p := by
    refine Finset.sum_le_sum fun i _ => ?_
    have := rpow_add_one_le_telescope hp (x := (i : ℝ) + 1)
      (by linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)])
    push_cast
    exact this
  rw [← Finset.sum_div, htel] at hsum
  have hM : 0 ≤ ((M : ℝ) + 1) ^ (-p) := by positivity
  have : (1 - ((M : ℝ) + 1) ^ (-p)) / p ≤ 1 / p := by
    apply div_le_div_of_nonneg_right _ hp.le
    linarith
  linarith

/-! ## The linear growth bound on `Re s ≥ 1/2` -/

/-- The absolute constant `K = Σ_{n≥1} n^{-3/2}` (numerically `≈ 2.612`). -/
def K : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ))

/-- `K ≤ 3`. -/
theorem K_le_three : K ≤ 3 := by
  have := tsum_add_one_rpow_le (p := 1 / 2) (by norm_num)
  rw [K]
  norm_num at this ⊢
  exact this

/-- **Linear growth on the half-plane `Re s ≥ 1/2`:** `‖ζ s‖ ≤ ‖s-1‖⁻¹ + K‖s‖` (`s ≠ 1`). -/
theorem norm_zeta_le_of_half_le_re_K {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s‖ ≤ ‖s - 1‖⁻¹ + ‖s‖ * K := by
  have hs0 : 0 < s.re := by linarith
  rw [zeta_eq_zetaAbel hs0 hs1, zetaAbel]
  refine (norm_add_le _ _).trans ?_
  rw [norm_div, norm_one, one_div]
  gcongr
  calc ‖∑' n : ℕ, emTerm (n + 1) s‖
      ≤ ∑' n : ℕ, ‖s‖ * ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
        refine tsum_of_norm_bounded
          ((summable_add_one_rpow (by norm_num)).mul_left ‖s‖).hasSum fun n => ?_
        calc ‖emTerm (n + 1) s‖ ≤ ‖s‖ * ((n + 1 : ℕ) : ℝ) ^ (-s.re - 1) :=
              norm_emTerm_le hs0 hs1 (by omega)
          _ ≤ ‖s‖ * ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
              push_cast
              apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
              apply Real.rpow_le_rpow_of_exponent_le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
              linarith
    _ = ‖s‖ * K := by rw [K, tsum_mul_left]

/-- **Linear growth on the half-plane `Re s ≥ 1/2`, explicit constant:**
`‖ζ s‖ ≤ ‖s-1‖⁻¹ + 3‖s‖` for `s ≠ 1`. -/
theorem norm_zeta_le_of_half_le_re {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s‖ ≤ ‖s - 1‖⁻¹ + 3 * ‖s‖ := by
  calc ‖riemannZeta s‖ ≤ ‖s - 1‖⁻¹ + ‖s‖ * K := norm_zeta_le_of_half_le_re_K hs hs1
    _ ≤ ‖s - 1‖⁻¹ + ‖s‖ * 3 := by gcongr; exact K_le_three
    _ = ‖s - 1‖⁻¹ + 3 * ‖s‖ := by ring

/-- **Target (A): polynomial (linear) growth in the critical strip.**
For `1/2 ≤ Re s ≤ 2` and `|Im s| ≥ 2`, `‖ζ s‖ ≤ 7 |Im s|`. -/
theorem zeta_growth_strip {s : ℂ} (h₁ : 1 / 2 ≤ s.re) (h₂ : s.re ≤ 2) (ht : 2 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 7 * |s.im| := by
  have hs1 : s ≠ 1 := fun h => by rw [h] at ht; norm_num at ht
  have h := norm_zeta_le_of_half_le_re h₁ hs1
  have hsm : ‖s - 1‖⁻¹ ≤ 2⁻¹ := by
    apply inv_anti₀ (by norm_num)
    calc (2 : ℝ) ≤ |s.im| := ht
      _ = |(s - 1).im| := by simp
      _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
  have hs : ‖s‖ ≤ 2 + |s.im| := by
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 2 + |s.im| := by
          gcongr
          rw [abs_le]
          constructor <;> linarith
  calc ‖riemannZeta s‖ ≤ ‖s - 1‖⁻¹ + 3 * ‖s‖ := h
    _ ≤ 2⁻¹ + 3 * (2 + |s.im|) := by gcongr
    _ ≤ 7 * |s.im| := by nlinarith [ht]

/-- **Target (A), existential form.** -/
theorem exists_zeta_growth_strip :
    ∃ C : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| → ‖riemannZeta s‖ ≤ C * |s.im| :=
  ⟨7, fun _ h₁ h₂ ht => zeta_growth_strip h₁ h₂ ht⟩

/-- **Target (B): growth on a vertical line `Re s = c`, `1/2 < c < 1`:**
`‖ζ(c + it)‖ ≤ 7 |t|` for `|t| ≥ 2`. -/
theorem zeta_growth_line {c : ℝ} (hc₁ : 1 / 2 < c) (hc₂ : c < 1) {t : ℝ} (ht : 2 ≤ |t|) :
    ‖riemannZeta ((c : ℂ) + t * I)‖ ≤ 7 * |t| := by
  have hre : ((c : ℂ) + t * I).re = c := by simp
  have him : ((c : ℂ) + t * I).im = t := by simp
  have := zeta_growth_strip (s := (c : ℂ) + t * I) (by rw [hre]; linarith) (by rw [hre]; linarith)
    (by rw [him]; exact ht)
  rwa [him] at this

/-! ## The sharper bound `‖ζ s‖ ≪ |Im s|^{1/2}`: split the representation at `N ≈ |Im s|` -/

/-- **Representation split at `N`.** For `Re s > 0`, `s ≠ 1` and any `N`,
`ζ(s) = Σ_{n=1}^{N} n^{-s} + (N+1)^{1-s}/(s-1) + Σ_{n > N} emTerm n s`. -/
theorem zeta_eq_sum_add_tail {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (N : ℕ) :
    riemannZeta s = ∑ i ∈ Finset.range N, ((i : ℂ) + 1) ^ (-s)
      + ((N : ℂ) + 1) ^ (1 - s) / (s - 1) + ∑' n : ℕ, emTerm (n + N + 1) s := by
  have hsum := summable_emTerm hs hs1
  have hsplit := Summable.sum_add_tsum_nat_add N hsum
  rw [zeta_eq_zetaAbel hs hs1, zetaAbel, ← hsplit, sum_emTerm]
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp
  ring

/-- Mean-value step: `(x+1)^{-1/2} ≤ 2((x+1)^{1/2} - x^{1/2})` for `x ≥ 0`. -/
theorem rpow_neg_half_le_telescope {x : ℝ} (hx : 0 ≤ x) :
    (x + 1) ^ (-(1 / 2 : ℝ)) ≤ 2 * ((x + 1) ^ (1 / 2 : ℝ) - x ^ (1 / 2 : ℝ)) := by
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ (1 / 2 : ℝ))
    (fun t => (1 / 2 : ℝ) * t ^ ((1 / 2 : ℝ) - 1)) (by linarith : x < x + 1)
    (Real.continuous_rpow_const (by norm_num)).continuousOn
    (fun t ht => Real.hasDerivAt_rpow_const (Or.inl (by linarith [ht.1] : t ≠ 0)))
  rw [add_sub_cancel_left, div_one] at hcd
  have hc1 : (x + 1) ^ ((1 / 2 : ℝ) - 1) ≤ c ^ ((1 / 2 : ℝ) - 1) :=
    Real.rpow_le_rpow_of_nonpos (by linarith [hc.1]) hc.2.le (by norm_num)
  rw [show -(1 / 2 : ℝ) = (1 / 2 : ℝ) - 1 by norm_num]
  linarith

/-- `Σ_{i<N} (i+1)^{-1/2} ≤ 2 N^{1/2}`. -/
theorem sum_add_one_rpow_neg_half_le (N : ℕ) :
    ∑ i ∈ Finset.range N, ((i : ℝ) + 1) ^ (-(1 / 2 : ℝ)) ≤ 2 * (N : ℝ) ^ (1 / 2 : ℝ) := by
  have htel := Finset.sum_range_sub (fun i : ℕ => (i : ℝ) ^ (1 / 2 : ℝ)) N
  simp only [Nat.cast_zero, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), sub_zero] at htel
  calc ∑ i ∈ Finset.range N, ((i : ℝ) + 1) ^ (-(1 / 2 : ℝ))
      ≤ ∑ i ∈ Finset.range N,
          2 * (((i + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) - (i : ℝ) ^ (1 / 2 : ℝ)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := rpow_neg_half_le_telescope (x := (i : ℝ)) (Nat.cast_nonneg i)
        push_cast
        exact this
    _ = 2 * (N : ℝ) ^ (1 / 2 : ℝ) := by rw [← Finset.mul_sum, htel]

/-- Specialization of `rpow_add_one_le_telescope` to `p = 1/2`. -/
theorem rpow_neg_three_half_le_telescope {x : ℝ} (hx : 1 ≤ x) :
    (x + 1) ^ (-(3 / 2 : ℝ)) ≤ 2 * (x ^ (-(1 / 2 : ℝ)) - (x + 1) ^ (-(1 / 2 : ℝ))) := by
  have := rpow_add_one_le_telescope (p := 1 / 2) (by norm_num) hx
  rw [show -(1 + (1 / 2 : ℝ)) = -(3 / 2 : ℝ) by norm_num] at this
  calc (x + 1) ^ (-(3 / 2 : ℝ))
      ≤ (x ^ (-(1 / 2 : ℝ)) - (x + 1) ^ (-(1 / 2 : ℝ))) / (1 / 2) := this
    _ = 2 * (x ^ (-(1 / 2 : ℝ)) - (x + 1) ^ (-(1 / 2 : ℝ))) := by ring

/-- Tail bound: `Σ_{m ≥ 0} (m + N + 1)^{-3/2} ≤ 2 N^{-1/2}` for `N ≥ 1`. -/
theorem tsum_tail_rpow_le {N : ℕ} (hN : 1 ≤ N) :
    ∑' m : ℕ, ((m : ℝ) + N + 1) ^ (-(3 / 2 : ℝ)) ≤ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine Real.tsum_le_of_sum_range_le (fun m => by positivity) fun M => ?_
  have htel := Finset.sum_range_sub' (fun m : ℕ => ((m : ℝ) + N) ^ (-(1 / 2 : ℝ))) M
  simp only [Nat.cast_zero, zero_add] at htel
  calc ∑ m ∈ Finset.range M, ((m : ℝ) + N + 1) ^ (-(3 / 2 : ℝ))
      ≤ ∑ m ∈ Finset.range M,
          2 * (((m : ℝ) + N) ^ (-(1 / 2 : ℝ)) - (((m + 1 : ℕ) : ℝ) + N) ^ (-(1 / 2 : ℝ))) := by
        refine Finset.sum_le_sum fun m _ => ?_
        have := rpow_neg_three_half_le_telescope (x := (m : ℝ) + N)
          (by linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])
        push_cast
        rw [show ((m : ℝ) + 1 + N) = (m : ℝ) + N + 1 by ring]
        exact this
    _ = 2 * ((N : ℝ) ^ (-(1 / 2 : ℝ)) - ((M : ℝ) + N) ^ (-(1 / 2 : ℝ))) := by
        rw [← Finset.mul_sum, htel]
    _ ≤ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
        have : 0 ≤ ((M : ℝ) + N) ^ (-(1 / 2 : ℝ)) := by positivity
        linarith

/-- The shifted `p`-series `Σ (n + N + 1)^a` converges for `a < -1`. -/
theorem summable_add_rpow (N : ℕ) {a : ℝ} (ha : a < -1) :
    Summable fun n : ℕ => ((n : ℝ) + N + 1) ^ a := by
  have := (summable_nat_add_iff N).mpr (summable_add_one_rpow ha)
  refine this.congr fun n => ?_
  push_cast
  rfl

/-- **The split bound.** For `Re s ≥ 1/2`, `s ≠ 1`, `N ≥ 1`:
`‖ζ s‖ ≤ 2 N^{1/2} + (N+1)^{1/2}/‖s-1‖ + 2 ‖s‖ N^{-1/2}`. -/
theorem norm_zeta_le_split {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s‖ ≤ 2 * (N : ℝ) ^ (1 / 2 : ℝ) + ((N : ℝ) + 1) ^ (1 / 2 : ℝ) / ‖s - 1‖
      + ‖s‖ * (2 * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have hs0 : 0 < s.re := by linarith
  rw [zeta_eq_sum_add_tail hs0 hs1 N]
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  refine add_le_add (add_le_add ?_ ?_) ?_
  · -- the partial sum
    calc ‖∑ i ∈ Finset.range N, ((i : ℂ) + 1) ^ (-s)‖
        ≤ ∑ i ∈ Finset.range N, ‖((i : ℂ) + 1) ^ (-s)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range N, ((i : ℝ) + 1) ^ (-(1 / 2 : ℝ)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hpos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
          rw [show ((i : ℂ) + 1) = (((i : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
            norm_ofReal_cpow hpos, neg_re]
          exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ ≤ 2 * (N : ℝ) ^ (1 / 2 : ℝ) := sum_add_one_rpow_neg_half_le N
  · -- the boundary term
    have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    rw [norm_div, show ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
      norm_ofReal_cpow hpos, sub_re, one_re]
    exact div_le_div_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)) (norm_nonneg _)
  · -- the tail
    calc ‖∑' n : ℕ, emTerm (n + N + 1) s‖
        ≤ ∑' n : ℕ, ‖s‖ * ((n : ℝ) + N + 1) ^ (-(3 / 2 : ℝ)) := by
          refine tsum_of_norm_bounded
            ((summable_add_rpow N (by norm_num)).mul_left ‖s‖).hasSum fun n => ?_
          calc ‖emTerm (n + N + 1) s‖
              ≤ ‖s‖ * ((n + N + 1 : ℕ) : ℝ) ^ (-s.re - 1) := norm_emTerm_le hs0 hs1 (by omega)
            _ ≤ ‖s‖ * ((n : ℝ) + N + 1) ^ (-(3 / 2 : ℝ)) := by
                push_cast
                apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
                apply Real.rpow_le_rpow_of_exponent_le
                  (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n), (N.cast_nonneg : (0 : ℝ) ≤ N)])
                linarith
      _ = ‖s‖ * ∑' n : ℕ, ((n : ℝ) + N + 1) ^ (-(3 / 2 : ℝ)) := tsum_mul_left
      _ ≤ ‖s‖ * (2 * (N : ℝ) ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (tsum_tail_rpow_le hN) (norm_nonneg _)

/-- **Target (A), sharp form.** For `1/2 ≤ Re s ≤ 2` and `|Im s| ≥ 2`,
`‖ζ s‖ ≤ 11 √|Im s|` — the classical convexity-type bound `ζ(σ + it) ≪ |t|^{1/2}`,
obtained by splitting the representation at `N = ⌊|Im s|⌋`. -/
theorem zeta_growth_strip_sqrt {s : ℂ} (h₁ : 1 / 2 ≤ s.re) (h₂ : s.re ≤ 2) (ht : 2 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 11 * Real.sqrt |s.im| := by
  have hs1 : s ≠ 1 := fun h => by rw [h] at ht; norm_num at ht
  set T := |s.im| with hT
  have hT0 : 0 ≤ T := abs_nonneg _
  set N := ⌊T⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by rw [Nat.cast_one]; linarith)
  have hNle : (N : ℝ) ≤ T := Nat.floor_le hT0
  have hltN : T < N + 1 := Nat.lt_floor_add_one T
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have h := norm_zeta_le_split h₁ hs1 hN1
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.rpow_neg (Nat.cast_nonneg N),
    ← Real.sqrt_eq_rpow] at h
  -- the elementary facts about `s`
  have hsm : 2 ≤ ‖s - 1‖ := by
    calc (2 : ℝ) ≤ |s.im| := ht
      _ = |(s - 1).im| := by simp
      _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
  have hs : ‖s‖ ≤ 2 + T := by
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 2 + T := by
          gcongr
          rw [abs_le]
          constructor <;> linarith
  -- square roots
  set a := Real.sqrt T with ha_def
  set b := Real.sqrt (N : ℝ) with hb_def
  have ha : a * a = T := Real.mul_self_sqrt hT0
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hbpos : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have hba : b ≤ a := Real.sqrt_le_sqrt hNle
  have hab : a ≤ 2 * b := by
    have h4 : T ≤ 4 * N := by linarith
    calc a = Real.sqrt T := rfl
      _ ≤ Real.sqrt (4 * N) := Real.sqrt_le_sqrt h4
      _ = 2 * b := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 * 2 by norm_num,
            Real.sqrt_mul_self (by norm_num)]
  have hN1' : Real.sqrt ((N : ℝ) + 1) ≤ 2 * a := by
    calc Real.sqrt ((N : ℝ) + 1) ≤ Real.sqrt (4 * T) := Real.sqrt_le_sqrt (by linarith)
      _ = 2 * a := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 * 2 by norm_num,
            Real.sqrt_mul_self (by norm_num)]
  -- the three terms
  have hterm2 : Real.sqrt ((N : ℝ) + 1) / ‖s - 1‖ ≤ a := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hterm3 : ‖s‖ * (2 * b⁻¹) ≤ 8 * a := by
    rw [show ‖s‖ * (2 * b⁻¹) = (2 * ‖s‖) / b by ring, div_le_iff₀ hbpos]
    nlinarith [mul_le_mul_of_nonneg_left hab ha0]
  calc ‖riemannZeta s‖ ≤ 2 * b + Real.sqrt ((N : ℝ) + 1) / ‖s - 1‖ + ‖s‖ * (2 * b⁻¹) := h
    _ ≤ 2 * a + a + 8 * a := by gcongr
    _ = 11 * a := by ring

/-- **Target (A), sharp form with `rpow`:** `‖ζ s‖ ≤ 11 |Im s|^{1/2}` on
`1/2 ≤ Re s ≤ 2`, `|Im s| ≥ 2`. -/
theorem zeta_growth_strip_rpow {s : ℂ} (h₁ : 1 / 2 ≤ s.re) (h₂ : s.re ≤ 2) (ht : 2 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 11 * |s.im| ^ (1 / 2 : ℝ) := by
  rw [← Real.sqrt_eq_rpow]
  exact zeta_growth_strip_sqrt h₁ h₂ ht

/-- **Target (B), sharp form:** on the line `Re s = c`, `1/2 < c < 1`,
`‖ζ(c + it)‖ ≤ 11 |t|^{1/2}` for `|t| ≥ 2`. -/
theorem zeta_growth_line_rpow {c : ℝ} (hc₁ : 1 / 2 < c) (hc₂ : c < 1) {t : ℝ} (ht : 2 ≤ |t|) :
    ‖riemannZeta ((c : ℂ) + t * I)‖ ≤ 11 * |t| ^ (1 / 2 : ℝ) := by
  have hre : ((c : ℂ) + t * I).re = c := by simp
  have him : ((c : ℂ) + t * I).im = t := by simp
  have := zeta_growth_strip_rpow (s := (c : ℂ) + t * I) (by rw [hre]; linarith)
    (by rw [hre]; linarith) (by rw [him]; exact ht)
  rwa [him] at this

end ZetaGrowth

end
