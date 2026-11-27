import Mathlib
import ZetaGrowth

/-!
# Second-order Euler–Maclaurin continuation of `ζ` and polynomial growth for `Re s > -1`

`ZetaGrowth` proves `ζ(s) = zetaAbel s = 1/(s-1) + Σ_{n≥1} emTerm n s` on `Re s > 0`, where
`emTerm n s = n^{-s} - ∫_n^{n+1} t^{-s} dt`.  This file pushes the Euler–Maclaurin expansion one
step further and proves everything *unconditionally* (no hypotheses beyond Mathlib):

* `emTerm₂ n s = emTerm n s + ((n+1)^{-s} - n^{-s})/2 + (s/12)((n+1)^{-s-1} - n^{-s-1})` is the
  second-order remainder.  It equals `-(H(n+1) - H(n))` for the explicit antiderivative
  `H = emAnti n s` of `Q(t) s(s+1) t^{-s-2}`, `Q(t) = ((t-n)² - (t-n) + 1/6)/2 = P₂(t)/2`
  (`emTerm₂_eq_emAnti`, `emAnti_hasDerivAt`), whence the **mean-value bound**
  `‖emTerm₂ n s‖ ≤ ‖s‖‖s+1‖/12 · n^{-Re s - 2}` (`norm_emTerm₂_le`), summable on `Re s > -1`.
* `zetaAbel₂ s = 1/(s-1) + 1/2 + s/12 + Σ_{n≥1} emTerm₂ n s` is holomorphic on `Re s > -1`,
  `s ≠ 1` (`zetaAbel₂_differentiableOn`), agrees with `zetaAbel` on `Re s > 0`
  (`zetaAbel₂_eq_zetaAbel`, by telescoping), hence — identity theorem, exactly as in
  `ZetaGrowth` — **`zeta_eq_zetaAbel₂ : ζ s = zetaAbel₂ s` for `Re s > -1`, `s ≠ 1`**.
* Splitting at `N` (`zeta_eq_sum_add_tail₂`, `norm_zeta_le_split₂`) and choosing `N = ⌊|Im s|⌋`
  gives the **polynomial growth bound with exponent `3/2`**:
  `zeta_growth_wide_bound : ‖ζ s‖ ≤ 7 |Im s|^{3/2}` for `-1/2 ≤ Re s ≤ 2`, `|Im s| ≥ 2`;
  `zeta_growth_neg_strip` (the strip `-1/2 ≤ Re s ≤ 1/2`) and `zeta_growth_wide`
  (`-1/2 ≤ Re s ≤ 2`) are its existential forms.  Note the wide bound is proven *directly* from
  the second-order representation, so no combination with `ZetaGrowth.zeta_growth_strip_sqrt`
  is needed (`zeta_growth_wide_of_sqrt` records that route as well).

**Not proven / not attempted:** anything for `Re s ≤ -1` (a third Euler–Maclaurin step or the
functional equation would be needed), and exponents sharper than `3/2` on `Re s = -1/2`.
-/

noncomputable section

open Complex Filter Topology
open ZetaGrowth

namespace ZetaGrowthNeg

/-! ## The second-order Euler–Maclaurin remainder -/

/-- The second-order Euler–Maclaurin remainder: the first-order remainder `emTerm n s` corrected
by the boundary terms `((n+1)^{-s} - n^{-s})/2` and `(s/12)((n+1)^{-s-1} - n^{-s-1})`.
Classically `emTerm₂ n s = -∫_n^{n+1} (P₂(t)/2) s(s+1) t^{-s-2} dt`, `P₂(t) = {t}² - {t} + 1/6`. -/
def emTerm₂ (n : ℕ) (s : ℂ) : ℂ :=
  emTerm n s + (((n : ℂ) + 1) ^ (-s) - (n : ℂ) ^ (-s)) / 2
    + s / 12 * (((n : ℂ) + 1) ^ (-s - 1) - (n : ℂ) ^ (-s - 1))

/-- The second-order continuation of `ζ`: `1/(s-1) + 1/2 + s/12 + Σ_{n ≥ 1} emTerm₂ n s`. -/
def zetaAbel₂ (s : ℂ) : ℂ := 1 / (s - 1) + 1 / 2 + s / 12 + ∑' n : ℕ, emTerm₂ (n + 1) s

/-- The (real) polynomial `Q(x) = ((x-n)² - (x-n) + 1/6)/2 = P₂(x)/2` on `[n, n+1]`. -/
def bern₂ (n : ℕ) (x : ℝ) : ℝ := ((x - n) * (x - n) - (x - n) + 1 / 6) / 2

/-- The antiderivative `H(z) = Q(z)·(-s) z^{-s-1} - (z - n - 1/2) z^{-s} + z^{1-s}/(1-s)` of
`Q(z) s(s+1) z^{-s-2}` (as a function of a complex variable, later restricted to real `z`). -/
def emAnti (n : ℕ) (s : ℂ) (z : ℂ) : ℂ :=
  ((z - n) * (z - n) - (z - n) + 1 / 6) / 2 * (-s) * z ^ (-s - 1)
    - (z - n - 1 / 2) * z ^ (-s) + z ^ (-s + 1) / (-s + 1)

/-- `|Q(x)| ≤ 1/12` for `x ∈ [n, n+1]`. -/
theorem abs_bern₂_le {n : ℕ} {x : ℝ} (hx : x ∈ Set.Icc (n : ℝ) (n + 1)) :
    |bern₂ n x| ≤ 1 / 12 := by
  obtain ⟨h1, h2⟩ := hx
  rw [bern₂, abs_le]
  constructor <;> nlinarith [sq_nonneg (x - n - 1 / 2)]

/-- `emTerm₂ n s = -(H(n+1) - H(n))`. -/
theorem emTerm₂_eq_emAnti (n : ℕ) (s : ℂ) :
    emTerm₂ n s = -(emAnti n s (((n : ℝ) + 1 : ℝ)) - emAnti n s ((n : ℝ))) := by
  unfold emTerm₂ emTerm emAnti
  rw [show (1 : ℂ) - s = -s + 1 by ring]
  push_cast
  ring

/-- `H'(x) = Q(x) s (s+1) x^{-s-2}` for real `x > 0` (`s ≠ 1`). -/
theorem emAnti_hasDerivAt (n : ℕ) {s : ℂ} (hs1 : s ≠ 1) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => emAnti n s t)
      (((bern₂ n x : ℝ) : ℂ) * (s * (s + 1)) * (x : ℂ) ^ (-s - 2)) x := by
  have hxs : (x : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.mpr hx
  have h1s : (-s + 1) ≠ 0 := by
    intro h
    apply hs1
    linear_combination -h
  have hp1 : HasDerivAt (fun z : ℂ => z ^ (-s - 1)) ((-s - 1) * (x : ℂ) ^ (-s - 1 - 1)) x :=
    (Complex.hasStrictDerivAt_cpow_const hxs).hasDerivAt
  have hp0 : HasDerivAt (fun z : ℂ => z ^ (-s)) ((-s) * (x : ℂ) ^ (-s - 1)) x :=
    (Complex.hasStrictDerivAt_cpow_const hxs).hasDerivAt
  have hp2 : HasDerivAt (fun z : ℂ => z ^ (-s + 1)) ((-s + 1) * (x : ℂ) ^ (-s + 1 - 1)) x :=
    (Complex.hasStrictDerivAt_cpow_const hxs).hasDerivAt
  have hlin : HasDerivAt (fun z : ℂ => z - n) 1 x := (hasDerivAt_id' (x := (x : ℂ))).sub_const _
  have hQ : HasDerivAt (fun z : ℂ => ((z - n) * (z - n) - (z - n) + 1 / 6) / 2)
      ((1 * ((x : ℂ) - n) + ((x : ℂ) - n) * 1 - 1) / 2) x :=
    (((hlin.mul hlin).sub hlin).add_const _).div_const _
  have hlin2 : HasDerivAt (fun z : ℂ => z - n - 1 / 2) 1 x := hlin.sub_const _
  have hE := (((hQ.mul_const (-s)).mul hp1).sub (hlin2.mul hp0)).add (hp2.div_const (-s + 1))
  have hE' : HasDerivAt (fun z : ℂ => emAnti n s z) _ x := hE
  refine hE'.comp_ofReal.congr_deriv ?_
  have e1 : (x : ℂ) ^ (-s - 1 - 1) = (x : ℂ) ^ (-s - 2) := by congr 1; ring
  have e2 : (x : ℂ) ^ (-s + 1 - 1) = (x : ℂ) ^ (-s) := by congr 1; ring
  rw [e1, e2, bern₂]
  push_cast
  field_simp
  ring

/-- **Mean-value bound** for the second-order remainder:
`‖emTerm₂ n s‖ ≤ ‖s‖ ‖s+1‖ / 12 · n^{-Re s - 2}` for `n ≥ 1`, `Re s ≥ -2`, `s ≠ 1`. -/
theorem norm_emTerm₂_le {s : ℂ} (hs : -2 ≤ s.re) (hs1 : s ≠ 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖emTerm₂ n s‖ ≤ ‖s‖ * ‖s + 1‖ / 12 * (n : ℝ) ^ (-s.re - 2) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set B : ℝ := ‖s‖ * ‖s + 1‖ / 12 * (n : ℝ) ^ (-s.re - 2) with hB
  have key := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun t : ℝ => emAnti n s t)
    (f' := fun t : ℝ => ((bern₂ n t : ℝ) : ℂ) * (s * (s + 1)) * (t : ℂ) ^ (-s - 2))
    (a := (n : ℝ)) (b := n + 1) (C := B) ?_ ?_ (n + 1) ⟨by linarith, le_rfl⟩
  · rw [emTerm₂_eq_emAnti, norm_neg]
    simpa using key
  · intro x hx
    exact (emAnti_hasDerivAt n hs1 (by linarith [hx.1])).hasDerivWithinAt
  · intro x hx
    have hxpos : 0 < x := by linarith [hx.1]
    show ‖((bern₂ n x : ℝ) : ℂ) * (s * (s + 1)) * (x : ℂ) ^ (-s - 2)‖ ≤ B
    rw [norm_mul, norm_mul, norm_mul, norm_real, Real.norm_eq_abs, norm_ofReal_cpow hxpos]
    have hre : (-s - 2).re = -s.re - 2 := by simp
    rw [hre]
    have hQ := abs_bern₂_le (n := n) (Set.Ico_subset_Icc_self hx)
    have hpow : x ^ (-s.re - 2) ≤ (n : ℝ) ^ (-s.re - 2) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hx.1 (by linarith)
    rw [hB]
    calc |bern₂ n x| * (‖s‖ * ‖s + 1‖) * x ^ (-s.re - 2)
        ≤ (1 / 12) * (‖s‖ * ‖s + 1‖) * (n : ℝ) ^ (-s.re - 2) := by gcongr
      _ = ‖s‖ * ‖s + 1‖ / 12 * (n : ℝ) ^ (-s.re - 2) := by ring

/-- The second-order remainder series converges absolutely on `Re s > -1`, `s ≠ 1`. -/
theorem summable_emTerm₂ {s : ℂ} (hs : -1 < s.re) (hs1 : s ≠ 1) :
    Summable fun n : ℕ => emTerm₂ (n + 1) s := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => ‖s‖ * ‖s + 1‖ / 12 * ((n : ℝ) + 1) ^ (-s.re - 2))
    ((summable_add_one_rpow (by linarith)).mul_left _) fun n => ?_
  have := norm_emTerm₂_le (by linarith) hs1 (n := n + 1) (by omega)
  push_cast at this
  exact this

/-- Each second-order term is holomorphic in `s` away from `s = 1` (for `n ≥ 1`). -/
theorem emTerm₂_differentiableAt {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (fun z => emTerm₂ n z) s := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : (n : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  have hd1 : DifferentiableAt ℂ (fun z : ℂ => -z) s := differentiableAt_id.neg
  have hd2 : DifferentiableAt ℂ (fun z : ℂ => -z - 1) s := hd1.sub_const 1
  unfold emTerm₂
  refine ((emTerm_differentiableAt hn hs1).add ?_).add ?_
  · exact ((hd1.const_cpow (Or.inl hn1)).sub (hd1.const_cpow (Or.inl hn0))).div_const _
  · exact (differentiableAt_id.div_const _).mul
      ((hd2.const_cpow (Or.inl hn1)).sub (hd2.const_cpow (Or.inl hn0)))

/-! ## Telescoping: `zetaAbel₂ = zetaAbel` on `Re s > 0` -/

/-- Partial sums of the second-order series in terms of the first-order ones:
`Σ_{i<N} emTerm₂ (i+1) s = Σ_{i<N} emTerm (i+1) s + ((N+1)^{-s} - 1)/2 + (s/12)((N+1)^{-s-1} - 1)`. -/
theorem sum_emTerm₂_eq (s : ℂ) (N : ℕ) :
    ∑ i ∈ Finset.range N, emTerm₂ (i + 1) s
      = ∑ i ∈ Finset.range N, emTerm (i + 1) s + (((N : ℂ) + 1) ^ (-s) - 1) / 2
        + s / 12 * (((N : ℂ) + 1) ^ (-s - 1) - 1) := by
  have h0 := Finset.sum_range_sub (fun i : ℕ => ((i : ℂ) + 1) ^ (-s)) N
  have h1 := Finset.sum_range_sub (fun i : ℕ => ((i : ℂ) + 1) ^ (-s - 1)) N
  simp only [Nat.cast_zero, zero_add, one_cpow] at h0 h1
  rw [← h0, ← h1, Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [emTerm₂]
  push_cast
  ring

/-- Fully expanded partial sums:
`Σ_{i<N} emTerm₂ (i+1) s = Σ_{i<N} (i+1)^{-s} - ((N+1)^{1-s} - 1)/(1-s) + ((N+1)^{-s} - 1)/2
  + (s/12)((N+1)^{-s-1} - 1)`. -/
theorem sum_emTerm₂ (s : ℂ) (N : ℕ) :
    ∑ i ∈ Finset.range N, emTerm₂ (i + 1) s
      = ∑ i ∈ Finset.range N, ((i : ℂ) + 1) ^ (-s) - (((N : ℂ) + 1) ^ (1 - s) - 1) / (1 - s)
        + (((N : ℂ) + 1) ^ (-s) - 1) / 2 + s / 12 * (((N : ℂ) + 1) ^ (-s - 1) - 1) := by
  rw [sum_emTerm₂_eq, sum_emTerm]

/-- `(N+1)^c → 0` as `N → ∞` when `Re c < 0`. -/
theorem tendsto_add_one_cpow_zero {c : ℂ} (hc : c.re < 0) :
    Tendsto (fun N : ℕ => ((N : ℂ) + 1) ^ c) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ (-(-c.re))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith)).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  refine h1.congr fun N => ?_
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [show ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
    norm_cpow_eq_rpow_re_of_pos hpos, neg_neg]

/-- On `Re s > 0`, `s ≠ 1`, the two continuations agree: `zetaAbel₂ s = zetaAbel s`. -/
theorem zetaAbel₂_eq_zetaAbel {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    zetaAbel₂ s = zetaAbel s := by
  have hsum := summable_emTerm hs hs1
  have hsum₂ := summable_emTerm₂ (by linarith) hs1
  have h0 : Tendsto (fun N : ℕ => ((N : ℂ) + 1) ^ (-s)) atTop (𝓝 0) :=
    tendsto_add_one_cpow_zero (by rw [neg_re]; linarith)
  have h1 : Tendsto (fun N : ℕ => ((N : ℂ) + 1) ^ (-s - 1)) atTop (𝓝 0) :=
    tendsto_add_one_cpow_zero (by rw [sub_re, neg_re, one_re]; linarith)
  have hpart : Tendsto (fun N => ∑ i ∈ Finset.range N, emTerm₂ (i + 1) s) atTop
      (𝓝 ((∑' n : ℕ, emTerm (n + 1) s) + (0 - 1) / 2 + s / 12 * (0 - 1))) := by
    simp_rw [sum_emTerm₂_eq]
    exact (hsum.hasSum.tendsto_sum_nat.add ((h0.sub_const 1).div_const 2)).add
      ((h1.sub_const 1).const_mul (s / 12))
  have hS : HasSum (fun n : ℕ => emTerm₂ (n + 1) s)
      ((∑' n : ℕ, emTerm (n + 1) s) + (0 - 1) / 2 + s / 12 * (0 - 1)) :=
    hsum₂.hasSum_iff_tendsto_nat.mpr hpart
  rw [zetaAbel₂, hS.tsum_eq, zetaAbel]
  ring

/-! ## Holomorphy of `zetaAbel₂` on `Re s > -1` and the identity theorem -/

/-- The half-plane `Re s > -1` with the pole removed. -/
def leftHalf : Set ℂ := {s : ℂ | -1 < s.re ∧ s ≠ 1}

/-- `zetaAbel₂` is holomorphic on `Re s > -1`, `s ≠ 1` (locally uniform convergence). -/
theorem zetaAbel₂_differentiableOn : DifferentiableOn ℂ zetaAbel₂ leftHalf := by
  intro s₀ hs₀
  obtain ⟨h0, h1⟩ := hs₀
  set W : Set ℂ := ({s | (s₀.re - 1) / 2 < s.re} ∩ {s | ‖s‖ < ‖s₀‖ + 1}) ∩ {1}ᶜ with hW
  have hWo : IsOpen W :=
    ((isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)).inter isOpen_compl_singleton
  have hs₀W : s₀ ∈ W := ⟨⟨by simp only [Set.mem_setOf_eq]; linarith, by simp⟩, h1⟩
  have hdiff : DifferentiableOn ℂ zetaAbel₂ W := by
    show DifferentiableOn ℂ
      (fun s => 1 / (s - 1) + 1 / 2 + s / 12 + ∑' n : ℕ, emTerm₂ (n + 1) s) W
    apply DifferentiableOn.add
    · intro s hs
      have hd : DifferentiableAt ℂ (fun z : ℂ => 1 / (z - 1) + 1 / 2 + z / 12) s := by
        fun_prop (disch := exact sub_ne_zero.mpr hs.2)
      exact hd.differentiableWithinAt
    · refine differentiableOn_tsum_of_summable_norm
        (u := fun n : ℕ => (‖s₀‖ + 1) * (‖s₀‖ + 2) / 12 * ((n : ℝ) + 1) ^ (-((s₀.re + 3) / 2)))
        ?_ ?_ hWo ?_
      · exact (summable_add_one_rpow (by linarith)).mul_left _
      · intro n s hs
        exact (emTerm₂_differentiableAt (by omega) hs.2).differentiableWithinAt
      · intro n s hs
        have hre : (s₀.re - 1) / 2 < s.re := hs.1.1
        have hnorm : ‖s‖ < ‖s₀‖ + 1 := hs.1.2
        have hnorm1 : ‖s + 1‖ ≤ ‖s‖ + 1 := by simpa using norm_add_le s 1
        have hA : ‖s‖ * ‖s + 1‖ ≤ (‖s₀‖ + 1) * (‖s₀‖ + 2) :=
          mul_le_mul hnorm.le (by linarith) (norm_nonneg _) (by positivity)
        have hB : ((n : ℝ) + 1) ^ (-s.re - 2) ≤ ((n : ℝ) + 1) ^ (-((s₀.re + 3) / 2)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
            (by linarith)
        calc ‖emTerm₂ (n + 1) s‖ ≤ ‖s‖ * ‖s + 1‖ / 12 * ((n + 1 : ℕ) : ℝ) ^ (-s.re - 2) :=
              norm_emTerm₂_le (by linarith) hs.2 (by omega)
          _ ≤ (‖s₀‖ + 1) * (‖s₀‖ + 2) / 12 * ((n : ℝ) + 1) ^ (-((s₀.re + 3) / 2)) := by
              push_cast
              exact mul_le_mul (div_le_div_of_nonneg_right hA (by norm_num)) hB
                (by positivity) (by positivity)
  exact (hdiff.differentiableAt (hWo.mem_nhds hs₀W)).differentiableWithinAt

/-- Identity-theorem step: on a convex open `V ⊆ leftHalf` containing a point of `Re s > 1`,
`ζ = zetaAbel₂`. -/
theorem eqOn_zeta_zetaAbel₂_of_convex {V : Set ℂ} (hV : Convex ℝ V) (hVo : IsOpen V)
    (hsub : V ⊆ leftHalf) {z₀ : ℂ} (hz₀ : z₀ ∈ V) (hz₀re : 1 < z₀.re) :
    Set.EqOn riemannZeta zetaAbel₂ V := by
  have hζ : AnalyticOnNhd ℂ riemannZeta V :=
    DifferentiableOn.analyticOnNhd
      (fun s hs => (differentiableAt_riemannZeta (hsub hs).2).differentiableWithinAt) hVo
  have hA : AnalyticOnNhd ℂ zetaAbel₂ V :=
    (zetaAbel₂_differentiableOn.mono hsub).analyticOnNhd hVo
  refine hζ.eqOn_of_preconnected_of_eventuallyEq hA hV.isPreconnected hz₀ ?_
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hz₀re) fun s hs => ?_
  have hs' : 1 < s.re := hs
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs'; simp at hs'
  rw [← zetaAbel_eq_zeta_of_one_lt_re hs', zetaAbel₂_eq_zetaAbel (by linarith) hs1]

/-- **The second-order continuation identity.** For `Re s > -1`, `s ≠ 1`:
`ζ(s) = 1/(s-1) + 1/2 + s/12 + Σ_{n≥1} emTerm₂ n s`. -/
theorem zeta_eq_zetaAbel₂ {s : ℂ} (hs : -1 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = zetaAbel₂ s := by
  have hre : IsOpen {z : ℂ | -1 < z.re} := isOpen_lt continuous_const continuous_re
  rcases lt_trichotomy s.im 0 with him | him | him
  · -- lower half-plane, `z₀ = 2 - I`
    refine eqOn_zeta_zetaAbel₂_of_convex (V := {z | -1 < z.re} ∩ {z | z.im < 0})
      ((convex_halfSpace_re_gt (-1)).inter (convex_halfSpace_im_lt 0))
      (hre.inter (isOpen_lt continuous_im continuous_const))
      (fun z hz => ⟨hz.1, fun h => by rw [h] at hz; simp at hz⟩)
      (z₀ := 2 - I) ⟨by norm_num, by simp⟩ (by simp) ⟨hs, him⟩
  · -- real axis: either `Re s > 1` (Dirichlet series) or `-1 < Re s < 1`
    have hre1 : s.re ≠ 1 := fun h => hs1 (Complex.ext h (by simpa using him))
    rcases lt_or_gt_of_ne hre1 with h | h
    · -- `-1 < s < 1`: use the convex set `{Re > -1} ∩ {Re - 1 < Im}`, `z₀ = 2 + 2I`
      have hL : IsLinearMap ℝ (fun z : ℂ => z.im - z.re) :=
        ⟨fun x y => by simp only [add_im, add_re]; ring,
         fun c x => by simp only [smul_im, smul_re, smul_eq_mul]; ring⟩
      refine eqOn_zeta_zetaAbel₂_of_convex (V := {z | -1 < z.re} ∩ {z | -1 < z.im - z.re})
        ((convex_halfSpace_re_gt (-1)).inter (convex_halfSpace_gt hL (-1)))
        (hre.inter (isOpen_lt continuous_const (continuous_im.sub continuous_re)))
        (fun z hz => ⟨hz.1, fun h => by rw [h] at hz; norm_num at hz⟩)
        (z₀ := 2 + 2 * I) ⟨by norm_num, by simp⟩ (by simp)
        ⟨hs, by simp only [Set.mem_setOf_eq]; linarith⟩
    · rw [← zetaAbel_eq_zeta_of_one_lt_re h, zetaAbel₂_eq_zetaAbel (by linarith) hs1]
  · -- upper half-plane, `z₀ = 2 + I`
    refine eqOn_zeta_zetaAbel₂_of_convex (V := {z | -1 < z.re} ∩ {z | 0 < z.im})
      ((convex_halfSpace_re_gt (-1)).inter (convex_halfSpace_im_gt 0))
      (hre.inter (isOpen_lt continuous_const continuous_im))
      (fun z hz => ⟨hz.1, fun h => by rw [h] at hz; simp at hz⟩)
      (z₀ := 2 + I) ⟨by norm_num, by simp⟩ (by simp) ⟨hs, him⟩

/-! ## Splitting the representation at `N` and the growth bound -/

/-- **Representation split at `N`.** For `Re s > -1`, `s ≠ 1` and any `N`,
`ζ(s) = Σ_{n=1}^{N} n^{-s} + (N+1)^{1-s}/(s-1) + (N+1)^{-s}/2 + (s/12)(N+1)^{-s-1}
  + Σ_{n > N} emTerm₂ n s`. -/
theorem zeta_eq_sum_add_tail₂ {s : ℂ} (hs : -1 < s.re) (hs1 : s ≠ 1) (N : ℕ) :
    riemannZeta s = ∑ i ∈ Finset.range N, ((i : ℂ) + 1) ^ (-s)
      + ((N : ℂ) + 1) ^ (1 - s) / (s - 1) + ((N : ℂ) + 1) ^ (-s) / 2
      + s / 12 * ((N : ℂ) + 1) ^ (-s - 1) + ∑' n : ℕ, emTerm₂ (n + N + 1) s := by
  have hsum := summable_emTerm₂ hs hs1
  have hsplit := Summable.sum_add_tsum_nat_add N hsum
  rw [zeta_eq_zetaAbel₂ hs hs1, zetaAbel₂, ← hsplit, sum_emTerm₂]
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp
  ring

/-- **The split bound.** For `Re s ≥ -1/2`, `s ≠ 1`, `N ≥ 1`:
`‖ζ s‖ ≤ N^{3/2} + (N+1)^{3/2}/‖s-1‖ + (N+1)^{1/2}/2 + ‖s‖/12 + ‖s‖‖s+1‖/12 · 2 N^{-1/2}`. -/
theorem norm_zeta_le_split₂ {s : ℂ} (hs : -1 / 2 ≤ s.re) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s‖ ≤ (N : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ)
      + ((N : ℝ) + 1) * ((N : ℝ) + 1) ^ (1 / 2 : ℝ) / ‖s - 1‖
      + ((N : ℝ) + 1) ^ (1 / 2 : ℝ) / 2 + ‖s‖ / 12
      + ‖s‖ * ‖s + 1‖ / 12 * (2 * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have hs' : -1 < s.re := by linarith
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hcast : ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [zeta_eq_sum_add_tail₂ hs' hs1 N]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add_left (norm_add_le _ _) _).trans ?_
  refine (add_le_add_left (add_le_add_left (norm_add_le _ _) _) _).trans ?_
  refine (add_le_add_left (add_le_add_left (add_le_add_left (norm_add_le _ _) _) _) _).trans ?_
  refine add_le_add (add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_) ?_
  · -- the partial sum: `N` terms each `≤ N^{1/2}`
    calc ‖∑ i ∈ Finset.range N, ((i : ℂ) + 1) ^ (-s)‖
        ≤ ∑ i ∈ Finset.range N, ‖((i : ℂ) + 1) ^ (-s)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range N, (N : ℝ) ^ (1 / 2 : ℝ) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hipos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
          have hiN : (i : ℝ) + 1 ≤ N := by
            have := Finset.mem_range.mp hi
            exact_mod_cast this
          rw [show ((i : ℂ) + 1) = (((i : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
            norm_ofReal_cpow hipos, neg_re]
          calc ((i : ℝ) + 1) ^ (-s.re) ≤ ((i : ℝ) + 1) ^ (1 / 2 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
            _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hipos.le hiN (by norm_num)
      _ = (N : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) := by
          simp [Finset.sum_const, Finset.card_range]
  · -- the boundary term `(N+1)^{1-s}/(s-1)`
    rw [norm_div, hcast, norm_ofReal_cpow hpos, sub_re, one_re]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    calc ((N : ℝ) + 1) ^ (1 - s.re) ≤ ((N : ℝ) + 1) ^ (1 + 1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = ((N : ℝ) + 1) * ((N : ℝ) + 1) ^ (1 / 2 : ℝ) := by
          rw [Real.rpow_add hpos, Real.rpow_one]
  · -- the boundary term `(N+1)^{-s}/2`
    rw [norm_div, hcast, norm_ofReal_cpow hpos, neg_re, Complex.norm_ofNat]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  · -- the boundary term `(s/12)(N+1)^{-s-1}`
    rw [norm_mul, norm_div, hcast, norm_ofReal_cpow hpos, sub_re, neg_re, one_re,
      Complex.norm_ofNat]
    calc ‖s‖ / 12 * ((N : ℝ) + 1) ^ (-s.re - 1) ≤ ‖s‖ / 12 * 1 := by
          gcongr
          exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
      _ = ‖s‖ / 12 := mul_one _
  · -- the tail
    calc ‖∑' n : ℕ, emTerm₂ (n + N + 1) s‖
        ≤ ∑' n : ℕ, ‖s‖ * ‖s + 1‖ / 12 * ((n : ℝ) + N + 1) ^ (-(3 / 2 : ℝ)) := by
          refine tsum_of_norm_bounded
            ((summable_add_rpow N (by norm_num)).mul_left _).hasSum fun n => ?_
          calc ‖emTerm₂ (n + N + 1) s‖
              ≤ ‖s‖ * ‖s + 1‖ / 12 * ((n + N + 1 : ℕ) : ℝ) ^ (-s.re - 2) :=
                norm_emTerm₂_le (by linarith) hs1 (by omega)
            _ ≤ ‖s‖ * ‖s + 1‖ / 12 * ((n : ℝ) + N + 1) ^ (-(3 / 2 : ℝ)) := by
                push_cast
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                apply Real.rpow_le_rpow_of_exponent_le
                  (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n), (N.cast_nonneg : (0 : ℝ) ≤ N)])
                linarith
      _ = ‖s‖ * ‖s + 1‖ / 12 * ∑' n : ℕ, ((n : ℝ) + N + 1) ^ (-(3 / 2 : ℝ)) := tsum_mul_left
      _ ≤ ‖s‖ * ‖s + 1‖ / 12 * (2 * (N : ℝ) ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (tsum_tail_rpow_le hN) (by positivity)

/-! ### Elementary real inequalities used in the final bound (kept separate so that
`nlinarith` runs in a small context) -/

/-- `1 ≤ a` when `0 ≤ a` and `2 ≤ a²`. -/
theorem one_le_of_two_le_mul_self {a : ℝ} (ha0 : 0 ≤ a) (h : 2 ≤ a * a) : 1 ≤ a := by
  nlinarith

/-- `a ≤ a²` for `a ≥ 1`. -/
theorem le_mul_self_of_one_le {a : ℝ} (ha : 1 ≤ a) : a ≤ a * a := by nlinarith

/-- `a² ≤ a³` for `a ≥ 1`. -/
theorem mul_self_le_cube_of_one_le {a : ℝ} (ha : 1 ≤ a) : a * a ≤ a * a * a := by nlinarith

/-- `(2 + T)(3 + T) ≤ 6 T²` for `T ≥ 2`. -/
theorem poly_bound_aux {T : ℝ} (hT : 2 ≤ T) : (2 + T) * (3 + T) ≤ 6 * (T * T) := by nlinarith

/-- `a⁴ ≤ 2 a³ b` when `0 ≤ a ≤ 2b`. -/
theorem quart_le_aux {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ 2 * b) :
    a * a * (a * a) ≤ 2 * (a * a * a) * b := by
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg ha0 ha0) ha0) (sub_nonneg.mpr hab)]

/-- **Polynomial growth on the wide strip, exponent `3/2`.** For `-1/2 ≤ Re s ≤ 2` and
`|Im s| ≥ 2`, `‖ζ s‖ ≤ 7 |Im s|^{3/2}` (split at `N = ⌊|Im s|⌋`). -/
theorem zeta_growth_wide_bound {s : ℂ} (h₁ : -1 / 2 ≤ s.re) (h₂ : s.re ≤ 2) (ht : 2 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 7 * |s.im| ^ (3 / 2 : ℝ) := by
  have hs1 : s ≠ 1 := fun h => by rw [h] at ht; norm_num at ht
  set T := |s.im| with hT
  have hT0 : 0 ≤ T := abs_nonneg _
  set N := ⌊T⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by rw [Nat.cast_one]; linarith)
  have hNle : (N : ℝ) ≤ T := Nat.floor_le hT0
  have hltN : T < N + 1 := Nat.lt_floor_add_one T
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have h := norm_zeta_le_split₂ h₁ hs1 hN1
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.rpow_neg (Nat.cast_nonneg N),
    ← Real.sqrt_eq_rpow] at h
  -- the elementary facts about `s`
  have hsm : 2 ≤ ‖s - 1‖ := by
    calc (2 : ℝ) ≤ |s.im| := ht
      _ = |(s - 1).im| := by simp
      _ ≤ ‖s - 1‖ := abs_im_le_norm _
  have hs : ‖s‖ ≤ 2 + T := by
    calc ‖s‖ ≤ |s.re| + |s.im| := norm_le_abs_re_add_abs_im s
      _ ≤ 2 + T := by
          gcongr
          rw [abs_le]
          constructor <;> linarith
  have hs1n : ‖s + 1‖ ≤ 3 + T := by
    calc ‖s + 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 + T + 1 := by rw [norm_one]; linarith
      _ = 3 + T := by ring
  -- square roots
  set a := Real.sqrt T with ha_def
  set b := Real.sqrt (N : ℝ) with hb_def
  set c := Real.sqrt ((N : ℝ) + 1) with hc_def
  have ha : a * a = T := Real.mul_self_sqrt hT0
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hbpos : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have hba : b ≤ a := Real.sqrt_le_sqrt hNle
  have hab : a ≤ 2 * b := by
    have h4 : T ≤ 4 * N := by linarith
    calc a = Real.sqrt T := rfl
      _ ≤ Real.sqrt (4 * N) := Real.sqrt_le_sqrt h4
      _ = 2 * b := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 * 2 by norm_num,
            Real.sqrt_mul_self (by norm_num)]
  have hca : c ≤ 2 * a := by
    calc c = Real.sqrt ((N : ℝ) + 1) := rfl
      _ ≤ Real.sqrt (4 * T) := Real.sqrt_le_sqrt (by linarith)
      _ = 2 * a := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 * 2 by norm_num,
            Real.sqrt_mul_self (by norm_num)]
  have ha1 : 1 ≤ a := one_le_of_two_le_mul_self ha0 (by rw [ha]; exact ht)
  have haT : a ≤ T := by rw [← ha]; exact le_mul_self_of_one_le ha1
  have haaa : T ≤ a * a * a := by rw [← ha]; exact mul_self_le_cube_of_one_le ha1
  -- the five terms
  have t1 : (N : ℝ) * b ≤ a * a * a := by
    have : (N : ℝ) ≤ a * a := by rw [ha]; exact hNle
    exact mul_le_mul this hba hb0 (by positivity)
  have t2 : ((N : ℝ) + 1) * c / ‖s - 1‖ ≤ 2 * (a * a * a) := by
    have hN2 : (N : ℝ) + 1 ≤ 2 * (a * a) := by rw [ha]; linarith
    have hprod2 : ((N : ℝ) + 1) * c ≤ (2 * (a * a)) * (2 * a) :=
      mul_le_mul hN2 hca hc0 (by positivity)
    calc ((N : ℝ) + 1) * c / ‖s - 1‖ ≤ ((N : ℝ) + 1) * c / 2 :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hsm
      _ ≤ (2 * (a * a)) * (2 * a) / 2 := div_le_div_of_nonneg_right hprod2 (by norm_num)
      _ = 2 * (a * a * a) := by ring
  have t3 : c / 2 ≤ a * a * a := by linarith
  have t4 : ‖s‖ / 12 ≤ a * a * a := by linarith
  have t5 : ‖s‖ * ‖s + 1‖ / 12 * (2 * b⁻¹) ≤ 2 * (a * a * a) := by
    rw [show ‖s‖ * ‖s + 1‖ / 12 * (2 * b⁻¹) = (‖s‖ * ‖s + 1‖ / 6) / b by ring,
      div_le_iff₀ hbpos]
    have hprod : ‖s‖ * ‖s + 1‖ ≤ 6 * (T * T) :=
      calc ‖s‖ * ‖s + 1‖ ≤ (2 + T) * (3 + T) := mul_le_mul hs hs1n (norm_nonneg _) (by positivity)
        _ ≤ 6 * (T * T) := poly_bound_aux ht
    have h2ab : T * T ≤ 2 * (a * a * a) * b := by
      rw [← ha]; exact quart_le_aux ha0 hab
    linarith
  have hT32 : T ^ (3 / 2 : ℝ) = a * a * a := by
    rw [show (3 / 2 : ℝ) = 1 / 2 * ((3 : ℕ) : ℝ) by norm_num, Real.rpow_mul hT0,
      Real.rpow_natCast, ← Real.sqrt_eq_rpow, ← ha_def]
    ring
  rw [hT32]
  linarith [h, t1, t2, t3, t4, t5]

/-- **Deliverable (2): polynomial growth on `-1/2 ≤ Re s ≤ 1/2`, exponent `3/2`.**
`∃ C, ∀ s, -1/2 ≤ Re s → Re s ≤ 1/2 → 2 ≤ |Im s| → ‖ζ s‖ ≤ C |Im s|^{3/2}` (with `C = 7`). -/
theorem zeta_growth_neg_strip :
    ∃ C : ℝ, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 1 / 2 → 2 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * |s.im| ^ (3 / 2 : ℝ) :=
  ⟨7, fun _ h₁ h₂ ht => zeta_growth_wide_bound h₁ (by linarith) ht⟩

/-- **Deliverable (3): polynomial growth on the wide strip `-1/2 ≤ Re s ≤ 2`, exponent `3/2`.**
`∃ C, ∀ s, -1/2 ≤ Re s → Re s ≤ 2 → 2 ≤ |Im s| → ‖ζ s‖ ≤ C |Im s|^{3/2}` (with `C = 7`). -/
theorem zeta_growth_wide :
    ∃ C : ℝ, ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * |s.im| ^ (3 / 2 : ℝ) :=
  ⟨7, fun _ h₁ h₂ ht => zeta_growth_wide_bound h₁ h₂ ht⟩

/-- The same wide bound obtained by *combining* `zeta_growth_neg_strip` (on `Re s ≤ 1/2`) with
`ZetaGrowth.zeta_growth_strip_rpow` (on `Re s ≥ 1/2`, exponent `1/2 ≤ 3/2`); constant `11`. -/
theorem zeta_growth_wide_of_sqrt {s : ℂ} (h₁ : -1 / 2 ≤ s.re) (h₂ : s.re ≤ 2) (ht : 2 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 11 * |s.im| ^ (3 / 2 : ℝ) := by
  have hT1 : (1 : ℝ) ≤ |s.im| := by linarith
  have hpow : |s.im| ^ (1 / 2 : ℝ) ≤ |s.im| ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
  have hnn : (0 : ℝ) ≤ |s.im| ^ (3 / 2 : ℝ) := by positivity
  rcases le_or_gt (1 / 2) s.re with h | h
  · calc ‖riemannZeta s‖ ≤ 11 * |s.im| ^ (1 / 2 : ℝ) := zeta_growth_strip_rpow h h₂ ht
      _ ≤ 11 * |s.im| ^ (3 / 2 : ℝ) := by gcongr
  · calc ‖riemannZeta s‖ ≤ 7 * |s.im| ^ (3 / 2 : ℝ) := zeta_growth_wide_bound h₁ h₂ ht
      _ ≤ 11 * |s.im| ^ (3 / 2 : ℝ) := by nlinarith

end ZetaGrowthNeg

end
