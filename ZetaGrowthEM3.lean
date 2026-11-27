import Mathlib
import ZetaGrowth
import ZetaGrowthNeg

/-!
# Fourth-order Euler–Maclaurin continuation of `ζ` and polynomial growth for `Re s > -3`

`ZetaGrowthNeg` proves `ζ(s) = zetaAbel₂ s = 1/(s-1) + 1/2 + s/12 + Σ_{n≥1} emTerm₂ n s` on
`Re s > -1`, with `emTerm₂ n s = -∫_n^{n+1} (P₂(t)/2) s(s+1) t^{-s-2} dt`.  This file takes two more
Euler–Maclaurin steps.  Integrating by parts with `P₃/6` (`P₃' = 3P₂`, `P₃(0) = P₃(1) = 0`) produces
**no** boundary term, and the next step with `P₄/24` (`P₄' = 4P₃`, `P₄(0) = P₄(1) = -1/30`) produces
the boundary term `(s(s+1)(s+2)/720)((n+1)^{-s-3} - n^{-s-3})`.  Everything is unconditional:

* `emTerm₄ n s = emTerm₂ n s - (s(s+1)(s+2)/720)((n+1)^{-s-3} - n^{-s-3})` is the fourth-order
  remainder.  It equals `-(H₄(n+1) - H₄(n))` for the explicit antiderivative `H₄ = emAnti₄ n s` of
  `(P₄(t-n)/24) s(s+1)(s+2)(s+3) t^{-s-4}` (`emTerm₄_eq_emAnti₄`, `emAnti₄_hasDerivAt`), whence the
  **mean-value bound** `‖emTerm₄ n s‖ ≤ ‖s‖‖s+1‖‖s+2‖‖s+3‖/720 · n^{-Re s - 4}` (`norm_emTerm₄_le`,
  using `|P₄| ≤ 1/30` on `[0,1]`), summable on `Re s > -3` (`summable_emTerm₄`).
* `zetaAbel₄ s = 1/(s-1) + 1/2 + s/12 - s(s+1)(s+2)/720 + Σ_{n≥1} emTerm₄ n s` is holomorphic on
  `Re s > -3`, `s ≠ 1` (`zetaAbel₄_differentiableOn`), agrees with `zetaAbel₂` on `Re s > -1`
  (`zetaAbel₄_eq_zetaAbel₂`, telescoping), hence — identity theorem on convex pieces —
  **`zeta_eq_zetaAbel₄ : ζ s = zetaAbel₄ s` for `Re s > -3`, `s ≠ 1`**.
* Splitting at `N = ⌊|Im s|⌋` (`zeta_eq_sum_add_tail₄`, `norm_zeta_le_split₄`) gives the
  **polynomial growth bound** `zeta_growth_left_bound : ‖ζ s‖ ≤ 12 |Im s|^4` on `-5/2 ≤ Re s ≤ 2`,
  `|Im s| ≥ 2` (`zeta_growth_left_rpow` with a real exponent, `zeta_growth_left` existential).

**Not proven / not attempted:** the sharper exponent `7/2` on `Re s = -5/2` (clean over sharp: the
exponent `4` avoids all square-root bookkeeping), anything for `Re s ≤ -3`, and the functional
equation.  No `sorry`, no hypotheses, no axioms beyond Mathlib's standard three.
-/

noncomputable section

open Complex Filter Topology
open ZetaGrowth ZetaGrowthNeg

namespace ZetaGrowthEM3

/-! ## The fourth-order Euler–Maclaurin remainder -/

/-- The fourth-order Euler–Maclaurin remainder: the second-order remainder `emTerm₂ n s` corrected
by the `P₄`-boundary term `(s(s+1)(s+2)/720)((n+1)^{-s-3} - n^{-s-3})` (the `P₃`-boundary terms
vanish since `P₃(0) = P₃(1) = 0`).  Classically
`emTerm₄ n s = -∫_n^{n+1} (P₄(t)/24) s(s+1)(s+2)(s+3) t^{-s-4} dt`, `P₄(t) = {t}⁴ - 2{t}³ + {t}² - 1/30`. -/
def emTerm₄ (n : ℕ) (s : ℂ) : ℂ :=
  emTerm₂ n s - s * (s + 1) * (s + 2) / 720 * (((n : ℂ) + 1) ^ (-s - 3) - (n : ℂ) ^ (-s - 3))

/-- The fourth-order continuation of `ζ`:
`1/(s-1) + 1/2 + s/12 - s(s+1)(s+2)/720 + Σ_{n ≥ 1} emTerm₄ n s`. -/
def zetaAbel₄ (s : ℂ) : ℂ :=
  1 / (s - 1) + 1 / 2 + s / 12 - s * (s + 1) * (s + 2) / 720 + ∑' n : ℕ, emTerm₄ (n + 1) s

/-- The (real) polynomial `P₄(x-n)/24 = ((x-n)⁴ - 2(x-n)³ + (x-n)² - 1/30)/24` on `[n, n+1]`. -/
def bern₄ (n : ℕ) (x : ℝ) : ℝ :=
  ((x - n) * (x - n) * (x - n) * (x - n) - 2 * ((x - n) * (x - n) * (x - n))
    + (x - n) * (x - n) - 1 / 30) / 24

/-- The antiderivative
`H₄(z) = (P₄/24)·f'''(z) - (P₃/6)·f''(z) + (P₂/2)·f'(z) - P₁·f(z) + F(z)`, `f(z) = z^{-s}`,
`P_k = P_k(z - n)`, of `(P₄(z-n)/24) s(s+1)(s+2)(s+3) z^{-s-4}` (as a function of a complex
variable, later restricted to real `z`). -/
def emAnti₄ (n : ℕ) (s : ℂ) (z : ℂ) : ℂ :=
  ((z - n) * (z - n) * (z - n) * (z - n) - 2 * ((z - n) * (z - n) * (z - n))
      + (z - n) * (z - n) - 1 / 30) / 24 * (-(s * (s + 1) * (s + 2))) * z ^ (-s - 3)
    - ((z - n) * (z - n) * (z - n) - 3 / 2 * ((z - n) * (z - n)) + 1 / 2 * (z - n)) / 6
      * (s * (s + 1)) * z ^ (-s - 2)
    + ((z - n) * (z - n) - (z - n) + 1 / 6) / 2 * (-s) * z ^ (-s - 1)
    - (z - n - 1 / 2) * z ^ (-s) + z ^ (-s + 1) / (-s + 1)

/-- `|P₄(x-n)/24| ≤ 1/720` for `x ∈ [n, n+1]` (since `P₄(u) = u²(u-1)² - 1/30 ∈ [-1/30, 7/240]`). -/
theorem abs_bern₄_le {n : ℕ} {x : ℝ} (hx : x ∈ Set.Icc (n : ℝ) (n + 1)) :
    |bern₄ n x| ≤ 1 / 720 := by
  obtain ⟨h1, h2⟩ := hx
  have hv : -(1 / 4) ≤ (x - n) * (x - n - 1) := by nlinarith [sq_nonneg (x - n - 1 / 2)]
  have hv0 : (x - n) * (x - n - 1) ≤ 0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]
  have hv2 : ((x - n) * (x - n - 1)) * ((x - n) * (x - n - 1)) ≤ 1 / 16 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (x - n) * (x - n - 1) + 1 / 4)
      (by linarith : (0 : ℝ) ≤ -((x - n) * (x - n - 1)))]
  have hv3 : 0 ≤ ((x - n) * (x - n - 1)) * ((x - n) * (x - n - 1)) := mul_self_nonneg _
  have heq : bern₄ n x = (((x - n) * (x - n - 1)) * ((x - n) * (x - n - 1)) - 1 / 30) / 24 := by
    rw [bern₄]; ring
  rw [heq, abs_le]
  constructor <;> linarith

/-- `emTerm₄ n s = -(H₄(n+1) - H₄(n))`. -/
theorem emTerm₄_eq_emAnti₄ (n : ℕ) (s : ℂ) :
    emTerm₄ n s = -(emAnti₄ n s (((n : ℝ) + 1 : ℝ)) - emAnti₄ n s ((n : ℝ))) := by
  unfold emTerm₄ emTerm₂ emTerm emAnti₄
  rw [show (1 : ℂ) - s = -s + 1 by ring]
  push_cast
  ring

/-- `H₄'(x) = (P₄(x-n)/24) s(s+1)(s+2)(s+3) x^{-s-4}` for real `x > 0` (`s ≠ 1`). -/
theorem emAnti₄_hasDerivAt (n : ℕ) {s : ℂ} (hs1 : s ≠ 1) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => emAnti₄ n s t)
      (((bern₄ n x : ℝ) : ℂ) * (s * (s + 1) * (s + 2) * (s + 3)) * (x : ℂ) ^ (-s - 4)) x := by
  have hxs : (x : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.mpr hx
  have h1s : (-s + 1) ≠ 0 := by
    intro h
    apply hs1
    linear_combination -h
  have hp3 : HasDerivAt (fun z : ℂ => z ^ (-s - 3)) ((-s - 3) * (x : ℂ) ^ (-s - 3 - 1)) x :=
    (Complex.hasStrictDerivAt_cpow_const hxs).hasDerivAt
  have hp2 : HasDerivAt (fun z : ℂ => z ^ (-s - 2)) ((-s - 2) * (x : ℂ) ^ (-s - 2 - 1)) x :=
    (Complex.hasStrictDerivAt_cpow_const hxs).hasDerivAt
  have hp1 : HasDerivAt (fun z : ℂ => z ^ (-s - 1)) ((-s - 1) * (x : ℂ) ^ (-s - 1 - 1)) x :=
    (Complex.hasStrictDerivAt_cpow_const hxs).hasDerivAt
  have hp0 : HasDerivAt (fun z : ℂ => z ^ (-s)) ((-s) * (x : ℂ) ^ (-s - 1)) x :=
    (Complex.hasStrictDerivAt_cpow_const hxs).hasDerivAt
  have hpm : HasDerivAt (fun z : ℂ => z ^ (-s + 1)) ((-s + 1) * (x : ℂ) ^ (-s + 1 - 1)) x :=
    (Complex.hasStrictDerivAt_cpow_const hxs).hasDerivAt
  have hu : HasDerivAt (fun z : ℂ => z - n) 1 x := (hasDerivAt_id' (x := (x : ℂ))).sub_const _
  have hu2 : HasDerivAt (fun z : ℂ => (z - n) * (z - n)) _ x := hu.mul hu
  have hu3 : HasDerivAt (fun z : ℂ => (z - n) * (z - n) * (z - n)) _ x := hu2.mul hu
  have hu4 : HasDerivAt (fun z : ℂ => (z - n) * (z - n) * (z - n) * (z - n)) _ x := hu3.mul hu
  have hB4 : HasDerivAt (fun z : ℂ => ((z - n) * (z - n) * (z - n) * (z - n)
      - 2 * ((z - n) * (z - n) * (z - n)) + (z - n) * (z - n) - 1 / 30) / 24) _ x :=
    (((hu4.sub (hu3.const_mul 2)).add hu2).sub_const _).div_const _
  have hB3 : HasDerivAt (fun z : ℂ => ((z - n) * (z - n) * (z - n) - 3 / 2 * ((z - n) * (z - n))
      + 1 / 2 * (z - n)) / 6) _ x :=
    ((hu3.sub (hu2.const_mul _)).add (hu.const_mul _)).div_const _
  have hB2 : HasDerivAt (fun z : ℂ => ((z - n) * (z - n) - (z - n) + 1 / 6) / 2) _ x :=
    ((hu2.sub hu).add_const _).div_const _
  have hB1 : HasDerivAt (fun z : ℂ => z - n - 1 / 2) 1 x := hu.sub_const _
  have hE := (((((hB4.mul_const (-(s * (s + 1) * (s + 2)))).mul hp3).sub
    ((hB3.mul_const (s * (s + 1))).mul hp2)).add ((hB2.mul_const (-s)).mul hp1)).sub
    (hB1.mul hp0)).add (hpm.div_const (-s + 1))
  have hE' : HasDerivAt (fun z : ℂ => emAnti₄ n s z) _ x := hE
  refine hE'.comp_ofReal.congr_deriv ?_
  have e1 : (x : ℂ) ^ (-s - 3 - 1) = (x : ℂ) ^ (-s - 4) := by congr 1; ring
  have e2 : (x : ℂ) ^ (-s - 2 - 1) = (x : ℂ) ^ (-s - 3) := by congr 1; ring
  have e3 : (x : ℂ) ^ (-s - 1 - 1) = (x : ℂ) ^ (-s - 2) := by congr 1; ring
  have e4 : (x : ℂ) ^ (-s + 1 - 1) = (x : ℂ) ^ (-s) := by congr 1; ring
  rw [e1, e2, e3, e4, bern₄]
  push_cast
  field_simp
  ring

/-- **Mean-value bound** for the fourth-order remainder:
`‖emTerm₄ n s‖ ≤ ‖s‖ ‖s+1‖ ‖s+2‖ ‖s+3‖ / 720 · n^{-Re s - 4}` for `n ≥ 1`, `Re s ≥ -4`, `s ≠ 1`. -/
theorem norm_emTerm₄_le {s : ℂ} (hs : -4 ≤ s.re) (hs1 : s ≠ 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖emTerm₄ n s‖ ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ / 720 * (n : ℝ) ^ (-s.re - 4) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set B : ℝ := ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ / 720 * (n : ℝ) ^ (-s.re - 4) with hB
  have key := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun t : ℝ => emAnti₄ n s t)
    (f' := fun t : ℝ =>
      ((bern₄ n t : ℝ) : ℂ) * (s * (s + 1) * (s + 2) * (s + 3)) * (t : ℂ) ^ (-s - 4))
    (a := (n : ℝ)) (b := n + 1) (C := B) ?_ ?_ (n + 1) ⟨by linarith, le_rfl⟩
  · rw [emTerm₄_eq_emAnti₄, norm_neg]
    simpa using key
  · intro x hx
    exact (emAnti₄_hasDerivAt n hs1 (by linarith [hx.1])).hasDerivWithinAt
  · intro x hx
    have hxpos : 0 < x := by linarith [hx.1]
    show ‖((bern₄ n x : ℝ) : ℂ) * (s * (s + 1) * (s + 2) * (s + 3)) * (x : ℂ) ^ (-s - 4)‖ ≤ B
    simp only [norm_mul]
    rw [norm_real, Real.norm_eq_abs, norm_ofReal_cpow hxpos]
    have hre : (-s - 4).re = -s.re - 4 := by simp
    rw [hre]
    have hQ := abs_bern₄_le (n := n) (Set.Ico_subset_Icc_self hx)
    have hpow : x ^ (-s.re - 4) ≤ (n : ℝ) ^ (-s.re - 4) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hx.1 (by linarith)
    rw [hB]
    calc |bern₄ n x| * (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖) * x ^ (-s.re - 4)
        ≤ (1 / 720) * (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖) * (n : ℝ) ^ (-s.re - 4) := by gcongr
      _ = ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ / 720 * (n : ℝ) ^ (-s.re - 4) := by ring

/-- The fourth-order remainder series converges absolutely on `Re s > -3`, `s ≠ 1`. -/
theorem summable_emTerm₄ {s : ℂ} (hs : -3 < s.re) (hs1 : s ≠ 1) :
    Summable fun n : ℕ => emTerm₄ (n + 1) s := by
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ / 720 * ((n : ℝ) + 1) ^ (-s.re - 4))
    ((summable_add_one_rpow (by linarith)).mul_left _) fun n => ?_
  have := norm_emTerm₄_le (by linarith) hs1 (n := n + 1) (by omega)
  push_cast at this
  exact this

/-- Each fourth-order term is holomorphic in `s` away from `s = 1` (for `n ≥ 1`). -/
theorem emTerm₄_differentiableAt {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (fun z => emTerm₄ n z) s := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : (n : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  have hd3 : DifferentiableAt ℂ (fun z : ℂ => -z - 3) s := differentiableAt_id.neg.sub_const 3
  have hpoly : DifferentiableAt ℂ (fun z : ℂ => z * (z + 1) * (z + 2) / 720) s :=
    ((differentiableAt_id.mul (differentiableAt_id.add_const 1)).mul
      (differentiableAt_id.add_const 2)).div_const _
  unfold emTerm₄
  refine (emTerm₂_differentiableAt hn hs1).sub (hpoly.mul ?_)
  exact (hd3.const_cpow (Or.inl hn1)).sub (hd3.const_cpow (Or.inl hn0))

/-! ## Telescoping: `zetaAbel₄ = zetaAbel₂` on `Re s > -1` -/

/-- Partial sums of the fourth-order series in terms of the second-order ones:
`Σ_{i<N} emTerm₄ (i+1) s = Σ_{i<N} emTerm₂ (i+1) s - (s(s+1)(s+2)/720)((N+1)^{-s-3} - 1)`. -/
theorem sum_emTerm₄_eq (s : ℂ) (N : ℕ) :
    ∑ i ∈ Finset.range N, emTerm₄ (i + 1) s
      = ∑ i ∈ Finset.range N, emTerm₂ (i + 1) s
        - s * (s + 1) * (s + 2) / 720 * (((N : ℂ) + 1) ^ (-s - 3) - 1) := by
  have h3 := Finset.sum_range_sub (fun i : ℕ => ((i : ℂ) + 1) ^ (-s - 3)) N
  simp only [Nat.cast_zero, zero_add, one_cpow] at h3
  rw [← h3, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [emTerm₄]
  push_cast
  ring

/-- Fully expanded partial sums of the fourth-order series. -/
theorem sum_emTerm₄ (s : ℂ) (N : ℕ) :
    ∑ i ∈ Finset.range N, emTerm₄ (i + 1) s
      = ∑ i ∈ Finset.range N, ((i : ℂ) + 1) ^ (-s) - (((N : ℂ) + 1) ^ (1 - s) - 1) / (1 - s)
        + (((N : ℂ) + 1) ^ (-s) - 1) / 2 + s / 12 * (((N : ℂ) + 1) ^ (-s - 1) - 1)
        - s * (s + 1) * (s + 2) / 720 * (((N : ℂ) + 1) ^ (-s - 3) - 1) := by
  rw [sum_emTerm₄_eq, sum_emTerm₂]

/-- On `Re s > -1`, `s ≠ 1`, the two continuations agree: `zetaAbel₄ s = zetaAbel₂ s`. -/
theorem zetaAbel₄_eq_zetaAbel₂ {s : ℂ} (hs : -1 < s.re) (hs1 : s ≠ 1) :
    zetaAbel₄ s = zetaAbel₂ s := by
  have hsum₂ := summable_emTerm₂ hs hs1
  have hsum₄ := summable_emTerm₄ (by linarith) hs1
  have h3 : Tendsto (fun N : ℕ => ((N : ℂ) + 1) ^ (-s - 3)) atTop (𝓝 0) :=
    tendsto_add_one_cpow_zero (by simp only [sub_re, neg_re]; norm_num; linarith)
  have hpart : Tendsto (fun N => ∑ i ∈ Finset.range N, emTerm₄ (i + 1) s) atTop
      (𝓝 ((∑' n : ℕ, emTerm₂ (n + 1) s) - s * (s + 1) * (s + 2) / 720 * (0 - 1))) := by
    simp_rw [sum_emTerm₄_eq]
    exact hsum₂.hasSum.tendsto_sum_nat.sub ((h3.sub_const 1).const_mul _)
  have hS : HasSum (fun n : ℕ => emTerm₄ (n + 1) s)
      ((∑' n : ℕ, emTerm₂ (n + 1) s) - s * (s + 1) * (s + 2) / 720 * (0 - 1)) :=
    hsum₄.hasSum_iff_tendsto_nat.mpr hpart
  rw [zetaAbel₄, hS.tsum_eq, zetaAbel₂]
  ring

/-! ## Holomorphy of `zetaAbel₄` on `Re s > -3` and the identity theorem -/

/-- The half-plane `Re s > -3` with the pole removed. -/
def leftHalf₄ : Set ℂ := {s : ℂ | -3 < s.re ∧ s ≠ 1}

/-- `zetaAbel₄` is holomorphic on `Re s > -3`, `s ≠ 1` (locally uniform convergence). -/
theorem zetaAbel₄_differentiableOn : DifferentiableOn ℂ zetaAbel₄ leftHalf₄ := by
  intro s₀ hs₀
  obtain ⟨h0, h1⟩ := hs₀
  set W : Set ℂ := ({s | (s₀.re - 3) / 2 < s.re} ∩ {s | ‖s‖ < ‖s₀‖ + 1}) ∩ {1}ᶜ with hW
  have hWo : IsOpen W :=
    ((isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)).inter isOpen_compl_singleton
  have hs₀W : s₀ ∈ W := ⟨⟨by simp only [Set.mem_ofPred_eq]; linarith, by simp⟩, h1⟩
  have hdiff : DifferentiableOn ℂ zetaAbel₄ W := by
    show DifferentiableOn ℂ
      (fun s => 1 / (s - 1) + 1 / 2 + s / 12 - s * (s + 1) * (s + 2) / 720
        + ∑' n : ℕ, emTerm₄ (n + 1) s) W
    apply DifferentiableOn.add
    · intro s hs
      have hd : DifferentiableAt ℂ
          (fun z : ℂ => 1 / (z - 1) + 1 / 2 + z / 12 - z * (z + 1) * (z + 2) / 720) s := by
        have hinv := (differentiableAt_const (1 : ℂ)).div (differentiableAt_id.sub_const 1)
          (sub_ne_zero.mpr hs.2)
        have hpoly : DifferentiableAt ℂ (fun z : ℂ => z * (z + 1) * (z + 2) / 720) s :=
          ((differentiableAt_id.mul (differentiableAt_id.add_const 1)).mul
            (differentiableAt_id.add_const 2)).div_const _
        exact ((hinv.add_const _).add (differentiableAt_id.div_const _)).sub hpoly
      exact hd.differentiableWithinAt
    · refine differentiableOn_tsum_of_summable_norm
        (u := fun n : ℕ => (‖s₀‖ + 1) * (‖s₀‖ + 2) * (‖s₀‖ + 3) * (‖s₀‖ + 4) / 720
          * ((n : ℝ) + 1) ^ (-((s₀.re + 5) / 2)))
        ?_ ?_ hWo ?_
      · exact (summable_add_one_rpow (by linarith)).mul_left _
      · intro n s hs
        exact (emTerm₄_differentiableAt (by omega) hs.2).differentiableWithinAt
      · intro n s hs
        have hre : (s₀.re - 3) / 2 < s.re := hs.1.1
        have hnorm : ‖s‖ < ‖s₀‖ + 1 := hs.1.2
        have hnorm1 : ‖s + 1‖ ≤ ‖s‖ + 1 := by simpa using norm_add_le s 1
        have hnorm2 : ‖s + 2‖ ≤ ‖s‖ + 2 := by simpa using norm_add_le s 2
        have hnorm3 : ‖s + 3‖ ≤ ‖s‖ + 3 := by simpa using norm_add_le s 3
        have hA : ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖
            ≤ (‖s₀‖ + 1) * (‖s₀‖ + 2) * (‖s₀‖ + 3) * (‖s₀‖ + 4) := by
          gcongr <;> linarith
        have hB : ((n : ℝ) + 1) ^ (-s.re - 4) ≤ ((n : ℝ) + 1) ^ (-((s₀.re + 5) / 2)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
            (by linarith)
        calc ‖emTerm₄ (n + 1) s‖
            ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ / 720 * ((n + 1 : ℕ) : ℝ) ^ (-s.re - 4) :=
              norm_emTerm₄_le (by linarith) hs.2 (by omega)
          _ ≤ (‖s₀‖ + 1) * (‖s₀‖ + 2) * (‖s₀‖ + 3) * (‖s₀‖ + 4) / 720
              * ((n : ℝ) + 1) ^ (-((s₀.re + 5) / 2)) := by
              push_cast
              exact mul_le_mul (div_le_div_of_nonneg_right hA (by norm_num)) hB
                (by positivity) (by positivity)
  exact (hdiff.differentiableAt (hWo.mem_nhds hs₀W)).differentiableWithinAt

/-- Identity-theorem step: on a convex open `V ⊆ leftHalf₄` containing a point of `Re s > 1`,
`ζ = zetaAbel₄`. -/
theorem eqOn_zeta_zetaAbel₄_of_convex {V : Set ℂ} (hV : Convex ℝ V) (hVo : IsOpen V)
    (hsub : V ⊆ leftHalf₄) {z₀ : ℂ} (hz₀ : z₀ ∈ V) (hz₀re : 1 < z₀.re) :
    Set.EqOn riemannZeta zetaAbel₄ V := by
  have hζ : AnalyticOnNhd ℂ riemannZeta V :=
    DifferentiableOn.analyticOnNhd
      (fun s hs => (differentiableAt_riemannZeta (hsub hs).2).differentiableWithinAt) hVo
  have hA : AnalyticOnNhd ℂ zetaAbel₄ V :=
    (zetaAbel₄_differentiableOn.mono hsub).analyticOnNhd hVo
  refine hζ.eqOn_of_preconnected_of_eventuallyEq hA hV.isPreconnected hz₀ ?_
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hz₀re) fun s hs => ?_
  have hs' : 1 < s.re := hs
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs'; simp at hs'
  rw [← zetaAbel_eq_zeta_of_one_lt_re hs', ← zetaAbel₂_eq_zetaAbel (by linarith) hs1,
    zetaAbel₄_eq_zetaAbel₂ (by linarith) hs1]

/-- **The fourth-order continuation identity.** For `Re s > -3`, `s ≠ 1`:
`ζ(s) = 1/(s-1) + 1/2 + s/12 - s(s+1)(s+2)/720 + Σ_{n≥1} emTerm₄ n s`. -/
theorem zeta_eq_zetaAbel₄ {s : ℂ} (hs : -3 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = zetaAbel₄ s := by
  have hre : IsOpen {z : ℂ | -3 < z.re} := isOpen_lt continuous_const continuous_re
  rcases lt_trichotomy s.im 0 with him | him | him
  · -- lower half-plane, `z₀ = 2 - I`
    refine eqOn_zeta_zetaAbel₄_of_convex (V := {z | -3 < z.re} ∩ {z | z.im < 0})
      ((convex_halfSpace_re_gt (-3)).inter (convex_halfSpace_im_lt 0))
      (hre.inter (isOpen_lt continuous_im continuous_const))
      (fun z hz => ⟨hz.1, fun h => by rw [h] at hz; simp at hz⟩)
      (z₀ := 2 - I) ⟨by norm_num, by simp⟩ (by simp) ⟨hs, him⟩
  · -- real axis: either `Re s > 1` (Dirichlet series) or `-3 < Re s < 1`
    have hre1 : s.re ≠ 1 := fun h => hs1 (Complex.ext h (by simpa using him))
    rcases lt_or_gt_of_ne hre1 with h | h
    · -- `-3 < s < 1`: use the convex set `{Re > -3} ∩ {Re - 1 < Im}`, `z₀ = 2 + 2I`
      have hL : IsLinearMap ℝ (fun z : ℂ => z.im - z.re) :=
        ⟨fun x y => by simp only [add_im, add_re]; ring,
         fun c x => by simp only [smul_im, smul_re, smul_eq_mul]; ring⟩
      refine eqOn_zeta_zetaAbel₄_of_convex (V := {z | -3 < z.re} ∩ {z | -1 < z.im - z.re})
        ((convex_halfSpace_re_gt (-3)).inter (convex_halfSpace_gt hL (-1)))
        (hre.inter (isOpen_lt continuous_const (continuous_im.sub continuous_re)))
        (fun z hz => ⟨hz.1, fun h => by rw [h] at hz; norm_num at hz⟩)
        (z₀ := 2 + 2 * I) ⟨by norm_num, by simp⟩ (by simp)
        ⟨hs, by simp only [Set.mem_ofPred_eq]; linarith⟩
    · rw [← zetaAbel_eq_zeta_of_one_lt_re h, ← zetaAbel₂_eq_zetaAbel (by linarith) hs1,
        zetaAbel₄_eq_zetaAbel₂ (by linarith) hs1]
  · -- upper half-plane, `z₀ = 2 + I`
    refine eqOn_zeta_zetaAbel₄_of_convex (V := {z | -3 < z.re} ∩ {z | 0 < z.im})
      ((convex_halfSpace_re_gt (-3)).inter (convex_halfSpace_im_gt 0))
      (hre.inter (isOpen_lt continuous_const continuous_im))
      (fun z hz => ⟨hz.1, fun h => by rw [h] at hz; simp at hz⟩)
      (z₀ := 2 + I) ⟨by norm_num, by simp⟩ (by simp) ⟨hs, him⟩

/-! ## Splitting the representation at `N` and the growth bound -/

/-- **Representation split at `N`.** For `Re s > -3`, `s ≠ 1` and any `N`,
`ζ(s) = Σ_{n=1}^{N} n^{-s} + (N+1)^{1-s}/(s-1) + (N+1)^{-s}/2 + (s/12)(N+1)^{-s-1}
  - (s(s+1)(s+2)/720)(N+1)^{-s-3} + Σ_{n > N} emTerm₄ n s`. -/
theorem zeta_eq_sum_add_tail₄ {s : ℂ} (hs : -3 < s.re) (hs1 : s ≠ 1) (N : ℕ) :
    riemannZeta s = ∑ i ∈ Finset.range N, ((i : ℂ) + 1) ^ (-s)
      + ((N : ℂ) + 1) ^ (1 - s) / (s - 1) + ((N : ℂ) + 1) ^ (-s) / 2
      + s / 12 * ((N : ℂ) + 1) ^ (-s - 1)
      - s * (s + 1) * (s + 2) / 720 * ((N : ℂ) + 1) ^ (-s - 3)
      + ∑' n : ℕ, emTerm₄ (n + N + 1) s := by
  have hsum := summable_emTerm₄ hs hs1
  have hsplit := Summable.sum_add_tsum_nat_add N hsum
  rw [zeta_eq_zetaAbel₄ hs hs1, zetaAbel₄, ← hsplit, sum_emTerm₄]
  -- the only non-polynomial identity needed: `x/(1-s) = -(x/(s-1))`
  have hw : (((N : ℂ) + 1) ^ (1 - s) - 1) / (1 - s)
      = -((((N : ℂ) + 1) ^ (1 - s) - 1) / (s - 1)) := by
    rw [← neg_sub s 1, div_neg]
  rw [hw]
  ring

/-- **The split bound** (integer powers only).  For `Re s ≥ -5/2`, `s ≠ 1`, `N ≥ 1`:
`‖ζ s‖ ≤ N·N³ + (N+1)⁴/‖s-1‖ + (N+1)³/2 + (‖s‖/12)(N+1)² + ‖s‖‖s+1‖‖s+2‖/720
  + ‖s‖‖s+1‖‖s+2‖‖s+3‖/720 · 2`. -/
theorem norm_zeta_le_split₄ {s : ℂ} (hs : -5 / 2 ≤ s.re) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s‖ ≤ (N : ℝ) * (N : ℝ) ^ 3
      + ((N : ℝ) + 1) ^ 4 / ‖s - 1‖
      + ((N : ℝ) + 1) ^ 3 / 2
      + ‖s‖ / 12 * ((N : ℝ) + 1) ^ 2
      + ‖s‖ * ‖s + 1‖ * ‖s + 2‖ / 720
      + ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ / 720 * 2 := by
  have hs' : -3 < s.re := by linarith
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hN1R : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)]
  have hcast : ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [zeta_eq_sum_add_tail₄ hs' hs1 N]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add_left (norm_sub_le _ _) _).trans ?_
  refine (add_le_add_left (add_le_add_left (norm_add_le _ _) _) _).trans ?_
  refine (add_le_add_left (add_le_add_left (add_le_add_left (norm_add_le _ _) _) _) _).trans ?_
  refine (add_le_add_left (add_le_add_left (add_le_add_left (add_le_add_left
    (norm_add_le _ _) _) _) _) _).trans ?_
  refine add_le_add (add_le_add (add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_) ?_) ?_
  · -- the partial sum: `N` terms each `≤ N³`
    calc ‖∑ i ∈ Finset.range N, ((i : ℂ) + 1) ^ (-s)‖
        ≤ ∑ i ∈ Finset.range N, ‖((i : ℂ) + 1) ^ (-s)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range N, (N : ℝ) ^ 3 := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hipos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
          have hiN : (i : ℝ) + 1 ≤ N := by
            have := Finset.mem_range.mp hi
            exact_mod_cast this
          rw [show ((i : ℂ) + 1) = (((i : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
            norm_ofReal_cpow hipos, neg_re]
          calc ((i : ℝ) + 1) ^ (-s.re) ≤ ((i : ℝ) + 1) ^ ((3 : ℕ) : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
            _ = ((i : ℝ) + 1) ^ 3 := Real.rpow_natCast _ 3
            _ ≤ (N : ℝ) ^ 3 := pow_le_pow_left₀ hipos.le hiN 3
      _ = (N : ℝ) * (N : ℝ) ^ 3 := by simp [Finset.sum_const, Finset.card_range]
  · -- the boundary term `(N+1)^{1-s}/(s-1)`
    rw [norm_div, hcast, norm_ofReal_cpow hpos, sub_re, one_re]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    calc ((N : ℝ) + 1) ^ (1 - s.re) ≤ ((N : ℝ) + 1) ^ ((4 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1R (by push_cast; linarith)
      _ = ((N : ℝ) + 1) ^ 4 := Real.rpow_natCast _ 4
  · -- the boundary term `(N+1)^{-s}/2`
    rw [norm_div, hcast, norm_ofReal_cpow hpos, neg_re, Complex.norm_ofNat]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    calc ((N : ℝ) + 1) ^ (-s.re) ≤ ((N : ℝ) + 1) ^ ((3 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1R (by push_cast; linarith)
      _ = ((N : ℝ) + 1) ^ 3 := Real.rpow_natCast _ 3
  · -- the boundary term `(s/12)(N+1)^{-s-1}`
    rw [norm_mul, norm_div, hcast, norm_ofReal_cpow hpos, sub_re, neg_re, one_re,
      Complex.norm_ofNat]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc ((N : ℝ) + 1) ^ (-s.re - 1) ≤ ((N : ℝ) + 1) ^ ((2 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1R (by push_cast; linarith)
      _ = ((N : ℝ) + 1) ^ 2 := Real.rpow_natCast _ 2
  · -- the boundary term `(s(s+1)(s+2)/720)(N+1)^{-s-3}`
    rw [norm_mul, norm_div, norm_mul, norm_mul, hcast, norm_ofReal_cpow hpos, Complex.norm_ofNat]
    have hre : (-s - 3).re = -s.re - 3 := by simp
    rw [hre]
    calc ‖s‖ * ‖s + 1‖ * ‖s + 2‖ / 720 * ((N : ℝ) + 1) ^ (-s.re - 3)
        ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖ / 720 * 1 := by
          gcongr
          exact Real.rpow_le_one_of_one_le_of_nonpos hN1R (by linarith)
      _ = ‖s‖ * ‖s + 1‖ * ‖s + 2‖ / 720 := mul_one _
  · -- the tail
    calc ‖∑' n : ℕ, emTerm₄ (n + N + 1) s‖
        ≤ ∑' n : ℕ, ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ / 720
            * ((n : ℝ) + N + 1) ^ (-(3 / 2 : ℝ)) := by
          refine tsum_of_norm_bounded
            ((summable_add_rpow N (by norm_num)).mul_left _).hasSum fun n => ?_
          calc ‖emTerm₄ (n + N + 1) s‖
              ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ / 720
                  * ((n + N + 1 : ℕ) : ℝ) ^ (-s.re - 4) :=
                norm_emTerm₄_le (by linarith) hs1 (by omega)
            _ ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ / 720
                  * ((n : ℝ) + N + 1) ^ (-(3 / 2 : ℝ)) := by
                push_cast
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                apply Real.rpow_le_rpow_of_exponent_le
                  (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n), (N.cast_nonneg : (0 : ℝ) ≤ N)])
                linarith
      _ = ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ / 720
            * ∑' n : ℕ, ((n : ℝ) + N + 1) ^ (-(3 / 2 : ℝ)) := tsum_mul_left
      _ ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ / 720 * (2 * (N : ℝ) ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (tsum_tail_rpow_le hN) (by positivity)
      _ ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ / 720 * 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : (N : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by norm_num)
          linarith

/-- The elementary real-arithmetic step behind `zeta_growth_left_bound`: with `T ≥ 2`,
`0 ≤ Nr ≤ T`, `Nr + 1 ≤ 2T`, `m ≥ 2` and `a, b, c, d ≤ 5/2 + T, 7/2 + T, 9/2 + T, 11/2 + T`, the
six-term bound of `norm_zeta_le_split₄` is at most `12 T⁴` (kept separate so that each step runs
in a small context). -/
theorem growth_arith {T Nr m a b c d : ℝ} (hT : 2 ≤ T) (hN0 : 0 ≤ Nr) (hNle : Nr ≤ T)
    (hN2T : Nr + 1 ≤ 2 * T) (hm : 2 ≤ m)
    (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d)
    (ha : a ≤ 5 / 2 + T) (hb : b ≤ 7 / 2 + T) (hc : c ≤ 9 / 2 + T) (hd : d ≤ 11 / 2 + T) :
    Nr * Nr ^ 3 + (Nr + 1) ^ 4 / m + (Nr + 1) ^ 3 / 2 + a / 12 * (Nr + 1) ^ 2
      + a * b * c / 720 + a * b * c * d / 720 * 2 ≤ 12 * T ^ 4 := by
  have hT0 : 0 ≤ T := by linarith
  have hT3 : 0 ≤ T ^ 3 := pow_nonneg hT0 3
  have hT34 : T ^ 3 * 2 ≤ T ^ 4 := by nlinarith [mul_nonneg hT3 (sub_nonneg.mpr hT)]
  have hN2T0 : 0 ≤ Nr + 1 := by linarith
  have haT : a ≤ 9 / 4 * T := by linarith
  have hbT : b ≤ 11 / 4 * T := by linarith
  have hcT : c ≤ 13 / 4 * T := by linarith
  have hdT : d ≤ 15 / 4 * T := by linarith
  have hN14 : (Nr + 1) ^ 4 ≤ (2 * T) ^ 4 := pow_le_pow_left₀ hN2T0 hN2T 4
  have hN13 : (Nr + 1) ^ 3 ≤ (2 * T) ^ 3 := pow_le_pow_left₀ hN2T0 hN2T 3
  have hN12 : (Nr + 1) ^ 2 ≤ (2 * T) ^ 2 := pow_le_pow_left₀ hN2T0 hN2T 2
  have t1 : Nr * Nr ^ 3 ≤ T ^ 4 := by
    calc Nr * Nr ^ 3 = Nr ^ 4 := by ring
      _ ≤ T ^ 4 := pow_le_pow_left₀ hN0 hNle 4
  have t2 : (Nr + 1) ^ 4 / m ≤ 8 * T ^ 4 := by
    calc (Nr + 1) ^ 4 / m ≤ (Nr + 1) ^ 4 / 2 :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hm
      _ ≤ (2 * T) ^ 4 / 2 := by linarith
      _ = 8 * T ^ 4 := by ring
  have t3 : (Nr + 1) ^ 3 / 2 ≤ 2 * T ^ 4 := by
    calc (Nr + 1) ^ 3 / 2 ≤ (2 * T) ^ 3 / 2 := by linarith
      _ = 4 * T ^ 3 := by ring
      _ ≤ 2 * T ^ 4 := by linarith
  have t4 : a / 12 * (Nr + 1) ^ 2 ≤ 3 / 8 * T ^ 4 := by
    calc a / 12 * (Nr + 1) ^ 2 ≤ (9 / 4 * T) / 12 * (2 * T) ^ 2 :=
          mul_le_mul (by linarith) hN12 (by positivity) (by positivity)
      _ = 3 / 4 * T ^ 3 := by ring
      _ ≤ 3 / 8 * T ^ 4 := by linarith
  have habc : a * b * c ≤ (9 / 4 * T) * (11 / 4 * T) * (13 / 4 * T) :=
    mul_le_mul (mul_le_mul haT hbT hb0 (by positivity)) hcT hc0 (by positivity)
  have habcd : a * b * c * d ≤ (9 / 4 * T) * (11 / 4 * T) * (13 / 4 * T) * (15 / 4 * T) :=
    mul_le_mul habc hdT hd0 (by positivity)
  have t5 : a * b * c / 720 ≤ T ^ 4 / 32 := by
    calc a * b * c / 720 ≤ (9 / 4 * T) * (11 / 4 * T) * (13 / 4 * T) / 720 := by linarith
      _ = 1287 / 46080 * T ^ 3 := by ring
      _ ≤ T ^ 4 / 32 := by linarith
  have t6 : a * b * c * d / 720 * 2 ≤ 19305 / 92160 * T ^ 4 := by
    calc a * b * c * d / 720 * 2
        ≤ (9 / 4 * T) * (11 / 4 * T) * (13 / 4 * T) * (15 / 4 * T) / 720 * 2 := by linarith
      _ = 19305 / 92160 * T ^ 4 := by ring
  linarith

/-- **Polynomial growth on the left strip, exponent `4`.** For `-5/2 ≤ Re s ≤ 2` and
`|Im s| ≥ 2`, `‖ζ s‖ ≤ 12 |Im s|⁴` (split at `N = ⌊|Im s|⌋`). -/
theorem zeta_growth_left_bound {s : ℂ} (h₁ : -5 / 2 ≤ s.re) (h₂ : s.re ≤ 2) (ht : 2 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 12 * |s.im| ^ 4 := by
  have hs1 : s ≠ 1 := fun h => by rw [h] at ht; norm_num at ht
  have hT0 : 0 ≤ |s.im| := abs_nonneg _
  have hN1 : 1 ≤ ⌊|s.im|⌋₊ := Nat.le_floor (by rw [Nat.cast_one]; linarith)
  have hNle : (⌊|s.im|⌋₊ : ℝ) ≤ |s.im| := Nat.floor_le hT0
  have hltN : |s.im| < ⌊|s.im|⌋₊ + 1 := Nat.lt_floor_add_one |s.im|
  -- the elementary facts about `s`
  have hsm : 2 ≤ ‖s - 1‖ := by
    calc (2 : ℝ) ≤ |s.im| := ht
      _ = |(s - 1).im| := by simp
      _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
  have hs : ‖s‖ ≤ 5 / 2 + |s.im| := by
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 5 / 2 + |s.im| := by
          gcongr
          rw [abs_le]
          constructor <;> linarith
  have hs1n : ‖s + 1‖ ≤ 7 / 2 + |s.im| := by
    have : ‖s + 1‖ ≤ ‖s‖ + 1 := by simpa using norm_add_le s 1
    linarith
  have hs2n : ‖s + 2‖ ≤ 9 / 2 + |s.im| := by
    have : ‖s + 2‖ ≤ ‖s‖ + 2 := by simpa using norm_add_le s 2
    linarith
  have hs3n : ‖s + 3‖ ≤ 11 / 2 + |s.im| := by
    have : ‖s + 3‖ ≤ ‖s‖ + 3 := by simpa using norm_add_le s 3
    linarith
  exact (norm_zeta_le_split₄ h₁ hs1 hN1).trans
    (growth_arith ht (Nat.cast_nonneg _) hNle (by linarith) hsm (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) hs hs1n hs2n hs3n)

/-- **Polynomial growth on the left strip, real exponent.** For `-5/2 ≤ Re s ≤ 2` and
`|Im s| ≥ 2`, `‖ζ s‖ ≤ 12 |Im s|^{4}` (with `rpow`). -/
theorem zeta_growth_left_rpow {s : ℂ} (h₁ : -5 / 2 ≤ s.re) (h₂ : s.re ≤ 2) (ht : 2 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 12 * |s.im| ^ (4 : ℝ) := by
  rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact zeta_growth_left_bound h₁ h₂ ht

/-- **Deliverable (3), existential form:** `∃ C A, ∀ s, -5/2 ≤ Re s → Re s ≤ 2 → 2 ≤ |Im s| →
‖ζ s‖ ≤ C |Im s|^A` (with `C = 12`, `A = 4`). -/
theorem zeta_growth_left :
    ∃ C A : ℝ, ∀ s : ℂ, -5 / 2 ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * |s.im| ^ A :=
  ⟨12, 4, fun _ h₁ h₂ ht => zeta_growth_left_rpow h₁ h₂ ht⟩

end ZetaGrowthEM3

end
