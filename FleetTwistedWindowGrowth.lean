import Mathlib
import ZetaGrowth

/-!
# Growth of `L(s,χ)` on `Re s ≥ 1/4` for a nonprincipal Dirichlet character

The ζ-chain (`FleetHeadContourZeta`) bounds `ζ` on `Re s ≥ 1/4` through the Euler–Maclaurin
continuation `ζ = 1/(s−1) + Σ emTerm`. For a nonprincipal character `χ` mod `N` the partial sums
`B n = Σ_{m ≤ n} χ(m)` are bounded by `N` (`norm_psum_le`), and Abel summation gives the continuation

`L(s,χ) = Σ_{n ≥ 0} B(n+1) ((n+1)^{-s} − (n+2)^{-s}) − χ(0)`   on `Re s > 0`   (`LFunction_eq_abel`),

whose terms are `≤ N ‖s‖ (n+1)^{-Re s − 1}`.

* `norm_LFunction_le`       : `‖L(s,χ)‖ ≤ 5 N ‖s‖ + 1` on `Re s ≥ 1/4`.
* `norm_deriv_LFunction_le` : `‖L'(s,χ)‖ ≤ 20 N ‖s‖ + 5 N + 4` on `Re s ≥ 1/2` (Cauchy, radius `1/4`).

There is no pole: `L(·,χ)` is entire for `χ ≠ 1` (Mathlib `differentiable_LFunction`).
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set
open scoped Real

namespace FleetTwistedWindow

variable {N : ℕ} [NeZero N]
set_option linter.unusedSectionVars false

/-! ## Bounded partial sums -/

/-- `Σ_{m < n} χ(m)`. -/
def psum (χ : DirichletCharacter ℂ N) (n : ℕ) : ℂ := ∑ m ∈ Finset.range n, χ (m : ZMod N)

lemma sum_range_eq_sum_univ (χ : DirichletCharacter ℂ N) :
    ∑ m ∈ Finset.range N, χ (m : ZMod N) = ∑ j : ZMod N, χ j := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne N)
  rw [Finset.sum_range (fun m => χ (m : ZMod (n + 1)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact Fin.cast_val_eq_self i

lemma psum_mul_add (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (k r : ℕ) :
    psum χ (k * N + r) = psum χ r := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : (k + 1) * N + r = (k * N + r) + N := by ring
    rw [e, psum, Finset.sum_range_add, ← psum, ih]
    have h0 : ∑ x ∈ Finset.range N, χ (((k * N + r + x : ℕ)) : ZMod N)
        = ∑ x ∈ Finset.range N, χ (((r + x : ℕ)) : ZMod N) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      congr 1
      push_cast
      rw [ZMod.natCast_self]; ring
    rw [h0]
    -- shift invariance of a full period
    have hsum : ∑ x ∈ Finset.range N, χ (((r + x : ℕ)) : ZMod N) = 0 := by
      have hper : ∀ c : ℕ, ∑ x ∈ Finset.range N, χ (((c + x : ℕ)) : ZMod N)
          = ∑ x ∈ Finset.range N, χ (x : ZMod N) := by
        intro c
        induction c with
        | zero => simp
        | succ c ihc =>
          rw [← ihc]
          set g : ℕ → ℂ := fun x => χ (((c + x : ℕ)) : ZMod N) with hg
          have h1 := Finset.sum_range_succ' g N
          have h2 := Finset.sum_range_succ g N
          have hgN : g N = g 0 := by
            simp only [hg]
            congr 1
            push_cast
            rw [ZMod.natCast_self]
          have hmid : ∑ x ∈ Finset.range N, χ (((c + 1 + x : ℕ)) : ZMod N)
              = ∑ x ∈ Finset.range N, g (x + 1) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            simp only [hg]; congr 2; ring
          rw [hmid]
          change _ = ∑ x ∈ Finset.range N, g x
          linear_combination h2 - h1 + hgN
      rw [hper, sum_range_eq_sum_univ, MulChar.sum_eq_zero_of_ne_one hχ]
    rw [hsum, add_zero]

lemma norm_psum_le (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (n : ℕ) : ‖psum χ n‖ ≤ N := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have e : n = (n / N) * N + n % N := by rw [mul_comm]; exact (Nat.div_add_mod n N).symm
  rw [e, psum_mul_add χ hχ]
  calc ‖psum χ (n % N)‖ ≤ ∑ m ∈ Finset.range (n % N), ‖χ (m : ZMod N)‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.range (n % N), (1 : ℝ) :=
        Finset.sum_le_sum fun m _ => DirichletCharacter.norm_le_one χ _
    _ = (n % N : ℕ) := by simp
    _ ≤ N := by exact_mod_cast (Nat.mod_lt n hN).le

/-! ## Mean-value bound for `x^{-s}` -/

lemma norm_ofReal_cpow' {x : ℝ} (hx : 0 < x) (z : ℂ) : ‖(x : ℂ) ^ z‖ = x ^ z.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos hx z

/-- `‖(x+1)^{-s} − x^{-s}‖ ≤ ‖s‖ x^{-Re s − 1}` for `x ≥ 1`, `Re s ≥ 0`. -/
lemma norm_cpow_succ_sub_le {s : ℂ} (hs : 0 ≤ s.re) {x : ℝ} (hx : 1 ≤ x) :
    ‖((x + 1 : ℝ) : ℂ) ^ (-s) - (x : ℂ) ^ (-s)‖ ≤ ‖s‖ * x ^ (-s.re - 1) := by
  rcases eq_or_ne s 0 with rfl | hs0
  · simp
  set B : ℝ := ‖s‖ * x ^ (-s.re - 1) with hB
  have key := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun t : ℝ => (t : ℂ) ^ (-s)) (f' := fun t : ℝ => (-s) * (t : ℂ) ^ (-s - 1))
    (a := x) (b := x + 1) (C := B) ?_ ?_ (x + 1) ⟨by linarith, le_rfl⟩
  · calc _ ≤ B * (x + 1 - x) := key
      _ = B := by ring
  · intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact (hasDerivAt_ofReal_cpow_const ht0 (neg_ne_zero.mpr hs0)).hasDerivWithinAt
  · intro t ht
    have htpos : 0 < t := by linarith [ht.1]
    rw [norm_mul, norm_neg, norm_ofReal_cpow' htpos]
    simp only [sub_re, neg_re, one_re]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by linarith) ht.1 (by linarith)) (norm_nonneg _)

/-! ## The Abel continuation -/

/-- The Abel-summation terms `B(n+1) ((n+1)^{-s} − (n+2)^{-s})`, `B(j) = Σ_{m ≤ j} χ(m)`. -/
def abelTerm (χ : DirichletCharacter ℂ N) (n : ℕ) (s : ℂ) : ℂ :=
  psum χ (n + 2) * (((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 2 : ℕ) : ℂ) ^ (-s))

/-- The continuation `Σ_n abelTerm n s − χ(0)`. -/
def abelL (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ := (∑' n : ℕ, abelTerm χ n s) - χ 0

lemma norm_abelTerm_le (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (n : ℕ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖abelTerm χ n s‖ ≤ N * ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1) := by
  unfold abelTerm
  rw [norm_mul]
  have h1 := norm_psum_le χ hχ (n + 2)
  have h2 := norm_cpow_succ_sub_le hs (x := (n : ℝ) + 1) (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
  have e1 : (((n + 1 : ℕ) : ℂ)) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  have e2 : (((n + 2 : ℕ) : ℂ)) = ((((n : ℝ) + 1) + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2, norm_sub_rev]
  calc ‖psum χ (n + 2)‖ * ‖((((n : ℝ) + 1) + 1 : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)‖
      ≤ N * (‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1)) := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma differentiable_abelTerm (χ : DirichletCharacter ℂ N) (n : ℕ) :
    Differentiable ℂ (abelTerm χ n) := by
  unfold abelTerm
  have h1 : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  have h2 : ((n + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
  refine (differentiable_const _).mul ((fun w => ?_) : Differentiable ℂ _)
  exact ((differentiableAt_neg_iff.mpr differentiableAt_id).const_cpow (Or.inl h1)).sub
    ((differentiableAt_neg_iff.mpr differentiableAt_id).const_cpow (Or.inl h2))

lemma summable_abelTerm (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n => abelTerm χ n s) := by
  refine Summable.of_norm_bounded
    ((ZetaGrowth.summable_add_one_rpow (a := -s.re - 1) (by linarith)).mul_left (N * ‖s‖)) ?_
  intro n
  exact norm_abelTerm_le χ hχ n hs.le

/-- `abelL` is holomorphic on `Re s > 0`. -/
lemma differentiableOn_abelL (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    DifferentiableOn ℂ (abelL χ) {s : ℂ | 0 < s.re} := by
  intro s₀ hs₀
  have hs₀' : 0 < s₀.re := hs₀
  set U : Set ℂ := {w : ℂ | s₀.re / 2 < w.re} ∩ Metric.ball 0 (‖s₀‖ + 1) with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hs₀U : s₀ ∈ U := ⟨by show s₀.re / 2 < s₀.re; linarith,
    by rw [Metric.mem_ball, dist_zero_right]; linarith⟩
  have hd : DifferentiableOn ℂ (fun w => ∑' n : ℕ, abelTerm χ n w) U := by
    refine differentiableOn_tsum_of_summable_norm
      ((ZetaGrowth.summable_add_one_rpow (a := -(s₀.re / 2) - 1) (by linarith)).mul_left
        (N * (‖s₀‖ + 1))) (fun n => (differentiable_abelTerm χ n).differentiableOn) hUo ?_
    intro n w hw
    have hwre : s₀.re / 2 < w.re := hw.1
    have hwn : ‖w‖ < ‖s₀‖ + 1 := by have := hw.2; rwa [Metric.mem_ball, dist_zero_right] at this
    refine (norm_abelTerm_le χ hχ n (by linarith)).trans ?_
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    have hp : ((n : ℝ) + 1) ^ (-w.re - 1) ≤ ((n : ℝ) + 1) ^ (-(s₀.re / 2) - 1) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    exact mul_le_mul (mul_le_mul_of_nonneg_left hwn.le hN0) hp (by positivity) (by positivity)
  have hd' : DifferentiableOn ℂ (abelL χ) U := hd.sub (differentiableOn_const _)
  exact (hd'.differentiableAt (hUo.mem_nhds hs₀U)).differentiableWithinAt

/-! ## Agreement with `L(s,χ)` -/

lemma abel_partial (χ : DirichletCharacter ℂ N) (s : ℂ) (K : ℕ) :
    ∑ n ∈ Finset.range K, χ ((n + 1 : ℕ) : ZMod N) * ((n + 1 : ℕ) : ℂ) ^ (-s)
      = ∑ n ∈ Finset.range K, abelTerm χ n s + psum χ (K + 1) * ((K + 1 : ℕ) : ℂ) ^ (-s) - χ 0 := by
  induction K with
  | zero => simp [psum]
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have hp : psum χ (K + 1 + 1) = psum χ (K + 1) + χ ((K + 1 : ℕ) : ZMod N) := by
      rw [psum, Finset.sum_range_succ, ← psum]
    unfold abelTerm
    rw [show K + 2 = K + 1 + 1 by ring, hp]
    push_cast
    ring

lemma LSeries_eq_abelL (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => χ (n : ZMod N)) s = abelL χ s := by
  have hs0 : 0 < s.re := by linarith
  -- the LSeries as a limit of partial sums
  have hsum : Summable (LSeries.term (fun n => χ (n : ZMod N)) s) :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  have hsum1 := (summable_nat_add_iff 1).mpr hsum
  have hL : LSeries (fun n => χ (n : ZMod N)) s
      = ∑' n : ℕ, χ ((n + 1 : ℕ) : ZMod N) * ((n + 1 : ℕ) : ℂ) ^ (-s) := by
    unfold LSeries
    rw [hsum.tsum_eq_zero_add]
    simp only [LSeries.term_zero, zero_add]
    congr 1; funext n
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), Complex.cpow_neg, div_eq_mul_inv]
  have hsumT : Summable (fun n : ℕ => χ ((n + 1 : ℕ) : ZMod N) * ((n + 1 : ℕ) : ℂ) ^ (-s)) := by
    refine hsum1.congr fun n => ?_
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), Complex.cpow_neg, div_eq_mul_inv]
  have h1 := hsumT.hasSum.tendsto_sum_nat
  have h2 := (summable_abelTerm χ hχ hs0).hasSum.tendsto_sum_nat
  -- the boundary term tends to `0`
  have h3 : Tendsto (fun K : ℕ => psum χ (K + 1) * ((K + 1 : ℕ) : ℂ) ^ (-s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hdec : Tendsto (fun K : ℕ => (N : ℝ) * ((K : ℝ) + 1) ^ (-s.re)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop hs0).comp
        (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
      simpa using this.const_mul (N : ℝ)
    refine squeeze_zero (fun _ => norm_nonneg _) (fun K => ?_) hdec
    rw [norm_mul]
    have e : (((K + 1 : ℕ) : ℂ)) = (((K : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [e, norm_ofReal_cpow' (by positivity)]
    simp only [neg_re]
    exact mul_le_mul_of_nonneg_right (norm_psum_le χ hχ _) (by positivity)
  have hlim := (h2.add h3).sub_const (χ 0)
  rw [add_zero] at hlim
  have heq : (fun K => ∑ n ∈ Finset.range K, χ ((n + 1 : ℕ) : ZMod N) * ((n + 1 : ℕ) : ℂ) ^ (-s))
      = fun K => ∑ n ∈ Finset.range K, abelTerm χ n s + psum χ (K + 1) * ((K + 1 : ℕ) : ℂ) ^ (-s) - χ 0 :=
    funext (abel_partial χ s)
  rw [heq] at h1
  rw [hL, abelL]
  exact tendsto_nhds_unique h1 hlim

/-- **The Abel continuation equals `L(s,χ)` on `Re s > 0`.** -/
theorem LFunction_eq_abel (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s = abelL χ s := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hconv : Convex ℝ {s : ℂ | 0 < s.re} := convex_halfSpace_re_gt 0
  have hf : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) {s : ℂ | 0 < s.re} :=
    ((DirichletCharacter.differentiable_LFunction hχ).differentiableOn).analyticOnNhd hU
  have hg : AnalyticOnNhd ℂ (abelL χ) {s : ℂ | 0 < s.re} := (differentiableOn_abelL χ hχ).analyticOnNhd hU
  have h2 : (2 : ℂ) ∈ {s : ℂ | 0 < s.re} := by show (0 : ℝ) < (2 : ℂ).re; norm_num
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 (2 : ℂ)] abelL χ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with w hw
    rw [DirichletCharacter.LFunction_eq_LSeries χ hw]
    exact LSeries_eq_abelL χ hχ hw
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconv.isPreconnected h2 hev hs

/-! ## The bounds -/

/-- **`‖L(s,χ)‖ ≤ 5 N ‖s‖ + 1`** on `Re s ≥ 1/4`, `χ ≠ 1`. -/
theorem norm_LFunction_le (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ} (hs : 1 / 4 ≤ s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ 5 * N * ‖s‖ + 1 := by
  have hs0 : 0 < s.re := by linarith
  rw [LFunction_eq_abel χ hχ hs0, abelL]
  have hK := ZetaGrowth.tsum_add_one_rpow_le (p := 1 / 4) (by norm_num)
  have hsumr := ZetaGrowth.summable_add_one_rpow (a := -(1 + 1 / 4)) (by norm_num)
  have hT : ‖∑' n : ℕ, abelTerm χ n s‖ ≤ 5 * N * ‖s‖ := by
    calc ‖∑' n : ℕ, abelTerm χ n s‖
        ≤ ∑' n : ℕ, (N * ‖s‖) * ((n : ℝ) + 1) ^ (-(1 + 1 / 4 : ℝ)) := by
          refine tsum_of_norm_bounded (hsumr.mul_left _).hasSum fun n => ?_
          refine (norm_abelTerm_le χ hχ n hs0.le).trans ?_
          have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
          have := Real.rpow_le_rpow_of_exponent_le hn1 (show -s.re - 1 ≤ -(1 + 1 / 4 : ℝ) by linarith)
          calc (N : ℝ) * ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1)
              ≤ N * ‖s‖ * ((n : ℝ) + 1) ^ (-(1 + 1 / 4 : ℝ)) :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = _ := by ring
      _ = (N * ‖s‖) * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + 1 / 4 : ℝ)) := tsum_mul_left
      _ ≤ (N * ‖s‖) * 5 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          norm_num at hK ⊢; linarith
      _ = 5 * N * ‖s‖ := by ring
  calc ‖(∑' n : ℕ, abelTerm χ n s) - χ 0‖ ≤ ‖∑' n : ℕ, abelTerm χ n s‖ + ‖χ 0‖ := norm_sub_le _ _
    _ ≤ 5 * N * ‖s‖ + 1 := add_le_add hT (DirichletCharacter.norm_le_one χ 0)

/-- **Cauchy estimate: `‖L'(s,χ)‖ ≤ 20 N ‖s‖ + 5 N + 4`** on `Re s ≥ 1/2`, `χ ≠ 1`. -/
theorem norm_deriv_LFunction_le (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖deriv (DirichletCharacter.LFunction χ) s‖ ≤ 20 * N * ‖s‖ + 5 * N + 4 := by
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := s) (R := 1 / 4)
    (C := 5 * N * (‖s‖ + 1 / 4) + 1) (f := DirichletCharacter.LFunction χ) (by norm_num)
    (DirichletCharacter.differentiable_LFunction hχ).diffContOnCl ?_
  · calc _ ≤ (5 * N * (‖s‖ + 1 / 4) + 1) / (1 / 4) := h
      _ = 20 * N * ‖s‖ + 5 * N + 4 := by ring
  intro z hz
  rw [mem_sphere_iff_norm] at hz
  have hre : |(z - s).re| ≤ 1 / 4 := by rw [← hz]; exact Complex.abs_re_le_norm _
  have hzre : 1 / 4 ≤ z.re := by rw [sub_re] at hre; linarith [(abs_le.mp hre).1]
  have hzn : ‖z‖ ≤ ‖s‖ + 1 / 4 := by
    calc ‖z‖ = ‖s + (z - s)‖ := by ring_nf
      _ ≤ ‖s‖ + ‖z - s‖ := norm_add_le _ _
      _ = ‖s‖ + 1 / 4 := by rw [hz]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc ‖DirichletCharacter.LFunction χ z‖ ≤ 5 * N * ‖z‖ + 1 := norm_LFunction_le χ hχ hzre
    _ ≤ 5 * N * (‖s‖ + 1 / 4) + 1 := by nlinarith

end FleetTwistedWindow
