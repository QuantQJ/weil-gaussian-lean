import FleetDirichletZeroFree
import FleetPsiStrip
import FleetTwistedWindowGrowth

/-!
# Least quadratic nonresidue from a zero-free half-plane for the quadratic characters

Main results:

* `exists_nonresidue_le_of_dirichletQuasiRH`: under `FleetDirichletZeroFree.DirichletQuasiRH`, for every
  `A > 8` there is `C` such that every odd prime `p` has a quadratic nonresidue `n` with
  `0 < n ≤ C (log p)^A`.
* `exists_nonresidue_le_of_zeroFree`: the same with `A > 1/(1 − θ₀)`, from the weaker hypothesis that for
  every odd prime `p` the `L`-function of the quadratic character mod `p` (`legendreChar p`) has no zero in
  `Re s > θ₀` (`1/2 ≤ θ₀ < 1`). Only these characters are used.

Route (Perron + contour shift, constants tracked in the modulus `N`):

1. `logDeriv_LFunction_le`: for `χ ≠ 1` mod `N` with `L(·,χ) ≠ 0` on `Re s > θ₀`,
   `‖L'/L(σ+it,χ)‖ ≤ (14 log(6N(|t|+8)) + 42)/δ²` on `θ₀ + 2δ ≤ σ ≤ 3 + θ₀`. This is the argument of
   `FleetPsiStrip.logDeriv_zeta_le` (holomorphic `log L` on a zero-free disc via
   `FleetLandauTransfer.exists_log_ball`, Mathlib's Borel–Carathéodory, Cauchy estimate), with the growth
   input `‖L(s,χ)‖ ≤ 5N‖s‖ + 1` (`FleetTwistedWindow.norm_LFunction_le`) and `‖log L(c,χ)‖ ≤ 3` on
   `Re c ≥ 2` (`LFunction_sub_one_norm_le`, `norm_log_le_three`). `L(·,χ)` is entire, so there is no pole.
2. `negLogDerivL_bound`: `‖L'/L(s,χ)‖ ≤ bigC N δ η · (1 + |Im s|)^η` on `Re s ≥ θ₀ + 2δ`, where
   `bigC N δ η = (14 log(6N) + 14 log 8 + 42 + 14/η)/δ² + Σ Λ(n)n^{-2}` is linear in `log N`.
3. `norm_sum_twistVM_le`: `FleetPsiStrip.partial_sum_bound'` (Perron, contour shift, unsmoothing; its
   constant is linear in the line bound) gives `‖Σ_{n ≤ x} χ(n)Λ(n)‖ ≤ (K log(6N) + K') x^α` for any
   `θ₀ < α < 1`, with `K, K'` depending only on `θ₀, α`.
4. `sum_twistVM_eq_psi`: if every `0 < n ≤ x < p` is a square mod `p`, the twisted sum for `legendreChar p`
   is `ψ(x)`; `quarter_le_psi` (`ψ(x) ≥ x/4` for `x ≥ 64`, from Mathlib's `Chebyshev.psi_ge'`).
   With `x = n(p) − 1`: `x/4 ≤ K'' log p · x^α`, so `x ≤ (4K'' log p)^{1/(1−α)}`, `1/(1−α) = A`.

The exponent is `A > 1/(1 − θ₀)` (any), not `A = 1/(1 − θ₀)`: step 1 bounds `L'/L` by `log` growth on lines
`Re s = θ₀ + 2δ`, which costs the `ε`; reaching `A = 8` itself would need the sum over zeros (explicit
formula with zero counting for `L(s,χ)`), which is not done here.
-/

set_option autoImplicit false
noncomputable section
open Complex Metric Set Filter Topology
open scoped ArithmeticFunction.vonMangoldt

namespace FleetLeastNonresidue

open FleetLandauTransfer

variable {N : ℕ} [NeZero N]
set_option linter.unusedSectionVars false

/-! ## 1. `L(s,χ)` near `1` on `Re s ≥ 2`, and its logarithm -/

/-- For `Re s ≥ 2`, `‖L(s,χ) − 1‖ ≤ π²/6 − 1` (the terms `n ≥ 2` of the Dirichlet series). -/
lemma LFunction_sub_one_norm_le (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖DirichletCharacter.LFunction χ s - 1‖ ≤ Real.pi ^ 2 / 6 - 1 := by
  have hs1 : 1 < s.re := by linarith
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs1]
  have hsum : LSeriesSummable (fun n : ℕ => χ n) s :=
    (DirichletCharacter.LSeriesSummable_iff (NeZero.ne N) χ).mpr hs1
  have h := (hasSum_nat_add_iff' 2).mpr hsum.LSeriesHasSum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, LSeries.term_zero,
    LSeries.term_of_ne_zero one_ne_zero, Nat.cast_one, map_one, one_cpow, div_one] at h
  refine h.norm_le_of_bounded hasSum_inv_sq_from_two fun n => ?_
  rw [LSeries.norm_term_eq]
  simp only [Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ↓reduceIte]
  have hn2 : (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by push_cast; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hpow : ((n + 2 : ℕ) : ℝ) ^ (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) ^ s.re :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hs
  have hchi : ‖χ ((n + 2 : ℕ) : ZMod N)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  calc ‖χ ((n + 2 : ℕ) : ZMod N)‖ / ((n + 2 : ℕ) : ℝ) ^ s.re
      ≤ 1 / ((n + 2 : ℕ) : ℝ) ^ s.re := by gcongr
    _ ≤ 1 / ((n + 2 : ℕ) : ℝ) ^ (2 : ℝ) := by
        apply one_div_le_one_div_of_le (by positivity) hpow
    _ = 1 / ((n : ℝ) + 2) ^ 2 := by rw [Real.rpow_two]; push_cast; ring

/-- A complex number within `π²/6 − 1` of `1` has `‖log w‖ ≤ 3`. -/
lemma norm_log_le_three {w : ℂ} (h : ‖w - 1‖ ≤ Real.pi ^ 2 / 6 - 1) : ‖Complex.log w‖ ≤ 3 := by
  have h2 := pi_sq_div_six_sub_one_lt
  have hhi : ‖w‖ ≤ 2 := by
    calc ‖w‖ = ‖(w - 1) + 1‖ := by ring_nf
      _ ≤ ‖w - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith
  have hlo : 1 / 3 ≤ ‖w‖ := by
    have : ‖(1 : ℂ)‖ ≤ ‖w‖ + ‖w - 1‖ := by
      calc ‖(1 : ℂ)‖ = ‖w - (w - 1)‖ := by ring_nf
        _ ≤ ‖w‖ + ‖w - 1‖ := norm_sub_le _ _
    rw [norm_one] at this
    linarith
  have hre : 0 < w.re := by
    have h3 : |(w - 1).re| ≤ ‖w - 1‖ := abs_re_le_norm _
    have h4 : (w - 1).re = w.re - 1 := by simp
    rw [h4] at h3
    have := (abs_le.mp h3).1
    linarith
  have hpos : 0 < ‖w‖ := by linarith
  have harg : |arg w| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have hlog : |Real.log ‖w‖| ≤ Real.log 3 := by
    rw [abs_le]
    constructor
    · have : Real.log (1 / 3) ≤ Real.log ‖w‖ := Real.log_le_log (by norm_num) hlo
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
  calc ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| :=
        norm_le_abs_re_add_abs_im _
    _ = |Real.log ‖w‖| + |arg w| := by rw [log_re, log_im]
    _ ≤ 3 := by linarith

/-! ## 2. `L'/L` to the right of a zero-free half-plane, uniformly in the modulus -/

/-- **Log-derivative bound, explicit in the modulus.** Let `χ ≠ 1` mod `N`, `1/4 ≤ θ₀ ≤ 1`, and
`L(s,χ) ≠ 0` on `Re s > θ₀`. For `δ > 0`, `θ₀ + 2δ ≤ σ ≤ 3 + θ₀` and every `t`:
`‖L'(σ+it,χ)/L(σ+it,χ)‖ ≤ (14 log(6N(|t|+8)) + 42)/δ/δ`.
(The argument of `FleetPsiStrip.logDeriv_zeta_le`: holomorphic `log L` on a zero-free disc,
Borel–Carathéodory, Cauchy; `L(·,χ)` is entire, so there is no pole and no restriction on `t`.) -/
theorem logDeriv_LFunction_le (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {θ₀ : ℝ}
    (hθ₀ : 1 / 4 ≤ θ₀) (hθ₀1 : θ₀ ≤ 1)
    (hZ : ∀ s : ℂ, θ₀ < s.re → DirichletCharacter.LFunction χ s ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) {σ t : ℝ} (hσ1 : θ₀ + 2 * δ ≤ σ) (hσ2 : σ ≤ 3 + θ₀) :
    ‖deriv (DirichletCharacter.LFunction χ) (σ + t * I) /
        DirichletCharacter.LFunction χ (σ + t * I)‖ ≤
      (14 * Real.log (6 * N * (|t| + 8)) + 42) / δ / δ := by
  set f := DirichletCharacter.LFunction χ with hf
  set c : ℂ := (θ₀ + 7 / 2 : ℝ) + t * I with hc
  set R : ℝ := 7 / 2 - δ / 2 with hR
  set r₃ : ℝ := 7 / 2 - δ with hr₃
  have hRpos : 0 < R := by linarith
  have hball : ∀ z ∈ ball c R, θ₀ + δ / 2 < z.re ∧ ‖z‖ ≤ |t| + 8 := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have h1 := abs_re_le_norm (z - c)
    have e1 : (z - c).re = z.re - (θ₀ + 7 / 2) := by simp [hc]
    rw [e1] at h1
    have a1 := (abs_lt.mp (h1.trans_lt hz)).1
    have hcn : ‖c‖ ≤ θ₀ + 7 / 2 + |t| := by
      calc ‖c‖ ≤ |c.re| + |c.im| := norm_le_abs_re_add_abs_im c
        _ = θ₀ + 7 / 2 + |t| := by
          simp [hc]; linarith
    have : ‖z‖ ≤ ‖c‖ + ‖z - c‖ := by
      calc ‖z‖ = ‖c + (z - c)‖ := by ring_nf
        _ ≤ ‖c‖ + ‖z - c‖ := norm_add_le _ _
    refine ⟨by linarith, by linarith⟩
  have hd : ∀ z ∈ ball c R, DifferentiableAt ℂ f z :=
    fun z _ => DirichletCharacter.differentiable_LFunction hχ z
  have hnz : ∀ z ∈ ball c R, f z ≠ 0 :=
    fun z hz => hZ z (by linarith [(hball z hz).1])
  obtain ⟨L, hLd, hLexp, hLc⟩ := exists_log_ball hd hnz hRpos
  have hcre : c.re = θ₀ + 7 / 2 := by simp [hc]
  have hLc3 : ‖L c‖ ≤ 3 := by
    rw [hLc]; exact norm_log_le_three (LFunction_sub_one_norm_le χ (by rw [hcre]; linarith))
  -- Borel–Carathéodory
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  set M := Real.log (6 * N * (|t| + 8)) with hM
  have hMpos : 0 < M := Real.log_pos (by nlinarith [abs_nonneg t])
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
    have hre : (L (c + z)).re = Real.log ‖f (c + z)‖ := by
      rw [← hLexp _ hw, norm_exp, Real.log_exp]
    rw [hre]
    obtain ⟨h1, h2⟩ := hball _ hw
    have hz5 := FleetTwistedWindow.norm_LFunction_le χ hχ (s := c + z) (by linarith)
    apply Real.log_le_log (norm_pos_iff.mpr (hnz _ hw))
    nlinarith [abs_nonneg t, norm_nonneg (c + z)]
  have hBC : ∀ w, ‖w - c‖ ≤ r₃ → ‖L w‖ ≤ (14 * M + 42) / δ := by
    intro w hw
    have hz : w - c ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff]; linarith
    have key := Complex.borelCaratheodory hMpos hgd hgM hRpos hz
    simp only [hg, add_sub_cancel, add_zero] at key
    have hu0 := norm_nonneg (w - c)
    have hden : δ / 2 ≤ R - ‖w - c‖ := by linarith
    have hδ2 : 0 < δ / 2 := by positivity
    have t1 : 2 * M * ‖w - c‖ / (R - ‖w - c‖) ≤ 2 * M * (7 / 2) / (δ / 2) :=
      div_le_div₀ (by positivity) (by gcongr; linarith) hδ2 hden
    have t2 : ‖L c‖ * (R + ‖w - c‖) / (R - ‖w - c‖) ≤ 3 * 7 / (δ / 2) :=
      div_le_div₀ (by norm_num) (mul_le_mul hLc3 (by linarith) (by linarith) (by norm_num))
        hδ2 hden
    calc ‖L w‖ ≤ _ := key
      _ ≤ 2 * M * (7 / 2) / (δ / 2) + 3 * 7 / (δ / 2) := add_le_add t1 t2
      _ = (14 * M + 42) / δ := by field_simp; ring
  -- Cauchy estimate on the circle of radius `δ` about `s = σ + it`
  set s : ℂ := (σ : ℂ) + t * I with hs
  have hsc : ‖s - c‖ = θ₀ + 7 / 2 - σ := by
    have : s - c = ((σ - (θ₀ + 7 / 2) : ℝ) : ℂ) := by rw [hs, hc]; push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have hcl : closedBall s δ ⊆ ball c R := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [mem_ball, dist_eq_norm]
    calc ‖z - c‖ ≤ ‖z - s‖ + ‖s - c‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < R := by rw [hsc]; linarith
  have hdc : DiffContOnCl ℂ L (ball s δ) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball s hδ.ne']
    exact fun z hz => (hLd z (hcl hz)).differentiableAt.differentiableWithinAt
  have hsph : ∀ z ∈ sphere s δ, ‖L z‖ ≤ (14 * M + 42) / δ := by
    intro z hz
    apply hBC
    rw [mem_sphere, dist_eq_norm] at hz
    calc ‖z - c‖ ≤ ‖z - s‖ + ‖s - c‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ r₃ := by rw [hz, hsc]; linarith
  have key := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ hdc hsph
  have hsR : s ∈ ball c R := hcl (mem_closedBall_self hδ.le)
  rw [(hLd s hsR).deriv] at key
  exact key

/-! ## 3. `G = −L'/L`, the Dirichlet series of `χ(n)Λ(n)` -/

/-- `G_χ(s) = −L'(s,χ)/L(s,χ)`. -/
def negLogDerivL (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s

/-- The twisted von Mangoldt coefficients `χ(n) Λ(n)`. -/
def twistVM (χ : DirichletCharacter ℂ N) (n : ℕ) : ℂ := χ n * (Λ n : ℂ)

lemma twistVM_zero (χ : DirichletCharacter ℂ N) : twistVM χ 0 = 0 := by simp [twistVM]

lemma norm_twistVM_le (χ : DirichletCharacter ℂ N) (n : ℕ) : ‖twistVM χ n‖ ≤ Λ n := by
  rw [twistVM, norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (DirichletCharacter.norm_le_one χ _)

/-- `‖χ(n)Λ(n)‖ ≤ (1/κ) n^κ`. -/
lemma norm_twistVM_le_rpow (χ : DirichletCharacter ℂ N) {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    ‖twistVM χ n‖ ≤ 1 / κ * (n : ℝ) ^ κ := by
  refine (norm_twistVM_le χ n).trans ?_
  have h1 : Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
  have h2 := Real.log_le_rpow_div (Nat.cast_nonneg n) hκ
  calc Λ n ≤ (n : ℝ) ^ κ / κ := h1.trans h2
    _ = 1 / κ * (n : ℝ) ^ κ := by ring

lemma negLogDerivL_eq_LSeries (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    negLogDerivL χ s = LSeries (twistVM χ) s := by
  rw [negLogDerivL, DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs, neg_div]
  have := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  rw [neg_div] at this
  exact this.symm

lemma negLogDerivL_differentiableAt (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ}
    (hs : DirichletCharacter.LFunction χ s ≠ 0) : DifferentiableAt ℂ (negLogDerivL χ) s := by
  have hd := DirichletCharacter.differentiable_LFunction hχ
  have hd' : DifferentiableAt ℂ (deriv (DirichletCharacter.LFunction χ)) s :=
    (hd.differentiableOn.deriv isOpen_univ).differentiableAt (isOpen_univ.mem_nhds (mem_univ s))
  exact (hd'.neg).div (hd s) hs

/-- `S = Σ Λ(n) n^{-2}`. -/
def S2 : ℝ := ∑' n : ℕ, ExplicitFormula.coeff 2 n

lemma S2_nonneg : 0 ≤ S2 := tsum_nonneg fun _ => ExplicitFormula.coeff_nonneg _ _

/-- On `Re s ≥ 2`, `‖G_χ(s)‖ ≤ Σ Λ(n) n^{-2}`. -/
lemma norm_negLogDerivL_le_of_re_ge (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖negLogDerivL χ s‖ ≤ S2 := by
  have h1 : 1 < s.re := by linarith
  have hsum : Summable fun n : ℕ => ‖LSeries.term (twistVM χ) s n‖ := by
    have : LSeriesSummable (twistVM χ) s :=
      DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ h1
    exact summable_norm_iff.mpr this
  have hc : Summable (ExplicitFormula.coeff 2) := ExplicitFormula.coeff_summable (by norm_num)
  rw [negLogDerivL_eq_LSeries χ h1, LSeries]
  refine (norm_tsum_le_tsum_norm hsum).trans (Summable.tsum_le_tsum (fun n => ?_) hsum hc)
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · exact ExplicitFormula.coeff_nonneg _ _
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    rw [ExplicitFormula.coeff, Real.rpow_neg (by linarith), div_eq_mul_inv]
    exact mul_le_mul (norm_twistVM_le χ n)
      (inv_anti₀ (by positivity) (Real.rpow_le_rpow_of_exponent_le hn1 hs))
      (by positivity) ArithmeticFunction.vonMangoldt_nonneg

/-- The constant of `negLogDerivL_bound`: `(14 log(6N) + 14 log 8 + 42 + 14/η)/δ² + Σ Λ(n)n^{-2}`. -/
def bigC (N : ℕ) (δ η : ℝ) : ℝ :=
  (14 * Real.log (6 * N) + 14 * Real.log 8 + 42 + 14 / η) / δ / δ + S2

/-- **`‖L'/L(s,χ)‖ ≤ C(N) (1 + |Im s|)^η`** on `Re s ≥ θ₀ + 2δ`, with `C(N) = bigC N δ η` linear in
`log N`, when `L(·,χ) ≠ 0` on `Re s > θ₀` (`χ ≠ 1`, `1/4 ≤ θ₀ ≤ 1`, `δ, η > 0`). -/
theorem negLogDerivL_bound (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {θ₀ : ℝ}
    (hθ₀ : 1 / 4 ≤ θ₀) (hθ₀1 : θ₀ ≤ 1)
    (hZ : ∀ s : ℂ, θ₀ < s.re → DirichletCharacter.LFunction χ s ≠ 0)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) (s : ℂ) (hs : θ₀ + 2 * δ ≤ s.re) :
    ‖negLogDerivL χ s‖ ≤ bigC N δ η * (1 + |s.im|) ^ η := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have h1 : 1 ≤ (1 + |s.im|) ^ η := Real.one_le_rpow (by linarith [abs_nonneg s.im]) hη.le
  have hl6 : 0 ≤ Real.log (6 * N) := Real.log_nonneg (by linarith)
  have hl8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  set A := 14 * Real.log (6 * N) + 14 * Real.log 8 + 42 + 14 / η with hA
  have hA0 : 0 ≤ A := by positivity
  have hS := S2_nonneg
  by_cases h3 : s.re ≤ 3 + θ₀
  · have e : s = (s.re : ℂ) + (s.im : ℂ) * I := (re_add_im s).symm
    have key := logDeriv_LFunction_le χ hχ hθ₀ hθ₀1 hZ hδ (σ := s.re) (t := s.im) hs h3
    rw [← e] at key
    have hlog : Real.log (6 * N * (|s.im| + 8)) ≤
        Real.log (6 * N) + Real.log 8 + (1 + |s.im|) ^ η / η := by
      rw [Real.log_mul (by positivity) (by positivity)]
      have h8 : Real.log (|s.im| + 8) ≤ Real.log 8 + Real.log (1 + |s.im|) := by
        rw [← Real.log_mul (by norm_num) (by positivity)]
        exact Real.log_le_log (by positivity) (by linarith [abs_nonneg s.im])
      have h9 := Real.log_le_rpow_div (x := 1 + |s.im|) (by positivity) hη
      linarith
    have hnum : 14 * Real.log (6 * N * (|s.im| + 8)) + 42 ≤ A * (1 + |s.im|) ^ η := by
      calc 14 * Real.log (6 * N * (|s.im| + 8)) + 42
          ≤ 14 * (Real.log (6 * N) + Real.log 8 + (1 + |s.im|) ^ η / η) + 42 := by linarith
        _ = (14 * Real.log (6 * N) + 14 * Real.log 8 + 42) * 1 + 14 / η * (1 + |s.im|) ^ η := by
            ring
        _ ≤ (14 * Real.log (6 * N) + 14 * Real.log 8 + 42) * (1 + |s.im|) ^ η +
              14 / η * (1 + |s.im|) ^ η := by gcongr
        _ = A * (1 + |s.im|) ^ η := by rw [hA]; ring
    have hG : ‖negLogDerivL χ s‖ = ‖deriv (DirichletCharacter.LFunction χ) s /
        DirichletCharacter.LFunction χ s‖ := by rw [negLogDerivL, neg_div, norm_neg]
    rw [hG]
    calc _ ≤ (14 * Real.log (6 * N * (|s.im| + 8)) + 42) / δ / δ := key
      _ ≤ A * (1 + |s.im|) ^ η / δ / δ := by gcongr
      _ = A / δ / δ * (1 + |s.im|) ^ η := by ring
      _ ≤ bigC N δ η * (1 + |s.im|) ^ η := by
          gcongr
          rw [bigC, ← hA]; linarith
  · push Not at h3
    have hb := norm_negLogDerivL_le_of_re_ge χ (s := s) (by linarith)
    have hC : S2 ≤ bigC N δ η := by
      rw [bigC, ← hA]; have : 0 ≤ A / δ / δ := by positivity
      linarith
    calc ‖negLogDerivL χ s‖ ≤ S2 := hb
      _ ≤ bigC N δ η := hC
      _ ≤ bigC N δ η * (1 + |s.im|) ^ η := le_mul_of_one_le_right (hS.trans hC) h1

/-! ## 4. Partial sums of `χ(n)Λ(n)`, explicit in the modulus -/

/-- **Twisted Chebyshev sum to the right of a zero-free half-plane, uniformly in the modulus.**
For `1/2 ≤ θ₀ < α < 1` there are `K, K' ≥ 0` (depending only on `θ₀, α`) such that for every modulus
`N`, every `χ ≠ 1` mod `N` with `L(s,χ) ≠ 0` on `Re s > θ₀`, and every `x ≥ 1`:
`‖Σ_{n ≤ x} χ(n)Λ(n)‖ ≤ (K log(6N) + K') x^α`. -/
theorem norm_sum_twistVM_le {θ₀ α : ℝ} (hθ₀ : 1 / 2 ≤ θ₀) (hθα : θ₀ < α) (hα1 : α < 1) :
    ∃ K K' : ℝ, 0 ≤ K ∧ 0 ≤ K' ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      (∀ s : ℂ, θ₀ < s.re → DirichletCharacter.LFunction χ s ≠ 0) → ∀ x : ℝ, 1 ≤ x →
        ‖∑ n ∈ Finset.Iic ⌊x⌋₊, twistVM χ n‖ ≤ (K * Real.log (6 * N) + K') * x ^ α := by
  set g := α - θ₀ with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  set δ := g / 4 with hδ
  set θ := g / 2 with hθ
  set η := θ / 2 with hη
  set κ := α - 1 / 2 with hκ
  have hδ0 : 0 < δ := by positivity
  have hθ0 : 0 < θ := by positivity
  have hη0 : 0 < η := by positivity
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  set I := ∫ t : ℝ, (1 + ‖t‖) ^ (-(1 + θ / 2)) with hI
  have hI0 : 0 ≤ I := MeasureTheory.integral_nonneg fun t => Real.rpow_nonneg (by positivity) _
  set K := 64 * 16 * I * 14 / δ / δ with hK
  set K' := 64 * 16 * I * ((14 * Real.log 8 + 42 + 14 / η) / δ / δ + S2) + 6 * (1 / κ) with hK'
  have hl8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hS := S2_nonneg
  refine ⟨K, K', by positivity, by positivity, ?_⟩
  intro N _ χ hχ hZ x hx
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hC0 : 0 ≤ bigC N δ η := by
    have : 0 ≤ Real.log (6 * N) := Real.log_nonneg (by linarith)
    rw [bigC]; positivity
  have key := FleetPsiStrip.partial_sum_bound' (a := twistVM χ) (twistVM_zero χ)
    (B := 1 / κ) (κ := κ) (by positivity) (norm_twistVM_le_rpow χ hκ0) hκ0.le (by rw [hκ]; linarith)
    (G := negLogDerivL χ) (fun s hs => negLogDerivL_eq_LSeries χ hs)
    (σ₀ := θ₀ + 2 * δ) (θ := θ) (C := bigC N δ η)
    (by linarith) (by rw [hδ, hg]; linarith) hθ0 (by rw [hθ, hg]; linarith)
    (by rw [hκ, hθ, hδ, hg]; linarith) hC0
    (fun s hs => negLogDerivL_differentiableAt χ hχ (hZ s (by linarith)))
    (fun s hs => negLogDerivL_bound χ hχ (by linarith) (by linarith) hZ hδ0 hη0 s hs) hx
  have hexp : θ₀ + 2 * δ + θ = α := by rw [hθ, hδ, hg]; ring
  rw [hexp] at key
  refine key.trans (le_of_eq ?_)
  rw [bigC, hK, hK']
  ring

/-! ## 5. The quadratic character mod `p` -/

/-- The quadratic (Legendre) character mod a prime `p`, as a Dirichlet character with values in `ℂ`. -/
def legendreChar (p : ℕ) [Fact p.Prime] : DirichletCharacter ℂ p :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

lemma legendreChar_apply (p : ℕ) [Fact p.Prime] (a : ZMod p) :
    legendreChar p a = ((quadraticChar (ZMod p) a : ℤ) : ℂ) := by
  simp [legendreChar, MulChar.ringHomComp_apply]

lemma legendreChar_ne_one (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) : legendreChar p ≠ 1 := by
  intro h
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
  have ha0 : a ≠ 0 := by
    intro h0; rw [h0, quadraticChar_zero] at ha; norm_num at ha
  have h1 : legendreChar p a = 1 := by
    rw [h, MulChar.one_apply (Ne.isUnit ha0)]
  rw [legendreChar_apply, ha] at h1
  norm_num at h1

lemma legendreChar_eq_one_of_isSquare (p : ℕ) [Fact p.Prime] {a : ZMod p} (ha0 : a ≠ 0)
    (ha : IsSquare a) : legendreChar p a = 1 := by
  rw [legendreChar_apply, (quadraticChar_one_iff_isSquare ha0).mpr ha]
  simp

/-- If every `0 < n ≤ x` is a square mod `p` and `x < p`, then `Σ_{n ≤ x} χ_p(n)Λ(n) = ψ(x)`. -/
lemma sum_twistVM_eq_psi (p : ℕ) [Fact p.Prime] {x : ℝ} (hxp : ⌊x⌋₊ < p)
    (hsq : ∀ n : ℕ, 0 < n → n ≤ ⌊x⌋₊ → IsSquare (n : ZMod p)) :
    ∑ n ∈ Finset.Iic ⌊x⌋₊, twistVM (legendreChar p) n = (Chebyshev.psi x : ℂ) := by
  have hpsi : Chebyshev.psi x = ∑ n ∈ Finset.Iic ⌊x⌋₊, Λ n := by
    rw [Chebyshev.psi_eq_sum_Icc]
    congr 1
  rw [hpsi]
  push_cast
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Iic] at hn
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp [twistVM]
  have hne : (n : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd hn0 hd
    omega
  rw [twistVM, legendreChar_eq_one_of_isSquare p hne (hsq n hn0 hn), one_mul]

/-! ## 6. The least quadratic nonresidue -/

/-- `ψ(x) ≥ x/4` for `x ≥ 64` (from Mathlib's `Chebyshev.psi_ge'`). -/
lemma quarter_le_psi {x : ℝ} (hx : 64 ≤ x) : x / 4 ≤ Chebyshev.psi x := by
  have h := Chebyshev.psi_ge' (x := x) (by linarith)
  have hl2 := Real.log_two_gt_d9
  have hlog : Real.log (x + 2) ≤ 2 * Real.sqrt (x + 2) := by
    have := Real.log_le_rpow_div (x := x + 2) (ε := 1 / 2) (by linarith) (by norm_num)
    rw [← Real.sqrt_eq_rpow] at this
    linarith
  set u := Real.sqrt (x + 2) with hu
  have hu2 : u ^ 2 = x + 2 := Real.sq_sqrt (by linarith)
  have hu8 : 8 ≤ u := by
    rw [hu, show (8 : ℝ) = Real.sqrt 64 by
      rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  nlinarith

/-- **Least quadratic nonresidue from a zero-free half-plane.** Let `1/2 ≤ θ₀ < 1` and suppose that for
every odd prime `p` the `L`-function of the quadratic character mod `p` has no zero in `Re s > θ₀`.
Then for every `A > 1/(1 − θ₀)` there is `C` such that every odd prime `p` has a quadratic nonresidue
`n` with `0 < n ≤ C (log p)^A`. -/
theorem exists_nonresidue_le_of_zeroFree {θ₀ : ℝ} (hθ₀ : 1 / 2 ≤ θ₀) (hθ₀1 : θ₀ < 1)
    (hZ : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ s : ℂ, θ₀ < s.re →
      DirichletCharacter.LFunction (legendreChar p) s ≠ 0)
    {A : ℝ} (hA : 1 / (1 - θ₀) < A) :
    ∃ C : ℝ, ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ C * Real.log p ^ A ∧ ¬ IsSquare (n : ZMod p) := by
  have h1θ : 0 < 1 - θ₀ := by linarith
  have hA2 : 2 ≤ 1 / (1 - θ₀) := by
    rw [le_div_iff₀ h1θ]; linarith
  have hA0 : 0 < A := by linarith
  set α := 1 - A⁻¹ with hα
  have hAinv : A⁻¹ < 1 - θ₀ := by
    rw [inv_lt_comm₀ hA0 h1θ]; rwa [one_div] at hA
  have hθα : θ₀ < α := by rw [hα]; linarith
  have hα1 : α < 1 := by rw [hα]; linarith [inv_pos.mpr hA0]
  obtain ⟨K, K', hK, hK', hsum⟩ := norm_sum_twistVM_le hθ₀ hθα hα1
  set K'' := 3 * K + K' with hK''
  have hK''0 : 0 ≤ K'' := by positivity
  refine ⟨max 65 (2 * (4 * K'') ^ A), ?_⟩
  intro p _ hp2
  have hp := (Fact.out : p.Prime)
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hL1 : 1 < Real.log p := by
    have h1 : Real.log 3 ≤ Real.log p :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hp3)
    have h3 : 1 < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      exact Real.exp_one_lt_d9.trans (by norm_num)
    linarith
  set Lp := Real.log p with hLp
  have hLA : 1 ≤ Lp ^ A := Real.one_le_rpow hL1.le hA0.le
  -- a nonresidue `a` exists, with `0 < a.val < p`
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
  have ha0 : a ≠ 0 := by
    intro h0; rw [h0, quadraticChar_zero] at ha; norm_num at ha
  have hav : 0 < a.val ∧ ¬ IsSquare ((a.val : ℕ) : ZMod p) := by
    refine ⟨Nat.pos_of_ne_zero (by rwa [Ne, ZMod.val_eq_zero]), ?_⟩
    rw [ZMod.natCast_zmod_val]
    exact quadraticChar_neg_one_iff_not_isSquare.mp ha
  have hex : ∃ n : ℕ, 0 < n ∧ ¬ IsSquare (n : ZMod p) := ⟨_, hav⟩
  classical
  set n₀ := Nat.find hex with hn₀def
  have hn₀ : 0 < n₀ ∧ ¬ IsSquare (n₀ : ZMod p) := Nat.find_spec hex
  have hn₀p : n₀ < p := lt_of_le_of_lt (Nat.find_min' hex hav) (ZMod.val_lt a)
  refine ⟨n₀, hn₀.1, ?_, hn₀.2⟩
  have hCm : 0 ≤ max 65 (2 * (4 * K'') ^ A) := le_trans (by norm_num) (le_max_left _ _)
  by_cases hsmall : (n₀ : ℝ) ≤ 65
  · calc (n₀ : ℝ) ≤ 65 := hsmall
      _ ≤ max 65 (2 * (4 * K'') ^ A) := le_max_left _ _
      _ ≤ max 65 (2 * (4 * K'') ^ A) * Lp ^ A := le_mul_of_one_le_right hCm hLA
  push Not at hsmall
  have hn₀1 : 1 ≤ n₀ := hn₀.1
  set x : ℝ := ((n₀ - 1 : ℕ) : ℝ) with hxdef
  have hxn : x = (n₀ : ℝ) - 1 := by rw [hxdef, Nat.cast_sub hn₀1]; norm_num
  have hx64 : 64 ≤ x := by rw [hxn]; linarith
  have hx0 : 0 < x := by linarith
  have hfl : ⌊x⌋₊ = n₀ - 1 := by rw [hxdef, Nat.floor_natCast]
  have hxp : ⌊x⌋₊ < p := by rw [hfl]; omega
  have hsq : ∀ n : ℕ, 0 < n → n ≤ ⌊x⌋₊ → IsSquare (n : ZMod p) := by
    intro n hn hle
    rw [hfl] at hle
    by_contra hns
    exact Nat.find_min hex (show n < n₀ by omega) ⟨hn, hns⟩
  have hS := sum_twistVM_eq_psi p hxp hsq
  have hb := hsum p (legendreChar p) (legendreChar_ne_one p hp2) (hZ p hp2) x (by linarith)
  rw [hS, Complex.norm_real, Real.norm_of_nonneg (Chebyshev.psi_nonneg x)] at hb
  have hq := quarter_le_psi hx64
  have hl6 : Real.log (6 * p) ≤ 3 * Lp := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    have hp3' : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    have h6 : Real.log 6 ≤ Real.log ((p : ℝ) ^ 2) :=
      Real.log_le_log (by norm_num) (by nlinarith)
    rw [Real.log_pow] at h6
    push_cast at h6
    linarith
  have hxα : 0 < x ^ α := Real.rpow_pos_of_pos hx0 _
  have hmain : x / 4 ≤ K'' * Lp * x ^ α := by
    calc x / 4 ≤ Chebyshev.psi x := hq
      _ ≤ (K * Real.log (6 * p) + K') * x ^ α := hb
      _ ≤ K'' * Lp * x ^ α := by
          gcongr
          rw [hK'']
          nlinarith
  have hsplit : x = x ^ α * x ^ A⁻¹ := by
    rw [← Real.rpow_add hx0, hα, show 1 - A⁻¹ + A⁻¹ = (1 : ℝ) by ring, Real.rpow_one]
  have hkey : x ^ A⁻¹ ≤ 4 * K'' * Lp := by
    have h2 : x ^ α * x ^ A⁻¹ ≤ x ^ α * (4 * K'' * Lp) := by
      rw [← hsplit]; nlinarith
    exact le_of_mul_le_mul_left h2 hxα
  have hxA : x ≤ (4 * K'') ^ A * Lp ^ A := by
    have h0 : 0 ≤ x ^ A⁻¹ := Real.rpow_nonneg hx0.le _
    calc x = (x ^ A⁻¹) ^ A := (Real.rpow_inv_rpow hx0.le hA0.ne').symm
      _ ≤ (4 * K'' * Lp) ^ A := Real.rpow_le_rpow h0 hkey hA0.le
      _ = (4 * K'') ^ A * Lp ^ A := Real.mul_rpow (by positivity) (by linarith)
  calc (n₀ : ℝ) = x + 1 := by rw [hxn]; ring
    _ ≤ 2 * x := by linarith
    _ ≤ 2 * ((4 * K'') ^ A * Lp ^ A) := by linarith
    _ = 2 * (4 * K'') ^ A * Lp ^ A := by ring
    _ ≤ max 65 (2 * (4 * K'') ^ A) * Lp ^ A := by
        gcongr
        exact le_max_right _ _

/-- **Least quadratic nonresidue from the Dirichlet `7/8` half-plane.** Under `DirichletQuasiRH`
(only its instances for the quadratic characters mod odd primes are used), for every `A > 8` there is
`C` such that every odd prime `p` has a quadratic nonresidue `n` with `0 < n ≤ C (log p)^A`. -/
theorem exists_nonresidue_le_of_dirichletQuasiRH (h : FleetDirichletZeroFree.DirichletQuasiRH)
    {A : ℝ} (hA : 8 < A) :
    ∃ C : ℝ, ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ C * Real.log p ^ A ∧ ¬ IsSquare (n : ZMod p) :=
  exists_nonresidue_le_of_zeroFree (θ₀ := 7 / 8) (by norm_num) (by norm_num)
    (fun p _ hp2 s hs => h (legendreChar p) hs (fun h1 => legendreChar_ne_one p hp2 h1.1))
    (by norm_num; exact hA)

end FleetLeastNonresidue
