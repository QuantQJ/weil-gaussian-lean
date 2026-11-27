import FleetPrimeTarget

/-!
# Sharpness of the trivial bound for the smoothed prime sum

`S_b(q) = Σ_n 2 Λ(n) n^{-1/2} e^{-b log² n} cos(q log n)`, `T(b) = S_b(0)`. This is the existing
`FleetPrimeSideConsequences.primeSumSym b q` (`primeSumSym_eq_S`).

Source: `research_notes/DUAL-INEQUALITY/CANCELLATION_ANALYSIS.md` §1, "Proposition (proved).
sup over q in [X, infinity) of S_b(q) = T(b), for every X and every b > 0."

* `summable_coeff`, `summable_S` : summability for `b > 0`.
* `S_le_T`, `abs_S_le_T` : `S_b(q) ≤ |S_b(q)| ≤ T(b)`.
* `exists_S_gt` : for every `X` and `ε > 0` some `q ≥ X` has `S_b(q) > T(b) − ε`.
* `isLUB_S`, `sSup_S` : `sup_{q ≥ X} S_b(q) = T(b)`.

Route: the source uses Kronecker's theorem and linear independence of the `log p`. Here only homogeneous
alignment is used (`exists_aligned`: some multiple `k L` puts every `k L log n`, `n < N`, within `δ` of `0`
mod `2π`), obtained from compactness of the torus `(ℝ/2πℤ)^N` (pigeonhole on a convergent subsequence).
No linear independence is needed. This route is the formalizer's choice, not the source's.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Finset
open scoped Real ArithmeticFunction
open GaussianTest FleetPrimeSideConsequences FleetPrimeOnlyRH

namespace FleetKroneckerSharpness

/-- Coefficient `2 Λ(n) n^{-1/2} e^{-b log² n}`. -/
def coeff (b : ℝ) (n : ℕ) : ℝ :=
  2 * Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ) * Real.exp (-b * Real.log n ^ 2)

/-- `S_b(q) = Σ_n 2 Λ(n) n^{-1/2} e^{-b log² n} cos(q log n)`. -/
def S (b q : ℝ) : ℝ := ∑' n : ℕ, coeff b n * Real.cos (q * Real.log n)

/-- `T(b) = S_b(0) = Σ_n 2 Λ(n) n^{-1/2} e^{-b log² n}`. -/
def T (b : ℝ) : ℝ := S b 0

lemma coeff_nonneg (b : ℝ) (n : ℕ) : 0 ≤ coeff b n := by
  unfold coeff
  have := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  positivity

lemma coeff_eq (b : ℝ) (n : ℕ) : coeff b n = |Λ n| * vW b n := by
  rw [_root_.abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  unfold coeff vW
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Real.rpow_def_of_pos hn']
    ring_nf

/-- **Summability** of the coefficients. -/
theorem summable_coeff {b : ℝ} (hb : 0 < b) : Summable (coeff b) := by
  have h := summable_c_vW (c := fun n => Λ n) (fun n => le_of_eq (_root_.abs_of_nonneg
    ArithmeticFunction.vonMangoldt_nonneg)) hb
  refine h.congr fun n => ?_
  rw [coeff_eq]

/-- **Summability** of the cosine series `S_b(q)`. -/
theorem summable_S {b : ℝ} (hb : 0 < b) (q : ℝ) :
    Summable (fun n : ℕ => coeff b n * Real.cos (q * Real.log n)) := by
  refine Summable.of_norm_bounded (summable_coeff hb) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, _root_.abs_of_nonneg (coeff_nonneg b n)]
  exact mul_le_of_le_one_right (coeff_nonneg b n) (Real.abs_cos_le_one _)

lemma T_eq (b : ℝ) : T b = ∑' n : ℕ, coeff b n := by
  unfold T S; simp

/-- **The trivial bound** `S_b(q) ≤ T(b)`. -/
theorem S_le_T {b : ℝ} (hb : 0 < b) (q : ℝ) : S b q ≤ T b := by
  rw [T_eq]
  exact Summable.tsum_le_tsum (fun n => mul_le_of_le_one_right (coeff_nonneg b n) (Real.cos_le_one _))
    (summable_S hb q) (summable_coeff hb)

/-- `|S_b(q)| ≤ T(b)`. -/
theorem abs_S_le_T {b : ℝ} (hb : 0 < b) (q : ℝ) : |S b q| ≤ T b := by
  rw [T_eq]
  refine (norm_tsum_le_tsum_norm ((summable_S hb q).norm)).trans ?_
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_S hb q).norm (summable_coeff hb)
  rw [Real.norm_eq_abs, abs_mul, _root_.abs_of_nonneg (coeff_nonneg b n)]
  exact mul_le_of_le_one_right (coeff_nonneg b n) (Real.abs_cos_le_one _)

/-- **Simultaneous homogeneous alignment** (Dirichlet/pigeonhole form, via compactness of the torus):
for every finite `N`, every `δ > 0` and every `L`, some multiple `k ≥ 1` brings every `k L log n`,
`n < N`, within `δ` of `0` in `Real.Angle` (`ℝ/2πℤ`). -/
theorem exists_aligned (N : ℕ) (L : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ k : ℕ, 1 ≤ k ∧ ‖(fun i : Fin N => (((k : ℝ) * L * Real.log (i : ℕ) : ℝ) : Real.Angle))‖ < δ := by
  have : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩
  have : CompactSpace Real.Angle := AddCircle.compactSpace (2 * π)
  set P : ℕ → (Fin N → Real.Angle) :=
    fun j i => (((j : ℝ) * L * Real.log (i : ℕ) : ℝ) : Real.Angle) with hP
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_univ (X := Fin N → Real.Angle)).tendsto_subseq
    (x := P) (fun _ => Set.mem_univ _)
  have hev := (Metric.tendsto_atTop.1 hlim) (δ / 2) (by linarith)
  obtain ⟨m, hm⟩ := hev
  have h1 := hm m le_rfl
  have h2 := hm (m + 1) (Nat.le_succ m)
  have hlt : φ m < φ (m + 1) := hφ (Nat.lt_succ_self m)
  refine ⟨φ (m + 1) - φ m, by omega, ?_⟩
  have hsub : (fun i : Fin N => ((((φ (m + 1) - φ m : ℕ) : ℝ) * L * Real.log (i : ℕ) : ℝ) : Real.Angle))
      = P (φ (m + 1)) - P (φ m) := by
    funext i
    simp only [hP, Pi.sub_apply]
    rw [← Real.Angle.coe_sub, Nat.cast_sub hlt.le]
    congr 1; ring
  rw [hsub, ← dist_eq_norm]
  calc dist (P (φ (m + 1))) (P (φ m)) ≤ dist (P (φ (m + 1))) a + dist (P (φ m)) a :=
        dist_triangle_right _ _ _
    _ < δ / 2 + δ / 2 := add_lt_add h2 h1
    _ = δ := by ring

/-- **Kronecker sharpness** (`CANCELLATION_ANALYSIS.md` §1): for every `b > 0`, every `X` and every
`ε > 0` there is `q ≥ X` with `S_b(q) > T(b) − ε`. -/
theorem exists_S_gt {b : ℝ} (hb : 0 < b) (X : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℝ, X ≤ q ∧ T b - ε < S b q := by
  have hsum := summable_coeff hb
  -- tail of the coefficients below ε/4
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 (tendsto_sum_nat_add (coeff b))) (ε / 4) (by linarith)
  have hNt := hN N le_rfl
  rw [Real.dist_eq, sub_zero] at hNt
  set tail := ∑' k : ℕ, coeff b (k + N) with htail
  have htail0 : 0 ≤ tail := tsum_nonneg fun k => coeff_nonneg b (k + N)
  rw [abs_of_nonneg htail0] at hNt
  -- the head as a continuous function on the torus
  set Φ : (Fin N → Real.Angle) → ℝ := fun x => ∑ i : Fin N, coeff b i * Real.Angle.cos (x i) with hΦ
  have hΦc : Continuous Φ := by
    refine continuous_finsetSum _ fun i _ => continuous_const.mul ?_
    exact Real.Angle.continuous_cos.comp (continuous_apply i)
  obtain ⟨δ, hδ, hδΦ⟩ := Metric.continuous_iff.1 hΦc 0 (ε / 4) (by linarith)
  obtain ⟨k, hk, hkδ⟩ := exists_aligned N (max X 0) hδ
  refine ⟨k * max X 0, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [le_max_left X 0, le_max_right X 0]
  · have hd := hδΦ _ (by rw [dist_zero_right]; exact hkδ)
    rw [Real.dist_eq] at hd
    have hΦ0 : Φ 0 = ∑ n ∈ range N, coeff b n := by
      simp only [hΦ, Pi.zero_apply, Real.Angle.cos_zero, mul_one]
      exact Fin.sum_univ_eq_sum_range (coeff b) N
    have hΦk : Φ (fun i : Fin N => (((k : ℝ) * max X 0 * Real.log (i : ℕ) : ℝ) : Real.Angle))
        = ∑ n ∈ range N, coeff b n * Real.cos ((k * max X 0) * Real.log n) := by
      simp only [hΦ, Real.Angle.cos_coe]
      exact Fin.sum_univ_eq_sum_range (fun n => coeff b n * Real.cos ((k * max X 0) * Real.log n)) N
    rw [hΦ0, hΦk] at hd
    have hT : T b = ∑ n ∈ range N, coeff b n + tail := by
      rw [T_eq, htail]; exact (hsum.sum_add_tsum_nat_add N).symm
    have hS : S b (k * max X 0) = ∑ n ∈ range N, coeff b n * Real.cos ((k * max X 0) * Real.log n)
        + ∑' j : ℕ, coeff b (j + N) * Real.cos ((k * max X 0) * Real.log ((j + N : ℕ) : ℝ)) := by
      unfold S; exact ((summable_S hb _).sum_add_tsum_nat_add N).symm
    have htailS : -tail ≤ ∑' j : ℕ, coeff b (j + N) * Real.cos ((k * max X 0) * Real.log ((j + N : ℕ) : ℝ)) := by
      have hs2 : Summable (fun j : ℕ => coeff b (j + N)) := (summable_nat_add_iff N).2 hsum
      have hs1 : Summable (fun j : ℕ => coeff b (j + N) * Real.cos ((k * max X 0) * Real.log ((j + N : ℕ) : ℝ))) :=
        (summable_nat_add_iff N).2 (summable_S hb (k * max X 0))
      rw [htail, ← tsum_neg]
      exact Summable.tsum_le_tsum (fun j => by
        have := coeff_nonneg b (j + N)
        nlinarith [Real.neg_one_le_cos ((k * max X 0) * Real.log ((j + N : ℕ) : ℝ))]) hs2.neg hs1
    have := (abs_lt.1 hd).1
    linarith

/-- **`sup_{q ≥ X} S_b(q) = T(b)`**: `T(b)` is an upper bound on `[X, ∞)` and the least one. -/
theorem isLUB_S {b : ℝ} (hb : 0 < b) (X : ℝ) : IsLUB (S b '' Set.Ici X) (T b) := by
  refine ⟨?_, fun y hy => ?_⟩
  · rintro _ ⟨q, -, rfl⟩; exact S_le_T hb q
  · by_contra h
    push Not at h
    obtain ⟨q, hq, hlt⟩ := exists_S_gt hb X (sub_pos.2 h)
    have := hy ⟨q, hq, rfl⟩
    linarith

theorem sSup_S {b : ℝ} (hb : 0 < b) (X : ℝ) : sSup (S b '' Set.Ici X) = T b :=
  (isLUB_S hb X).csSup_eq ⟨S b X, X, Set.self_mem_Ici, rfl⟩

/-! ## Agreement with the existing two-sided von Mangoldt sum `primeSumSym` -/

lemma term_vonMangoldt_eq_real (b q : ℝ) (n : ℕ) :
    term (fun n => Λ n) b q n = ((coeff b n * Real.cos (q * Real.log n) : ℝ) : ℂ) := by
  unfold term coeff
  rw [FleetPrimeTarget.gauss_add_neg]
  have hc : (((n : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) = (n : ℂ) ^ (-(1 / 2) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]; push_cast; ring_nf
  push_cast
  rw [hc]; ring

/-- `primeSumSym b q` (the two-sided von Mangoldt sum of `FleetPrimeSideConsequences`) is `S_b(q)`. -/
theorem primeSumSym_eq_S {b : ℝ} (hb : 0 < b) (q : ℝ) : primeSumSym b q = (S b q : ℂ) := by
  rw [primeSumSym_eq hb, S, Complex.ofReal_tsum]
  congr 1; funext n; exact term_vonMangoldt_eq_real b q n

/-- `Re primeSumSym b q ≤ Re primeSumSym b 0`. -/
theorem primeSumSym_re_le {b : ℝ} (hb : 0 < b) (q : ℝ) :
    (primeSumSym b q).re ≤ (primeSumSym b 0).re := by
  rw [primeSumSym_eq_S hb, primeSumSym_eq_S hb, Complex.ofReal_re, Complex.ofReal_re]
  exact S_le_T hb q

/-- For every `X` and `ε > 0` some `q ≥ X` has `Re primeSumSym b q > Re primeSumSym b 0 − ε`. -/
theorem exists_primeSumSym_re_gt {b : ℝ} (hb : 0 < b) (X : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℝ, X ≤ q ∧ (primeSumSym b 0).re - ε < (primeSumSym b q).re := by
  obtain ⟨q, hq, h⟩ := exists_S_gt hb X hε
  refine ⟨q, hq, ?_⟩
  rw [primeSumSym_eq_S hb, primeSumSym_eq_S hb, Complex.ofReal_re, Complex.ofReal_re]
  exact h

end FleetKroneckerSharpness
