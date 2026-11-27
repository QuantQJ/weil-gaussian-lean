/-
Copyright 2026 James C. Kerr (QuantQJ). Apache-2.0.
-/
import Kerr.NumberTheory.PowerfulNumbers.PsiSum

/-!
# `ψ`-sums of `C n^{−p}` over a dyadic block

New file (written for this repo). For `C > 0`, `p > 0`, `N ≥ 1`, `N ≤ N₁ ≤ N₂ ≤ 2N`, with
`λ = C p (p+1) (2N+2)^{−p−2}`:

* `block_exp_sum`: `‖∑ e(h C n^{−p})‖ ≤ √h (4L/√λ + 4N√λ) + (8/√λ)/√h`, `L = C p N^{−p−1}`
  (second differences `≥ hλ` by the mean value theorem; `vdc_second_derivative` with `δ = √(hλ)`);
* `block_psi`: `|∑_{N₁ ≤ n ≤ N₂} ψ(C n^{−p})| ≤ 6 N^{3/7} A^{4/7} + 3B`
  (`psi_sum_bound` with `Δ = (A/N)^{4/7}`).
-/

noncomputable section
open Finset Real

namespace Kerr.PowerfulNumbers

/-- Mean value bounds: `q (b+1)^{−q−1} ≤ b^{−q} − (b+1)^{−q} ≤ q b^{−q−1}`. -/
lemma rpow_neg_diff_bounds {q b : ℝ} (hq : 0 < q) (hb : 0 < b) :
    q * (b + 1) ^ (-q - 1) ≤ b ^ (-q) - (b + 1) ^ (-q) ∧
      b ^ (-q) - (b + 1) ^ (-q) ≤ q * b ^ (-q - 1) := by
  have hd : ∀ x ∈ Set.Ioo b (b + 1), HasDerivAt (fun u : ℝ => u ^ (-q)) (-q * x ^ (-q - 1)) x :=
    fun x hx => Real.hasDerivAt_rpow_const (Or.inl (by linarith [hx.1]))
  have hc : ContinuousOn (fun u : ℝ => u ^ (-q)) (Set.Icc b (b + 1)) := fun x hx =>
    (Real.hasDerivAt_rpow_const (p := -q) (Or.inl (by linarith [hx.1] : x ≠ 0))).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope _ _ (by linarith : b < b + 1) hc hd
  rw [show b + 1 - b = 1 by ring, div_one] at hξe
  have h1 : b ^ (-q) - (b + 1) ^ (-q) = q * ξ ^ (-q - 1) := by linarith
  rw [h1]
  constructor
  · exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by linarith [hξ.1]) hξ.2.le (by linarith)) hq.le
  · exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hb hξ.1.le (by linarith)) hq.le

/-- Second difference: `(a+2)^{−p} − 2(a+1)^{−p} + a^{−p} ≥ p(p+1)(a+2)^{−p−2}`. -/
lemma rpow_neg_second_diff {p a : ℝ} (hp : 0 < p) (ha : 0 < a) :
    p * (p + 1) * (a + 2) ^ (-p - 2) ≤ (a + 2) ^ (-p) - 2 * (a + 1) ^ (-p) + a ^ (-p) := by
  set φ : ℝ → ℝ := fun u => (u + 1) ^ (-p) - u ^ (-p) with hφ
  have hd : ∀ x ∈ Set.Ioo a (a + 1), HasDerivAt φ
      (-p * (x + 1) ^ (-p - 1) * 1 - -p * x ^ (-p - 1)) x := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have h1 := (Real.hasDerivAt_rpow_const (p := -p) (Or.inl (by linarith : x + 1 ≠ 0))).comp x
      ((hasDerivAt_id x).add_const 1)
    exact h1.sub (Real.hasDerivAt_rpow_const (Or.inl hx0.ne'))
  have hc : ContinuousOn φ (Set.Icc a (a + 1)) := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have h1 := (Real.hasDerivAt_rpow_const (p := -p) (Or.inl (by linarith : x + 1 ≠ 0))).comp x
      ((hasDerivAt_id x).add_const 1)
    exact (h1.sub (Real.hasDerivAt_rpow_const (Or.inl hx0.ne'))).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope φ _ (by linarith : a < a + 1) hc hd
  rw [show a + 1 - a = 1 by ring, div_one] at hξe
  simp only [hφ] at hξe
  have hξ0 : 0 < ξ := by linarith [hξ.1]
  obtain ⟨hlo, -⟩ := rpow_neg_diff_bounds (q := p + 1) (by linarith) hξ0
  have e1 : -(p + 1) = -p - 1 := by ring
  have e2 : -p - 1 - 1 = -p - 2 := by ring
  rw [e1] at hlo
  rw [e2] at hlo
  have hmono : (a + 2) ^ (-p - 2) ≤ (ξ + 1) ^ (-p - 2) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith [hξ.2]) (by linarith)
  have e3 : a + 1 + 1 = a + 2 := by ring
  rw [e3] at hξe
  nlinarith [mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ p * (p + 1))]

/-- `λ = C p (p+1) (2N+2)^{−p−2}`. -/
def blam (C p : ℝ) (N : ℕ) : ℝ := C * p * (p + 1) * (2 * (N : ℝ) + 2) ^ (-p - 2)

/-- `A = 4 L/√λ + 4 N √λ`, `L = C p N^{−p−1}`. -/
def bA (C p : ℝ) (N : ℕ) : ℝ :=
  4 * (C * p * (N : ℝ) ^ (-p - 1)) / Real.sqrt (blam C p N) + 4 * N * Real.sqrt (blam C p N)

lemma blam_pos {C p : ℝ} (hC : 0 < C) (hp : 0 < p) (N : ℕ) : 0 < blam C p N := by
  unfold blam; positivity

lemma bA_pos {C p : ℝ} (hC : 0 < C) (hp : 0 < p) {N : ℕ} (hN : 1 ≤ N) : 0 < bA C p N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have := blam_pos hC hp N
  unfold bA; positivity

/-- **Exponential sums over a block.** -/
theorem block_exp_sum {C p : ℝ} (hC : 0 < C) (hp : 0 < p) {N N₁ N₂ : ℕ} (hN : 1 ≤ N)
    (h1 : N ≤ N₁) (h12 : N₁ ≤ N₂) (h2 : N₂ ≤ 2 * N) {h : ℕ} (hh : 1 ≤ h) :
    ‖∑ n ∈ Icc N₁ N₂, ee (h * (C * (n : ℝ) ^ (-p)))‖ ≤
      bA C p N * Real.sqrt h + 8 / Real.sqrt (blam C p N) / Real.sqrt h := by
  set lam := blam C p N with hlam
  set L := C * p * (N : ℝ) ^ (-p - 1) with hL
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlam0 : 0 < lam := blam_pos hC hp N
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hL0 : 0 ≤ L := by positivity
  set F : ℕ → ℝ := fun n => h * (C * (n : ℝ) ^ (-p)) with hF
  set lh := (h : ℝ) * lam with hlh
  have hlh0 : 0 < lh := by positivity
  have hstep : ∀ n, N₁ ≤ n → n < N₂ → lh ≤ (F (n + 2) - F (n + 1)) - (F (n + 1) - F n) := by
    intro n hn1 hn2
    have hn0 : (0 : ℝ) < n := by
      have : 1 ≤ n := hN.trans (h1.trans hn1); exact_mod_cast this
    have hsd := rpow_neg_second_diff hp hn0
    have hn2' : (n : ℝ) + 1 ≤ N₂ := by exact_mod_cast hn2
    have h2' : (N₂ : ℝ) ≤ 2 * N := by exact_mod_cast h2
    have hmono : (2 * (N : ℝ) + 2) ^ (-p - 2) ≤ ((n : ℝ) + 2) ^ (-p - 2) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    simp only [hF]
    push_cast
    have e : (h : ℝ) * (C * ((n : ℝ) + 2) ^ (-p)) - h * (C * ((n : ℝ) + 1) ^ (-p)) -
        (h * (C * ((n : ℝ) + 1) ^ (-p)) - h * (C * (n : ℝ) ^ (-p))) =
        h * C * (((n : ℝ) + 2) ^ (-p) - 2 * ((n : ℝ) + 1) ^ (-p) + (n : ℝ) ^ (-p)) := by ring
    rw [e]
    have hhC : 0 ≤ (h : ℝ) * C := by positivity
    calc lh = h * C * (p * (p + 1) * (2 * (N : ℝ) + 2) ^ (-p - 2)) := by
          simp only [hlh, hlam, blam]; ring
      _ ≤ h * C * (p * (p + 1) * ((n : ℝ) + 2) ^ (-p - 2)) := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left hsd hhC
  have hrange : (F (N₂ + 1) - F N₂) - (F (N₁ + 1) - F N₁) ≤ h * L := by
    have hN₁ : (0 : ℝ) < N₁ := by have : 1 ≤ N₁ := hN.trans h1; exact_mod_cast this
    have hN₂ : (0 : ℝ) < N₂ := by have : 1 ≤ N₂ := hN.trans (h1.trans h12); exact_mod_cast this
    obtain ⟨-, hup⟩ := rpow_neg_diff_bounds hp hN₁
    obtain ⟨hlo2, -⟩ := rpow_neg_diff_bounds hp hN₂
    have hpow : (N₁ : ℝ) ^ (-p - 1) ≤ (N : ℝ) ^ (-p - 1) :=
      Real.rpow_le_rpow_of_nonpos hN0 (by exact_mod_cast h1) (by linarith)
    have hlo2' : 0 ≤ (N₂ : ℝ) ^ (-p) - ((N₂ : ℝ) + 1) ^ (-p) :=
      le_trans (by positivity) hlo2
    simp only [hF, hL]
    push_cast
    have hhC : 0 ≤ (h : ℝ) * C := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hup hhC, mul_le_mul_of_nonneg_left hpow
      (by positivity : (0 : ℝ) ≤ h * C * p), mul_nonneg hhC hlo2']
  have hsqrt : Real.sqrt lh = Real.sqrt h * Real.sqrt lam := by
    rw [hlh, Real.sqrt_mul hh0.le]
  have hsh0 : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh0
  have hsl0 : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam0
  have hA : bA C p N = 4 * L / Real.sqrt lam + 4 * N * Real.sqrt lam := by
    simp only [bA, hL, hlam]
  rw [hA]
  rcases le_or_gt lh (1 / 4) with hsmall | hlarge
  · set δ := Real.sqrt lh with hδ
    have hδ0 : 0 < δ := Real.sqrt_pos.mpr hlh0
    have hδ2 : δ ^ 2 = lh := Real.sq_sqrt hlh0.le
    have hδ1 : δ ≤ 1 / 2 := by
      rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hsmall
    have hv := vdc_second_derivative h12 hlh0 hδ0 hstep
    have hfac : 2 * δ / lh + 2 + 1 / δ ≤ 4 / δ := by
      rw [← hδ2]
      have : 2 ≤ 1 / δ := by rw [le_div_iff₀ hδ0]; linarith
      have e : 2 * δ / δ ^ 2 = 2 / δ := by field_simp
      rw [e]
      have e2 : (4 : ℝ) / δ = 2 / δ + 1 / δ + 1 / δ := by ring
      linarith
    have hfac0 : 0 ≤ 2 * δ / lh + 2 + 1 / δ := by positivity
    calc ‖∑ n ∈ Icc N₁ N₂, ee (h * (C * (n : ℝ) ^ (-p)))‖
        ≤ ((F (N₂ + 1) - F N₂) - (F (N₁ + 1) - F N₁) + 2) * (2 * δ / lh + 2 + 1 / δ) := hv
      _ ≤ (h * L + 2) * (2 * δ / lh + 2 + 1 / δ) := by gcongr
      _ ≤ (h * L + 2) * (4 / δ) := by gcongr
      _ = Real.sqrt h * (4 * L / Real.sqrt lam) + 8 / Real.sqrt lam / Real.sqrt h := by
          rw [hsqrt]
          field_simp
          simp only [Real.sq_sqrt hh0.le]
          ring
      _ ≤ (4 * L / Real.sqrt lam + 4 * N * Real.sqrt lam) * Real.sqrt h +
          8 / Real.sqrt lam / Real.sqrt h := by
          have : 0 ≤ 4 * N * Real.sqrt lam * Real.sqrt h := by positivity
          nlinarith
  · have hcard : ‖∑ n ∈ Icc N₁ N₂, ee (h * (C * (n : ℝ) ^ (-p)))‖ ≤ 2 * N := by
      refine (norm_sum_le _ _).trans ?_
      simp only [norm_ee, sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
      have : N₂ + 1 - N₁ ≤ 2 * N := by omega
      exact_mod_cast this
    have hsl : 1 / 2 < Real.sqrt lh := by
      rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) hlarge
    rw [hsqrt] at hsl
    have h8 : 0 ≤ 8 / Real.sqrt lam / Real.sqrt h := by positivity
    have h4 : 0 ≤ 4 * L / Real.sqrt lam * Real.sqrt h := by positivity
    nlinarith

/-- **`ψ`-sums over a block.** `|∑_{N₁ ≤ n ≤ N₂} ψ(C n^{−p})| ≤ 6 N^{3/7} A^{4/7} + 3B`. -/
theorem block_psi {C p : ℝ} (hC : 0 < C) (hp : 0 < p) {N N₁ N₂ : ℕ} (hN : 1 ≤ N)
    (h1 : N ≤ N₁) (h12 : N₁ ≤ N₂) (h2 : N₂ ≤ 2 * N) :
    |∑ n ∈ Icc N₁ N₂, psi (C * (n : ℝ) ^ (-p))| ≤
      6 * (N : ℝ) ^ (3 / 7 : ℝ) * bA C p N ^ (4 / 7 : ℝ) + 3 * (8 / Real.sqrt (blam C p N)) := by
  set A := bA C p N with hAdef
  set B := 8 / Real.sqrt (blam C p N) with hB
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hA0 : 0 < A := bA_pos hC hp hN
  have hB0 : 0 ≤ B := by positivity
  have hcard : ((Icc N₁ N₂).card : ℝ) ≤ N + 1 := by
    rw [Nat.card_Icc]; have : N₂ + 1 - N₁ ≤ N + 1 := by omega
    exact_mod_cast this
  have hNsplit : (N : ℝ) = (N : ℝ) ^ (3 / 7 : ℝ) * (N : ℝ) ^ (4 / 7 : ℝ) := by
    rw [← Real.rpow_add hN0]; norm_num
  have hP0 : 0 ≤ (N : ℝ) ^ (3 / 7 : ℝ) * A ^ (4 / 7 : ℝ) := by positivity
  rcases le_or_gt A N with hAN | hAN
  · set Δ := (A / N) ^ (4 / 7 : ℝ) with hΔ
    have hΔ0 : 0 < Δ := by positivity
    have hΔ1 : Δ ≤ 1 := Real.rpow_le_one (by positivity) (by rw [div_le_one hN0]; exact hAN)
      (by norm_num)
    have hS : ∀ h : ℕ, 1 ≤ h → ‖∑ j ∈ Icc N₁ N₂, ee (h * (C * (j : ℝ) ^ (-p)))‖ ≤
        A * Real.sqrt h + B / Real.sqrt h := fun h hh => block_exp_sum hC hp hN h1 h12 h2 hh
    have hpsi := psi_sum_bound (fun j => C * (j : ℝ) ^ (-p)) (Icc N₁ N₂) hΔ0 hΔ1 hA0.le hB0 hS
    have hNΔ : (N : ℝ) * Δ = (N : ℝ) ^ (3 / 7 : ℝ) * A ^ (4 / 7 : ℝ) := by
      have h4 : (N : ℝ) ^ (4 / 7 : ℝ) ≠ 0 := by positivity
      calc (N : ℝ) * Δ = (N : ℝ) * (A ^ (4 / 7 : ℝ) / (N : ℝ) ^ (4 / 7 : ℝ)) := by
            rw [hΔ, Real.div_rpow hA0.le hN0.le]
        _ = ((N : ℝ) ^ (3 / 7 : ℝ) * (N : ℝ) ^ (4 / 7 : ℝ)) *
              (A ^ (4 / 7 : ℝ) / (N : ℝ) ^ (4 / 7 : ℝ)) := by rw [← hNsplit]
        _ = (N : ℝ) ^ (3 / 7 : ℝ) * A ^ (4 / 7 : ℝ) := by field_simp
    have hAs : A = A ^ (3 / 7 : ℝ) * A ^ (4 / 7 : ℝ) := by
      rw [← Real.rpow_add hA0]; norm_num
    have hAΔ : A * Δ ^ (-(3 / 4 : ℝ)) = (N : ℝ) ^ (3 / 7 : ℝ) * A ^ (4 / 7 : ℝ) := by
      have e1 : Δ ^ (-(3 / 4 : ℝ)) = (N : ℝ) ^ (3 / 7 : ℝ) / A ^ (3 / 7 : ℝ) := by
        rw [hΔ, ← Real.rpow_mul (by positivity),
          show (4 / 7 : ℝ) * (-(3 / 4)) = -(3 / 7) by norm_num,
          Real.rpow_neg (by positivity), Real.div_rpow hA0.le hN0.le, inv_div]
      have h3 : A ^ (3 / 7 : ℝ) ≠ 0 := by positivity
      rw [e1]
      calc A * ((N : ℝ) ^ (3 / 7 : ℝ) / A ^ (3 / 7 : ℝ))
          = (A ^ (3 / 7 : ℝ) * A ^ (4 / 7 : ℝ)) * ((N : ℝ) ^ (3 / 7 : ℝ) / A ^ (3 / 7 : ℝ)) := by
            rw [← hAs]
        _ = (N : ℝ) ^ (3 / 7 : ℝ) * A ^ (4 / 7 : ℝ) := by field_simp
    have hcΔ : ((Icc N₁ N₂).card : ℝ) * Δ / 2 ≤ (N : ℝ) * Δ := by
      have : ((Icc N₁ N₂).card : ℝ) * Δ ≤ (N + 1) * Δ := mul_le_mul_of_nonneg_right hcard hΔ0.le
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith
    calc _ ≤ ((Icc N₁ N₂).card : ℝ) * Δ / 2 + (5 * A * Δ ^ (-(3 / 4 : ℝ)) + 3 * B) := hpsi
      _ ≤ (N : ℝ) * Δ + (5 * (A * Δ ^ (-(3 / 4 : ℝ))) + 3 * B) := by
          have := hcΔ; nlinarith
      _ = 6 * (N : ℝ) ^ (3 / 7 : ℝ) * A ^ (4 / 7 : ℝ) + 3 * B := by rw [hNΔ, hAΔ]; ring
  · have habs : ∀ t : ℝ, |psi t| ≤ 1 / 2 := by
      intro t; rw [psi, abs_le]
      constructor <;> linarith [Int.fract_nonneg t, Int.fract_lt_one t]
    have h1' : |∑ n ∈ Icc N₁ N₂, psi (C * (n : ℝ) ^ (-p))| ≤ (N : ℝ) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      refine (sum_le_sum (fun n _ => habs _)).trans ?_
      rw [sum_const, nsmul_eq_mul]
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith
    have h2' : (N : ℝ) ≤ (N : ℝ) ^ (3 / 7 : ℝ) * A ^ (4 / 7 : ℝ) := by
      conv_lhs => rw [hNsplit]
      gcongr
    nlinarith

/-- **Block bound in terms of `μ = C N^{−p−2}`.** There are `K₁, K₂` (depending on `p`) with
`|∑_{N₁ ≤ n ≤ N₂} ψ(C n^{−p})| ≤ K₁ N μ^{2/7} + K₂ μ^{−1/2}`. -/
theorem block_psi_mu {p : ℝ} (hp : 0 < p) : ∃ K₁ K₂ : ℝ, 0 ≤ K₁ ∧ 0 ≤ K₂ ∧
    ∀ C : ℝ, 0 < C → ∀ N N₁ N₂ : ℕ, 1 ≤ N → N ≤ N₁ → N₁ ≤ N₂ → N₂ ≤ 2 * N →
      |∑ n ∈ Icc N₁ N₂, psi (C * (n : ℝ) ^ (-p))| ≤
        K₁ * N * (C * (N : ℝ) ^ (-p - 2)) ^ (2 / 7 : ℝ) +
          K₂ * (C * (N : ℝ) ^ (-p - 2)) ^ (-(1 / 2 : ℝ)) := by
  set cp := 4 * (4 : ℝ) ^ (p + 2) / (p + 1) + 4 with hcp
  have hcp0 : 0 < cp := by positivity
  set q := p * (p + 1) with hq
  have hq0 : 0 < q := by positivity
  refine ⟨6 * cp ^ (4 / 7 : ℝ) * q ^ (2 / 7 : ℝ), 24 * ((4 : ℝ) ^ (-p - 2) * q) ^ (-(1 / 2 : ℝ)),
    by positivity, by positivity, ?_⟩
  intro C hC N N₁ N₂ hN h1 h12 h2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set lam := blam C p N with hlam
  have hlam0 : 0 < lam := blam_pos hC hp N
  set μ := C * (N : ℝ) ^ (-p - 2) with hμ
  have hμ0 : 0 < μ := by positivity
  -- two-sided bounds for `λ`
  have hlam_up : lam ≤ q * μ := by
    simp only [hlam, blam, hμ, hq]
    have : (2 * (N : ℝ) + 2) ^ (-p - 2) ≤ (N : ℝ) ^ (-p - 2) :=
      Real.rpow_le_rpow_of_nonpos hN0 (by linarith) (by linarith)
    have hc : 0 ≤ C * p * (p + 1) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hc]
  have hlam_lo : (4 : ℝ) ^ (-p - 2) * q * μ ≤ lam := by
    simp only [hlam, blam, hμ, hq]
    have : (4 * (N : ℝ)) ^ (-p - 2) ≤ (2 * (N : ℝ) + 2) ^ (-p - 2) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    rw [Real.mul_rpow (by norm_num) hN0.le] at this
    have hc : 0 ≤ C * p * (p + 1) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hc]
  -- `A ≤ cp N √λ`
  have hL : C * p * (N : ℝ) ^ (-p - 1) ≤ 4 ^ (p + 2) / (p + 1) * N * lam := by
    simp only [hlam, blam]
    have h4 : (4 * (N : ℝ)) ^ (-p - 2) ≤ (2 * (N : ℝ) + 2) ^ (-p - 2) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    rw [Real.mul_rpow (by norm_num) hN0.le] at h4
    have e1 : (N : ℝ) ^ (-p - 1) = N * (N : ℝ) ^ (-p - 2) := by
      rw [show (-p - 1) = 1 + (-p - 2) by ring, Real.rpow_add hN0, Real.rpow_one]
    have e2 : (4 : ℝ) ^ (p + 2) * (4 : ℝ) ^ (-p - 2) = 1 := by
      rw [← Real.rpow_add (by norm_num)]; ring_nf; exact Real.rpow_zero 4
    rw [e1]
    have hp1 : 0 < p + 1 := by linarith
    have key : C * p * (N * (N : ℝ) ^ (-p - 2)) =
        4 ^ (p + 2) / (p + 1) * N * (C * p * (p + 1) * ((4 : ℝ) ^ (-p - 2) * (N : ℝ) ^ (-p - 2))) := by
      field_simp
      linarith [e2]
    rw [key]
    gcongr
  have hsl0 : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam0
  have hA : bA C p N ≤ cp * N * Real.sqrt lam := by
    have hms := Real.mul_self_sqrt hlam0.le
    have h1' : 4 * (C * p * (N : ℝ) ^ (-p - 1)) / Real.sqrt lam ≤
        4 * (4 ^ (p + 2) / (p + 1)) * N * Real.sqrt lam := by
      rw [div_le_iff₀ hsl0]
      calc 4 * (C * p * (N : ℝ) ^ (-p - 1)) ≤ 4 * (4 ^ (p + 2) / (p + 1) * N * lam) := by gcongr
        _ = 4 * (4 ^ (p + 2) / (p + 1)) * N * Real.sqrt lam * Real.sqrt lam := by
            linear_combination (-(4 * (4 ^ (p + 2) / (p + 1)) * N)) * hms
    calc bA C p N = 4 * (C * p * (N : ℝ) ^ (-p - 1)) / Real.sqrt lam + 4 * N * Real.sqrt lam := rfl
      _ ≤ 4 * (4 ^ (p + 2) / (p + 1)) * N * Real.sqrt lam + 4 * N * Real.sqrt lam := by gcongr
      _ = cp * N * Real.sqrt lam := by rw [hcp]; ring
  have hb := block_psi hC hp hN h1 h12 h2
  have hA0 := bA_pos hC hp hN
  -- `N^{3/7} A^{4/7} ≤ cp^{4/7} N λ^{2/7}`
  have hA47 : (N : ℝ) ^ (3 / 7 : ℝ) * bA C p N ^ (4 / 7 : ℝ) ≤
      cp ^ (4 / 7 : ℝ) * N * lam ^ (2 / 7 : ℝ) := by
    have h1' : bA C p N ^ (4 / 7 : ℝ) ≤ (cp * N * Real.sqrt lam) ^ (4 / 7 : ℝ) :=
      Real.rpow_le_rpow hA0.le hA (by norm_num)
    have e : (cp * N * Real.sqrt lam) ^ (4 / 7 : ℝ) =
        cp ^ (4 / 7 : ℝ) * (N : ℝ) ^ (4 / 7 : ℝ) * lam ^ (2 / 7 : ℝ) := by
      rw [Real.mul_rpow (by positivity) hsl0.le, Real.mul_rpow hcp0.le hN0.le,
        Real.sqrt_eq_rpow, ← Real.rpow_mul hlam0.le]
      norm_num
    rw [e] at h1'
    have hNs : (N : ℝ) = (N : ℝ) ^ (3 / 7 : ℝ) * (N : ℝ) ^ (4 / 7 : ℝ) := by
      rw [← Real.rpow_add hN0]; norm_num
    calc (N : ℝ) ^ (3 / 7 : ℝ) * bA C p N ^ (4 / 7 : ℝ)
        ≤ (N : ℝ) ^ (3 / 7 : ℝ) * (cp ^ (4 / 7 : ℝ) * (N : ℝ) ^ (4 / 7 : ℝ) * lam ^ (2 / 7 : ℝ)) := by
          gcongr
      _ = cp ^ (4 / 7 : ℝ) * ((N : ℝ) ^ (3 / 7 : ℝ) * (N : ℝ) ^ (4 / 7 : ℝ)) * lam ^ (2 / 7 : ℝ) := by
          ring
      _ = cp ^ (4 / 7 : ℝ) * N * lam ^ (2 / 7 : ℝ) := by rw [← hNs]
  have hl27 : lam ^ (2 / 7 : ℝ) ≤ q ^ (2 / 7 : ℝ) * μ ^ (2 / 7 : ℝ) := by
    rw [← Real.mul_rpow hq0.le hμ0.le]
    exact Real.rpow_le_rpow hlam0.le hlam_up (by norm_num)
  have hl12 : 8 / Real.sqrt lam ≤ 8 * ((4 : ℝ) ^ (-p - 2) * q) ^ (-(1 / 2 : ℝ)) * μ ^ (-(1 / 2 : ℝ)) := by
    have hlo0 : 0 < (4 : ℝ) ^ (-p - 2) * q * μ := by positivity
    have h' : lam ^ (-(1 / 2 : ℝ)) ≤ ((4 : ℝ) ^ (-p - 2) * q * μ) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hlo0 hlam_lo (by norm_num)
    rw [Real.mul_rpow (by positivity) hμ0.le] at h'
    have e : 8 / Real.sqrt lam = 8 * lam ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_neg hlam0.le, div_eq_mul_inv]
    rw [e]
    calc 8 * lam ^ (-(1 / 2 : ℝ)) ≤ 8 * (((4 : ℝ) ^ (-p - 2) * q) ^ (-(1 / 2 : ℝ)) *
          μ ^ (-(1 / 2 : ℝ))) := by gcongr
      _ = _ := by ring
  calc |∑ n ∈ Icc N₁ N₂, psi (C * (n : ℝ) ^ (-p))|
      ≤ 6 * (N : ℝ) ^ (3 / 7 : ℝ) * bA C p N ^ (4 / 7 : ℝ) + 3 * (8 / Real.sqrt lam) := hb
    _ ≤ 6 * (cp ^ (4 / 7 : ℝ) * N * (q ^ (2 / 7 : ℝ) * μ ^ (2 / 7 : ℝ))) +
        3 * (8 * ((4 : ℝ) ^ (-p - 2) * q) ^ (-(1 / 2 : ℝ)) * μ ^ (-(1 / 2 : ℝ))) := by
        have := mul_le_mul_of_nonneg_left hl27 (by positivity : (0 : ℝ) ≤ cp ^ (4 / 7 : ℝ) * N)
        nlinarith
    _ = 6 * cp ^ (4 / 7 : ℝ) * q ^ (2 / 7 : ℝ) * N * μ ^ (2 / 7 : ℝ) +
        24 * ((4 : ℝ) ^ (-p - 2) * q) ^ (-(1 / 2 : ℝ)) * μ ^ (-(1 / 2 : ℝ)) := by ring

end Kerr.PowerfulNumbers
