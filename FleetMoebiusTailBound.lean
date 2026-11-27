import FleetMoebiusTail

/-!
# The Möbius tail beyond `e^{1.1/b}` is exponentially small, unconditionally

Absolute bound, no cancellation in `μ`, no prime-distribution input. For weights with the Gaussian envelope

  `|k n| ≤ 2 · exp(−½ log n − b log² n)`   (`n ≥ 1`),

and any cutoff `M ≥ 1` with `log M ≥ 1.1/b`, the Möbius tail of `FleetMoebiusTail` satisfies

  `|Σ_{M < m ≤ N} μ(m) T m| ≤ 2 · exp(−0.6375/b)`,     uniformly in `N` (and in `α` for the cosine weights).

Proof: the tangent-line inequality `−½t − bt² ≤ 25/(16b) − 3t` gives `|k(x)| ≤ 2e^{25/(16b)} x^{-3}`;
`log j ≤ j`; `Σ_{j ≤ N} j^{-2} ≤ 2`; `Σ_{M<m≤N} m^{-3} ≤ 1/(2M²)` (telescoping); `M² ≥ e^{2.2/b}`.

With `N = ⌈e^{2.2/b}⌉` and `M ≥ √N`, `FleetMoebiusTail.prime_sum_sub_budget` then says the mollified budget
equals the prime sum up to `2e^{−0.6375/b}`: all arithmetic content sits in the retained head `m ≤ M`.
-/

set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace FleetMoebiusTailBound

open FleetMoebiusTail

/-- Gaussian envelope pointwise: `exp(−½t − bt²) ≤ exp(25/(16b)) · exp(−3t)`. -/
lemma tangent {b : ℝ} (hb : 0 < b) (t : ℝ) :
    Real.exp (-(1/2) * t - b * t ^ 2) ≤ Real.exp (25 / (16 * b)) * Real.exp (-3 * t) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h : 0 ≤ b * (t - 5 / (4 * b)) ^ 2 := by positivity
  have e : b * (t - 5 / (4 * b)) ^ 2 = b * t ^ 2 - 5 / 2 * t + 25 / (16 * b) := by
    field_simp; ring
  linarith

lemma exp_neg_three_log {x : ℝ} (hx : 0 < x) : Real.exp (-3 * Real.log x) = 1 / x ^ 3 := by
  rw [show -3 * Real.log x = -(Real.log (x ^ 3)) by rw [Real.log_pow]; push_cast; ring,
    Real.exp_neg, Real.exp_log (by positivity), one_div]

/-- `Σ_{j=1}^{n} 1/j² ≤ 2 − 1/n` for `n ≥ 1`. -/
lemma sum_inv_sq_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Icc 1 n, (1 : ℝ) / (j : ℝ) ^ 2 ≤ 2 - 1 / n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · norm_num
    rw [Finset.sum_Icc_succ_top (by omega)]
    have := ih hpos
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hpos
    have key : (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / n - 1 / ((n + 1 : ℕ) : ℝ) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

lemma sum_inv_sq_le_two (n : ℕ) : ∑ j ∈ Icc 1 n, (1 : ℝ) / (j : ℝ) ^ 2 ≤ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have := sum_inv_sq_le n hn
  have : (0 : ℝ) ≤ 1 / n := by positivity
  linarith

/-- `Σ_{M<m≤N} 1/m³ ≤ 1/(2M²) − 1/(2N²)` for `1 ≤ M ≤ N`. -/
lemma sum_inv_cube_le (M : ℕ) (hM : 1 ≤ M) (N : ℕ) (hMN : M ≤ N) :
    ∑ m ∈ Ioc M N, (1 : ℝ) / (m : ℝ) ^ 3 ≤ 1 / (2 * (M : ℝ) ^ 2) - 1 / (2 * (N : ℝ) ^ 2) := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ N hMN ih =>
    rw [Finset.sum_Ioc_succ_top (by omega)]
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast le_trans hM hMN
    have key : (1 : ℝ) / ((N + 1 : ℕ) : ℝ) ^ 3
        ≤ 1 / (2 * (N : ℝ) ^ 2) - 1 / (2 * ((N + 1 : ℕ) : ℝ) ^ 2) := by
      push_cast
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (N : ℝ), mul_pos (by linarith : (0:ℝ) < N) (by linarith : (0:ℝ) < N)]
    linarith

lemma sum_inv_cube_le' (M : ℕ) (hM : 1 ≤ M) (N : ℕ) :
    ∑ m ∈ Ioc M N, (1 : ℝ) / (m : ℝ) ^ 3 ≤ 1 / (2 * (M : ℝ) ^ 2) := by
  rcases le_or_gt M N with h | h
  · have := sum_inv_cube_le M hM N h
    have : (0 : ℝ) ≤ 1 / (2 * (N : ℝ) ^ 2) := by positivity
    linarith
  · rw [Finset.Ioc_eq_empty (by omega)]; simp

/-- **Möbius tail bound.** -/
theorem moebius_tail_bound {b : ℝ} (hb : 0 < b) (N M : ℕ) (hM : 1 ≤ M)
    (hML : 11 / (10 * b) ≤ Real.log M) (k : ℕ → ℝ)
    (hk : ∀ n : ℕ, 1 ≤ n → |k n| ≤ 2 * Real.exp (-(1/2) * Real.log n - b * Real.log n ^ 2)) :
    |∑ m ∈ Ioc M N, ((μ m : ℤ) : ℝ) * T N k m| ≤ 2 * Real.exp (-(51 / 80) / b) := by
  set C := Real.exp (25 / (16 * b)) with hC
  have hpt : ∀ m ∈ Ioc M N, ∀ j ∈ Icc 1 N,
      |Real.log j * k (m * j)| ≤ 2 * C * ((1 : ℝ) / (m : ℝ) ^ 3 * (1 / (j : ℝ) ^ 2)) := by
    intro m hm j hj
    have hm1 : 1 ≤ m := by have := (Finset.mem_Ioc.mp hm).1; omega
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
    have hjR : (0 : ℝ) < j := by exact_mod_cast hj1
    have hx : (0 : ℝ) < ((m * j : ℕ) : ℝ) := by push_cast; positivity
    have hk' := hk (m * j) (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))
    have ht := tangent hb (Real.log ((m * j : ℕ) : ℝ))
    rw [exp_neg_three_log hx] at ht
    have hlog0 : 0 ≤ Real.log j := Real.log_natCast_nonneg j
    have hlogj : Real.log j ≤ j := by linarith [Real.log_le_sub_one_of_pos hjR]
    have hkx : |k (m * j)| ≤ 2 * C * (1 / ((m * j : ℕ) : ℝ) ^ 3) := by
      calc |k (m * j)| ≤ 2 * Real.exp (-(1/2) * Real.log ((m * j : ℕ) : ℝ) - b * Real.log ((m * j : ℕ) : ℝ) ^ 2) := hk'
        _ ≤ 2 * (C * (1 / ((m * j : ℕ) : ℝ) ^ 3)) := by linarith
        _ = _ := by ring
    rw [abs_mul, abs_of_nonneg hlog0]
    calc Real.log j * |k (m * j)| ≤ (j : ℝ) * (2 * C * (1 / ((m * j : ℕ) : ℝ) ^ 3)) :=
          mul_le_mul hlogj hkx (abs_nonneg _) hjR.le
      _ = 2 * C * ((1 : ℝ) / (m : ℝ) ^ 3 * (1 / (j : ℝ) ^ 2)) := by
          push_cast; field_simp
  have hC0 : 0 ≤ C := (Real.exp_pos _).le
  have h1 : |∑ m ∈ Ioc M N, ((μ m : ℤ) : ℝ) * T N k m|
      ≤ ∑ m ∈ Ioc M N, ∑ j ∈ Icc 1 N, 2 * C * ((1 : ℝ) / (m : ℝ) ^ 3 * (1 / (j : ℝ) ^ 2)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun m hm => ?_))
    have hmu : |((μ m : ℤ) : ℝ)| ≤ 1 := by
      have := ArithmeticFunction.abs_moebius_le_one (n := m)
      exact_mod_cast this
    rw [abs_mul]
    calc |((μ m : ℤ) : ℝ)| * |T N k m| ≤ 1 * |T N k m| :=
          mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
      _ = |T N k m| := one_mul _
      _ ≤ ∑ j ∈ Icc 1 N, |Real.log j * k (m * j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum (fun j hj => hpt m hm j hj)
  have h2 : ∑ m ∈ Ioc M N, ∑ j ∈ Icc 1 N, 2 * C * ((1 : ℝ) / (m : ℝ) ^ 3 * (1 / (j : ℝ) ^ 2))
      = 2 * C * ((∑ m ∈ Ioc M N, (1 : ℝ) / (m : ℝ) ^ 3) * (∑ j ∈ Icc 1 N, (1 : ℝ) / (j : ℝ) ^ 2)) := by
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.mul_sum]
  have hA := sum_inv_cube_le' M hM N
  have hB := sum_inv_sq_le_two N
  have h3 : 2 * C * ((∑ m ∈ Ioc M N, (1 : ℝ) / (m : ℝ) ^ 3) * (∑ j ∈ Icc 1 N, (1 : ℝ) / (j : ℝ) ^ 2))
      ≤ 2 * C * (1 / (M : ℝ) ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc (∑ m ∈ Ioc M N, (1 : ℝ) / (m : ℝ) ^ 3) * (∑ j ∈ Icc 1 N, (1 : ℝ) / (j : ℝ) ^ 2)
        ≤ (1 / (2 * (M : ℝ) ^ 2)) * 2 :=
          mul_le_mul hA hB (Finset.sum_nonneg (fun _ _ => by positivity)) (by positivity)
      _ = 1 / (M : ℝ) ^ 2 := by field_simp
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hM2 : 1 / (M : ℝ) ^ 2 ≤ Real.exp (-(11 / 5) / b) := by
    have hexp : Real.exp (11 / (10 * b)) ≤ M := by
      calc Real.exp (11 / (10 * b)) ≤ Real.exp (Real.log M) := Real.exp_le_exp.mpr hML
        _ = M := Real.exp_log hMR
    have hsq : Real.exp (11 / 5 / b) ≤ (M : ℝ) ^ 2 := by
      have : Real.exp (11 / 5 / b) = Real.exp (11 / (10 * b)) ^ 2 := by
        rw [← Real.exp_nat_mul]; congr 1; field_simp; ring
      rw [this]; exact pow_le_pow_left₀ (Real.exp_pos _).le hexp 2
    rw [show -(11 / 5) / b = -(11 / 5 / b) by ring, Real.exp_neg, one_div]
    exact inv_anti₀ (Real.exp_pos _) hsq
  have h4 : 2 * C * (1 / (M : ℝ) ^ 2) ≤ 2 * Real.exp (-(51 / 80) / b) := by
    calc 2 * C * (1 / (M : ℝ) ^ 2) ≤ 2 * C * Real.exp (-(11 / 5) / b) :=
          mul_le_mul_of_nonneg_left hM2 (by positivity)
      _ = 2 * Real.exp (-(51 / 80) / b) := by
          rw [hC, mul_assoc, ← Real.exp_add]; congr 2; field_simp; ring
  rw [h2] at h1
  linarith

/-- **Mollified budget = prime sum up to `2e^{−0.6375/b}`** (weights zero beyond `N`, `M ≤ N`). -/
theorem prime_sum_near_budget {b : ℝ} (hb : 0 < b) (N M : ℕ) (hM : 1 ≤ M) (hMN : M ≤ N)
    (hML : 11 / (10 * b) ≤ Real.log M) (k : ℕ → ℝ) (hkN : ∀ n, N < n → k n = 0)
    (hk : ∀ n : ℕ, 1 ≤ n → |k n| ≤ 2 * Real.exp (-(1/2) * Real.log n - b * Real.log n ^ 2)) :
    |∑ d ∈ Icc 1 N, vonMangoldt d * k d - ∑ n ∈ Icc 1 N, Real.log n * uM M k n|
      ≤ 2 * Real.exp (-(51 / 80) / b) := by
  rw [prime_sum_sub_budget N M hMN k hkN]
  exact moebius_tail_bound hb N M hM hML k hk

end FleetMoebiusTailBound
