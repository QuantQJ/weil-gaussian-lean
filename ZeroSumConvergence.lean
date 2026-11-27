import Mathlib

/-!
# Convergence of zero sums under a Riemann–von Mangoldt-type counting bound

Conditional scaffolding for the `T → ∞` limit of the explicit formula on the zero side.

Setting: `γ : ℕ → ℝ` is a sequence of real ordinates, listed in non-decreasing absolute
value, all of modulus `≥ 2`, and `count γ T := Set.ncard {n | |γ n| ≤ T}` is its counting
function.  The **unproven input** is the pair of hypotheses

* `hfin : ∀ T, {n | |γ n| ≤ T}.Finite`   (finitely many ordinates below any height), and
* `hN   : ∀ T ≥ 2, (count γ T : ℝ) ≤ C * T * Real.log T`   (`N(T) = O(T log T)`).

(`hfin` is needed because `Set.ncard` of an infinite set is `0`, which would make `hN`
vacuous; for the actual zeta zeros both are consequences of Riemann–von Mangoldt.)

**Proven from these hypotheses:**
* `count_ge_succ`                — `n + 1 ≤ count γ |γ n|` (monotonicity).
* `abs_rpow_three_halves_ge`     — `(n+1)/(2C) ≤ |γ n|^(3/2)`.
* `inv_sq_le`                    — `1/(γ n)^2 ≤ (2C)^(4/3) / (n+1)^(4/3)`.
* `summable_inv_sq_of_count_bound` — `Summable (fun n => 1/(γ n)^2)`.
* `summable_norm_of_decay`, `summable_of_decay` — for `G : ℝ → ℂ` with
  `‖G t‖ ≤ K/(1+t^2)`, the zero sum `∑ G (γ n)` is (absolutely) summable.
* `tendsto_partial_sums`         — the height-`T` truncations `∑' n, if |γ n| ≤ T then G (γ n) else 0`
  converge to the full zero sum as `T → ∞` (Tannery / dominated convergence for `tsum`).

**Not proven here:** the zero-density bound itself (`hN`, `hfin`) — that is the only
external input; nothing about `ζ` is used or asserted in this file.
-/

noncomputable section

open Filter Topology

namespace ZeroSumConvergence

/-- Counting function of the sequence `γ`: the number of indices `n` with `|γ n| ≤ T`.
(`Set.ncard` returns `0` for an infinite set, hence the separate finiteness hypothesis
`hfin` in every theorem below.) -/
def count (γ : ℕ → ℝ) (T : ℝ) : ℕ := Set.ncard {n | |γ n| ≤ T}

/-- If `|γ ·|` is monotone and every level set is finite, then the first `n + 1` ordinates all
lie below `|γ n|`, so `n + 1 ≤ count γ |γ n|`. -/
theorem count_ge_succ (γ : ℕ → ℝ) (hmono : Monotone (fun n => |γ n|))
    (hfin : ∀ T, {n | |γ n| ≤ T}.Finite) (n : ℕ) :
    n + 1 ≤ count γ |γ n| := by
  have hsub : ((Finset.range (n + 1) : Finset ℕ) : Set ℕ) ⊆ {m | |γ m| ≤ |γ n|} := by
    intro m hm
    rw [Finset.coe_range, Set.mem_Iio] at hm
    exact hmono (Nat.lt_succ_iff.mp hm)
  have h := Set.ncard_le_ncard hsub (hfin _)
  rw [Set.ncard_coe_finset, Finset.card_range] at h
  exact h

/-- The constant `C` in the counting bound is forced to be positive (the bound at `T = |γ 0|`
gives `1 ≤ C · |γ 0| · log |γ 0|`). -/
theorem count_bound_const_pos (γ : ℕ → ℝ) (C : ℝ) (hγ : ∀ n, 2 ≤ |γ n|)
    (hmono : Monotone (fun n => |γ n|)) (hfin : ∀ T, {n | |γ n| ≤ T}.Finite)
    (hN : ∀ T ≥ 2, (count γ T : ℝ) ≤ C * T * Real.log T) : 0 < C := by
  have h0 : (1 : ℝ) ≤ count γ |γ 0| := by
    exact_mod_cast count_ge_succ γ hmono hfin 0
  have h1 := hN |γ 0| (hγ 0)
  have hlog : 0 ≤ Real.log |γ 0| := Real.log_nonneg (by linarith [hγ 0])
  have hpos : 0 ≤ |γ 0| * Real.log |γ 0| := by positivity
  by_contra hC
  push_neg at hC
  have := mul_nonpos_of_nonpos_of_nonneg hC hpos
  rw [← mul_assoc] at this
  linarith

/-- From `n + 1 ≤ C |γ n| log |γ n|` and `log x ≤ 2 √x`, we get `(n+1)/(2C) ≤ |γ n|^(3/2)`. -/
theorem abs_rpow_three_halves_ge (γ : ℕ → ℝ) (C : ℝ) (hγ : ∀ n, 2 ≤ |γ n|)
    (hmono : Monotone (fun n => |γ n|)) (hfin : ∀ T, {n | |γ n| ≤ T}.Finite)
    (hN : ∀ T ≥ 2, (count γ T : ℝ) ≤ C * T * Real.log T) (n : ℕ) :
    ((n : ℝ) + 1) / (2 * C) ≤ |γ n| ^ ((3 : ℝ) / 2) := by
  have hC := count_bound_const_pos γ C hγ hmono hfin hN
  have ha : (2 : ℝ) ≤ |γ n| := hγ n
  have ha0 : 0 < |γ n| := by linarith
  have hcount : ((n : ℝ) + 1) ≤ count γ |γ n| := by
    exact_mod_cast count_ge_succ γ hmono hfin n
  have hlog : Real.log |γ n| ≤ 2 * |γ n| ^ ((1 : ℝ) / 2) := by
    have := Real.log_le_rpow_div (x := |γ n|) (ε := 1 / 2) ha0.le (by norm_num)
    calc Real.log |γ n| ≤ |γ n| ^ ((1 : ℝ) / 2) / (1 / 2) := this
      _ = 2 * |γ n| ^ ((1 : ℝ) / 2) := by ring
  have hsplit : |γ n| ^ ((3 : ℝ) / 2) = |γ n| * |γ n| ^ ((1 : ℝ) / 2) := by
    rw [show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_add ha0, Real.rpow_one]
  have h1 : ((n : ℝ) + 1) ≤ C * |γ n| * Real.log |γ n| := hcount.trans (hN _ ha)
  have h2 : C * |γ n| * Real.log |γ n| ≤ C * |γ n| * (2 * |γ n| ^ ((1 : ℝ) / 2)) := by
    apply mul_le_mul_of_nonneg_left hlog
    positivity
  rw [div_le_iff₀ (by positivity), hsplit]
  nlinarith [h1, h2]

/-- Pointwise bound `1/(γ n)^2 ≤ (2C)^(4/3) / (n+1)^(4/3)`. -/
theorem inv_sq_le (γ : ℕ → ℝ) (C : ℝ) (hγ : ∀ n, 2 ≤ |γ n|)
    (hmono : Monotone (fun n => |γ n|)) (hfin : ∀ T, {n | |γ n| ≤ T}.Finite)
    (hN : ∀ T ≥ 2, (count γ T : ℝ) ≤ C * T * Real.log T) (n : ℕ) :
    1 / (γ n) ^ 2 ≤ (2 * C) ^ ((4 : ℝ) / 3) / ((n : ℝ) + 1) ^ ((4 : ℝ) / 3) := by
  have hC := count_bound_const_pos γ C hγ hmono hfin hN
  have ha0 : 0 < |γ n| := by linarith [hγ n]
  have hkey := abs_rpow_three_halves_ge γ C hγ hmono hfin hN n
  have hb0 : 0 ≤ ((n : ℝ) + 1) / (2 * C) := by positivity
  -- raise to the power 4/3
  have hpow : (((n : ℝ) + 1) / (2 * C)) ^ ((4 : ℝ) / 3) ≤ |γ n| ^ 2 := by
    calc (((n : ℝ) + 1) / (2 * C)) ^ ((4 : ℝ) / 3)
        ≤ (|γ n| ^ ((3 : ℝ) / 2)) ^ ((4 : ℝ) / 3) :=
          Real.rpow_le_rpow hb0 hkey (by norm_num)
      _ = |γ n| ^ ((3 : ℝ) / 2 * (4 / 3)) := (Real.rpow_mul ha0.le _ _).symm
      _ = |γ n| ^ (2 : ℝ) := by norm_num
      _ = |γ n| ^ 2 := Real.rpow_two _
  have hbpos : 0 < (((n : ℝ) + 1) / (2 * C)) ^ ((4 : ℝ) / 3) := by
    apply Real.rpow_pos_of_pos
    positivity
  calc 1 / (γ n) ^ 2 = 1 / |γ n| ^ 2 := by rw [sq_abs]
    _ ≤ 1 / (((n : ℝ) + 1) / (2 * C)) ^ ((4 : ℝ) / 3) :=
        one_div_le_one_div_of_le hbpos hpow
    _ = (2 * C) ^ ((4 : ℝ) / 3) / ((n : ℝ) + 1) ^ ((4 : ℝ) / 3) := by
        rw [Real.div_rpow (by positivity) (by positivity), one_div_div]

/-- **(1)** Under the counting bound `N(T) ≤ C T log T`, the series `∑ 1/γ_n²` converges. -/
theorem summable_inv_sq_of_count_bound (γ : ℕ → ℝ) (C : ℝ) (hγ : ∀ n, 2 ≤ |γ n|)
    (hmono : Monotone (fun n => |γ n|)) (hfin : ∀ T, {n | |γ n| ≤ T}.Finite)
    (hN : ∀ T ≥ 2, (count γ T : ℝ) ≤ C * T * Real.log T) :
    Summable (fun n => 1 / (γ n) ^ 2) := by
  -- dominating series: (2C)^(4/3) * ((n+1)^(4/3))⁻¹
  have hp : Summable (fun n : ℕ => (((n : ℝ)) ^ ((4 : ℝ) / 3))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  have hp1 : Summable (fun n : ℕ => ((((n + 1 : ℕ) : ℝ)) ^ ((4 : ℝ) / 3))⁻¹) :=
    (summable_nat_add_iff 1).mpr hp
  have hdom : Summable (fun n : ℕ =>
      (2 * C) ^ ((4 : ℝ) / 3) / ((n : ℝ) + 1) ^ ((4 : ℝ) / 3)) := by
    have := hp1.mul_left ((2 * C) ^ ((4 : ℝ) / 3))
    refine this.congr fun n => ?_
    push_cast
    ring
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => inv_sq_le γ C hγ hmono hfin hN n) hdom
  have : 0 < |γ n| := by linarith [hγ n]
  have : (γ n) ^ 2 = |γ n| ^ 2 := (sq_abs _).symm
  rw [this]
  positivity

/-- Absolute summability of the zero sum of a function with quadratic decay
`‖G t‖ ≤ K / (1 + t²)`. -/
theorem summable_norm_of_decay (γ : ℕ → ℝ) (C : ℝ) (hγ : ∀ n, 2 ≤ |γ n|)
    (hmono : Monotone (fun n => |γ n|)) (hfin : ∀ T, {n | |γ n| ≤ T}.Finite)
    (hN : ∀ T ≥ 2, (count γ T : ℝ) ≤ C * T * Real.log T)
    (G : ℝ → ℂ) (K : ℝ) (hG : ∀ t, ‖G t‖ ≤ K / (1 + t ^ 2)) :
    Summable (fun n => ‖G (γ n)‖) := by
  have hK : 0 ≤ K := by
    have := hG 0
    rw [zero_pow two_ne_zero, add_zero, div_one] at this
    exact (norm_nonneg _).trans this
  have hsum := (summable_inv_sq_of_count_bound γ C hγ hmono hfin hN).mul_left K
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hsum
  have hsq : 0 < (γ n) ^ 2 := by
    have : 0 < |γ n| := by linarith [hγ n]
    rw [← sq_abs]; positivity
  calc ‖G (γ n)‖ ≤ K / (1 + (γ n) ^ 2) := hG _
    _ ≤ K / (γ n) ^ 2 := div_le_div_of_nonneg_left hK hsq (by linarith)
    _ = K * (1 / (γ n) ^ 2) := by rw [mul_one_div]

/-- **(2)** The zero sum `∑ G (γ n)` of a function with quadratic decay converges. -/
theorem summable_of_decay (γ : ℕ → ℝ) (C : ℝ) (hγ : ∀ n, 2 ≤ |γ n|)
    (hmono : Monotone (fun n => |γ n|)) (hfin : ∀ T, {n | |γ n| ≤ T}.Finite)
    (hN : ∀ T ≥ 2, (count γ T : ℝ) ≤ C * T * Real.log T)
    (G : ℝ → ℂ) (K : ℝ) (hG : ∀ t, ‖G t‖ ≤ K / (1 + t ^ 2)) :
    Summable (fun n => G (γ n)) :=
  (summable_norm_of_decay γ C hγ hmono hfin hN G K hG).of_norm

/-- **(3)** The truncated zero sums at height `T` (what the contour at height `T` produces)
converge, as `T → ∞`, to the full zero sum. Proof: Tannery's theorem
(`tendsto_tsum_of_dominated_convergence`) with dominating sequence `‖G (γ n)‖`. -/
theorem tendsto_partial_sums (γ : ℕ → ℝ) (C : ℝ) (hγ : ∀ n, 2 ≤ |γ n|)
    (hmono : Monotone (fun n => |γ n|)) (hfin : ∀ T, {n | |γ n| ≤ T}.Finite)
    (hN : ∀ T ≥ 2, (count γ T : ℝ) ≤ C * T * Real.log T)
    (G : ℝ → ℂ) (K : ℝ) (hG : ∀ t, ‖G t‖ ≤ K / (1 + t ^ 2)) :
    Tendsto (fun T : ℝ => ∑' n, if |γ n| ≤ T then G (γ n) else 0) atTop
      (𝓝 (∑' n, G (γ n))) := by
  have hbound := summable_norm_of_decay γ C hγ hmono hfin hN G K hG
  refine tendsto_tsum_of_dominated_convergence
    (f := fun (T : ℝ) (n : ℕ) => if |γ n| ≤ T then G (γ n) else 0)
    (g := fun n => G (γ n)) (bound := fun n => ‖G (γ n)‖) hbound (fun k => ?_) ?_
  · -- each term is eventually constant
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop |γ k|] with T hT
    simp [hT]
  · refine Eventually.of_forall fun T k => ?_
    split_ifs <;> simp

end ZeroSumConvergence
