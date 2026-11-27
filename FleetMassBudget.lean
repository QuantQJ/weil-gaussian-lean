/-
Copyright 2026 James C. Kerr (QuantQJ). Apache-2.0.
-/
import Mathlib
import ZeroDensityUnconditional

/-!
# A named explicit mass budget

`FleetMassBound.exists_uniform_mass_bound` discharges the mass conjunct of
`FleetRationalBankCriterion.Feasible` with the witness `M := ∑' n, (1 + γ n ^ 2)⁻¹` -- the tsum
itself, so an existence proof with no numeral and no route to one.  This file names a constant
instead and proves what can be proved about it.

* `kSeven = 5 (log 10 + 6)` is `ZeroDensity.K 7`, the repo's explicit local-counting constant.
* `tailConst = 2/√13` bounds `∑_{j ≥ 14} j^{-3/2}` (comparison with `∫_13^∞ t^{-3/2} dt`).
* `budget = 4 · kSeven · tailConst = 40 (log 10 + 6)/√13`, the two-sided constant.

**Proved unconditionally**: `budget_pos`, `budget_eq`, `log_ten_lt_three`, `kSeven_lt_45`,
`sqrt_thirteen_gt`, and `budget_lt_100` -- so the budget is a named closed-form constant, under
100, with no existential.  `log_ten_lt_three` goes through Mathlib's `Real.exp_one_gt_d9`.

**Proved as a reduction**: `sum_weight_le_blocks` (the weight is antitone in the height, so a
family at heights at least its block indices has mass at most the block sum) and
`mass_le_budget`, which assembles the bound from its two numeric inputs, each named as an
explicit hypothesis rather than assumed:

* `hcount` -- at most `K(7) log (j+1)` ordinates land in block `j ≥ 14`.  This is the repo's
  `ZeroDensityUnconditional.ncard_zeros_near_height_le` instantiated at integer heights; the
  instantiation is **not** done here (it needs the repo build, not just Mathlib).
* `htail`  -- `∑_{j ≥ 14} log (j+1) (1 + j²)⁻¹ ≤ 2/√13`.  Numerically `0.269`, so the stated
  `2/√13 = 0.5547` is comfortable, but the finite head plus tail comparison is **not** proved
  here either.

So: the constant is named and bounded; the two inputs that would make the whole thing
unconditional are isolated, stated, and still open.  The sharper value `44.67` quoted in
discussion needs `log 10 < 2.303` (`kSeven_lt`, available as a hypothesis) together with the
sharper tail `0.269`; with the crude inputs proved here the honest numeral is `< 100`.
-/

set_option autoImplicit false
noncomputable section
open Finset
open Reduction

namespace MassBudget

/-- `ZeroDensity.K 7 = 5 (log 10 + 6)`, the explicit local-counting constant of the repo. -/
def kSeven : ℝ := 5 * (Real.log 10 + 6)

/-- `∑_{j ≥ 14} j^{-3/2} ≤ 2/√13`, the tail comparison constant. -/
def tailConst : ℝ := 2 / Real.sqrt 13

/-- **The named budget.**  Two-sided: `4 · K(7) · (2/√13)`. -/
def budget : ℝ := 4 * kSeven * tailConst

theorem kSeven_pos : 0 < kSeven := by
  have : (0:ℝ) < Real.log 10 := Real.log_pos (by norm_num)
  unfold kSeven; linarith

theorem tailConst_pos : 0 < tailConst := by
  unfold tailConst
  have : (0:ℝ) < Real.sqrt 13 := Real.sqrt_pos.mpr (by norm_num)
  positivity

theorem budget_pos : 0 < budget := by
  unfold budget
  have := kSeven_pos
  have := tailConst_pos
  positivity

/-- Closed form. -/
theorem budget_eq : budget = 40 * (Real.log 10 + 6) / Real.sqrt 13 := by
  unfold budget kSeven tailConst; ring

/-- Numeric enclosure of `K(7)`, from `2.302 < log 10 < 2.303`. -/
theorem kSeven_lt (h : Real.log 10 < 2.303) : kSeven < 41.515 := by
  unfold kSeven; linarith

theorem kSeven_gt (h : 2.302 < Real.log 10) : 41.51 < kSeven := by
  unfold kSeven; linarith

/-- The weight is antitone in the height: a zero further out contributes less. -/
theorem weight_le_of_le {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ |a|) :
    (1 + a ^ 2)⁻¹ ≤ (1 + b ^ 2)⁻¹ := by
  have h1 : (0:ℝ) < 1 + b ^ 2 := by positivity
  have hsq : b ^ 2 ≤ a ^ 2 := by
    have : b ^ 2 ≤ |a| ^ 2 := by nlinarith
    simpa [sq_abs] using this
  exact inv_anti₀ h1 (by linarith)

/-- **Block monotonicity.**  If every member of a finite family sits at height at least its
block index, the weighted mass is at most the sum of the block weights. -/
theorem sum_weight_le_blocks {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (blk : ι → ℕ)
    (h : ∀ i ∈ s, ((blk i : ℝ)) ≤ |γ i|) :
    ∑ i ∈ s, (1 + (γ i) ^ 2)⁻¹ ≤ ∑ i ∈ s, (1 + ((blk i : ℝ)) ^ 2)⁻¹ :=
  Finset.sum_le_sum fun i hi =>
    weight_le_of_le (Nat.cast_nonneg (blk i)) (h i hi)

/-- **The assembled bound, with its two numeric inputs named as hypotheses.**
`hcount`: at most `K(7) log (j+1)` ordinates of either sign land in block `j ≥ 14`
(the repo's `ncard_zeros_near_height_le`, instantiated at integer heights).
`htail`:  `∑_{j ≥ 14} log (j+1) · (1 + j²)⁻¹ ≤ 2/√13` (the comparison with `∑ j^{-3/2}`). -/
theorem mass_le_budget (block : ℕ → ℝ)
    (hcount : ∀ j : ℕ, 14 ≤ j → block j ≤ 2 * kSeven * Real.log (j + 1) * (1 + (j : ℝ) ^ 2)⁻¹)
    (S : Finset ℕ) (hS : ∀ j ∈ S, 14 ≤ j)
    (htail : ∑ j ∈ S, 2 * kSeven * Real.log (j + 1) * (1 + (j : ℝ) ^ 2)⁻¹
      ≤ 2 * kSeven * tailConst) :
    ∑ j ∈ S, block j ≤ budget / 2 := by
  have h1 : ∑ j ∈ S, block j
      ≤ ∑ j ∈ S, 2 * kSeven * Real.log (j + 1) * (1 + (j : ℝ) ^ 2)⁻¹ :=
    Finset.sum_le_sum fun j hj => hcount j (hS j hj)
  have h2 : budget / 2 = 2 * kSeven * tailConst := by unfold budget; ring
  rw [h2]
  exact h1.trans htail

/-! ### Discharging the numerals -/

/-- `log 10 < 3`, from Mathlib's enclosure of `e`. -/
theorem log_ten_lt_three : Real.log 10 < 3 := by
  have h : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hp : Real.exp 1 ^ 3 = Real.exp 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hc : (2.7182818283 : ℝ) ^ 3 < Real.exp 3 := by
    rw [← hp]
    exact pow_lt_pow_left₀ h (by norm_num) (by norm_num)
  have hnum : (10 : ℝ) < (2.7182818283 : ℝ) ^ 3 := by norm_num
  have h10 : (10 : ℝ) < Real.exp 3 := lt_trans hnum hc
  calc Real.log 10 < Real.log (Real.exp 3) := Real.log_lt_log (by norm_num) h10
    _ = 3 := Real.log_exp 3

/-- `K(7) < 45`, unconditionally. -/
theorem kSeven_lt_45 : kSeven < 45 := by
  unfold kSeven; linarith [log_ten_lt_three]

/-- `√13 > 3.6`. -/
theorem sqrt_thirteen_gt : (3.6 : ℝ) < Real.sqrt 13 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

/-- **The budget is under 100, unconditionally.** -/
theorem budget_lt_100 : budget < 100 := by
  have hk := kSeven_lt_45
  have hk0 := kSeven_pos
  have hs : (3.6 : ℝ) < Real.sqrt 13 := sqrt_thirteen_gt
  have hs0 : (0:ℝ) < Real.sqrt 13 := by linarith
  have he : budget = 8 * kSeven / Real.sqrt 13 := by unfold budget kSeven tailConst; ring
  rw [he, div_lt_iff₀ hs0]
  nlinarith

/-! ### `hcount`, discharged from the repo's unconditional local zero count -/

/-- `kSeven` is literally `ZeroDensity.K 7`. -/
theorem kSeven_eq_K7 : kSeven = ZeroDensity.K 7 := by
  unfold kSeven ZeroDensity.K
  norm_num

/-- The weighted mass contributed by the ordinates in the band of radius `1` about `j + 1`. -/
def zeroBlock (j : ℕ) : ℝ :=
  (({ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im - ((j : ℝ) + 1)| ≤ 1}).ncard : ℝ)
    * (1 + (j : ℝ) ^ 2)⁻¹

/-- **`hcount`, discharged.**  No hypothesis: this is
`ZeroDensityUnconditional.ncard_zeros_near_height_le` at the integer height `j + 1`. -/
theorem hcount_zeroBlock (j : ℕ) (hj : 14 ≤ j) :
    zeroBlock j ≤ 2 * kSeven * Real.log (j + 1) * (1 + (j : ℝ) ^ 2)⁻¹ := by
  have hj' : (14 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hpos : (0 : ℝ) ≤ (j : ℝ) + 1 := by linarith
  have h4 : (4 : ℝ) ≤ |((j : ℝ) + 1)| := by
    rw [abs_of_nonneg hpos]; linarith
  have hc := ZeroDensityUnconditional.ncard_zeros_near_height_le ((j : ℝ) + 1) h4
  rw [abs_of_nonneg hpos] at hc
  have hw : (0 : ℝ) ≤ (1 + (j : ℝ) ^ 2)⁻¹ := by positivity
  unfold zeroBlock
  calc (({ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im - ((j : ℝ) + 1)| ≤ 1}).ncard : ℝ)
        * (1 + (j : ℝ) ^ 2)⁻¹
      ≤ (2 * ZeroDensity.K 7 * Real.log ((j : ℝ) + 1)) * (1 + (j : ℝ) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hc hw
    _ = 2 * kSeven * Real.log ((j : ℝ) + 1) * (1 + (j : ℝ) ^ 2)⁻¹ := by
        rw [kSeven_eq_K7]

/-- **The bound with `hcount` discharged**: only the tail estimate remains a hypothesis. -/
theorem mass_le_budget_of_tail (S : Finset ℕ) (hS : ∀ j ∈ S, 14 ≤ j)
    (htail : ∑ j ∈ S, 2 * kSeven * Real.log (j + 1) * (1 + (j : ℝ) ^ 2)⁻¹
      ≤ 2 * kSeven * tailConst) :
    ∑ j ∈ S, zeroBlock j ≤ budget / 2 :=
  mass_le_budget zeroBlock (fun j hj => hcount_zeroBlock j hj) S hS htail

/-! ### Toward `htail`: the log is beaten by a power, provably -/

/-- `√(j+1) ≤ √j + 1`. -/
theorem sqrt_succ_le (j : ℕ) : Real.sqrt ((j : ℝ) + 1) ≤ Real.sqrt (j : ℝ) + 1 := by
  have h0 : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hs : Real.sqrt (j : ℝ) ^ 2 = (j : ℝ) := Real.sq_sqrt h0
  have hsn : 0 ≤ Real.sqrt (j : ℝ) := Real.sqrt_nonneg _
  have hle : ((j : ℝ) + 1) ≤ (Real.sqrt (j : ℝ) + 1) ^ 2 := by nlinarith
  calc Real.sqrt ((j : ℝ) + 1) ≤ Real.sqrt ((Real.sqrt (j : ℝ) + 1) ^ 2) :=
        Real.sqrt_le_sqrt hle
    _ = Real.sqrt (j : ℝ) + 1 := Real.sqrt_sq (by linarith)

/-- **`log (j+1) ≤ 2 √j`.**  Two applications of `log x ≤ x - 1`, no numerics. -/
theorem log_succ_le_two_sqrt (j : ℕ) (hj : 1 ≤ j) :
    Real.log ((j : ℝ) + 1) ≤ 2 * Real.sqrt (j : ℝ) := by
  have h1 : (0:ℝ) < (j : ℝ) + 1 := by positivity
  have hsq : Real.log (Real.sqrt ((j : ℝ) + 1)) = Real.log ((j : ℝ) + 1) / 2 :=
    Real.log_sqrt (by linarith)
  have hpos : (0:ℝ) < Real.sqrt ((j : ℝ) + 1) := Real.sqrt_pos.mpr h1
  have hstep : Real.log (Real.sqrt ((j : ℝ) + 1)) ≤ Real.sqrt ((j : ℝ) + 1) - 1 :=
    Real.log_le_sub_one_of_pos hpos
  have hss := sqrt_succ_le j
  rw [hsq] at hstep
  linarith

/-- **Termwise**: the block weight is at most `2 √j / j²` for `j ≥ 1`.  The log is beaten by a
power, with no numerics and no `rpow`. -/
theorem term_le_sqrt_div (j : ℕ) (hj : 1 ≤ j) :
    Real.log ((j : ℝ) + 1) * (1 + (j : ℝ) ^ 2)⁻¹ ≤ 2 * (Real.sqrt (j : ℝ) / (j : ℝ) ^ 2) := by
  have hjR : (1:ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hj0 : (0:ℝ) < (j : ℝ) := by linarith
  have hlog := log_succ_le_two_sqrt j hj
  have hw : (0:ℝ) < (1 + (j : ℝ) ^ 2)⁻¹ := by positivity
  have hwle : (1 + (j : ℝ) ^ 2)⁻¹ ≤ ((j : ℝ) ^ 2)⁻¹ := by
    apply inv_anti₀ (by positivity); linarith
  have hsn : (0:ℝ) ≤ Real.sqrt (j : ℝ) := Real.sqrt_nonneg _
  calc Real.log ((j : ℝ) + 1) * (1 + (j : ℝ) ^ 2)⁻¹
      ≤ (2 * Real.sqrt (j : ℝ)) * (1 + (j : ℝ) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hlog hw.le
    _ ≤ (2 * Real.sqrt (j : ℝ)) * ((j : ℝ) ^ 2)⁻¹ := by
        apply mul_le_mul_of_nonneg_left hwle; positivity
    _ = 2 * (Real.sqrt (j : ℝ) / (j : ℝ) ^ 2) := by
        rw [div_eq_mul_inv]; ring

/-- **The bound with `hcount` discharged and the log eliminated.**  The only remaining input is
the pure power-tail estimate `∑_{j ∈ S} √j / j² ≤ tailConst`, i.e. `∑_{j ≥ 14} j^{-3/2} ≤ 2/√13`
— no logarithm, no zeta data, a statement about `ℕ` and `√` alone.  Mathlib route:
`AntitoneOn.tsum_comp_add_le_integral 13` with `f t = t ^ (-(3/2) : ℝ)` and
`∫_{Ioi 13} t^{-3/2} = 2/√13`. -/
theorem mass_le_budget_of_powerTail (S : Finset ℕ) (hS : ∀ j ∈ S, 14 ≤ j)
    (hpow : ∑ j ∈ S, Real.sqrt (j : ℝ) / (j : ℝ) ^ 2 ≤ tailConst) :
    ∑ j ∈ S, zeroBlock j ≤ budget := by
  have hk := kSeven_pos
  have step : ∀ j ∈ S, zeroBlock j ≤ 4 * kSeven * (Real.sqrt (j : ℝ) / (j : ℝ) ^ 2) := by
    intro j hj
    have hj14 := hS j hj
    have hj1 : 1 ≤ j := le_trans (by norm_num) hj14
    have h1 := hcount_zeroBlock j hj14
    have h2 := term_le_sqrt_div j hj1
    have h3 : 2 * kSeven * Real.log ((j : ℝ) + 1) * (1 + (j : ℝ) ^ 2)⁻¹
        ≤ 2 * kSeven * (2 * (Real.sqrt (j : ℝ) / (j : ℝ) ^ 2)) := by
      have : (0:ℝ) ≤ 2 * kSeven := by linarith
      calc 2 * kSeven * Real.log ((j : ℝ) + 1) * (1 + (j : ℝ) ^ 2)⁻¹
          = (2 * kSeven) * (Real.log ((j : ℝ) + 1) * (1 + (j : ℝ) ^ 2)⁻¹) := by ring
        _ ≤ (2 * kSeven) * (2 * (Real.sqrt (j : ℝ) / (j : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left h2 this
    have h4 : 2 * kSeven * (2 * (Real.sqrt (j : ℝ) / (j : ℝ) ^ 2))
        = 4 * kSeven * (Real.sqrt (j : ℝ) / (j : ℝ) ^ 2) := by ring
    linarith [h1, h3]
  calc ∑ j ∈ S, zeroBlock j
      ≤ ∑ j ∈ S, 4 * kSeven * (Real.sqrt (j : ℝ) / (j : ℝ) ^ 2) :=
        Finset.sum_le_sum step
    _ = 4 * kSeven * ∑ j ∈ S, Real.sqrt (j : ℝ) / (j : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ 4 * kSeven * tailConst := by
        apply mul_le_mul_of_nonneg_left hpow
        linarith
    _ = budget := by unfold budget; ring

/-! ### `htail`, discharged by telescoping -/

/-- `g k = 1/√(k+13)`, the telescoping majorant. -/
def g (k : ℕ) : ℝ := 1 / Real.sqrt ((k : ℝ) + 13)

/-- **The termwise telescoping bound.**  `(k+14)^{-3/2} ≤ 2 (g k − g (k+1))`.
Elementary: `g k − g (k+1) = 1/(ab(a+b))` with `a = √(k+13) ≤ b = √(k+14)`, and
`ab(a+b) ≤ 2b³`. -/
theorem term_le_telescope (k : ℕ) :
    Real.sqrt ((k : ℝ) + 14) / ((k : ℝ) + 14) ^ 2 ≤ 2 * (g k - g (k + 1)) := by
  have h13 : (0:ℝ) < (k : ℝ) + 13 := by positivity
  have h14 : (0:ℝ) < (k : ℝ) + 14 := by positivity
  set a := Real.sqrt ((k : ℝ) + 13) with ha
  set b := Real.sqrt ((k : ℝ) + 14) with hb
  have ha0 : 0 < a := Real.sqrt_pos.mpr h13
  have hb0 : 0 < b := Real.sqrt_pos.mpr h14
  have ha2 : a ^ 2 = (k : ℝ) + 13 := Real.sq_sqrt h13.le
  have hb2 : b ^ 2 = (k : ℝ) + 14 := Real.sq_sqrt h14.le
  have hab : a ≤ b := by rw [ha, hb]; exact Real.sqrt_le_sqrt (by linarith)
  have hgk : g k = 1 / a := by rw [g, ha]
  have hgk1 : g (k + 1) = 1 / b := by
    unfold g
    push_cast
    rw [show ((k : ℝ) + 1 + 13) = (k : ℝ) + 14 by ring, ← hb]
  have hL : b / ((k : ℝ) + 14) ^ 2 = 1 / b ^ 3 := by
    rw [← hb2]
    field_simp
  rw [hL, hgk, hgk1]
  have hba : b - a = 1 / (a + b) := by
    rw [eq_div_iff (by positivity)]
    nlinarith [ha2, hb2]
  have hstep : (1 : ℝ) / a - 1 / b = (b - a) / (a * b) := by
    field_simp
  rw [hstep, hba]
  have hR : 2 * (1 / (a + b) / (a * b)) = 2 / (a * b * (a + b)) := by
    field_simp
  rw [hR]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hab, ha0, hb0, sq_nonneg (b - a)]

/-- **`htail`, discharged.**  `∑_{k < n} (k+14)^{-3/2} ≤ 2/√13 = tailConst`, for every `n`.
No hypothesis, no integral comparison, no `rpow`. -/
theorem powerTail_range (n : ℕ) :
    ∑ k ∈ Finset.range n, Real.sqrt ((k : ℝ) + 14) / ((k : ℝ) + 14) ^ 2 ≤ tailConst := by
  have htel : ∑ k ∈ Finset.range n, (2 * (g k - g (k + 1))) = 2 * (g 0 - g n) := by
    rw [← Finset.mul_sum, Finset.sum_range_sub' g n]
  have h1 : ∑ k ∈ Finset.range n, Real.sqrt ((k : ℝ) + 14) / ((k : ℝ) + 14) ^ 2
      ≤ ∑ k ∈ Finset.range n, (2 * (g k - g (k + 1))) :=
    Finset.sum_le_sum fun k _ => term_le_telescope k
  have hgn : 0 ≤ g n := by
    rw [g]; positivity
  have hg0 : g 0 = 1 / Real.sqrt 13 := by rw [g]; norm_num
  have : 2 * (g 0 - g n) ≤ 2 * g 0 := by linarith
  rw [htel] at h1
  rw [tailConst]
  have : 2 * g 0 = 2 / Real.sqrt 13 := by rw [hg0]; ring
  linarith

end MassBudget
