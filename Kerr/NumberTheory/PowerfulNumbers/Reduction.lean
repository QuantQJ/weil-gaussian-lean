/-
Copyright 2026 James C. Kerr (QuantQJ). Apache-2.0.
`A`, `B`, `ErrorTermImprovement`: statement copied from google-deepmind/formal-conjectures,
`FormalConjectures/Wikipedia/PowerfulNumbersDensity.lean` (commit a425ca3e), Apache-2.0,
© 2026 The Formal Conjectures Authors.
-/
import Kerr.NumberTheory.PowerfulNumbers.Decomposition
import Kerr.NumberTheory.PowerfulNumbers.Sums

/-!
# Reduction: `M(x) = O(x^α)` (`α < 1`) and `Δ_{2,3}(x) = O(x^θ)` (`θ < 1/6`) ⇒ the conjecture

With `Q(x) = ∑_{d ≤ x} μ(d) D(x/d⁶)` (`Q_eq_sum_moebius_D`), `D(t) = ζ(3/2) t^{1/2} + ζ(2/3) t^{1/3}
+ Δ(t)`, split at `d ≤ Y = ⌊x^κ⌋`, `κ = 1/6 − (1−α)/24`:

* `d ≤ Y`: main terms `ζ(3/2) x^{1/2} ∑_{d ≤ Y} μ(d)/d³`, `ζ(2/3) x^{1/3} ∑_{d ≤ Y} μ(d)/d²`, whose
  tails are `O(Y^{α−3})`, `O(Y^{α−2})` (partial summation, `moebius_tail_le`), and the error
  `∑_{d ≤ Y} |Δ(x/d⁶)| ≤ C x^θ Y^{1−6θ}/(1−6θ)`;
* `d > Y`: for each `(a,c)` the `d`-sum is `M(T) − M(Y)`, `T = ⌊(x/(a²c³))^{1/6}⌋`, so the total is
  `≤ 2C x^{α/6} ∑_{a²c³ ≤ x/(Y+1)⁶} (a²c³)^{−α/6} ≤ 6C/(1−α/3) · x^{1/2} (Y+1)^{α−3}`.

All four pieces are `O(x^{1/6 − δ})` with `δ = (1−α)(1−6θ)/24` (`errorTerm_of_bounds`).
The split point `κ` and the value of `δ` are my choices; any `κ` with
`max(1/(3(3−α)), 1/(6(2−α))) < κ < 1/6` works.
-/

noncomputable section
open Finset Real Filter Asymptotics Topology

open scoped ArithmeticFunction.Moebius

namespace Kerr.PowerfulNumbers

/-- (formal-conjectures) `ζ(3/2)/ζ(3)`. -/
noncomputable abbrev A : ℝ := (riemannZeta (3 / 2)).re / (riemannZeta 3).re

/-- (formal-conjectures) `ζ(2/3)/ζ(2)`, `ζ(2/3)` by analytic continuation. -/
noncomputable abbrev B : ℝ := (riemannZeta (2 / 3)).re / (riemannZeta 2).re

/-- (formal-conjectures, `PowerfulNumbersDensity.error_term_improvement`, open) There is `δ > 0`
with `Q(x) − A x^{1/2} − B x^{1/3} = O(x^{1/6−δ})`. -/
def ErrorTermImprovement : Prop :=
  ∃ δ > (0 : ℝ),
    (fun x : ℝ => (Q x : ℝ) - A * x ^ ((1 : ℝ) / 2) - B * x ^ ((1 : ℝ) / 3)) =O[atTop]
      fun x => x ^ ((1 : ℝ) / 6 - δ)

/-- The error term of the `(2,3)` divisor problem, `Δ(t) = D(t) − ζ(3/2) t^{1/2} − ζ(2/3) t^{1/3}`. -/
def Δ23 (t : ℝ) : ℝ :=
  (D t : ℝ) - (riemannZeta (3 / 2)).re * t ^ ((1 : ℝ) / 2) -
    (riemannZeta (2 / 3)).re * t ^ ((1 : ℝ) / 3)

/-- `n ↦ a²c³` as a real number. -/
local notation "nn" p => (((p : ℕ × ℕ).1 ^ 2 * (p : ℕ × ℕ).2 ^ 3 : ℕ) : ℝ)

theorem D_eq_card_of_le {y : ℝ} {M : ℕ} (hM : ⌊y⌋₊ ≤ M) :
    D y = ((Icc 1 M ×ˢ Icc 1 M).filter (fun p : ℕ × ℕ => (nn p) ≤ y)).card := by
  unfold D
  congr 1
  ext ⟨a, c⟩
  simp only [mem_filter, mem_product, mem_Icc]
  constructor
  · rintro ⟨⟨⟨ha1, ha⟩, hc1, hc⟩, hy⟩
    exact ⟨⟨⟨ha1, ha.trans hM⟩, hc1, hc.trans hM⟩, hy⟩
  · rintro ⟨⟨⟨ha1, -⟩, hc1, -⟩, hy⟩
    have hpos : 0 < a ^ 2 * c ^ 3 := by positivity
    have hle : a ^ 2 * c ^ 3 ≤ ⌊y⌋₊ := (Nat.le_floor_iff' hpos.ne').mpr hy
    have hale : a ≤ a ^ 2 * c ^ 3 :=
      le_trans (Nat.le_self_pow (by norm_num) a) (Nat.le_mul_of_pos_right _ (by positivity))
    have hcle : c ≤ a ^ 2 * c ^ 3 :=
      le_trans (Nat.le_self_pow (by norm_num) c) (Nat.le_mul_of_pos_left _ (by positivity))
    exact ⟨⟨⟨ha1, hale.trans hle⟩, hc1, hcle.trans hle⟩, hy⟩

/-- **Lattice-point sum.** `∑_{a²c³ ≤ X} (a²c³)^{−β} ≤ 3/(1−2β) · X^{1/2−β}` for `0 ≤ β < 1/2`. -/
theorem sum_pairs_rpow_le {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β < 1 / 2) (M : ℕ) {X : ℝ} (hX : 0 ≤ X) :
    ∑ p ∈ (Icc 1 M ×ˢ Icc 1 M).filter (fun p : ℕ × ℕ => (nn p) ≤ X), (nn p) ^ (-β) ≤
      3 / (1 - 2 * β) * X ^ (1 / 2 - β) := by
  have h2β : 0 < 1 - 2 * β := by linarith
  rw [sum_filter, sum_product_right]
  -- inner sum for a fixed `c`
  have hinner : ∀ c ∈ Icc 1 M, (∑ a ∈ Icc 1 M,
      if (((a, c) : ℕ × ℕ).1 ^ 2 * ((a, c) : ℕ × ℕ).2 ^ 3 : ℕ) ≤ X then
        ((((a, c) : ℕ × ℕ).1 ^ 2 * ((a, c) : ℕ × ℕ).2 ^ 3 : ℕ) : ℝ) ^ (-β) else 0) ≤
      X ^ (1 / 2 - β) / (1 - 2 * β) * (c : ℝ) ^ (-(3 / 2 : ℝ)) := by
    intro c hc
    have hc1 : 1 ≤ c := (mem_Icc.mp hc).1
    have hc0 : (0 : ℝ) < c := by exact_mod_cast hc1
    have hc3 : (0 : ℝ) < (c : ℝ) ^ 3 := by positivity
    set A := ⌊(X / (c : ℝ) ^ 3) ^ (2 : ℝ)⁻¹⌋₊ with hA
    -- each term
    have hterm : ∀ a : ℕ, 1 ≤ a → ((a ^ 2 * c ^ 3 : ℕ) : ℝ) ^ (-β) =
        (a : ℝ) ^ (-(2 * β)) * (c : ℝ) ^ (-(3 * β)) := by
      intro a ha
      have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
      push_cast
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast_mul ha0.le,
        ← Real.rpow_natCast_mul hc0.le]
      push_cast; ring_nf
    have hsub : ∀ a ∈ Icc 1 M, ((a ^ 2 * c ^ 3 : ℕ) : ℝ) ≤ X → a ∈ Icc 1 A := by
      intro a ha hax
      have ha1 := (mem_Icc.mp ha).1
      refine mem_Icc.mpr ⟨ha1, ?_⟩
      rw [hA, Nat.le_floor_iff (by positivity)]
      have h1 : ((a : ℝ) ^ 2) ≤ X / (c : ℝ) ^ 3 := by
        rw [le_div_iff₀ hc3]; push_cast at hax; exact hax
      have h2 := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
      rwa [show ((a : ℝ) ^ 2) ^ (2 : ℝ)⁻¹ = (a : ℝ) by
        rw [show ((2 : ℝ)⁻¹) = ((2 : ℕ) : ℝ)⁻¹ by norm_num]
        exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)] at h2
    calc (∑ a ∈ Icc 1 M, if (((a, c) : ℕ × ℕ).1 ^ 2 * ((a, c) : ℕ × ℕ).2 ^ 3 : ℕ) ≤ X then
          ((((a, c) : ℕ × ℕ).1 ^ 2 * ((a, c) : ℕ × ℕ).2 ^ 3 : ℕ) : ℝ) ^ (-β) else 0)
        ≤ ∑ a ∈ Icc 1 A, (a : ℝ) ^ (-(2 * β)) * (c : ℝ) ^ (-(3 * β)) := by
          rw [← sum_filter]
          calc _ = ∑ a ∈ (Icc 1 M).filter (fun a : ℕ => ((a ^ 2 * c ^ 3 : ℕ) : ℝ) ≤ X),
                (a : ℝ) ^ (-(2 * β)) * (c : ℝ) ^ (-(3 * β)) := by
                refine sum_congr rfl (fun a ha => ?_)
                simp only [mem_filter, mem_Icc] at ha
                exact hterm a ha.1.1
            _ ≤ _ := sum_le_sum_of_subset_of_nonneg
                (fun a ha => by simp only [mem_filter] at ha; exact hsub a ha.1 ha.2)
                (fun a _ _ => by positivity)
      _ = (c : ℝ) ^ (-(3 * β)) * ∑ a ∈ Icc 1 A, (a : ℝ) ^ (-(2 * β)) := by
          rw [mul_sum]; exact sum_congr rfl (fun a _ => mul_comm _ _)
      _ ≤ (c : ℝ) ^ (-(3 * β)) * ((A : ℝ) ^ (1 - 2 * β) / (1 - 2 * β)) := by
          gcongr; exact sum_Icc_rpow_neg_le (by linarith) (by linarith) A
      _ ≤ (c : ℝ) ^ (-(3 * β)) * (((X / (c : ℝ) ^ 3) ^ (2 : ℝ)⁻¹) ^ (1 - 2 * β) / (1 - 2 * β)) := by
          gcongr
          exact Nat.floor_le (by positivity)
      _ = X ^ (1 / 2 - β) / (1 - 2 * β) * (c : ℝ) ^ (-(3 / 2 : ℝ)) := by
          have key : (c : ℝ) ^ (-(3 * β)) / (c : ℝ) ^ (((3 : ℕ) : ℝ) * (1 / 2 - β)) =
              (c : ℝ) ^ (-(3 / 2 : ℝ)) := by
            rw [← Real.rpow_sub hc0]; push_cast; ring_nf
          rw [← Real.rpow_mul (by positivity), show (2 : ℝ)⁻¹ * (1 - 2 * β) = 1 / 2 - β by ring,
            Real.div_rpow hX hc3.le, show ((c : ℝ) ^ 3) = (c : ℝ) ^ ((3 : ℕ) : ℝ) by
              rw [Real.rpow_natCast], ← Real.rpow_mul hc0.le, ← key]
          ring
  refine (sum_le_sum hinner).trans ?_
  rw [← mul_sum]
  have hsumc : ∑ c ∈ Icc 1 M, (c : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 3 := by
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simp
    rw [Finset.Icc_eq_cons_Ioc hM, sum_cons]
    have h := sum_Ioc_rpow_neg_le (γ := 3 / 2) (by norm_num) le_rfl M
    norm_num at h ⊢
    linarith
  have hpos : 0 ≤ X ^ (1 / 2 - β) / (1 - 2 * β) := div_nonneg (Real.rpow_nonneg hX _) h2β.le
  calc X ^ (1 / 2 - β) / (1 - 2 * β) * ∑ c ∈ Icc 1 M, (c : ℝ) ^ (-(3 / 2 : ℝ))
      ≤ X ^ (1 / 2 - β) / (1 - 2 * β) * 3 := by gcongr
    _ = 3 / (1 - 2 * β) * X ^ (1 / 2 - β) := by ring

/-- `|∑_{d ≤ Y} μ(d)/d^k − 1/ζ(k)| ≤ C(2 + k + k/(k−α)) Y^{α−k}` from `|M(n)| ≤ C n^α`. -/
theorem moebius_partial_sub_inv_zeta {α C : ℝ} (hα1 : α < 1)
    (hM : ∀ n : ℕ, 1 ≤ n → |mert n| ≤ C * (n : ℝ) ^ α) {k : ℕ} (hk : 2 ≤ k) {Y : ℕ}
    (hY : 1 ≤ Y) :
    |∑ d ∈ Icc 1 Y, (μ d : ℝ) / (d : ℝ) ^ k - ((riemannZeta k).re)⁻¹| ≤
      C * (2 + k + k / (k - α)) * (Y : ℝ) ^ (α - k) := by
  set f : ℕ → ℝ := fun d => (μ d : ℝ) / (d : ℝ) ^ k with hf
  have hS := (hasSum_moebius_div_pow hk).tendsto_sum_nat
  have hS1 : Tendsto (fun n => ∑ i ∈ range (n + 1), f i) atTop (𝓝 ((riemannZeta k).re)⁻¹) :=
    (tendsto_add_atTop_iff_nat 1).mpr hS
  have hT : Tendsto (fun n => |∑ d ∈ Icc 1 Y, f d - ∑ i ∈ range (n + 1), f i|) atTop
      (𝓝 |∑ d ∈ Icc 1 Y, f d - ((riemannZeta k).re)⁻¹|) :=
    (continuous_abs.tendsto _).comp (tendsto_const_nhds.sub hS1)
  refine le_of_tendsto hT (eventually_atTop.mpr ⟨Y, fun n hn => ?_⟩)
  have hf0 : f 0 = 0 := by simp [hf]
  have hrange : ∑ i ∈ range (n + 1), f i = ∑ i ∈ Ioc 0 n, f i := by
    rw [range_eq_Ico, Finset.Ico_add_one_right_eq_Icc, Finset.Icc_eq_cons_Ioc (Nat.zero_le n),
      sum_cons, hf0, zero_add]
  have hIcc : ∑ d ∈ Icc 1 Y, f d = ∑ i ∈ Ioc 0 Y, f i := by
    rw [← Finset.Icc_add_one_left_eq_Ioc, zero_add]
  rw [hrange, hIcc, ← Finset.sum_Ioc_consecutive f (Nat.zero_le Y) hn, sub_add_cancel_left,
    abs_neg]
  exact moebius_tail_le hα1 hM hk hY hn

/-- **The `d > Y` part.** `|∑_{Y < d ≤ x} μ(d) D(x/d⁶)| ≤ 2C x^{α/6} ∑_{a²c³ ≤ x/(Y+1)⁶} (a²c³)^{−α/6}`. -/
theorem large_d_bound {α C : ℝ} (hα0 : 0 ≤ α) (hC : 0 ≤ C)
    (hM : ∀ n : ℕ, 1 ≤ n → |mert n| ≤ C * (n : ℝ) ^ α) {x : ℝ} (hx : 1 ≤ x) {Y : ℕ}
    (hY : 1 ≤ Y) :
    |∑ d ∈ Ioc Y ⌊x⌋₊, (μ d : ℝ) * (D (x / (d : ℝ) ^ 6) : ℝ)| ≤
      2 * C * x ^ (α / 6) * ∑ p ∈ (Icc 1 ⌊x⌋₊ ×ˢ Icc 1 ⌊x⌋₊).filter
        (fun p : ℕ × ℕ => (nn p) ≤ x / ((Y : ℝ) + 1) ^ 6), (nn p) ^ (-(α / 6)) := by
  set N := ⌊x⌋₊ with hN
  set PP := Icc 1 N ×ˢ Icc 1 N with hPP
  have hx0 : 0 < x := by linarith
  -- `D(x/d⁶)` as a sum over `PP`
  have hD : ∀ d ∈ Ioc Y N, (D (x / (d : ℝ) ^ 6) : ℝ) =
      ∑ p ∈ PP, if (nn p) ≤ x / (d : ℝ) ^ 6 then (1 : ℝ) else 0 := by
    intro d hd
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (hY.trans (mem_Ioc.mp hd).1.le)
    have hle : ⌊x / (d : ℝ) ^ 6⌋₊ ≤ N := by
      apply Nat.floor_le_floor
      rw [div_le_iff₀ (by positivity)]
      nlinarith [one_le_pow₀ (n := 6) hd1]
    rw [D_eq_card_of_le hle, sum_boole]
  have hswap : ∑ d ∈ Ioc Y N, (μ d : ℝ) * (D (x / (d : ℝ) ^ 6) : ℝ) =
      ∑ p ∈ PP, ∑ d ∈ Ioc Y N, if (nn p) ≤ x / (d : ℝ) ^ 6 then (μ d : ℝ) else 0 := by
    rw [← sum_comm]
    refine sum_congr rfl (fun d hd => ?_)
    rw [hD d hd, mul_sum]
    refine sum_congr rfl (fun p _ => ?_)
    split_ifs <;> simp
  rw [hswap]
  -- each inner sum
  have hinner : ∀ p ∈ PP, |∑ d ∈ Ioc Y N, if (nn p) ≤ x / (d : ℝ) ^ 6 then (μ d : ℝ) else 0| ≤
      if (nn p) ≤ x / ((Y : ℝ) + 1) ^ 6 then 2 * C * x ^ (α / 6) * (nn p) ^ (-(α / 6)) else 0 := by
    intro p hp
    simp only [hPP, mem_product, mem_Icc] at hp
    have hn1 : (1 : ℝ) ≤ nn p := by
      have : 1 ≤ p.1 ^ 2 * p.2 ^ 3 := Nat.one_le_iff_ne_zero.mpr (by
        have := hp.1.1; have := hp.2.1; positivity)
      exact_mod_cast this
    have hn0 : (0 : ℝ) < nn p := by linarith
    set u := x / (nn p) with hu
    have hu0 : 0 < u := div_pos hx0 hn0
    have hux : u ≤ x := div_le_self hx0.le hn1
    set T := ⌊u ^ (6 : ℝ)⁻¹⌋₊ with hT
    -- the filter is `Ioc Y T`
    have hcond : ∀ d : ℕ, ((nn p) ≤ x / (d : ℝ) ^ 6 ∧ 1 ≤ d) ↔ (d ≤ T ∧ 1 ≤ d) := by
      intro d
      constructor
      · rintro ⟨h, hd⟩
        refine ⟨?_, hd⟩
        have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
        have h6 : (d : ℝ) ^ 6 ≤ u := by
          rw [hu, le_div_iff₀ hn0]; rw [le_div_iff₀ (by positivity)] at h; linarith
        rw [hT, Nat.le_floor_iff (by positivity)]
        have := Real.rpow_le_rpow (by positivity) h6 (by norm_num : (0 : ℝ) ≤ (6 : ℝ)⁻¹)
        rwa [show ((d : ℝ) ^ 6) ^ (6 : ℝ)⁻¹ = (d : ℝ) by
          rw [show ((6 : ℝ)⁻¹) = ((6 : ℕ) : ℝ)⁻¹ by norm_num]
          exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)] at this
      · rintro ⟨h, hd⟩
        refine ⟨?_, hd⟩
        have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
        have h1 : (d : ℝ) ≤ u ^ (6 : ℝ)⁻¹ := by
          rw [hT] at h; exact (Nat.le_floor_iff (by positivity)).mp h
        have h6 := pow_le_pow_left₀ hd0.le h1 6
        rw [show (u ^ (6 : ℝ)⁻¹) ^ 6 = u by
          rw [show ((6 : ℝ)⁻¹) = ((6 : ℕ) : ℝ)⁻¹ by norm_num]
          exact Real.rpow_inv_natCast_pow hu0.le (by norm_num)] at h6
        rw [le_div_iff₀ (by positivity)]
        rw [hu, le_div_iff₀ hn0] at h6
        linarith
    have hTN : T ≤ N := by
      apply Nat.floor_le_floor
      rcases le_or_gt u 1 with hu1 | hu1
      · exact (Real.rpow_le_one hu0.le hu1 (by norm_num)).trans hx
      · calc u ^ (6 : ℝ)⁻¹ ≤ u ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu1.le (by norm_num)
          _ = u := Real.rpow_one u
          _ ≤ x := hux
    have hfilter : (Ioc Y N).filter (fun d : ℕ => (nn p) ≤ x / (d : ℝ) ^ 6) = Ioc Y T := by
      ext d
      simp only [mem_filter, mem_Ioc]
      constructor
      · rintro ⟨⟨h1, -⟩, h3⟩
        exact ⟨h1, ((hcond d).mp ⟨h3, by omega⟩).1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, h2.trans hTN⟩, ((hcond d).mpr ⟨h2, by omega⟩).1⟩
    have hnn : 0 ≤ 2 * C * x ^ (α / 6) * (nn p) ^ (-(α / 6)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) (Real.rpow_nonneg hx0.le _))
        (Real.rpow_nonneg hn0.le _)
    rw [← sum_filter, hfilter]
    by_cases hTY : Y < T
    · have hcond' : (nn p) ≤ x / ((Y : ℝ) + 1) ^ 6 := by
        have := ((hcond (Y + 1)).mpr ⟨hTY, by omega⟩).1
        push_cast at this ⊢; exact this
      rw [if_pos hcond']
      have hsplit : ∑ d ∈ Ioc Y T, (μ d : ℝ) = mert T - mert Y := by
        unfold mert; rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le Y) hTY.le]; ring
      rw [hsplit]
      have hT1 : 1 ≤ T := by omega
      have hTr : (T : ℝ) ≤ u ^ (6 : ℝ)⁻¹ := Nat.floor_le (by positivity)
      have hYT : (Y : ℝ) ≤ T := by exact_mod_cast hTY.le
      have hTα : (T : ℝ) ^ α ≤ (u ^ (6 : ℝ)⁻¹) ^ α := Real.rpow_le_rpow (by positivity) hTr hα0
      have hYα : (Y : ℝ) ^ α ≤ (T : ℝ) ^ α := Real.rpow_le_rpow (by positivity) hYT hα0
      have hu6 : (u ^ (6 : ℝ)⁻¹) ^ α = x ^ (α / 6) * (nn p) ^ (-(α / 6)) := by
        rw [← Real.rpow_mul hu0.le, show (6 : ℝ)⁻¹ * α = α / 6 by ring, hu,
          Real.div_rpow hx0.le hn0.le, Real.rpow_neg hn0.le, div_eq_mul_inv]
      calc |mert T - mert Y| ≤ |mert T| + |mert Y| := abs_sub _ _
        _ ≤ C * (T : ℝ) ^ α + C * (Y : ℝ) ^ α := add_le_add (hM T hT1) (hM Y hY)
        _ ≤ 2 * C * (T : ℝ) ^ α := by nlinarith [mul_le_mul_of_nonneg_left hYα hC]
        _ ≤ 2 * C * (u ^ (6 : ℝ)⁻¹) ^ α := mul_le_mul_of_nonneg_left hTα (by linarith)
        _ = 2 * C * x ^ (α / 6) * (nn p) ^ (-(α / 6)) := by rw [hu6]; ring
    · rw [Finset.Ioc_eq_empty (by omega), sum_empty, abs_zero]
      split_ifs
      · exact hnn
      · exact le_rfl
  calc |∑ p ∈ PP, ∑ d ∈ Ioc Y N, if (nn p) ≤ x / (d : ℝ) ^ 6 then (μ d : ℝ) else 0|
      ≤ ∑ p ∈ PP, |∑ d ∈ Ioc Y N, if (nn p) ≤ x / (d : ℝ) ^ 6 then (μ d : ℝ) else 0| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ PP, if (nn p) ≤ x / ((Y : ℝ) + 1) ^ 6 then
          2 * C * x ^ (α / 6) * (nn p) ^ (-(α / 6)) else 0 := sum_le_sum hinner
    _ = _ := by rw [← sum_filter, mul_sum]

lemma rpow_div_pow_six {x : ℝ} (hx : 0 ≤ x) {d : ℕ} (hd : 1 ≤ d) (y : ℝ) :
    (x / (d : ℝ) ^ 6) ^ y = x ^ y * (d : ℝ) ^ (-(6 * y)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [Real.div_rpow hx (by positivity), ← Real.rpow_natCast_mul hd0.le, Real.rpow_neg hd0.le,
    div_eq_mul_inv]
  push_cast; ring_nf

lemma rpow_le_of_half_le {x κ c Y : ℝ} (hx : 1 ≤ x) (hc : c ≤ 0) (hY : x ^ κ / 2 ≤ Y) :
    Y ^ c ≤ 2 ^ (-c) * x ^ (κ * c) := by
  have hx0 : 0 < x := by linarith
  have h1 : 0 < x ^ κ / 2 := by positivity
  calc Y ^ c ≤ (x ^ κ / 2) ^ c := Real.rpow_le_rpow_of_nonpos h1 hY hc
    _ = 2 ^ (-c) * x ^ (κ * c) := by
      rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hx0.le, Real.rpow_neg
        (by norm_num), div_eq_mul_inv]
      ring

lemma exponent_ineq_a {α θ : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hθ0 : 0 ≤ θ) :
    1 / 2 + (1 / 6 - (1 - α) / 24) * (α - 3) ≤ 1 / 6 - (1 - α) * (1 - 6 * θ) / 24 := by
  have h : (1 / 6 - (1 - α) * (1 - 6 * θ) / 24) - (1 / 2 + (1 / 6 - (1 - α) / 24) * (α - 3)) =
      (1 - α) * (α + 6 * θ) / 24 := by ring
  have : 0 ≤ (1 - α) * (α + 6 * θ) / 24 :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
  linarith

lemma exponent_ineq_b {α θ : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hθ0 : 0 ≤ θ) :
    1 / 3 + (1 / 6 - (1 - α) / 24) * (α - 2) ≤ 1 / 6 - (1 - α) * (1 - 6 * θ) / 24 := by
  have h : (1 / 6 - (1 - α) * (1 - 6 * θ) / 24) - (1 / 3 + (1 / 6 - (1 - α) / 24) * (α - 2)) =
      (1 - α) * (1 + α + 6 * θ) / 24 := by ring
  have : 0 ≤ (1 - α) * (1 + α + 6 * θ) / 24 :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
  linarith

lemma exponent_ineq_d {α θ : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hθ0 : 0 ≤ θ) :
    α / 6 + (1 - 6 * (1 / 6 - (1 - α) / 24)) * (1 / 2 - α / 6) ≤
      1 / 6 - (1 - α) * (1 - 6 * θ) / 24 := by
  have h : (1 / 6 - (1 - α) * (1 - 6 * θ) / 24) -
      (α / 6 + (1 - 6 * (1 / 6 - (1 - α) / 24)) * (1 / 2 - α / 6)) =
      (1 - α) * (α + 6 * θ) / 24 := by ring
  have : 0 ≤ (1 - α) * (α + 6 * θ) / 24 :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
  linarith

/-- **Reduction theorem.** If `|M(n)| ≤ C₁ n^α` (`0 ≤ α < 1`) and `|Δ(t)| ≤ C₂ t^θ` for `t ≥ 1`
(`0 ≤ θ < 1/6`), then `Q(x) − A x^{1/2} − B x^{1/3} = O(x^{1/6 − (1−α)(1−6θ)/24})`. -/
theorem errorTerm_of_bounds {α θ C₁ C₂ : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1 / 6) (hM : ∀ n : ℕ, 1 ≤ n → |mert n| ≤ C₁ * (n : ℝ) ^ α)
    (hΔ : ∀ t : ℝ, 1 ≤ t → |Δ23 t| ≤ C₂ * t ^ θ) :
    (fun x : ℝ => (Q x : ℝ) - A * x ^ ((1 : ℝ) / 2) - B * x ^ ((1 : ℝ) / 3)) =O[atTop]
      fun x => x ^ ((1 : ℝ) / 6 - (1 - α) * (1 - 6 * θ) / 24) := by
  have hC₁ : 0 ≤ C₁ := by have := (abs_nonneg _).trans (hM 1 le_rfl); simpa using this
  have hC₂ : 0 ≤ C₂ := by have := (abs_nonneg _).trans (hΔ 1 le_rfl); simpa using this
  set κ : ℝ := 1 / 6 - (1 - α) / 24 with hκ
  set e : ℝ := 1 / 6 - (1 - α) * (1 - 6 * θ) / 24 with he
  set z32 := (riemannZeta (3 / 2)).re with hz32
  set z23 := (riemannZeta (2 / 3)).re with hz23
  set K3 := C₁ * (2 + ((3 : ℕ) : ℝ) + ((3 : ℕ) : ℝ) / (((3 : ℕ) : ℝ) - α)) with hK3
  set K2 := C₁ * (2 + ((2 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) / (((2 : ℕ) : ℝ) - α)) with hK2
  have hK3n : 0 ≤ K3 := by
    have : 0 < 3 - α := by linarith
    refine mul_nonneg hC₁ ?_; push_cast; positivity
  have hK2n : 0 ≤ K2 := by
    have : 0 < 2 - α := by linarith
    refine mul_nonneg hC₁ ?_; push_cast; positivity
  have h6θ : 0 < 1 - 6 * θ := by linarith
  have hβ : 0 < 1 - 2 * (α / 6) := by linarith
  refine IsBigO.of_bound (|z32| * K3 * 2 ^ (3 - α) + |z23| * K2 * 2 ^ (2 - α) +
    C₂ / (1 - 6 * θ) + 2 * C₁ * (3 / (1 - 2 * (α / 6)))) (eventually_atTop.mpr ⟨1, fun x hx => ?_⟩)
  have hx0 : 0 < x := by linarith
  have hxe0 : 0 ≤ x ^ e := Real.rpow_nonneg hx0.le _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hxe0]
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  have hκ1 : κ ≤ 1 / 6 := by rw [hκ]; linarith
  have hxκ : 1 ≤ x ^ κ := Real.one_le_rpow hx hκ0.le
  set N := ⌊x⌋₊ with hN
  set Y := ⌊x ^ κ⌋₊ with hY
  have hY1 : 1 ≤ Y := Nat.le_floor (by simpa using hxκ)
  have hYle : (Y : ℝ) ≤ x ^ κ := Nat.floor_le (by positivity)
  have hYlt : x ^ κ < (Y : ℝ) + 1 := Nat.lt_floor_add_one _
  have hYr1 : (1 : ℝ) ≤ Y := by exact_mod_cast hY1
  have hYhalf : x ^ κ / 2 ≤ Y := by linarith
  have hxκx : x ^ κ ≤ x := by
    calc x ^ κ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
      _ = x := Real.rpow_one x
  have hYN : Y ≤ N := Nat.floor_le_floor hxκx
  -- decomposition
  have hQ : (Q x : ℝ) = ∑ d ∈ Icc 1 Y, (μ d : ℝ) * (D (x / (d : ℝ) ^ 6) : ℝ) +
      ∑ d ∈ Ioc Y N, (μ d : ℝ) * (D (x / (d : ℝ) ^ 6) : ℝ) := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) (Q_eq_sum_moebius_D x)
    push_cast at h
    rw [h, ← hN]
    have e1 : ∀ n : ℕ, Icc 1 n = Ioc 0 n := fun n => by rw [← Finset.Icc_add_one_left_eq_Ioc, zero_add]
    rw [e1, e1, Finset.sum_Ioc_consecutive _ (Nat.zero_le Y) hYN]
  -- the `d ≤ Y` part
  have hS1 : ∑ d ∈ Icc 1 Y, (μ d : ℝ) * (D (x / (d : ℝ) ^ 6) : ℝ) =
      z32 * x ^ ((1 : ℝ) / 2) * ∑ d ∈ Icc 1 Y, (μ d : ℝ) / (d : ℝ) ^ 3 +
      z23 * x ^ ((1 : ℝ) / 3) * ∑ d ∈ Icc 1 Y, (μ d : ℝ) / (d : ℝ) ^ 2 +
      ∑ d ∈ Icc 1 Y, (μ d : ℝ) * Δ23 (x / (d : ℝ) ^ 6) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl (fun d hd => ?_)
    have hd1 : 1 ≤ d := (mem_Icc.mp hd).1
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    have e2 : (x / (d : ℝ) ^ 6) ^ ((1 : ℝ) / 2) = x ^ ((1 : ℝ) / 2) / (d : ℝ) ^ 3 := by
      rw [rpow_div_pow_six hx0.le hd1, show -(6 * ((1 : ℝ) / 2)) = -((3 : ℕ) : ℝ) by norm_num,
        Real.rpow_neg hd0.le, Real.rpow_natCast]; ring
    have e3 : (x / (d : ℝ) ^ 6) ^ ((1 : ℝ) / 3) = x ^ ((1 : ℝ) / 3) / (d : ℝ) ^ 2 := by
      rw [rpow_div_pow_six hx0.le hd1, show -(6 * ((1 : ℝ) / 3)) = -((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_neg hd0.le, Real.rpow_natCast]; ring
    simp only [Δ23, e2, e3, ← hz32, ← hz23]
    field_simp
    ring
  -- tails of the Möbius series
  have hT3 := moebius_partial_sub_inv_zeta hα1 hM (k := 3) (by norm_num) hY1
  have hT2 := moebius_partial_sub_inv_zeta hα1 hM (k := 2) (by norm_num) hY1
  rw [← hK3] at hT3
  rw [← hK2] at hT2
  push_cast at hT3 hT2
  -- the error as four pieces
  have hE : (Q x : ℝ) - A * x ^ ((1 : ℝ) / 2) - B * x ^ ((1 : ℝ) / 3) =
      z32 * x ^ ((1 : ℝ) / 2) * (∑ d ∈ Icc 1 Y, (μ d : ℝ) / (d : ℝ) ^ 3 - ((riemannZeta 3).re)⁻¹) +
      z23 * x ^ ((1 : ℝ) / 3) * (∑ d ∈ Icc 1 Y, (μ d : ℝ) / (d : ℝ) ^ 2 - ((riemannZeta 2).re)⁻¹) +
      ∑ d ∈ Icc 1 Y, (μ d : ℝ) * Δ23 (x / (d : ℝ) ^ 6) +
      ∑ d ∈ Ioc Y N, (μ d : ℝ) * (D (x / (d : ℝ) ^ 6) : ℝ) := by
    rw [hQ, hS1, A, B, ← hz32, ← hz23]; ring
  rw [hE]
  -- piece 1
  have hP1 : |z32 * x ^ ((1 : ℝ) / 2) * (∑ d ∈ Icc 1 Y, (μ d : ℝ) / (d : ℝ) ^ 3 -
      ((riemannZeta 3).re)⁻¹)| ≤ |z32| * K3 * 2 ^ (3 - α) * x ^ e := by
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    have hY3 := rpow_le_of_half_le (c := α - 3) hx (by linarith) hYhalf
    rw [show -(α - 3) = 3 - α by ring] at hY3
    have hexp : 1 / 2 + κ * (α - 3) ≤ e := exponent_ineq_a hα0 hα1 hθ0
    have hx1 : x ^ ((1 : ℝ) / 2) * x ^ (κ * (α - 3)) ≤ x ^ e := by
      rw [← Real.rpow_add hx0]; exact Real.rpow_le_rpow_of_exponent_le hx hexp
    calc |z32| * x ^ ((1 : ℝ) / 2) * |∑ d ∈ Icc 1 Y, (μ d : ℝ) / (d : ℝ) ^ 3 - ((riemannZeta 3).re)⁻¹|
        ≤ |z32| * x ^ ((1 : ℝ) / 2) * (K3 * (Y : ℝ) ^ (α - 3)) := by gcongr
      _ ≤ |z32| * x ^ ((1 : ℝ) / 2) * (K3 * (2 ^ (3 - α) * x ^ (κ * (α - 3)))) := by gcongr
      _ = |z32| * K3 * 2 ^ (3 - α) * (x ^ ((1 : ℝ) / 2) * x ^ (κ * (α - 3))) := by ring
      _ ≤ |z32| * K3 * 2 ^ (3 - α) * x ^ e := by gcongr
  -- piece 2
  have hP2 : |z23 * x ^ ((1 : ℝ) / 3) * (∑ d ∈ Icc 1 Y, (μ d : ℝ) / (d : ℝ) ^ 2 -
      ((riemannZeta 2).re)⁻¹)| ≤ |z23| * K2 * 2 ^ (2 - α) * x ^ e := by
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    have hY2 := rpow_le_of_half_le (c := α - 2) hx (by linarith) hYhalf
    rw [show -(α - 2) = 2 - α by ring] at hY2
    have hexp : 1 / 3 + κ * (α - 2) ≤ e := exponent_ineq_b hα0 hα1 hθ0
    have hx1 : x ^ ((1 : ℝ) / 3) * x ^ (κ * (α - 2)) ≤ x ^ e := by
      rw [← Real.rpow_add hx0]; exact Real.rpow_le_rpow_of_exponent_le hx hexp
    calc |z23| * x ^ ((1 : ℝ) / 3) * |∑ d ∈ Icc 1 Y, (μ d : ℝ) / (d : ℝ) ^ 2 - ((riemannZeta 2).re)⁻¹|
        ≤ |z23| * x ^ ((1 : ℝ) / 3) * (K2 * (Y : ℝ) ^ (α - 2)) := by gcongr
      _ ≤ |z23| * x ^ ((1 : ℝ) / 3) * (K2 * (2 ^ (2 - α) * x ^ (κ * (α - 2)))) := by gcongr
      _ = |z23| * K2 * 2 ^ (2 - α) * (x ^ ((1 : ℝ) / 3) * x ^ (κ * (α - 2))) := by ring
      _ ≤ |z23| * K2 * 2 ^ (2 - α) * x ^ e := by gcongr
  -- piece 3
  have hP3 : |∑ d ∈ Icc 1 Y, (μ d : ℝ) * Δ23 (x / (d : ℝ) ^ 6)| ≤ C₂ / (1 - 6 * θ) * x ^ e := by
    have hterm : ∀ d ∈ Icc 1 Y, |(μ d : ℝ) * Δ23 (x / (d : ℝ) ^ 6)| ≤
        C₂ * x ^ θ * (d : ℝ) ^ (-(6 * θ)) := by
      intro d hd
      have hd1 : 1 ≤ d := (mem_Icc.mp hd).1
      have hdY : (d : ℝ) ≤ Y := by exact_mod_cast (mem_Icc.mp hd).2
      have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
      have hd6 : (d : ℝ) ^ 6 ≤ x := by
        calc (d : ℝ) ^ 6 ≤ (x ^ κ) ^ 6 := by gcongr; exact hdY.trans hYle
          _ = x ^ (κ * 6) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
          _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
          _ = x := Real.rpow_one x
      have ht1 : 1 ≤ x / (d : ℝ) ^ 6 := by rw [le_div_iff₀ (by positivity)]; linarith
      rw [abs_mul]
      have hmu : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      calc |(μ d : ℝ)| * |Δ23 (x / (d : ℝ) ^ 6)| ≤ 1 * (C₂ * (x / (d : ℝ) ^ 6) ^ θ) :=
            mul_le_mul hmu (hΔ _ ht1) (abs_nonneg _) zero_le_one
        _ = C₂ * x ^ θ * (d : ℝ) ^ (-(6 * θ)) := by rw [rpow_div_pow_six hx0.le hd1]; ring
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hterm).trans ?_)
    rw [← mul_sum]
    have hsum := sum_Icc_rpow_neg_le (γ := 6 * θ) (by linarith) (by linarith) Y
    have hYpow : (Y : ℝ) ^ (1 - 6 * θ) ≤ x ^ (κ * (1 - 6 * θ)) := by
      rw [Real.rpow_mul hx0.le]; exact Real.rpow_le_rpow (by positivity) hYle h6θ.le
    have hexp : θ + κ * (1 - 6 * θ) = e := by rw [hκ, he]; ring
    calc C₂ * x ^ θ * ∑ d ∈ Icc 1 Y, (d : ℝ) ^ (-(6 * θ))
        ≤ C₂ * x ^ θ * ((Y : ℝ) ^ (1 - 6 * θ) / (1 - 6 * θ)) := by gcongr
      _ ≤ C₂ * x ^ θ * (x ^ (κ * (1 - 6 * θ)) / (1 - 6 * θ)) := by gcongr
      _ = C₂ / (1 - 6 * θ) * (x ^ θ * x ^ (κ * (1 - 6 * θ))) := by ring
      _ = C₂ / (1 - 6 * θ) * x ^ e := by rw [← Real.rpow_add hx0, hexp]
  -- piece 4
  have hP4 : |∑ d ∈ Ioc Y N, (μ d : ℝ) * (D (x / (d : ℝ) ^ 6) : ℝ)| ≤
      2 * C₁ * (3 / (1 - 2 * (α / 6))) * x ^ e := by
    have h1 := large_d_bound hα0 hC₁ hM hx hY1
    rw [← hN] at h1
    have hX0 : 0 ≤ x / ((Y : ℝ) + 1) ^ 6 := by positivity
    have h2 := sum_pairs_rpow_le (β := α / 6) (by positivity) (by linarith) N hX0
    have hXle : x / ((Y : ℝ) + 1) ^ 6 ≤ x ^ (1 - 6 * κ) := by
      have hx6 : x ^ (6 * κ) = (x ^ κ) ^ 6 := by
        rw [mul_comm, Real.rpow_mul hx0.le, show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast]
      rw [Real.rpow_sub hx0, Real.rpow_one, hx6]
      apply div_le_div_of_nonneg_left hx0.le (by positivity)
      gcongr
    have h3 : (x / ((Y : ℝ) + 1) ^ 6) ^ (1 / 2 - α / 6) ≤ x ^ ((1 - 6 * κ) * (1 / 2 - α / 6)) := by
      rw [Real.rpow_mul hx0.le]
      exact Real.rpow_le_rpow hX0 hXle (by linarith)
    have hexp : α / 6 + (1 - 6 * κ) * (1 / 2 - α / 6) ≤ e := exponent_ineq_d hα0 hα1 hθ0
    have hx4 : x ^ (α / 6) * x ^ ((1 - 6 * κ) * (1 / 2 - α / 6)) ≤ x ^ e := by
      rw [← Real.rpow_add hx0]; exact Real.rpow_le_rpow_of_exponent_le hx hexp
    have hc : 0 ≤ 2 * C₁ * x ^ (α / 6) := by positivity
    calc _ ≤ _ := h1
      _ ≤ 2 * C₁ * x ^ (α / 6) * (3 / (1 - 2 * (α / 6)) * (x / ((Y : ℝ) + 1) ^ 6) ^ (1 / 2 - α / 6)) :=
          mul_le_mul_of_nonneg_left h2 hc
      _ ≤ 2 * C₁ * x ^ (α / 6) * (3 / (1 - 2 * (α / 6)) * x ^ ((1 - 6 * κ) * (1 / 2 - α / 6))) := by
          gcongr
      _ = 2 * C₁ * (3 / (1 - 2 * (α / 6))) * (x ^ (α / 6) * x ^ ((1 - 6 * κ) * (1 / 2 - α / 6))) := by
          ring
      _ ≤ 2 * C₁ * (3 / (1 - 2 * (α / 6))) * x ^ e := by gcongr
  refine le_trans (abs_add_le _ _) ?_
  refine le_trans (add_le_add (abs_add_le _ _) le_rfl) ?_
  refine le_trans (add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl) ?_
  have := add_le_add (add_le_add (add_le_add hP1 hP2) hP3) hP4
  refine this.trans (le_of_eq ?_)
  ring

end Kerr.PowerfulNumbers
