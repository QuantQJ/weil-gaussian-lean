/-
Copyright 2026 James C. Kerr (QuantQJ). Apache-2.0.
-/
import Kerr.NumberTheory.PowerfulNumbers.Block
import Kerr.NumberTheory.PowerfulNumbers.EulerMaclaurin2
import Kerr.NumberTheory.PowerfulNumbers.Reduction

/-!
# The `(2,3)` divisor problem: `Δ(x) = O(x^{3/20})`

New file (written for this repo). With `Z = ⌊x^{1/5}⌋`, `w = x^{1/2} Z^{−3/2}`, `W = ⌊w⌋`:

* `D_hyperbola`: `D(x) = ∑_{c ≤ Z} ⌊(x/c³)^{1/2}⌋ + ∑_{a ≤ W} ⌊(x/a²)^{1/3}⌋ − W Z`;
* `⌊y⌋ = y − 1/2 − ψ(y)`, the main terms by `zeta_partial_sum_approx` (second-order
  Euler–Maclaurin with `ζ(3/2)`, `ζ(2/3)`), the boundary terms cancel up to `O(1)`;
* the two `ψ`-sums by dyadic blocks (`block_psi_mu`, van der Corput's second-derivative test):
  `O(x^{1/7} log x)` and `O(x^{1/10} log x)`.

Result: `divisorBound23_three_twentieths : DivisorBound23 (3/20)` (`3/20 < 1/6`). The exponent
`3/20` (= `1/7 + 1/140`, the `1/140` absorbing `log x`) is my choice; the literature has `2/15`
(Richert 1952) and better.
-/

noncomputable section
open Finset Real

namespace Kerr.PowerfulNumbers

lemma le_rpow_inv_iff_nat {a : ℕ} {y : ℝ} (hy : 0 ≤ y) {k : ℕ} (hk : k ≠ 0) :
    (a : ℝ) ≤ y ^ ((k : ℝ)⁻¹) ↔ (a : ℝ) ^ k ≤ y := by
  rw [Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg a) hy (by positivity), Real.rpow_natCast]

/-- `#{1 ≤ a ≤ M : a² c³ ≤ x} = ⌊(x/c³)^{1/2}⌋` when that is `≤ M`. -/
lemma card_a {x : ℝ} (hx : 0 ≤ x) {c M : ℕ} (hc : 1 ≤ c)
    (hM : ⌊(x / (c : ℝ) ^ 3) ^ ((2 : ℕ) : ℝ)⁻¹⌋₊ ≤ M) :
    ((Icc 1 M).filter (fun a : ℕ => ((a ^ 2 * c ^ 3 : ℕ) : ℝ) ≤ x)).card =
      ⌊(x / (c : ℝ) ^ 3) ^ ((2 : ℕ) : ℝ)⁻¹⌋₊ := by
  have hc0 : (0 : ℝ) < (c : ℝ) ^ 3 := by have : (1 : ℝ) ≤ c := by exact_mod_cast hc
                                         positivity
  have hset : (Icc 1 M).filter (fun a : ℕ => ((a ^ 2 * c ^ 3 : ℕ) : ℝ) ≤ x) =
      Icc 1 ⌊(x / (c : ℝ) ^ 3) ^ ((2 : ℕ) : ℝ)⁻¹⌋₊ := by
    ext a
    simp only [mem_filter, mem_Icc]
    have hiff : ((a ^ 2 * c ^ 3 : ℕ) : ℝ) ≤ x ↔ a ≤ ⌊(x / (c : ℝ) ^ 3) ^ ((2 : ℕ) : ℝ)⁻¹⌋₊ := by
      rw [Nat.le_floor_iff (by positivity), le_rpow_inv_iff_nat (by positivity) (by norm_num),
        le_div_iff₀ hc0]
      push_cast; rfl
    rw [hiff]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans hM⟩, h2⟩
  rw [hset, Nat.card_Icc]; omega

/-- `#{Z < c ≤ M : a² c³ ≤ x} = ⌊(x/a²)^{1/3}⌋ − Z` when `Z ≤ ⌊(x/a²)^{1/3}⌋ ≤ M`. -/
lemma card_c {x : ℝ} (hx : 0 ≤ x) {a Z M : ℕ} (ha : 1 ≤ a)
    (hZ : Z ≤ ⌊(x / (a : ℝ) ^ 2) ^ ((3 : ℕ) : ℝ)⁻¹⌋₊)
    (hM : ⌊(x / (a : ℝ) ^ 2) ^ ((3 : ℕ) : ℝ)⁻¹⌋₊ ≤ M) :
    ((Ioc Z M).filter (fun c : ℕ => ((a ^ 2 * c ^ 3 : ℕ) : ℝ) ≤ x)).card =
      ⌊(x / (a : ℝ) ^ 2) ^ ((3 : ℕ) : ℝ)⁻¹⌋₊ - Z := by
  have ha0 : (0 : ℝ) < (a : ℝ) ^ 2 := by have : (1 : ℝ) ≤ a := by exact_mod_cast ha
                                         positivity
  have hset : (Ioc Z M).filter (fun c : ℕ => ((a ^ 2 * c ^ 3 : ℕ) : ℝ) ≤ x) =
      Ioc Z ⌊(x / (a : ℝ) ^ 2) ^ ((3 : ℕ) : ℝ)⁻¹⌋₊ := by
    ext c
    simp only [mem_filter, mem_Ioc]
    have hiff : ((a ^ 2 * c ^ 3 : ℕ) : ℝ) ≤ x ↔ c ≤ ⌊(x / (a : ℝ) ^ 2) ^ ((3 : ℕ) : ℝ)⁻¹⌋₊ := by
      rw [Nat.le_floor_iff (by positivity), le_rpow_inv_iff_nat (by positivity) (by norm_num),
        le_div_iff₀ ha0]
      push_cast; ring_nf
    rw [hiff]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans hM⟩, h2⟩
  rw [hset, Nat.card_Ioc]

lemma rpow_inv_le_self {y x : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (hx : 1 ≤ x) {k : ℕ} (hk : 1 ≤ k) :
    y ^ ((k : ℝ)⁻¹) ≤ x := by
  have hk' : (0 : ℝ) < (k : ℝ)⁻¹ := by positivity
  have hk1 : (k : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hk)
  rcases le_or_gt y 1 with h | h
  · exact (Real.rpow_le_one hy h hk'.le).trans hx
  · calc y ^ ((k : ℝ)⁻¹) ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h.le hk1
      _ = y := Real.rpow_one y
      _ ≤ x := hyx

/-- **Dirichlet hyperbola for `D`.** For `1 ≤ Z` and `W` with `a ≤ W ↔ a² Z³ ≤ x` (`a ≥ 1`):
`D(x) = ∑_{c ≤ Z} ⌊(x/c³)^{1/2}⌋ + ∑_{a ≤ W} (⌊(x/a²)^{1/3}⌋ − Z)`. -/
theorem D_hyperbola {x : ℝ} (hx : 1 ≤ x) {Z W : ℕ} (hZ : 1 ≤ Z)
    (hZN : Z ≤ ⌊x⌋₊) (hW : ∀ a : ℕ, 1 ≤ a → (a ≤ W ↔ ((a ^ 2 * Z ^ 3 : ℕ) : ℝ) ≤ x)) :
    D x = ∑ c ∈ Icc 1 Z, ⌊(x / (c : ℝ) ^ 3) ^ ((2 : ℕ) : ℝ)⁻¹⌋₊ +
      ∑ a ∈ Icc 1 W, (⌊(x / (a : ℝ) ^ 2) ^ ((3 : ℕ) : ℝ)⁻¹⌋₊ - Z) := by
  set N := ⌊x⌋₊ with hN
  have hx0 : 0 ≤ x := by linarith
  have hlex : ∀ n : ℕ, 1 ≤ n → ((n : ℕ) : ℝ) ≤ x → n ≤ N := fun n hn h =>
    (Nat.le_floor_iff' (by omega)).mpr h
  -- `W ≤ N`
  have hWN : W ≤ N := by
    rcases Nat.eq_zero_or_pos W with h0 | hWpos
    · omega
    have h := (hW W hWpos).mp le_rfl
    refine hlex W hWpos (le_trans ?_ h)
    have : W ≤ W ^ 2 * Z ^ 3 :=
      le_trans (Nat.le_self_pow (by norm_num) W) (Nat.le_mul_of_pos_right _ (by positivity))
    exact_mod_cast this
  have hFle : ∀ c : ℕ, 1 ≤ c → ⌊(x / (c : ℝ) ^ 3) ^ ((2 : ℕ) : ℝ)⁻¹⌋₊ ≤ N := by
    intro c hc
    have hc1 : (1 : ℝ) ≤ (c : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hc)
    exact Nat.floor_le_floor (rpow_inv_le_self (by positivity) (div_le_self hx0 hc1) hx (by norm_num))
  have hGle : ∀ a : ℕ, 1 ≤ a → ⌊(x / (a : ℝ) ^ 2) ^ ((3 : ℕ) : ℝ)⁻¹⌋₊ ≤ N := by
    intro a ha
    have ha1 : (1 : ℝ) ≤ (a : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast ha)
    exact Nat.floor_le_floor (rpow_inv_le_self (by positivity) (div_le_self hx0 ha1) hx (by norm_num))
  unfold D
  rw [← hN, ← card_filter_add_card_filter_not (fun p : ℕ × ℕ => p.2 ≤ Z), filter_filter,
    filter_filter, card_filter, card_filter, sum_product_right, sum_product]
  congr 1
  · -- `c ≤ Z`
    have hsub : Icc 1 Z ⊆ Icc 1 N := fun n hn => by simp only [mem_Icc] at hn ⊢; omega
    trans ∑ c ∈ Icc 1 Z, ∑ a ∈ Icc 1 N,
        (if ((((a, c) : ℕ × ℕ).1 ^ 2 * ((a, c) : ℕ × ℕ).2 ^ 3 : ℕ) : ℝ) ≤ x ∧ ((a, c) : ℕ × ℕ).2 ≤ Z
          then 1 else 0)
    · refine (sum_subset hsub (fun c hc hcZ => sum_eq_zero (fun a _ => ?_))).symm
      simp only [mem_Icc] at hc hcZ
      rw [if_neg]; omega
    refine sum_congr rfl (fun c hc => ?_)
    have hc' := mem_Icc.mp hc
    rw [← card_a hx0 hc'.1 (hFle c hc'.1), card_filter]
    refine sum_congr rfl (fun a _ => ?_)
    simp only [hc'.2, and_true]
  · -- `c > Z`
    have hsub : Icc 1 W ⊆ Icc 1 N := fun n hn => by simp only [mem_Icc] at hn ⊢; omega
    trans ∑ a ∈ Icc 1 W, ∑ c ∈ Icc 1 N,
        (if ((((a, c) : ℕ × ℕ).1 ^ 2 * ((a, c) : ℕ × ℕ).2 ^ 3 : ℕ) : ℝ) ≤ x ∧ ¬((a, c) : ℕ × ℕ).2 ≤ Z
          then 1 else 0)
    · refine (sum_subset hsub (fun a ha haW => sum_eq_zero (fun c _ => ?_))).symm
      simp only [mem_Icc] at ha haW
      rw [if_neg]
      rintro ⟨h1, h2⟩
      have hnot : ¬ a ≤ W := by omega
      apply hnot
      refine (hW a (by omega)).mpr (le_trans ?_ h1)
      have : a ^ 2 * Z ^ 3 ≤ a ^ 2 * c ^ 3 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
      exact_mod_cast this
    refine sum_congr rfl (fun a ha => ?_)
    have ha' := mem_Icc.mp ha
    have hZG : Z ≤ ⌊(x / (a : ℝ) ^ 2) ^ ((3 : ℕ) : ℝ)⁻¹⌋₊ := by
      have h := (hW a ha'.1).mp ha'.2
      have ha0 : (0 : ℝ) < (a : ℝ) ^ 2 := by have : (1 : ℝ) ≤ a := by exact_mod_cast ha'.1
                                             positivity
      rw [Nat.le_floor_iff (by positivity), le_rpow_inv_iff_nat (by positivity) (by norm_num),
        le_div_iff₀ ha0]
      push_cast at h; linarith
    rw [← card_c hx0 ha'.1 hZG (hGle a ha'.1), card_filter]
    have hIoc : Ioc Z N = (Icc 1 N).filter (fun c => ¬ c ≤ Z) := by
      ext c; simp only [mem_Ioc, mem_filter, mem_Icc]; omega
    rw [hIoc, sum_filter]
    refine sum_congr rfl (fun c _ => ?_)
    by_cases h : c ≤ Z <;> simp [h]

/-- **Dyadic decomposition.** For `0 < p ≤ 3/2` there are `K₁, K₂` with, for `C > 0`, `1 ≤ M ≤ Y`,
`|∑_{n ≤ M} ψ(C n^{−p})| ≤ (log₂ M + 1)(K₁ C^{2/7} Y^{1−2(p+2)/7} + K₂ C^{−1/2} Y^{(p+2)/2})`. -/
theorem dyadic_psi {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 3 / 2) : ∃ K₁ K₂ : ℝ, 0 ≤ K₁ ∧ 0 ≤ K₂ ∧
    ∀ C : ℝ, 0 < C → ∀ M : ℕ, ∀ Y : ℝ, 1 ≤ M → (M : ℝ) ≤ Y →
      |∑ n ∈ Icc 1 M, psi (C * (n : ℝ) ^ (-p))| ≤ ((Nat.log 2 M : ℝ) + 1) *
        (K₁ * C ^ (2 / 7 : ℝ) * Y ^ (1 - 2 * (p + 2) / 7) +
          K₂ * C ^ (-(1 / 2 : ℝ)) * Y ^ ((p + 2) / 2)) := by
  obtain ⟨K₁, K₂, hK₁, hK₂, hblock⟩ := block_psi_mu hp
  refine ⟨K₁, K₂, hK₁, hK₂, fun C hC M Y hM hMY => ?_⟩
  set J := Nat.log 2 M with hJ
  set bound := K₁ * C ^ (2 / 7 : ℝ) * Y ^ (1 - 2 * (p + 2) / 7) +
    K₂ * C ^ (-(1 / 2 : ℝ)) * Y ^ ((p + 2) / 2) with hbound
  have hY0 : 0 < Y := lt_of_lt_of_le (by exact_mod_cast hM) hMY
  have hb0 : 0 ≤ bound := by positivity
  have hmaps : ∀ n ∈ Icc 1 M, Nat.log 2 n ∈ range (J + 1) := by
    intro n hn
    simp only [mem_Icc] at hn
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right hn.2))
  rw [← sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ j ∈ range (J + 1),
      |∑ n ∈ (Icc 1 M).filter (fun n => Nat.log 2 n = j), psi (C * (n : ℝ) ^ (-p))| ≤ bound := by
    intro j _
    set S := (Icc 1 M).filter (fun n => Nat.log 2 n = j) with hS
    rcases S.eq_empty_or_nonempty with h0 | hne
    · rw [h0, sum_empty, abs_zero]; exact hb0
    have hmemS : ∀ n ∈ S, (1 ≤ n ∧ n ≤ M) ∧ 2 ^ j ≤ n ∧ n < 2 ^ (j + 1) := by
      intro n hn
      have hn' := mem_filter.mp hn
      have hn1 := (mem_Icc.mp hn'.1)
      refine ⟨hn1, ?_, ?_⟩
      · rw [← hn'.2]; exact Nat.pow_log_le_self 2 (by omega)
      · rw [← hn'.2]; exact Nat.lt_pow_succ_log_self (by norm_num) n
    have hconv : ∀ a ∈ S, ∀ b ∈ S, ∀ n, a ≤ n → n ≤ b → n ∈ S := by
      intro a ha b hb n han hnb
      have ha' := mem_filter.mp ha
      have hb' := mem_filter.mp hb
      have ha1 := mem_Icc.mp ha'.1
      have hb1 := mem_Icc.mp hb'.1
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, le_antisymm ?_ ?_⟩
      · rw [← hb'.2]; exact Nat.log_mono_right hnb
      · rw [← ha'.2]; exact Nat.log_mono_right han
    rw [eq_Icc_of_ordConnected hne hconv]
    have hu := hmemS _ (S.min'_mem hne)
    have hv := hmemS _ (S.max'_mem hne)
    have huv : S.min' hne ≤ S.max' hne := S.min'_le _ (S.max'_mem hne)
    have hN1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    have hv2 : S.max' hne ≤ 2 * 2 ^ j := by have := hv.2.2; rw [pow_succ] at this; omega
    have hb := hblock C hC (2 ^ j) (S.min' hne) (S.max' hne) hN1 hu.2.1 huv hv2
    set N : ℝ := ((2 ^ j : ℕ) : ℝ) with hNdef
    have hN0 : 0 < N := by positivity
    have hNY : N ≤ Y := by
      have : 2 ^ j ≤ M := le_trans hu.2.1 (le_trans huv hv.1.2)
      have : (N : ℝ) ≤ M := by rw [hNdef]; exact_mod_cast this
      linarith
    have e1 : N * (C * N ^ (-p - 2)) ^ (2 / 7 : ℝ) = C ^ (2 / 7 : ℝ) * N ^ (1 - 2 * (p + 2) / 7) := by
      rw [Real.mul_rpow hC.le (by positivity), ← Real.rpow_mul hN0.le,
        show (1 : ℝ) - 2 * (p + 2) / 7 = 1 + (-p - 2) * (2 / 7) by ring, Real.rpow_add hN0,
        Real.rpow_one]
      ring
    have e2 : (C * N ^ (-p - 2)) ^ (-(1 / 2 : ℝ)) = C ^ (-(1 / 2 : ℝ)) * N ^ ((p + 2) / 2) := by
      rw [Real.mul_rpow hC.le (by positivity), ← Real.rpow_mul hN0.le]
      congr 2; ring
    have hexp1 : 0 ≤ 1 - 2 * (p + 2) / 7 := by linarith
    have hexp2 : 0 ≤ (p + 2) / 2 := by linarith
    calc _ ≤ K₁ * N * (C * N ^ (-p - 2)) ^ (2 / 7 : ℝ) + K₂ * (C * N ^ (-p - 2)) ^ (-(1 / 2 : ℝ)) :=
          hb
      _ = K₁ * C ^ (2 / 7 : ℝ) * N ^ (1 - 2 * (p + 2) / 7) +
          K₂ * C ^ (-(1 / 2 : ℝ)) * N ^ ((p + 2) / 2) := by
          rw [mul_assoc K₁, e1, e2]; ring
      _ ≤ bound := by
          rw [hbound]
          gcongr
  calc _ ≤ ∑ j ∈ range (J + 1),
        |∑ n ∈ (Icc 1 M).filter (fun n => Nat.log 2 n = j), psi (C * (n : ℝ) ^ (-p))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range (J + 1), bound := sum_le_sum hfib
    _ = ((J : ℝ) + 1) * bound := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring

lemma natFloor_eq_sub_psi {y : ℝ} (hy : 0 ≤ y) : (⌊y⌋₊ : ℝ) = y - 1 / 2 - psi y := by
  rw [natCast_floor_eq_intCast_floor hy, psi, Int.fract]; ring

/-- `|−2w + 3 w^{2/3} W^{1/3} − W| ≤ 3/w` for `1 ≤ W ≤ w < W + 1`. -/
lemma bracket_T1 {w W : ℝ} (hW1 : 1 ≤ W) (hWw : W ≤ w) (hwW : w < W + 1) :
    |-2 * w + 3 * (w ^ (2 / 3 : ℝ) * W ^ (1 / 3 : ℝ)) - W| ≤ 3 / w := by
  have hw0 : 0 < w := by linarith
  have hW0 : 0 < W := by linarith
  set t := (W / w) ^ (1 / 3 : ℝ) with ht
  have hr0 : 0 < W / w := div_pos hW0 hw0
  have hr1 : W / w ≤ 1 := (div_le_one hw0).mpr hWw
  have ht0 : 0 < t := Real.rpow_pos_of_pos hr0 _
  have ht1 : t ≤ 1 := Real.rpow_le_one hr0.le hr1 (by norm_num)
  have ht3 : t ^ 3 = W / w := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hr0.le]; norm_num
  have hWt : W ^ (1 / 3 : ℝ) = w ^ (1 / 3 : ℝ) * t := by
    rw [ht, ← Real.mul_rpow hw0.le hr0.le]; congr 1; field_simp
  have hww : w ^ (2 / 3 : ℝ) * w ^ (1 / 3 : ℝ) = w := by
    rw [← Real.rpow_add hw0]; norm_num
  have hWeq : W = w * t ^ 3 := by rw [ht3]; field_simp
  have e : -2 * w + 3 * (w ^ (2 / 3 : ℝ) * W ^ (1 / 3 : ℝ)) - W = -(w * ((1 - t) ^ 2 * (t + 2))) := by
    have hwt : w ^ (2 / 3 : ℝ) * (w ^ (1 / 3 : ℝ) * t) = w * t := by rw [← mul_assoc, hww]
    rw [hWt, hwt]
    conv_lhs => rw [hWeq]
    ring
  rw [e, abs_neg, abs_of_nonneg (by positivity)]
  have h1 : 1 - t ≤ 1 - t ^ 3 := by nlinarith [pow_le_one₀ ht0.le ht1 (n := 2)]
  have h2 : 1 - t ^ 3 < 1 / w := by
    rw [ht3, lt_div_iff₀ hw0]; field_simp; linarith
  have h3 : 0 ≤ 1 - t := by linarith
  have h4 : (1 - t) ^ 2 ≤ (1 / w) ^ 2 := by
    have := lt_of_le_of_lt h1 h2
    exact pow_le_pow_left₀ h3 this.le 2
  calc w * ((1 - t) ^ 2 * (t + 2)) ≤ w * ((1 / w) ^ 2 * 3) := by
        gcongr
        · linarith
    _ = 3 / w := by field_simp

/-- **Boundary terms of the hyperbola.** -/
lemma bracket_bound {x Z w W S1 S2 z32 z23 : ℝ} (hZ : 0 < Z) (hW1 : 1 ≤ W) (hWw : W ≤ w)
    (hwW : w < W + 1) (hZw : Z ≤ w) (hw6 : w ≤ 6 * Z)
    (hx12 : x ^ (1 / 2 : ℝ) = w * Z ^ (3 / 2 : ℝ)) (hx13 : x ^ (1 / 3 : ℝ) = w ^ (2 / 3 : ℝ) * Z)
    (hE1 : |S1 - z32 - Z ^ (1 - 3 / 2 : ℝ) / (1 - 3 / 2) - Z ^ (-(3 / 2) : ℝ) / 2| ≤
      3 / 2 * Z ^ (-(3 / 2 + 1) : ℝ) / 8)
    (hE2 : |S2 - z23 - W ^ (1 - 2 / 3 : ℝ) / (1 - 2 / 3) - W ^ (-(2 / 3) : ℝ) / 2| ≤
      2 / 3 * W ^ (-(2 / 3 + 1) : ℝ) / 8) :
    |x ^ (1 / 2 : ℝ) * S1 - Z / 2 + x ^ (1 / 3 : ℝ) * S2 - W / 2 - W * Z - z32 * x ^ (1 / 2 : ℝ) -
      z23 * x ^ (1 / 3 : ℝ)| ≤ 6 := by
  have hw0 : 0 < w := by linarith
  have hW0 : 0 < W := by linarith
  set E1 := S1 - z32 - Z ^ (1 - 3 / 2 : ℝ) / (1 - 3 / 2) - Z ^ (-(3 / 2) : ℝ) / 2 with hE1d
  set E2 := S2 - z23 - W ^ (1 - 2 / 3 : ℝ) / (1 - 2 / 3) - W ^ (-(2 / 3) : ℝ) / 2 with hE2d
  -- the pieces
  have hA1 : x ^ (1 / 2 : ℝ) * (Z ^ (1 - 3 / 2 : ℝ) / (1 - 3 / 2)) = -2 * (w * Z) := by
    rw [hx12, show (1 - 3 / 2 : ℝ) = -(1 / 2) by norm_num]
    have : Z ^ (3 / 2 : ℝ) * Z ^ (-(1 / 2) : ℝ) = Z := by rw [← Real.rpow_add hZ]; norm_num
    rw [show w * Z ^ (3 / 2 : ℝ) * (Z ^ (-(1 / 2) : ℝ) / (-(1 / 2))) =
      -2 * w * (Z ^ (3 / 2 : ℝ) * Z ^ (-(1 / 2) : ℝ)) by ring, this]
    ring
  have hA2 : x ^ (1 / 2 : ℝ) * (Z ^ (-(3 / 2) : ℝ) / 2) = w / 2 := by
    rw [hx12]
    have : Z ^ (3 / 2 : ℝ) * Z ^ (-(3 / 2) : ℝ) = 1 := by rw [← Real.rpow_add hZ]; norm_num
    linear_combination (w / 2) * this
  have hA3 : |x ^ (1 / 2 : ℝ) * E1| ≤ 9 / 8 := by
    rw [abs_mul, abs_of_nonneg (by rw [hx12]; positivity)]
    have hZ52 : Z ^ (3 / 2 : ℝ) * Z ^ (-(3 / 2 + 1) : ℝ) = Z⁻¹ := by
      rw [← Real.rpow_add hZ, ← Real.rpow_neg_one]; norm_num
    calc x ^ (1 / 2 : ℝ) * |E1| ≤ (w * Z ^ (3 / 2 : ℝ)) * (3 / 2 * Z ^ (-(3 / 2 + 1) : ℝ) / 8) := by
          rw [hx12]; gcongr
      _ = 3 / 16 * (w * Z⁻¹) := by rw [← hZ52]; ring
      _ ≤ 3 / 16 * 6 := by
          gcongr
          rw [← div_eq_mul_inv, div_le_iff₀ hZ]; linarith
      _ ≤ 9 / 8 := by norm_num
  have hB1 : x ^ (1 / 3 : ℝ) * (W ^ (1 - 2 / 3 : ℝ) / (1 - 2 / 3)) =
      3 * Z * (w ^ (2 / 3 : ℝ) * W ^ (1 / 3 : ℝ)) := by
    rw [hx13, show (1 - 2 / 3 : ℝ) = 1 / 3 by norm_num]; field_simp
  have hq : w ^ (2 / 3 : ℝ) * W ^ (-(2 / 3) : ℝ) = (w / W) ^ (2 / 3 : ℝ) := by
    rw [Real.div_rpow hw0.le hW0.le, Real.rpow_neg hW0.le]; ring
  have hB2 : x ^ (1 / 3 : ℝ) * (W ^ (-(2 / 3) : ℝ) / 2) = Z / 2 * (w / W) ^ (2 / 3 : ℝ) := by
    rw [hx13, ← hq]; ring
  have hwW1 : 1 ≤ w / W := (le_div_iff₀ hW0).mpr (by linarith)
  have hwW2 : w / W ≤ 2 := (div_le_iff₀ hW0).mpr (by linarith)
  have hq1 : 1 ≤ (w / W) ^ (2 / 3 : ℝ) := Real.one_le_rpow hwW1 (by norm_num)
  have hq2 : (w / W) ^ (2 / 3 : ℝ) ≤ w / W := by
    calc (w / W) ^ (2 / 3 : ℝ) ≤ (w / W) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hwW1 (by norm_num)
      _ = w / W := Real.rpow_one _
  have hB3 : |x ^ (1 / 3 : ℝ) * E2| ≤ 1 / 3 := by
    rw [abs_mul, abs_of_nonneg (by rw [hx13]; positivity)]
    have hW53 : W ^ (-(2 / 3 + 1) : ℝ) = W ^ (-(2 / 3) : ℝ) * W⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hW0]; norm_num
    have hZW : Z / W ≤ 2 := by rw [div_le_iff₀ hW0]; linarith
    calc x ^ (1 / 3 : ℝ) * |E2| ≤ (w ^ (2 / 3 : ℝ) * Z) * (2 / 3 * W ^ (-(2 / 3 + 1) : ℝ) / 8) := by
          rw [hx13]; gcongr
      _ = 1 / 12 * (w ^ (2 / 3 : ℝ) * W ^ (-(2 / 3) : ℝ)) * (Z / W) := by rw [hW53]; ring
      _ ≤ 1 / 12 * 2 * 2 := by rw [hq]; gcongr; linarith
      _ ≤ 1 / 3 := by norm_num
  have hT1 := bracket_T1 hW1 hWw hwW
  have hT1' : |Z * (-2 * w + 3 * (w ^ (2 / 3 : ℝ) * W ^ (1 / 3 : ℝ)) - W)| ≤ 3 := by
    rw [abs_mul, abs_of_pos hZ]
    calc Z * |(-2 * w + 3 * (w ^ (2 / 3 : ℝ) * W ^ (1 / 3 : ℝ)) - W)| ≤ Z * (3 / w) := by gcongr
      _ ≤ 3 := by rw [mul_div_assoc', div_le_iff₀ hw0]; linarith
  have hT3 : |Z / 2 * ((w / W) ^ (2 / 3 : ℝ) - 1)| ≤ 1 := by
    rw [abs_of_nonneg (by have := hq1; positivity)]
    have : (w / W) - 1 ≤ 1 / W := by rw [div_sub_one hW0.ne', div_le_div_iff_of_pos_right hW0]; linarith
    have hZW : Z ≤ 2 * W := by linarith
    calc Z / 2 * ((w / W) ^ (2 / 3 : ℝ) - 1) ≤ Z / 2 * (1 / W) := by gcongr; linarith
      _ ≤ 1 := by rw [div_mul_div_comm, div_le_one (by positivity)]; linarith
  have hexp : x ^ (1 / 2 : ℝ) * S1 - Z / 2 + x ^ (1 / 3 : ℝ) * S2 - W / 2 - W * Z -
      z32 * x ^ (1 / 2 : ℝ) - z23 * x ^ (1 / 3 : ℝ) =
      Z * (-2 * w + 3 * (w ^ (2 / 3 : ℝ) * W ^ (1 / 3 : ℝ)) - W) + (w - W) / 2 +
        Z / 2 * ((w / W) ^ (2 / 3 : ℝ) - 1) + x ^ (1 / 2 : ℝ) * E1 + x ^ (1 / 3 : ℝ) * E2 := by
    have h1 : S1 = E1 + z32 + Z ^ (1 - 3 / 2 : ℝ) / (1 - 3 / 2) + Z ^ (-(3 / 2) : ℝ) / 2 := by
      rw [hE1d]; ring
    have h2 : S2 = E2 + z23 + W ^ (1 - 2 / 3 : ℝ) / (1 - 2 / 3) + W ^ (-(2 / 3) : ℝ) / 2 := by
      rw [hE2d]; ring
    rw [h1, h2]
    linear_combination hA1 + hA2 + hB1 + hB2
  rw [hexp]
  have hT2 : |(w - W) / 2| ≤ 1 / 2 := by
    rw [abs_of_nonneg (by linarith)]; linarith
  calc _ ≤ |Z * (-2 * w + 3 * (w ^ (2 / 3 : ℝ) * W ^ (1 / 3 : ℝ)) - W)| + |(w - W) / 2| +
        |Z / 2 * ((w / W) ^ (2 / 3 : ℝ) - 1)| + |x ^ (1 / 2 : ℝ) * E1| + |x ^ (1 / 3 : ℝ) * E2| := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)
    _ ≤ 3 + 1 / 2 + 1 + 9 / 8 + 1 / 3 := by gcongr
    _ ≤ 6 := by norm_num

lemma log2_bound {M : ℕ} {x : ℝ} (hx : 1 ≤ x) (hM : 1 ≤ M) (hMx : (M : ℝ) ≤ 3 * x) :
    (Nat.log 2 M : ℝ) + 1 ≤ 214 * x ^ (1 / 140 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have h2 : (2 : ℝ) ^ (Nat.log 2 M) ≤ M := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have hlog : (Nat.log 2 M : ℝ) * Real.log 2 ≤ Real.log 3 + Real.log x := by
    rw [← Real.log_pow, ← Real.log_mul (by norm_num) hx0.ne']
    exact Real.log_le_log (by positivity) (h2.trans hMx)
  have hl3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
  have hlx : Real.log x ≤ x ^ (1 / 140 : ℝ) / (1 / 140) := Real.log_le_rpow_div hx0.le (by norm_num)
  have hl2 : (2 : ℝ) / 3 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hx1 : 1 ≤ x ^ (1 / 140 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hJ0 : (0 : ℝ) ≤ Nat.log 2 M := Nat.cast_nonneg _
  have hJ : (Nat.log 2 M : ℝ) * (2 / 3) ≤ 2 + 140 * x ^ (1 / 140 : ℝ) := by
    have : (Nat.log 2 M : ℝ) * (2 / 3) ≤ (Nat.log 2 M : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hl2.le hJ0
    have e : x ^ (1 / 140 : ℝ) / (1 / 140) = 140 * x ^ (1 / 140 : ℝ) := by field_simp
    linarith
  linarith

lemma two_rpow_three_halves_le : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 3 := by
  have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ (3 / 2 : ℝ) := by positivity
  rw [← pow_le_pow_iff_left₀ h0 (by norm_num) (two_ne_zero)]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

set_option maxHeartbeats 1000000 in
/-- **The `(2,3)` divisor problem with exponent `3/20`.** `|Δ(x)| ≤ C x^{3/20}` for `x ≥ 1`. -/
theorem divisor23_bound : ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → |Δ23 x| ≤ C * x ^ (3 / 20 : ℝ) := by
  obtain ⟨Kb1, Kb2, hKb1, hKb2, hdb⟩ := dyadic_psi (p := 3 / 2) (by norm_num) (by norm_num)
  obtain ⟨Ka1, Ka2, hKa1, hKa2, hda⟩ := dyadic_psi (p := 2 / 3) (by norm_num) (by norm_num)
  refine ⟨6 + 214 * (Kb1 + Kb2 + 3 * Ka1 + 9 * Ka2), fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hx15 : 1 ≤ x ^ (1 / 5 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hx15x : x ^ (1 / 5 : ℝ) ≤ x := by
    calc x ^ (1 / 5 : ℝ) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
      _ = x := Real.rpow_one x
  set Z := ⌊x ^ (1 / 5 : ℝ)⌋₊ with hZdef
  have hZ1 : 1 ≤ Z := Nat.le_floor (by simpa using hx15)
  have hZr1 : (1 : ℝ) ≤ Z := by exact_mod_cast hZ1
  have hZ0 : (0 : ℝ) < Z := by linarith
  have hZle : (Z : ℝ) ≤ x ^ (1 / 5 : ℝ) := Nat.floor_le (by positivity)
  have hZlt : x ^ (1 / 5 : ℝ) < Z + 1 := Nat.lt_floor_add_one _
  have hZhalf : x ^ (1 / 5 : ℝ) / 2 ≤ Z := by linarith
  have hZN : Z ≤ ⌊x⌋₊ := Nat.floor_le_floor hx15x
  set w := x ^ (1 / 2 : ℝ) * (Z : ℝ) ^ (-(3 / 2) : ℝ) with hwdef
  have hw_ge : x ^ (1 / 5 : ℝ) ≤ w := by
    have h1 : (x ^ (1 / 5 : ℝ)) ^ (-(3 / 2) : ℝ) ≤ (Z : ℝ) ^ (-(3 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hZ0 hZle (by norm_num)
    have e : x ^ (1 / 2 : ℝ) * (x ^ (1 / 5 : ℝ)) ^ (-(3 / 2) : ℝ) = x ^ (1 / 5 : ℝ) := by
      rw [← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]; norm_num
    rw [← e, hwdef]; gcongr
  have hw_le : w ≤ 3 * x ^ (1 / 5 : ℝ) := by
    have h1 : (Z : ℝ) ^ (-(3 / 2) : ℝ) ≤ (x ^ (1 / 5 : ℝ) / 2) ^ (-(3 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hZhalf (by norm_num)
    have e : x ^ (1 / 2 : ℝ) * (x ^ (1 / 5 : ℝ) / 2) ^ (-(3 / 2) : ℝ) =
        (2 : ℝ) ^ (3 / 2 : ℝ) * x ^ (1 / 5 : ℝ) := by
      rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hx0.le,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul, ← mul_assoc,
        ← Real.rpow_add hx0]
      norm_num; ring
    calc w ≤ x ^ (1 / 2 : ℝ) * (x ^ (1 / 5 : ℝ) / 2) ^ (-(3 / 2) : ℝ) := by rw [hwdef]; gcongr
      _ = (2 : ℝ) ^ (3 / 2 : ℝ) * x ^ (1 / 5 : ℝ) := e
      _ ≤ 3 * x ^ (1 / 5 : ℝ) := by gcongr; exact two_rpow_three_halves_le
  have hw1 : 1 ≤ w := hx15.trans hw_ge
  have hw0 : 0 < w := by linarith
  set W := ⌊w⌋₊ with hWdef
  have hW1 : 1 ≤ W := Nat.le_floor (by simpa using hw1)
  have hWr1 : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hWw : (W : ℝ) ≤ w := Nat.floor_le hw0.le
  have hwW : w < W + 1 := Nat.lt_floor_add_one _
  -- `x^{1/2} = w Z^{3/2}`, `x^{1/3} = w^{2/3} Z`
  have hx12 : x ^ (1 / 2 : ℝ) = w * (Z : ℝ) ^ (3 / 2 : ℝ) := by
    rw [hwdef, mul_assoc, ← Real.rpow_add hZ0]; norm_num
  have hx13 : x ^ (1 / 3 : ℝ) = w ^ (2 / 3 : ℝ) * Z := by
    have hw23 : w ^ (2 / 3 : ℝ) = x ^ (1 / 3 : ℝ) * (Z : ℝ) ^ (-1 : ℝ) := by
      rw [hwdef, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hx0.le,
        ← Real.rpow_mul hZ0.le]
      norm_num
    rw [hw23, Real.rpow_neg_one, mul_assoc, inv_mul_cancel₀ hZ0.ne', mul_one]
  -- hyperbola
  have hWiff : ∀ a : ℕ, 1 ≤ a → (a ≤ W ↔ ((a ^ 2 * Z ^ 3 : ℕ) : ℝ) ≤ x) := by
    intro a _
    have hw2 : w ^ 2 = x / (Z : ℝ) ^ 3 := by
      rw [hwdef, mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast ((Z : ℝ) ^ (-(3 / 2) : ℝ)),
        ← Real.rpow_mul hx0.le, ← Real.rpow_mul hZ0.le]
      norm_num
      exact (div_eq_mul_inv _ _).symm
    rw [hWdef, Nat.le_floor_iff hw0.le, ← pow_le_pow_iff_left₀ (Nat.cast_nonneg a) hw0.le two_ne_zero,
      hw2, le_div_iff₀ (by positivity)]
    push_cast; rfl
  have hD := D_hyperbola hx hZ1 hZN hWiff
  have hFc : ∀ c ∈ Icc 1 Z, (x / (c : ℝ) ^ 3) ^ ((2 : ℕ) : ℝ)⁻¹ =
      x ^ (1 / 2 : ℝ) * (c : ℝ) ^ (-(3 / 2) : ℝ) := by
    intro c hc
    have hc0 : (0 : ℝ) < c := by have := (mem_Icc.mp hc).1; exact_mod_cast this
    rw [Real.div_rpow hx0.le (by positivity), ← Real.rpow_natCast (c : ℝ) 3,
      ← Real.rpow_mul hc0.le, Real.rpow_neg hc0.le, div_eq_mul_inv]
    norm_num
  have hGa : ∀ a ∈ Icc 1 W, (x / (a : ℝ) ^ 2) ^ ((3 : ℕ) : ℝ)⁻¹ =
      x ^ (1 / 3 : ℝ) * (a : ℝ) ^ (-(2 / 3) : ℝ) := by
    intro a ha
    have ha0 : (0 : ℝ) < a := by have := (mem_Icc.mp ha).1; exact_mod_cast this
    rw [Real.div_rpow hx0.le (by positivity), ← Real.rpow_natCast (a : ℝ) 2,
      ← Real.rpow_mul ha0.le, Real.rpow_neg ha0.le, div_eq_mul_inv]
    norm_num
  have hZG : ∀ a ∈ Icc 1 W, Z ≤ ⌊(x / (a : ℝ) ^ 2) ^ ((3 : ℕ) : ℝ)⁻¹⌋₊ := by
    intro a ha
    have ha' := mem_Icc.mp ha
    have h := (hWiff a ha'.1).mp ha'.2
    have ha0 : (0 : ℝ) < (a : ℝ) ^ 2 := by have : (1 : ℝ) ≤ a := by exact_mod_cast ha'.1
                                           positivity
    rw [Nat.le_floor_iff (by positivity), le_rpow_inv_iff_nat (by positivity) (by norm_num),
      le_div_iff₀ ha0]
    push_cast at h; linarith
  set S1 := ∑ c ∈ Icc 1 Z, (c : ℝ) ^ (-(3 / 2) : ℝ) with hS1
  set S2 := ∑ a ∈ Icc 1 W, (a : ℝ) ^ (-(2 / 3) : ℝ) with hS2
  set P1 := ∑ c ∈ Icc 1 Z, psi (x ^ (1 / 2 : ℝ) * (c : ℝ) ^ (-(3 / 2) : ℝ)) with hP1
  set P2 := ∑ a ∈ Icc 1 W, psi (x ^ (1 / 3 : ℝ) * (a : ℝ) ^ (-(2 / 3) : ℝ)) with hP2
  have hsum1 : ∑ c ∈ Icc 1 Z, (⌊(x / (c : ℝ) ^ 3) ^ ((2 : ℕ) : ℝ)⁻¹⌋₊ : ℝ) =
      x ^ (1 / 2 : ℝ) * S1 - Z / 2 - P1 := by
    have h : ∀ c ∈ Icc 1 Z, (⌊(x / (c : ℝ) ^ 3) ^ ((2 : ℕ) : ℝ)⁻¹⌋₊ : ℝ) =
        x ^ (1 / 2 : ℝ) * (c : ℝ) ^ (-(3 / 2) : ℝ) - 1 / 2 -
          psi (x ^ (1 / 2 : ℝ) * (c : ℝ) ^ (-(3 / 2) : ℝ)) := fun c hc => by
      rw [natFloor_eq_sub_psi (by positivity), hFc c hc]
    rw [sum_congr rfl h, sum_sub_distrib, sum_sub_distrib, ← mul_sum, sum_const, Nat.card_Icc,
      nsmul_eq_mul]
    push_cast; ring
  have hsum2 : ∑ a ∈ Icc 1 W, ((⌊(x / (a : ℝ) ^ 2) ^ ((3 : ℕ) : ℝ)⁻¹⌋₊ - Z : ℕ) : ℝ) =
      x ^ (1 / 3 : ℝ) * S2 - W / 2 - P2 - W * Z := by
    have h : ∀ a ∈ Icc 1 W, ((⌊(x / (a : ℝ) ^ 2) ^ ((3 : ℕ) : ℝ)⁻¹⌋₊ - Z : ℕ) : ℝ) =
        x ^ (1 / 3 : ℝ) * (a : ℝ) ^ (-(2 / 3) : ℝ) - 1 / 2 -
          psi (x ^ (1 / 3 : ℝ) * (a : ℝ) ^ (-(2 / 3) : ℝ)) - Z := fun a ha => by
      rw [Nat.cast_sub (hZG a ha), natFloor_eq_sub_psi (by positivity), hGa a ha]
    rw [sum_congr rfl h, sum_sub_distrib, sum_sub_distrib, sum_sub_distrib, ← mul_sum, sum_const,
      sum_const, Nat.card_Icc, nsmul_eq_mul, nsmul_eq_mul]
    push_cast; ring
  have hDr : (D x : ℝ) = x ^ (1 / 2 : ℝ) * S1 - Z / 2 - P1 + (x ^ (1 / 3 : ℝ) * S2 - W / 2 - P2) -
      W * Z := by
    rw [hD, Nat.cast_add, Nat.cast_sum, Nat.cast_sum, hsum1, hsum2]; ring
  -- Euler–Maclaurin
  have hE1 := zeta_partial_sum_approx (s := 3 / 2) (by norm_num) (by norm_num) hZ1
  have hE2 := zeta_partial_sum_approx (s := 2 / 3) (by norm_num) (by norm_num) hW1
  have hc32 : ((3 / 2 : ℝ) : ℂ) = (3 / 2 : ℂ) := by push_cast; ring
  have hc23 : ((2 / 3 : ℝ) : ℂ) = (2 / 3 : ℂ) := by push_cast; ring
  rw [hc32] at hE1
  rw [hc23] at hE2
  have hbr := bracket_bound hZ0 hWr1 hWw hwW (hZle.trans hw_ge)
    (by linarith) hx12 hx13 hE1 hE2
  -- the `ψ`-sums
  have hlogZ := log2_bound hx hZ1 (by linarith)
  have hlogW := log2_bound hx hW1 (by linarith)
  have hP1b := hdb (x ^ (1 / 2 : ℝ)) (by positivity) Z (x ^ (1 / 5 : ℝ)) hZ1 hZle
  have hP2b := hda (x ^ (1 / 3 : ℝ)) (by positivity) W (3 * x ^ (1 / 5 : ℝ)) hW1 (hWw.trans hw_le)
  have hx17 : 1 ≤ x ^ (1 / 7 : ℝ) := Real.one_le_rpow hx (by norm_num)
  have hx107 : x ^ (1 / 10 : ℝ) ≤ x ^ (1 / 7 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have eb1 : (x ^ (1 / 2 : ℝ)) ^ (2 / 7 : ℝ) * (x ^ (1 / 5 : ℝ)) ^ (1 - 2 * (3 / 2 + 2) / 7 : ℝ) =
      x ^ (1 / 7 : ℝ) := by
    rw [← Real.rpow_mul hx0.le, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]; norm_num
  have eb2 : (x ^ (1 / 2 : ℝ)) ^ (-(1 / 2) : ℝ) * (x ^ (1 / 5 : ℝ)) ^ ((3 / 2 + 2) / 2 : ℝ) =
      x ^ (1 / 10 : ℝ) := by
    rw [← Real.rpow_mul hx0.le, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]; norm_num
  have ea1 : (x ^ (1 / 3 : ℝ)) ^ (2 / 7 : ℝ) * (3 * x ^ (1 / 5 : ℝ)) ^ (1 - 2 * (2 / 3 + 2) / 7 : ℝ) =
      (3 : ℝ) ^ (5 / 21 : ℝ) * x ^ (1 / 7 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hx0.le, ← Real.rpow_mul hx0.le]
    norm_num
    rw [mul_left_comm, ← Real.rpow_add hx0]; norm_num
  have ea2 : (x ^ (1 / 3 : ℝ)) ^ (-(1 / 2) : ℝ) * (3 * x ^ (1 / 5 : ℝ)) ^ ((2 / 3 + 2) / 2 : ℝ) =
      (3 : ℝ) ^ (4 / 3 : ℝ) * x ^ (1 / 10 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hx0.le, ← Real.rpow_mul hx0.le]
    norm_num
    rw [mul_left_comm, ← Real.rpow_add hx0]; norm_num
  have h3a : (3 : ℝ) ^ (5 / 21 : ℝ) ≤ 3 := by
    calc (3 : ℝ) ^ (5 / 21 : ℝ) ≤ 3 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 3 := Real.rpow_one 3
  have h3b : (3 : ℝ) ^ (4 / 3 : ℝ) ≤ 9 := by
    calc (3 : ℝ) ^ (4 / 3 : ℝ) ≤ 3 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 9 := by norm_num
  have hP1' : |P1| ≤ 214 * x ^ (1 / 140 : ℝ) * ((Kb1 + Kb2) * x ^ (1 / 7 : ℝ)) := by
    refine hP1b.trans ?_
    have hin : Kb1 * (x ^ (1 / 2 : ℝ)) ^ (2 / 7 : ℝ) * (x ^ (1 / 5 : ℝ)) ^ (1 - 2 * (3 / 2 + 2) / 7 : ℝ) +
        Kb2 * (x ^ (1 / 2 : ℝ)) ^ (-(1 / 2) : ℝ) * (x ^ (1 / 5 : ℝ)) ^ ((3 / 2 + 2) / 2 : ℝ) ≤
        (Kb1 + Kb2) * x ^ (1 / 7 : ℝ) := by
      rw [mul_assoc Kb1, eb1, mul_assoc Kb2, eb2]
      nlinarith [mul_le_mul_of_nonneg_left hx107 hKb2]
    have hin0 : 0 ≤ Kb1 * (x ^ (1 / 2 : ℝ)) ^ (2 / 7 : ℝ) * (x ^ (1 / 5 : ℝ)) ^ (1 - 2 * (3 / 2 + 2) / 7 : ℝ) +
        Kb2 * (x ^ (1 / 2 : ℝ)) ^ (-(1 / 2) : ℝ) * (x ^ (1 / 5 : ℝ)) ^ ((3 / 2 + 2) / 2 : ℝ) := by positivity
    calc _ ≤ 214 * x ^ (1 / 140 : ℝ) * (Kb1 * (x ^ (1 / 2 : ℝ)) ^ (2 / 7 : ℝ) *
          (x ^ (1 / 5 : ℝ)) ^ (1 - 2 * (3 / 2 + 2) / 7 : ℝ) + Kb2 * (x ^ (1 / 2 : ℝ)) ^ (-(1 / 2) : ℝ) *
          (x ^ (1 / 5 : ℝ)) ^ ((3 / 2 + 2) / 2 : ℝ)) := mul_le_mul_of_nonneg_right hlogZ hin0
      _ ≤ _ := by gcongr
  have hP2' : |P2| ≤ 214 * x ^ (1 / 140 : ℝ) * ((3 * Ka1 + 9 * Ka2) * x ^ (1 / 7 : ℝ)) := by
    refine hP2b.trans ?_
    have hin : Ka1 * (x ^ (1 / 3 : ℝ)) ^ (2 / 7 : ℝ) * (3 * x ^ (1 / 5 : ℝ)) ^ (1 - 2 * (2 / 3 + 2) / 7 : ℝ) +
        Ka2 * (x ^ (1 / 3 : ℝ)) ^ (-(1 / 2) : ℝ) * (3 * x ^ (1 / 5 : ℝ)) ^ ((2 / 3 + 2) / 2 : ℝ) ≤
        (3 * Ka1 + 9 * Ka2) * x ^ (1 / 7 : ℝ) := by
      rw [mul_assoc Ka1, ea1, mul_assoc Ka2, ea2]
      have hx70 : 0 ≤ x ^ (1 / 7 : ℝ) := by positivity
      have hx100 : 0 ≤ x ^ (1 / 10 : ℝ) := by positivity
      have h1 : (3 : ℝ) ^ (5 / 21 : ℝ) * x ^ (1 / 7 : ℝ) ≤ 3 * x ^ (1 / 7 : ℝ) :=
        mul_le_mul_of_nonneg_right h3a hx70
      have h2 : (3 : ℝ) ^ (4 / 3 : ℝ) * x ^ (1 / 10 : ℝ) ≤ 9 * x ^ (1 / 7 : ℝ) :=
        mul_le_mul h3b hx107 hx100 (by norm_num)
      have h1' := mul_le_mul_of_nonneg_left h1 hKa1
      have h2' := mul_le_mul_of_nonneg_left h2 hKa2
      linarith
    have hin0 : 0 ≤ Ka1 * (x ^ (1 / 3 : ℝ)) ^ (2 / 7 : ℝ) * (3 * x ^ (1 / 5 : ℝ)) ^ (1 - 2 * (2 / 3 + 2) / 7 : ℝ) +
        Ka2 * (x ^ (1 / 3 : ℝ)) ^ (-(1 / 2) : ℝ) * (3 * x ^ (1 / 5 : ℝ)) ^ ((2 / 3 + 2) / 2 : ℝ) := by positivity
    calc _ ≤ 214 * x ^ (1 / 140 : ℝ) * (Ka1 * (x ^ (1 / 3 : ℝ)) ^ (2 / 7 : ℝ) *
          (3 * x ^ (1 / 5 : ℝ)) ^ (1 - 2 * (2 / 3 + 2) / 7 : ℝ) + Ka2 * (x ^ (1 / 3 : ℝ)) ^ (-(1 / 2) : ℝ) *
          (3 * x ^ (1 / 5 : ℝ)) ^ ((2 / 3 + 2) / 2 : ℝ)) := mul_le_mul_of_nonneg_right hlogW hin0
      _ ≤ _ := by gcongr
  -- assemble
  have hΔ : Δ23 x = (x ^ (1 / 2 : ℝ) * S1 - Z / 2 + x ^ (1 / 3 : ℝ) * S2 - W / 2 - W * Z -
      (riemannZeta (3 / 2)).re * x ^ (1 / 2 : ℝ) - (riemannZeta (2 / 3)).re * x ^ (1 / 3 : ℝ)) -
      P1 - P2 := by
    rw [Δ23, hDr]; ring
  have hx320 : x ^ (1 / 140 : ℝ) * x ^ (1 / 7 : ℝ) = x ^ (3 / 20 : ℝ) := by
    rw [← Real.rpow_add hx0]; norm_num
  have hx320' : 1 ≤ x ^ (3 / 20 : ℝ) := Real.one_le_rpow hx (by norm_num)
  rw [hΔ]
  calc _ ≤ |x ^ (1 / 2 : ℝ) * S1 - Z / 2 + x ^ (1 / 3 : ℝ) * S2 - W / 2 - W * Z -
        (riemannZeta (3 / 2)).re * x ^ (1 / 2 : ℝ) - (riemannZeta (2 / 3)).re * x ^ (1 / 3 : ℝ)| +
        |P1| + |P2| := by
        refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans le_rfl) le_rfl)
    _ ≤ 6 + 214 * x ^ (1 / 140 : ℝ) * ((Kb1 + Kb2) * x ^ (1 / 7 : ℝ)) +
        214 * x ^ (1 / 140 : ℝ) * ((3 * Ka1 + 9 * Ka2) * x ^ (1 / 7 : ℝ)) := by gcongr
    _ = 6 + 214 * (Kb1 + Kb2 + 3 * Ka1 + 9 * Ka2) * (x ^ (1 / 140 : ℝ) * x ^ (1 / 7 : ℝ)) := by ring
    _ ≤ (6 + 214 * (Kb1 + Kb2 + 3 * Ka1 + 9 * Ka2)) * x ^ (3 / 20 : ℝ) := by
        rw [hx320]
        have : 0 ≤ 214 * (Kb1 + Kb2 + 3 * Ka1 + 9 * Ka2) := by positivity
        nlinarith

end Kerr.PowerfulNumbers
