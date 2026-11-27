/-
Copyright 2026 James C. Kerr (QuantQJ). Apache-2.0.
-/
import Kerr.NumberTheory.PowerfulNumbers.VanDerCorput
import Kerr.NumberTheory.PowerfulNumbers.Sums

/-!
# Sums of `ψ(t) = {t} − 1/2` from exponential sums

New file (written for this repo). With `P(t) = ({t}² − {t} + 1/6)/2 = B₂({t})/2`:

* `psi_ge`, `psi_le`: `(P(t+Δ) − P(t))/Δ − Δ/2 ≤ ψ(t) ≤ (P(t) − P(t−Δ))/Δ + Δ/2` (`0 < Δ ≤ 1`);
* `hasSum_P`: `P(t) = (2π²)⁻¹ ∑_{n ≥ 1} cos(2πnt)/n²` (Mathlib's Fourier series of `B₂`);
* `psi_sum_bound`: if `‖∑_{j∈s} e(h f_j)‖ ≤ A √h + B/√h` for all `h ≥ 1`, then
  `|∑_{j ∈ s} ψ(f_j)| ≤ |s| Δ/2 + 5 A Δ^{−3/4} + 3 B`.
-/

noncomputable section
open Complex Finset Real

namespace Kerr.PowerfulNumbers

/-- `ψ(t) = {t} − 1/2`. -/
def psi (t : ℝ) : ℝ := Int.fract t - 1 / 2

/-- `P(t) = ({t}² − {t} + 1/6)/2`, a bounded antiderivative of `ψ`. -/
def Pb (t : ℝ) : ℝ := (Int.fract t ^ 2 - Int.fract t + 1 / 6) / 2

lemma fract_add_of_lt {t Δ : ℝ} (hΔ : 0 ≤ Δ) (h : Int.fract t + Δ < 1) :
    Int.fract (t + Δ) = Int.fract t + Δ :=
  Int.fract_eq_iff.mpr ⟨by linarith [Int.fract_nonneg t], h, ⌊t⌋, by
    rw [← Int.self_sub_fract t]; ring⟩

lemma fract_add_of_ge {t Δ : ℝ} (hΔ : Δ ≤ 1) (h : 1 ≤ Int.fract t + Δ) :
    Int.fract (t + Δ) = Int.fract t + Δ - 1 :=
  Int.fract_eq_iff.mpr ⟨by linarith, by linarith [Int.fract_lt_one t], ⌊t⌋ + 1, by
    push_cast; rw [← Int.self_sub_fract t]; ring⟩

lemma psi_ge {t Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ ≤ 1) :
    (Pb (t + Δ) - Pb t) / Δ - Δ / 2 ≤ psi t := by
  rw [sub_le_iff_le_add, div_le_iff₀ hΔ0]
  have hs0 := Int.fract_nonneg t
  have hs1 := Int.fract_lt_one t
  rcases lt_or_ge (Int.fract t + Δ) 1 with h | h
  · rw [Pb, Pb, psi, fract_add_of_lt hΔ0.le h]; nlinarith
  · rw [Pb, Pb, psi, fract_add_of_ge hΔ1 h]; nlinarith

lemma psi_le {t Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ ≤ 1) :
    psi t ≤ (Pb t - Pb (t - Δ)) / Δ + Δ / 2 := by
  have h := psi_ge (t := t - Δ) hΔ0 hΔ1
  rw [sub_add_cancel] at h
  have hs0 := Int.fract_nonneg t
  have hs1 := Int.fract_lt_one t
  rw [← sub_le_iff_le_add, le_div_iff₀ hΔ0]
  rcases lt_or_ge (Int.fract t) Δ with h' | h'
  · -- `{t − Δ} = {t} − Δ + 1`
    have hf : Int.fract (t - Δ) = Int.fract t - Δ + 1 :=
      Int.fract_eq_iff.mpr ⟨by linarith, by linarith, ⌊t⌋ - 1, by
        push_cast; rw [← Int.self_sub_fract t]; ring⟩
    rw [Pb, Pb, psi, hf]; nlinarith
  · have hf : Int.fract (t - Δ) = Int.fract t - Δ :=
      Int.fract_eq_iff.mpr ⟨by linarith, by linarith, ⌊t⌋, by
        rw [← Int.self_sub_fract t]; ring⟩
    rw [Pb, Pb, psi, hf]; nlinarith

/-- Fourier series of `P`. -/
theorem hasSum_P (t : ℝ) :
    HasSum (fun n : ℕ => 1 / (2 * π ^ 2) * (1 / (n : ℝ) ^ 2 * Real.cos (2 * π * n * t))) (Pb t) := by
  have hx : Int.fract t ∈ Set.Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  have h := hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero hx
  have hb : (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * 1))).eval (Int.fract t) =
      Int.fract t ^ 2 - Int.fract t + 6⁻¹ := bernoulliFun_two _
  rw [hb] at h
  have hcos : ∀ n : ℕ, Real.cos (2 * π * n * Int.fract t) = Real.cos (2 * π * n * t) := by
    intro n
    have : 2 * π * (n : ℝ) * Int.fract t = 2 * π * n * t - ((n * ⌊t⌋ : ℤ) : ℝ) * (2 * π) := by
      rw [Int.fract]; push_cast; ring
    rw [this, Real.cos_sub_int_mul_two_pi]
  simp only [hcos, mul_one] at h
  have h2 := h.mul_left (1 / (2 * π ^ 2))
  convert h2 using 1
  rw [Pb]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

lemma norm_ee_sub_one_le (θ : ℝ) : ‖ee θ - 1‖ ≤ 2 * π * |θ| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * π * θ)
  rw [ee, show (((2 * π * θ : ℝ) : ℂ) * I) = I * ((2 * π * θ : ℝ) : ℂ) by ring]
  refine h.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]

lemma norm_ee_sub_one_le_two (θ : ℝ) : ‖ee θ - 1‖ ≤ 2 := by
  refine (norm_sub_le _ _).trans ?_
  rw [norm_ee, norm_one]; norm_num

lemma tsum_rpow_neg_le {γ : ℝ} (hγ : 1 < γ) :
    ∑' n : ℕ, (n : ℝ) ^ (-γ) ≤ 1 + 1 / (γ - 1) := by
  refine Real.tsum_le_of_sum_range_le (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _) (fun N => ?_)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp; positivity
  have e : range N ⊆ insert 0 (insert 1 (Ioc 1 N)) := by
    intro n hn
    simp only [mem_range] at hn
    simp only [mem_insert, mem_Ioc]
    omega
  have hle := sum_le_sum_of_subset_of_nonneg (f := fun n : ℕ => (n : ℝ) ^ (-γ)) e
    (fun n _ _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  rw [sum_insert (by simp), sum_insert (by simp)] at hle
  have h1 := sum_Ioc_rpow_neg_le hγ le_rfl N
  simp only [Nat.cast_zero, Nat.cast_one, Real.one_rpow] at hle h1
  rw [Real.zero_rpow (by linarith)] at hle
  linarith

/-- **Key estimate for `P`-differences.** If `‖∑_{j∈s} e(h f_j)‖ ≤ A √h + B/√h` for `h ≥ 1`, then
`|∑_{j∈s} (P(f_j + Δ) − P(f_j))| ≤ Δ (5 A Δ^{−3/4} + 3 B)`. -/
theorem P_diff_sum_bound (f : ℕ → ℝ) (s : Finset ℕ) {Δ : ℝ} (hΔ0 : 0 < Δ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hS : ∀ h : ℕ, 1 ≤ h → ‖∑ j ∈ s, ee (h * f j)‖ ≤ A * Real.sqrt h + B / Real.sqrt h) :
    |∑ j ∈ s, (Pb (f j + Δ) - Pb (f j))| ≤ Δ * (5 * A * Δ ^ (-(3 / 4 : ℝ)) + 3 * B) := by
  set a : ℕ → ℝ := fun n => 1 / (2 * π ^ 2) * (1 / (n : ℝ) ^ 2 *
    ∑ j ∈ s, (Real.cos (2 * π * n * (f j + Δ)) - Real.cos (2 * π * n * f j))) with ha
  have hsum : HasSum a (∑ j ∈ s, (Pb (f j + Δ) - Pb (f j))) := by
    have := hasSum_sum (s := s) (fun j _ => (hasSum_P (f j + Δ)).sub (hasSum_P (f j)))
    convert this using 1
    funext n
    simp only [ha, mul_sum, ← mul_sub]
  -- termwise bound
  have hcos : ∀ n : ℕ, ∑ j ∈ s, (Real.cos (2 * π * n * (f j + Δ)) - Real.cos (2 * π * n * f j)) =
      ((ee (n * Δ) - 1) * ∑ j ∈ s, ee (n * f j)).re := by
    intro n
    rw [sub_mul, mul_sum, one_mul, ← sum_sub_distrib, Complex.re_sum]
    refine sum_congr rfl (fun j _ => ?_)
    rw [← ee_add, Complex.sub_re, ee_eq, ee_eq]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_zero, mul_one, add_zero]
    ring_nf
  have hterm : ∀ n : ℕ, |a n| ≤ Δ * (A * Δ ^ (-(3 / 4 : ℝ)) * (n : ℝ) ^ (-(5 / 4 : ℝ)) +
      B * (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ha]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hSn := hS n hn
    set m := ‖ee (n * Δ) - 1‖ with hm
    have hm0 : 0 ≤ m := norm_nonneg _
    have hm2 : m ≤ 2 := norm_ee_sub_one_le_two _
    have hmΔ : m ≤ 2 * π * (n * Δ) := by
      have := norm_ee_sub_one_le (n * Δ); rwa [abs_of_pos (by positivity)] at this
    have hsq : Real.sqrt n = (n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow n
    have hre : |∑ j ∈ s, (Real.cos (2 * π * n * (f j + Δ)) - Real.cos (2 * π * n * f j))| ≤
        m * (A * (n : ℝ) ^ (1 / 2 : ℝ) + B / (n : ℝ) ^ (1 / 2 : ℝ)) := by
      rw [hcos]
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, ← hsq]
      exact mul_le_mul_of_nonneg_left hSn hm0
    have hπ : 0 < π := Real.pi_pos
    rw [ha, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * π ^ 2)),
      abs_of_pos (by positivity : (0 : ℝ) < 1 / (n : ℝ) ^ 2)]
    -- `m ≤ 2^{3/4} (2π n Δ)^{1/4}` for the `A` part, `m ≤ 2π n Δ` for the `B` part
    have hmA : m ≤ 2 ^ (3 / 4 : ℝ) * (2 * π * (n * Δ)) ^ (1 / 4 : ℝ) := by
      calc m = m ^ (3 / 4 : ℝ) * m ^ (1 / 4 : ℝ) := by
            rw [← Real.rpow_add' hm0 (by norm_num)]; norm_num
        _ ≤ 2 ^ (3 / 4 : ℝ) * (2 * π * (n * Δ)) ^ (1 / 4 : ℝ) := by
            gcongr
    have hAn : 0 ≤ A * (n : ℝ) ^ (1 / 2 : ℝ) := by positivity
    have hBn : 0 ≤ B / (n : ℝ) ^ (1 / 2 : ℝ) := by positivity
    have hc1 : 2 ^ (3 / 4 : ℝ) * (2 * π) ^ (1 / 4 : ℝ) / (2 * π ^ 2) ≤ 1 := by
      have h1 : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 := by
        calc (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2
      have h2 : (2 * π) ^ (1 / 4 : ℝ) ≤ 2 * π := by
        calc (2 * π) ^ (1 / 4 : ℝ) ≤ (2 * π) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by nlinarith [Real.pi_gt_three]) (by norm_num)
          _ = 2 * π := Real.rpow_one _
      rw [div_le_one (by positivity)]
      have : 0 ≤ (2 * π) ^ (1 / 4 : ℝ) := by positivity
      nlinarith [Real.pi_gt_three]
    have hn54 : (1 : ℝ) / (n : ℝ) ^ 2 * (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) =
        (n : ℝ) ^ (-(5 / 4 : ℝ)) := by
      rw [one_div, ← Real.rpow_natCast, ← Real.rpow_neg hn0.le, ← Real.rpow_add hn0,
        ← Real.rpow_add hn0]
      norm_num
    have hΔ14 : Δ * Δ ^ (-(3 / 4 : ℝ)) = Δ ^ (1 / 4 : ℝ) := by
      have e : Δ ^ (1 / 4 : ℝ) = Δ ^ (1 : ℝ) * Δ ^ (-(3 / 4 : ℝ)) := by
        rw [← Real.rpow_add hΔ0]; norm_num
      rw [e, Real.rpow_one]
    have hsplit4 : (2 * π * (n * Δ)) ^ (1 / 4 : ℝ) =
        (2 * π) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ) * Δ ^ (1 / 4 : ℝ) := by
      rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 * π) (by positivity : (0 : ℝ) ≤ (n : ℝ) * Δ),
        Real.mul_rpow (by positivity : (0 : ℝ) ≤ (n : ℝ)) hΔ0.le]
      ring
    have hTA : 1 / (2 * π ^ 2) * (1 / (n : ℝ) ^ 2) *
        (2 ^ (3 / 4 : ℝ) * (2 * π * (n * Δ)) ^ (1 / 4 : ℝ) * A * (n : ℝ) ^ (1 / 2 : ℝ)) ≤
        Δ * (A * Δ ^ (-(3 / 4 : ℝ)) * (n : ℝ) ^ (-(5 / 4 : ℝ))) := by
      rw [hsplit4]
      have hX : 0 ≤ A * (n : ℝ) ^ (-(5 / 4 : ℝ)) * Δ ^ (1 / 4 : ℝ) := by positivity
      calc 1 / (2 * π ^ 2) * (1 / (n : ℝ) ^ 2) *
            (2 ^ (3 / 4 : ℝ) * ((2 * π) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ) * Δ ^ (1 / 4 : ℝ)) *
              A * (n : ℝ) ^ (1 / 2 : ℝ))
          = 2 ^ (3 / 4 : ℝ) * (2 * π) ^ (1 / 4 : ℝ) / (2 * π ^ 2) *
              (A * (1 / (n : ℝ) ^ 2 * (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ)) *
                Δ ^ (1 / 4 : ℝ)) := by ring
        _ = 2 ^ (3 / 4 : ℝ) * (2 * π) ^ (1 / 4 : ℝ) / (2 * π ^ 2) *
              (A * (n : ℝ) ^ (-(5 / 4 : ℝ)) * Δ ^ (1 / 4 : ℝ)) := by rw [hn54]
        _ ≤ 1 * (A * (n : ℝ) ^ (-(5 / 4 : ℝ)) * Δ ^ (1 / 4 : ℝ)) :=
              mul_le_mul_of_nonneg_right hc1 hX
        _ = Δ * (A * Δ ^ (-(3 / 4 : ℝ)) * (n : ℝ) ^ (-(5 / 4 : ℝ))) := by rw [← hΔ14]; ring
    have hn32 : (n : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / ((n : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ)) := by
      rw [Real.rpow_neg hn0.le, ← one_div, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
        Real.rpow_add hn0, Real.rpow_one]
    have hTB : 1 / (2 * π ^ 2) * (1 / (n : ℝ) ^ 2) * (2 * π * (n * Δ) * B / (n : ℝ) ^ (1 / 2 : ℝ)) ≤
        Δ * (B * (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
      have hs0 : 0 < (n : ℝ) ^ (1 / 2 : ℝ) := by positivity
      rw [hn32]
      have e : 1 / (2 * π ^ 2) * (1 / (n : ℝ) ^ 2) * (2 * π * (n * Δ) * B / (n : ℝ) ^ (1 / 2 : ℝ)) =
          1 / π * (Δ * (B * (1 / ((n : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ))))) := by
        field_simp
      rw [e]
      have hY : 0 ≤ Δ * (B * (1 / ((n : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ)))) := by positivity
      have hπ1 : 1 / π ≤ 1 := by rw [div_le_one hπ]; linarith [Real.pi_gt_three]
      nlinarith
    calc 1 / (2 * π ^ 2) * (1 / (n : ℝ) ^ 2 *
          |∑ j ∈ s, (Real.cos (2 * π * n * (f j + Δ)) - Real.cos (2 * π * n * f j))|)
        ≤ 1 / (2 * π ^ 2) * (1 / (n : ℝ) ^ 2 *
            (m * (A * (n : ℝ) ^ (1 / 2 : ℝ) + B / (n : ℝ) ^ (1 / 2 : ℝ)))) := by gcongr
      _ = 1 / (2 * π ^ 2) * (1 / (n : ℝ) ^ 2) * (m * A * (n : ℝ) ^ (1 / 2 : ℝ)) +
          1 / (2 * π ^ 2) * (1 / (n : ℝ) ^ 2) * (m * B / (n : ℝ) ^ (1 / 2 : ℝ)) := by ring
      _ ≤ 1 / (2 * π ^ 2) * (1 / (n : ℝ) ^ 2) *
            (2 ^ (3 / 4 : ℝ) * (2 * π * (n * Δ)) ^ (1 / 4 : ℝ) * A * (n : ℝ) ^ (1 / 2 : ℝ)) +
          1 / (2 * π ^ 2) * (1 / (n : ℝ) ^ 2) * (2 * π * (n * Δ) * B / (n : ℝ) ^ (1 / 2 : ℝ)) := by
          gcongr
      _ ≤ Δ * (A * Δ ^ (-(3 / 4 : ℝ)) * (n : ℝ) ^ (-(5 / 4 : ℝ))) +
          Δ * (B * (n : ℝ) ^ (-(3 / 2 : ℝ))) := add_le_add hTA hTB
      _ = Δ * (A * Δ ^ (-(3 / 4 : ℝ)) * (n : ℝ) ^ (-(5 / 4 : ℝ)) + B * (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
          ring
  -- summing
  set b : ℕ → ℝ := fun n => Δ * (A * Δ ^ (-(3 / 4 : ℝ)) * (n : ℝ) ^ (-(5 / 4 : ℝ)) +
      B * (n : ℝ) ^ (-(3 / 2 : ℝ))) with hb
  have hs54 : Summable (fun n : ℕ => (n : ℝ) ^ (-(5 / 4 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hs32 : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hbs : HasSum b (Δ * (A * Δ ^ (-(3 / 4 : ℝ)) * ∑' n : ℕ, (n : ℝ) ^ (-(5 / 4 : ℝ)) +
      B * ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)))) := by
    have := ((hs54.hasSum.mul_left (A * Δ ^ (-(3 / 4 : ℝ)))).add
      (hs32.hasSum.mul_left B)).mul_left Δ
    simpa [hb, mul_add] using this
  have hup := hasSum_le (fun n => (le_abs_self _).trans (hterm n)) hsum hbs
  have hlo := hasSum_le (fun n => (neg_le_abs (a n)).trans (hterm n)) hsum.neg hbs
  have ht54 := tsum_rpow_neg_le (γ := 5 / 4) (by norm_num)
  have ht32 := tsum_rpow_neg_le (γ := 3 / 2) (by norm_num)
  norm_num at ht54 ht32
  have hfin : Δ * (A * Δ ^ (-(3 / 4 : ℝ)) * ∑' n : ℕ, (n : ℝ) ^ (-(5 / 4 : ℝ)) +
      B * ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))) ≤ Δ * (5 * A * Δ ^ (-(3 / 4 : ℝ)) + 3 * B) := by
    have hAD : 0 ≤ A * Δ ^ (-(3 / 4 : ℝ)) := by positivity
    have e1 : A * Δ ^ (-(3 / 4 : ℝ)) * ∑' n : ℕ, (n : ℝ) ^ (-(5 / 4 : ℝ)) ≤
        A * Δ ^ (-(3 / 4 : ℝ)) * 5 := mul_le_mul_of_nonneg_left (by linarith) hAD
    have e2 : B * ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) ≤ B * 3 :=
      mul_le_mul_of_nonneg_left (by linarith) hB
    nlinarith
  rw [abs_le]
  constructor <;> linarith

/-- **`ψ`-sums from exponential sums.** If `‖∑_{j∈s} e(h f_j)‖ ≤ A √h + B/√h` for all `h ≥ 1`,
then `|∑_{j∈s} ψ(f_j)| ≤ |s| Δ/2 + 5 A Δ^{−3/4} + 3 B` for `0 < Δ ≤ 1`. -/
theorem psi_sum_bound (f : ℕ → ℝ) (s : Finset ℕ) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ ≤ 1)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hS : ∀ h : ℕ, 1 ≤ h → ‖∑ j ∈ s, ee (h * f j)‖ ≤ A * Real.sqrt h + B / Real.sqrt h) :
    |∑ j ∈ s, psi (f j)| ≤ s.card * Δ / 2 + (5 * A * Δ ^ (-(3 / 4 : ℝ)) + 3 * B) := by
  set X := 5 * A * Δ ^ (-(3 / 4 : ℝ)) + 3 * B with hX
  have h1 := P_diff_sum_bound f s hΔ0 hA hB hS
  have hS' : ∀ h : ℕ, 1 ≤ h → ‖∑ j ∈ s, ee (h * (f j - Δ))‖ ≤ A * Real.sqrt h + B / Real.sqrt h := by
    intro h hh
    have e : ∑ j ∈ s, ee (h * (f j - Δ)) = ee (-(h * Δ)) * ∑ j ∈ s, ee (h * f j) := by
      rw [mul_sum]; refine sum_congr rfl (fun j _ => ?_)
      rw [← ee_add]; congr 1; ring
    rw [e, norm_mul, norm_ee, one_mul]; exact hS h hh
  have h2 := P_diff_sum_bound (fun j => f j - Δ) s hΔ0 hA hB hS'
  simp only [sub_add_cancel] at h2
  have hlow : ∑ j ∈ s, ((Pb (f j + Δ) - Pb (f j)) / Δ - Δ / 2) ≤ ∑ j ∈ s, psi (f j) :=
    sum_le_sum (fun j _ => psi_ge hΔ0 hΔ1)
  have hhigh : ∑ j ∈ s, psi (f j) ≤ ∑ j ∈ s, ((Pb (f j) - Pb (f j - Δ)) / Δ + Δ / 2) :=
    sum_le_sum (fun j _ => psi_le hΔ0 hΔ1)
  rw [sum_sub_distrib, ← sum_div, sum_const, nsmul_eq_mul] at hlow
  rw [sum_add_distrib, ← sum_div, sum_const, nsmul_eq_mul] at hhigh
  have hb1 := abs_le.mp h1
  have hb2 := abs_le.mp h2
  have q1 : -X ≤ (∑ j ∈ s, (Pb (f j + Δ) - Pb (f j))) / Δ := by
    rw [le_div_iff₀ hΔ0]; linarith
  have q2 : (∑ j ∈ s, (Pb (f j) - Pb (f j - Δ))) / Δ ≤ X := by
    rw [div_le_iff₀ hΔ0]; linarith
  rw [abs_le]
  constructor <;> nlinarith

end Kerr.PowerfulNumbers
