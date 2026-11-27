/-
Copyright 2026 James C. Kerr (QuantQJ). Apache-2.0.
-/
import Mathlib

/-!
# Elementary sums for the powerful-numbers reduction

* `sum_Ioc_rpow_neg_le`: `∑_{m < n ≤ M} n^{-γ} ≤ m^{1-γ}/(γ-1)` (`γ > 1`, `m ≥ 1`).
* `sum_Icc_rpow_neg_le`: `∑_{1 ≤ n ≤ N} n^{-γ} ≤ N^{1-γ}/(1-γ)` (`0 ≤ γ < 1`).
* `abel_moebius`: discrete partial summation against `mert n = ∑_{0<k≤n} μ(k)`.
* `moebius_tail_le`: if `|mert n| ≤ C n^α` (`0 ≤ α < 1`), then
  `|∑_{Y < d ≤ Z} μ(d)/d^k| ≤ C (2 + k + k/(k-α)) Y^{α-k}` for `k ≥ 2`.
* `hasSum_moebius_div_pow`: `∑ μ(d)/d^k = 1/ζ(k)` (`k ≥ 2`).
-/

noncomputable section
open Finset Real Filter Topology

open scoped ArithmeticFunction.Moebius

namespace Kerr.PowerfulNumbers

lemma antitoneOn_rpow_neg {γ : ℝ} (hγ : 0 ≤ γ) {a b : ℝ} (ha : 0 < a) :
    AntitoneOn (fun t : ℝ => t ^ (-γ)) (Set.Icc a b) := by
  intro s hs t ht hst
  exact Real.rpow_le_rpow_of_nonpos (by linarith [hs.1]) hst (by linarith)

lemma sum_Ioc_eq_sum_Ico_succ (f : ℕ → ℝ) (m M : ℕ) :
    ∑ n ∈ Ioc m M, f n = ∑ i ∈ Ico m M, f (i + 1) := by
  rw [Finset.sum_Ico_add' (f := f) (c := 1), Finset.Ico_add_one_right_eq_Icc,
    Finset.Icc_add_one_left_eq_Ioc]

theorem sum_Ioc_rpow_neg_le {γ : ℝ} (hγ : 1 < γ) {m : ℕ} (hm : 1 ≤ m) (M : ℕ) :
    ∑ n ∈ Ioc m M, (n : ℝ) ^ (-γ) ≤ (m : ℝ) ^ (1 - γ) / (γ - 1) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hpos : 0 ≤ (m : ℝ) ^ (1 - γ) / (γ - 1) :=
    div_nonneg (Real.rpow_nonneg hm0.le _) (by linarith)
  rcases le_or_gt M m with hMm | hmM
  · rw [Finset.Ioc_eq_empty (by omega), sum_empty]; exact hpos
  rw [sum_Ioc_eq_sum_Ico_succ (fun n : ℕ => (n : ℝ) ^ (-γ))]
  have h := AntitoneOn.sum_le_integral_Ico (f := fun t : ℝ => t ^ (-γ)) hmM.le
    (antitoneOn_rpow_neg (by linarith) hm0)
  refine h.trans ?_
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  rw [integral_rpow (Or.inr ⟨by linarith, by
    rw [Set.uIcc_of_le (by exact_mod_cast hmM.le)]; intro h0; linarith [h0.1]⟩)]
  have e : -γ + 1 = 1 - γ := by ring
  rw [e]
  have hMpow : 0 ≤ (M : ℝ) ^ (1 - γ) := Real.rpow_nonneg hM0.le _
  have hg : 0 < γ - 1 := by linarith
  have e2 : ((M : ℝ) ^ (1 - γ) - (m : ℝ) ^ (1 - γ)) / (1 - γ) =
      ((m : ℝ) ^ (1 - γ) - (M : ℝ) ^ (1 - γ)) / (γ - 1) := by
    rw [div_eq_div_iff (by linarith) (by linarith)]; ring
  rw [e2]
  exact div_le_div_of_nonneg_right (by linarith) hg.le

theorem sum_Icc_rpow_neg_le {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (N : ℕ) :
    ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-γ) ≤ (N : ℝ) ^ (1 - γ) / (1 - γ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [Real.zero_rpow (by linarith : (1 - γ) ≠ 0)]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hfi : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-γ)) (Set.Icc (0 : ℝ) (0 + N)) := by
    rw [zero_add, integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegral.intervalIntegrable_rpow' (r := -γ) (by linarith) (a := 0) (b := N)).1
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-γ)) (Set.Ioc (0 : ℝ) (0 + N)) := by
    intro s hs t ht hst
    exact Real.rpow_le_rpow_of_nonpos hs.1 hst (by linarith)
  have h := AntitoneOn.sum_le_integral_of_integrableOn hanti hfi
  simp only [zero_add] at h
  have e : ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-γ) = ∑ i ∈ range N, ((i + 1 : ℕ) : ℝ) ^ (-γ) := by
    rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (f := fun n : ℕ => (n : ℝ) ^ (-γ)) (c := 1),
      zero_add, Finset.Ico_add_one_right_eq_Icc]
  rw [e]
  refine h.trans (le_of_eq ?_)
  rw [integral_rpow (Or.inl (by linarith)), Real.zero_rpow (by linarith)]
  ring_nf

/-- `mert n = ∑_{0 < k ≤ n} μ(k)` (the Mertens function at integers). -/
def mert (n : ℕ) : ℝ := ∑ k ∈ Ioc 0 n, (μ k : ℝ)

lemma mert_succ (n : ℕ) : mert (n + 1) = mert n + μ (n + 1) := by
  unfold mert; rw [Finset.sum_Ioc_succ_top (Nat.zero_le n)]

/-- **Discrete partial summation.**
`∑_{Y < d ≤ Z} μ(d) w(d) = M(Z) w(Z) − M(Y) w(Y) + ∑_{Y ≤ d < Z} M(d) (w(d) − w(d+1))`. -/
theorem abel_moebius (w : ℕ → ℝ) {Y Z : ℕ} (hYZ : Y ≤ Z) :
    ∑ d ∈ Ioc Y Z, (μ d : ℝ) * w d =
      mert Z * w Z - mert Y * w Y + ∑ d ∈ Ico Y Z, mert d * (w d - w (d + 1)) := by
  induction Z, hYZ using Nat.le_induction with
  | base => simp
  | succ Z hYZ ih =>
    rw [Finset.sum_Ioc_succ_top hYZ, ih, Finset.sum_Ico_succ_top hYZ, mert_succ]
    push_cast; ring

lemma inv_pow_sub_inv_pow_le (k : ℕ) {d : ℝ} (hd : 1 ≤ d) :
    1 / d ^ k - 1 / (d + 1) ^ k ≤ k / d ^ (k + 1) := by
  have hd0 : 0 < d := by linarith
  have hd1 : 0 < d + 1 := by linarith
  have hb := one_add_mul_le_pow (a := -1 / (d + 1)) (by
    rw [neg_div, neg_le_neg_iff, div_le_iff₀ hd1]; linarith) k
  have e1 : 1 + -1 / (d + 1) = d / (d + 1) := by field_simp; ring
  rw [e1, div_pow] at hb
  set u := d ^ k / (d + 1) ^ k with hu
  have hdk : 0 < d ^ k := pow_pos hd0 k
  have e2 : 1 / (d + 1) ^ k = u / d ^ k := by rw [hu]; field_simp
  rw [e2, ← sub_div]
  have h3 : 1 - u ≤ k / (d + 1) := by
    have : (k : ℝ) * (-1 / (d + 1)) = -(k / (d + 1)) := by ring
    linarith
  have h4 : (k : ℝ) / (d + 1) ≤ k / d :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg k) hd0 (by linarith)
  calc (1 - u) / d ^ k ≤ (k / d) / d ^ k := by gcongr; linarith
    _ = k / d ^ (k + 1) := by rw [pow_succ]; field_simp

/-- **Tail of `∑ μ(d)/d^k`** from a bound `|M(n)| ≤ C n^α`, `0 ≤ α < 1`, `k ≥ 2`. -/
theorem moebius_tail_le {α C : ℝ} (hα1 : α < 1)
    (hM : ∀ n : ℕ, 1 ≤ n → |mert n| ≤ C * (n : ℝ) ^ α) {k : ℕ} (hk : 2 ≤ k)
    {Y Z : ℕ} (hY : 1 ≤ Y) (hYZ : Y ≤ Z) :
    |∑ d ∈ Ioc Y Z, (μ d : ℝ) / (d : ℝ) ^ k| ≤
      C * (2 + k + k / (k - α)) * (Y : ℝ) ^ (α - k) := by
  have hC : 0 ≤ C := by
    have := (abs_nonneg _).trans (hM 1 le_rfl); simpa using this
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
  have hYr : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  -- rpow bookkeeping: `n^α / n^j = n^(α - j)`
  have hdiv : ∀ n : ℕ, 1 ≤ n → ∀ j : ℕ, (n : ℝ) ^ α / (n : ℝ) ^ j = (n : ℝ) ^ (α - j) := by
    intro n hn j
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [Real.rpow_sub hn0, Real.rpow_natCast]
  have hmono : ∀ n : ℕ, Y ≤ n → (n : ℝ) ^ (α - k) ≤ (Y : ℝ) ^ (α - k) := by
    intro n hn
    exact Real.rpow_le_rpow_of_nonpos hY0 (by exact_mod_cast hn) (by linarith)
  have hsplit := abel_moebius (fun d => 1 / (d : ℝ) ^ k) hYZ
  simp only [mul_one_div] at hsplit
  rw [hsplit]
  -- the two boundary terms
  have hb1 : |mert Z / (Z : ℝ) ^ k| ≤ C * (Y : ℝ) ^ (α - k) := by
    have hZ : 1 ≤ Z := hY.trans hYZ
    have hZ0 : (0 : ℝ) < Z := by exact_mod_cast hZ
    rw [abs_div, abs_of_pos (pow_pos hZ0 k)]
    calc |mert Z| / (Z : ℝ) ^ k ≤ C * (Z : ℝ) ^ α / (Z : ℝ) ^ k := by
          gcongr; exact hM Z hZ
      _ = C * (Z : ℝ) ^ (α - k) := by rw [mul_div_assoc, hdiv Z hZ k]
      _ ≤ C * (Y : ℝ) ^ (α - k) := mul_le_mul_of_nonneg_left (hmono Z hYZ) hC
  have hb2 : |mert Y / (Y : ℝ) ^ k| ≤ C * (Y : ℝ) ^ (α - k) := by
    rw [abs_div, abs_of_pos (pow_pos hY0 k)]
    calc |mert Y| / (Y : ℝ) ^ k ≤ C * (Y : ℝ) ^ α / (Y : ℝ) ^ k := by
          gcongr; exact hM Y hY
      _ = C * (Y : ℝ) ^ (α - k) := by rw [mul_div_assoc, hdiv Y hY k]
  -- the middle sum
  have hterm : ∀ d ∈ Ico Y Z, |mert d * (1 / (d : ℝ) ^ k - 1 / ((d + 1 : ℕ) : ℝ) ^ k)| ≤
      C * k * (d : ℝ) ^ (-(k + 1 - α)) := by
    intro d hd
    have hd1 : 1 ≤ d := hY.trans (mem_Ico.mp hd).1
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    have hw := inv_pow_sub_inv_pow_le k hdr
    have hw0 : 0 ≤ 1 / (d : ℝ) ^ k - 1 / ((d : ℝ) + 1) ^ k := by
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le (by positivity) (by gcongr; linarith)
    push_cast
    rw [abs_mul, abs_of_nonneg hw0]
    calc |mert d| * (1 / (d : ℝ) ^ k - 1 / ((d : ℝ) + 1) ^ k)
        ≤ (C * (d : ℝ) ^ α) * (k / (d : ℝ) ^ (k + 1)) :=
          mul_le_mul (hM d hd1) hw hw0 (mul_nonneg hC (Real.rpow_nonneg hd0.le _))
      _ = C * k * ((d : ℝ) ^ α / (d : ℝ) ^ (k + 1)) := by ring
      _ = C * k * (d : ℝ) ^ (-(k + 1 - α)) := by
          rw [hdiv d hd1 (k + 1)]; push_cast; ring_nf
  have hmid : |∑ d ∈ Ico Y Z, mert d * (1 / (d : ℝ) ^ k - 1 / ((d + 1 : ℕ) : ℝ) ^ k)| ≤
      C * k * (1 + 1 / (k - α)) * (Y : ℝ) ^ (α - k) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (sum_le_sum hterm).trans ?_
    rw [← mul_sum]
    have hsub : Ico Y Z ⊆ Icc Y Z := Ico_subset_Icc_self
    have hnn : ∀ d ∈ Icc Y Z, 0 ≤ (d : ℝ) ^ (-(k + 1 - α) : ℝ) := fun d _ => Real.rpow_nonneg (Nat.cast_nonneg d) _
    have h1 := sum_le_sum_of_subset_of_nonneg hsub (fun d hd _ => hnn d hd)
    rw [Finset.Icc_eq_cons_Ioc hYZ, sum_cons] at h1
    have h2 := sum_Ioc_rpow_neg_le (γ := k + 1 - α) (by linarith) hY Z
    have e3 : (Y : ℝ) ^ (-(k + 1 - α) : ℝ) ≤ (Y : ℝ) ^ (α - k) :=
      Real.rpow_le_rpow_of_exponent_le hYr (by linarith)
    have e4 : (Y : ℝ) ^ (1 - (k + 1 - α)) = (Y : ℝ) ^ (α - k) := by ring_nf
    rw [e4] at h2
    have hpow : 0 ≤ (Y : ℝ) ^ (α - k) := Real.rpow_nonneg hY0.le _
    have hka : 0 < (k : ℝ) - α := by linarith
    have e5 : (Y : ℝ) ^ (α - k) / (k + 1 - α - 1) = 1 / (k - α) * (Y : ℝ) ^ (α - k) := by
      rw [show (k : ℝ) + 1 - α - 1 = k - α by ring]; ring
    rw [e5] at h2
    have hCk : 0 ≤ C * k := by positivity
    calc C * k * ∑ d ∈ Ico Y Z, (d : ℝ) ^ (-(k + 1 - α))
        ≤ C * k * ((Y : ℝ) ^ (α - k) + 1 / (k - α) * (Y : ℝ) ^ (α - k)) := by
          gcongr; linarith
      _ = C * k * (1 + 1 / (k - α)) * (Y : ℝ) ^ (α - k) := by ring
  have htri : |mert Z / (Z : ℝ) ^ k - mert Y / (Y : ℝ) ^ k +
      ∑ d ∈ Ico Y Z, mert d * (1 / (d : ℝ) ^ k - 1 / ((d + 1 : ℕ) : ℝ) ^ k)| ≤
      C * (Y : ℝ) ^ (α - k) + C * (Y : ℝ) ^ (α - k) +
        C * k * (1 + 1 / (k - α)) * (Y : ℝ) ^ (α - k) := by
    refine (abs_add_le _ _).trans ?_
    refine add_le_add ((abs_sub _ _).trans (add_le_add hb1 hb2)) hmid
  refine htri.trans (le_of_eq ?_)
  have hka : (k : ℝ) - α ≠ 0 := by linarith
  field_simp
  ring

/-- `∑_{d ≥ 1} μ(d)/d^k = ζ(k)⁻¹` (real form), `k ≥ 2`. -/
theorem hasSum_moebius_div_pow {k : ℕ} (hk : 2 ≤ k) :
    HasSum (fun d : ℕ => (μ d : ℝ) / (d : ℝ) ^ k) ((riemannZeta k).re)⁻¹ := by
  have hs : 1 < (k : ℂ).re := by simp; exact_mod_cast hk
  have hL := (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs).LSeriesHasSum
  have hinv : LSeries (fun n => (μ n : ℂ)) k = (riemannZeta k)⁻¹ := by
    have h := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
    rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at h
    exact (eq_inv_of_mul_eq_one_right h)
  rw [hinv] at hL
  have hreal : riemannZeta k = ((∑' n : ℕ, 1 / (n : ℝ) ^ k : ℝ) : ℂ) := by
    rw [zeta_nat_eq_tsum_of_gt_one (by omega), Complex.ofReal_tsum]
    push_cast; rfl
  have hterm : ∀ n : ℕ, LSeries.term (fun n => (μ n : ℂ)) k n = (((μ n : ℝ) / (n : ℝ) ^ k : ℝ) : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn.ne']
      push_cast
      rw [Complex.cpow_natCast]
  have h2 : HasSum (fun n : ℕ => ((((μ n : ℝ) / (n : ℝ) ^ k : ℝ)) : ℂ)) (riemannZeta k)⁻¹ := by
    have : LSeries.term (fun n => (μ n : ℂ)) k = fun n : ℕ => ((((μ n : ℝ) / (n : ℝ) ^ k : ℝ)) : ℂ) :=
      funext hterm
    rw [← this]; exact hL
  have h3 := Complex.reCLM.hasSum h2
  simp only [Complex.reCLM_apply, Complex.ofReal_re] at h3
  convert h3 using 1
  rw [hreal, ← Complex.ofReal_inv, Complex.ofReal_re, Complex.ofReal_re]

end Kerr.PowerfulNumbers
