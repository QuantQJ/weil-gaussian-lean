/-
Copyright 2026 James C. Kerr (QuantQJ). Apache-2.0.
-/
import Kerr.PNT.ZetaBounds

/-!
# `∑_{n ≤ N} n^{−s} = ζ(s) + N^{1−s}/(1−s) + N^{−s}/2 + O(N^{−s−1})` for real `s > 0`, `s ≠ 1`

New file (written for this repo). From the representation `ζ = ζ₀ N` (`Zeta0EqZeta`, copied from
PrimeNumberTheoremAnd) the remainder is `−s ∫_N^∞ (⌊x⌋ + 1/2 − x) x^{−s−1} dx`; on each `[n, n+1]`
integration by parts against `p(x) = ((x−n)² − (x−n))/2` (which vanishes at both ends,
`|p| ≤ 1/8`) bounds the piece by `(n^{−s−1} − (n+1)^{−s−1})/8`, and the pieces telescope.
-/

noncomputable section
open MeasureTheory Set Real Filter Topology

namespace Kerr.PowerfulNumbers

/-- The real integrand `(⌊x⌋ + 1/2 − x) x^{−(s+1)}`. -/
def emf (s x : ℝ) : ℝ := ((⌊x⌋ : ℝ) + 1 / 2 - x) * x ^ (-(s + 1))

lemma emf_unit {s : ℝ} (hs : 0 < s) {M : ℕ} (hM : 1 ≤ M) :
    |∫ x in (M : ℝ)..((M : ℝ) + 1), emf s x| ≤
      ((M : ℝ) ^ (-(s + 1)) - ((M : ℝ) + 1) ^ (-(s + 1))) / 8 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  set φ : ℝ → ℝ := fun x => x ^ (-(s + 1)) with hφ
  set φ' : ℝ → ℝ := fun x => -(s + 1) * x ^ (-(s + 1) - 1) with hφ'
  set v : ℝ → ℝ := fun x => ((x - M) * (x - M) - (x - M)) / 2 with hv
  set v' : ℝ → ℝ := fun x => x - M - 1 / 2 with hv'
  have hle : (M : ℝ) ≤ (M : ℝ) + 1 := by linarith
  -- a.e. congruence: on `(M, M+1)` the floor is `M`
  have hcongr : ∫ x in (M : ℝ)..((M : ℝ) + 1), emf s x =
      ∫ x in (M : ℝ)..((M : ℝ) + 1), -(φ x * v' x) := by
    apply intervalIntegral.integral_congr_ae
    have hnull : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ ({(M : ℝ) + 1} : Set ℝ) :=
      measure_eq_zero_iff_ae_notMem.mp (measure_singleton _)
    filter_upwards [hnull] with x hx hxI
    rw [uIoc_of_le hle] at hxI
    have hx1 : x < (M : ℝ) + 1 := lt_of_le_of_ne hxI.2 (by simpa using hx)
    have hfl : (⌊x⌋ : ℝ) = M := by
      have : ⌊x⌋ = (M : ℤ) := Int.floor_eq_iff.mpr ⟨by push_cast; linarith [hxI.1], by push_cast; linarith⟩
      rw [this]; push_cast; rfl
    simp only [emf, hφ, hv', hfl]
    ring
  rw [hcongr, intervalIntegral.integral_neg]
  -- integration by parts
  have hpos : ∀ x ∈ uIcc (M : ℝ) ((M : ℝ) + 1), 0 < x := by
    intro x hx; rw [uIcc_of_le hle] at hx; linarith [hx.1]
  have hdφ : ∀ x ∈ uIcc (M : ℝ) ((M : ℝ) + 1), HasDerivAt φ (φ' x) x :=
    fun x hx => Real.hasDerivAt_rpow_const (Or.inl (hpos x hx).ne')
  have hdv : ∀ x ∈ uIcc (M : ℝ) ((M : ℝ) + 1), HasDerivAt v (v' x) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => y - M) 1 x := by
      simpa using (hasDerivAt_id x).sub_const (M : ℝ)
    have h2 := ((h1.mul h1).sub h1).div_const 2
    convert h2 using 1
    simp only [hv']; ring
  have hcφ' : ContinuousOn φ' (uIcc (M : ℝ) ((M : ℝ) + 1)) := by
    intro x hx
    exact ((Real.continuousAt_rpow_const _ _ (Or.inl (hpos x hx).ne')).const_mul _).continuousWithinAt
  have hiφ' : IntervalIntegrable φ' volume (M : ℝ) ((M : ℝ) + 1) := hcφ'.intervalIntegrable
  have hiv' : IntervalIntegrable v' volume (M : ℝ) ((M : ℝ) + 1) :=
    (by fun_prop : Continuous v').intervalIntegrable _ _
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hdφ hdv hiφ' hiv'
  have hvM : v M = 0 := by simp [hv]
  have hvM1 : v ((M : ℝ) + 1) = 0 := by simp [hv]
  rw [hvM, hvM1, mul_zero, mul_zero, sub_zero, zero_sub] at hibp
  rw [hibp, neg_neg]
  -- `|∫ φ' v| ≤ (1/8) ∫ (−φ')`
  have hbound : ∀ x ∈ Icc (M : ℝ) ((M : ℝ) + 1), |φ' x * v x| ≤ (-φ' x) / 8 := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hφ'n : φ' x ≤ 0 := by
      simp only [hφ']
      have : 0 ≤ x ^ (-(s + 1) - 1) := Real.rpow_nonneg hx0.le _
      nlinarith
    have hv1 : |v x| ≤ 1 / 8 := by
      simp only [hv]
      have ha : 0 ≤ x - M := by linarith [hx.1]
      have hb : 0 ≤ (M : ℝ) + 1 - x := by linarith [hx.2]
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (x - M - 1 / 2), mul_nonneg ha hb]
    rw [abs_mul, abs_of_nonpos hφ'n]
    nlinarith [abs_nonneg (v x)]
  have hint1 : IntervalIntegrable (fun x => φ' x * v x) volume (M : ℝ) ((M : ℝ) + 1) :=
    (hcφ'.mul (by fun_prop : Continuous v).continuousOn).intervalIntegrable
  have hint2 : IntervalIntegrable (fun x => (-φ' x) / 8) volume (M : ℝ) ((M : ℝ) + 1) :=
    (hiφ'.neg).div_const 8
  have hftc : ∫ x in (M : ℝ)..((M : ℝ) + 1), (-φ' x) / 8 =
      ((M : ℝ) ^ (-(s + 1)) - ((M : ℝ) + 1) ^ (-(s + 1))) / 8 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_neg,
      intervalIntegral.integral_eq_sub_of_hasDerivAt hdφ hiφ']
    simp only [hφ]; ring
  calc |∫ x in (M : ℝ)..((M : ℝ) + 1), φ' x * v x|
      ≤ ∫ x in (M : ℝ)..((M : ℝ) + 1), |φ' x * v x| :=
        intervalIntegral.abs_integral_le_integral_abs hle
    _ ≤ ∫ x in (M : ℝ)..((M : ℝ) + 1), (-φ' x) / 8 :=
        intervalIntegral.integral_mono_on hle hint1.abs hint2 hbound
    _ = _ := hftc

lemma emf_complex {s x : ℝ} (hx : 0 < x) :
    ((⌊x⌋ : ℂ) + 1 / 2 - x) * (x : ℂ) ^ (-((s : ℂ) + 1)) = ((emf s x : ℝ) : ℂ) := by
  rw [emf, Complex.ofReal_mul, Complex.ofReal_cpow hx.le]
  push_cast; ring_nf

lemma emf_integrableOn {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 1 ≤ N) :
    IntegrableOn (emf s) (Ioi (N : ℝ)) := by
  have hc := integrableOn_of_Zeta0_fun (N := N) (by omega) (s := (s : ℂ)) (by simpa using hs)
  have hc' : IntegrableOn (fun x : ℝ => ((emf s x : ℝ) : ℂ)) (Ioi (N : ℝ)) := by
    refine hc.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx0 : 0 < x := lt_of_le_of_lt (Nat.cast_nonneg N) hx
    exact emf_complex hx0
  exact hc'.re

lemma emf_interval {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 1 ≤ N) {M : ℕ} (hNM : N ≤ M) :
    |∫ x in (N : ℝ)..(M : ℝ), emf s x| ≤ ((N : ℝ) ^ (-(s + 1)) - (M : ℝ) ^ (-(s + 1))) / 8 := by
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
    have hM : 1 ≤ M := hN.trans hNM
    have hi : ∀ a b : ℝ, (N : ℝ) ≤ a → a ≤ b → IntervalIntegrable (emf s) volume a b := by
      intro a b ha hab
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
      refine (emf_integrableOn hs hN).mono_set (fun x hx => ?_)
      exact lt_of_le_of_lt ha hx.1
    have hN' : (N : ℝ) ≤ M := by exact_mod_cast hNM
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := (M : ℝ))
      (hi _ _ le_rfl hN') (hi _ _ hN' (by push_cast; linarith))]
    have hu := emf_unit hs hM
    push_cast
    calc |(∫ x in (N : ℝ)..(M : ℝ), emf s x) + ∫ x in (M : ℝ)..((M : ℝ) + 1), emf s x|
        ≤ |∫ x in (N : ℝ)..(M : ℝ), emf s x| + |∫ x in (M : ℝ)..((M : ℝ) + 1), emf s x| :=
          abs_add_le _ _
      _ ≤ _ := by linarith

lemma emf_Ioi {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 1 ≤ N) :
    |∫ x in Ioi (N : ℝ), emf s x| ≤ (N : ℝ) ^ (-(s + 1)) / 8 := by
  have hT := intervalIntegral_tendsto_integral_Ioi (N : ℝ) (emf_integrableOn hs hN)
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hT' := (continuous_abs.tendsto _).comp hT
  refine le_of_tendsto hT' (eventually_atTop.mpr ⟨N, fun M hM => ?_⟩)
  have h := emf_interval hs hN hM
  have hM0 : 0 ≤ (M : ℝ) ^ (-(s + 1)) := Real.rpow_nonneg (Nat.cast_nonneg M) _
  simp only [Function.comp]
  linarith

/-- **Second-order Euler–Maclaurin with `ζ`.** For real `s > 0`, `s ≠ 1`, `N ≥ 1`:
`|∑_{n ≤ N} n^{−s} − ζ(s) − N^{1−s}/(1−s) − N^{−s}/2| ≤ s N^{−s−1}/8`. -/
theorem zeta_partial_sum_approx {s : ℝ} (hs : 0 < s) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    |∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-s) - (riemannZeta s).re - (N : ℝ) ^ (1 - s) / (1 - s) -
      (N : ℝ) ^ (-s) / 2| ≤ s * (N : ℝ) ^ (-(s + 1)) / 8 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hz := Zeta0EqZeta (N := N) (by omega) (s := (s : ℂ)) (by simpa using hs)
    (by intro h; apply hs1; exact_mod_cast h)
  rw [riemannZeta0_apply] at hz
  -- the integral is real
  have hI : ∫ x in Ioi (N : ℝ), ((⌊x⌋ : ℂ) + 1 / 2 - x) * (x : ℂ) ^ (-((s : ℂ) + 1)) =
      ((∫ x in Ioi (N : ℝ), emf s x : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    exact emf_complex (lt_of_le_of_lt (Nat.cast_nonneg N) hx)
  rw [hI] at hz
  -- the finite sum is real
  have hS : ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ (s : ℂ) =
      ((∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-s) : ℝ) : ℂ) := by
    rw [Finset.range_eq_Ico, Finset.Ico_add_one_right_eq_Icc, Finset.Icc_eq_cons_Ioc (Nat.zero_le N),
      Finset.sum_cons, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]
    have h0 : (1 : ℂ) / ((0 : ℕ) : ℂ) ^ (s : ℂ) = 0 := by
      rw [Nat.cast_zero, Complex.zero_cpow (by exact_mod_cast hs.ne'), div_zero]
    rw [h0, zero_add]
    push_cast
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast, Complex.ofReal_neg,
      Complex.cpow_neg, one_div]
  rw [hS] at hz
  have hNs1 : ((N : ℂ) ^ (1 - (s : ℂ))) = (((N : ℝ) ^ (1 - s) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hN0.le]; push_cast; rfl
  have hNs : ((N : ℂ) ^ (-(s : ℂ))) = (((N : ℝ) ^ (-s) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hN0.le]; push_cast; rfl
  rw [hNs1, hNs] at hz
  have h1s : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have h1sc : (1 - (s : ℂ)) ≠ 0 := by exact_mod_cast h1s
  have hz2 : riemannZeta s = ((∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-s) - (N : ℝ) ^ (1 - s) / (1 - s) -
      (N : ℝ) ^ (-s) / 2 + s * ∫ x in Ioi (N : ℝ), emf s x : ℝ) : ℂ) := by
    rw [← hz]; push_cast; ring
  have hre : (riemannZeta s).re = ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-s) - (N : ℝ) ^ (1 - s) / (1 - s) -
      (N : ℝ) ^ (-s) / 2 + s * ∫ x in Ioi (N : ℝ), emf s x := by
    rw [hz2, Complex.ofReal_re]
  have hI8 := emf_Ioi hs hN
  have key : ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-s) - (riemannZeta s).re - (N : ℝ) ^ (1 - s) / (1 - s) -
      (N : ℝ) ^ (-s) / 2 = -(s * ∫ x in Ioi (N : ℝ), emf s x) := by
    rw [hre]; ring
  rw [key, abs_neg, abs_mul, abs_of_pos hs]
  calc s * |∫ x in Ioi (N : ℝ), emf s x| ≤ s * ((N : ℝ) ^ (-(s + 1)) / 8) := by gcongr
    _ = s * (N : ℝ) ^ (-(s + 1)) / 8 := by ring

end Kerr.PowerfulNumbers
