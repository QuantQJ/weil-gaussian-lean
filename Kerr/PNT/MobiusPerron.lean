/-
Kerr/PNT/MobiusPerron.lean — new file (written for this repo, not copied).
Smoothed Perron identity for the Möbius function, using the copied PrimeNumberTheoremAnd
Perron formulas `Perron.formulaGtOne` / `Perron.formulaLtOne` (PerronFormula.lean, Apache-2.0,
© the PrimeNumberTheoremAnd contributors):

  (1/2πi) ∫_{(b)} x^s/(s(s+1)) · (1/ζ(s)) ds = ∑_{n ≤ x} μ(n) (1 - n/x)     (b > 1, x ∉ ℕ).
-/
import Kerr.PNT.MobiusInvZeta
import Kerr.PNT.PerronFormula

open Complex Filter Topology Set MeasureTheory ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace KerrPNT.Mobius

local notation "ζ" => riemannZeta

/-- `VerticalIntegral` of the Perron kernel. -/
lemma vertInt_perron {y b : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) (hb : 0 < b) :
    VerticalIntegral (Perron.f y) b =
      2 * Real.pi * I * (if 1 < y then (1 - 1 / (y : ℂ)) else 0) := by
  have h2pi : (2 * Real.pi * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, I_ne_zero]
  split_ifs with h
  · have := Perron.formulaGtOne (x := y) h hb
    simp only [VerticalIntegral', smul_eq_mul] at this
    have e : VerticalIntegral (Perron.f y) b = (2 * Real.pi * I) * (1 / (2 * Real.pi * I) *
        VerticalIntegral (fun s ↦ (y : ℂ) ^ s / (s * (s + 1))) b) := by
      rw [← mul_assoc, mul_one_div_cancel h2pi, one_mul]
    rw [e, this]
  · have hlt : y < 1 := lt_of_le_of_ne (not_lt.mp h) hy1
    rw [Perron.formulaLtOne hy hlt hb]; simp

lemma norm_perron_f {y : ℝ} (hy : 0 < y) (s : ℂ) :
    ‖Perron.f y s‖ = y ^ s.re * ‖Perron.f 1 s‖ := by
  simp only [Perron.f, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy, ofReal_one, one_cpow,
    norm_one]
  ring

lemma invZeta_eq_LSeries {s : ℂ} (hs : 1 < s.re) : invZeta s = LSeries (fun n ↦ (μ n : ℂ)) s := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs; simp at hs
  rw [invZeta_of_ne hs1, ← LSeries_one_eq_riemannZeta hs]
  have := LSeries_one_mul_Lseries_moebius hs
  exact inv_eq_of_mul_eq_one_right this

/-- **Smoothed Perron identity for μ.** -/
theorem perron_moebius {x b : ℝ} (hx : 0 < x) (hxn : ∀ n : ℕ, (n : ℝ) ≠ x) (hb : 1 < b) :
    VerticalIntegral (fun s ↦ Perron.f x s * invZeta s) b =
      2 * Real.pi * I * ∑ n ∈ Finset.Iic ⌊x⌋₊, (μ n : ℂ) * (1 - n / x) := by
  set g : ℕ → ℝ → ℂ := fun n t ↦
    if n = 0 then 0 else (μ n : ℂ) * Perron.f (x / n) (b + t * I) with hg
  have hb0 : (b : ℝ) ≠ 0 := by linarith
  have hbm : (b : ℝ) ≠ -1 := by linarith
  -- pointwise expansion
  have hpt : ∀ t : ℝ, Perron.f x (b + t * I) * invZeta (b + t * I) = ∑' n, g n t := by
    intro t
    have hre : 1 < ((b : ℂ) + t * I).re := by simpa using hb
    rw [invZeta_eq_LSeries hre, LSeries, ← tsum_mul_left]
    congr 1; funext n
    rw [LSeries.term_def]
    by_cases hn : n = 0
    · simp [hg, hn]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      simp only [hg, hn, ite_false]
      rw [← Perron.f_mul_eq_f hx hnpos, div_eq_mul_inv, ← cpow_neg]
      push_cast
      ring
  -- integrability of each term
  have hint : ∀ n, Integrable (g n) := by
    intro n
    by_cases hn : n = 0
    · simp [hg, hn]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      simp only [hg, hn, ite_false]
      exact (Perron.isIntegrable (div_pos hx hnpos) hb0 hbm).const_mul _
  set K : ℝ := ∫ t : ℝ, ‖Perron.f 1 (b + t * I)‖ with hK
  have hK1 : Integrable (fun t : ℝ ↦ ‖Perron.f 1 (b + t * I)‖) :=
    (Perron.isIntegrable one_pos hb0 hbm).norm
  have hbound : ∀ n, ∫ t, ‖g n t‖ ≤ x ^ b * K * (n : ℝ) ^ (-b) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp [hg, Real.zero_rpow (by linarith : -b ≠ 0)]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have e : ∀ t : ℝ, ‖g n t‖ ≤ x ^ b * (n : ℝ) ^ (-b) * ‖Perron.f 1 (b + t * I)‖ := by
        intro t
        simp only [hg, hn, ite_false, norm_mul]
        rw [norm_perron_f (div_pos hx hnpos)]
        have hμ : ‖(μ n : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_intCast]
          exact_mod_cast abs_moebius_le_one
        have hre : ((b : ℂ) + t * I).re = b := by simp
        rw [hre, Real.div_rpow hx.le hnpos.le, div_eq_mul_inv, ← Real.rpow_neg hnpos.le]
        calc ‖(μ n : ℂ)‖ * (x ^ b * (n : ℝ) ^ (-b) * ‖Perron.f 1 (b + t * I)‖)
            ≤ 1 * (x ^ b * (n : ℝ) ^ (-b) * ‖Perron.f 1 (b + t * I)‖) := by gcongr
          _ = _ := one_mul _
      calc ∫ t, ‖g n t‖ ≤ ∫ t : ℝ, x ^ b * (n : ℝ) ^ (-b) * ‖Perron.f 1 (b + t * I)‖ :=
            integral_mono (hint n).norm (hK1.const_mul _) e
        _ = x ^ b * K * (n : ℝ) ^ (-b) := by rw [integral_const_mul]; ring
  have hsum : Summable fun n ↦ ∫ t, ‖g n t‖ := by
    refine Summable.of_nonneg_of_le (fun n ↦ integral_nonneg fun _ ↦ norm_nonneg _) hbound ?_
    exact (Real.summable_nat_rpow.mpr (by linarith)).mul_left _
  -- swap
  have hswap := integral_tsum_of_summable_integral_norm hint hsum
  have hterm : ∀ n, I * ∫ t, g n t =
      2 * Real.pi * I * ((μ n : ℂ) * (if (n : ℝ) ≤ x ∧ n ≠ 0 then (1 - (n : ℂ) / x) else 0)) := by
    intro n
    by_cases hn : n = 0
    · simp [hg, hn]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      simp only [hg, hn, ite_false, integral_const_mul]
      have hy : 0 < x / n := div_pos hx hnpos
      have hy1 : x / n ≠ 1 := by
        intro h; rw [div_eq_one_iff_eq hnpos.ne'] at h; exact hxn n h.symm
      have hv := vertInt_perron hy hy1 (by linarith : (0 : ℝ) < b)
      simp only [VerticalIntegral, smul_eq_mul] at hv
      have hiff : 1 < x / n ↔ (n : ℝ) ≤ x ∧ n ≠ 0 := by
        rw [one_lt_div hnpos]
        constructor
        · intro h; exact ⟨h.le, hn⟩
        · rintro ⟨h, -⟩; exact lt_of_le_of_ne h (hxn n)
      calc I * ((μ n : ℂ) * ∫ t : ℝ, Perron.f (x / n) (b + t * I))
          = (μ n : ℂ) * (I * ∫ t : ℝ, Perron.f (x / n) (b + t * I)) := by ring
        _ = _ := by
          rw [hv]
          by_cases h : 1 < x / n
          · have h' := hiff.mp h
            rw [if_pos h, if_pos h']
            have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
            have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
            have : (1 : ℂ) - 1 / ((x / n : ℝ) : ℂ) = 1 - n / x := by
              push_cast; field_simp
            rw [this]; ring
          · have h' : ¬ ((n : ℝ) ≤ x ∧ n ≠ 0) := fun hh ↦ h (hiff.mpr hh)
            rw [if_neg h, if_neg h']; ring
  calc VerticalIntegral (fun s ↦ Perron.f x s * invZeta s) b
      = I * ∫ t : ℝ, ∑' n, g n t := by
        simp only [VerticalIntegral, smul_eq_mul]; congr 1; exact integral_congr_ae
          (Eventually.of_forall hpt)
    _ = ∑' n, I * ∫ t, g n t := by rw [← hswap, tsum_mul_left]
    _ = ∑' n, 2 * Real.pi * I * ((μ n : ℂ) * (if (n : ℝ) ≤ x ∧ n ≠ 0 then (1 - (n : ℂ) / x) else 0)) := by
        congr 1; funext n; exact hterm n
    _ = ∑ n ∈ Finset.Iic ⌊x⌋₊,
          2 * Real.pi * I * ((μ n : ℂ) * (if (n : ℝ) ≤ x ∧ n ≠ 0 then (1 - (n : ℂ) / x) else 0)) := by
        apply tsum_eq_sum
        intro n hn
        rw [Finset.mem_Iic, Nat.le_floor_iff hx.le] at hn
        rw [if_neg (fun h ↦ hn h.1)]; ring
    _ = 2 * Real.pi * I * ∑ n ∈ Finset.Iic ⌊x⌋₊, (μ n : ℂ) * (1 - n / x) := by
        rw [← Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.mem_Iic, Nat.le_floor_iff hx.le] at hn
        by_cases h0 : n = 0
        · subst h0; simp
        · rw [if_pos ⟨hn, h0⟩]

end KerrPNT.Mobius
