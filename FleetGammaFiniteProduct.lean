import Mathlib

noncomputable section
open Complex Filter Topology

namespace FleetGammaFiniteProduct

def logApprox (n : ℕ) (z : ℂ) : ℂ :=
  (z - 1) * (Real.log n : ℂ) -
    ∑ k ∈ Finset.range (n + 1), Complex.log (1 + (z - 1) / ((k : ℂ) + 1))

lemma shifted_ne_zero (z : ℂ) (hz : 0 < z.re) (k : ℕ) : z + (k : ℂ) ≠ 0 := by
  intro he
  have h := congrArg Complex.re he
  simp only [add_re, natCast_re, zero_re] at h
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

lemma log_argument_eq (k : ℕ) (z : ℂ) :
    1 + (z - 1) / ((k : ℂ) + 1) = (z + k) / ((k : ℂ) + 1) := by
  have hk : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
  field_simp
  ring

/-- A finite logarithmic approximation exponentiates to the normalized Gamma product. -/
theorem exp_logApprox (n : ℕ) (hn : n ≠ 0) (z : ℂ) (hz : 0 < z.re) :
    Complex.exp (logApprox n z) = Complex.GammaSeq z n / Complex.GammaSeq 1 n := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hk (k : ℕ) : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
  have hP : (∏ k ∈ Finset.range (n + 1), (z + (k : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => shifted_ne_zero z hz k)
  have hQ : (∏ k ∈ Finset.range (n + 1), ((1 : ℂ) + (k : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => by simpa [add_comm] using hk k)
  have he : Complex.exp ((z - 1) * (Real.log n : ℂ)) = (n : ℂ) ^ (z - 1) := by
    rw [Complex.cpow_def_of_ne_zero hnC]
    have hl : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
      exact (Complex.ofReal_log (Nat.cast_nonneg n)).symm
    rw [hl]
    congr 1
    ring
  have hp : Complex.exp (∑ k ∈ Finset.range (n + 1),
      Complex.log (1 + (z - 1) / ((k : ℂ) + 1))) =
      (∏ k ∈ Finset.range (n + 1), (z + k)) /
        (∏ k ∈ Finset.range (n + 1), ((1 : ℂ) + k)) := by
    rw [Complex.exp_sum]
    simp_rw [log_argument_eq]
    have ha (k : ℕ) : Complex.exp (Complex.log ((z + k) / ((k : ℂ) + 1))) =
        (z + k) / ((k : ℂ) + 1) := Complex.exp_log (div_ne_zero (shifted_ne_zero z hz k) (hk k))
    simp_rw [ha]
    rw [Finset.prod_div_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro k _
    ring
  unfold logApprox
  rw [Complex.exp_sub, he, hp, Complex.cpow_sub _ _ hnC, Complex.cpow_one]
  unfold Complex.GammaSeq
  rw [Complex.cpow_one]
  field_simp

/-- The exponentials converge to Gamma using only the existing pointwise product limit. -/
theorem tendsto_exp_logApprox (z : ℂ) (hz : 0 < z.re) :
    Tendsto (fun n : ℕ => Complex.exp (logApprox n z)) atTop (𝓝 (Complex.Gamma z)) := by
  have he : (fun n : ℕ => Complex.exp (logApprox n z)) =ᶠ[atTop]
      (fun n => Complex.GammaSeq z n / Complex.GammaSeq 1 n) := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact exp_logApprox n hn z hz
  have ht := (Complex.GammaSeq_tendsto_Gamma z).div (Complex.GammaSeq_tendsto_Gamma 1)
    (by rw [Complex.Gamma_one]; exact one_ne_zero)
  simpa only [Complex.Gamma_one, div_one] using ht.congr' he.symm

/-- Rewrite the logarithmic approximation into a convergent harmonic part and a regularized sum. -/
theorem logApprox_eq_regularized (n : ℕ) (z : ℂ) :
    logApprox n z = (z - 1) * ((Real.log n : ℂ) - (harmonic (n + 1) : ℂ)) -
      ∑ k ∈ Finset.range (n + 1),
        (Complex.log (1 + (z - 1) / ((k : ℂ) + 1)) - (z - 1) / ((k : ℂ) + 1)) := by
  have hh : (harmonic (n + 1) : ℂ) = ∑ k ∈ Finset.range (n + 1), ((k : ℂ) + 1)⁻¹ := by
    simp [harmonic]
  have hs : (∑ k ∈ Finset.range (n + 1), (z - 1) / ((k : ℂ) + 1)) =
      (z - 1) * (harmonic (n + 1) : ℂ) := by
    rw [hh, Finset.mul_sum]
    simp only [div_eq_mul_inv]
  rw [Finset.sum_sub_distrib, hs]
  unfold logApprox
  ring

end FleetGammaFiniteProduct
