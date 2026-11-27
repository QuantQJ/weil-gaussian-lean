import Mathlib

set_option autoImplicit false

/-!
# A finite sum of unimodular exponentials with equal weights does not tend to zero

For a finite family of real frequencies `θ k` (`k ∈ S`, `S ≠ ∅`) set

  `F s := ∑ k ∈ S, exp (i θ_k s)`.

**Main result** (`exists_large_of_nonempty`): for every `S₀` there is `s ≥ S₀` with
`‖F s‖ ≥ 1/2`.

**Proof (first Fourier coefficient on `[L, 2L]`).** Fix `k₀ ∈ S` and integrate
`F(s) e^{-i θ_{k₀} s}` over `[L, 2L]`.  Every `k` with `θ_k = θ_{k₀}` contributes exactly `L`
(there is at least one such `k`, namely `k₀`), and every `k` with `θ_k ≠ θ_{k₀}` contributes a
term of modulus `≤ 2 / |θ_k − θ_{k₀}|` (`integral_exp_mul_I_bound`, explicit antiderivative).
So the real part of the integral is `≥ L − D` with `D` independent of `L`.  If `‖F‖ < 1/2` on
`[L, 2L]` the integral has modulus `≤ L/2`, forcing `L ≤ 2D`; taking `L ≥ max S₀ (2D + 1)`
gives a contradiction.
-/

open Complex

namespace ExpSumLowerBound

/-- `‖exp (i δ s)‖ = 1` for real `δ, s`. -/
lemma norm_exp_I_mul (δ s : ℝ) : ‖Complex.exp (I * (δ : ℂ) * (s : ℂ))‖ = 1 := by
  have h : I * (δ : ℂ) * (s : ℂ) = ((δ * s : ℝ) : ℂ) * I := by push_cast; ring
  rw [h, norm_exp_ofReal_mul_I]

/-- **Off-diagonal bound.** For `δ ≠ 0`, `‖∫_L^{2L} e^{i δ s} ds‖ ≤ 2 / |δ|`. -/
theorem integral_exp_mul_I_bound (δ : ℝ) (hδ : δ ≠ 0) (L : ℝ) :
    ‖∫ s in L..(2*L), Complex.exp (I * (δ : ℂ) * (s : ℂ))‖ ≤ 2 / |δ| := by
  have hc : I * (δ : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hδ)
  rw [integral_exp_mul_complex hc, norm_div, norm_mul, norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs]
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  calc ‖Complex.exp (I * (δ : ℂ) * ((2*L : ℝ) : ℂ)) - Complex.exp (I * (δ : ℂ) * (L : ℂ))‖
      ≤ ‖Complex.exp (I * (δ : ℂ) * ((2*L : ℝ) : ℂ))‖
          + ‖Complex.exp (I * (δ : ℂ) * (L : ℂ))‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_exp_I_mul, norm_exp_I_mul]; norm_num

/-- **Diagonal value.** `∫_L^{2L} e^{i · 0 · s} ds = L`. -/
lemma integral_exp_zero (L : ℝ) :
    (∫ s in L..(2*L), Complex.exp (I * ((0 : ℝ) : ℂ) * (s : ℂ))) = (L : ℂ) := by
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero,
    intervalIntegral.integral_const, Complex.real_smul, mul_one]
  push_cast
  ring

/-- **Main result.** A nonempty finite sum of unimodular exponentials `∑_{k∈S} e^{i θ_k s}`
(equal weights) is `≥ 1/2` in modulus at arbitrarily large `s`. -/
theorem exists_large_of_nonempty {ι : Type*} [DecidableEq ι] (S : Finset ι) (hS : S.Nonempty)
    (θ : ι → ℝ) : ∀ S₀ : ℝ, ∃ s : ℝ, S₀ ≤ s ∧
      (1/2 : ℝ) ≤ ‖∑ k ∈ S, Complex.exp (I * (θ k : ℂ) * (s : ℂ))‖ := by
  intro S₀
  obtain ⟨k₀, hk₀⟩ := hS
  classical
  -- the off-diagonal constant `D = ∑_k c k`, independent of `L`
  set c : ι → ℝ := fun k => if θ k = θ k₀ then 0 else 2 / |θ k - θ k₀| with hc
  have hc_nonneg : ∀ k, 0 ≤ c k := by
    intro k
    simp only [hc]
    split_ifs
    · exact le_rfl
    · positivity
  set D := ∑ k ∈ S, c k with hD
  have hD_nonneg : 0 ≤ D := Finset.sum_nonneg (fun k _ => hc_nonneg k)
  set L := max S₀ (2 * D + 1) with hL
  have hL_S₀ : S₀ ≤ L := le_max_left _ _
  have hL_D : 2 * D + 1 ≤ L := le_max_right _ _
  have hL_pos : 0 < L := by linarith
  by_contra hcon
  push_neg at hcon
  -- the Fourier coefficients `G k = ∫_L^{2L} e^{i (θ_k − θ_{k₀}) s} ds`
  set G : ι → ℂ := fun k =>
    ∫ s in L..(2*L), Complex.exp (I * ((θ k - θ k₀ : ℝ) : ℂ) * (s : ℂ)) with hG
  -- identity: `∫ F(s) e^{-i θ_{k₀} s} = ∑_k G k`
  have hident : (∫ s in L..(2*L), (∑ k ∈ S, Complex.exp (I * (θ k : ℂ) * (s : ℂ)))
      * Complex.exp (-(I * (θ k₀ : ℂ) * (s : ℂ)))) = ∑ k ∈ S, G k := by
    have hpt : ∀ s : ℝ, (∑ k ∈ S, Complex.exp (I * (θ k : ℂ) * (s : ℂ)))
        * Complex.exp (-(I * (θ k₀ : ℂ) * (s : ℂ)))
        = ∑ k ∈ S, Complex.exp (I * ((θ k - θ k₀ : ℝ) : ℂ) * (s : ℂ)) := by
      intro s
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp_rw [hpt]
    apply intervalIntegral.integral_finset_sum
    intro k _
    exact (by fun_prop : Continuous fun s : ℝ =>
      Complex.exp (I * ((θ k - θ k₀ : ℝ) : ℂ) * (s : ℂ))).intervalIntegrable _ _
  -- upper bound from the (assumed) smallness of `F` on `[L, 2L]`
  have hupper : ‖∑ k ∈ S, G k‖ ≤ (1/2) * L := by
    rw [← hident]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := L) (b := 2*L) (C := 1/2)
      (f := fun s : ℝ => (∑ k ∈ S, Complex.exp (I * (θ k : ℂ) * (s : ℂ)))
        * Complex.exp (-(I * (θ k₀ : ℂ) * (s : ℂ)))) ?_
    · have h2 : |2*L - L| = L := by
        rw [abs_of_pos (by linarith)]; ring
      rw [h2] at hb
      exact hb
    · intro s hs
      rw [Set.uIoc_of_le (by linarith)] at hs
      have hsL : L < s := hs.1
      rw [norm_mul]
      have h1 : ‖Complex.exp (-(I * (θ k₀ : ℂ) * (s : ℂ)))‖ = 1 := by
        have h' : -(I * (θ k₀ : ℂ) * (s : ℂ)) = I * ((-θ k₀ : ℝ) : ℂ) * (s : ℂ) := by
          push_cast; ring
        rw [h', norm_exp_I_mul]
      rw [h1, mul_one]
      exact (hcon s (by linarith)).le
  -- diagonal terms are exactly `L`
  have hdiag : ∀ k, θ k = θ k₀ → G k = (L : ℂ) := by
    intro k hk
    simp only [hG]
    rw [show θ k - θ k₀ = 0 from sub_eq_zero.mpr hk]
    exact integral_exp_zero L
  -- every term has real part `≥ -(c k)`
  have hre_lb : ∀ k, -(c k) ≤ (G k).re := by
    intro k
    by_cases hk : θ k = θ k₀
    · rw [hdiag k hk, Complex.ofReal_re]
      simp only [hc, if_pos hk, neg_zero]
      exact hL_pos.le
    · have hb := integral_exp_mul_I_bound (θ k - θ k₀) (sub_ne_zero.mpr hk) L
      simp only [hc, if_neg hk]
      have habs := Complex.abs_re_le_norm (G k)
      rw [abs_le] at habs
      have h' : ‖G k‖ ≤ 2 / |θ k - θ k₀| := by
        skip; exact hb
      linarith [habs.1]
  -- lower bound on the real part of the sum
  have hsum_re : L - D ≤ (∑ k ∈ S, G k).re := by
    rw [Complex.re_sum, ← Finset.add_sum_erase S _ hk₀, hdiag k₀ rfl, Complex.ofReal_re]
    have h1 : ∑ k ∈ S.erase k₀, -(c k) ≤ ∑ k ∈ S.erase k₀, (G k).re :=
      Finset.sum_le_sum (fun k _ => hre_lb k)
    have h2 : -D ≤ ∑ k ∈ S.erase k₀, -(c k) := by
      rw [Finset.sum_neg_distrib, hD, neg_le_neg_iff]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun k _ _ => hc_nonneg k)
    linarith
  have hre_le := Complex.re_le_norm (∑ k ∈ S, G k)
  skip
  linarith

end ExpSumLowerBound
