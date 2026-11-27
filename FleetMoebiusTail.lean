import FleetDivisorCertificate

/-!
# Finite Möbius truncation of the prime sum: the budget gap is the Möbius tail

For any weights `k : ℕ → ℝ` vanishing beyond `N`, put

  `T m = Σ_{j ≤ N} log j · k(m j)`                       (smooth in the sense that `j` runs over all integers),
  `u_M n = Σ_{m ≤ M} μ(m) k(m n)`                        (mollified multiplier, only `μ` up to `M`).

Then
* `budget_eq`             `Σ_{n ≤ N} log n · u_M n = Σ_{m ≤ M} μ(m) T m`;
* `prime_sum_eq_moebius`  `Σ_{d ≤ N} Λ(d) k d = Σ_{m ≤ N} μ(m) T m`        (`Λ = μ ∗ log`);
* `prime_sum_sub_budget`  `Σ Λ k − budget(u_M) = Σ_{M < m ≤ N} μ(m) T m`   (the Möbius tail), `M ≤ N`;
* `prime_sum_le_free_bound` for any `u`:
  `Σ Λ k ≤ Σ log n · u n + Σ_{d ≤ N} log d · max(−E d, 0)`  (`Λ ≤ log`; no primes on the right).

With `k d = 2 d^{-1/2} e^{-b log² d} cos(α log d)`, `T m = m^{-1/2} I_b(α, log m)` cut at `N`; this is the
finite form of `FleetMoebiusSmoothDecomposition.primeSumSym_eq_moebius_smooth`. All finite; no analysis.
-/

set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace FleetMoebiusTail

/-- Inner smooth sum `T m = Σ_{j ≤ N} log j · k(m j)`. -/
def T (N : ℕ) (k : ℕ → ℝ) (m : ℕ) : ℝ := ∑ j ∈ Icc 1 N, Real.log j * k (m * j)

/-- Mollified multiplier `u_M n = Σ_{m ≤ M} μ(m) k(m n)`. -/
def uM (M : ℕ) (k : ℕ → ℝ) (n : ℕ) : ℝ := ∑ m ∈ Icc 1 M, ((μ m : ℤ) : ℝ) * k (m * n)

/-- The budget of the mollified multiplier is the Möbius sum truncated at `M`. -/
theorem budget_eq (N M : ℕ) (k : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, Real.log n * uM M k n = ∑ m ∈ Icc 1 M, ((μ m : ℤ) : ℝ) * T N k m := by
  simp only [uM, T, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => ?_))
  ring

/-- `Λ = μ ∗ log`, pointwise. -/
lemma vonMangoldt_eq_antidiag (n : ℕ) :
    (Λ n : ℝ) = ∑ p ∈ n.divisorsAntidiagonal, ((μ p.1 : ℤ) : ℝ) * Real.log p.2 := by
  rw [← ArithmeticFunction.moebius_mul_log_eq_vonMangoldt, ArithmeticFunction.mul_apply]
  simp [ArithmeticFunction.intCoe_apply, ArithmeticFunction.log_apply]

/-- **The prime sum is the full finite Möbius sum.** -/
theorem prime_sum_eq_moebius (N : ℕ) (k : ℕ → ℝ) (hk : ∀ n, N < n → k n = 0) :
    ∑ d ∈ Icc 1 N, vonMangoldt d * k d = ∑ m ∈ Icc 1 N, ((μ m : ℤ) : ℝ) * T N k m := by
  set f : ℕ × ℕ → ℝ := fun p => ((μ p.1 : ℤ) : ℝ) * Real.log p.2 * k (p.1 * p.2) with hf
  set s := (Icc 1 N ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ N) with hs
  -- right side: sum over the full square, then drop pairs with `m j > N`
  have hR : ∑ m ∈ Icc 1 N, ((μ m : ℤ) : ℝ) * T N k m = ∑ p ∈ s, f p := by
    have h1 : ∑ m ∈ Icc 1 N, ((μ m : ℤ) : ℝ) * T N k m = ∑ p ∈ Icc 1 N ×ˢ Icc 1 N, f p := by
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      simp only [T, Finset.mul_sum, hf]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [h1, hs, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    split_ifs with h
    · rfl
    · simp only [hf, hk (p.1 * p.2) (by omega), mul_zero]
  -- left side: fibre the filtered square over `d = m j`
  have hmaps : ∀ p ∈ s, p.1 * p.2 ∈ Icc 1 N := by
    intro p hp
    simp only [hs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    refine Finset.mem_Icc.mpr ⟨?_, hp.2⟩
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  rw [hR, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hd' := Finset.mem_Icc.mp hd
  have hfib : s.filter (fun p => p.1 * p.2 = d) = d.divisorsAntidiagonal := by
    ext ⟨a, c⟩
    simp only [hs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Nat.mem_divisorsAntidiagonal]
    constructor
    · rintro ⟨_, h⟩; exact ⟨h, by omega⟩
    · rintro ⟨h, _⟩
      have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at h; omega)
      have hc : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp at h; omega)
      have ha' : a ≤ d := h ▸ Nat.le_mul_of_pos_right a hc
      have hc' : c ≤ d := h ▸ Nat.le_mul_of_pos_left c ha
      exact ⟨⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, by omega⟩, h⟩
  rw [hfib, vonMangoldt_eq_antidiag, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  simp only [hf, (Nat.mem_divisorsAntidiagonal.mp hp).1]

/-- **Budget gap = Möbius tail.** For `M ≤ N`, the prime sum minus the budget of `u_M` is
`Σ_{M < m ≤ N} μ(m) T m`. -/
theorem prime_sum_sub_budget (N M : ℕ) (hMN : M ≤ N) (k : ℕ → ℝ) (hk : ∀ n, N < n → k n = 0) :
    ∑ d ∈ Icc 1 N, vonMangoldt d * k d - ∑ n ∈ Icc 1 N, Real.log n * uM M k n
      = ∑ m ∈ Ioc M N, ((μ m : ℤ) : ℝ) * T N k m := by
  rw [prime_sum_eq_moebius N k hk, budget_eq]
  have hI : ∀ K : ℕ, Icc 1 K = Ioc 0 K := fun K => by ext; simp [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hI N, hI M, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le M) hMN]
  ring

/-- **Prime-free upper bound** for any multiplier `u`: coverage failures are charged at `log d ≥ Λ(d)`. -/
theorem prime_sum_le_free_bound (N : ℕ) (u k : ℕ → ℝ) :
    ∑ d ∈ Icc 1 N, vonMangoldt d * k d
      ≤ ∑ n ∈ Icc 1 N, Real.log n * u n
        + ∑ d ∈ Icc 1 N, Real.log d * max (-(FleetDivisorCertificate.E N u k d)) 0 := by
  have h := FleetDivisorCertificate.certificate_identity N u k
  simp only [smul_eq_mul] at h
  rw [h, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  gcongr with d _
  calc -(vonMangoldt d * FleetDivisorCertificate.E N u k d)
      = vonMangoldt d * (-(FleetDivisorCertificate.E N u k d)) := by ring
    _ ≤ vonMangoldt d * max (-(FleetDivisorCertificate.E N u k d)) 0 :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) vonMangoldt_nonneg
    _ ≤ Real.log d * max (-(FleetDivisorCertificate.E N u k d)) 0 :=
        mul_le_mul_of_nonneg_right vonMangoldt_le_log (le_max_right _ _)

end FleetMoebiusTail
