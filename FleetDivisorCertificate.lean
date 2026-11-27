import Mathlib

/-!
# The divisor-identity certificate

`Σ_{d ∣ n} Λ(d) = log n` turns any choice of multipliers `U n` (scalars, or matrices for the bank
version) into an exact rewriting of a von Mangoldt sum. With the coverage residuals

  `E d = Σ_{n ≤ N, d ∣ n} U n − K d`,

  `Σ_{d ≤ N} Λ(d) • K d = Σ_{n ≤ N} (log n) • U n − Σ_{d ≤ N} Λ(d) • E d`.          (`certificate_identity`)

Scalar case: coverage `K d ≤ Σ_{d ∣ n} U n` at every prime power `d ≤ N` gives
`Σ Λ(d) K d ≤ Σ (log n) U n` (`prime_sum_le_budget`), hence for any `A`,
`A − Σ (log n) U n ≤ A − Σ Λ(d) K d` (`lower_bound_of_coverage`).

Bank case: if `A − Σ (log n) • U n` and every `E d` (at prime powers) are positive semidefinite,
then `A − Σ Λ(d) • K d` is positive semidefinite (`bank_posSemidef_of_certificate`).

Everything is finite (`n, d ≤ N`); no analytic input.
-/

set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction


namespace FleetDivisorCertificate

/-- Multiples of `d` up to `N`. -/
def mult (N d : ℕ) : Finset ℕ := (Icc 1 N).filter (fun n => d ∣ n)

/-- Swap: `Σ_d Λ(d) Σ_{d ∣ n} U n = Σ_n (log n) U n`, in any real module. -/
theorem swap {M : Type*} [AddCommMonoid M] [Module ℝ M] (N : ℕ) (U : ℕ → M) :
    ∑ d ∈ Icc 1 N, vonMangoldt d • ∑ n ∈ mult N d, U n = ∑ n ∈ Icc 1 N, Real.log n • U n := by
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm' (t' := Icc 1 N) (s' := fun n => n.divisors)]
  · refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [← Finset.sum_smul, vonMangoldt_sum]
  · intro d n
    simp only [mult, Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨_, ⟨h1, h2⟩, hd⟩
      exact ⟨⟨hd, by omega⟩, h1, h2⟩
    · rintro ⟨⟨hd, hn⟩, h1, h2⟩
      have := Nat.le_of_dvd (by omega) hd
      have := Nat.pos_of_dvd_of_pos hd (by omega)
      exact ⟨⟨by omega, by omega⟩, ⟨h1, h2⟩, hd⟩

/-- Coverage residual. -/
def E {M : Type*} [AddCommGroup M] (N : ℕ) (U K : ℕ → M) (d : ℕ) : M :=
  (∑ n ∈ mult N d, U n) - K d

/-- **Exact certificate identity.** -/
theorem certificate_identity {M : Type*} [AddCommGroup M] [Module ℝ M] (N : ℕ) (U K : ℕ → M) :
    ∑ d ∈ Icc 1 N, vonMangoldt d • K d
      = ∑ n ∈ Icc 1 N, Real.log n • U n - ∑ d ∈ Icc 1 N, vonMangoldt d • E N U K d := by
  rw [← swap N U]
  simp only [E, smul_sub, Finset.sum_sub_distrib]
  abel

/-- Scalar: coverage at prime powers bounds the prime sum by the budget. -/
theorem prime_sum_le_budget (N : ℕ) (u k : ℕ → ℝ)
    (hcov : ∀ d ∈ Icc 1 N, IsPrimePow d → k d ≤ ∑ n ∈ mult N d, u n) :
    ∑ d ∈ Icc 1 N, vonMangoldt d * k d ≤ ∑ n ∈ Icc 1 N, Real.log n * u n := by
  have h := certificate_identity N u k
  simp only [smul_eq_mul] at h
  have hnn : 0 ≤ ∑ d ∈ Icc 1 N, vonMangoldt d * E N u k d := by
    apply Finset.sum_nonneg
    intro d hd
    by_cases hp : IsPrimePow d
    · exact mul_nonneg vonMangoldt_nonneg (by simp only [E]; linarith [hcov d hd hp])
    · rw [vonMangoldt_eq_zero_iff.mpr hp, zero_mul]
  linarith

/-- Scalar: `R = A − Σ Λ k` is bounded below by `A − budget`. -/
theorem lower_bound_of_coverage (N : ℕ) (u k : ℕ → ℝ) (A : ℝ)
    (hcov : ∀ d ∈ Icc 1 N, IsPrimePow d → k d ≤ ∑ n ∈ mult N d, u n) :
    A - ∑ n ∈ Icc 1 N, Real.log n * u n ≤ A - ∑ d ∈ Icc 1 N, vonMangoldt d * k d := by
  linarith [prime_sum_le_budget N u k hcov]

lemma psd_smul {m : Type*} [Fintype m] {M : Matrix m m ℝ} (hM : M.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    (c • M).PosSemidef := by
  exact hM.smul hc

/-- Bank version: `B = A − Σ (log n) U n ⪰ 0` and `E d ⪰ 0` at prime powers give `A − Σ Λ(d) K d ⪰ 0`. -/
theorem bank_posSemidef_of_certificate {m : Type*} [Fintype m] (N : ℕ)
    (U K : ℕ → Matrix m m ℝ) (A : Matrix m m ℝ)
    (hB : (A - ∑ n ∈ Icc 1 N, Real.log n • U n).PosSemidef)
    (hE : ∀ d ∈ Icc 1 N, IsPrimePow d → (E N U K d).PosSemidef) :
    (A - ∑ d ∈ Icc 1 N, vonMangoldt d • K d).PosSemidef := by
  rw [certificate_identity N U K, sub_sub_eq_add_sub, add_sub_right_comm]
  -- A - Σ log U + Σ Λ E
  have term : ∀ d ∈ Icc 1 N, (vonMangoldt d • E N U K d).PosSemidef := by
    intro d hd
    by_cases hp : IsPrimePow d
    · exact psd_smul (hE d hd hp) vonMangoldt_nonneg
    · rw [vonMangoldt_eq_zero_iff.mpr hp, zero_smul]; exact Matrix.PosSemidef.zero
  have hsum : (∑ d ∈ Icc 1 N, vonMangoldt d • E N U K d).PosSemidef := by
    have key : ∀ (s : Finset ℕ), s ⊆ Icc 1 N →
        (∑ d ∈ s, vonMangoldt d • E N U K d).PosSemidef := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro _; simpa using Matrix.PosSemidef.zero
      | insert a s' ha ih =>
        intro hs
        rw [Finset.sum_insert ha]
        exact (term a (hs (Finset.mem_insert_self a s'))).add
          (ih (fun x hx => hs (Finset.mem_insert_of_mem hx)))
    exact key _ (subset_refl _)
  exact hB.add hsum


/-- **Floor for nonnegative corrections.** Write the multipliers as `u₀ + v` with `v ≥ 0`. Whatever `v` is,
the certificate's excess over the prime sum is at least `Σ Λ(d) · max(T d, 0)`, where
`T d = Σ_{d ∣ n} u₀ n − k d` is the coverage residual of `u₀` alone. -/
theorem excess_ge_floor (N : ℕ) (u₀ v k : ℕ → ℝ) (hv : ∀ n, 0 ≤ v n)
    (hcov : ∀ d ∈ Icc 1 N, IsPrimePow d → k d ≤ ∑ n ∈ mult N d, (u₀ n + v n)) :
    ∑ d ∈ Icc 1 N, vonMangoldt d * max ((∑ n ∈ mult N d, u₀ n) - k d) 0
      ≤ ∑ n ∈ Icc 1 N, Real.log n * (u₀ n + v n) - ∑ d ∈ Icc 1 N, vonMangoldt d * k d := by
  have h := certificate_identity N (fun n => u₀ n + v n) k
  simp only [smul_eq_mul] at h
  have hle : ∑ d ∈ Icc 1 N, vonMangoldt d * max ((∑ n ∈ mult N d, u₀ n) - k d) 0
      ≤ ∑ d ∈ Icc 1 N, vonMangoldt d * E N (fun n => u₀ n + v n) k d := by
    apply Finset.sum_le_sum
    intro d hd
    by_cases hp : IsPrimePow d
    · apply mul_le_mul_of_nonneg_left _ vonMangoldt_nonneg
      have hvs : 0 ≤ ∑ n ∈ mult N d, v n := Finset.sum_nonneg (fun n _ => hv n)
      have hsplit : ∑ n ∈ mult N d, (u₀ n + v n) = (∑ n ∈ mult N d, u₀ n) + ∑ n ∈ mult N d, v n :=
        Finset.sum_add_distrib
      simp only [E]
      rw [hsplit]
      have := hcov d hd hp
      rw [hsplit] at this
      exact max_le (by linarith) (by linarith)
    · rw [vonMangoldt_eq_zero_iff.mpr hp, zero_mul, zero_mul]
  linarith

end FleetDivisorCertificate
