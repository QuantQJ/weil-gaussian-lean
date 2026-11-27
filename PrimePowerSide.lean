import ExplicitFormula
import Mathlib

/-!
# The prime side, with the primes made explicit

`ExplicitFormula.primeSide c g = Σ_{n ≥ 0} Λ(n) n^{−c} · 𝓕g(log n)` is a sum over
all natural numbers, but `Λ` vanishes off the prime powers. This module makes
that structure explicit.

**Proven here (complete proofs; only the standard Lean/Mathlib foundations):**

1. `coeff_eq_zero_of_not_isPrimePow`: `coeff c n = 0` unless `n` is a prime power.
2. `coeff_prime_pow`: for `p` prime and `k ≠ 0`,
   `coeff c (p ^ k) = log p · p^{−(k c)}`.
3. `primeSide_eq_tsum_primePow`: the prime side equals the same sum restricted
   to the subtype `{n : ℕ // IsPrimePow n}`; the restricted family is summable
   (`primePow_summable`).
4. (Stretch) `primePow_equiv : {n // IsPrimePow n} ≃ {p // p.Prime} × ℕ+`,
   `n = p ^ k`, built from `eq_of_prime_pow_eq` (primes agree) and
   `Nat.pow_right_injective` (exponents agree), and the reindexed formula
   `primeSide_eq_tsum_prime_pnat`:
   `primeSide c g = Σ_{(p,k)} log p · p^{−(k c)} · 𝓕g(k · log p)`,
   with summability `prime_pnat_summable`.

Nothing here needs `1 < c` except the summability statements and (3)-(4),
which reindex a sum — `tsum` reindexing along an injection whose range covers
the support (`Function.Injective.tsum_eq`) is unconditional, but we keep the
hypotheses so the statements read as statements about a convergent sum.
Nothing about zeros of `ζ` is claimed; this is bookkeeping on the arithmetic
half of the explicit formula.
-/

noncomputable section
open MeasureTheory Real Complex
open scoped FourierTransform ArithmeticFunction

namespace PrimePowerSide

open ExplicitFormula

/-! ## The coefficients on and off the prime powers -/

/-- The prime-side weight vanishes unless `n` is a prime power. -/
theorem coeff_eq_zero_of_not_isPrimePow (c : ℝ) {n : ℕ} (hn : ¬ IsPrimePow n) :
    coeff c n = 0 := by
  unfold coeff
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn, zero_mul]

/-- The support of the prime-side weight lies in the prime powers. -/
theorem support_coeff_subset (c : ℝ) :
    Function.support (coeff c) ⊆ {n : ℕ | IsPrimePow n} := by
  intro n hn
  by_contra h
  exact hn (coeff_eq_zero_of_not_isPrimePow c h)

/-- On a prime power `p ^ k` (`p` prime, `k ≠ 0`) the weight is
`log p · p^{−(k c)}`: `Λ(p^k) = log p` and `(p^k)^{−c} = p^{−(k c)}`. -/
theorem coeff_prime_pow (c : ℝ) {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    coeff c (p ^ k) = Real.log p * (p : ℝ) ^ (-(k * c)) := by
  unfold coeff
  rw [ArithmeticFunction.vonMangoldt_apply_pow hk, ArithmeticFunction.vonMangoldt_apply_prime hp]
  congr 1
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hp0]
  congr 1
  ring

/-! ## Restricting the prime side to the prime powers -/

/-- Each term of the prime side, as a function of `n`. -/
def term (c : ℝ) (g : ℝ → ℂ) (n : ℕ) : ℂ := (coeff c n : ℂ) * 𝓕 g (Real.log n)

theorem term_eq_zero_of_not_isPrimePow (c : ℝ) (g : ℝ → ℂ) {n : ℕ} (hn : ¬ IsPrimePow n) :
    term c g n = 0 := by
  simp [term, coeff_eq_zero_of_not_isPrimePow c hn]

/-- The support of the prime-side terms lies in the prime powers. -/
theorem support_term_subset (c : ℝ) (g : ℝ → ℂ) :
    Function.support (term c g) ⊆ {n : ℕ | IsPrimePow n} := by
  intro n hn
  by_contra h
  exact hn (term_eq_zero_of_not_isPrimePow c g h)

/-- **The prime side is a sum over prime powers.** -/
theorem primeSide_eq_tsum_primePow (c : ℝ) (g : ℝ → ℂ) :
    primeSide c g
      = ∑' q : {n : ℕ // IsPrimePow n}, (coeff c q : ℂ) * 𝓕 g (Real.log q) := by
  unfold primeSide
  exact (tsum_subtype_eq_of_support_subset (f := term c g) (support_term_subset c g)).symm

/-- Summability of the prime-power-indexed family, for `1 < c` and `g` integrable. -/
theorem primePow_summable {c : ℝ} (hc : 1 < c) {g : ℝ → ℂ} (hg : Integrable g) :
    Summable fun q : {n : ℕ // IsPrimePow n} => (coeff c q : ℂ) * 𝓕 g (Real.log q) :=
  (primeSide_summable hc hg).subtype _

/-! ## Reindexing by pairs `(p, k)`, `p` prime, `k ≥ 1` -/

/-- The map `(p, k) ↦ p ^ k` from prime–exponent pairs to `ℕ`. -/
def pairToNat (pk : {p : ℕ // p.Prime} × ℕ+) : ℕ := pk.1.1 ^ (pk.2 : ℕ)

theorem pairToNat_isPrimePow (pk : {p : ℕ // p.Prime} × ℕ+) : IsPrimePow (pairToNat pk) :=
  pk.1.2.isPrimePow.pow pk.2.ne_zero

/-- Uniqueness of prime-power representation: `p ^ k = q ^ l` with `p, q` prime and
`k, l ≥ 1` forces `p = q` and `k = l`. -/
theorem pairToNat_injective : Function.Injective pairToNat := by
  rintro ⟨⟨p, hp⟩, k⟩ ⟨⟨q, hq⟩, l⟩ h
  simp only [pairToNat] at h
  have hpq : p = q := eq_of_prime_pow_eq hp.prime hq.prime k.pos h
  subst hpq
  have hkl : (k : ℕ) = l := Nat.pow_right_injective hp.two_le h
  simp [PNat.coe_inj.mp hkl]

/-- Every prime power is `p ^ k` for some pair. -/
theorem range_pairToNat : Set.range pairToNat = {n : ℕ | IsPrimePow n} := by
  ext n
  constructor
  · rintro ⟨pk, rfl⟩
    exact pairToNat_isPrimePow pk
  · intro hn
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
    exact ⟨(⟨p, hp⟩, ⟨k, hk⟩), rfl⟩

/-- **The prime powers are in bijection with prime–exponent pairs**, `n = p ^ k`. -/
def primePow_equiv : {p : ℕ // p.Prime} × ℕ+ ≃ {n : ℕ // IsPrimePow n} :=
  Equiv.ofBijective (fun pk => ⟨pairToNat pk, pairToNat_isPrimePow pk⟩)
    ⟨fun a b h => pairToNat_injective (congrArg Subtype.val h),
     fun ⟨n, hn⟩ => by
      obtain ⟨pk, hpk⟩ := (range_pairToNat ▸ hn : n ∈ Set.range pairToNat)
      exact ⟨pk, Subtype.ext hpk⟩⟩

@[simp] theorem primePow_equiv_apply_val (pk : {p : ℕ // p.Prime} × ℕ+) :
    ((primePow_equiv pk : {n : ℕ // IsPrimePow n}) : ℕ) = pk.1.1 ^ (pk.2 : ℕ) := rfl

/-- The prime-side term at `p ^ k`, in closed form. -/
theorem term_pair (c : ℝ) (g : ℝ → ℂ) (pk : {p : ℕ // p.Prime} × ℕ+) :
    term c g (pairToNat pk)
      = ((Real.log pk.1.1 * (pk.1.1 : ℝ) ^ (-((pk.2 : ℕ) * c)) : ℝ) : ℂ)
          * 𝓕 g ((pk.2 : ℕ) * Real.log pk.1.1) := by
  obtain ⟨⟨p, hp⟩, k⟩ := pk
  simp only [term, pairToNat, coeff_prime_pow c hp k.ne_zero, Nat.cast_pow, Real.log_pow]

/-- **The prime side, reindexed over pairs `(p, k)`:**
`primeSide c g = Σ_{p prime, k ≥ 1} log p · p^{−(k c)} · 𝓕g(k log p)`. -/
theorem primeSide_eq_tsum_prime_pnat (c : ℝ) (g : ℝ → ℂ) :
    primeSide c g
      = ∑' pk : {p : ℕ // p.Prime} × ℕ+,
          ((Real.log pk.1.1 * (pk.1.1 : ℝ) ^ (-((pk.2 : ℕ) * c)) : ℝ) : ℂ)
            * 𝓕 g ((pk.2 : ℕ) * Real.log pk.1.1) := by
  have h := pairToNat_injective.tsum_eq (f := term c g)
    (by rw [range_pairToNat]; exact support_term_subset c g)
  have hP : primeSide c g = ∑' n : ℕ, term c g n := rfl
  rw [hP, ← h]
  exact tsum_congr fun pk => term_pair c g pk

/-- Summability of the pair-indexed family, for `1 < c` and `g` integrable. -/
theorem prime_pnat_summable {c : ℝ} (hc : 1 < c) {g : ℝ → ℂ} (hg : Integrable g) :
    Summable fun pk : {p : ℕ // p.Prime} × ℕ+ =>
      ((Real.log pk.1.1 * (pk.1.1 : ℝ) ^ (-((pk.2 : ℕ) * c)) : ℝ) : ℂ)
        * 𝓕 g ((pk.2 : ℕ) * Real.log pk.1.1) := by
  have hs : Summable (term c g ∘ pairToNat) :=
    (primeSide_summable hc hg).comp_injective pairToNat_injective
  refine hs.congr fun pk => ?_
  exact term_pair c g pk

end PrimePowerSide

end
