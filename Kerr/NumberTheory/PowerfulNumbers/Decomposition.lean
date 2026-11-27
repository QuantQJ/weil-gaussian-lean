/-
Copyright 2026 James C. Kerr (QuantQJ). Apache-2.0.
The definitions `Full`, `Powerful`, `Q`, `A`, `B` and the proposition `ErrorTermImprovement`
are copied (statement only) from google-deepmind/formal-conjectures,
`FormalConjecturesForMathlib/Data/Nat/Full.lean` and
`FormalConjectures/Wikipedia/PowerfulNumbersDensity.lean` (commit a425ca3e), Apache-2.0,
© 2025-2026 The Formal Conjectures Authors.
-/
import Mathlib

/-!
# Powerful numbers: `n = a²b³` with `b` squarefree, and `Q(x) = ∑_d μ(d) D(x/d⁶)`

* `pow_two_mul_pow_three_powerful`, `exists_sq_mul_cube_of_powerful`,
  `sq_mul_cube_injective`: every powerful `n ≥ 1` is `a²b³` with `b` squarefree, uniquely.
* `Q_eq_card_pairs`: `Q(x) = #{(a,b) : b squarefree, a²b³ ≤ x}`.
* `sum_moebius_sq_dvd`: `∑_{d² ∣ b} μ(d) = [b squarefree]`.
* `Q_eq_sum_moebius_D`: `Q(x) = ∑_{d ≤ x} μ(d) D(x/d⁶)`, `D(y) = #{(a,c) ≥ 1 : a²c³ ≤ y}`.
-/

noncomputable section
open Finset

open scoped ArithmeticFunction.Moebius

namespace Kerr.PowerfulNumbers

/-- (formal-conjectures) `n` is `k`-full if `p^k ∣ n` for every prime factor `p` of `n`. -/
def Full (k : ℕ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ^ k ∣ n

/-- (formal-conjectures) Powerful = `2`-full. -/
abbrev Powerful : ℕ → Prop := Full 2

instance Powerful.decide (n : ℕ) : Decidable (Powerful n) := by
  dsimp [Powerful, Full]; infer_instance

/-- (formal-conjectures) `Q(x)` = number of powerful `n` with `1 ≤ n ≤ x`. -/
noncomputable abbrev Q (x : ℝ) : ℕ := {n : ℕ | 0 < n ∧ Powerful n ∧ (n : ℝ) ≤ x}.ncard

/-- `D(x) = #{(a,c) : 1 ≤ a, 1 ≤ c, a²c³ ≤ x}` (the `(2,3)` divisor problem). -/
def D (x : ℝ) : ℕ :=
  ((Icc 1 ⌊x⌋₊ ×ˢ Icc 1 ⌊x⌋₊).filter (fun p : ℕ × ℕ => ((p.1 ^ 2 * p.2 ^ 3 : ℕ) : ℝ) ≤ x)).card

theorem pow_two_mul_pow_three_powerful (a b : ℕ) : Powerful (a ^ 2 * b ^ 3) := by
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hd := Nat.dvd_of_mem_primeFactors hp
  rcases (Nat.Prime.dvd_mul hpp).mp hd with h | h
  · exact (pow_dvd_pow_of_dvd (hpp.dvd_of_dvd_pow h) 2).mul_right _
  · have : p ^ 2 ∣ b ^ 3 :=
      (pow_dvd_pow p (by norm_num : 2 ≤ 3)).trans (pow_dvd_pow_of_dvd (hpp.dvd_of_dvd_pow h) 3)
    exact this.mul_left _

theorem exists_sq_mul_cube_of_powerful {n : ℕ} (hn : 0 < n) (hP : Powerful n) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ Squarefree b ∧ a ^ 2 * b ^ 3 = n := by
  obtain ⟨s, t, hs, ht, hst, hsf⟩ := Nat.sq_mul_squarefree_of_pos hn
  -- every prime factor of `s` divides `t`
  have hdiv : s ∣ t := by
    rw [← Nat.prod_primeFactors_of_squarefree hsf]
    refine Finset.prod_primes_dvd t (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime)
      (fun p hp => ?_)
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hps := Nat.dvd_of_mem_primeFactors hp
    by_contra hpt
    have hpn : p ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpp, hst ▸ hps.mul_left _, hn.ne'⟩
    have h2 : p ^ 2 ∣ t ^ 2 * s := hst ▸ hP p hpn
    have hcop : Nat.Coprime (p ^ 2) (t ^ 2) :=
      Nat.Coprime.pow 2 2 ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hpt)
    have h3 : p ^ 2 ∣ s := hcop.dvd_of_dvd_mul_left h2
    have := hsf p (by rw [← pow_two]; exact h3)
    exact hpp.one_lt.ne' (Nat.isUnit_iff.mp this)
  obtain ⟨u, rfl⟩ := hdiv
  refine ⟨u, s, Nat.pos_of_ne_zero (by rintro rfl; simp at ht), hs, hsf, ?_⟩
  rw [← hst]; ring

theorem sq_mul_cube_injective {a b a' b' : ℕ} (ha : a ≠ 0) (hb : Squarefree b) (ha' : a' ≠ 0)
    (hb' : Squarefree b') (h : a ^ 2 * b ^ 3 = a' ^ 2 * b' ^ 3) : a = a' ∧ b = b' := by
  have hb0 := hb.ne_zero
  have hb0' := hb'.ne_zero
  have key : ∀ p, a.factorization p = a'.factorization p ∧ b.factorization p = b'.factorization p := by
    intro p
    have e := congrArg (fun n => n.factorization p) h
    change (a ^ 2 * b ^ 3).factorization p = (a' ^ 2 * b' ^ 3).factorization p at e
    rw [Nat.factorization_mul (pow_ne_zero _ ha) (pow_ne_zero _ hb0),
      Nat.factorization_mul (pow_ne_zero _ ha') (pow_ne_zero _ hb0'),
      Nat.factorization_pow, Nat.factorization_pow, Nat.factorization_pow,
      Nat.factorization_pow] at e
    simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e
    have h1 := hb.natFactorization_le_one p
    have h2 := hb'.natFactorization_le_one p
    omega
  exact ⟨Nat.eq_of_factorization_eq ha ha' (fun p => (key p).1),
    Nat.eq_of_factorization_eq hb0 hb0' (fun p => (key p).2)⟩

/-- `Q(x) = #{(a,b) ∈ [1,⌊x⌋]² : b squarefree, a²b³ ≤ x}`. -/
theorem Q_eq_card_pairs (x : ℝ) :
    Q x = ((Icc 1 ⌊x⌋₊ ×ˢ Icc 1 ⌊x⌋₊).filter
      (fun p : ℕ × ℕ => Squarefree p.2 ∧ ((p.1 ^ 2 * p.2 ^ 3 : ℕ) : ℝ) ≤ x)).card := by
  have hset : {n : ℕ | 0 < n ∧ Powerful n ∧ (n : ℝ) ≤ x} =
      ↑((Icc 1 ⌊x⌋₊).filter Powerful) := by
    ext n
    simp only [Set.mem_ofPred_eq, coe_filter, mem_Icc]
    constructor
    · rintro ⟨h0, hP, hx⟩
      exact ⟨⟨h0, (Nat.le_floor_iff' h0.ne').mpr hx⟩, hP⟩
    · rintro ⟨⟨h0, hx⟩, hP⟩
      exact ⟨h0, hP, (Nat.le_floor_iff' (by omega)).mp hx⟩
  rw [Q, hset, Set.ncard_coe_finset]
  symm
  refine card_bij (fun p _ => p.1 ^ 2 * p.2 ^ 3) ?_ ?_ ?_
  · rintro ⟨a, b⟩ hab
    simp only [mem_filter, mem_product, mem_Icc] at hab ⊢
    obtain ⟨⟨⟨ha1, -⟩, hb1, -⟩, -, hx⟩ := hab
    have hpos : 0 < a ^ 2 * b ^ 3 := by positivity
    exact ⟨⟨hpos, (Nat.le_floor_iff' hpos.ne').mpr hx⟩, pow_two_mul_pow_three_powerful a b⟩
  · rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' h
    simp only [mem_filter, mem_product, mem_Icc] at hab hab'
    obtain ⟨e1, e2⟩ := sq_mul_cube_injective (by omega) hab.2.1 (by omega) hab'.2.1 h
    exact Prod.ext e1 e2
  · intro n hn
    simp only [mem_filter, mem_Icc] at hn
    obtain ⟨⟨h1, hN⟩, hP⟩ := hn
    obtain ⟨a, b, ha, hb, hsf, rfl⟩ := exists_sq_mul_cube_of_powerful h1 hP
    have hale : a ≤ a ^ 2 * b ^ 3 :=
      le_trans (Nat.le_self_pow (by norm_num) a) (Nat.le_mul_of_pos_right _ (by positivity))
    have hble : b ≤ a ^ 2 * b ^ 3 :=
      le_trans (Nat.le_self_pow (by norm_num) b) (Nat.le_mul_of_pos_left _ (by positivity))
    refine ⟨(a, b), ?_, rfl⟩
    simp only [mem_filter, mem_product, mem_Icc]
    refine ⟨⟨⟨ha, hale.trans hN⟩, hb, hble.trans hN⟩, hsf, ?_⟩
    exact (Nat.le_floor_iff' (by positivity)).mp hN

/-- `∑_{d ∣ t} μ(d) = [t = 1]`. -/
theorem sum_divisors_moebius (t : ℕ) :
    ∑ d ∈ t.divisors, (μ d : ℤ) = if t = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f t) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  exact h

/-- `∑_{1 ≤ d ≤ N, d² ∣ b} μ(d) = [b squarefree]` for `1 ≤ b ≤ N`. -/
theorem sum_moebius_sq_dvd {b N : ℕ} (hb : 0 < b) (hbN : b ≤ N) :
    ∑ d ∈ (Icc 1 N).filter (fun d => d ^ 2 ∣ b), (μ d : ℤ) = if Squarefree b then 1 else 0 := by
  obtain ⟨s, t, hs, ht, hts, hsf⟩ := Nat.sq_mul_squarefree_of_pos hb
  have hset : (Icc 1 N).filter (fun d => d ^ 2 ∣ b) = t.divisors := by
    ext d
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd1, -⟩, hdb⟩
      refine ⟨?_, ht.ne'⟩
      have hd0 : d ≠ 0 := by omega
      rw [← Nat.factorization_le_iff_dvd hd0 ht.ne']
      intro p
      have h1 := (Nat.factorization_le_iff_dvd (pow_ne_zero 2 hd0) hb.ne').mpr hdb p
      rw [← hts, Nat.factorization_mul (pow_ne_zero 2 ht.ne') hs.ne', Nat.factorization_pow,
        Nat.factorization_pow] at h1
      simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul] at h1
      have h2 := hsf.natFactorization_le_one p
      omega
    · rintro ⟨hdt, -⟩
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdt ht
      have hdb : d ^ 2 ∣ b := hts ▸ (pow_dvd_pow_of_dvd hdt 2).mul_right s
      have hdle : d ≤ b := le_trans (Nat.le_self_pow (by norm_num) d) (Nat.le_of_dvd hb hdb)
      exact ⟨⟨hd1, hdle.trans hbN⟩, hdb⟩
  rw [hset, sum_divisors_moebius]
  by_cases h1 : t = 1
  · subst h1; simp only [one_pow, one_mul] at hts; subst hts; simp [hsf]
  · rw [if_neg h1, if_neg]
    intro hsq
    have : IsUnit t := hsq t (hts ▸ ⟨s, by ring⟩)
    exact h1 (Nat.isUnit_iff.mp this)

/-- **Möbius decomposition.** `Q(x) = ∑_{1 ≤ d ≤ x} μ(d) D(x/d⁶)`. -/
theorem Q_eq_sum_moebius_D (x : ℝ) :
    (Q x : ℤ) = ∑ d ∈ Icc 1 ⌊x⌋₊, (μ d : ℤ) * (D (x / (d : ℝ) ^ 6) : ℤ) := by
  set N := ⌊x⌋₊ with hN
  set P := (Icc 1 N ×ˢ Icc 1 N).filter
    (fun p : ℕ × ℕ => ((p.1 ^ 2 * p.2 ^ 3 : ℕ) : ℝ) ≤ x) with hP
  have h1 : (Q x : ℤ) = ∑ p ∈ P, (if Squarefree p.2 then 1 else 0 : ℤ) := by
    rw [sum_boole, hP, filter_filter, Q_eq_card_pairs, ← hN]
    congr 2
    ext p; simp only [mem_filter]; tauto
  have h2 : ∀ p ∈ P, (if Squarefree p.2 then 1 else 0 : ℤ) =
      ∑ d ∈ Icc 1 N, if d ^ 2 ∣ p.2 then (μ d : ℤ) else 0 := by
    intro p hp
    simp only [hP, mem_filter, mem_product, mem_Icc] at hp
    rw [← sum_moebius_sq_dvd (by omega) hp.1.2.2, sum_filter]
  rw [h1, sum_congr rfl h2, sum_comm]
  refine sum_congr rfl (fun d hd => ?_)
  simp only [mem_Icc] at hd
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  -- `#{(a,b) ∈ P : d² ∣ b} = D(x/d⁶)`
  have hd0 : (0 : ℝ) < (d : ℝ) ^ 6 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd.1
    positivity
  have hdpos : 0 < d := hd.1
  rw [Nat.cast_inj]
  symm
  refine card_bij (fun p _ => (p.1, d ^ 2 * p.2)) ?_ ?_ ?_
  · rintro ⟨a, c⟩ hac
    simp only [D, hP, mem_filter, mem_product, mem_Icc] at hac ⊢
    obtain ⟨⟨⟨ha1, -⟩, hc1, -⟩, hx⟩ := hac
    rw [le_div_iff₀ hd0] at hx
    have hx' : ((a ^ 2 * (d ^ 2 * c) ^ 3 : ℕ) : ℝ) ≤ x := by
      have e : ((a ^ 2 * (d ^ 2 * c) ^ 3 : ℕ) : ℝ) = ((a ^ 2 * c ^ 3 : ℕ) : ℝ) * (d : ℝ) ^ 6 := by
        push_cast; ring
      rw [e]; exact hx
    have hpos : 0 < a ^ 2 * (d ^ 2 * c) ^ 3 := by positivity
    have hle : a ^ 2 * (d ^ 2 * c) ^ 3 ≤ N := (Nat.le_floor_iff' hpos.ne').mpr hx'
    have hale : a ≤ a ^ 2 * (d ^ 2 * c) ^ 3 :=
      le_trans (Nat.le_self_pow (by norm_num) a) (Nat.le_mul_of_pos_right _ (by positivity))
    have hble : d ^ 2 * c ≤ a ^ 2 * (d ^ 2 * c) ^ 3 :=
      le_trans (Nat.le_self_pow (by norm_num) _) (Nat.le_mul_of_pos_left _ (by positivity))
    refine ⟨⟨⟨⟨ha1, hale.trans hle⟩, Nat.mul_pos (pow_pos hdpos 2) hc1, hble.trans hle⟩, hx'⟩,
      dvd_mul_right _ _⟩
  · rintro ⟨a, c⟩ _ ⟨a', c'⟩ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    have : d ^ 2 ≠ 0 := pow_ne_zero 2 (by omega)
    rw [Nat.mul_left_cancel (Nat.pos_of_ne_zero this) h2]
  · rintro ⟨a, b⟩ hab
    simp only [hP, mem_filter, mem_product, mem_Icc] at hab
    obtain ⟨⟨⟨⟨ha1, haN⟩, hb1, hbN⟩, hx⟩, ⟨c, rfl⟩⟩ := hab
    have hc1 : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h; simp at hb1
      · exact h
    refine ⟨(a, c), ?_, rfl⟩
    simp only [D, mem_filter, mem_product, mem_Icc]
    have hx' : ((a ^ 2 * c ^ 3 : ℕ) : ℝ) ≤ x / (d : ℝ) ^ 6 := by
      rw [le_div_iff₀ hd0]
      have e : ((a ^ 2 * c ^ 3 : ℕ) : ℝ) * (d : ℝ) ^ 6 = ((a ^ 2 * (d ^ 2 * c) ^ 3 : ℕ) : ℝ) := by
        push_cast; ring
      rw [e]; exact hx
    have hpos : 0 < a ^ 2 * c ^ 3 := by positivity
    have hle : a ^ 2 * c ^ 3 ≤ ⌊x / (d : ℝ) ^ 6⌋₊ := (Nat.le_floor_iff' hpos.ne').mpr hx'
    have hale : a ≤ a ^ 2 * c ^ 3 :=
      le_trans (Nat.le_self_pow (by norm_num) a) (Nat.le_mul_of_pos_right _ (by positivity))
    have hcle : c ≤ a ^ 2 * c ^ 3 :=
      le_trans (Nat.le_self_pow (by norm_num) c) (Nat.le_mul_of_pos_left _ (by positivity))
    exact ⟨⟨⟨ha1, hale.trans hle⟩, hc1, hcle.trans hle⟩, hx'⟩

end Kerr.PowerfulNumbers
