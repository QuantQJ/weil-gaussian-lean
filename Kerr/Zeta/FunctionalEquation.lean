import Kerr.Zeta.Conjugation
import Mathlib

/-!
# File-14 RH scaffold: the statements that are now proved

Source: `File-14/formal_proofs/riemann_hypothesis_complete.lean` (QJ). That file states its
definitions and ~30 theorems, most with `sorry`. This module keeps the source's definitions and
proves the statements that are true and provable from Mathlib plus `Kerr.ZetaConj`.

Two source statements are **false as written** because of Mathlib's convention `Γ(−n) = 0`
at the poles of Γ; corrected versions (restricted to the critical strip, where they are the
intended statements) are proved below:
* `zeta_functional_equation` fails at `s = −2` (LHS `= 0`, RHS `≠ 0`).
* `functional_equation` (for the source's `xi`) fails at `s = −2` for the same reason.
Also false as written: `de_la_vallee_poussin_region` quantifies over **every** `A > 0`, which
fails for `A > (log 16)/2` (it would exclude the zero at `1/2 + 14.13…i`); the true theorem has
one fixed small `A`. It is not included here.

Ported to Lean v4.16 / Mathlib, 2026-11-11.
-/

noncomputable section
open Complex
open scoped ComplexConjugate Real

namespace Kerr.File14RH

/-- Non-trivial zeros (source definition). -/
def IsNonTrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1

/-- The critical line (source definition). -/
def IsOnCriticalLine (s : ℂ) : Prop :=
  s.re = 1 / 2

/-- The source's Riemann Hypothesis. -/
def RiemannHypothesis' : Prop :=
  ∀ s : ℂ, IsNonTrivialZero s → IsOnCriticalLine s

/-- Zero-free region `Re s ≥ 1` (source; from Mathlib). -/
theorem zero_free_region (s : ℂ) (h : 1 ≤ s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re h

/-- From hp-proof/ZeroSymmetry.lean (QJ). -/
theorem bernoulli_two_mul_ne_zero {k : ℕ} (hk : k ≠ 0) : bernoulli (2 * k) ≠ 0 := by
  intro h
  have hζ := riemannZeta_two_mul_nat hk
  rw [h] at hζ
  simp only [Rat.cast_zero, mul_zero, zero_div] at hζ
  have hre : 1 < ((2 * k : ℕ) : ℂ).re := by
    rw [Complex.natCast_re]
    exact_mod_cast (by omega : 1 < 2 * k)
  exact riemannZeta_ne_zero_of_one_lt_re hre (by exact_mod_cast hζ)

/-- `ζ` does not vanish at the negative odd integers `−(2m+1)`. -/
theorem riemannZeta_neg_odd_ne_zero (m : ℕ) : riemannZeta (-(2 * m + 1 : ℂ)) ≠ 0 := by
  have h := riemannZeta_neg_nat_eq_bernoulli (2 * m + 1)
  have hcast : (-(2 * m + 1 : ℂ)) = -((2 * m + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [hcast, h]
  have hB : bernoulli (2 * m + 1 + 1) ≠ 0 := by
    have : 2 * m + 1 + 1 = 2 * (m + 1) := by ring
    rw [this]
    exact bernoulli_two_mul_ne_zero (Nat.succ_ne_zero m)
  have hB' : (bernoulli (2 * m + 1 + 1) : ℂ) ≠ 0 := by exact_mod_cast hB
  have hden : (((2 * m + 1 : ℕ) : ℂ) + 1) ≠ 0 := by
    have : (((2 * m + 1 : ℕ) : ℂ) + 1) = ((2 * m + 1 + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this]
    exact_mod_cast Nat.succ_ne_zero (2 * m + 1)
  exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hB') hden


/-- Every zero of `ζ` with `Re s ≤ 0` is trivial (or `s = 0`, which is not a zero). -/
theorem zero_re_pos {s : ℂ} (hz : riemannZeta s = 0) (htriv : ¬∃ n : ℕ, s = -2 * (n + 1)) :
    0 < s.re := by
  by_contra hre
  push_neg at hre
  by_cases hn : ∃ m : ℕ, s = -(m : ℂ)
  · obtain ⟨m, rfl⟩ := hn
    rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simp at hk; subst hk; simp [riemannZeta_zero] at hz
      · apply htriv; refine ⟨k - 1, ?_⟩
        rw [hk]; push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hk0.ne')]; ring
    · apply riemannZeta_neg_odd_ne_zero k
      rw [hk] at hz; push_cast at hz; exact hz
  · have h1 : ∀ n : ℕ, (1 - s) ≠ -(n : ℂ) := by
      intro n e; have := congrArg Complex.re e; simp at this
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h2 : (1 - s) ≠ 1 := by
      intro e; apply hn; exact ⟨0, by simp; linear_combination -e⟩
    have fe := riemannZeta_one_sub h1 h2
    rw [sub_sub_cancel, hz] at fe
    have hre1 : 1 ≤ (1 - s).re := by simp; linarith
    have hz1 : riemannZeta (1 - s) ≠ 0 := riemannZeta_ne_zero_of_one_le_re hre1
    have hg : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    have hp : (2 : ℂ) * (2 * (π : ℂ)) ^ (-(1 - s)) ≠ 0 := by
      refine mul_ne_zero two_ne_zero ?_
      rw [Ne, Complex.cpow_eq_zero_iff]; push_neg
      intro h; exfalso; exact (by exact_mod_cast Real.pi_pos.ne' : (π : ℂ) ≠ 0) (by
        have := h; simpa using this)
    have hc : Complex.cos (π * (1 - s) / 2) ≠ 0 := by
      rw [Ne, Complex.cos_eq_zero_iff]
      rintro ⟨k, hk⟩
      have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
      have hs : s = -(2 * (k : ℂ)) := by
        apply mul_left_cancel₀ hpi; linear_combination (-2 : ℂ) * hk
      have hkre : (k : ℝ) ≥ 0 := by
        have := congrArg Complex.re hs; simp at this; linarith
      have hk0 : 0 ≤ k := by exact_mod_cast hkre
      have hkc : ((k.toNat : ℕ) : ℂ) = (k : ℂ) := by exact_mod_cast Int.toNat_of_nonneg hk0
      apply hn; refine ⟨(2 * k.toNat), ?_⟩
      rw [hs]; push_cast; rw [hkc]
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hp hg) hc) hz1) fe.symm

/-- Zeros of `ζ` other than the trivial ones and `s = 1` lie in the open strip. -/
theorem zero_mem_strip {s : ℂ} (hz : riemannZeta s = 0) (htriv : ¬∃ n : ℕ, s = -2 * (n + 1)) :
    0 < s.re ∧ s.re < 1 := by
  refine ⟨zero_re_pos hz htriv, ?_⟩
  by_contra h; push_neg at h
  exact riemannZeta_ne_zero_of_one_le_re h hz

/-- **The source's RH is Mathlib's `RiemannHypothesis`.** -/
theorem riemannHypothesis'_iff : RiemannHypothesis' ↔ RiemannHypothesis := by
  constructor
  · intro h s hz htriv _
    exact h s ⟨hz, zero_mem_strip hz htriv⟩
  · intro h s hs
    refine h s hs.1 ?_ ?_
    · rintro ⟨n, hn⟩
      have := congrArg Complex.re hn; simp at this
      linarith [hs.2.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    · intro e; have := congrArg Complex.re e; simp at this; linarith [hs.2.2]

lemma ne_neg_nat_of_re_pos {s : ℂ} (h : 0 < s.re) (n : ℕ) : s ≠ -(n : ℂ) := by
  intro e; have := congrArg Complex.re e; simp at this
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

lemma ne_one_of_re_lt {s : ℂ} (h : s.re < 1) : s ≠ 1 := by
  intro e; rw [e] at h; simp at h

/-- **Zero symmetry, `1 − s` form** (source section 17). -/
theorem zero_symmetry' (s : ℂ) (hs : IsNonTrivialZero s) : IsNonTrivialZero (1 - s) := by
  obtain ⟨hz, h0, h1⟩ := hs
  refine ⟨?_, by simp; linarith, by simp; linarith⟩
  rw [riemannZeta_one_sub (ne_neg_nat_of_re_pos h0) (ne_one_of_re_lt h1), hz, mul_zero]

/-- **Zero symmetry, `1 − conj ρ` form** (source section 7). -/
theorem zero_symmetry (ρ : ℂ) (hρ : IsNonTrivialZero ρ) : IsNonTrivialZero (1 - conj ρ) := by
  apply zero_symmetry'
  obtain ⟨hz, h0, h1⟩ := hρ
  refine ⟨?_, by simpa using h0, by simpa using h1⟩
  rw [Kerr.ZetaConj.riemannZeta_conj, hz, map_zero]

/-- Zeros are symmetric about the critical line (source). -/
theorem zero_symmetry_critical_line (ρ : ℂ) (_hρ : IsNonTrivialZero ρ) :
    IsOnCriticalLine ρ ↔ IsOnCriticalLine (1 - conj ρ) := by
  unfold IsOnCriticalLine
  simp only [sub_re, one_re, conj_re]
  constructor <;> intro h <;> linarith

lemma gammaR_mul_zeta {s : ℂ} (h : 0 < s.re) :
    (π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * riemannZeta s = completedRiemannZeta s := by
  have hs0 : s ≠ 0 := by intro e; rw [e] at h; simp at h
  rw [riemannZeta_def_of_ne_zero hs0, ← Complex.Gammaℝ_def, mul_div_cancel₀ _ (Complex.Gammaℝ_ne_zero_of_re_pos h)]

/-- **Functional equation for `ζ`, on the critical strip** (corrected source statement; the
source's hypothesis `Re s ≠ 0, 1` lets in `s = −2`, where it fails). -/
theorem zeta_functional_equation (s : ℂ) (hs : 0 < s.re ∧ s.re < 1) :
    (π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * riemannZeta s =
    (π : ℂ) ^ (-(1 - s) / 2) * Complex.Gamma ((1 - s) / 2) * riemannZeta (1 - s) := by
  rw [gammaR_mul_zeta hs.1, gammaR_mul_zeta (by simp; linarith), completedRiemannZeta_one_sub]

/-- The source's ξ. -/
def xi (s : ℂ) : ℂ :=
  s * (s - 1) * (π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * riemannZeta s

/-- **`ξ(s) = ξ(1 − s)` on the critical strip** (corrected source statement). -/
theorem functional_equation (s : ℂ) (hs : 0 < s.re ∧ s.re < 1) : xi s = xi (1 - s) := by
  have e1 : xi s = s * (s - 1) * ((π : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * riemannZeta s) := by
    unfold xi; ring
  have e2 : xi (1 - s) = (1 - s) * (1 - s - 1) *
      ((π : ℂ) ^ (-(1 - s) / 2) * Complex.Gamma ((1 - s) / 2) * riemannZeta (1 - s)) := by
    unfold xi; ring
  rw [e1, e2, zeta_functional_equation s hs]; ring

end Kerr.File14RH
