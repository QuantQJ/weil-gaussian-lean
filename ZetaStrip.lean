import Mathlib
import Reduction

/-!
# Every nontrivial zero of `ζ` lies in the open critical strip

For `ρ` with `Reduction.IsNontrivialZero ρ` (i.e. `ζ ρ = 0`, `ρ` is not a
trivial zero `-2(n+1)`, and `ρ ≠ 1`) we prove `0 < ρ.re ∧ ρ.re < 1`.

**Proven (unconditionally, no custom axioms):**

* `re_lt_one_of_isNontrivialZero` — `ρ.re < 1`. This is the contrapositive of
  Mathlib's `riemannZeta_ne_zero_of_one_le_re` (nonvanishing on `re ≥ 1`).
* `re_pos_of_isNontrivialZero` — `0 < ρ.re`. Via the functional equation
  `riemannZeta_one_sub` applied to `s := 1 - ρ` (so `s.re ≥ 1`): the factors
  `(2π)^(-s)`, `Γ s`, `ζ s` are all nonzero, hence `cos (π s / 2) = 0`, hence
  `s = 2k+1` for an integer `k`, hence `ρ = -2k`; `ρ.re ≤ 0` and `ζ 0 ≠ 0`
  force `k ≥ 1`, so `ρ` would be a trivial zero — contradiction.
* `mem_strip_of_isNontrivialZero` — the conjunction of the two.

Nothing is left unproven: the full target (both strict inequalities) is
established. The results only *locate* the zeros; they say nothing about
`ρ.re = 1/2`.
-/

noncomputable section
open Complex
open scoped Real

namespace ZetaStrip

/-- A nontrivial zero of `ζ` has real part strictly less than `1`
(contrapositive of Mathlib's nonvanishing on `re s ≥ 1`). -/
theorem re_lt_one_of_isNontrivialZero {ρ : ℂ} (h : Reduction.IsNontrivialZero ρ) :
    ρ.re < 1 := by
  by_contra hle
  push_neg at hle
  exact riemannZeta_ne_zero_of_one_le_re hle h.1

/-- A nontrivial zero of `ζ` is not `0`, since `ζ 0 = -1/2`. -/
theorem ne_zero_of_isNontrivialZero {ρ : ℂ} (h : Reduction.IsNontrivialZero ρ) :
    ρ ≠ 0 := by
  rintro rfl
  have h0 := h.1
  rw [riemannZeta_zero] at h0
  norm_num at h0

/-- A nontrivial zero of `ζ` has strictly positive real part. Uses the
functional equation and the nonvanishing of `ζ`, `Γ` and `(2π)^(-s)` on
`re s ≥ 1`, which force `cos (π s / 2) = 0` and hence a trivial zero. -/
theorem re_pos_of_isNontrivialZero {ρ : ℂ} (h : Reduction.IsNontrivialZero ρ) :
    0 < ρ.re := by
  obtain ⟨hζ, hnt, -⟩ := h
  have hρ0 : ρ ≠ 0 := ne_zero_of_isNontrivialZero ⟨hζ, hnt, by
    rintro rfl
    exact riemannZeta_ne_zero_of_one_le_re (by simp) hζ⟩
  by_contra hle
  push_neg at hle
  -- the reflected point
  set s : ℂ := 1 - ρ with hs
  have hsre : 1 ≤ s.re := by
    rw [hs, sub_re, one_re]
    linarith
  have hs1 : s ≠ 1 := by
    intro h1
    apply hρ0
    rw [hs] at h1
    linear_combination -h1
  have hsn : ∀ n : ℕ, s ≠ -n := by
    intro n hn
    have hre := congrArg Complex.re hn
    rw [neg_re, natCast_re] at hre
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  -- functional equation at `s`
  have hfe := riemannZeta_one_sub hsn hs1
  have h1s : 1 - s = ρ := by rw [hs]; ring
  rw [h1s, hζ] at hfe
  have hζs : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hsre
  have hΓ : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpow : (2 * π : ℂ) ^ (-s) ≠ 0 := by
    intro hp
    rw [cpow_eq_zero_iff] at hp
    have h2 := hp.1
    rw [mul_eq_zero] at h2
    rcases h2 with h2 | h2
    · norm_num at h2
    · exact hπ h2
  have hcos : cos (π * s / 2) = 0 := by
    by_contra hc
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpow) hΓ) hc) hζs)
      hfe.symm
  -- `s = 2k + 1` for an integer `k`
  obtain ⟨k, hk⟩ := cos_eq_zero_iff.mp hcos
  have hsk : s = 2 * k + 1 := by
    apply mul_left_cancel₀ hπ
    linear_combination 2 * hk
  have hρk : ρ = -2 * k := by
    rw [← h1s, hsk]; ring
  -- `k ≥ 1`
  have hρre : ρ.re = -2 * k := by
    rw [hρk]
    simp
  have hk0 : (0 : ℝ) ≤ k := by linarith
  have hk0' : (0 : ℤ) ≤ k := by exact_mod_cast hk0
  have hkne : k ≠ 0 := by
    rintro rfl
    apply hρ0
    rw [hρk]
    simp
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ k - 1 by omega)
  apply hnt
  refine ⟨n, ?_⟩
  have hkn : (k : ℂ) = n + 1 := by
    have : k = (n : ℤ) + 1 := by omega
    rw [this]
    push_cast
    ring
  rw [hρk, hkn]

/-- Every nontrivial zero of `ζ` lies in the open critical strip
`0 < re ρ < 1`. -/
theorem mem_strip_of_isNontrivialZero {ρ : ℂ} (h : Reduction.IsNontrivialZero ρ) :
    0 < ρ.re ∧ ρ.re < 1 :=
  ⟨re_pos_of_isNontrivialZero h, re_lt_one_of_isNontrivialZero h⟩

end ZetaStrip

end
