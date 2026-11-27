import Mathlib

/-!
# Zero-free regions `σ > 1 − 1/(R log(q·max(1,|t|)))` for Dirichlet `L`-functions from the `7/8` half-plane

**The hypothesis.** `DirichletQuasiRH` is OpenAI's statement
`OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`, copied verbatim (binders and
conclusion) from `lean/ComparatorChallenges/DirichletSevenEighths.lean` of https://github.com/openai/math
(Apache-2.0, Copyright (c) OpenAI): for every modulus `q`, every Dirichlet character `χ` mod `q` and
every `s` with `7/8 < Re s`, `L(s,χ) ≠ 0` unless `χ = 1` and `s = 1`. It is carried as a hypothesis
(a `Prop` in every theorem's signature), never as an `axiom`, exactly as `QuasiRHWiring.QuasiRH` carries
the `ζ` case.

**The regions.** Write `ℓ(q,t) = log(q·max(1,|t|))` (`logQT`). For `q ≥ q₀ ≥ 2` and all `t`,
`ℓ(q,t) ≥ log q₀`, with equality at `q = q₀`, `|t| ≤ 1`. Hence:

* `re_gt_of_region_strict` / `LFunction_ne_zero_region_strict`: for `R ≥ 8/log q₀`, every `s` with
  `Re s > 1 − 1/(R ℓ(q, Im s))` has `Re s > 7/8`, so `L(s,χ) ≠ 0` (all `χ` mod `q`, principal or not,
  primitive or not; the only exception is the pole `χ = 1`, `s = 1`).
* `LFunction_ne_zero_region`: the closed form `Re s ≥ 1 − 1/(R ℓ)` for every `R > 8/log q₀`.
* `region_subset_halfPlane_iff`: `R = 8/log q₀` is the least `R` for which the region (for all `q ≥ q₀`,
  all `t`) lies inside `Re s > 7/8`; so `8/log q₀` is the best constant of this shape that the half-plane
  gives.
* Numerics: `six_four_lt_eight_div_log_three` (`8/log 3 > 6.4`), `five_six_lt_eight_div_log_four`
  (`8/log 4 > 5.6`), `eight_div_log_five_lt` (`8/log 5 < 5.05`).
* `LFunction_ne_zero_q_ge_three`: `q ≥ 3`, `R = 8/log 3` (strict region; `8/log 3 = 7.28…`).
* `LFunction_ne_zero_kadiri_shape`: `q ≥ 5`, `Re s ≥ 1 − 1/(5.60 ℓ(q,t))` (Kadiri's form and constant),
  and `LFunction_ne_zero_q_ge_five`: `q ≥ 5`, `R = 8/log 5 < 5.05` (strict region).

There is no exceptional zero in any of these regions: the half-plane hypothesis has none.

Published comparison: H. Kadiri, *Explicit zero-free regions for Dirichlet L-functions*, Theorem 1.1:
`L(s,χ) ≠ 0` for `Re s ≥ 1 − 1/(5.60 log(q·max(1,|Im s|)))`, for `3 ≤ q ≤ 400 000` and primitive
nonprincipal `χ` (unconditional; it uses Platt's partial GRH verification for those moduli). The results
here are conditional on `DirichletQuasiRH`, hold for every modulus and every character, and give a smaller
`R` than `5.60` exactly from `q₀ = 5` on; at `q₀ = 3, 4` they give `R = 8/log q₀ > 5.6`.
-/

set_option autoImplicit false
noncomputable section
open Complex

namespace FleetDirichletZeroFree

/-- **OpenAI's Dirichlet `7/8` half-plane, as a hypothesis.** The statement of
`OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re` from
https://github.com/openai/math, `lean/ComparatorChallenges/DirichletSevenEighths.lean`
(Apache-2.0, Copyright (c) OpenAI), with its binders turned into a `∀`. -/
def DirichletQuasiRH : Prop :=
  ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ},
    (7 / 8 : ℝ) < s.re → ¬ (χ = 1 ∧ s = 1) → DirichletCharacter.LFunction χ s ≠ 0

/-- `ℓ(q,t) = log(q · max(1,|t|))`. -/
def logQT (q : ℕ) (t : ℝ) : ℝ := Real.log (q * max 1 |t|)

lemma log_le_logQT {q₀ q : ℕ} (hq₀ : 1 ≤ q₀) (hq : q₀ ≤ q) (t : ℝ) :
    Real.log q₀ ≤ logQT q t := by
  unfold logQT
  have h0 : (0 : ℝ) < q₀ := by exact_mod_cast hq₀
  have h1 : (q₀ : ℝ) ≤ q := by exact_mod_cast hq
  have h2 : (1 : ℝ) ≤ max 1 |t| := le_max_left _ _
  apply Real.log_le_log h0
  nlinarith

lemma logQT_of_abs_le_one (q : ℕ) {t : ℝ} (ht : |t| ≤ 1) : logQT q t = Real.log q := by
  unfold logQT
  rw [max_eq_left ht, mul_one]

lemma log_pos_of_two_le {q₀ : ℕ} (hq₀ : 2 ≤ q₀) : 0 < Real.log q₀ :=
  Real.log_pos (by exact_mod_cast (show 1 < q₀ by omega))

/-- **Geometry (strict form).** For `q ≥ q₀ ≥ 2` and `R ≥ 8/log q₀`,
`Re s > 1 − 1/(R ℓ(q, Im s))` implies `Re s > 7/8`. -/
theorem re_gt_of_region_strict {q₀ q : ℕ} (hq₀ : 2 ≤ q₀) (hq : q₀ ≤ q) {R : ℝ}
    (hR : 8 / Real.log q₀ ≤ R) {s : ℂ} (hs : 1 - 1 / (R * logQT q s.im) < s.re) :
    7 / 8 < s.re := by
  have hl0 := log_pos_of_two_le hq₀
  have hl := log_le_logQT (by omega) hq s.im
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  have h8 : 8 ≤ R * logQT q s.im := by
    calc (8 : ℝ) = 8 / Real.log q₀ * Real.log q₀ := by field_simp
      _ ≤ R * logQT q s.im := mul_le_mul hR hl hl0.le hR0.le
  have : 1 / (R * logQT q s.im) ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) h8
  linarith

/-- **Geometry (closed form).** For `q ≥ q₀ ≥ 2` and `R > 8/log q₀`,
`Re s ≥ 1 − 1/(R ℓ(q, Im s))` implies `Re s > 7/8`. -/
theorem re_gt_of_region {q₀ q : ℕ} (hq₀ : 2 ≤ q₀) (hq : q₀ ≤ q) {R : ℝ}
    (hR : 8 / Real.log q₀ < R) {s : ℂ} (hs : 1 - 1 / (R * logQT q s.im) ≤ s.re) :
    7 / 8 < s.re := by
  have hl0 := log_pos_of_two_le hq₀
  have hl := log_le_logQT (by omega) hq s.im
  have hR0 : 0 < R := lt_of_le_of_lt (by positivity) hR
  have h8 : 8 < R * logQT q s.im := by
    calc (8 : ℝ) = 8 / Real.log q₀ * Real.log q₀ := by field_simp
      _ < R * Real.log q₀ := by gcongr
      _ ≤ R * logQT q s.im := by gcongr
  have : 1 / (R * logQT q s.im) < 1 / 8 := one_div_lt_one_div_of_lt (by norm_num) h8
  linarith

/-- **Optimality of `8/log q₀`.** For `q₀ ≥ 2` and `R > 0`: the strict region
`Re s > 1 − 1/(R ℓ(q, Im s))`, for all `q ≥ q₀` and all `s`, lies inside the half-plane `Re s > 7/8`
if and only if `R ≥ 8/log q₀`. -/
theorem region_subset_halfPlane_iff {q₀ : ℕ} (hq₀ : 2 ≤ q₀) {R : ℝ} (hR : 0 < R) :
    (∀ q : ℕ, q₀ ≤ q → ∀ s : ℂ, 1 - 1 / (R * logQT q s.im) < s.re → 7 / 8 < s.re) ↔
      8 / Real.log q₀ ≤ R := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have hl0 := log_pos_of_two_le hq₀
    have hRl : R * Real.log q₀ < 8 := by
      have := mul_lt_mul_of_pos_right hlt hl0
      rwa [div_mul_cancel₀ _ hl0.ne'] at this
    have hpos : 0 < R * Real.log q₀ := by positivity
    have hlt8 : 1 / 8 < 1 / (R * Real.log q₀) := one_div_lt_one_div_of_lt hpos hRl
    have := h q₀ le_rfl ((7 / 8 : ℝ) : ℂ) (by
      rw [Complex.ofReal_im, logQT_of_abs_le_one q₀ (by simp), Complex.ofReal_re]
      linarith)
    rw [Complex.ofReal_re] at this
    exact lt_irrefl _ this
  · intro hR' q hq s hs
    exact re_gt_of_region_strict hq₀ hq hR' hs

/-- **Zero-free region (strict form)** from `DirichletQuasiRH`: for `q ≥ q₀ ≥ 2`, `R ≥ 8/log q₀`,
every Dirichlet character `χ` mod `q`, `L(s,χ) ≠ 0` when `Re s > 1 − 1/(R log(q·max(1,|Im s|)))`,
except at the pole `χ = 1`, `s = 1`. -/
theorem LFunction_ne_zero_region_strict (h : DirichletQuasiRH) {q₀ q : ℕ} [NeZero q]
    (hq₀ : 2 ≤ q₀) (hq : q₀ ≤ q) (χ : DirichletCharacter ℂ q) {R : ℝ}
    (hR : 8 / Real.log q₀ ≤ R) {s : ℂ} (hs : 1 - 1 / (R * logQT q s.im) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) : DirichletCharacter.LFunction χ s ≠ 0 :=
  h χ (re_gt_of_region_strict hq₀ hq hR hs) hpole

/-- **Zero-free region (closed form)** from `DirichletQuasiRH`: for `q ≥ q₀ ≥ 2`, `R > 8/log q₀`,
every Dirichlet character `χ` mod `q`, `L(s,χ) ≠ 0` when `Re s ≥ 1 − 1/(R log(q·max(1,|Im s|)))`,
except at the pole `χ = 1`, `s = 1`. -/
theorem LFunction_ne_zero_region (h : DirichletQuasiRH) {q₀ q : ℕ} [NeZero q]
    (hq₀ : 2 ≤ q₀) (hq : q₀ ≤ q) (χ : DirichletCharacter ℂ q) {R : ℝ}
    (hR : 8 / Real.log q₀ < R) {s : ℂ} (hs : 1 - 1 / (R * logQT q s.im) ≤ s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) : DirichletCharacter.LFunction χ s ≠ 0 :=
  h χ (re_gt_of_region hq₀ hq hR hs) hpole

/-! ## Numerics -/

lemma log_three_lt : Real.log 3 < 1.25 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h := Real.sum_le_exp_of_nonneg (x := 1.25) (by norm_num) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

lemma log_four_lt : Real.log 4 < 1.3863 := by
  have e : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [e]
  linarith [Real.log_two_lt_d9]

lemma log_five_gt : 1.5862 < Real.log 5 := by
  have e : Real.log 5 = 2 * Real.log 2 + Real.log (5 / 4) := by
    rw [show (5 : ℝ) = 2 ^ 2 * (5 / 4) by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  have h1 := Real.one_sub_inv_le_log_of_pos (x := 5 / 4) (by norm_num)
  rw [e]
  norm_num at h1
  linarith [Real.log_two_gt_d9]

/-- `8/log 3 > 6.4` (numerically `8/log 3 = 7.2819…`): at `q₀ = 3` the constant is worse than `5.60`. -/
theorem six_four_lt_eight_div_log_three : (6.4 : ℝ) < 8 / Real.log 3 := by
  have h0 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [lt_div_iff₀ h0]
  nlinarith [log_three_lt]

/-- `8/log 4 > 5.6` (numerically `5.7707…`): at `q₀ = 4` the constant is still worse than `5.60`. -/
theorem five_six_lt_eight_div_log_four : (5.6 : ℝ) < 8 / Real.log 4 := by
  have h0 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  rw [lt_div_iff₀ h0]
  nlinarith [log_four_lt]

/-- `8/log 5 < 5.05` (numerically `8/log 5 = 4.9707…`): from `q₀ = 5` on, the constant beats `5.60`. -/
theorem eight_div_log_five_lt : 8 / Real.log 5 < (5.05 : ℝ) := by
  have h0 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  rw [div_lt_iff₀ h0]
  nlinarith [log_five_gt]

/-! ## The instances -/

/-- **All `q ≥ 3`, all `t`:** `L(s,χ) ≠ 0` for `Re s > 1 − 1/((8/log 3) · log(q·max(1,|Im s|)))`
(`8/log 3 = 7.2819…`), every `χ` mod `q`, except the pole `χ = 1`, `s = 1`. -/
theorem LFunction_ne_zero_q_ge_three (h : DirichletQuasiRH) {q : ℕ} [NeZero q] (hq : 3 ≤ q)
    (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 - 1 / (8 / Real.log 3 * logQT q s.im) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  LFunction_ne_zero_region_strict h (q₀ := 3) (by norm_num) hq χ (by norm_num) hs hpole

/-- **All `q ≥ 5`, all `t`:** `L(s,χ) ≠ 0` for `Re s > 1 − 1/((8/log 5) · log(q·max(1,|Im s|)))`
(`8/log 5 = 4.9707… < 5.05`), every `χ` mod `q`, except the pole `χ = 1`, `s = 1`. -/
theorem LFunction_ne_zero_q_ge_five (h : DirichletQuasiRH) {q : ℕ} [NeZero q] (hq : 5 ≤ q)
    (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 - 1 / (8 / Real.log 5 * logQT q s.im) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  LFunction_ne_zero_region_strict h (q₀ := 5) (by norm_num) hq χ (by norm_num) hs hpole

/-- **Kadiri's shape and constant, all `q ≥ 5`:** `L(s,χ) ≠ 0` for
`Re s ≥ 1 − 1/(5.60 · log(q·max(1,|Im s|)))`, every `χ` mod `q` (no primitivity, no upper bound on `q`,
no exceptional zero), except the pole `χ = 1`, `s = 1`. -/
theorem LFunction_ne_zero_kadiri_shape (h : DirichletQuasiRH) {q : ℕ} [NeZero q] (hq : 5 ≤ q)
    (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 - 1 / (5.60 * logQT q s.im) ≤ s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  LFunction_ne_zero_region h (q₀ := 5) (by norm_num) hq χ
    (by push_cast; linarith [eight_div_log_five_lt]) hs hpole

end FleetDirichletZeroFree
