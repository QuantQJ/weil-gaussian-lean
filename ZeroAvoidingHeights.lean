import ZeroDensityUnconditional
import ZeroDensity
import FiniteZeros
import Reduction
import Mathlib

/-!
# Heights that avoid every zero ordinate, quantitatively

**Proven (unconditional, standard axioms only):**

* `δ T₀ := 1 / (8 · K(7) · log (T₀ + 1) + 8)` is positive and `≤ 1/8`, of order `1 / log T₀`.
* `exists_height_avoiding_zeros`: for every `T₀ ≥ 4` there is a height `T ∈ [T₀, T₀ + 1]`
  with `|Im ρ − T| ≥ δ T₀` for **every** nontrivial zero `ρ`.
* `exists_seq_heights`: a sequence `T k ∈ [4 + k, 5 + k]` of such heights (with
  `δ (4 + k)`-avoidance), and `heights_tendsto_atTop`: `T k → ∞`.

**Route.** Only the finitely many zeros with `|Im ρ − (T₀ + ½)| ≤ 1` can come within `δ ≤ 1/8`
of some `T ∈ [T₀, T₀ + 1]`; their number `N` is `≤ 2 K(7) log (T₀ + ½) ≤ 2 K(7) log (T₀ + 1)`
by `ZeroDensityUnconditional.ncard_zeros_near_height_le`. The union of the `N` open
intervals `(γ − δ, γ + δ)` has Lebesgue measure `≤ 2 N δ < 1 = vol [T₀, T₀ + 1]`, so the
interval is not covered (`measure_mono` + `measure_biUnion_finset_le`).

**Not proven / no hypotheses:** nothing in this file is hypothesis-dependent.
-/

noncomputable section

open Reduction Set MeasureTheory Filter

namespace ZeroAvoidingHeights

/-- The avoidance gap at base height `T₀`: `δ T₀ = 1 / (8 K(7) log (T₀ + 1) + 8)`. -/
def δ (T₀ : ℝ) : ℝ := 1 / (8 * ZeroDensity.K 7 * Real.log (T₀ + 1) + 8)

/-- `K(7) ≥ 0`. -/
theorem K7_nonneg : 0 ≤ ZeroDensity.K 7 := ZeroDensity.K_nonneg (by norm_num)

/-- The denominator of `δ` is at least `8` when `T₀ ≥ 0`. -/
theorem eight_le_denom {T₀ : ℝ} (hT₀ : 0 ≤ T₀) :
    8 ≤ 8 * ZeroDensity.K 7 * Real.log (T₀ + 1) + 8 := by
  have hlog : 0 ≤ Real.log (T₀ + 1) := Real.log_nonneg (by linarith)
  nlinarith [K7_nonneg]

/-- `δ T₀ > 0` for `T₀ ≥ 0`. -/
theorem δ_pos {T₀ : ℝ} (hT₀ : 0 ≤ T₀) : 0 < δ T₀ := by
  unfold δ
  have := eight_le_denom hT₀
  positivity

/-- `δ T₀ ≤ 1/8` for `T₀ ≥ 0`. -/
theorem δ_le_eighth {T₀ : ℝ} (hT₀ : 0 ≤ T₀) : δ T₀ ≤ 1 / 8 := by
  unfold δ
  have := eight_le_denom hT₀
  exact one_div_le_one_div_of_le (by norm_num) this

/-- The key numerical inequality: if `N ≤ 2 K(7) log (T₀ + 1)` then `N · (2 δ T₀) < 1`. -/
theorem card_mul_two_δ_lt_one {T₀ : ℝ} (hT₀ : 0 ≤ T₀) {N : ℝ}
    (hN : N ≤ 2 * ZeroDensity.K 7 * Real.log (T₀ + 1)) : N * (2 * δ T₀) < 1 := by
  unfold δ
  have h8 := eight_le_denom hT₀
  have hlog : 0 ≤ Real.log (T₀ + 1) := Real.log_nonneg (by linarith)
  have hpos : 0 < 8 * ZeroDensity.K 7 * Real.log (T₀ + 1) + 8 := by linarith
  rw [mul_one_div, mul_div_assoc', div_lt_one hpos]
  nlinarith [K7_nonneg]

/-- The count of nontrivial zeros with `|Im ρ − (T₀ + ½)| ≤ 1` is at most
`2 K(7) log (T₀ + 1)` for `T₀ ≥ 4`. -/
theorem ncard_window_le {T₀ : ℝ} (hT₀ : 4 ≤ T₀) :
    ({ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im - (T₀ + 1 / 2)| ≤ 1}.ncard : ℝ)
      ≤ 2 * ZeroDensity.K 7 * Real.log (T₀ + 1) := by
  have habs : |T₀ + 1 / 2| = T₀ + 1 / 2 := abs_of_pos (by linarith)
  have h := ZeroDensityUnconditional.ncard_zeros_near_height_le (T₀ + 1 / 2)
    (by rw [habs]; linarith)
  rw [habs] at h
  refine h.trans ?_
  have hlog : Real.log (T₀ + 1 / 2) ≤ Real.log (T₀ + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  nlinarith [K7_nonneg]

/-- **Zero-avoiding height.** For `T₀ ≥ 4` there is `T ∈ [T₀, T₀ + 1]` at distance at least
`δ T₀` from the ordinate of every nontrivial zero. -/
theorem exists_height_avoiding_zeros (T₀ : ℝ) (hT₀ : 4 ≤ T₀) :
    ∃ T ∈ Set.Icc T₀ (T₀ + 1), ∀ ρ, IsNontrivialZero ρ → δ T₀ ≤ |ρ.im - T| := by
  have hT₀' : (0 : ℝ) ≤ T₀ := by linarith
  have hδ := δ_pos hT₀'
  have hδ8 := δ_le_eighth hT₀'
  -- the finitely many relevant zeros
  set S : Set ℂ := {ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im - (T₀ + 1 / 2)| ≤ 1} with hS
  have hfin : S.Finite := ZeroDensity.finite_zeros_near_height (T₀ + 1 / 2)
  set F : Finset ℂ := hfin.toFinset with hF
  have hcard : (F.card : ℝ) ≤ 2 * ZeroDensity.K 7 * Real.log (T₀ + 1) := by
    have := ncard_window_le hT₀
    rwa [Set.ncard_eq_toFinset_card S hfin] at this
  -- the union of the avoidance intervals
  set U : Set ℝ := ⋃ ρ ∈ F, Set.Ioo (ρ.im - δ T₀) (ρ.im + δ T₀) with hU
  have hvolU : volume U ≤ ENNReal.ofReal ((F.card : ℝ) * (2 * δ T₀)) := by
    refine (measure_biUnion_finset_le F _).trans ?_
    have : ∀ ρ ∈ F, volume (Set.Ioo (ρ.im - δ T₀) (ρ.im + δ T₀)) = ENNReal.ofReal (2 * δ T₀) := by
      intro ρ _
      rw [Real.volume_Ioo]
      congr 1
      ring
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul,
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  by_contra hcon
  push_neg at hcon
  -- the interval is covered by `U`
  have hsub : Set.Icc T₀ (T₀ + 1) ⊆ U := by
    intro T hT
    obtain ⟨ρ, hρ, hlt⟩ := hcon T hT
    have hρF : ρ ∈ F := by
      rw [hF, Set.Finite.mem_toFinset, hS]
      refine ⟨hρ, ?_⟩
      have h1 := abs_sub_lt_iff.mp hlt
      rw [abs_le]
      constructor <;> linarith [hT.1, hT.2]
    rw [hU, Set.mem_iUnion₂]
    refine ⟨ρ, hρF, ?_⟩
    have h1 := abs_sub_lt_iff.mp hlt
    exact ⟨by linarith, by linarith⟩
  have hvol : volume (Set.Icc T₀ (T₀ + 1)) ≤ ENNReal.ofReal ((F.card : ℝ) * (2 * δ T₀)) :=
    (measure_mono hsub).trans hvolU
  rw [Real.volume_Icc, show T₀ + 1 - T₀ = (1 : ℝ) by ring, ENNReal.ofReal_one,
    ENNReal.one_le_ofReal] at hvol
  exact absurd hvol (not_le.mpr (card_mul_two_δ_lt_one hT₀' hcard))

/-- **A sequence of zero-avoiding heights.** `T k ∈ [4 + k, 5 + k]` and every nontrivial zero
has `|Im ρ − T k| ≥ δ (4 + k)`. -/
theorem exists_seq_heights :
    ∃ T : ℕ → ℝ, (∀ k : ℕ, 4 + (k : ℝ) ≤ T k ∧ T k ≤ 5 + (k : ℝ)) ∧
      ∀ (k : ℕ) (ρ : ℂ), IsNontrivialZero ρ → δ (4 + (k : ℝ)) ≤ |ρ.im - T k| := by
  have h : ∀ k : ℕ, ∃ T ∈ Set.Icc (4 + (k : ℝ)) (4 + (k : ℝ) + 1),
      ∀ ρ, IsNontrivialZero ρ → δ (4 + k) ≤ |ρ.im - T| :=
    fun k => exists_height_avoiding_zeros (4 + k) (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  choose T hT using h
  refine ⟨T, fun k => ⟨(hT k).1.1, ?_⟩, fun k ρ hρ => (hT k).2 ρ hρ⟩
  have := (hT k).1.2
  linarith

/-- Any sequence with `4 + k ≤ T k` tends to `+∞`; in particular the heights of
`exists_seq_heights` do. -/
theorem heights_tendsto_atTop (T : ℕ → ℝ) (hT : ∀ k : ℕ, 4 + (k : ℝ) ≤ T k) :
    Tendsto T atTop atTop :=
  tendsto_atTop_mono hT (tendsto_atTop_add_const_left atTop (4 : ℝ) tendsto_natCast_atTop_atTop)

end ZeroAvoidingHeights

end
