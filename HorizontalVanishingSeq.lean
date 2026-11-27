import TestFunctions
import HorizontalDecay
import ZeroAvoidingHeights
import SegmentBoundUnconditional
import ZetaConj
import Reduction
import Mathlib

/-!
# Horizontal integrals vanish along the zero-avoiding heights

The contour argument for the explicit formula shifts the line `Re s = c` to `Re s = 1 − c`
through a rectangle `[1−c, c] × [−T, T]`; its top and bottom edges carry the integrals
`∫ σ in −½..3/2, (ζ'/ζ)(σ ± iT) · Gt a g (σ ± iT)`. This module proves that they tend to `0`
along a **fixed** sequence of heights `heights k ∈ [4 + k, 5 + k]` that stay at distance
`δ(4 + k)` from every zero ordinate.

**Proven unconditionally (Mathlib's standard axioms only):**

* `heights` — the sequence of `ZeroAvoidingHeights.exists_seq_heights`, exported as a `def`
  (via `Classical.choose`) with its properties `heights_ge`, `heights_le`, `heights_avoid`,
  `heights_avoid_neg` (symmetric avoidance at `−heights k`, via `ZetaConj.isNontrivialZero_conj`),
  `heights_tendsto_atTop`, so downstream assembly can refer to one and the same sequence.
* `segment_bound_top` / `segment_bound_bot` — the unconditional segment bound of
  `SegmentBoundUnconditional` at `±heights k` for `k ≥ 2`, `σ ∈ [−½, 3/2]`.
* `segment_bound_log_sq_top` / `segment_bound_log_sq_bot` — the same bound packaged as
  `‖ζ'/ζ(σ ± i·heights k)‖ ≤ B · (log (heights k))²` with the explicit constant `B`, using
  `1/δ(4+k) = 8 K(7) log(5+k) + 8 ≤ (16 K(7) + 8) log (heights k)`.
* `horizontal_vanishing_filter` — filter form of `TestFunctions.horizontal_vanishing`: an
  *eventual* polylog bound along a filter `l` with `|T| → ∞` suffices.
* `horizontal_tendsto_zero_seq` / `horizontal_tendsto_zero_seq_neg` — the top and bottom
  horizontal integrals tend to `0` as `k → ∞`, for every test function `IsTestFn a g`.

**Hypothesis-dependent:** nothing. **Not proven:** nothing is left open in this file.
No `sorry`, no custom axioms.
-/

set_option autoImplicit false

noncomputable section

open Reduction Complex Filter Topology Set TestFunctions
open scoped ComplexConjugate

namespace HorizontalVanishingSeq

/-! ## The fixed sequence of zero-avoiding heights -/

/-- The fixed sequence of zero-avoiding heights: `heights k ∈ [4 + k, 5 + k]` and every
nontrivial zero has `|Im ρ − heights k| ≥ δ(4 + k)`. -/
def heights : ℕ → ℝ := Classical.choose ZeroAvoidingHeights.exists_seq_heights

/-- The defining properties of `heights`. -/
theorem heights_spec :
    (∀ k : ℕ, 4 + (k : ℝ) ≤ heights k ∧ heights k ≤ 5 + (k : ℝ)) ∧
      ∀ (k : ℕ) (ρ : ℂ), IsNontrivialZero ρ →
        ZeroAvoidingHeights.δ (4 + (k : ℝ)) ≤ |ρ.im - heights k| :=
  Classical.choose_spec ZeroAvoidingHeights.exists_seq_heights

/-- `4 + k ≤ heights k`. -/
theorem heights_ge (k : ℕ) : 4 + (k : ℝ) ≤ heights k := (heights_spec.1 k).1

/-- `heights k ≤ 5 + k`. -/
theorem heights_le (k : ℕ) : heights k ≤ 5 + (k : ℝ) := (heights_spec.1 k).2

/-- Zero avoidance at `+heights k`. -/
theorem heights_avoid (k : ℕ) (ρ : ℂ) (hρ : IsNontrivialZero ρ) :
    ZeroAvoidingHeights.δ (4 + (k : ℝ)) ≤ |ρ.im - heights k| :=
  heights_spec.2 k ρ hρ

/-- Zero avoidance at `−heights k`: since `ρ ↦ conj ρ` maps nontrivial zeros to nontrivial
zeros and negates the ordinate, `|Im ρ − (−heights k)| = |Im (conj ρ) − heights k| ≥ δ`. -/
theorem heights_avoid_neg (k : ℕ) (ρ : ℂ) (hρ : IsNontrivialZero ρ) :
    ZeroAvoidingHeights.δ (4 + (k : ℝ)) ≤ |ρ.im - (-heights k)| := by
  have h := heights_avoid k (conj ρ) (ZetaConj.isNontrivialZero_conj hρ)
  rw [Complex.conj_im] at h
  have : |-ρ.im - heights k| = |ρ.im - (-heights k)| := by
    rw [← abs_neg]; congr 1; ring
  rwa [this] at h

/-- `heights k > 0`. -/
theorem heights_pos (k : ℕ) : 0 < heights k := by
  have := heights_ge k
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

/-- `heights k ≥ 6` for `k ≥ 2`. -/
theorem six_le_heights (k : ℕ) (hk : 2 ≤ k) : 6 ≤ heights k := by
  have h1 := heights_ge k
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

/-- `heights k → +∞`. -/
theorem heights_tendsto_atTop : Tendsto heights atTop atTop :=
  ZeroAvoidingHeights.heights_tendsto_atTop heights heights_ge

/-- `log (heights k) ≥ 1`, since `heights k ≥ 4 > e`. -/
theorem one_le_log_heights (k : ℕ) : 1 ≤ Real.log (heights k) := by
  rw [Real.le_log_iff_exp_le (heights_pos k)]
  have h1 := Real.exp_one_lt_d9
  have h2 := heights_ge k
  have h3 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  norm_num at h1
  linarith

/-- The avoidance gap `δ(4 + k)` is positive. -/
theorem δ_pos (k : ℕ) : 0 < ZeroAvoidingHeights.δ (4 + (k : ℝ)) :=
  ZeroAvoidingHeights.δ_pos (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])

/-! ## The segment bound at `±heights k` -/

/-- **Segment bound, top edge.** For `k ≥ 2` and `σ ∈ [−½, 3/2]`,
`‖ζ'/ζ(σ + i·heights k)‖ ≤ 623 Λ₀ log (heights k) + 2 Λ₀ log (heights k) / δ(4 + k)`. -/
theorem segment_bound_top (k : ℕ) (hk : 2 ≤ k) :
    ∀ σ ∈ Icc (-1/2 : ℝ) (3/2),
      ‖deriv riemannZeta (σ + heights k * I) / riemannZeta (σ + heights k * I)‖
        ≤ 623 * SegmentBoundUnconditional.Λ₀ * Real.log (heights k)
          + 2 * SegmentBoundUnconditional.Λ₀ * Real.log (heights k)
              / ZeroAvoidingHeights.δ (4 + (k : ℝ)) := by
  have habs : |heights k| = heights k := abs_of_pos (heights_pos k)
  have := SegmentBoundUnconditional.norm_logDeriv_zeta_le_on_full_segment (heights k)
    (by rw [habs]; exact six_le_heights k hk) _ (δ_pos k) (fun ρ hρ => heights_avoid k ρ hρ)
  rwa [habs] at this

/-- **Segment bound, bottom edge.** The same bound at height `−heights k`. -/
theorem segment_bound_bot (k : ℕ) (hk : 2 ≤ k) :
    ∀ σ ∈ Icc (-1/2 : ℝ) (3/2),
      ‖deriv riemannZeta (σ + ((-heights k : ℝ) : ℂ) * I)
          / riemannZeta (σ + ((-heights k : ℝ) : ℂ) * I)‖
        ≤ 623 * SegmentBoundUnconditional.Λ₀ * Real.log (heights k)
          + 2 * SegmentBoundUnconditional.Λ₀ * Real.log (heights k)
              / ZeroAvoidingHeights.δ (4 + (k : ℝ)) := by
  have habs : |-heights k| = heights k := by rw [abs_neg]; exact abs_of_pos (heights_pos k)
  have := SegmentBoundUnconditional.norm_logDeriv_zeta_le_on_full_segment (-heights k)
    (by rw [habs]; exact six_le_heights k hk) _ (δ_pos k) (fun ρ hρ => heights_avoid_neg k ρ hρ)
  rwa [habs] at this

/-! ## Packaging as a `log²` bound -/

/-- The constant of the `log²` bound: `B = 623 Λ₀ + 2 Λ₀ (16 K(7) + 8)`. -/
def B : ℝ :=
  623 * SegmentBoundUnconditional.Λ₀
    + 2 * SegmentBoundUnconditional.Λ₀ * (16 * ZeroDensity.K 7 + 8)

/-- `Λ₀ ≥ 0`. -/
theorem Λ₀_nonneg : 0 ≤ SegmentBoundUnconditional.Λ₀ := by
  unfold SegmentBoundUnconditional.Λ₀
  have h := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (4 : ℝ)
  have : 0 ≤ Real.log (3 + 12 * (2 : ℝ) ^ (4 : ℝ)) := Real.log_nonneg (by linarith)
  linarith

/-- `1 / δ(4 + k) = 8 K(7) log (5 + k) + 8 ≤ (16 K(7) + 8) · log (heights k)`, since
`5 + k ≤ (4 + k)² ≤ (heights k)²` and `log (heights k) ≥ 1`. -/
theorem one_div_δ_le (k : ℕ) :
    1 / ZeroAvoidingHeights.δ (4 + (k : ℝ))
      ≤ (16 * ZeroDensity.K 7 + 8) * Real.log (heights k) := by
  unfold ZeroAvoidingHeights.δ
  rw [one_div_one_div]
  have hK := ZeroAvoidingHeights.K7_nonneg
  have hL := one_le_log_heights k
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hlog : Real.log (4 + (k : ℝ) + 1) ≤ 2 * Real.log (heights k) := by
    have h1 : 4 + (k : ℝ) + 1 ≤ heights k ^ 2 := by
      have := heights_ge k
      nlinarith
    calc Real.log (4 + (k : ℝ) + 1) ≤ Real.log (heights k ^ 2) :=
          Real.log_le_log (by linarith) h1
      _ = 2 * Real.log (heights k) := by
          rw [Real.log_pow]; push_cast; ring
  nlinarith

/-- **`log²` bound, top edge.** For `k ≥ 2` and `σ ∈ [−½, 3/2]`,
`‖ζ'/ζ(σ + i·heights k)‖ ≤ B · (log (heights k))²`. -/
theorem segment_bound_log_sq_top (k : ℕ) (hk : 2 ≤ k) :
    ∀ σ ∈ Icc (-1/2 : ℝ) (3/2),
      ‖deriv riemannZeta (σ + heights k * I) / riemannZeta (σ + heights k * I)‖
        ≤ B * (Real.log (heights k)) ^ 2 := by
  intro σ hσ
  refine (segment_bound_top k hk σ hσ).trans ?_
  exact bound_le_B_log_sq k

where
  /-- The purely numerical step: the segment bound is at most `B · log²`. -/
  bound_le_B_log_sq (k : ℕ) :
      623 * SegmentBoundUnconditional.Λ₀ * Real.log (heights k)
          + 2 * SegmentBoundUnconditional.Λ₀ * Real.log (heights k)
              / ZeroAvoidingHeights.δ (4 + (k : ℝ))
        ≤ B * (Real.log (heights k)) ^ 2 := by
    set L := Real.log (heights k) with hLdef
    have hL := one_le_log_heights k
    have hΛ := Λ₀_nonneg
    have hK := ZeroAvoidingHeights.K7_nonneg
    have hinv := one_div_δ_le k
    have h2 : L / ZeroAvoidingHeights.δ (4 + (k : ℝ)) ≤ (16 * ZeroDensity.K 7 + 8) * L * L := by
      rw [div_eq_mul_one_div]
      calc L * (1 / ZeroAvoidingHeights.δ (4 + (k : ℝ)))
          ≤ L * ((16 * ZeroDensity.K 7 + 8) * L) :=
            mul_le_mul_of_nonneg_left hinv (by linarith)
        _ = (16 * ZeroDensity.K 7 + 8) * L * L := by ring
    have h3 : L ≤ L * L := by nlinarith
    have hc : 0 ≤ 2 * SegmentBoundUnconditional.Λ₀ := by linarith
    have hc' : 0 ≤ 623 * SegmentBoundUnconditional.Λ₀ := by linarith
    calc 623 * SegmentBoundUnconditional.Λ₀ * L
          + 2 * SegmentBoundUnconditional.Λ₀ * L / ZeroAvoidingHeights.δ (4 + (k : ℝ))
        = 623 * SegmentBoundUnconditional.Λ₀ * L
          + 2 * SegmentBoundUnconditional.Λ₀ * (L / ZeroAvoidingHeights.δ (4 + (k : ℝ))) := by
          rw [mul_div_assoc]
      _ ≤ 623 * SegmentBoundUnconditional.Λ₀ * (L * L)
          + 2 * SegmentBoundUnconditional.Λ₀ * ((16 * ZeroDensity.K 7 + 8) * L * L) :=
          add_le_add (mul_le_mul_of_nonneg_left h3 hc') (mul_le_mul_of_nonneg_left h2 hc)
      _ = B * L ^ 2 := by unfold B; ring

/-- **`log²` bound, bottom edge.** For `k ≥ 2` and `σ ∈ [−½, 3/2]`,
`‖ζ'/ζ(σ − i·heights k)‖ ≤ B · (log (heights k))²`. -/
theorem segment_bound_log_sq_bot (k : ℕ) (hk : 2 ≤ k) :
    ∀ σ ∈ Icc (-1/2 : ℝ) (3/2),
      ‖deriv riemannZeta (σ + ((-heights k : ℝ) : ℂ) * I)
          / riemannZeta (σ + ((-heights k : ℝ) : ℂ) * I)‖
        ≤ B * (Real.log (heights k)) ^ 2 := by
  intro σ hσ
  exact (segment_bound_bot k hk σ hσ).trans (segment_bound_log_sq_top.bound_le_B_log_sq k)

/-! ## Horizontal vanishing along a filter -/

/-- **Horizontal vanishing, filter form.** If `|T| → ∞` along `l` and eventually along `l`
`‖F (σ + iT)‖ ≤ B (log |T|)²` for `σ ∈ [σ₁, σ₂]`, then
`∫ σ in σ₁..σ₂, F (σ + iT) · Gt a g (σ + iT) → 0` along `l`
(via `‖Gt‖ ≤ C₂ e^{aM} / T²`, `M = max |σ₁ − ½| |σ₂ − ½|`). -/
theorem horizontal_vanishing_filter {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) {σ₁ σ₂ : ℝ}
    (hσ : σ₁ ≤ σ₂) (F : ℂ → ℂ) (B : ℝ) (l : Filter ℝ) (hl : Tendsto (fun T : ℝ => |T|) l atTop)
    (hF : ∀ᶠ T : ℝ in l, ∀ σ ∈ Icc σ₁ σ₂, ‖F (σ + T * I)‖ ≤ B * (Real.log |T|) ^ 2) :
    Tendsto (fun T : ℝ => ∫ σ in σ₁..σ₂, F (σ + T * I) * Gt a g (σ + T * I)) l (𝓝 0) := by
  set M : ℝ := max |σ₁ - 1 / 2| |σ₂ - 1 / 2| with hM
  set K : ℝ := C₂ a g * Real.exp (a * M) with hKdef
  refine HorizontalDecay.horizontal_integral_tendsto_zero_filter
    (F := fun z => F z * Gt a g z) hσ l
    (fun T => B * K * (Real.log |T| / |T|) ^ 2) ?_ ?_
  · filter_upwards [hF, hl.eventually_ge_atTop 1] with T hT hT1
    intro σ hσ'
    have hT0 : T ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hT1
      norm_num at hT1
    have hre : (σ + T * I).re = σ := by simp
    have him : (σ + T * I).im = T := by simp
    have h1 := hT σ hσ'
    have hσM : |σ - 1 / 2| ≤ M := by
      rcases hσ' with ⟨hl', hr⟩
      rcases le_or_gt (1 / 2) σ with hh | hh
      · calc |σ - 1 / 2| = σ - 1 / 2 := abs_of_nonneg (by linarith)
          _ ≤ σ₂ - 1 / 2 := by linarith
          _ ≤ |σ₂ - 1 / 2| := le_abs_self _
          _ ≤ M := le_max_right _ _
      · calc |σ - 1 / 2| = -(σ - 1 / 2) := abs_of_neg (by linarith)
          _ ≤ -(σ₁ - 1 / 2) := by linarith
          _ ≤ |σ₁ - 1 / 2| := neg_le_abs _
          _ ≤ M := le_max_left _ _
    have h2 : ‖Gt a g (σ + T * I)‖ ≤ K / |T| ^ 2 := by
      have := Gt_decay h (s := σ + T * I) (by rw [him]; exact hT0)
      rw [hre, him] at this
      rw [_root_.sq_abs]
      refine this.trans ?_
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (C₂_nonneg h)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hσM h.nonneg
    have hBn : 0 ≤ B * Real.log |T| ^ 2 := (norm_nonneg _).trans h1
    calc ‖F (σ + T * I) * Gt a g (σ + T * I)‖
        = ‖F (σ + T * I)‖ * ‖Gt a g (σ + T * I)‖ := norm_mul _ _
      _ ≤ (B * Real.log |T| ^ 2) * (K / |T| ^ 2) := mul_le_mul h1 h2 (norm_nonneg _) hBn
      _ = B * K * (Real.log |T| / |T|) ^ 2 := by rw [div_pow]; ring
  · have h0 : Tendsto (fun x : ℝ => B * K * (Real.log x ^ 1 / (1 * x + 0)) ^ 2) atTop
        (𝓝 (B * K * 0 ^ 2)) :=
      ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).pow 2).const_mul (B * K)
    simp only [pow_one, one_mul, add_zero, zero_pow two_ne_zero, mul_zero] at h0
    exact h0.comp hl

/-! ## The main theorems: the top and bottom edges vanish along `heights` -/

/-- **Top edge vanishes.** For every test function `g` on `[−a, a]`,
`∫ σ in −½..3/2, (ζ'/ζ)(σ + i·heights k) · Gt a g (σ + i·heights k) → 0` as `k → ∞`. -/
theorem horizontal_tendsto_zero_seq {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) :
    Tendsto (fun k : ℕ => ∫ σ in (-1/2 : ℝ)..(3/2),
      (deriv riemannZeta (σ + heights k * I) / riemannZeta (σ + heights k * I))
        * Gt a g (σ + heights k * I)) atTop (𝓝 0) := by
  have key := horizontal_vanishing_filter h (by norm_num : (-1/2 : ℝ) ≤ 3/2)
    (fun z => deriv riemannZeta z / riemannZeta z) B (map heights atTop) ?_ ?_
  · exact tendsto_map'_iff.mp key
  · rw [tendsto_map'_iff]
    exact tendsto_atTop_mono (fun k => le_abs_self (heights k)) heights_tendsto_atTop
  · rw [eventually_map]
    filter_upwards [eventually_ge_atTop 2] with k hk
    intro σ hσ
    rw [abs_of_pos (heights_pos k)]
    exact segment_bound_log_sq_top k hk σ hσ

/-- **Bottom edge vanishes.** For every test function `g` on `[−a, a]`,
`∫ σ in −½..3/2, (ζ'/ζ)(σ − i·heights k) · Gt a g (σ − i·heights k) → 0` as `k → ∞`,
by the conjugation symmetry of the zeros (`heights_avoid_neg`) and of `Gt_decay`. -/
theorem horizontal_tendsto_zero_seq_neg {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) :
    Tendsto (fun k : ℕ => ∫ σ in (-1/2 : ℝ)..(3/2),
      (deriv riemannZeta (σ + ((-heights k : ℝ) : ℂ) * I)
          / riemannZeta (σ + ((-heights k : ℝ) : ℂ) * I))
        * Gt a g (σ + ((-heights k : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
  have key := horizontal_vanishing_filter h (by norm_num : (-1/2 : ℝ) ≤ 3/2)
    (fun z => deriv riemannZeta z / riemannZeta z) B (map (fun k => -heights k) atTop) ?_ ?_
  · exact tendsto_map'_iff.mp key
  · rw [tendsto_map'_iff]
    refine tendsto_atTop_mono (fun k => ?_) heights_tendsto_atTop
    show heights k ≤ |-heights k|
    rw [abs_neg]
    exact le_abs_self _
  · rw [eventually_map]
    filter_upwards [eventually_ge_atTop 2] with k hk
    intro σ hσ
    show ‖_‖ ≤ B * (Real.log |-heights k|) ^ 2
    rw [abs_neg, abs_of_pos (heights_pos k)]
    exact segment_bound_log_sq_bot k hk σ hσ

end HorizontalVanishingSeq

end
