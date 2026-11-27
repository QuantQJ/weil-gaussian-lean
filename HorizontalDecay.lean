import Mathlib

/-!
# Horizontal decay: the estimate that closes a rectangular contour

Let `F : ℂ → ℂ` (think `F = ζ'/ζ · G`, `G` a rapidly decaying test-function
transform). This module proves that the horizontal integral
`∫ σ in a..b, F (σ + T·i)` tends to `0` as `T → +∞` (and as `T → −∞`) as
soon as `‖F(σ + T·i)‖` is bounded on the segment `a ≤ σ ≤ b` by a function
of `T` alone that tends to `0`.

**Proven unconditionally** (the growth bound is always an explicit hypothesis):

* `horizontal_integral_norm_le` — `‖∫ σ in a..b, F (σ + T i)‖ ≤ bound T * |b − a|`.
* `horizontal_integral_tendsto_zero_filter` — the general filter form, with an
  *eventual* bound (`∀ᶠ T in l, …`); `atTop` and `atBot` are instances.
* `horizontal_integral_tendsto_zero` — the `T → +∞` statement with the
  signature requested by the contour argument (the `IntervalIntegrable`
  hypothesis is accepted for interface fidelity but is not needed by the proof:
  the norm bound holds for the Bochner integral regardless of integrability).
* `horizontal_integral_tendsto_zero_atBot` — the symmetric `T → −∞` statement.
* `log_sq_mul_exp_neg_tendsto_zero` — `K · (log T)² · exp(−T) → 0`.
* `horizontal_integral_tendsto_zero_of_log_sq_exp` / `…_atBot` — the corollary
  under the concrete bound `‖F(σ + T i)‖ ≤ K (log T)² exp(−T)` for `T ≥ 2`
  (resp. `K (log(−T))² exp T` for `T ≤ −2`).

**Hypothesis (the unproven input in every theorem):** the pointwise growth
bound on the horizontal segment. Nothing here proves any bound on `ζ'/ζ`.
-/

noncomputable section

open Filter Topology Complex Set intervalIntegral

namespace HorizontalDecay

/-- On the segment `Im s = T`, `a ≤ Re s ≤ b`, a pointwise bound `‖F‖ ≤ bound T`
gives `‖∫ σ in a..b, F (σ + T i)‖ ≤ bound T * |b − a|`. No integrability needed. -/
theorem horizontal_integral_norm_le {F : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b) (T : ℝ)
    (bound : ℝ → ℝ) (hbound : ∀ σ : ℝ, σ ∈ Icc a b → ‖F (σ + T * I)‖ ≤ bound T) :
    ‖∫ σ in a..b, F (σ + T * I)‖ ≤ bound T * |b - a| := by
  refine norm_integral_le_of_norm_le_const fun σ hσ => hbound σ ?_
  rw [uIoc_of_le hab] at hσ
  exact Ioc_subset_Icc_self hσ

/-- General filter form: if eventually along `l` the segment bound `bound T`
holds and `bound → 0` along `l`, the horizontal integral tends to `0` along `l`. -/
theorem horizontal_integral_tendsto_zero_filter {F : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (l : Filter ℝ) (bound : ℝ → ℝ)
    (hbound : ∀ᶠ T : ℝ in l, ∀ σ : ℝ, σ ∈ Icc a b → ‖F (σ + T * I)‖ ≤ bound T)
    (hlim : Tendsto bound l (𝓝 0)) :
    Tendsto (fun T : ℝ => ∫ σ in a..b, F (σ + T * I)) l (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun T => bound T * |b - a|) ?_ ?_
  · exact hbound.mono fun T hT => horizontal_integral_norm_le hab T bound hT
  · simpa using hlim.mul_const |b - a|

/-- The requested statement: as `T → +∞`, `∫ σ in a..b, F (σ + T i) → 0` given a
segment bound `bound T → 0`. The `IntervalIntegrable` hypothesis `hint` matches the
contour-argument interface; the proof does not use it. -/
theorem horizontal_integral_tendsto_zero {F : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (_hint : ∀ T, IntervalIntegrable (fun σ : ℝ => F (σ + T * I)) MeasureTheory.volume a b)
    (bound : ℝ → ℝ) (hbound : ∀ T : ℝ, ∀ σ : ℝ, σ ∈ Icc a b → ‖F (σ + T * I)‖ ≤ bound T)
    (hlim : Tendsto bound atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => ∫ σ in a..b, F (σ + T * I)) atTop (𝓝 0) :=
  horizontal_integral_tendsto_zero_filter hab atTop bound (Eventually.of_forall hbound) hlim

/-- Symmetric statement as `T → −∞`. -/
theorem horizontal_integral_tendsto_zero_atBot {F : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (_hint : ∀ T, IntervalIntegrable (fun σ : ℝ => F (σ + T * I)) MeasureTheory.volume a b)
    (bound : ℝ → ℝ) (hbound : ∀ T : ℝ, ∀ σ : ℝ, σ ∈ Icc a b → ‖F (σ + T * I)‖ ≤ bound T)
    (hlim : Tendsto bound atBot (𝓝 0)) :
    Tendsto (fun T : ℝ => ∫ σ in a..b, F (σ + T * I)) atBot (𝓝 0) :=
  horizontal_integral_tendsto_zero_filter hab atBot bound (Eventually.of_forall hbound) hlim

/-- For `T ≥ 1`, `(log T)² ≤ T²` (from `log T ≤ T − 1 ≤ T` and `0 ≤ log T`). -/
theorem log_sq_le_sq {T : ℝ} (hT : 1 ≤ T) : (Real.log T) ^ 2 ≤ T ^ 2 := by
  have h0 : 0 ≤ Real.log T := Real.log_nonneg hT
  have h1 : Real.log T ≤ T := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  exact pow_le_pow_left₀ h0 h1 2

/-- `K · (log T)² · exp(−T) → 0` as `T → +∞`, for any real `K`. -/
theorem log_sq_mul_exp_neg_tendsto_zero (K : ℝ) :
    Tendsto (fun T : ℝ => K * (Real.log T) ^ 2 * Real.exp (-T)) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun T => |K| * (T ^ 2 * Real.exp (-T))) ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    rw [Real.norm_eq_abs, abs_mul, abs_mul, _root_.abs_pow, Real.abs_exp, mul_assoc]
    have hsq : |Real.log T| ^ 2 ≤ T ^ 2 := by rw [_root_.sq_abs]; exact log_sq_le_sq hT
    have hexp : 0 ≤ Real.exp (-T) := (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq hexp) (abs_nonneg K)
  · simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).const_mul |K|

/-- `K · (log(−T))² · exp T → 0` as `T → −∞` (the mirror of the previous theorem). -/
theorem log_sq_mul_exp_tendsto_zero_atBot (K : ℝ) :
    Tendsto (fun T : ℝ => K * (Real.log (-T)) ^ 2 * Real.exp T) atBot (𝓝 0) := by
  have h := (log_sq_mul_exp_neg_tendsto_zero K).comp tendsto_neg_atBot_atTop
  refine h.congr fun T => ?_
  simp [Function.comp]

/-- Corollary with the concrete growth bound: if for `T ≥ 2` and `a ≤ σ ≤ b`,
`‖F(σ + T i)‖ ≤ K (log T)² exp(−T)`, then the horizontal integral tends to `0` as
`T → +∞`. The bound is the unproven hypothesis. -/
theorem horizontal_integral_tendsto_zero_of_log_sq_exp {F : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (K : ℝ)
    (hbound : ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, σ ∈ Icc a b →
      ‖F (σ + T * I)‖ ≤ K * (Real.log T) ^ 2 * Real.exp (-T)) :
    Tendsto (fun T : ℝ => ∫ σ in a..b, F (σ + T * I)) atTop (𝓝 0) :=
  horizontal_integral_tendsto_zero_filter hab atTop
    (fun T => K * (Real.log T) ^ 2 * Real.exp (-T))
    ((eventually_ge_atTop 2).mono fun T hT => hbound T hT)
    (log_sq_mul_exp_neg_tendsto_zero K)

/-- Mirror corollary: if for `T ≤ −2` and `a ≤ σ ≤ b`,
`‖F(σ + T i)‖ ≤ K (log(−T))² exp T`, the horizontal integral tends to `0` as `T → −∞`. -/
theorem horizontal_integral_tendsto_zero_of_log_sq_exp_atBot {F : ℂ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (K : ℝ)
    (hbound : ∀ T : ℝ, T ≤ -2 → ∀ σ : ℝ, σ ∈ Icc a b →
      ‖F (σ + T * I)‖ ≤ K * (Real.log (-T)) ^ 2 * Real.exp T) :
    Tendsto (fun T : ℝ => ∫ σ in a..b, F (σ + T * I)) atBot (𝓝 0) :=
  horizontal_integral_tendsto_zero_filter hab atBot
    (fun T => K * (Real.log (-T)) ^ 2 * Real.exp T)
    ((eventually_le_atBot (-2)).mono fun T hT => hbound T hT)
    (log_sq_mul_exp_tendsto_zero_atBot K)

end HorizontalDecay

end
