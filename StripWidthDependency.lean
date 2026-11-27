import OffLineDetection

/-!
# Dependency map: the strip half-width `δ` as a parameter

`OffLineDetection.abs_t_im_lt` states `|Im (t x)| < 1/2`.  The constant `1/2` is **not** an
internal choice: it is exactly what `ZetaStrip.mem_strip_of_isNontrivialZero` (`0 < Re ρ < 1`)
gives after the change of variable `Im (t x) = 1/2 - Re (canonical x)` (`OffLineDetection.t_im`).

This module isolates the dependence.  It parametrises the two places where the half-width is
consumed and records the direction of the dependence.  It asserts nothing about any particular
value of `δ`; `StripHalfWidth δ` for `δ < 1/2` is an **input**, stated here as a `Prop`, never
proved.

## Where the half-width is consumed

1. `OffLineDetection.far_exponent_le` — through `t_im_sq_lt : (Im t)² < 1/4`.  Generalised below
   as `far_exponent_le_delta`: the far-field decay exponent is `-(1 - δ²)/(4b) = -(1 - δ²) s`.
   At `δ = 1/2` this is the file's `-3/(16 b) = -(3/4) s`.
2. `GaussianTraceFormula.tendsto_hfun_sum` / `gaussian_formula_of_realizes` — through the
   hypothesis `him : ∀ i, |(t i).im| ≤ 1/2`, which is handed to
   `GaussianTest.gaussR_sup_uniform _ _ (1/2)` and `gaussR_weighted_uniform _ _ (1/2)`.  Those
   hold for **every** `c ≥ 0` (`GaussianTest.majorant`), with constant proportional to
   `exp (c²/(2b))`.

Both are monotone in `δ`: a smaller half-width gives a faster far-field decay and a smaller
dominating constant.  No step of the chain competes against `δ`, so no value of `δ` is a
threshold and tightening `1/2` buys nothing downstream.
-/

set_option autoImplicit false

noncomputable section

open Complex
open scoped Real

namespace StripWidthDependency

open Reduction ZeroSumLimit GaussianTest OffLineDetection

/-! ## The half-width as a predicate -/

/-- `StripHalfWidth δ`: every canonical zero ordinate is within `δ` of the real axis,
equivalently every nontrivial zero has `|Re ρ - 1/2| < δ`. -/
def StripHalfWidth (δ : ℝ) : Prop := ∀ x : Index, |(t x).im| < δ

/-- The proved case: `δ = 1/2`, i.e. the open critical strip. -/
theorem stripHalfWidth_half : StripHalfWidth (1 / 2) := abs_t_im_lt

/-- `StripHalfWidth δ` is literally a zero-free-region statement for `ζ`. -/
theorem stripHalfWidth_iff_re_bounds (δ : ℝ) :
    StripHalfWidth δ ↔
      ∀ x : Index, 1 / 2 - δ < (canonical x).re ∧ (canonical x).re < 1 / 2 + δ := by
  simp only [StripHalfWidth, t_im, abs_lt]
  constructor
  · intro h x
    obtain ⟨h1, h2⟩ := h x
    exact ⟨by linarith, by linarith⟩
  · intro h x
    obtain ⟨h1, h2⟩ := h x
    exact ⟨by linarith, by linarith⟩

/-- The only route to `StripHalfWidth δ`: a zero-free region for `ζ` of half-width `δ`. -/
theorem stripHalfWidth_of_zeroFree {δ : ℝ}
    (h : ∀ ρ : ℂ, IsNontrivialZero ρ → |1 / 2 - ρ.re| < δ) : StripHalfWidth δ := by
  intro x
  rw [t_im]
  exact h _ (multEnum_canonical.nontrivial x)

/-- Under the Gaussian trace hypothesis the conclusion is `δ = 0`: `ordinates_real` already
gives every `StripHalfWidth δ` with `δ > 0`.  So the detection chain cannot *produce* a
half-width strictly between `0` and `1/2`; it consumes one. -/
theorem stripHalfWidth_of_ordinates_real {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ x : Index, (ordinate (canonical x)).im = 0) : StripHalfWidth δ := by
  intro x
  have hx : (t x).im = 0 := h x
  rw [hx, abs_zero]
  exact hδ

/-! ## Consumption site 1: the far-field exponent -/

/-- The far-field decay rate in `s = 1/(4b)` as a function of the half-width. -/
def farDecayRate (δ : ℝ) : ℝ := 1 - δ ^ 2

theorem farDecayRate_half : farDecayRate (1 / 2) = 3 / 4 := by
  norm_num [farDecayRate]

theorem farDecayRate_five_twelfths : farDecayRate (5 / 12) = 119 / 144 := by
  norm_num [farDecayRate]

/-- The decay rate is antitone in the half-width: a narrower strip decays faster. -/
theorem farDecayRate_antitone {δ δ' : ℝ} (h0 : 0 ≤ δ) (h : δ ≤ δ') :
    farDecayRate δ' ≤ farDecayRate δ := by
  simp only [farDecayRate]
  nlinarith

/-- `OffLineDetection.far_exponent_le` with the half-width free.  At `δ = 1/2` the right-hand
side is `-3/(16 b) + 1/4 - (Re z - α)²/4`, verbatim the original. -/
lemma far_exponent_le_delta {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) {δ α : ℝ} {z : ℂ}
    (him : z.im ^ 2 < δ ^ 2) (hre : 1 ≤ |z.re - α|) :
    (z.im ^ 2 - (z.re - α) ^ 2) / (4 * b)
      ≤ -(1 - δ ^ 2) / (4 * b) + 1 / 4 - (z.re - α) ^ 2 / 4 := by
  have hX : 1 ≤ (z.re - α) ^ 2 := by
    rw [← _root_.sq_abs]
    nlinarith [abs_nonneg (z.re - α)]
  have heq : -(1 - δ ^ 2) / (4 * b) + 1 / 4 - (z.re - α) ^ 2 / 4
      = (-(1 - δ ^ 2) + b - b * (z.re - α) ^ 2) / (4 * b) := by
    field_simp
  rw [heq, div_le_div_iff_of_pos_right (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 hX) (sub_nonneg.2 hb1)]

/-- `OffLineDetection.norm_gaussHat_far` with the half-width free. -/
lemma norm_gaussHat_far_delta {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) {δ α : ℝ} {x : Index}
    (hδ : (t x).im ^ 2 < δ ^ 2) (hx : x ∉ Z α) :
    ‖gaussHat b α (t x)‖
      ≤ Real.sqrt (π / b) * Real.exp (-(1 - δ ^ 2) / (4 * b)) * (Real.exp (1 / 4) * w α x) := by
  have hre : 1 ≤ |(t x).re - α| := by
    simp only [Z, Set.mem_setOf_eq, not_lt] at hx
    exact hx
  rw [norm_gaussHat hb]
  have h := far_exponent_le_delta hb hb1 hδ hre
  calc Real.sqrt (π / b) * Real.exp (((t x).im ^ 2 - ((t x).re - α) ^ 2) / (4 * b))
      ≤ Real.sqrt (π / b)
          * Real.exp (-(1 - δ ^ 2) / (4 * b) + 1 / 4 - ((t x).re - α) ^ 2 / 4) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h) (Real.sqrt_nonneg _)
    _ = Real.sqrt (π / b) * Real.exp (-(1 - δ ^ 2) / (4 * b))
          * (Real.exp (1 / 4) * w α x) := by
        unfold w
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, neg_div]
        ring_nf

/-- Sanity: at `δ = 1/2` the generalised far bound is the one already in the repo. -/
theorem far_bound_delta_half {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) {α : ℝ} {x : Index}
    (hx : x ∉ Z α) :
    ‖gaussHat b α (t x)‖
      ≤ Real.sqrt (π / b) * Real.exp (-(3 / 4) / (4 * b)) * (Real.exp (1 / 4) * w α x) := by
  have hδ : (t x).im ^ 2 < (1 / 2 : ℝ) ^ 2 := by
    have := t_im_sq_lt x
    nlinarith
  have h := norm_gaussHat_far_delta hb hb1 hδ hx
  norm_num at h ⊢
  convert h using 4

end StripWidthDependency

end
