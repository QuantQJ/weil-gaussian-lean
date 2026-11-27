import FleetSmoothWindowBasic
import FleetHeadContourShift

/-!
# Contour tools for the smooth window

Generic vertical-line identities for a function `f` holomorphic on a closed vertical strip (or half-strip),
with integrable vertical lines and vanishing horizontal sides.

* `line_shift_zero`: `∫ f(a₁+iy) dy = ∫ f(a₂+iy) dy` when `f` is holomorphic on `a₁ ≤ Re ≤ a₂`.
* `line_shift_one`: for `f = Φ·(−ζ')`, `Φ` entire, `a₁ < 1 < a₂`:
  `∫ f(a₂+iy) dy − ∫ f(a₁+iy) dy = 2π Φ'(1)` (generalizes `FleetHeadContour.line_shift`).
* `half_strip_upper`, `half_strip_lower`: the two half-strips `a₁ ≤ Re ≤ a₂`, `±Im ≥ τ`.
* `tendsto_horiz_of_bound`: horizontal sides vanish under a pointwise bound tending to `0`.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set MeasureTheory intervalIntegral
open scoped Real

namespace FleetSmoothWindow

lemma rect_re_im (a T : ℝ) : (((a : ℂ) + (T : ℂ) * I)).re = a ∧ (((a : ℂ) + (T : ℂ) * I)).im = T := by
  constructor <;> simp

/-- Cauchy on the rectangle `[a₁,a₂] × [y₁,y₂]` in the form used below. -/
lemma rect_zero {f : ℂ → ℂ} {a₁ a₂ y₁ y₂ : ℝ} (ha : a₁ ≤ a₂) (hy : y₁ ≤ y₂)
    (hf : ∀ z : ℂ, a₁ ≤ z.re → z.re ≤ a₂ → y₁ ≤ z.im → z.im ≤ y₂ → DifferentiableAt ℂ f z) :
    (∫ x in a₁..a₂, f ((x : ℂ) + y₁ * I)) - (∫ x in a₁..a₂, f ((x : ℂ) + y₂ * I))
      + I * (∫ y in y₁..y₂, f ((a₂ : ℂ) + y * I)) - I * (∫ y in y₁..y₂, f ((a₁ : ℂ) + y * I)) = 0 := by
  have H := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((a₁ : ℂ) + (y₁ : ℂ) * I) ((a₂ : ℂ) + (y₂ : ℂ) * I) ?_
  · obtain ⟨h1, h2⟩ := rect_re_im a₁ y₁
    obtain ⟨h3, h4⟩ := rect_re_im a₂ y₂
    rw [h1, h2, h3, h4] at H
    simpa [smul_eq_mul] using H
  · intro z hz
    obtain ⟨h1, h2⟩ := rect_re_im a₁ y₁
    obtain ⟨h3, h4⟩ := rect_re_im a₂ y₂
    rw [h1, h2, h3, h4, mem_reProdIm, uIcc_of_le ha, uIcc_of_le hy] at hz
    exact (hf z hz.1.1 hz.1.2 hz.2.1 hz.2.2).differentiableWithinAt

/-- **Line shift without a pole.** -/
theorem line_shift_zero {f : ℂ → ℂ} {a₁ a₂ : ℝ} (ha : a₁ ≤ a₂)
    (hf : ∀ z : ℂ, a₁ ≤ z.re → z.re ≤ a₂ → DifferentiableAt ℂ f z)
    (h1 : Integrable (fun y : ℝ => f ((a₁ : ℂ) + y * I)))
    (h2 : Integrable (fun y : ℝ => f ((a₂ : ℂ) + y * I)))
    (htop : Tendsto (fun T : ℝ => ∫ x in a₁..a₂, f ((x : ℂ) + T * I)) atTop (𝓝 0))
    (hbot : Tendsto (fun T : ℝ => ∫ x in a₁..a₂, f ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) atTop (𝓝 0)) :
    ∫ y : ℝ, f ((a₁ : ℂ) + y * I) = ∫ y : ℝ, f ((a₂ : ℂ) + y * I) := by
  have hV1 := intervalIntegral_tendsto_integral h1 tendsto_neg_atTop_atBot tendsto_id
  have hV2 := intervalIntegral_tendsto_integral h2 tendsto_neg_atTop_atBot tendsto_id
  have hlim : Tendsto (fun T : ℝ => (∫ x in a₁..a₂, f ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
      - (∫ x in a₁..a₂, f ((x : ℂ) + T * I))
      + I * (∫ y in (-T)..T, f ((a₂ : ℂ) + y * I)) - I * (∫ y in (-T)..T, f ((a₁ : ℂ) + y * I))) atTop
      (𝓝 (0 - 0 + I * (∫ y : ℝ, f ((a₂ : ℂ) + y * I)) - I * (∫ y : ℝ, f ((a₁ : ℂ) + y * I)))) :=
    ((hbot.sub htop).add (hV2.const_mul I)).sub (hV1.const_mul I)
  have hconst : ∀ᶠ T : ℝ in atTop, (∫ x in a₁..a₂, f ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
      - (∫ x in a₁..a₂, f ((x : ℂ) + T * I))
      + I * (∫ y in (-T)..T, f ((a₂ : ℂ) + y * I)) - I * (∫ y in (-T)..T, f ((a₁ : ℂ) + y * I)) = 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact rect_zero ha (by linarith) (fun z h1 h2 _ _ => hf z h1 h2)
  have heq := tendsto_nhds_unique (hlim.congr' hconst) tendsto_const_nhds
  have hI : I ≠ 0 := I_ne_zero
  have : I * ((∫ y : ℝ, f ((a₂ : ℂ) + y * I)) - (∫ y : ℝ, f ((a₁ : ℂ) + y * I))) = I * 0 := by
    rw [mul_sub]; linear_combination heq
  have := mul_left_cancel₀ hI this
  linear_combination -this

/-- **Line shift across the pole of `ζ'` at `1`.** -/
theorem line_shift_one {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) {a₁ a₂ : ℝ} (ha₁ : a₁ < 1) (ha₂ : 1 < a₂)
    (h1 : Integrable (fun y : ℝ => Φ ((a₁ : ℂ) + y * I) * (-deriv riemannZeta ((a₁ : ℂ) + y * I))))
    (h2 : Integrable (fun y : ℝ => Φ ((a₂ : ℂ) + y * I) * (-deriv riemannZeta ((a₂ : ℂ) + y * I))))
    (htop : Tendsto (fun T : ℝ => ∫ x in a₁..a₂,
      Φ ((x : ℂ) + T * I) * (-deriv riemannZeta ((x : ℂ) + T * I))) atTop (𝓝 0))
    (hbot : Tendsto (fun T : ℝ => ∫ x in a₁..a₂,
      Φ ((x : ℂ) + ((-T : ℝ) : ℂ) * I) * (-deriv riemannZeta ((x : ℂ) + ((-T : ℝ) : ℂ) * I))) atTop (𝓝 0)) :
    (∫ y : ℝ, Φ ((a₂ : ℂ) + y * I) * (-deriv riemannZeta ((a₂ : ℂ) + y * I)))
      - (∫ y : ℝ, Φ ((a₁ : ℂ) + y * I) * (-deriv riemannZeta ((a₁ : ℂ) + y * I)))
      = 2 * π * deriv Φ 1 := by
  set f : ℂ → ℂ := fun s => Φ s * (-deriv riemannZeta s) with hf
  have hV2 := intervalIntegral_tendsto_integral h2 tendsto_neg_atTop_atBot tendsto_id
  have hV1 := intervalIntegral_tendsto_integral h1 tendsto_neg_atTop_atBot tendsto_id
  have hlim : Tendsto (fun T : ℝ => RectangleWinding.rectInt f a₁ a₂ (-T) T) atTop
      (𝓝 (0 - 0 + I * (∫ y : ℝ, f ((a₂ : ℂ) + y * I)) - I * (∫ y : ℝ, f ((a₁ : ℂ) + y * I)))) := by
    unfold RectangleWinding.rectInt
    exact ((hbot.sub htop).add (hV2.const_mul I)).sub (hV1.const_mul I)
  have hconst : ∀ᶠ T : ℝ in atTop, RectangleWinding.rectInt f a₁ a₂ (-T) T = 2 * π * I * deriv Φ 1 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact FleetHeadContour.rect_shift hΦ ha₁ ha₂ (by linarith) hT
  have heq := tendsto_nhds_unique (hlim.congr' hconst) tendsto_const_nhds
  have hI : I ≠ 0 := I_ne_zero
  have : I * ((∫ y : ℝ, f ((a₂ : ℂ) + y * I)) - (∫ y : ℝ, f ((a₁ : ℂ) + y * I)))
      = I * (2 * π * deriv Φ 1) := by
    rw [mul_sub]; linear_combination heq
  exact mul_left_cancel₀ hI this

/-- **Upper half-strip.** `∫_{y>τ} f(a₂+iy) = ∫_{y>τ} f(a₁+iy) + i ∫_{a₁}^{a₂} f(x+iτ) dx`. -/
theorem half_strip_upper {f : ℂ → ℂ} {a₁ a₂ τ : ℝ} (ha : a₁ ≤ a₂)
    (hf : ∀ z : ℂ, a₁ ≤ z.re → z.re ≤ a₂ → τ ≤ z.im → DifferentiableAt ℂ f z)
    (h1 : IntegrableOn (fun y : ℝ => f ((a₁ : ℂ) + y * I)) (Ioi τ))
    (h2 : IntegrableOn (fun y : ℝ => f ((a₂ : ℂ) + y * I)) (Ioi τ))
    (htop : Tendsto (fun T : ℝ => ∫ x in a₁..a₂, f ((x : ℂ) + T * I)) atTop (𝓝 0)) :
    ∫ y in Ioi τ, f ((a₂ : ℂ) + y * I)
      = (∫ y in Ioi τ, f ((a₁ : ℂ) + y * I)) + I * ∫ x in a₁..a₂, f ((x : ℂ) + τ * I) := by
  have hV1 := intervalIntegral_tendsto_integral_Ioi τ h1 tendsto_id
  have hV2 := intervalIntegral_tendsto_integral_Ioi τ h2 tendsto_id
  have hlim : Tendsto (fun T : ℝ => (∫ x in a₁..a₂, f ((x : ℂ) + τ * I))
      - (∫ x in a₁..a₂, f ((x : ℂ) + T * I))
      + I * (∫ y in τ..T, f ((a₂ : ℂ) + y * I)) - I * (∫ y in τ..T, f ((a₁ : ℂ) + y * I))) atTop
      (𝓝 ((∫ x in a₁..a₂, f ((x : ℂ) + τ * I)) - 0 + I * (∫ y in Ioi τ, f ((a₂ : ℂ) + y * I))
        - I * (∫ y in Ioi τ, f ((a₁ : ℂ) + y * I)))) :=
    (((tendsto_const_nhds).sub htop).add (hV2.const_mul I)).sub (hV1.const_mul I)
  have hconst : ∀ᶠ T : ℝ in atTop, (∫ x in a₁..a₂, f ((x : ℂ) + τ * I))
      - (∫ x in a₁..a₂, f ((x : ℂ) + T * I))
      + I * (∫ y in τ..T, f ((a₂ : ℂ) + y * I)) - I * (∫ y in τ..T, f ((a₁ : ℂ) + y * I)) = 0 := by
    filter_upwards [eventually_ge_atTop τ] with T hT
    exact rect_zero ha hT (fun z h1 h2 h3 _ => hf z h1 h2 h3)
  have heq := tendsto_nhds_unique (hlim.congr' hconst) tendsto_const_nhds
  have hI2 : I * I = -1 := I_mul_I
  linear_combination (-I) * heq + ((∫ y in Ioi τ, f ((a₂ : ℂ) + y * I))
    - ∫ y in Ioi τ, f ((a₁ : ℂ) + y * I)) * hI2

/-- **Lower half-strip.** `∫_{y<−τ} f(a₂+iy) = ∫_{y<−τ} f(a₁+iy) − i ∫_{a₁}^{a₂} f(x−iτ) dx`. -/
theorem half_strip_lower {f : ℂ → ℂ} {a₁ a₂ τ : ℝ} (ha : a₁ ≤ a₂)
    (hf : ∀ z : ℂ, a₁ ≤ z.re → z.re ≤ a₂ → z.im ≤ -τ → DifferentiableAt ℂ f z)
    (h1 : IntegrableOn (fun y : ℝ => f ((a₁ : ℂ) + y * I)) (Iic (-τ)))
    (h2 : IntegrableOn (fun y : ℝ => f ((a₂ : ℂ) + y * I)) (Iic (-τ)))
    (hbot : Tendsto (fun T : ℝ => ∫ x in a₁..a₂, f ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) atTop (𝓝 0)) :
    ∫ y in Iic (-τ), f ((a₂ : ℂ) + y * I)
      = (∫ y in Iic (-τ), f ((a₁ : ℂ) + y * I)) - I * ∫ x in a₁..a₂, f ((x : ℂ) + ((-τ : ℝ) : ℂ) * I) := by
  have hV1 := intervalIntegral_tendsto_integral_Iic (-τ) h1 tendsto_neg_atTop_atBot
  have hV2 := intervalIntegral_tendsto_integral_Iic (-τ) h2 tendsto_neg_atTop_atBot
  have hlim : Tendsto (fun T : ℝ => (∫ x in a₁..a₂, f ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
      - (∫ x in a₁..a₂, f ((x : ℂ) + ((-τ : ℝ) : ℂ) * I))
      + I * (∫ y in (-T)..(-τ), f ((a₂ : ℂ) + y * I)) - I * (∫ y in (-T)..(-τ), f ((a₁ : ℂ) + y * I))) atTop
      (𝓝 (0 - (∫ x in a₁..a₂, f ((x : ℂ) + ((-τ : ℝ) : ℂ) * I))
        + I * (∫ y in Iic (-τ), f ((a₂ : ℂ) + y * I))
        - I * (∫ y in Iic (-τ), f ((a₁ : ℂ) + y * I)))) :=
    ((hbot.sub tendsto_const_nhds).add (hV2.const_mul I)).sub (hV1.const_mul I)
  have hconst : ∀ᶠ T : ℝ in atTop, (∫ x in a₁..a₂, f ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
      - (∫ x in a₁..a₂, f ((x : ℂ) + ((-τ : ℝ) : ℂ) * I))
      + I * (∫ y in (-T)..(-τ), f ((a₂ : ℂ) + y * I)) - I * (∫ y in (-T)..(-τ), f ((a₁ : ℂ) + y * I)) = 0 := by
    filter_upwards [eventually_ge_atTop τ] with T hT
    exact rect_zero ha (by linarith) (fun z h1 h2 _ h4 => hf z h1 h2 h4)
  have heq := tendsto_nhds_unique (hlim.congr' hconst) tendsto_const_nhds
  have hI2 : I * I = -1 := I_mul_I
  linear_combination (-I) * heq + ((∫ y in Iic (-τ), f ((a₂ : ℂ) + y * I))
    - ∫ y in Iic (-τ), f ((a₁ : ℂ) + y * I)) * hI2

/-- **Horizontal sides vanish** under a pointwise bound tending to `0`. -/
theorem tendsto_horiz_of_bound {f : ℂ → ℂ} {a₁ a₂ : ℝ} {B : ℝ → ℝ} (hB : Tendsto B atTop (𝓝 0))
    {σ : ℝ} (hb : ∀ T : ℝ, 1 ≤ T → ∀ x ∈ uIcc a₁ a₂, ‖f ((x : ℂ) + ((σ * T : ℝ) : ℂ) * I)‖ ≤ B T) :
    Tendsto (fun T : ℝ => ∫ x in a₁..a₂, f ((x : ℂ) + ((σ * T : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hmaj : Tendsto (fun T => B T * |a₂ - a₁|) atTop (𝓝 0) := by simpa using hB.mul_const |a₂ - a₁|
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hmaj
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  exact intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => hb T hT x (uIoc_subset_uIcc hx)

/-- Integrability from a one-Gaussian linear majorant. -/
theorem integrable_of_gauss1 {b : ℝ} (hb : 0 < b) {g : ℝ → ℂ} (hg : Continuous g) {β P Q : ℝ}
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (h : ∀ y : ℝ, ‖g y‖ ≤ (P + Q * |y|) * Real.exp (-(y - β) ^ 2 / (4 * b))) :
    Integrable g := by
  refine FleetHeadContour.integrable_of_gauss_bound hb β P Q hg fun y => (h y).trans ?_
  have : 0 ≤ P + Q * |y| := by positivity
  have h0 := Real.exp_pos (-(y + β) ^ 2 / (4 * b))
  nlinarith

end FleetSmoothWindow
