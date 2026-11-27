import Mathlib

/-!
# The rectangle winding-number lemma

Mathlib proves `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` (the
boundary integral of a holomorphic function over a rectangle vanishes) but has no
statement of the complementary fact: the boundary integral of `(z - p)⁻¹` over an
axis-parallel rectangle containing `p` in its interior equals `2πi`.

We define `rectInt f x₁ x₂ y₁ y₂` in the same four-term form Mathlib uses
(bottom edge − top edge + `I ·` right edge − `I ·` left edge, with `z = x₁ + y₁ I`,
`w = x₂ + y₂ I`), and prove

* `rect_winding` — `rectInt (fun z => (z - p)⁻¹) x₁ x₂ y₁ y₂ = 2 * π * I`
  whenever `x₁ < p.re < x₂` and `y₁ < p.im < y₂`.

Route: direct computation with the principal branch of `Complex.log`.
* `integral_horiz` — each horizontal edge at height `y ≠ p.im` stays off the branch
  cut of `log (· - p)`, so `∫ = log (x₂ + yI - p) - log (x₁ + yI - p)`.
* `integral_vert_right` — the right edge lies in `re (z - p) > 0`, same antiderivative.
* `integral_vert_left` — the left edge crosses the negative real axis of `z - p`,
  so we use `log (p - z)` instead (its argument has positive real part there).
* `log_sub_log_neg_of_im_pos` / `..._of_im_neg` — `log z - log (-z) = ± π I`
  according to the sign of `im z`; the four edge contributions collapse to
  `[log c₃ - log (-c₃)] - [log c₄ - log (-c₄)] = πI - (-πI) = 2πI`.

Every proof is complete (no placeholders) and no custom axioms are introduced; every
theorem depends only on `propext`, `Classical.choice`, `Quot.sound`.
-/

noncomputable section

open Complex
open scoped Real

namespace RectangleWinding

/-- The four-edge boundary integral of `f` over the rectangle
`[x₁, x₂] × [y₁, y₂]`, traversed counterclockwise, in the same four-term shape as
Mathlib's `Complex.integral_boundary_rect_*` lemmas (`z = x₁ + y₁ I`, `w = x₂ + y₂ I`). -/
def rectInt (f : ℂ → ℂ) (x₁ x₂ y₁ y₂ : ℝ) : ℂ :=
  (∫ x in x₁..x₂, f (x + y₁ * I)) - (∫ x in x₁..x₂, f (x + y₂ * I))
    + I * (∫ y in y₁..y₂, f (x₂ + y * I)) - I * (∫ y in y₁..y₂, f (x₁ + y * I))

/-! ## Points off the branch cut -/

/-- A point of a horizontal line at height `y ≠ p.im`, shifted by `-p`, lies in the
slit plane (its imaginary part `y - p.im` is nonzero). -/
theorem horiz_mem_slitPlane (p : ℂ) (x y : ℝ) (hy : y ≠ p.im) :
    ((x : ℂ) + y * I - p) ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  right
  have h : ((x : ℂ) + y * I - p).im = y - p.im := by simp
  rw [h]
  exact sub_ne_zero.mpr hy

/-- A point of a vertical line at abscissa `x > p.re`, shifted by `-p`, lies in the
slit plane (its real part `x - p.re` is positive). -/
theorem vertRight_mem_slitPlane (p : ℂ) (x y : ℝ) (hx : p.re < x) :
    ((x : ℂ) + y * I - p) ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  left
  have h : ((x : ℂ) + y * I - p).re = x - p.re := by simp
  rw [h]
  linarith

/-- For a point `z` of a vertical line at abscissa `x < p.re`, the reflected vector
`p - z` lies in the slit plane (its real part `p.re - x` is positive). -/
theorem vertLeft_mem_slitPlane (p : ℂ) (x y : ℝ) (hx : x < p.re) :
    (p - ((x : ℂ) + y * I)) ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  left
  have h : (p - ((x : ℂ) + y * I)).re = p.re - x := by simp
  rw [h]
  linarith

/-! ## Derivatives of the edge parametrisations -/

/-- `t ↦ (t : ℂ)` has derivative `1`. -/
theorem hasDerivAt_ofReal (t : ℝ) : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
  simpa using (hasDerivAt_id t).ofReal_comp

/-- The horizontal parametrisation `t ↦ t + yI - p` has derivative `1`. -/
theorem hasDerivAt_horiz (p : ℂ) (y t : ℝ) :
    HasDerivAt (fun s : ℝ => (s : ℂ) + y * I - p) 1 t :=
  ((hasDerivAt_ofReal t).add_const (y * I)).sub_const p

/-- The vertical parametrisation `t ↦ x + tI - p` has derivative `I`. -/
theorem hasDerivAt_vert (p : ℂ) (x t : ℝ) :
    HasDerivAt (fun s : ℝ => (x : ℂ) + s * I - p) I t := by
  have h := (((hasDerivAt_ofReal t).mul_const I).const_add (x : ℂ)).sub_const p
  simpa using h

/-- The reflected vertical parametrisation `t ↦ p - (x + tI)` has derivative `-I`. -/
theorem hasDerivAt_vertReflected (p : ℂ) (x t : ℝ) :
    HasDerivAt (fun s : ℝ => p - ((x : ℂ) + s * I)) (-I) t := by
  have h := (((hasDerivAt_ofReal t).mul_const I).const_add (x : ℂ)).const_sub p
  simpa using h

/-! ## The four edge integrals -/

/-- Horizontal edge at height `y ≠ p.im`:
`∫_{x₁}^{x₂} (x + yI - p)⁻¹ dx = log (x₂ + yI - p) - log (x₁ + yI - p)`. -/
theorem integral_horiz (p : ℂ) (x₁ x₂ y : ℝ) (hy : y ≠ p.im) :
    ∫ x in x₁..x₂, ((x : ℂ) + y * I - p)⁻¹
      = log ((x₂ : ℂ) + y * I - p) - log ((x₁ : ℂ) + y * I - p) := by
  have hderiv : ∀ x ∈ Set.uIcc x₁ x₂,
      HasDerivAt (fun t : ℝ => log ((t : ℂ) + y * I - p)) (((x : ℂ) + y * I - p)⁻¹) x := by
    intro x _
    have h := (hasDerivAt_horiz p y x).clog_real (horiz_mem_slitPlane p x y hy)
    simpa [one_div] using h
  have hint : IntervalIntegrable (fun x : ℝ => ((x : ℂ) + y * I - p)⁻¹)
      MeasureTheory.volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    apply Continuous.inv₀
    · fun_prop
    · intro x
      exact slitPlane_ne_zero (horiz_mem_slitPlane p x y hy)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- Right vertical edge at abscissa `x > p.re`:
`I ∫_{y₁}^{y₂} (x + yI - p)⁻¹ dy = log (x + y₂I - p) - log (x + y₁I - p)`. -/
theorem integral_vert_right (p : ℂ) (x y₁ y₂ : ℝ) (hx : p.re < x) :
    I * ∫ y in y₁..y₂, ((x : ℂ) + y * I - p)⁻¹
      = log ((x : ℂ) + y₂ * I - p) - log ((x : ℂ) + y₁ * I - p) := by
  have hderiv : ∀ y ∈ Set.uIcc y₁ y₂,
      HasDerivAt (fun t : ℝ => log ((x : ℂ) + t * I - p))
        (I * ((x : ℂ) + y * I - p)⁻¹) y := by
    intro y _
    have h := (hasDerivAt_vert p x y).clog_real (vertRight_mem_slitPlane p x y hx)
    simpa [div_eq_mul_inv] using h
  have hint : IntervalIntegrable (fun y : ℝ => I * ((x : ℂ) + y * I - p)⁻¹)
      MeasureTheory.volume y₁ y₂ := by
    apply Continuous.intervalIntegrable
    apply Continuous.mul continuous_const
    apply Continuous.inv₀
    · fun_prop
    · intro y
      exact slitPlane_ne_zero (vertRight_mem_slitPlane p x y hx)
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- Left vertical edge at abscissa `x < p.re`. This edge crosses the branch cut of
`log (· - p)`, so the antiderivative used is `log (p - ·)`:
`I ∫_{y₁}^{y₂} (x + yI - p)⁻¹ dy = log (p - (x + y₂I)) - log (p - (x + y₁I))`. -/
theorem integral_vert_left (p : ℂ) (x y₁ y₂ : ℝ) (hx : x < p.re) :
    I * ∫ y in y₁..y₂, ((x : ℂ) + y * I - p)⁻¹
      = log (p - ((x : ℂ) + y₂ * I)) - log (p - ((x : ℂ) + y₁ * I)) := by
  have hderiv : ∀ y ∈ Set.uIcc y₁ y₂,
      HasDerivAt (fun t : ℝ => log (p - ((x : ℂ) + t * I)))
        (I * ((x : ℂ) + y * I - p)⁻¹) y := by
    intro y _
    have h := (hasDerivAt_vertReflected p x y).clog_real (vertLeft_mem_slitPlane p x y hx)
    convert h using 1
    rw [div_eq_mul_inv, ← neg_sub p ((x : ℂ) + y * I), inv_neg]
    ring
  have hint : IntervalIntegrable (fun y : ℝ => I * ((x : ℂ) + y * I - p)⁻¹)
      MeasureTheory.volume y₁ y₂ := by
    apply Continuous.intervalIntegrable
    apply Continuous.mul continuous_const
    apply Continuous.inv₀
    · fun_prop
    · intro y
      have h := slitPlane_ne_zero (vertLeft_mem_slitPlane p x y hx)
      intro h0
      apply h
      rw [← neg_sub p ((x : ℂ) + y * I)] at h0
      exact neg_eq_zero.mp h0
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-! ## The branch-jump identities -/

/-- For `im z > 0`, `log z - log (-z) = π I` (the moduli agree; `arg (-z) = arg z - π`). -/
theorem log_sub_log_neg_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    log z - log (-z) = π * I := by
  apply Complex.ext
  · simp [log_re]
  · simp [log_im, arg_neg_eq_arg_sub_pi_of_im_pos hz]

/-- For `im z < 0`, `log z - log (-z) = -π I` (the moduli agree; `arg (-z) = arg z + π`). -/
theorem log_sub_log_neg_of_im_neg {z : ℂ} (hz : z.im < 0) :
    log z - log (-z) = -(π * I) := by
  apply Complex.ext
  · simp [log_re]
  · simp [log_im, arg_neg_eq_arg_add_pi_of_im_neg hz]

/-! ## The winding-number lemma -/

/-- **Rectangle winding number.** For `x₁ < p.re < x₂` and `y₁ < p.im < y₂`, the
counterclockwise boundary integral of `(z - p)⁻¹` over the rectangle
`[x₁, x₂] × [y₁, y₂]` equals `2πi`. -/
theorem rect_winding (p : ℂ) (x₁ x₂ y₁ y₂ : ℝ)
    (hx₁ : x₁ < p.re) (hx₂ : p.re < x₂) (hy₁ : y₁ < p.im) (hy₂ : p.im < y₂) :
    rectInt (fun z => (z - p)⁻¹) x₁ x₂ y₁ y₂ = 2 * π * I := by
  unfold rectInt
  simp only []
  rw [integral_horiz p x₁ x₂ y₁ hy₁.ne, integral_horiz p x₁ x₂ y₂ hy₂.ne',
    integral_vert_right p x₂ y₁ y₂ hx₂, integral_vert_left p x₁ y₁ y₂ hx₁]
  have e3 : p - ((x₁ : ℂ) + y₂ * I) = -((x₁ : ℂ) + y₂ * I - p) := by ring
  have e4 : p - ((x₁ : ℂ) + y₁ * I) = -((x₁ : ℂ) + y₁ * I - p) := by ring
  rw [e3, e4]
  have h3 : log ((x₁ : ℂ) + y₂ * I - p) - log (-((x₁ : ℂ) + y₂ * I - p)) = π * I :=
    log_sub_log_neg_of_im_pos (by simp; linarith)
  have h4 : log ((x₁ : ℂ) + y₁ * I - p) - log (-((x₁ : ℂ) + y₁ * I - p)) = -(π * I) :=
    log_sub_log_neg_of_im_neg (by simp; linarith)
  linear_combination h3 - h4

end RectangleWinding

end
