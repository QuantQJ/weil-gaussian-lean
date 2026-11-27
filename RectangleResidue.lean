import Residue
import RectangleWinding

/-!
# The residue theorem for simple poles on a rectangle

This module glues together the two halves proved elsewhere in the project:

* `Residue.rectBoundaryIntegral_eq_sum_residue_mul_winding` — the algebraic
  reduction: if `f - ∑ p ∈ P, residue p / (ζ - pole p)` is holomorphic on the
  closed rectangle, then `∮ f = ∑ p ∈ P, residue p · ∮ (ζ - pole p)⁻¹`;
* `RectangleWinding.rect_winding` — the winding lemma:
  `∮ (ζ - p)⁻¹ = 2πI` for `p` in the open rectangle.

**Proven (unconditionally, no custom axioms):**

* `rectBoundaryIntegral_eq_rectInt` — the two modules' four-term boundary
  integrals agree: `Residue.rectBoundaryIntegral f (x₁ + y₁ I) (x₂ + y₂ I)
  = RectangleWinding.rectInt f x₁ x₂ y₁ y₂`.
* `intervalIntegrable_inv_sub_horiz` / `intervalIntegrable_inv_sub_vert` —
  `ζ ↦ (ζ - p)⁻¹` is interval integrable along a horizontal (resp. vertical)
  segment not passing through `p` (continuity on the segment).
* `segmentIntegrable_inv_sub_of_mem_interior` — hence `ζ ↦ (ζ - p)⁻¹` is
  `Residue.SegmentIntegrable` on the rectangle whenever `p` is in its interior.
* `rectBoundaryIntegral_inv_sub_eq_two_pi_I` — the winding lemma in
  `Residue.rectBoundaryIntegral` form.
* `rectangle_residue_simplePoles` — **the residue theorem for simple poles**:
  for `x₁ < x₂`, `y₁ < y₂`, a finite set `P` of simple poles all in the open
  rectangle, `f - principalPart P` holomorphic on the closed rectangle and `f`
  segment integrable, `rectBoundaryIntegral f (x₁ + y₁ I) (x₂ + y₂ I)
  = 2πI · ∑ p ∈ P, residue p`.
* `rectangle_residue_simplePoles'` — the same statement with corners `z w : ℂ`.

Nothing is left unproven; the only hypotheses are the holomorphy of the
principal-part-subtracted function and segment integrability of `f` itself,
exactly as in `Residue.rectBoundaryIntegral_eq_sum_residue_mul_winding`.
-/

noncomputable section

open Complex MeasureTheory intervalIntegral Set Interval
open scoped Real

namespace RectangleResidue

open Residue RectangleWinding

/-! ## Bridging the two boundary-integral conventions -/

/-- `Residue.rectBoundaryIntegral` with corners `x₁ + y₁ I`, `x₂ + y₂ I` is
literally `RectangleWinding.rectInt f x₁ x₂ y₁ y₂`. -/
theorem rectBoundaryIntegral_eq_rectInt (f : ℂ → ℂ) (x₁ x₂ y₁ y₂ : ℝ) :
    rectBoundaryIntegral f ((x₁ : ℂ) + y₁ * I) ((x₂ : ℂ) + y₂ * I) =
      rectInt f x₁ x₂ y₁ y₂ := by
  simp [rectBoundaryIntegral, rectInt]

/-- The general form of the bridge: for arbitrary corners `z w`,
`rectBoundaryIntegral f z w = rectInt f z.re w.re z.im w.im`. -/
theorem rectBoundaryIntegral_eq_rectInt' (f : ℂ → ℂ) (z w : ℂ) :
    rectBoundaryIntegral f z w = rectInt f z.re w.re z.im w.im := rfl

/-! ## Segment integrability of `(ζ - p)⁻¹` off the pole -/

/-- Along a horizontal segment at height `y ≠ p.im`, `x ↦ (x + yI - p)⁻¹` is
continuous, hence interval integrable. -/
theorem intervalIntegrable_inv_sub_horiz (p : ℂ) (x₁ x₂ y : ℝ) (hy : y ≠ p.im) :
    IntervalIntegrable (fun x : ℝ => ((x : ℂ) + y * I - p)⁻¹) volume x₁ x₂ := by
  apply Continuous.intervalIntegrable
  apply Continuous.inv₀
  · fun_prop
  · intro x h
    have h' := congrArg Complex.im h
    simp at h'
    exact hy (by linarith)

/-- Along a vertical segment at abscissa `x ≠ p.re`, `y ↦ (x + yI - p)⁻¹` is
continuous, hence interval integrable. -/
theorem intervalIntegrable_inv_sub_vert (p : ℂ) (x y₁ y₂ : ℝ) (hx : x ≠ p.re) :
    IntervalIntegrable (fun y : ℝ => ((x : ℂ) + y * I - p)⁻¹) volume y₁ y₂ := by
  apply Continuous.intervalIntegrable
  apply Continuous.inv₀
  · fun_prop
  · intro y h
    have h' := congrArg Complex.re h
    simp at h'
    exact hx (by linarith)

/-- If `p` lies in the open rectangle `(x₁, x₂) × (y₁, y₂)`, then `ζ ↦ (ζ - p)⁻¹`
is segment integrable (in the sense of `Residue.SegmentIntegrable`) on the
rectangle with corners `x₁ + y₁ I`, `x₂ + y₂ I`. -/
theorem segmentIntegrable_inv_sub_of_mem_interior (p : ℂ) (x₁ x₂ y₁ y₂ : ℝ)
    (hx₁ : x₁ < p.re) (hx₂ : p.re < x₂) (hy₁ : y₁ < p.im) (hy₂ : p.im < y₂) :
    SegmentIntegrable (fun ζ => (ζ - p)⁻¹) ((x₁ : ℂ) + y₁ * I) ((x₂ : ℂ) + y₂ * I) := by
  have hzre : ((x₁ : ℂ) + y₁ * I).re = x₁ := by simp
  have hzim : ((x₁ : ℂ) + y₁ * I).im = y₁ := by simp
  have hwre : ((x₂ : ℂ) + y₂ * I).re = x₂ := by simp
  have hwim : ((x₂ : ℂ) + y₂ * I).im = y₂ := by simp
  unfold SegmentIntegrable
  simp only [hzre, hzim, hwre, hwim]
  exact ⟨intervalIntegrable_inv_sub_horiz p x₁ x₂ y₁ hy₁.ne,
    intervalIntegrable_inv_sub_horiz p x₁ x₂ y₂ hy₂.ne',
    intervalIntegrable_inv_sub_vert p x₂ y₁ y₂ hx₂.ne',
    intervalIntegrable_inv_sub_vert p x₁ y₁ y₂ hx₁.ne⟩

/-! ## The winding lemma in `rectBoundaryIntegral` form -/

/-- For `p` in the open rectangle, the `Residue`-convention boundary integral of
`ζ ↦ (ζ - p)⁻¹` equals `2πI`. -/
theorem rectBoundaryIntegral_inv_sub_eq_two_pi_I (p : ℂ) (x₁ x₂ y₁ y₂ : ℝ)
    (hx₁ : x₁ < p.re) (hx₂ : p.re < x₂) (hy₁ : y₁ < p.im) (hy₂ : p.im < y₂) :
    rectBoundaryIntegral (fun ζ => (ζ - p)⁻¹) ((x₁ : ℂ) + y₁ * I) ((x₂ : ℂ) + y₂ * I) =
      2 * π * I := by
  rw [rectBoundaryIntegral_eq_rectInt]
  exact rect_winding p x₁ x₂ y₁ y₂ hx₁ hx₂ hy₁ hy₂

/-! ## The residue theorem for simple poles -/

/-- **Residue theorem for simple poles on a rectangle.**
Let `x₁ < x₂`, `y₁ < y₂`, and let `P` be a finite set of simple poles, each in the
open rectangle `(x₁, x₂) × (y₁, y₂)`. If `f - ∑ p ∈ P, residue p / (ζ - pole p)`
is complex differentiable on the closed rectangle and `f` is segment integrable
on its boundary, then
`rectBoundaryIntegral f (x₁ + y₁ I) (x₂ + y₂ I) = 2πI · ∑ p ∈ P, residue p`. -/
theorem rectangle_residue_simplePoles (f : ℂ → ℂ) (x₁ x₂ y₁ y₂ : ℝ)
    (_hx : x₁ < x₂) (_hy : y₁ < y₂) (P : Finset SimplePole)
    (h_in : ∀ p ∈ P, x₁ < p.pole.re ∧ p.pole.re < x₂ ∧ y₁ < p.pole.im ∧ p.pole.im < y₂)
    (h_holo : DifferentiableOn ℂ (subtractPrincipalPart f P) ([[x₁, x₂]] ×ℂ [[y₁, y₂]]))
    (hf : SegmentIntegrable f ((x₁ : ℂ) + y₁ * I) ((x₂ : ℂ) + y₂ * I)) :
    rectBoundaryIntegral f ((x₁ : ℂ) + y₁ * I) ((x₂ : ℂ) + y₂ * I) =
      2 * π * I * ∑ p ∈ P, p.residue := by
  have hdiff : DifferentiableOn ℂ (subtractPrincipalPart f P)
      ([[((x₁ : ℂ) + y₁ * I).re, ((x₂ : ℂ) + y₂ * I).re]] ×ℂ
        [[((x₁ : ℂ) + y₁ * I).im, ((x₂ : ℂ) + y₂ * I).im]]) := by
    simpa using h_holo
  have hP : ∀ p ∈ P, SegmentIntegrable (fun ζ => (ζ - p.pole)⁻¹)
      ((x₁ : ℂ) + y₁ * I) ((x₂ : ℂ) + y₂ * I) := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := h_in p hp
    exact segmentIntegrable_inv_sub_of_mem_interior p.pole x₁ x₂ y₁ y₂ h1 h2 h3 h4
  rw [rectBoundaryIntegral_eq_sum_residue_mul_winding f P _ _ hdiff hf hP]
  have hsum : ∀ p ∈ P, p.residue * rectBoundaryIntegral (fun ζ => (ζ - p.pole)⁻¹)
      ((x₁ : ℂ) + y₁ * I) ((x₂ : ℂ) + y₂ * I) = 2 * π * I * p.residue := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := h_in p hp
    rw [rectBoundaryIntegral_inv_sub_eq_two_pi_I p.pole x₁ x₂ y₁ y₂ h1 h2 h3 h4]
    ring
  rw [Finset.sum_congr rfl hsum, ← Finset.mul_sum]

/-- The residue theorem for simple poles with arbitrary complex corners `z`, `w`:
poles in the open rectangle `(z.re, w.re) × (z.im, w.im)`, holomorphy of
`f - principalPart P` on the closed rectangle, and segment integrability of `f`
give `rectBoundaryIntegral f z w = 2πI · ∑ p ∈ P, residue p`. -/
theorem rectangle_residue_simplePoles' (f : ℂ → ℂ) (z w : ℂ)
    (hx : z.re < w.re) (hy : z.im < w.im) (P : Finset SimplePole)
    (h_in : ∀ p ∈ P, z.re < p.pole.re ∧ p.pole.re < w.re ∧ z.im < p.pole.im ∧ p.pole.im < w.im)
    (h_holo : DifferentiableOn ℂ (subtractPrincipalPart f P) ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (hf : SegmentIntegrable f z w) :
    rectBoundaryIntegral f z w = 2 * π * I * ∑ p ∈ P, p.residue := by
  have hz : z = (z.re : ℂ) + z.im * I := (re_add_im z).symm
  have hw : w = (w.re : ℂ) + w.im * I := (re_add_im w).symm
  rw [hz, hw] at hf ⊢
  exact rectangle_residue_simplePoles f z.re w.re z.im w.im hx hy P h_in h_holo hf

end RectangleResidue

end
