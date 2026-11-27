import Mathlib

/-!
# Rectangle boundary integrals and the algebraic half of the residue theorem

This module packages Mathlib's rectangle Cauchy theorem
(`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`) into a named
quantity `rectBoundaryIntegral f z w` — the four-segment boundary integral of
`f` around the axis-parallel rectangle with corners `z` and `w` — and proves
the purely algebraic reduction of the residue theorem for simple poles.

**Proven (unconditionally):**

* `rectBoundaryIntegral_eq_zero_of_differentiableOn` — Cauchy: `f` holomorphic
  on the closed rectangle ⇒ boundary integral `= 0` (wrapper).
* `rectBoundaryIntegral_sub`, `rectBoundaryIntegral_const_mul`,
  `rectBoundaryIntegral_finset_sum` — linearity of the boundary integral,
  under segment integrability (`SegmentIntegrable`) where Mathlib requires it.
* `rectBoundaryIntegral_eq_sum_residue_mul_winding` — **main reduction**: if
  `f - ∑ p ∈ P, residue p / (ζ - pole p)` is holomorphic on the closed
  rectangle and the relevant segment integrals exist, then
  `rectBoundaryIntegral f z w = ∑ p ∈ P, residue p * rectBoundaryIntegral (ζ ↦ (ζ - pole p)⁻¹) z w`.

**Not proven here (by design):** the winding-number lemma
`rectBoundaryIntegral (fun ζ => (ζ - p)⁻¹) z w = 2πI` for `p` in the open
rectangle (and `= 0` for `p` outside). That lemma is proved in a separate
module; combined with `rectBoundaryIntegral_eq_sum_residue_mul_winding` it
yields the residue theorem for simple poles on a rectangle:
`∮ f = 2πI · ∑ (interior residues)`.
-/

noncomputable section

open Complex intervalIntegral MeasureTheory Set Interval

namespace Residue

/-- A simple pole: its location and its residue. -/
structure SimplePole where
  /-- Location of the pole. -/
  pole : ℂ
  /-- Residue of the function at the pole. -/
  residue : ℂ
  deriving DecidableEq

/-- The boundary integral of `f` around the axis-parallel rectangle with corners
`z` and `w`, in the same four-term form as Mathlib's
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`
(bottom edge minus top edge, plus `I ·` right edge minus `I ·` left edge). -/
def rectBoundaryIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I * (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) -
    I * (∫ y : ℝ in z.im..w.im, f (z.re + y * I))

/-- The principal part attached to a finite set of simple poles:
`∑ p ∈ P, residue p / (ζ - pole p)`. -/
def principalPart (P : Finset SimplePole) (ζ : ℂ) : ℂ :=
  ∑ p ∈ P, p.residue / (ζ - p.pole)

/-- `f` with the principal part of `P` subtracted off. -/
def subtractPrincipalPart (f : ℂ → ℂ) (P : Finset SimplePole) : ℂ → ℂ :=
  fun ζ => f ζ - principalPart P ζ

/-- Segment integrability: the four parametrized restrictions of `f` to the
edges of the rectangle with corners `z`, `w` are interval integrable. -/
def SegmentIntegrable (f : ℂ → ℂ) (z w : ℂ) : Prop :=
  IntervalIntegrable (fun x : ℝ => f (x + z.im * I)) volume z.re w.re ∧
  IntervalIntegrable (fun x : ℝ => f (x + w.im * I)) volume z.re w.re ∧
  IntervalIntegrable (fun y : ℝ => f (w.re + y * I)) volume z.im w.im ∧
  IntervalIntegrable (fun y : ℝ => f (z.re + y * I)) volume z.im w.im

/-- Segment integrability is closed under pointwise subtraction. -/
theorem SegmentIntegrable.sub {f g : ℂ → ℂ} {z w : ℂ}
    (hf : SegmentIntegrable f z w) (hg : SegmentIntegrable g z w) :
    SegmentIntegrable (f - g) z w :=
  ⟨hf.1.sub hg.1, hf.2.1.sub hg.2.1, hf.2.2.1.sub hg.2.2.1, hf.2.2.2.sub hg.2.2.2⟩

/-- Segment integrability is closed under multiplication by a constant. -/
theorem SegmentIntegrable.const_mul {f : ℂ → ℂ} {z w : ℂ}
    (hf : SegmentIntegrable f z w) (c : ℂ) :
    SegmentIntegrable (fun ζ => c * f ζ) z w :=
  ⟨hf.1.const_mul c, hf.2.1.const_mul c, hf.2.2.1.const_mul c, hf.2.2.2.const_mul c⟩

/-- A pointwise finite sum of interval-integrable functions is interval integrable
(the `fun x => ∑ ...` form of `IntervalIntegrable.sum`). -/
theorem intervalIntegrable_finset_sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℂ} {a b : ℝ}
    (h : ∀ i ∈ s, IntervalIntegrable (F i) volume a b) :
    IntervalIntegrable (fun x => ∑ i ∈ s, F i x) volume a b := by
  have := IntervalIntegrable.sum s h
  rwa [Finset.sum_fn] at this

/-- Segment integrability is closed under finite sums. -/
theorem SegmentIntegrable.sum {ι : Type*} (s : Finset ι) {F : ι → ℂ → ℂ} {z w : ℂ}
    (h : ∀ i ∈ s, SegmentIntegrable (F i) z w) :
    SegmentIntegrable (fun ζ => ∑ i ∈ s, F i ζ) z w :=
  ⟨intervalIntegrable_finset_sum s (fun i hi => (h i hi).1),
   intervalIntegrable_finset_sum s (fun i hi => (h i hi).2.1),
   intervalIntegrable_finset_sum s (fun i hi => (h i hi).2.2.1),
   intervalIntegrable_finset_sum s (fun i hi => (h i hi).2.2.2)⟩

/-- **Cauchy on a rectangle** (wrapper): if `f` is complex differentiable on the
closed rectangle with corners `z`, `w`, its boundary integral vanishes. -/
theorem rectBoundaryIntegral_eq_zero_of_differentiableOn (f : ℂ → ℂ) (z w : ℂ)
    (H : DifferentiableOn ℂ f ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    rectBoundaryIntegral f z w = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w H
  simpa [rectBoundaryIntegral, smul_eq_mul] using h

/-- The boundary integral is additive under subtraction, given segment
integrability of both functions. -/
theorem rectBoundaryIntegral_sub (f g : ℂ → ℂ) (z w : ℂ)
    (hf : SegmentIntegrable f z w) (hg : SegmentIntegrable g z w) :
    rectBoundaryIntegral (f - g) z w = rectBoundaryIntegral f z w - rectBoundaryIntegral g z w := by
  obtain ⟨hf1, hf2, hf3, hf4⟩ := hf
  obtain ⟨hg1, hg2, hg3, hg4⟩ := hg
  simp only [rectBoundaryIntegral, Pi.sub_apply, integral_sub hf1 hg1, integral_sub hf2 hg2,
    integral_sub hf3 hg3, integral_sub hf4 hg4]
  ring

/-- The boundary integral commutes with multiplication by a constant
(no integrability needed). -/
theorem rectBoundaryIntegral_const_mul (f : ℂ → ℂ) (z w : ℂ) (c : ℂ) :
    rectBoundaryIntegral (fun ζ => c * f ζ) z w = c * rectBoundaryIntegral f z w := by
  simp only [rectBoundaryIntegral, intervalIntegral.integral_const_mul]
  ring

/-- The boundary integral of a finite sum is the finite sum of the boundary
integrals, given segment integrability of each summand. -/
theorem rectBoundaryIntegral_finset_sum {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (z w : ℂ)
    (h : ∀ i ∈ s, SegmentIntegrable (F i) z w) :
    rectBoundaryIntegral (fun ζ => ∑ i ∈ s, F i ζ) z w =
      ∑ i ∈ s, rectBoundaryIntegral (F i) z w := by
  simp only [rectBoundaryIntegral]
  rw [integral_finset_sum (fun i hi => (h i hi).1), integral_finset_sum (fun i hi => (h i hi).2.1),
    integral_finset_sum (fun i hi => (h i hi).2.2.1),
    integral_finset_sum (fun i hi => (h i hi).2.2.2)]
  simp only [Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- The principal part, rewritten with `⁻¹` instead of `/`. -/
theorem principalPart_eq (P : Finset SimplePole) :
    principalPart P = fun ζ => ∑ p ∈ P, p.residue * (ζ - p.pole)⁻¹ := by
  funext ζ
  simp [principalPart, div_eq_mul_inv]

/-- **Main algebraic reduction of the residue theorem for simple poles.**
If `f - principalPart P` is complex differentiable on the closed rectangle with
corners `z`, `w`, and `f` and each `ζ ↦ (ζ - pole p)⁻¹` are segment
integrable, then the boundary integral of `f` is the residue-weighted sum of
the boundary integrals of `ζ ↦ (ζ - pole p)⁻¹`. Together with the winding
lemma (`rectBoundaryIntegral (fun ζ => (ζ - p)⁻¹) z w = 2πI` for interior `p`,
proved elsewhere) this is the residue theorem on a rectangle. -/
theorem rectBoundaryIntegral_eq_sum_residue_mul_winding (f : ℂ → ℂ) (P : Finset SimplePole)
    (z w : ℂ)
    (hdiff : DifferentiableOn ℂ (subtractPrincipalPart f P) ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (hf : SegmentIntegrable f z w)
    (hP : ∀ p ∈ P, SegmentIntegrable (fun ζ => (ζ - p.pole)⁻¹) z w) :
    rectBoundaryIntegral f z w =
      ∑ p ∈ P, p.residue * rectBoundaryIntegral (fun ζ => (ζ - p.pole)⁻¹) z w := by
  have hg : SegmentIntegrable (principalPart P) z w := by
    rw [principalPart_eq]
    exact SegmentIntegrable.sum P (fun p hp => (hP p hp).const_mul p.residue)
  have h0 : rectBoundaryIntegral (f - principalPart P) z w = 0 :=
    rectBoundaryIntegral_eq_zero_of_differentiableOn (f - principalPart P) z w hdiff
  have h1 := rectBoundaryIntegral_sub f (principalPart P) z w hf hg
  rw [h0] at h1
  have h2 : rectBoundaryIntegral (principalPart P) z w =
      ∑ p ∈ P, p.residue * rectBoundaryIntegral (fun ζ => (ζ - p.pole)⁻¹) z w := by
    rw [principalPart_eq,
      rectBoundaryIntegral_finset_sum P (fun p ζ => p.residue * (ζ - p.pole)⁻¹) z w
        (fun p hp => (hP p hp).const_mul p.residue)]
    exact Finset.sum_congr rfl (fun p _ => rectBoundaryIntegral_const_mul _ z w p.residue)
  rw [← h2]
  exact sub_eq_zero.mp h1.symm

end Residue

end
