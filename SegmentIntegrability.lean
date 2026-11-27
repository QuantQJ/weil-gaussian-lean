import ContourShift
import Residue
import ZetaStrip
import ZerosCountable
import Mathlib

/-!
# Segment integrability of `(ζ'/ζ) · G` on the contour-shift rectangle

This module discharges hypothesis (h4) `hF` of `ContourShift.contour_shift_rectangle`:
for `c > 1`, `T > 0`, the integrand `ContourShift.F G s = (ζ'(s)/ζ(s)) · G s` is
interval integrable along the four edges of the rectangle with corners
`(1 - c) - T I` and `c + T I`, provided `G` is continuous on the closed rectangle
and `ζ` has no zero on its boundary.

**Proven (unconditionally, no custom axioms):**

* `ne_one_of_mem_boundary` — the pole `1` never lies on the boundary.
* `continuousAt_deriv_riemannZeta` — `ζ'` is continuous off `1` (analyticity of `ζ`
  on `{1}ᶜ` from `ZerosCountable`, then `AnalyticOnNhd.deriv`).
* `continuousOn_F_boundary` — `F G` is continuous on the boundary.
* `intervalIntegrable_bottom/top/right/left` — the four edge integrals exist
  (`ContinuousOn.intervalIntegrable` after the affine parametrisation).
* `segmentIntegrable_F` — the bundled `Residue.SegmentIntegrable` statement (h4).
* `finite_zerosBox` — the zeros of `ζ` in `1 - c ≤ Re s ≤ c`, `|Im s| ≤ B` are
  finitely many (compactness + isolated zeros of `ζ` on `{1}ᶜ` + `ζ ≠ 0` near the
  pole `1` via `riemannZeta_residue_one`).
* `exists_T_avoiding_zeros`, `exists_T_avoiding_zeros'` — for every `T₀` there is
  `T ≥ T₀` such that `ζ` has no zero on the lines `Im s = ±T` within the strip.
* `boundary_nonvanishing_of_edges` — nonvanishing on the horizontal edges and the
  left edge gives nonvanishing on the whole boundary (right edge `Re s = c > 1` is
  automatic).

**Not proven / not stated:** anything about the size of the edge integrals, or
the `T → ∞` limit. The left edge `Re s = 1 - c < 0` may meet a trivial zero
(`1 - c = -2n`), so nonvanishing there is an explicit hypothesis, not a theorem.
-/

noncomputable section

open Complex MeasureTheory intervalIntegral Set Interval Filter Topology
open scoped Real

namespace SegmentIntegrability

/-! ## The rectangle and its boundary -/

/-- The closed rectangle `[1 - c, c] × [-T, T]` (as in `ContourShift`). -/
def rect (c T : ℝ) : Set ℂ := [[1 - c, c]] ×ℂ [[-T, T]]

/-- The boundary of the rectangle: points of the closed rectangle lying on one of the
four edge lines `Re s = 1 - c`, `Re s = c`, `Im s = -T`, `Im s = T`. -/
def boundary (c T : ℝ) : Set ℂ :=
  {s | s ∈ rect c T ∧ (s.re = 1 - c ∨ s.re = c ∨ s.im = -T ∨ s.im = T)}

/-- The pole `1` never lies on the boundary when `c > 1`, `T > 0`. -/
theorem ne_one_of_mem_boundary {c T : ℝ} (hc : 1 < c) (hT : 0 < T) {s : ℂ}
    (hs : s ∈ boundary c T) : s ≠ 1 := by
  rintro rfl
  obtain ⟨-, h⟩ := hs
  simp only [one_re, one_im] at h
  rcases h with h | h | h | h <;> linarith

/-- Membership in the boundary from the real/imaginary coordinates. -/
theorem mem_boundary_iff {c T : ℝ} {s : ℂ} :
    s ∈ boundary c T ↔
      (s.re ∈ [[1 - c, c]] ∧ s.im ∈ [[-T, T]]) ∧
        (s.re = 1 - c ∨ s.re = c ∨ s.im = -T ∨ s.im = T) := by
  simp only [boundary, rect, mem_setOf_eq, mem_reProdIm]

/-! ## Continuity of the integrand off the zeros and the pole -/

/-- `ζ'` is continuous at every `s ≠ 1`: `ζ` is analytic on `{1}ᶜ`, hence so is `ζ'`. -/
theorem continuousAt_deriv_riemannZeta {s : ℂ} (hs : s ≠ 1) :
    ContinuousAt (deriv riemannZeta) s :=
  (ZerosCountable.analyticOnNhd_riemannZeta.deriv s
    (Set.mem_compl_singleton_iff.mpr hs)).continuousAt

/-- `ζ'/ζ` is continuous at every `s ≠ 1` with `ζ s ≠ 0`. -/
theorem continuousAt_logDeriv_riemannZeta {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    ContinuousAt (fun s => deriv riemannZeta s / riemannZeta s) s :=
  (continuousAt_deriv_riemannZeta hs).div (differentiableAt_riemannZeta hs).continuousAt hz

/-- `F G = (ζ'/ζ) · G` is continuous on the boundary of the rectangle, given `G`
continuous on the closed rectangle and `ζ` nonvanishing on the boundary. -/
theorem continuousOn_F_boundary {c T : ℝ} (hc : 1 < c) (hT : 0 < T) (G : ℂ → ℂ)
    (hG : ContinuousOn G (rect c T))
    (hnz : ∀ s ∈ boundary c T, riemannZeta s ≠ 0) :
    ContinuousOn (ContourShift.F G) (boundary c T) := by
  have h1 : ContinuousOn (fun s => deriv riemannZeta s / riemannZeta s) (boundary c T) :=
    continuousOn_of_forall_continuousAt fun s hs =>
      continuousAt_logDeriv_riemannZeta (ne_one_of_mem_boundary hc hT hs) (hnz s hs)
  exact h1.mul (hG.mono fun s hs => hs.1)

/-- Generic edge lemma: `F G ∘ φ` is interval integrable on `[a, b]` for any continuous
parametrisation `φ` mapping `[[a, b]]` into the boundary. -/
theorem intervalIntegrable_F_comp {c T : ℝ} (hc : 1 < c) (hT : 0 < T) (G : ℂ → ℂ)
    (hG : ContinuousOn G (rect c T))
    (hnz : ∀ s ∈ boundary c T, riemannZeta s ≠ 0)
    {φ : ℝ → ℂ} (hφ : Continuous φ) {a b : ℝ} (hmaps : MapsTo φ [[a, b]] (boundary c T)) :
    IntervalIntegrable (fun x => ContourShift.F G (φ x)) volume a b :=
  ((continuousOn_F_boundary hc hT G hG hnz).comp hφ.continuousOn hmaps).intervalIntegrable

/-! ## The four edges -/

/-- Bottom edge `Im s = -T`, `Re s` from `1 - c` to `c`. -/
theorem intervalIntegrable_bottom {c T : ℝ} (hc : 1 < c) (hT : 0 < T) (G : ℂ → ℂ)
    (hG : ContinuousOn G (rect c T))
    (hnz : ∀ s ∈ boundary c T, riemannZeta s ≠ 0) :
    IntervalIntegrable (fun x : ℝ => ContourShift.F G (x + ((-T : ℝ) : ℂ) * I))
      volume (1 - c) c := by
  refine intervalIntegrable_F_comp hc hT G hG hnz
    (φ := fun x : ℝ => (x : ℂ) + ((-T : ℝ) : ℂ) * I) (by fun_prop) ?_
  intro x hx
  rw [mem_boundary_iff]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
    add_zero, add_im, mul_im, zero_add, zero_mul]
  exact ⟨⟨hx, left_mem_uIcc⟩, by simp⟩

/-- Top edge `Im s = T`, `Re s` from `1 - c` to `c`. -/
theorem intervalIntegrable_top {c T : ℝ} (hc : 1 < c) (hT : 0 < T) (G : ℂ → ℂ)
    (hG : ContinuousOn G (rect c T))
    (hnz : ∀ s ∈ boundary c T, riemannZeta s ≠ 0) :
    IntervalIntegrable (fun x : ℝ => ContourShift.F G (x + (T : ℂ) * I))
      volume (1 - c) c := by
  refine intervalIntegrable_F_comp hc hT G hG hnz
    (φ := fun x : ℝ => (x : ℂ) + (T : ℂ) * I) (by fun_prop) ?_
  intro x hx
  rw [mem_boundary_iff]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
    add_zero, add_im, mul_im, zero_add, zero_mul]
  exact ⟨⟨hx, right_mem_uIcc⟩, by simp⟩

/-- Right edge `Re s = c`, `Im s` from `-T` to `T`. -/
theorem intervalIntegrable_right {c T : ℝ} (hc : 1 < c) (hT : 0 < T) (G : ℂ → ℂ)
    (hG : ContinuousOn G (rect c T))
    (hnz : ∀ s ∈ boundary c T, riemannZeta s ≠ 0) :
    IntervalIntegrable (fun y : ℝ => ContourShift.F G ((c : ℂ) + y * I))
      volume (-T) T := by
  refine intervalIntegrable_F_comp hc hT G hG hnz
    (φ := fun y : ℝ => (c : ℂ) + (y : ℂ) * I) (by fun_prop) ?_
  intro y hy
  rw [mem_boundary_iff]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
    add_zero, add_im, mul_im, zero_add, zero_mul]
  exact ⟨⟨right_mem_uIcc, hy⟩, by simp⟩

/-- Left edge `Re s = 1 - c`, `Im s` from `-T` to `T`. -/
theorem intervalIntegrable_left {c T : ℝ} (hc : 1 < c) (hT : 0 < T) (G : ℂ → ℂ)
    (hG : ContinuousOn G (rect c T))
    (hnz : ∀ s ∈ boundary c T, riemannZeta s ≠ 0) :
    IntervalIntegrable (fun y : ℝ => ContourShift.F G (((1 - c : ℝ) : ℂ) + y * I))
      volume (-T) T := by
  refine intervalIntegrable_F_comp hc hT G hG hnz
    (φ := fun y : ℝ => ((1 - c : ℝ) : ℂ) + (y : ℂ) * I) (by fun_prop) ?_
  intro y hy
  rw [mem_boundary_iff]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
    add_zero, add_im, mul_im, zero_add, zero_mul]
  exact ⟨⟨left_mem_uIcc, hy⟩, by simp⟩

/-! ## The bundled statement: hypothesis (h4) of `contour_shift_rectangle` -/

/-- **Segment integrability of `F G`.** For `c > 1`, `T > 0`, `G` continuous on the
closed rectangle and `ζ` nonvanishing on the boundary, `F G` is interval integrable
along the four edges of the rectangle with corners `(1 - c) - T I` and `c + T I`.
This is exactly hypothesis `hF` of `ContourShift.contour_shift_rectangle`. -/
theorem segmentIntegrable_F (c T : ℝ) (hc : 1 < c) (hT : 0 < T) (G : ℂ → ℂ)
    (hG : ContinuousOn G (rect c T))
    (hnz : ∀ s ∈ boundary c T, riemannZeta s ≠ 0) :
    Residue.SegmentIntegrable (ContourShift.F G) ((1 - c) - T * I) (c + T * I) := by
  have hzre : ((1 - c) - T * I : ℂ).re = 1 - c := by simp
  have hzim : ((1 - c) - T * I : ℂ).im = -T := by simp
  have hwre : (c + T * I : ℂ).re = c := by simp
  have hwim : (c + T * I : ℂ).im = T := by simp
  unfold Residue.SegmentIntegrable
  rw [hzre, hzim, hwre, hwim]
  exact ⟨intervalIntegrable_bottom hc hT G hG hnz, intervalIntegrable_top hc hT G hG hnz,
    intervalIntegrable_right hc hT G hG hnz, intervalIntegrable_left hc hT G hG hnz⟩

/-- A differentiable `G` (hypothesis (h1) of `contour_shift_rectangle`) is in particular
continuous, so (h4) follows from (h1) and boundary nonvanishing. -/
theorem segmentIntegrable_F_of_differentiableOn (c T : ℝ) (hc : 1 < c) (hT : 0 < T)
    (G : ℂ → ℂ) (hG : DifferentiableOn ℂ G ([[1 - c, c]] ×ℂ [[-T, T]]))
    (hnz : ∀ s ∈ boundary c T, riemannZeta s ≠ 0) :
    Residue.SegmentIntegrable (ContourShift.F G) ((1 - c) - T * I) (c + T * I) :=
  segmentIntegrable_F c T hc hT G hG.continuousOn hnz

/-! ## Choosing a height `T` whose horizontal lines carry no zero -/

/-- The zeros of `ζ` in the box `1 - c ≤ Re s ≤ c`, `|Im s| ≤ B`. -/
def zerosBox (c B : ℝ) : Set ℂ :=
  {s | riemannZeta s = 0 ∧ 1 - c ≤ s.re ∧ s.re ≤ c ∧ |s.im| ≤ B}

/-- `ζ` is nonvanishing on a punctured neighbourhood of the pole `1`
(from `riemannZeta_residue_one`: `(s - 1) ζ s → 1`). -/
theorem eventually_ne_zero_nhdsWithin_one : ∀ᶠ s in 𝓝[≠] (1 : ℂ), riemannZeta s ≠ 0 := by
  have h := riemannZeta_residue_one.eventually_ne one_ne_zero
  exact h.mono fun s hs => right_ne_zero_of_mul hs

/-- `ζ` is nonvanishing on a punctured neighbourhood of every point (isolated zeros
off `1`, and the pole at `1`). -/
theorem eventually_ne_zero_nhdsWithin (z : ℂ) : ∀ᶠ s in 𝓝[≠] z, riemannZeta s ≠ 0 := by
  by_cases hz : z = 1
  · subst hz; exact eventually_ne_zero_nhdsWithin_one
  · exact ZerosCountable.isolated_zero_riemannZeta hz

/-- **Finiteness of the zeros in a box.** The zeros of `ζ` with `1 - c ≤ Re s ≤ c` and
`|Im s| ≤ B` form a finite set: an infinite subset of the compact box would have an
accumulation point, contradicting `eventually_ne_zero_nhdsWithin`. -/
theorem finite_zerosBox (c B : ℝ) : (zerosBox c B).Finite := by
  by_contra hinf
  have hinf' : (zerosBox c B).Infinite := hinf
  have hK : IsCompact (Icc (1 - c) c ×ℂ Icc (-B) B) := isCompact_Icc.reProdIm isCompact_Icc
  have hsub : zerosBox c B ⊆ Icc (1 - c) c ×ℂ Icc (-B) B := by
    intro s hs
    obtain ⟨-, h1, h2, h3⟩ := hs
    rw [mem_reProdIm]
    exact ⟨⟨h1, h2⟩, abs_le.mp h3⟩
  obtain ⟨z, -, hacc⟩ := hinf'.exists_accPt_of_subset_isCompact hK hsub
  rw [accPt_iff_frequently] at hacc
  have hev := eventually_nhdsWithin_iff.mp (eventually_ne_zero_nhdsWithin z)
  obtain ⟨y, hy1, hy2⟩ := (hacc.and_eventually hev).exists
  exact hy2 (Set.mem_compl_singleton_iff.mpr hy1.1) hy1.2.1

/-- **A zero-free height exists.** For every `T₀ ≥ 0` there is `T ∈ [T₀, T₀ + 1]` such
that `ζ` has no zero on the lines `Im s = T` and `Im s = -T` within the strip
`1 - c ≤ Re s ≤ c`. The imaginary parts (and their negatives) of the finitely many
zeros in the box of height `T₀ + 1` cannot cover the infinite interval `[T₀, T₀ + 1]`. -/
theorem exists_T_avoiding_zeros (c T₀ : ℝ) (hT₀ : 0 ≤ T₀) :
    ∃ T : ℝ, T₀ ≤ T ∧ T ≤ T₀ + 1 ∧
      ∀ s : ℂ, 1 - c ≤ s.re → s.re ≤ c → (s.im = T ∨ s.im = -T) → riemannZeta s ≠ 0 := by
  have hfin : ((fun s : ℂ => s.im) '' zerosBox c (T₀ + 1) ∪
      (fun s : ℂ => -s.im) '' zerosBox c (T₀ + 1)).Finite :=
    ((finite_zerosBox c _).image _).union ((finite_zerosBox c _).image _)
  obtain ⟨T, hT, hTn⟩ :=
    (Set.Icc_infinite (show T₀ < T₀ + 1 by linarith)).exists_notMem_finite hfin
  refine ⟨T, hT.1, hT.2, ?_⟩
  intro s h1 h2 h3 h0
  apply hTn
  have hT0 : 0 ≤ T := le_trans hT₀ hT.1
  have habs : |s.im| ≤ T₀ + 1 := by
    rcases h3 with h3 | h3
    · rw [h3, _root_.abs_of_nonneg hT0]; exact hT.2
    · rw [h3, abs_neg, _root_.abs_of_nonneg hT0]; exact hT.2
  have hmem : s ∈ zerosBox c (T₀ + 1) := ⟨h0, h1, h2, habs⟩
  rcases h3 with h3 | h3
  · exact Or.inl ⟨s, hmem, h3⟩
  · exact Or.inr ⟨s, hmem, by show -s.im = T; rw [h3, neg_neg]⟩

/-- Variant for arbitrary `T₀` (no sign condition): some `T ≥ max T₀ 1` (hence
`T ≥ T₀`, `T > 0`) has zero-free horizontal lines within the strip. -/
theorem exists_T_avoiding_zeros' (c T₀ : ℝ) :
    ∃ T : ℝ, T₀ ≤ T ∧ 0 < T ∧ T ≤ max T₀ 1 + 1 ∧
      ∀ s : ℂ, 1 - c ≤ s.re → s.re ≤ c → (s.im = T ∨ s.im = -T) → riemannZeta s ≠ 0 := by
  obtain ⟨T, h1, h2, h3⟩ := exists_T_avoiding_zeros c (max T₀ 1)
    (le_trans zero_le_one (le_max_right T₀ 1))
  refine ⟨T, ?_, ?_, h2, h3⟩
  · linarith [le_max_left T₀ 1]
  · linarith [le_max_right T₀ 1]

/-! ## From edge nonvanishing to boundary nonvanishing -/

/-- If `ζ` has no zero on the horizontal lines `Im s = ±T` within the strip (as supplied
by `exists_T_avoiding_zeros`) and no zero on the left edge `Re s = 1 - c`, then `ζ` has
no zero on the whole boundary: the right edge `Re s = c > 1` is zero-free by
`riemannZeta_ne_zero_of_one_le_re`. The left-edge condition is a genuine hypothesis
(`1 - c` could be a trivial zero `-2n`). -/
theorem boundary_nonvanishing_of_edges {c T : ℝ} (hc : 1 < c) (hT : 0 < T)
    (hhoriz : ∀ s : ℂ, 1 - c ≤ s.re → s.re ≤ c → (s.im = T ∨ s.im = -T) →
      riemannZeta s ≠ 0)
    (hleft : ∀ s : ℂ, s.re = 1 - c → -T ≤ s.im → s.im ≤ T → riemannZeta s ≠ 0) :
    ∀ s ∈ boundary c T, riemannZeta s ≠ 0 := by
  intro s hs
  rw [mem_boundary_iff] at hs
  obtain ⟨⟨hre, him⟩, h⟩ := hs
  have hc' : 1 - c ≤ c := by linarith
  have hT' : -T ≤ T := by linarith
  rw [uIcc_of_le hc'] at hre
  rw [uIcc_of_le hT'] at him
  rcases h with h | h | h | h
  · exact hleft s h him.1 him.2
  · exact riemannZeta_ne_zero_of_one_le_re (by rw [h]; exact hc.le)
  · exact hhoriz s hre.1 hre.2 (Or.inr h)
  · exact hhoriz s hre.1 hre.2 (Or.inl h)

end SegmentIntegrability

end
