import Residue
import RectangleWinding
import RectangleResidue
import LogDerivResidue
import ZetaLogDerivPole
import ZetaStrip
import Mathlib

/-!
# The contour-shift identity for the explicit formula (conditional skeleton)

Let `c > 1`, `T > 0`, and consider the rectangle with corners `z = (1 - c) - T I`
and `w = c + T I`. For a test factor `G : ℂ → ℂ` put `F s := (ζ'(s)/ζ(s)) · G s`.
Let `Z : Finset ℂ` be the zeros of `ζ` in the open rectangle and `m : ℂ → ℕ` their
multiplicities. The residue theorem gives

  `rectBoundaryIntegral F z w = 2πI · (∑ ρ ∈ Z, m ρ · G ρ − G 1)`,

i.e. (right vertical, upward) − (left vertical, upward) + (top) − (bottom) equals
`2πI` times the residues at the zeros (`m ρ · G ρ`) and at the pole `s = 1` (`−G 1`).

**Proven here (no custom axioms):**

* `rectBoundaryIntegral_eq_of_extension` — the residue theorem for simple poles in
  a form robust to Lean's `x / 0 = 0` convention: if `f = K + principalPart P` on the
  closed rectangle *away from the poles* and `K` is holomorphic on the closed
  rectangle, then `∮ f = 2πI · ∑ residues`.
* `contour_shift_rectangle` — the contour-shift identity above, **conditional** on
  the hypotheses (h1)–(h4) listed below.
* `vertical_lines_difference` — the corollary isolating the two vertical integrals.
* `mem_openRect_of_isNontrivialZero`, `one_not_mem_of_isNontrivialZero` — via
  `ZetaStrip`, the location clauses of (h2) hold automatically when `Z` consists of
  nontrivial zeros with `|Im ρ| < T`.

**Hypotheses of `contour_shift_rectangle` (the unproven analytic inputs):**

* (h1) `hG`: `G` is complex differentiable on the closed rectangle.
* (h2) `hZ_in`, `hZ_one`, `hZ_all`: every `ρ ∈ Z` lies in the open rectangle,
  `1 ∉ Z`, and every zero of `ζ` in the closed rectangle other than the point `1`
  belongs to `Z` (so no zero lies on the boundary). The pole `1` lies in the open
  rectangle automatically (`c > 1`, `T > 0`) and this is proven, not assumed.
* (h3) `hH`: **the principal-part / removable-singularity input** — there is a
  holomorphic `H` on the closed rectangle with
  `ζ'/ζ (s) = H s + ∑ ρ ∈ Z, m ρ / (s − ρ) − 1 / (s − 1)` at every `s` of the
  closed rectangle with `ζ s ≠ 0`, `s ≠ 1`. This is exactly "`ζ'/ζ` has only simple
  poles in the rectangle, at the zeros (residue `m ρ`) and at `1` (residue `−1`)".
  `LogDerivResidue` and `ZetaLogDerivPole` prove the pointwise residue *limits*,
  not this global removable-singularity statement, so it stays a hypothesis.
  It is deliberately NOT stated as `DifferentiableOn ℂ (F − principalPart P)`:
  with Lean's `x / 0 = 0`, `F ρ = 0` at a zero `ρ`, so `F − principalPart P` takes
  a junk value at each pole and is (in general) not even continuous there; that
  naive hypothesis would be unsatisfiable. The `∃ H` form is the honest one, and
  `rectBoundaryIntegral_eq_of_extension` is the residue theorem adapted to it.
* (h4) `hF`: `F` is interval integrable along the four edges.

**Not proven / not stated:** the `T → ∞` limit, any bound on the horizontal
segments, the Hadamard factorisation of `ζ` (which would discharge (h3)), and the
identification of `Z` with the actual zero set. This file is the algebraic skeleton
of the analytic half of the explicit formula with the analysis isolated in (h3).
-/

noncomputable section

open Complex MeasureTheory intervalIntegral Set Interval Filter Topology
open scoped Real

namespace ContourShift

open Residue

/-! ## The residue theorem, robust to junk values at the poles -/

/-- **Residue theorem for simple poles, extension form.** If `K` is holomorphic on
the closed rectangle and `f = K + principalPart P` on the closed rectangle away from
the poles (all of which lie in the open rectangle), and `f` is segment integrable,
then `rectBoundaryIntegral f z w = 2πI · ∑ p ∈ P, residue p`. Unlike
`RectangleResidue.rectangle_residue_simplePoles'`, nothing is required of `f` *at*
the poles. -/
theorem rectBoundaryIntegral_eq_of_extension (f K : ℂ → ℂ) (z w : ℂ)
    (hx : z.re < w.re) (hy : z.im < w.im) (P : Finset SimplePole)
    (h_in : ∀ p ∈ P, z.re < p.pole.re ∧ p.pole.re < w.re ∧ z.im < p.pole.im ∧ p.pole.im < w.im)
    (hK : DifferentiableOn ℂ K ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (hfK : ∀ s ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]], (∀ p ∈ P, s ≠ p.pole) →
      f s = K s + principalPart P s)
    (hf : SegmentIntegrable f z w) :
    rectBoundaryIntegral f z w = 2 * π * I * ∑ p ∈ P, p.residue := by
  -- the corrected function, with the "right" values at the poles
  set g : ℂ → ℂ := fun s => K s + principalPart P s with hg
  -- the four edges lie in the closed rectangle and avoid the poles
  have hbot : EqOn (fun x : ℝ => f (x + z.im * I)) (fun x : ℝ => g (x + z.im * I))
      [[z.re, w.re]] := by
    intro x hx'
    show f _ = g _
    apply hfK
    · rw [mem_reProdIm]
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
        sub_zero, add_zero, add_im, mul_im, zero_add, zero_mul]
      exact ⟨hx', left_mem_uIcc⟩
    · intro p hp heq
      have h := congrArg Complex.im heq
      simp at h
      linarith [(h_in p hp).2.2.1]
  have htop : EqOn (fun x : ℝ => f (x + w.im * I)) (fun x : ℝ => g (x + w.im * I))
      [[z.re, w.re]] := by
    intro x hx'
    show f _ = g _
    apply hfK
    · rw [mem_reProdIm]
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
        sub_zero, add_zero, add_im, mul_im, zero_add, zero_mul]
      exact ⟨hx', right_mem_uIcc⟩
    · intro p hp heq
      have h := congrArg Complex.im heq
      simp at h
      linarith [(h_in p hp).2.2.2]
  have hright : EqOn (fun y : ℝ => f (w.re + y * I)) (fun y : ℝ => g (w.re + y * I))
      [[z.im, w.im]] := by
    intro y hy'
    show f _ = g _
    apply hfK
    · rw [mem_reProdIm]
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
        sub_zero, add_zero, add_im, mul_im, zero_add, zero_mul]
      exact ⟨right_mem_uIcc, hy'⟩
    · intro p hp heq
      have h := congrArg Complex.re heq
      simp at h
      linarith [(h_in p hp).2.1]
  have hleft : EqOn (fun y : ℝ => f (z.re + y * I)) (fun y : ℝ => g (z.re + y * I))
      [[z.im, w.im]] := by
    intro y hy'
    show f _ = g _
    apply hfK
    · rw [mem_reProdIm]
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
        sub_zero, add_zero, add_im, mul_im, zero_add, zero_mul]
      exact ⟨left_mem_uIcc, hy'⟩
    · intro p hp heq
      have h := congrArg Complex.re heq
      simp at h
      linarith [(h_in p hp).1]
  -- the boundary integrals of `f` and `g` agree
  have hint : rectBoundaryIntegral f z w = rectBoundaryIntegral g z w := by
    unfold rectBoundaryIntegral
    rw [integral_congr hbot, integral_congr htop, integral_congr hright, integral_congr hleft]
  -- `g` is segment integrable because `f` is
  have hgint : SegmentIntegrable g z w := by
    obtain ⟨h1, h2, h3, h4⟩ := hf
    exact ⟨h1.congr_ae (ae_restrict_of_forall_mem measurableSet_uIoc
        fun x hx => hbot (uIoc_subset_uIcc hx)),
      h2.congr_ae (ae_restrict_of_forall_mem measurableSet_uIoc
        fun x hx => htop (uIoc_subset_uIcc hx)),
      h3.congr_ae (ae_restrict_of_forall_mem measurableSet_uIoc
        fun y hy => hright (uIoc_subset_uIcc hy)),
      h4.congr_ae (ae_restrict_of_forall_mem measurableSet_uIoc
        fun y hy => hleft (uIoc_subset_uIcc hy))⟩
  -- `g - principalPart P = K` identically
  have hsub : subtractPrincipalPart g P = K := by
    funext s
    simp [subtractPrincipalPart, hg]
  rw [hint]
  refine RectangleResidue.rectangle_residue_simplePoles' g z w hx hy P h_in ?_ hgint
  rw [hsub]
  exact hK

/-! ## The explicit-formula integrand and its pole set -/

/-- The integrand of the explicit-formula contour integral: `F s = (ζ'(s)/ζ(s)) · G s`. -/
def F (G : ℂ → ℂ) (s : ℂ) : ℂ := (deriv riemannZeta s / riemannZeta s) * G s

/-- The pole set: each `ρ ∈ Z` with residue `m ρ · G ρ`, and `1` with residue `−G 1`. -/
def poleSet (G : ℂ → ℂ) (Z : Finset ℂ) (m : ℂ → ℕ) : Finset SimplePole :=
  insert ⟨1, -G 1⟩ (Z.image fun ρ => ⟨ρ, (m ρ : ℂ) * G ρ⟩)

/-- `ρ ↦ ⟨ρ, m ρ · G ρ⟩` is injective. -/
theorem poleSet_injOn (G : ℂ → ℂ) (Z : Finset ℂ) (m : ℂ → ℕ) :
    ∀ x ∈ Z, ∀ y ∈ Z,
      (fun ρ : ℂ => (⟨ρ, (m ρ : ℂ) * G ρ⟩ : SimplePole)) x =
        (fun ρ : ℂ => (⟨ρ, (m ρ : ℂ) * G ρ⟩ : SimplePole)) y → x = y := by
  intro x _ y _ h
  simpa using congrArg SimplePole.pole h

/-- If `1 ∉ Z`, the pole at `1` is not among the zero poles. -/
theorem one_pole_not_mem_image (G : ℂ → ℂ) (Z : Finset ℂ) (m : ℂ → ℕ) (hZ1 : (1 : ℂ) ∉ Z) :
    (⟨1, -G 1⟩ : SimplePole) ∉ Z.image fun ρ => (⟨ρ, (m ρ : ℂ) * G ρ⟩ : SimplePole) := by
  intro h
  rw [Finset.mem_image] at h
  obtain ⟨ρ, hρ, h⟩ := h
  have hρ1 : ρ = 1 := by simpa using congrArg SimplePole.pole h
  exact hZ1 (hρ1 ▸ hρ)

/-- The residues of the pole set sum to `∑ ρ ∈ Z, m ρ · G ρ − G 1`. -/
theorem sum_residue_poleSet (G : ℂ → ℂ) (Z : Finset ℂ) (m : ℂ → ℕ) (hZ1 : (1 : ℂ) ∉ Z) :
    ∑ p ∈ poleSet G Z m, p.residue = ∑ ρ ∈ Z, (m ρ : ℂ) * G ρ - G 1 := by
  unfold poleSet
  rw [Finset.sum_insert (one_pole_not_mem_image G Z m hZ1),
    Finset.sum_image (poleSet_injOn G Z m)]
  ring

/-- The principal part of the pole set, written out. -/
theorem principalPart_poleSet (G : ℂ → ℂ) (Z : Finset ℂ) (m : ℂ → ℕ) (hZ1 : (1 : ℂ) ∉ Z)
    (s : ℂ) :
    principalPart (poleSet G Z m) s =
      -G 1 / (s - 1) + ∑ ρ ∈ Z, ((m ρ : ℂ) * G ρ) / (s - ρ) := by
  unfold principalPart poleSet
  rw [Finset.sum_insert (one_pole_not_mem_image G Z m hZ1),
    Finset.sum_image (poleSet_injOn G Z m)]

/-! ## The regular part -/

/-- The holomorphic remainder: `H · G + ∑ ρ ∈ Z, m ρ · dslope G ρ − dslope G 1`, where
`dslope G ρ s = (G s − G ρ)/(s − ρ)` for `s ≠ ρ` (and `G' ρ` at `s = ρ`). -/
def regularPart (H G : ℂ → ℂ) (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ) : ℂ :=
  H s * G s + ∑ ρ ∈ Z, (m ρ : ℂ) * dslope G ρ s - dslope G 1 s

/-- A point of the open rectangle has the closed rectangle as a neighbourhood. -/
theorem closedRect_mem_nhds {c T : ℝ} {ρ : ℂ}
    (hρ : 1 - c < ρ.re ∧ ρ.re < c ∧ -T < ρ.im ∧ ρ.im < T) :
    ([[1 - c, c]] ×ℂ [[-T, T]]) ∈ 𝓝 ρ := by
  rw [mem_nhds_iff]
  refine ⟨Ioo (1 - c) c ×ℂ Ioo (-T) T, ?_, IsOpen.reProdIm isOpen_Ioo isOpen_Ioo, ?_⟩
  · intro s hs
    rw [mem_reProdIm] at hs ⊢
    exact ⟨Icc_subset_uIcc (Ioo_subset_Icc_self hs.1), Icc_subset_uIcc (Ioo_subset_Icc_self hs.2)⟩
  · rw [mem_reProdIm]
    exact ⟨⟨hρ.1, hρ.2.1⟩, ⟨hρ.2.2.1, hρ.2.2.2⟩⟩

/-- The point `1` lies in the open rectangle when `c > 1`, `T > 0`. -/
theorem one_mem_openRect {c T : ℝ} (hc : 1 < c) (hT : 0 < T) :
    1 - c < (1 : ℂ).re ∧ (1 : ℂ).re < c ∧ -T < (1 : ℂ).im ∧ (1 : ℂ).im < T := by
  simp only [one_re, one_im]
  exact ⟨by linarith, hc, by linarith, hT⟩

/-- The regular part is holomorphic on the closed rectangle, given (h1) for `G` and
holomorphy of `H` (the removable-singularity input). -/
theorem differentiableOn_regularPart {c T : ℝ} (hc : 1 < c) (hT : 0 < T)
    (H G : ℂ → ℂ) (Z : Finset ℂ) (m : ℂ → ℕ)
    (hH : DifferentiableOn ℂ H ([[1 - c, c]] ×ℂ [[-T, T]]))
    (hG : DifferentiableOn ℂ G ([[1 - c, c]] ×ℂ [[-T, T]]))
    (hZ_in : ∀ ρ ∈ Z, 1 - c < ρ.re ∧ ρ.re < c ∧ -T < ρ.im ∧ ρ.im < T) :
    DifferentiableOn ℂ (regularPart H G Z m) ([[1 - c, c]] ×ℂ [[-T, T]]) := by
  unfold regularPart
  refine ((hH.fun_mul hG).fun_add (DifferentiableOn.fun_sum fun ρ hρ => ?_)).fun_sub ?_
  · exact ((Complex.differentiableOn_dslope (closedRect_mem_nhds (hZ_in ρ hρ))).mpr hG).const_mul _
  · exact (Complex.differentiableOn_dslope (closedRect_mem_nhds (one_mem_openRect hc hT))).mpr hG

/-- Away from the poles, `F = regularPart + principalPart` on the closed rectangle,
given (h2) and (h3). -/
theorem F_eq_regularPart_add_principalPart {c T : ℝ}
    (H G : ℂ → ℂ) (Z : Finset ℂ) (m : ℂ → ℕ)
    (hZ_one : (1 : ℂ) ∉ Z)
    (hZ_all : ∀ s ∈ [[1 - c, c]] ×ℂ [[-T, T]], s ≠ 1 → riemannZeta s = 0 → s ∈ Z)
    (hHeq : ∀ s ∈ [[1 - c, c]] ×ℂ [[-T, T]], riemannZeta s ≠ 0 → s ≠ 1 →
      deriv riemannZeta s / riemannZeta s =
        H s + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) - 1 / (s - 1)) :
    ∀ s ∈ [[1 - c, c]] ×ℂ [[-T, T]], (∀ p ∈ poleSet G Z m, s ≠ p.pole) →
      F G s = regularPart H G Z m s + principalPart (poleSet G Z m) s := by
  intro s hs hsP
  have hs1 : s ≠ 1 := hsP ⟨1, -G 1⟩ (Finset.mem_insert_self _ _)
  have hsZ : ∀ ρ ∈ Z, s ≠ ρ := fun ρ hρ =>
    hsP ⟨ρ, (m ρ : ℂ) * G ρ⟩ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hρ))
  have hζ : riemannZeta s ≠ 0 := fun h0 => hsZ s (hZ_all s hs hs1 h0) rfl
  have hid := hHeq s hs hζ hs1
  rw [F, regularPart, principalPart_poleSet G Z m hZ_one, hid, dslope_of_ne G hs1,
    slope_def_field]
  have hsum : ∀ ρ ∈ Z, (m ρ : ℂ) * dslope G ρ s = (m ρ : ℂ) * ((G s - G ρ) / (s - ρ)) := by
    intro ρ hρ
    rw [dslope_of_ne G (hsZ ρ hρ), slope_def_field]
  rw [Finset.sum_congr rfl hsum, sub_mul, add_mul, Finset.sum_mul]
  have hsum2 : ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) * G s
      = ∑ ρ ∈ Z, ((m ρ : ℂ) * ((G s - G ρ) / (s - ρ)) + (m ρ : ℂ) * G ρ / (s - ρ)) :=
    Finset.sum_congr rfl (fun ρ _ => by ring)
  rw [hsum2, Finset.sum_add_distrib]
  ring

/-! ## Consistency of (h2) with the strip location of the nontrivial zeros -/

/-- A nontrivial zero `ρ` with `-T < Im ρ < T` lies in the open rectangle
`(1 - c, c) × (-T, T)` for every `c > 1` (its real part is in `(0, 1)` by
`ZetaStrip.mem_strip_of_isNontrivialZero`). So `hZ_in` holds automatically when `Z`
consists of nontrivial zeros with `|Im ρ| < T`. -/
theorem mem_openRect_of_isNontrivialZero {c T : ℝ} (hc : 1 < c) {ρ : ℂ}
    (hρ : Reduction.IsNontrivialZero ρ) (hT₁ : -T < ρ.im) (hT₂ : ρ.im < T) :
    1 - c < ρ.re ∧ ρ.re < c ∧ -T < ρ.im ∧ ρ.im < T := by
  obtain ⟨h0, h1⟩ := ZetaStrip.mem_strip_of_isNontrivialZero hρ
  exact ⟨by linarith, by linarith, hT₁, hT₂⟩

/-- `1` is never a nontrivial zero, so `hZ_one` holds automatically when `Z`
consists of nontrivial zeros. -/
theorem one_not_mem_of_isNontrivialZero {Z : Finset ℂ}
    (hZ : ∀ ρ ∈ Z, Reduction.IsNontrivialZero ρ) : (1 : ℂ) ∉ Z :=
  fun h => (hZ 1 h).2.2 rfl

/-! ## The contour-shift identity -/

/-- **Contour-shift identity (conditional).** For `c > 1`, `T > 0`, the boundary
integral of `F = (ζ'/ζ) · G` around the rectangle with corners `(1 - c) - T I` and
`c + T I` equals `2πI · (∑ ρ ∈ Z, m ρ · G ρ − G 1)`.

Hypotheses (see the module docstring): (h1) `hG`; (h2) `hZ_in`, `hZ_one`, `hZ_all`;
(h3) `hH` — the removable-singularity input: a holomorphic `H` on the closed rectangle
with `ζ'/ζ = H + ∑ ρ ∈ Z, m ρ/(s − ρ) − 1/(s − 1)` wherever `ζ s ≠ 0`, `s ≠ 1`;
(h4) `hF`. Everything else (the residue theorem, the winding number, the location
of the pole `1`, the residue bookkeeping) is proven. -/
theorem contour_shift_rectangle (c T : ℝ) (hc : 1 < c) (hT : 0 < T)
    (G : ℂ → ℂ) (Z : Finset ℂ) (m : ℂ → ℕ)
    (hG : DifferentiableOn ℂ G ([[1 - c, c]] ×ℂ [[-T, T]]))
    (hZ_in : ∀ ρ ∈ Z, 1 - c < ρ.re ∧ ρ.re < c ∧ -T < ρ.im ∧ ρ.im < T)
    (hZ_one : (1 : ℂ) ∉ Z)
    (hZ_all : ∀ s ∈ [[1 - c, c]] ×ℂ [[-T, T]], s ≠ 1 → riemannZeta s = 0 → s ∈ Z)
    (hH : ∃ H : ℂ → ℂ, DifferentiableOn ℂ H ([[1 - c, c]] ×ℂ [[-T, T]]) ∧
      ∀ s ∈ [[1 - c, c]] ×ℂ [[-T, T]], riemannZeta s ≠ 0 → s ≠ 1 →
        deriv riemannZeta s / riemannZeta s =
          H s + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) - 1 / (s - 1))
    (hF : SegmentIntegrable (F G) ((1 - c) - T * I) (c + T * I)) :
    rectBoundaryIntegral (F G) ((1 - c) - T * I) (c + T * I) =
      2 * π * I * (∑ ρ ∈ Z, (m ρ : ℂ) * G ρ - G 1) := by
  obtain ⟨H, hHd, hHeq⟩ := hH
  have hzre : ((1 - c) - T * I : ℂ).re = 1 - c := by simp
  have hzim : ((1 - c) - T * I : ℂ).im = -T := by simp
  have hwre : (c + T * I : ℂ).re = c := by simp
  have hwim : (c + T * I : ℂ).im = T := by simp
  rw [← sum_residue_poleSet G Z m hZ_one]
  refine rectBoundaryIntegral_eq_of_extension (F G) (regularPart H G Z m) _ _
    (by rw [hzre, hwre]; linarith) (by rw [hzim, hwim]; linarith) (poleSet G Z m) ?_ ?_ ?_ hF
  · intro p hp
    rw [hzre, hzim, hwre, hwim]
    unfold poleSet at hp
    rw [Finset.mem_insert, Finset.mem_image] at hp
    rcases hp with rfl | ⟨ρ, hρ, rfl⟩
    · exact one_mem_openRect hc hT
    · exact hZ_in ρ hρ
  · rw [hzre, hzim, hwre, hwim]
    exact differentiableOn_regularPart hc hT H G Z m hHd hG hZ_in
  · rw [hzre, hzim, hwre, hwim]
    exact F_eq_regularPart_add_principalPart H G Z m hZ_one hZ_all hHeq

/-- **Vertical-line difference (conditional corollary).** Isolating the two vertical
integrals in `contour_shift_rectangle`:
`I ∫_{-T}^{T} F(c + yI) dy − I ∫_{-T}^{T} F((1 − c) + yI) dy
  = 2πI (∑ ρ ∈ Z, m ρ · G ρ − G 1) − ∫_{1-c}^{c} F(x − TI) dx + ∫_{1-c}^{c} F(x + TI) dx`,
with the same hypotheses (h1)–(h4). -/
theorem vertical_lines_difference (c T : ℝ) (hc : 1 < c) (hT : 0 < T)
    (G : ℂ → ℂ) (Z : Finset ℂ) (m : ℂ → ℕ)
    (hG : DifferentiableOn ℂ G ([[1 - c, c]] ×ℂ [[-T, T]]))
    (hZ_in : ∀ ρ ∈ Z, 1 - c < ρ.re ∧ ρ.re < c ∧ -T < ρ.im ∧ ρ.im < T)
    (hZ_one : (1 : ℂ) ∉ Z)
    (hZ_all : ∀ s ∈ [[1 - c, c]] ×ℂ [[-T, T]], s ≠ 1 → riemannZeta s = 0 → s ∈ Z)
    (hH : ∃ H : ℂ → ℂ, DifferentiableOn ℂ H ([[1 - c, c]] ×ℂ [[-T, T]]) ∧
      ∀ s ∈ [[1 - c, c]] ×ℂ [[-T, T]], riemannZeta s ≠ 0 → s ≠ 1 →
        deriv riemannZeta s / riemannZeta s =
          H s + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) - 1 / (s - 1))
    (hF : SegmentIntegrable (F G) ((1 - c) - T * I) (c + T * I)) :
    I * (∫ y in (-T)..T, F G (c + y * I)) - I * (∫ y in (-T)..T, F G ((1 - c) + y * I)) =
      2 * π * I * (∑ ρ ∈ Z, (m ρ : ℂ) * G ρ - G 1)
        - (∫ x in (1 - c)..c, F G (x - T * I)) + (∫ x in (1 - c)..c, F G (x + T * I)) := by
  have h := contour_shift_rectangle c T hc hT G Z m hG hZ_in hZ_one hZ_all hH hF
  have hzre : ((1 - c) - T * I : ℂ).re = 1 - c := by simp
  have hzim : ((1 - c) - T * I : ℂ).im = -T := by simp
  have hwre : (c + T * I : ℂ).re = c := by simp
  have hwim : (c + T * I : ℂ).im = T := by simp
  unfold rectBoundaryIntegral at h
  rw [hzre, hzim, hwre, hwim] at h
  have e1 : (fun x : ℝ => F G (x + ((-T : ℝ) : ℂ) * I)) = fun x : ℝ => F G (x - T * I) := by
    funext x
    congr 1
    push_cast
    ring
  have e2 : (fun y : ℝ => F G (((1 - c : ℝ) : ℂ) + y * I)) =
      fun y : ℝ => F G ((1 - c) + y * I) := by
    funext y
    congr 1
    push_cast
    ring
  rw [e1, e2] at h
  linear_combination h

end ContourShift

end
