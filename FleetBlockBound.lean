import Mathlib

noncomputable section

namespace FleetBlockBound

/-- The real quadratic form of a Hermitian two-block operator. The off-diagonal
blocks are represented by B and its adjoint through the real cross term. -/
def blockForm {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (A : E →L[ℂ] E) (D : F →L[ℂ] F) (B : F →L[ℂ] E) (x : E) (y : F) : ℝ :=
  (inner (𝕜 := ℂ) x (A x)).re + 2 * (inner (𝕜 := ℂ) x (B y)).re + (inner (𝕜 := ℂ) y (D y)).re

lemma cross_lower {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (B : F →L[ℂ] E) {b : ℝ} (hb : ‖B‖ ≤ b) (x : E) (y : F) :
    -b * ‖x‖ * ‖y‖ ≤ (inner (𝕜 := ℂ) x (B y)).re := by
  have hi := re_inner_le_norm (𝕜 := ℂ) (-x) (B y)
  simp only [inner_neg_left, map_neg, norm_neg] at hi
  change -(inner (𝕜 := ℂ) x (B y)).re ≤ ‖x‖ * ‖B y‖ at hi
  have hn := B.le_opNorm y
  have hbn : 0 ≤ b := (norm_nonneg B).trans hb
  have hnorm : ‖B y‖ ≤ b * ‖y‖ := hn.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg y))
  have hm := mul_le_mul_of_nonneg_left hnorm (norm_nonneg x)
  nlinarith

/-- A finite head bound, an infinite tail bound, and a coupling bound combine
without assuming positivity of the whole operator. -/
theorem block_lower_bound {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (A : E →L[ℂ] E) (D : F →L[ℂ] F) (B : F →L[ℂ] E)
    {a d b : ℝ}
    (hA : ∀ x, a * ‖x‖^2 ≤ (inner (𝕜 := ℂ) x (A x)).re)
    (hD : ∀ y, d * ‖y‖^2 ≤ (inner (𝕜 := ℂ) y (D y)).re)
    (hB : ‖B‖ ≤ b) (x : E) (y : F) :
    (min a d - b) * (‖x‖^2 + ‖y‖^2) ≤ blockForm A D B x y := by
  have hb : 0 ≤ b := (norm_nonneg B).trans hB
  have ha := hA x
  have hd := hD y
  have hc := cross_lower B hB x y
  have hax := mul_le_mul_of_nonneg_right (min_le_left a d) (sq_nonneg ‖x‖)
  have hdy := mul_le_mul_of_nonneg_right (min_le_right a d) (sq_nonneg ‖y‖)
  have hs := mul_nonneg hb (sq_nonneg (‖x‖ - ‖y‖))
  unfold blockForm
  nlinarith

/-- Weighted variant useful when the tail coercivity is much stronger than the
head bound. Optimizing epsilon gives a sharper certificate than min(a,d)-b. -/
theorem block_lower_bound_weighted {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (A : E →L[ℂ] E) (D : F →L[ℂ] F) (B : F →L[ℂ] E)
    {a d b ε : ℝ} (hε : 0 < ε)
    (hA : ∀ x, a * ‖x‖^2 ≤ (inner (𝕜 := ℂ) x (A x)).re)
    (hD : ∀ y, d * ‖y‖^2 ≤ (inner (𝕜 := ℂ) y (D y)).re)
    (hB : ‖B‖ ≤ b) (x : E) (y : F) :
    (a - ε) * ‖x‖^2 + (d - b^2 / ε) * ‖y‖^2 ≤ blockForm A D B x y := by
  have ha := hA x
  have hd := hD y
  have hc := cross_lower B hB x y
  have hs := sq_nonneg (ε * ‖x‖ - b * ‖y‖)
  have he : ε * (b^2 / ε) = b^2 := mul_div_cancel₀ _ (ne_of_gt hε)
  have hyoung : 2 * b * ‖x‖ * ‖y‖ ≤ ε * ‖x‖^2 + (b^2 / ε) * ‖y‖^2 := by
    apply (mul_le_mul_iff_right₀ hε).mp
    nlinarith
  unfold blockForm
  nlinarith

/-- The same estimate on quadratic forms, so the diagonal blocks need not be
bounded operators. For an unbounded operator, use its form domains as E and F. -/
theorem form_lower_bound_weighted {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (qE : E → ℝ) (qF : F → ℝ) (B : F →L[ℂ] E)
    {a d b ε : ℝ} (hε : 0 < ε)
    (hA : ∀ x, a * ‖x‖^2 ≤ qE x)
    (hD : ∀ y, d * ‖y‖^2 ≤ qF y)
    (hB : ‖B‖ ≤ b) (x : E) (y : F) :
    (a - ε) * ‖x‖^2 + (d - b^2 / ε) * ‖y‖^2 ≤
      qE x + 2 * (inner (𝕜 := ℂ) x (B y)).re + qF y := by
  have ha := hA x
  have hd := hD y
  have hc := cross_lower B hB x y
  have hs := sq_nonneg (ε * ‖x‖ - b * ‖y‖)
  have he : ε * (b^2 / ε) = b^2 := mul_div_cancel₀ _ (ne_of_gt hε)
  have hyoung : 2 * b * ‖x‖ * ‖y‖ ≤ ε * ‖x‖^2 + (b^2 / ε) * ‖y‖^2 := by
    apply (mul_le_mul_iff_right₀ hε).mp
    nlinarith
  nlinarith

/-- A Schur-complement certificate: diagonal head and tail bounds together with
an off-diagonal norm bound certify a common lower bound m. No spectral
conclusion or numerical error bound is assumed implicitly. -/
theorem form_lower_bound_of_schur {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (qE : E → ℝ) (qF : F → ℝ) (B : F →L[ℂ] E)
    {a d b m : ℝ} (hma : m < a)
    (hA : ∀ x, a * ‖x‖^2 ≤ qE x)
    (hD : ∀ y, d * ‖y‖^2 ≤ qF y)
    (hB : ‖B‖ ≤ b) (hschur : b^2 ≤ (a - m) * (d - m)) (x : E) (y : F) :
    m * (‖x‖^2 + ‖y‖^2) ≤
      qE x + 2 * (inner (𝕜 := ℂ) x (B y)).re + qF y := by
  have he : 0 < a - m := sub_pos.mpr hma
  have hw := form_lower_bound_weighted qE qF B he hA hD hB x y
  have hdiv : b^2 / (a - m) ≤ d - m := (div_le_iff₀ he).mpr (by nlinarith [hschur])
  have hm := mul_le_mul_of_nonneg_right hdiv (sq_nonneg ‖y‖)
  nlinarith


end FleetBlockBound
