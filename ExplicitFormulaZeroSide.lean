import PrincipalPartDischarge
import SegmentIntegrability
import HorizontalVanishingSeq
import ZeroSumLimit
import LeftLineBound
import PrimeSideLaplace
import LogDerivSegmentBound
import TestFunctions
import ExplicitFormula
import ZetaStrip
import Reduction
import Mathlib

/-!
# The explicit formula, zero side: assembly

**Weil's explicit formula for `ζ`, with the archimedean part kept as the explicit left-line
functional.** For a test function `g` on `[−a, a]` (`TestFunctions.IsTestFn a g`) put
`G s := Gt a g s = ∫_{-a}^{a} g(u) e^{(s−½)u} du` (entire in `s`), and

* `leftLine a g  := ∫ t, (ζ'/ζ)(−½ + it) · G(−½ + it) dt`  (the archimedean functional),
* `rightLine a g := ∫ t, (ζ'/ζ)(3/2 + it) · G(3/2 + it) dt` (the prime side).

**Main theorem** (`explicit_formula_zero_side`, unconditional): for every enumeration with
multiplicity `zeros : ι → ℂ` of the nontrivial zeros (`ZeroSumLimit.MultEnum zeros`, which
exists unconditionally: `ZeroSumLimit.multEnum_canonical`),

  `∑' i, G (zeros i) = G 1 + (1/2π) (rightLine a g − leftLine a g)`,

equivalently `2πi (∑' i, G(zeros i) − G 1) = i·rightLine a g − i·leftLine a g`
(`explicit_formula_zero_side_raw`). With the prime-side identification of
`PrimeSideLaplace` this becomes (`explicit_formula_zero_side_primeSide`, for `g` supported in
`[−a, a]`; `_indicator` for any `IsTestFn a g`):

  `∑' i, hfun a g (ordinate (zeros i)) = G 1 − ∑ₙ Λ(n) n^{−1/2} g(log n) − (1/2π) leftLine a g`.

This is Weil's explicit formula, evaluated at the **complex** zeros `ρ` (through `Gt a g ρ =
hfun a g (ordinate ρ)`, not at their real projections), over the class `IsTestFn`, with the
archimedean functional given explicitly by the left-line integral plus the pole term `G 1`.
It is the corrected form of the provisional `Reduction.ZeroSideIdentity`, whose documented
defects (real-projected evaluation, quantification over all integrable `g`, free `arch`) it
removes.

**Proof.** (A) `contour_identity_at_height`: the contour-shift identity of
`PrincipalPartDischarge` on the rectangle `[−½, 3/2] × [−T_k, T_k]` along the zero-avoiding
heights `T_k = HorizontalVanishingSeq.heights k` (`k ≥ 2`); the boundary is zero-free (vertical
edges by `ZetaStrip`/`LeftLineBound`, horizontal edges by the avoidance gap and conjugation).
(B) `tendsto_right_truncated` / `tendsto_left_truncated`: the vertical edges converge to the two
line integrals (`LeftLineBound` integrability + `intervalIntegral_tendsto_integral`).
(C) `HorizontalVanishingSeq`: the horizontal edges tend to `0`.
(D) `tendsto_zero_sum_truncated`: the finite zero sums converge to `∑' i, G (zeros i)`
(`ZeroSumLimit`). (E) Uniqueness of limits.

**Hypothesis-dependent:** only `explicit_formula_zero_side_nat`, which packages the `ℕ`-indexed
form under `hinf : {ρ | IsNontrivialZero ρ}.Infinite` (needed solely to index the zeros by `ℕ`;
not proven in the project). Every other theorem — the generic `MultEnum` form, the canonical
enumeration, and the prime-side forms — is unconditional.

**Not proven:** the evaluation of `leftLine a g` through the functional equation (the
classical `Γ'/Γ` form of the archimedean term and the second prime-side half `g(−log n)`);
here the archimedean part is kept as the explicit functional `leftLine a g + G 1`.
No `sorry`, no custom axioms.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Topology Set MeasureTheory Reduction TestFunctions PrincipalPartDischarge
  HorizontalVanishingSeq ZeroSumLimit
open scoped Real ArithmeticFunction Interval

namespace ExplicitFormulaZeroSide

/-! ## The two line functionals -/

/-- The archimedean functional: `ζ'/ζ` against `Gt a g` along the left line `Re s = −½`. -/
def leftLine (a : ℝ) (g : ℝ → ℂ) : ℂ :=
  ∫ t : ℝ, deriv riemannZeta (-1/2 + t * I) / riemannZeta (-1/2 + t * I) * Gt a g (-1/2 + t * I)

/-- The prime-side functional: `ζ'/ζ` against `Gt a g` along the right line `Re s = 3/2`. -/
def rightLine (a : ℝ) (g : ℝ → ℂ) : ℂ :=
  ∫ t : ℝ, deriv riemannZeta (3/2 + t * I) / riemannZeta (3/2 + t * I) * Gt a g (3/2 + t * I)

/-! ## Cast normalisations for the four edges of the rectangle -/

/-- The right edge, cast form. -/
lemma right_pt (y : ℝ) : ((3/2 : ℝ) : ℂ) + y * I = 3/2 + y * I := by push_cast; ring

/-- The left edge, cast form: `1 − 3/2 = −½`. -/
lemma left_pt (y : ℝ) : (1 : ℂ) - ((3/2 : ℝ) : ℂ) + y * I = -1/2 + y * I := by push_cast; ring

/-- The bottom edge, cast form. -/
lemma bottom_pt (x T : ℝ) : (x : ℂ) - T * I = x + ((-T : ℝ) : ℂ) * I := by push_cast; ring

/-! ## The boundary of the rectangle `[−½, 3/2] × [−T_k, T_k]` is zero-free -/

/-- No zero of `ζ` on the horizontal edges `Im s = ±heights k` (`k ≥ 2`): a zero there would be
a nontrivial zero (nonzero imaginary part), contradicting the avoidance gap `δ(4 + k) > 0`. -/
theorem zeta_ne_zero_on_horizontal_edges (k : ℕ) (hk : 2 ≤ k) :
    ∀ s : ℂ, 1 - (3/2 : ℝ) ≤ s.re → s.re ≤ 3/2 →
      (s.im = heights k ∨ s.im = -heights k) → riemannZeta s ≠ 0 := by
  intro s _ _ him h0
  have hT6 := six_le_heights k hk
  have hne : s.im ≠ 0 := by
    rcases him with him | him <;> rw [him] <;> intro h <;> linarith
  have hnt : IsNontrivialZero s := LogDerivSegmentBound.isNontrivialZero_of_im_ne_zero h0 hne
  have hδ := δ_pos k
  rcases him with him | him
  · have h1 := heights_avoid k s hnt
    rw [him, sub_self, abs_zero] at h1
    linarith
  · have h1 := heights_avoid_neg k s hnt
    rw [him, sub_self, abs_zero] at h1
    linarith

/-- No zero of `ζ` on the left edge `Re s = 1 − 3/2 = −½`. -/
theorem zeta_ne_zero_on_left_edge (T : ℝ) :
    ∀ s : ℂ, s.re = 1 - (3/2 : ℝ) → -T ≤ s.im → s.im ≤ T → riemannZeta s ≠ 0 := by
  intro s hs _ _
  apply LeftLineBound.riemannZeta_ne_zero_of_re_eq_neg_half
  rw [hs]
  norm_num

/-- `ζ` has no zero on the whole boundary of the rectangle `[−½, 3/2] × [−heights k, heights k]`
for `k ≥ 2`. -/
theorem boundary_nonvanishing (k : ℕ) (hk : 2 ≤ k) :
    ∀ s ∈ SegmentIntegrability.boundary (3/2) (heights k), riemannZeta s ≠ 0 :=
  SegmentIntegrability.boundary_nonvanishing_of_edges (by norm_num) (heights_pos k)
    (zeta_ne_zero_on_horizontal_edges k hk) (zeta_ne_zero_on_left_edge (heights k))

/-- Every zero of `ζ` (other than `1`) in the closed rectangle is strictly interior: it is a
nontrivial zero, so `0 < Re < 1`, and its ordinate is `≠ ±heights k` by the avoidance gap. -/
theorem zeros_interior (k : ℕ) :
    ∀ s ∈ [[1 - (3/2 : ℝ), (3/2 : ℝ)]] ×ℂ [[-heights k, heights k]], s ≠ 1 → riemannZeta s = 0 →
      1 - (3/2 : ℝ) < s.re ∧ s.re < 3/2 ∧ -heights k < s.im ∧ s.im < heights k := by
  intro s hs hs1 h0
  have hT0 : (0 : ℝ) ≤ heights k := (heights_pos k).le
  have hmem : s ∈ zeroFinset (3/2) (heights k) := mem_zeroFinset.mpr ⟨hs, hs1, h0⟩
  obtain ⟨hnt, him⟩ := (mem_zeroFinset_three_halves hT0).mp hmem
  obtain ⟨hre0, hre1⟩ := ZetaStrip.mem_strip_of_isNontrivialZero hnt
  have hδ := δ_pos k
  have h1 := heights_avoid k s hnt
  have h2 := heights_avoid_neg k s hnt
  rw [abs_le] at him
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · refine lt_of_le_of_ne him.1 fun heq => ?_
    have h3 : s.im - (-heights k) = 0 := by rw [← heq]; ring
    rw [h3, abs_zero] at h2
    linarith
  · refine lt_of_le_of_ne him.2 fun heq => ?_
    rw [heq, sub_self, abs_zero] at h1
    linarith

/-! ## (A) The contour identity at the zero-avoiding heights -/

/-- **(A) Contour identity at height `heights k`** (`k ≥ 2`), in exactly the orientation of
`Residue.rectBoundaryIntegral` (bottom − top + i·right − i·left):

`∫_{−½}^{3/2} F(x − iT) dx − ∫_{−½}^{3/2} F(x + iT) dx + i ∫_{−T}^{T} F(3/2 + iy) dy
  − i ∫_{−T}^{T} F(−½ + iy) dy = 2πi (∑_{ρ ∈ zeroFinset (3/2) T} zetaOrder ρ · G ρ − G 1)`,

with `F s = (ζ'/ζ)(s) · Gt a g s`, `T = heights k`. The hypotheses of
`PrincipalPartDischarge.contour_shift_rectangle_of_G` are discharged: `Gt a g` is entire,
`F` is segment integrable since the boundary is zero-free, and all zeros are interior. -/
theorem contour_identity_at_height {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) (k : ℕ) (hk : 2 ≤ k) :
    (∫ x in (-1/2 : ℝ)..(3/2),
        deriv riemannZeta (x + ((-heights k : ℝ) : ℂ) * I)
            / riemannZeta (x + ((-heights k : ℝ) : ℂ) * I)
          * Gt a g (x + ((-heights k : ℝ) : ℂ) * I))
      - (∫ x in (-1/2 : ℝ)..(3/2),
        deriv riemannZeta (x + heights k * I) / riemannZeta (x + heights k * I)
          * Gt a g (x + heights k * I))
      + I * (∫ y in (-heights k)..(heights k),
        deriv riemannZeta (3/2 + y * I) / riemannZeta (3/2 + y * I) * Gt a g (3/2 + y * I))
      - I * (∫ y in (-heights k)..(heights k),
        deriv riemannZeta (-1/2 + y * I) / riemannZeta (-1/2 + y * I) * Gt a g (-1/2 + y * I))
    = 2 * π * I * (∑ ρ ∈ zeroFinset (3/2) (heights k), (zetaOrder ρ : ℂ) * Gt a g ρ
        - Gt a g 1) := by
  have hc : (1 : ℝ) < 3/2 := by norm_num
  have hT : 0 < heights k := heights_pos k
  have hG : DifferentiableOn ℂ (Gt a g)
      ([[1 - (3/2 : ℝ), (3/2 : ℝ)]] ×ℂ [[-heights k, heights k]]) :=
    (Gt_differentiable h.continuous).differentiableOn
  have hF := SegmentIntegrability.segmentIntegrable_F_of_differentiableOn (3/2) (heights k) hc hT
    (Gt a g) hG (boundary_nonvanishing k hk)
  have key := PrincipalPartDischarge.vertical_lines_difference_of_G (3/2) (heights k) hc hT
    (Gt a g) hG hF (zeros_interior k)
  simp only [ContourShift.F, right_pt, left_pt, bottom_pt] at key
  rw [show (1 - 3/2 : ℝ) = -1/2 by norm_num] at key
  linear_combination key

/-! ## (B) The vertical edges converge to the line integrals -/

/-- `−heights k → −∞`. -/
theorem neg_heights_tendsto_atBot : Tendsto (fun k : ℕ => -heights k) atTop atBot :=
  tendsto_neg_atTop_atBot.comp heights_tendsto_atTop

/-- **(B) Right edge.** The truncated right-line integrals converge to `rightLine a g`. -/
theorem tendsto_right_truncated {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) :
    Tendsto (fun k : ℕ => ∫ y in (-heights k)..(heights k),
      deriv riemannZeta (3/2 + y * I) / riemannZeta (3/2 + y * I) * Gt a g (3/2 + y * I))
      atTop (𝓝 (rightLine a g)) :=
  intervalIntegral_tendsto_integral (LeftLineBound.integrable_logDeriv_mul_Gt_right h)
    neg_heights_tendsto_atBot heights_tendsto_atTop

/-- **(B) Left edge.** The truncated left-line integrals converge to `leftLine a g`. -/
theorem tendsto_left_truncated {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) :
    Tendsto (fun k : ℕ => ∫ y in (-heights k)..(heights k),
      deriv riemannZeta (-1/2 + y * I) / riemannZeta (-1/2 + y * I) * Gt a g (-1/2 + y * I))
      atTop (𝓝 (leftLine a g)) :=
  intervalIntegral_tendsto_integral (LeftLineBound.integrable_logDeriv_mul_Gt_left h)
    neg_heights_tendsto_atBot heights_tendsto_atTop

/-! ## (C) The horizontal edges vanish (re-exported from `HorizontalVanishingSeq`) -/

/-- **(C) Top edge → 0.** -/
theorem tendsto_top_edge {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) :
    Tendsto (fun k : ℕ => ∫ x in (-1/2 : ℝ)..(3/2),
      deriv riemannZeta (x + heights k * I) / riemannZeta (x + heights k * I)
        * Gt a g (x + heights k * I)) atTop (𝓝 0) :=
  horizontal_tendsto_zero_seq h

/-- **(C) Bottom edge → 0.** -/
theorem tendsto_bottom_edge {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) :
    Tendsto (fun k : ℕ => ∫ x in (-1/2 : ℝ)..(3/2),
      deriv riemannZeta (x + ((-heights k : ℝ) : ℂ) * I)
          / riemannZeta (x + ((-heights k : ℝ) : ℂ) * I)
        * Gt a g (x + ((-heights k : ℝ) : ℂ) * I)) atTop (𝓝 0) :=
  horizontal_tendsto_zero_seq_neg h

/-! ## (D) The truncated zero sums converge -/

/-- **(D) Zero sums.** Along the heights, the finite multiplicity-weighted zero sums converge to
`∑' i, Gt a g (zeros i)` for any enumeration with multiplicity. -/
theorem tendsto_zero_sum_truncated {ι : Type*} {zeros : ι → ℂ} (hz : MultEnum zeros) {a : ℝ}
    {g : ℝ → ℂ} (h : IsTestFn a g) :
    Tendsto (fun k : ℕ => ∑ ρ ∈ zeroFinset (3/2) (heights k), (zetaOrder ρ : ℂ) * Gt a g ρ)
      atTop (𝓝 (∑' i, Gt a g (zeros i))) :=
  tendsto_sum_zeroFinset hz h heights heights_tendsto_atTop

/-! ## (E) The main theorem -/

/-- **(E) Explicit formula, zero side (raw form).** For every enumeration with multiplicity
`zeros : ι → ℂ` of the nontrivial zeros and every test function `g` on `[−a, a]`,

  `2πi (∑' i, Gt a g (zeros i) − Gt a g 1) = i · rightLine a g − i · leftLine a g`.

Unconditional: (A) along `k` with the limits (B), (C), (D) and uniqueness of limits. -/
theorem explicit_formula_zero_side_raw {ι : Type*} {zeros : ι → ℂ} (hz : MultEnum zeros)
    {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) :
    2 * π * I * (∑' i, Gt a g (zeros i) - Gt a g 1) = I * rightLine a g - I * leftLine a g := by
  have hBot := tendsto_bottom_edge h
  have hTop := tendsto_top_edge h
  have hR := tendsto_right_truncated h
  have hL := tendsto_left_truncated h
  have hS := tendsto_zero_sum_truncated hz h
  have hlhs := ((hBot.sub hTop).add (hR.const_mul I)).sub (hL.const_mul I)
  have hrhs := (hS.sub (tendsto_const_nhds (x := Gt a g 1))).const_mul (2 * π * I)
  have hlim := tendsto_nhds_unique_of_eventuallyEq hlhs hrhs
    (Filter.eventually_atTop.mpr ⟨2, fun k hk => contour_identity_at_height h k hk⟩)
  linear_combination -hlim

/-- **(E) EXPLICIT FORMULA, ZERO SIDE.** For every enumeration with multiplicity
`zeros : ι → ℂ` of the nontrivial zeros of `ζ` and every test function `g` on `[−a, a]`,

  `∑' i, Gt a g (zeros i) = Gt a g 1 + (1/2π) (rightLine a g − leftLine a g)`.

Weil's explicit formula at the complex zeros, over `IsTestFn`, with the archimedean functional
`Gt a g 1 − (1/2π) leftLine a g` explicit. Unconditional. -/
theorem explicit_formula_zero_side {ι : Type*} {zeros : ι → ℂ} (hz : MultEnum zeros)
    {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) :
    ∑' i, Gt a g (zeros i) = Gt a g 1 + 1 / (2 * π) * (rightLine a g - leftLine a g) := by
  have key := explicit_formula_zero_side_raw hz h
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2π : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero hπ
  have hsub : ∑' i, Gt a g (zeros i) - Gt a g 1 = (rightLine a g - leftLine a g) / (2 * π) := by
    rw [eq_div_iff h2π]
    apply mul_left_cancel₀ Complex.I_ne_zero
    linear_combination key
  linear_combination hsub

/-- **(E′) `HasSum` form.** The zero side converges (absolutely, `ZeroSumLimit.summable_norm_Gt`)
to `Gt a g 1 + (1/2π) (rightLine a g − leftLine a g)`. -/
theorem hasSum_zero_side {ι : Type*} {zeros : ι → ℂ} (hz : MultEnum zeros)
    {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) :
    HasSum (fun i => Gt a g (zeros i))
      (Gt a g 1 + 1 / (2 * π) * (rightLine a g - leftLine a g)) := by
  rw [← explicit_formula_zero_side hz h]
  exact (summable_Gt hz h).hasSum

/-- **(E) Canonical enumeration, unconditional.** The explicit formula for the canonical
enumeration with multiplicity `ZeroSumLimit.canonical : Index → ℂ`. -/
theorem explicit_formula_zero_side_canonical {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) :
    ∑' x : Index, Gt a g (canonical x)
      = Gt a g 1 + 1 / (2 * π) * (rightLine a g - leftLine a g) :=
  explicit_formula_zero_side multEnum_canonical h

/-- **(E) `ℕ`-indexed form.** Under `hinf` (infinitely many nontrivial zeros — the only input
not proven in the project, needed solely for an `ℕ`-indexed enumeration), there is an
enumeration with multiplicity `zeros : ℕ → ℂ` such that the explicit formula holds for every
test function. -/
theorem explicit_formula_zero_side_nat (hinf : {ρ : ℂ | IsNontrivialZero ρ}.Infinite) :
    ∃ zeros : ℕ → ℂ, MultEnum zeros ∧ ∀ (a : ℝ) (g : ℝ → ℂ), IsTestFn a g →
      ∑' n, Gt a g (zeros n) = Gt a g 1 + 1 / (2 * π) * (rightLine a g - leftLine a g) := by
  obtain ⟨zeros, hz⟩ := exists_multEnum_nat hinf
  exact ⟨zeros, hz, fun a g h => explicit_formula_zero_side hz h⟩

/-! ## (F) The right line as the classical prime side -/

/-- The point `3/2 + i(2πξ)` is `ExplicitFormula.line (3/2) ξ`. -/
lemma line_pt (ξ : ℝ) :
    (3/2 : ℂ) + ((2 * π * ξ : ℝ) : ℂ) * I = ExplicitFormula.line (3/2) ξ := by
  simp only [ExplicitFormula.line]
  push_cast
  ring

/-- Change of variables `t = 2πξ`: `rightLine a g = 2π ∫ ξ, (ζ'/ζ)(line ξ) · Gt a g (line ξ)`. -/
theorem rightLine_eq_two_pi_mul_integral_xi (a : ℝ) (g : ℝ → ℂ) :
    rightLine a g = 2 * π * ∫ ξ : ℝ,
      deriv riemannZeta (ExplicitFormula.line (3/2) ξ) / riemannZeta (ExplicitFormula.line (3/2) ξ)
        * Gt a g (ExplicitFormula.line (3/2) ξ) := by
  unfold rightLine
  have hchg := Measure.integral_comp_mul_left
    (fun t : ℝ => deriv riemannZeta (3/2 + t * I) / riemannZeta (3/2 + t * I)
      * Gt a g (3/2 + t * I)) (2 * π)
  simp only [line_pt, abs_of_pos (inv_pos.mpr Real.two_pi_pos), Complex.real_smul] at hchg
  rw [hchg]
  have h2π : (2 * (π : ℂ)) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  push_cast
  rw [← mul_assoc, mul_inv_cancel₀ h2π, one_mul]

/-- The ξ-integral of `ζ'/ζ · Gt` is minus the ξ-integral of `−ζ'/ζ · Gt` (the form used in
`PrimeSideLaplace`). -/
lemma integral_xi_eq_neg (a : ℝ) (g : ℝ → ℂ) :
    (∫ ξ : ℝ, deriv riemannZeta (ExplicitFormula.line (3/2) ξ)
        / riemannZeta (ExplicitFormula.line (3/2) ξ) * Gt a g (ExplicitFormula.line (3/2) ξ))
      = -∫ ξ : ℝ, (-deriv riemannZeta (ExplicitFormula.line (3/2) ξ)
        / riemannZeta (ExplicitFormula.line (3/2) ξ)) * Gt a g (ExplicitFormula.line (3/2) ξ) := by
  rw [← integral_neg]
  congr 1
  funext ξ
  ring

/-- **(F) The right line is minus `2π` times the prime side**, for `g` supported in `[−a, a]`:
`rightLine a g = −2π ∑ₙ Λ(n) n^{−1/2} g(log n)` (`PrimeSideLaplace.rightLine_eq_primeSide`, which
is stated with `−ζ'/ζ`; the sign is tracked by `integral_xi_eq_neg`). -/
theorem rightLine_eq_neg_primeSide {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g)
    (hsupp : ∀ u, a < |u| → g u = 0) :
    rightLine a g
      = -(2 * π * ∑' n : ℕ, (Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2) : ℂ) * g (Real.log n)) := by
  rw [rightLine_eq_two_pi_mul_integral_xi, integral_xi_eq_neg,
    PrimeSideLaplace.rightLine_eq_primeSide h hsupp]
  ring

/-- **(F) The right line is minus `2π` times the prime side, no support hypothesis**: for any
`IsTestFn a g`, with `g` truncated to `[−a, a]` in the sum. -/
theorem rightLine_eq_neg_primeSide_indicator {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) :
    rightLine a g
      = -(2 * π * ∑' n : ℕ, (Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2) : ℂ)
          * (Icc (-a) a).indicator g (Real.log n)) := by
  rw [rightLine_eq_two_pi_mul_integral_xi, integral_xi_eq_neg,
    PrimeSideLaplace.rightLine_eq_primeSide_indicator h]
  ring

/-- **(F) EXPLICIT FORMULA, ZERO SIDE, PRIME-SIDE FORM.** For `g` a test function supported in
`[−a, a]` and any enumeration with multiplicity of the nontrivial zeros,

  `∑' i, hfun a g (ordinate (zeros i))
      = Gt a g 1 − ∑ₙ Λ(n) n^{−1/2} g(log n) − (1/2π) leftLine a g`,

where `hfun a g t = ∫ g(u) e^{itu} du` and `Gt a g ρ = hfun a g (ordinate ρ)` at the complex
zero `ρ = ½ + i·ordinate ρ`. Unconditional. -/
theorem explicit_formula_zero_side_primeSide {ι : Type*} {zeros : ι → ℂ} (hz : MultEnum zeros)
    {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) (hsupp : ∀ u, a < |u| → g u = 0) :
    ∑' i, hfun a g (ordinate (zeros i))
      = Gt a g 1 - (∑' n : ℕ, (Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2) : ℂ) * g (Real.log n))
        - 1 / (2 * π) * leftLine a g := by
  have key := explicit_formula_zero_side hz h
  have hR := rightLine_eq_neg_primeSide h hsupp
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2π : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero hπ
  have hRP : 1 / (2 * π) * rightLine a g
      = -(∑' n : ℕ, (Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2) : ℂ) * g (Real.log n)) := by
    rw [hR, mul_neg, ← mul_assoc, one_div_mul_cancel h2π, one_mul]
  rw [tsum_congr (fun i => (Gt_at_ordinate a g (zeros i)).symm)]
  linear_combination key + hRP

/-- **(F) Prime-side form without a support hypothesis** (the sum carries the truncation
`𝟙_{[−a,a]} g`). -/
theorem explicit_formula_zero_side_primeSide_indicator {ι : Type*} {zeros : ι → ℂ}
    (hz : MultEnum zeros) {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) :
    ∑' i, hfun a g (ordinate (zeros i))
      = Gt a g 1 - (∑' n : ℕ, (Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2) : ℂ)
          * (Icc (-a) a).indicator g (Real.log n))
        - 1 / (2 * π) * leftLine a g := by
  have key := explicit_formula_zero_side hz h
  have hR := rightLine_eq_neg_primeSide_indicator h
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2π : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero hπ
  have hRP : 1 / (2 * π) * rightLine a g
      = -(∑' n : ℕ, (Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2) : ℂ)
          * (Icc (-a) a).indicator g (Real.log n)) := by
    rw [hR, mul_neg, ← mul_assoc, one_div_mul_cancel h2π, one_mul]
  rw [tsum_congr (fun i => (Gt_at_ordinate a g (zeros i)).symm)]
  linear_combination key + hRP

/-- **(F) Prime-side form, canonical enumeration, unconditional.** -/
theorem explicit_formula_zero_side_primeSide_canonical {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g)
    (hsupp : ∀ u, a < |u| → g u = 0) :
    ∑' x : Index, hfun a g (ordinate (canonical x))
      = Gt a g 1 - (∑' n : ℕ, (Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2) : ℂ) * g (Real.log n))
        - 1 / (2 * π) * leftLine a g :=
  explicit_formula_zero_side_primeSide multEnum_canonical h hsupp

end ExplicitFormulaZeroSide

end
