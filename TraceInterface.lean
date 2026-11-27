import ExplicitFormulaZeroSide
import Reduction
import Mathlib

/-!
# The abstract trace interface (archimedean term fixed)

This module replaces the superseded provisional interface `Reduction.ZeroSideIdentity` /
`Reduction.HasArithmeticTrace` (free `arch`, integrable-`g` quantification, real-projected
evaluation) by the corrected one produced by `ExplicitFormulaZeroSide`:

* `weilRHS a g` — the right-hand side of Weil's explicit formula, exactly as proven in
  `ExplicitFormulaZeroSide.explicit_formula_zero_side_primeSide`:
  `Gt a g 1 − ∑ₙ Λ(n) n^{−1/2} g(log n) − (1/2π) leftLine a g`.
  The archimedean term is **fixed**: it is the pole term `Gt a g 1` together with the explicit
  left-line functional `leftLine a g = ∫ (ζ'/ζ)(−½ + it) · Gt a g (−½ + it) dt`. Nothing is free.
* `RealizesExplicitFormula spec` — the **target property for any candidate spectrum**
  `spec : ι → ℂ`: for every test function `g ∈ IsTestFn a g` supported in `[−a, a]`,
  `∑ᵢ hfun a g (spec i) = weilRHS a g` (as a `HasSum`).
* `RealSpectrumRealizes γ` — the same for a real-valued spectrum `γ : ι → ℝ`, the shape a
  self-adjoint operator's spectrum would have.

**Proven (unconditionally):** the ordinates of the nontrivial zeros, in any enumeration with
multiplicity (`zeros_realize`), and in particular the canonical one (`canonical_realizes`),
satisfy `RealizesExplicitFormula`. So the interface is inhabited by the zeros themselves.

**Proven (conditionally):** under RH the ordinates are real, and the real projection of the
canonical ordinates satisfies `RealSpectrumRealizes` (`realizes_of_RH`) — the interface is
satisfiable by a real spectrum exactly when it should be. Conversely, any real spectrum that
contains every ordinate implies RH (`realizes_implies_RH_of_subset`; this is the definition of
the critical line and uses nothing about the explicit formula).

No `sorry`, no custom axioms.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Topology Set MeasureTheory Reduction TestFunctions ExplicitFormulaZeroSide
  ZeroSumLimit
open scoped Real ArithmeticFunction

namespace TraceInterface

/-! ## The fixed right-hand side -/

/-- **The right-hand side of Weil's explicit formula, archimedean term fixed.**
`weilRHS a g = Gt a g 1 − ∑ₙ Λ(n) n^{−1/2} g(log n) − (1/2π) leftLine a g`: the pole term, the
prime side, and the explicit left-line functional `ExplicitFormulaZeroSide.leftLine`. This is
verbatim the right-hand side of `ExplicitFormulaZeroSide.explicit_formula_zero_side_primeSide`;
no term is left free. -/
def weilRHS (a : ℝ) (g : ℝ → ℂ) : ℂ :=
  Gt a g 1 - (∑' n : ℕ, (Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2) : ℂ) * g (Real.log n))
    - 1 / (2 * π) * leftLine a g

/-! ## The interface -/

/-- **The target property for any candidate spectrum** `spec : ι → ℂ`: for every test function
`g` (`IsTestFn a g`) supported in `[−a, a]`, the spectral sum `∑ᵢ hfun a g (spec i)` converges to
the fixed right-hand side `weilRHS a g` of the explicit formula. The archimedean term is fixed as
the left-line functional; the only freedom is the spectrum. The ordinates of the nontrivial
zeros satisfy this unconditionally (`zeros_realize`, `canonical_realizes`). -/
def RealizesExplicitFormula {ι : Type*} (spec : ι → ℂ) : Prop :=
  ∀ (a : ℝ) (g : ℝ → ℂ), IsTestFn a g → (∀ u, a < |u| → g u = 0) →
    HasSum (fun i => hfun a g (spec i)) (weilRHS a g)

/-- **The target property for a real spectrum** `γ : ι → ℝ` (the shape of the spectrum of a
self-adjoint operator): `RealizesExplicitFormula` for the complexification `i ↦ (γ i : ℂ)`. -/
def RealSpectrumRealizes {ι : Type*} (γ : ι → ℝ) : Prop :=
  RealizesExplicitFormula (fun i => ((γ i : ℝ) : ℂ))

/-! ## The zeros satisfy the interface (unconditional) -/

/-- The proven value `Gt a g 1 + (1/2π)(rightLine − leftLine)` equals `weilRHS a g` for `g`
supported in `[−a, a]` (`ExplicitFormulaZeroSide.rightLine_eq_neg_primeSide`). -/
theorem weilRHS_eq {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) (hsupp : ∀ u, a < |u| → g u = 0) :
    Gt a g 1 + 1 / (2 * π) * (rightLine a g - leftLine a g) = weilRHS a g := by
  have hR := rightLine_eq_neg_primeSide h hsupp
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2π : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero hπ
  have hRP : 1 / (2 * π) * rightLine a g
      = -(∑' n : ℕ, (Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2) : ℂ) * g (Real.log n)) := by
    rw [hR, mul_neg, ← mul_assoc, one_div_mul_cancel h2π, one_mul]
  unfold weilRHS
  linear_combination hRP

/-- **The ordinates of the nontrivial zeros realize the explicit formula** — for every
enumeration with multiplicity `zeros : ι → ℂ` (`ZeroSumLimit.MultEnum`). Unconditional: this is
`ExplicitFormulaZeroSide.hasSum_zero_side` rewritten through `Gt_at_ordinate` and the prime-side
identification of the right line. -/
theorem zeros_realize {ι : Type*} {zeros : ι → ℂ} (hz : MultEnum zeros) :
    RealizesExplicitFormula (fun i => ordinate (zeros i)) := by
  intro a g h hsupp
  have hs := hasSum_zero_side hz h
  rw [weilRHS_eq h hsupp] at hs
  have hfun_eq : (fun i => hfun a g (ordinate (zeros i))) = fun i => Gt a g (zeros i) :=
    funext fun i => (Gt_at_ordinate a g (zeros i)).symm
  rw [hfun_eq]
  exact hs

/-- **The canonical enumeration realizes the explicit formula.** Unconditional. -/
theorem canonical_realizes :
    RealizesExplicitFormula (fun x : Index => ordinate (canonical x)) :=
  zeros_realize multEnum_canonical

/-! ## Real spectra -/

/-- Under RH every ordinate of a nontrivial zero is real: `(ordinate ρ).re` casts back to
`ordinate ρ`. -/
theorem ordinate_eq_re_of_RH (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    (((ordinate ρ).re : ℝ) : ℂ) = ordinate ρ := by
  have hre : ρ.re = 1 / 2 := riemannHypothesis_iff.mp hRH ρ hρ
  have him : (ordinate ρ).im = 0 := (re_eq_half_iff_ordinate_im_eq_zero ρ).mp hre
  apply Complex.ext
  · simp
  · simp [him]

/-- **Under RH the real projection of the canonical ordinates realizes the explicit formula.**
The interface `RealSpectrumRealizes` is therefore satisfiable by a real spectrum whenever RH
holds: the spectrum `x ↦ (ordinate (canonical x)).re` is real and its spectral sums reproduce
`weilRHS`. -/
theorem realizes_of_RH (h : RiemannHypothesis) :
    RealSpectrumRealizes (fun x : Index => (ordinate (canonical x)).re) := by
  unfold RealSpectrumRealizes
  have heq : (fun x : Index => (((ordinate (canonical x)).re : ℝ) : ℂ))
      = fun x : Index => ordinate (canonical x) :=
    funext fun x => ordinate_eq_re_of_RH h (multEnum_canonical.nontrivial x)
  rw [heq]
  exact canonical_realizes

/-- **A real spectrum containing every ordinate implies RH.** If every nontrivial zero has its
ordinate among the (real) values `γ i`, then every ordinate is real, i.e. every nontrivial zero
lies on the critical line. This is the definition of the critical line, not a consequence of the
explicit formula. -/
theorem realizes_implies_RH_of_subset {ι : Type*} (γ : ι → ℝ)
    (h : ∀ ρ, IsNontrivialZero ρ → ∃ i, ((γ i : ℝ) : ℂ) = ordinate ρ) : RiemannHypothesis := by
  apply riemannHypothesis_of_ordinates_real
  intro ρ hρ
  obtain ⟨i, hi⟩ := h ρ hρ
  rw [← hi]
  exact Complex.ofReal_im _

end TraceInterface

end
