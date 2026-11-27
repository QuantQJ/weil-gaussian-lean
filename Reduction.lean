import Mathlib
import ExplicitFormula

/-!
# The Hilbert–Pólya reduction: the interface between operators and zeros

Until this module, no theorem in the project mentioned a zero of `ζ`. This
module fixes the interface, using Mathlib's own `RiemannHypothesis`:

* `IsNontrivialZero ρ` — `ζ(ρ) = 0`, `ρ` not a trivial zero, `ρ ≠ 1`
  (exactly the quantifier of Mathlib's `RiemannHypothesis`).
* `ordinate ρ := −i (ρ − ½)` — the number `t` with `ρ = ½ + i t`.
* `SpectrumRealizesZeros S` — every nontrivial zero has its ordinate in `S`.

**Proven (unconditionally):**

* `riemannHypothesis_of_ordinates_real` — if every nontrivial zero has a real
  ordinate, RH holds. (One line of complex arithmetic; it is the *definition*
  of the critical line.)
* `hilbert_polya_reduction` — if the ordinates lie in a set of reals, RH.
* `hilbert_polya_reduction_selfAdjoint` — if the ordinates lie in the spectrum
  of a **self-adjoint element of any C⋆-algebra** (bounded self-adjoint
  operators on a Hilbert space in particular), RH. Uses Mathlib's
  `IsSelfAdjoint.mem_spectrum_eq_re`.

These are reductions, not progress on RH: the whole difficulty is the
hypothesis `SpectrumRealizesZeros (spectrum H)`, and nothing here inhabits
it. Note also that a *bounded* operator has bounded spectrum, while the
ordinates are unbounded (not proven here), so for the bounded version the
hypothesis is expected to be unsatisfiable; the set-valued version is the
one an unbounded operator would instantiate once Mathlib can state its
spectrum.

**Interface only (no theorem claims them):**

* `ZeroSideIdentity` — the target shape of the zero side of the explicit
  formula: `Σ_ρ 𝓕g(ordinate ρ) = primeSide + archimedean`, with the prime
  side the one proven in `ExplicitFormula`.
* `HasArithmeticTrace` — the property an operator's spectrum must have for the
  reduction to bite: its spectral sums reproduce the prime side.

No `sorry`, no custom axioms.
-/

noncomputable section
open Complex MeasureTheory
open scoped FourierTransform

namespace Reduction

/-! ## Zeros and ordinates -/

/-- A nontrivial zero of `ζ`: exactly the hypotheses quantified over in
Mathlib's `RiemannHypothesis`. -/
def IsNontrivialZero (ρ : ℂ) : Prop :=
  riemannZeta ρ = 0 ∧ (¬∃ n : ℕ, ρ = -2 * (n + 1)) ∧ ρ ≠ 1

/-- The ordinate `t` of `ρ = ½ + i t`, i.e. `t = −i (ρ − ½)`. -/
def ordinate (ρ : ℂ) : ℂ := -I * (ρ - 1 / 2)

lemma ordinate_im (ρ : ℂ) : (ordinate ρ).im = 1 / 2 - ρ.re := by
  simp [ordinate]

lemma ordinate_re (ρ : ℂ) : (ordinate ρ).re = ρ.im := by
  simp [ordinate]

/-- A zero lies on the critical line iff its ordinate is real. -/
theorem re_eq_half_iff_ordinate_im_eq_zero (ρ : ℂ) :
    ρ.re = 1 / 2 ↔ (ordinate ρ).im = 0 := by
  rw [ordinate_im]
  constructor <;> intro h <;> linarith

/-- Mathlib's `RiemannHypothesis`, restated through `IsNontrivialZero`. -/
theorem riemannHypothesis_iff :
    RiemannHypothesis ↔ ∀ ρ, IsNontrivialZero ρ → ρ.re = 1 / 2 := by
  constructor
  · intro h ρ ⟨h0, htriv, h1⟩
    exact h ρ h0 htriv h1
  · intro h s h0 htriv h1
    exact h s ⟨h0, htriv, h1⟩

/-! ## The reductions -/

/-- **RH from real ordinates.** -/
theorem riemannHypothesis_of_ordinates_real
    (h : ∀ ρ, IsNontrivialZero ρ → (ordinate ρ).im = 0) : RiemannHypothesis := by
  rw [riemannHypothesis_iff]
  intro ρ hρ
  exact (re_eq_half_iff_ordinate_im_eq_zero ρ).mpr (h ρ hρ)

/-- A set `S ⊆ ℂ` *realizes the zeros* if every nontrivial zero has its
ordinate in `S`. This is the hypothesis a Hilbert–Pólya operator would have
to satisfy with `S = spectrum H`. -/
def SpectrumRealizesZeros (S : Set ℂ) : Prop :=
  ∀ ρ, IsNontrivialZero ρ → ordinate ρ ∈ S

/-- **Hilbert–Pólya reduction, set form.** Ordinates inside a set of reals
⟹ RH. -/
theorem hilbert_polya_reduction {S : Set ℂ} (hS : ∀ z ∈ S, z.im = 0)
    (h : SpectrumRealizesZeros S) : RiemannHypothesis :=
  riemannHypothesis_of_ordinates_real fun ρ hρ => hS _ (h ρ hρ)

/-- **Hilbert–Pólya reduction, operator form.** If the ordinates of the
nontrivial zeros lie in the spectrum of a self-adjoint element of a
C⋆-algebra — e.g. a bounded self-adjoint operator on a Hilbert space — then RH.
The spectrum of a self-adjoint element is real (`IsSelfAdjoint.mem_spectrum_eq_re`). -/
theorem hilbert_polya_reduction_selfAdjoint
    {A : Type*} [CStarAlgebra A] [StarModule ℂ A]
    {H : A} (hH : IsSelfAdjoint H)
    (h : SpectrumRealizesZeros (spectrum ℂ H)) : RiemannHypothesis := by
  refine hilbert_polya_reduction (S := spectrum ℂ H) ?_ h
  intro z hz
  have hzr : z = (z.re : ℂ) := hH.mem_spectrum_eq_re hz
  rw [hzr]
  exact Complex.ofReal_im _

/-- Specialization: a bounded self-adjoint operator on a complex Hilbert space. -/
theorem hilbert_polya_reduction_operator
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    (h : SpectrumRealizesZeros (spectrum ℂ H)) : RiemannHypothesis :=
  hilbert_polya_reduction_selfAdjoint hH h


/-! ## Ordinate-sequence form (compatibility with the earlier revision) -/

/-- The point `½ + iγ` on the critical line. -/
def criticalPoint (γ : ℝ) : ℂ := (1 / 2 : ℂ) + I * γ

theorem criticalPoint_re (γ : ℝ) : (criticalPoint γ).re = 1 / 2 := by
  simp [criticalPoint]

/-- A real sequence `γ` *is the ordinate spectrum* if the nontrivial zeros are
exactly `{½ + iγ_n}`. -/
def IsOrdinateSpectrum (γ : ℕ → ℝ) : Prop :=
  (∀ s, IsNontrivialZero s → ∃ n, s = criticalPoint (γ n)) ∧
    (∀ n, IsNontrivialZero (criticalPoint (γ n)))

/-- **Hilbert–Pólya reduction, ordinate-sequence form.** If a real sequence is
the ordinate spectrum, RH holds. -/
theorem ordinate_spectrum_implies_RH (γ : ℕ → ℝ) (h : IsOrdinateSpectrum γ) :
    RiemannHypothesis := by
  intro s hs htriv hne
  obtain ⟨n, rfl⟩ := h.1 s ⟨hs, htriv, hne⟩
  exact criticalPoint_re (γ n)

/-- Restatement of Mathlib's `RiemannHypothesis` via `IsNontrivialZero`. -/
theorem RH_of_nontrivial_zeros_on_critical_line
    (h : ∀ s, IsNontrivialZero s → s.re = 1 / 2) : RiemannHypothesis :=
  riemannHypothesis_iff.mpr h

/-- The ordinate-sequence form is an instance of the set form: an ordinate
spectrum places every ordinate in the real set `{γ_n}`. -/
theorem isOrdinateSpectrum_realizes (γ : ℕ → ℝ) (h : IsOrdinateSpectrum γ) :
    SpectrumRealizesZeros (Set.range fun n => (γ n : ℂ)) := by
  intro ρ hρ
  obtain ⟨n, rfl⟩ := h.1 ρ hρ
  refine ⟨n, ?_⟩
  simp only [ordinate, criticalPoint]
  ring_nf
  rw [Complex.I_sq]
  ring

/-! ## The interface for the two open halves -/

/-- **Target shape of the zero side of the explicit formula** — PROVISIONAL INTERFACE,
superseded. An independent critic panel (2026-09-12, `docs/`) found three defects
in this definition, all real: (1) it evaluates `𝓕 g` at the REAL part of the
ordinate, discarding `Re ρ − ½`, so it is Weil's zero side only if RH is already
assumed — the correct object evaluates a test transform at the complex zero
(`TestFunctions.Gt a g ρ`); (2) it quantifies over all integrable `g`, for which
the zero sums diverge (indicator functions), so it is unsatisfiable for any
zero-density spectrum — the correct class is `TestFunctions.IsTestFn`;
(3) `arch` is left free, so the identity is trivially satisfiable by choosing
`arch` as the difference. The corrected statement, with `arch` FIXED as an
explicit functional, is the target of `ExplicitFormulaZeroSide`. This definition
is kept only so that `zeroSide_iff_arithmeticTrace` below still compiles; it
asserts nothing and no theorem in the project relies on it. -/
def ZeroSideIdentity (zeros : ℕ → ℂ) (c : ℝ) (arch : (ℝ → ℂ) → ℂ) : Prop :=
  ∀ g : ℝ → ℂ, Integrable g →
    HasSum (fun n => (𝓕 g) (ordinate (zeros n)).re) (ExplicitFormula.primeSide c g + arch g)

/-- **Arithmetic trace property** — PROVISIONAL INTERFACE, superseded for the same
three reasons as `ZeroSideIdentity` (free `arch`; integrable-`g` quantification;
real-projected evaluation). With `arch` unconstrained ANY summable real spectrum
satisfies it (take `arch g := Σ 𝓕g(spec n) − primeSide c g`), so it carries no
arithmetic content. The honest version fixes `arch` to the explicit functional
produced by the contour shift and quantifies over `IsTestFn`; see
`ExplicitFormulaZeroSide`. Kept for compatibility only. -/
def HasArithmeticTrace (spec : ℕ → ℝ) (c : ℝ) (arch : (ℝ → ℂ) → ℂ) : Prop :=
  ∀ g : ℝ → ℂ, Integrable g →
    HasSum (fun n => (𝓕 g) (spec n)) (ExplicitFormula.primeSide c g + arch g)

/-- If an enumeration of the zeros has real ordinates given by a real
sequence `spec`, then `ZeroSideIdentity` and `HasArithmeticTrace` coincide —
the zero side of the explicit formula *is* an arithmetic trace formula for
the ordinates. -/
theorem zeroSide_iff_arithmeticTrace (zeros : ℕ → ℂ) (spec : ℕ → ℝ)
    (hspec : ∀ n, ordinate (zeros n) = (spec n : ℂ)) (c : ℝ) (arch : (ℝ → ℂ) → ℂ) :
    ZeroSideIdentity zeros c arch ↔ HasArithmeticTrace spec c arch := by
  unfold ZeroSideIdentity HasArithmeticTrace
  have hre : ∀ n, (ordinate (zeros n)).re = spec n := fun n => by
    rw [hspec n]; exact Complex.ofReal_re _
  have hfun : ∀ g : ℝ → ℂ, (fun n => (𝓕 g) (ordinate (zeros n)).re) = fun n => (𝓕 g) (spec n) :=
    fun g => funext fun n => by rw [hre n]
  constructor
  · intro h g hg
    have := h g hg
    rwa [hfun g] at this
  · intro h g hg
    have := h g hg
    rwa [hfun g]

end Reduction

end
