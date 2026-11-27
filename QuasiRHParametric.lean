/-
Copyright 2026 James C. Kerr (QuantQJ). Apache-2.0.
-/
import QuasiRHWiring

/-!
# The strip argument, parametric in the zero-free abscissa

`QuasiRHWiring.QuasiRH` fixes the abscissa `7/8` and `QuasiRHWiring.abs_half_sub_re_le`
derives `|1/2 - Re ρ| ≤ 3/8` from it. Neither step uses the value `7/8`: the first is the
half-plane itself, the second is the functional-equation symmetry
`ZeroSymmetry.isNontrivialZero_one_sub`. This file states the same two steps with the
abscissa as a parameter, so a future zero-free half-plane shrinks the strip with no new
proof: `QuasiRHAt σ₀` gives `|1/2 - Re ρ| ≤ σ₀ - 1/2` and `StripHalfWidth δ` for any
`δ > σ₀ - 1/2`.

Nothing here is assumed: `QuasiRHAt` is a `Prop` carried in every signature, exactly as
`QuasiRH` is in `QuasiRHWiring`.  This file imports only `QuasiRHWiring`, so it carries no
dependency on the vendored `OAI/` tree; the `σ₀ = 7/8` instance is obtained at the call site
from `QuasiRHProved.quasiRH_holds`.
-/

set_option autoImplicit false
noncomputable section

open Complex
open Reduction ZetaStrip StripWidthDependency ZeroSymmetry

namespace QuasiRHParametric

/-- Zero-free half-plane with abscissa `σ₀`: `ζ s ≠ 0` whenever `σ₀ < Re s`. -/
def QuasiRHAt (σ₀ : ℝ) : Prop := ∀ s : ℂ, σ₀ < s.re → riemannZeta s ≠ 0

/-- The fixed-abscissa hypothesis of `QuasiRHWiring` is the case `σ₀ = 7/8`. -/
theorem quasiRHAt_seven_eighths_iff : QuasiRHAt (7 / 8) ↔ QuasiRHWiring.QuasiRH := Iff.rfl

/-- A larger abscissa is a weaker hypothesis. -/
theorem QuasiRHAt.mono {σ₀ σ₁ : ℝ} (h : QuasiRHAt σ₀) (h01 : σ₀ ≤ σ₁) : QuasiRHAt σ₁ :=
  fun s hs => h s (lt_of_le_of_lt h01 hs)

/-- Upper bound on the real part of a nontrivial zero. -/
theorem re_le_of_quasiRHAt {σ₀ : ℝ} (h : QuasiRHAt σ₀) {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    ρ.re ≤ σ₀ := by
  by_contra hc
  push_neg at hc
  exact h ρ hc hρ.1

/-- Lower bound, from the functional-equation symmetry of the zero set. -/
theorem re_ge_of_quasiRHAt {σ₀ : ℝ} (h : QuasiRHAt σ₀) {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    1 - σ₀ ≤ ρ.re := by
  have h1 := re_le_of_quasiRHAt h (isNontrivialZero_one_sub hρ)
  rw [Complex.sub_re, Complex.one_re] at h1
  linarith

/-- **The strip, parametric.** Abscissa `σ₀` gives half-width `σ₀ - 1/2`. -/
theorem abs_half_sub_re_le_of_quasiRHAt {σ₀ : ℝ} (h : QuasiRHAt σ₀) {ρ : ℂ}
    (hρ : IsNontrivialZero ρ) : |1 / 2 - ρ.re| ≤ σ₀ - 1 / 2 := by
  rw [abs_le]
  exact ⟨by linarith [re_le_of_quasiRHAt h hρ], by linarith [re_ge_of_quasiRHAt h hρ]⟩

/-- **Automatic shrinking.** Any `δ` strictly above `σ₀ - 1/2` is a strip half-width. -/
theorem stripHalfWidth_of_quasiRHAt {σ₀ δ : ℝ} (h : QuasiRHAt σ₀) (hδ : σ₀ - 1 / 2 < δ) :
    StripHalfWidth δ := by
  apply stripHalfWidth_of_zeroFree
  intro ρ hρ
  exact lt_of_le_of_lt (abs_half_sub_re_le_of_quasiRHAt h hρ) hδ

/-- The present input `σ₀ = 7/8` reproduces `QuasiRHWiring.abs_half_sub_re_le`. -/
theorem abs_half_sub_re_le_seven_eighths (h : QuasiRHAt (7 / 8)) {ρ : ℂ}
    (hρ : IsNontrivialZero ρ) : |1 / 2 - ρ.re| ≤ 3 / 8 := by
  have := abs_half_sub_re_le_of_quasiRHAt h hρ
  linarith

/-- And reproduces the `2/5` strip. -/
theorem stripHalfWidth_two_fifths_of (h : QuasiRHAt (7 / 8)) : StripHalfWidth (2 / 5) :=
  stripHalfWidth_of_quasiRHAt h (by norm_num)

/-!
The unconditional instance `QuasiRHAt (7/8)` is **not** stated here: it would need
`QuasiRHProved.quasiRH_holds`, hence the vendored `OAI/` tree, and this file is deliberately
OAI-free so that it builds and audits on its own.  To use it, apply
`quasiRHAt_seven_eighths_iff.mpr QuasiRHWiring.quasiRH_holds` at the call site.
-/

end QuasiRHParametric
