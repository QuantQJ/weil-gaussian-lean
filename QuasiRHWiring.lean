import StripWidthDependency
import ZeroSymmetry

/-!
# Wiring the 2026 quasi-RH zero-free half-plane into the strip geometry

The external input is carried as a **hypothesis**, never an `axiom`: every theorem
below displays `QuasiRH` in its own signature, so nothing is silently conditional.
-/

set_option autoImplicit false
noncomputable section
open Complex
open scoped Real

namespace QuasiRHWiring

open Reduction ZetaStrip OffLineDetection StripWidthDependency ZeroSymmetry

/-- OpenAI, "The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8",
30 Sep 2026. Stated, not assumed-as-axiom. -/
def QuasiRH : Prop := ∀ s : ℂ, (7 / 8 : ℝ) < s.re → riemannZeta s ≠ 0

theorem re_le_of_quasiRH (h : QuasiRH) {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    ρ.re ≤ 7 / 8 := by
  by_contra hc
  push_neg at hc
  exact h ρ hc hρ.1

/-- The lower bound, from the functional-equation symmetry already proved in the repo. -/
theorem re_ge_of_quasiRH (h : QuasiRH) {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    (1 : ℝ) / 8 ≤ ρ.re := by
  have h1 := re_le_of_quasiRH h (isNontrivialZero_one_sub hρ)
  rw [Complex.sub_re, Complex.one_re] at h1
  linarith

theorem abs_half_sub_re_le (h : QuasiRH) {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    |1 / 2 - ρ.re| ≤ 3 / 8 := by
  rw [abs_le]
  exact ⟨by linarith [re_le_of_quasiRH h hρ], by linarith [re_ge_of_quasiRH h hρ]⟩

/-- **The tightening.** `1/2 → 2/5`. -/
theorem stripHalfWidth_two_fifths (h : QuasiRH) : StripHalfWidth (2 / 5) := by
  apply stripHalfWidth_of_zeroFree
  intro ρ hρ
  exact lt_of_le_of_lt (abs_half_sub_re_le h hρ) (by norm_num)

/-- The far-field decay rate improves from `3/4` to `21/25`. -/
theorem farDecayRate_two_fifths : farDecayRate (2 / 5) = 21 / 25 := by
  unfold farDecayRate; norm_num

theorem farDecayRate_half : farDecayRate (1 / 2) = 3 / 4 := by
  unfold farDecayRate; norm_num

theorem decay_strictly_improves : farDecayRate (1 / 2) < farDecayRate (2 / 5) := by
  rw [farDecayRate_two_fifths, farDecayRate_half]; norm_num

end QuasiRHWiring

#print axioms QuasiRHWiring.stripHalfWidth_two_fifths
#print axioms QuasiRHWiring.decay_strictly_improves
#print axioms QuasiRHWiring.abs_half_sub_re_le
