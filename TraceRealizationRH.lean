import GaussianTraceFormula
import OffLineDetection
import Mathlib

/-!
# A real spectrum realizing the explicit formula forces RH

Glue for Fleet 7. `TraceInterface.RealSpectrumRealizes γ` says: for every
compactly supported `C²` test function `g`, the spectral sum `Σ hfun a g (γ i)`
converges to the arithmetic side `weilRHS a g` of the explicit formula — the
prime sum plus the pole term plus the FIXED left-line archimedean functional.
No zero of `ζ` appears in that hypothesis.

`GaussianTraceFormula` extends both the zero side and the `γ` side to Gaussian
windows by a cutoff limit; `OffLineDetection` shows that an off-line zero makes
the Gaussian zero side grow like `exp(β²/(4b))` as the width `b → 0`, while a real
tempered spectrum grows at most like `b^{-1/2}`. Hence every ordinate is real.
-/

set_option autoImplicit false

open TraceInterface

namespace TraceRealizationRH

/-- **Main theorem of Fleet 7.** If a real sequence `γ` with `Σ 1/(1+γ²) < ∞`
satisfies the explicit formula against every compactly supported `C²` test
function (with the archimedean term fixed as the left-line functional), then the
Riemann Hypothesis holds. -/
theorem real_trace_spectrum_implies_RH {ι : Type*} (γ : ι → ℝ)
    (hsum : Summable (fun i => 1 / (1 + (γ i) ^ 2)))
    (hγ : RealSpectrumRealizes γ) : RiemannHypothesis :=
  OffLineDetection.RH_of_gaussian_trace γ hsum
    (fun _ hb α => GaussianTraceFormula.gaussian_trace_eq γ hsum hγ hb α)
    (fun _ hb α => (GaussianTraceFormula.gaussian_formula_zeros hb α).summable)

/-- Contrapositive form: if RH fails, no real tempered spectrum realizes the
explicit formula. -/
theorem no_real_spectrum_of_not_RH (h : ¬ RiemannHypothesis) {ι : Type*} (γ : ι → ℝ)
    (hsum : Summable (fun i => 1 / (1 + (γ i) ^ 2))) : ¬ RealSpectrumRealizes γ :=
  fun hγ => h (real_trace_spectrum_implies_RH γ hsum hγ)

open Reduction ZeroSumLimit in
/-- The ordinates of the canonical enumeration are tempered: `Σ 1/(1 + Im ρ²) < ∞`. -/
theorem summable_inv_one_add_sq_im :
    Summable (fun x : Index => 1 / (1 + ((ordinate (canonical x)).re) ^ 2)) := by
  have h := ZeroSumLimit.summable_inv_sq_im multEnum_canonical
  have hfin : {x : Index | |(canonical x).im| ≤ 0}.Finite := multEnum_canonical.finite 0
  refine Summable.of_norm_bounded_eventually h ?_
  have : ∀ x ∉ {x : Index | |(canonical x).im| ≤ 0},
      ‖1 / (1 + ((ordinate (canonical x)).re) ^ 2)‖ ≤ 1 / ((canonical x).im) ^ 2 := by
    intro x hx
    simp only [Set.mem_setOf_eq, not_le] at hx
    have hne : (canonical x).im ≠ 0 := fun h0 => by simp [h0] at hx
    have hsq : 0 < ((canonical x).im) ^ 2 := by positivity
    rw [Reduction.ordinate_re, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact one_div_le_one_div_of_le hsq (by linarith)
  exact hfin.subset fun x hx => by
    by_contra hcon
    exact hx (this x hcon)

open Reduction ZeroSumLimit in
/-- **RH is equivalent to the existence of a real tempered spectrum realizing the
explicit formula.** -/
theorem RH_iff_exists_real_spectrum :
    RiemannHypothesis ↔
      ∃ γ : Index → ℝ, Summable (fun x => 1 / (1 + (γ x) ^ 2)) ∧ RealSpectrumRealizes γ := by
  constructor
  · intro h
    exact ⟨fun x => (ordinate (canonical x)).re, summable_inv_one_add_sq_im,
      TraceInterface.realizes_of_RH h⟩
  · rintro ⟨γ, hsum, hγ⟩
    exact real_trace_spectrum_implies_RH γ hsum hγ

end TraceRealizationRH
