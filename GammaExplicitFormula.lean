import TraceRealizationRH
import FunctionalEqLogDeriv

/-!
# Two-sided arithmetic explicit formula with an independent gamma functional

The old `leftLine` contains a reflected arithmetic contribution. This file removes
it using the functional equation. The remaining integral is defined using only
Gamma, tangent and the test function, with no zeta function or zero data.

The gamma integral is on a shifted vertical line. Identification with the usual
critical-line digamma integral is a separate normalization theorem, not asserted here.
-/

set_option autoImplicit false
noncomputable section
open Complex MeasureTheory TestFunctions ExplicitFormulaZeroSide
open scoped Real ArithmeticFunction

namespace GammaExplicitFormula

def reflect (g : ℝ → ℂ) (u : ℝ) : ℂ := g (-u)

theorem deriv_reflect {g : ℝ → ℂ} (hg : Differentiable ℝ g) (u : ℝ) :
    deriv (reflect g) u = -deriv g (-u) := by
  have h := ((hg (-u)).hasDerivAt.scomp u (hasDerivAt_neg u)).deriv
  simp only [Function.comp_def, neg_one_smul] at h
  exact h

theorem isTestFn_reflect {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) :
    IsTestFn a (reflect g) where
  nonneg := h.nonneg
  smooth := h.smooth.comp contDiff_neg
  left := by simpa [reflect] using h.right
  right := h.left
  deriv_left := by rw [deriv_reflect h.differentiable, neg_neg, h.deriv_right, neg_zero]
  deriv_right := by rw [deriv_reflect h.differentiable, h.deriv_left, neg_zero]

theorem support_reflect {a : ℝ} {g : ℝ → ℂ}
    (h : ∀ u, a < |u| → g u = 0) : ∀ u, a < |u| → reflect g u = 0 := by
  intro u hu
  exact h (-u) (by simpa using hu)

theorem Gt_reflect (a : ℝ) (g : ℝ → ℂ) (s : ℂ) :
    Gt a (reflect g) s = Gt a g (1 - s) := by
  unfold Gt reflect
  have heq : (fun u : ℝ => g (-u) * exp ((s - 1 / 2) * u)) =
      (fun u : ℝ => g (-u) * exp (((1 - s) - 1 / 2) * (-u : ℝ))) := by
    funext u
    congr 2
    push_cast
    ring
  rw [heq]
  simpa using (intervalIntegral.integral_comp_neg
    (fun u : ℝ => g u * exp (((1 - s) - 1 / 2) * u)) (a := -a) (b := a))

/-- Logarithmic derivative of the gamma/trigonometric factor in the functional equation. -/
def gammaKernel (s : ℂ) : ℂ :=
  -(Real.log (2 * Real.pi) : ℂ) + deriv Gamma s / Gamma s
    - (Real.pi : ℂ) / 2 * tan (Real.pi * s / 2)

/-- Gamma-only integral on `Re s = 3/2`, paired with the reflected transform. -/
def gammaIntegral (a : ℝ) (g : ℝ → ℂ) : ℂ :=
  ∫ t : ℝ, gammaKernel (3 / 2 + t * I) * Gt a g (-1 / 2 - t * I)

theorem logDeriv_reflection (t : ℝ) :
    deriv riemannZeta (-1 / 2 - t * I) / riemannZeta (-1 / 2 - t * I) =
      -gammaKernel (3 / 2 + t * I)
      - deriv riemannZeta (3 / 2 + t * I) / riemannZeta (3 / 2 + t * I) := by
  let s : ℂ := 3 / 2 + t * I
  have hsre : s.re = 3 / 2 := by simp [s]
  have hs (n : ℕ) : s ≠ -(n : ℂ) := by
    intro he
    have := congrArg Complex.re he
    simp only [hsre, neg_re, natCast_re] at this
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hs0 : s ≠ 0 := by intro he; have := congrArg Complex.re he; simp [hsre] at this
  have hs1 : s ≠ 1 := LeftLineBound.three_halves_add_mul_I_ne_one t
  have hz := LeftLineBound.riemannZeta_right_line_ne_zero t
  have hleft : riemannZeta (1 - s) ≠ 0 :=
    LeftLineBound.riemannZeta_ne_zero_of_re_eq_neg_half (by simp [hsre]; norm_num)
  have hc : cos (Real.pi * s / 2) ≠ 0 := by
    intro he
    apply hleft
    rw [riemannZeta_one_sub hs hs1, he]
    simp
  have he := FunctionalEqLogDeriv.logDeriv_zeta_one_sub hs hs0 hs1 hz hc
  have hpt : 1 - s = -1 / 2 - t * I := by dsimp [s]; ring
  rw [hpt] at he
  change _ = -gammaKernel s - _
  dsimp [gammaKernel]
  linear_combination -he

theorem reflected_integrand (a : ℝ) (g : ℝ → ℂ) (t : ℝ) :
    gammaKernel (3 / 2 + t * I) * Gt a g (-1 / 2 - t * I) =
      -(deriv riemannZeta (-1 / 2 - t * I) / riemannZeta (-1 / 2 - t * I)
        * Gt a g (-1 / 2 - t * I))
      - deriv riemannZeta (3 / 2 + t * I) / riemannZeta (3 / 2 + t * I)
        * Gt a (reflect g) (3 / 2 + t * I) := by
  rw [Gt_reflect]
  have hp : (1 - (3 / 2 + t * I) : ℂ) = -1 / 2 - t * I := by ring
  rw [hp, logDeriv_reflection]
  ring

theorem integrable_gamma {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) :
    Integrable (fun t : ℝ => gammaKernel (3 / 2 + t * I) * Gt a g (-1 / 2 - t * I)) := by
  have hl := (LeftLineBound.integrable_logDeriv_mul_Gt_left h).comp_neg
  have hr := LeftLineBound.integrable_logDeriv_mul_Gt_right (isTestFn_reflect h)
  apply (hl.neg.sub hr).congr
  filter_upwards [] with t
  simpa [← sub_eq_add_neg] using (reflected_integrand a g t).symm

theorem gammaIntegral_eq {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) :
    gammaIntegral a g = -leftLine a g - rightLine a (reflect g) := by
  have hl := (LeftLineBound.integrable_logDeriv_mul_Gt_left h).comp_neg
  have hr := LeftLineBound.integrable_logDeriv_mul_Gt_right (isTestFn_reflect h)
  unfold gammaIntegral
  simp_rw [reflected_integrand]
  have hl' : Integrable (fun t : ℝ =>
      deriv riemannZeta (-1 / 2 - t * I) / riemannZeta (-1 / 2 - t * I)
        * Gt a g (-1 / 2 - t * I)) := by simpa [← sub_eq_add_neg] using hl
  rw [integral_sub (by exact hl'.neg) hr, integral_neg]
  congr 1
  change -(∫ t : ℝ, _) = -leftLine a g
  congr 1
  simpa [leftLine, sub_eq_add_neg] using MeasureTheory.integral_neg_eq_self (fun t : ℝ =>
    deriv riemannZeta (-1 / 2 + t * I) / riemannZeta (-1 / 2 + t * I)
      * Gt a g (-1 / 2 + t * I)) volume

/-- The arithmetic sum on the positive logarithmic axis. -/
def primeSum (g : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, (Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2) : ℂ) * g (Real.log n)

/-- The two-sided formula, with a gamma-only shifted-line integral. -/
def gammaRHS (a : ℝ) (g : ℝ → ℂ) : ℂ :=
  Gt a g 1 + gammaIntegral a g / (2 * Real.pi)
    - primeSum g - primeSum (reflect g)

theorem weilRHS_eq_gammaRHS {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g)
    (hsupp : ∀ u, a < |u| → g u = 0) :
    TraceInterface.weilRHS a g = gammaRHS a g := by
  have hr := rightLine_eq_neg_primeSide (isTestFn_reflect h) (support_reflect hsupp)
  have hg := gammaIntegral_eq h
  have hp : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  unfold TraceInterface.weilRHS gammaRHS primeSum
  rw [hg, hr]
  field_simp
  ring

theorem explicit_formula_gamma {ι : Type*} {zeros : ι → ℂ}
    (hz : ZeroSumLimit.MultEnum zeros) {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g)
    (hsupp : ∀ u, a < |u| → g u = 0) :
    HasSum (fun i => hfun a g (Reduction.ordinate (zeros i))) (gammaRHS a g) := by
  rw [← weilRHS_eq_gammaRHS h hsupp]
  exact TraceInterface.zeros_realize hz a g h hsupp

/-- Both pole terms displayed. The subtraction of `G(0)` removes the pole already
encoded by the shifted gamma contour. The critical-line normalization is proved separately
in `FleetStandardExplicitFormula.archimedean_eq_standard`, with the usual separated
log-pi presentation in `FleetSeparatedExplicitFormula.standardArchimedean_eq_separated`. -/
def archimedean (a : ℝ) (g : ℝ → ℂ) : ℂ :=
  gammaIntegral a g / (2 * Real.pi) - Gt a g 0

theorem gammaRHS_eq_two_poles (a : ℝ) (g : ℝ → ℂ) :
    gammaRHS a g = Gt a g 0 + Gt a g 1 + archimedean a g
      - primeSum g - primeSum (reflect g) := by
  unfold gammaRHS archimedean
  ring

/-- The explicit formula with both pole terms and both logarithmic directions
displayed. `archimedean` is the independent shifted-gamma representation above. -/
theorem explicit_formula_two_sided {ι : Type*} {zeros : ι → ℂ}
    (hz : ZeroSumLimit.MultEnum zeros) {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g)
    (hsupp : ∀ u, a < |u| → g u = 0) :
    HasSum (fun i => hfun a g (Reduction.ordinate (zeros i)))
      (Gt a g 0 + Gt a g 1 + archimedean a g
        - ∑' n : ℕ, (Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2) : ℂ)
          * (g (Real.log n) + g (-Real.log n))) := by
  have hs := PrimeSideLaplace.summable_primeSide h hsupp
  have hr := PrimeSideLaplace.summable_primeSide (isTestFn_reflect h) (support_reflect hsupp)
  have he := explicit_formula_gamma hz h hsupp
  rw [gammaRHS_eq_two_poles, sub_sub, primeSum, primeSum, ← hs.tsum_add hr] at he
  simpa only [reflect, ← mul_add] using he

/-- A construction target whose functional and index type are independent of zero data. -/
def RealSpectrumRealizesGamma {ι : Type*} (γ : ι → ℝ) : Prop :=
  ∀ (a : ℝ) (g : ℝ → ℂ), IsTestFn a g → (∀ u, a < |u| → g u = 0) →
    HasSum (fun i => hfun a g (γ i)) (gammaRHS a g)

theorem realizes_gamma_iff {ι : Type*} (γ : ι → ℝ) :
    RealSpectrumRealizesGamma γ ↔ TraceInterface.RealSpectrumRealizes γ := by
  constructor
  · intro h a g hg hs
    rw [weilRHS_eq_gammaRHS hg hs]
    exact h a g hg hs
  · intro h a g hg hs
    rw [← weilRHS_eq_gammaRHS hg hs]
    exact h a g hg hs

/-- The equivalent realization target uses no zeta data in its RHS or indexing type.
This is an equivalence, not a construction of the spectrum from arithmetic. -/
theorem RH_iff_exists_gamma_spectrum :
    RiemannHypothesis ↔ ∃ (ι : Type) (γ : ι → ℝ),
      Summable (fun i => 1 / (1 + (γ i) ^ 2)) ∧ RealSpectrumRealizesGamma γ := by
  constructor
  · intro h
    obtain ⟨γ, hs, hr⟩ := TraceRealizationRH.RH_iff_exists_real_spectrum.mp h
    exact ⟨ZeroSumLimit.Index, γ, hs, (realizes_gamma_iff γ).mpr hr⟩
  · rintro ⟨ι, γ, hs, hr⟩
    exact TraceRealizationRH.real_trace_spectrum_implies_RH γ hs ((realizes_gamma_iff γ).mp hr)

end GammaExplicitFormula
