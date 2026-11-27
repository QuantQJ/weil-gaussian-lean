/-
Copyright 2026 James C. Kerr (QuantQJ). Apache-2.0.
-/
import FleetSimpleZeros

/-!
# The sign, not the norm: a one-point arithmetic test

Every criterion in this development — `RH_iff_zero_trace_bound'`, `RH_iff_pole_prime_bound`,
`RH_iff_primeSumSym_bound`, `RH_iff_PrimeTarget`, `FleetSimpleZeros.TraceLimsupLe` — takes a
**norm** of the zero trace, or a limsup of one.  That throws the sign away, and the sign is
strictly stronger information available at no extra cost.

Under RH every ordinate is real, so every term `gaussHat b α (ordinate ρ)` is a *positive real*
and the whole trace is a positive real.  Hence

  `signedTrace b α < 0`  at a **single** `(b, α)`  ⟹  `¬ RiemannHypothesis`.

No limit, no norm, no quantifier over `b`, no bound to establish — one evaluation.  And by
`FleetPrimePoleBoundRH.zero_trace_eq_rhs` the left side is
`poleTerm b α + archimedean (gauss b α) - primeSumSym b α`, so this is a single inequality in
the primes.

## Why a sign can go negative at all

`gaussHat b α` at a **complex** ordinate `γ - i e` has modulus `√(π/b) e^{(e² - (γ-α)²)/(4b)}`
and argument `-(γ-α)e/(2b)` (`GaussianTest.norm_gaussHat`, and `FleetPairCosh.gaussRatioB` for
the amplification `2(exp (e²/(4b)) - 1)`).  The modulus is amplified by `e^{e²/(4b)}` and the
phase rotates at rate `(γ-α)/(2b)`, so an off-line zero contributes an *oscillating* term whose
real part is negative on half of each period, with amplitude growing as `b → 0`.  On-line zeros
contribute only positive terms.  So the sign test fires exactly where the amplification does,
and it fires at a point rather than in a limit.

## The structure nobody used: this is a heat evolution

`√(π/b) exp(-(u)²/(4b)) = 2π · p_b(u)` where `p_b` is the heat kernel at time `b`.  So, writing
`μ` for the zero-counting measure on ordinates,

  `signedTrace b α = 2π (p_b * μ)(α)`,   hence   `∂_b signedTrace = ∂²_α signedTrace`.

The two parameters of every criterion in the tree are therefore **not independent**: the family
is one solution of the heat equation, determined by its data at any single `b`.  Two
consequences, both free:

* forward propagation — `p_{b'-b} * ·` is convolution with a probability kernel, so
  nonnegativity at `b` implies it at every `b' > b`.  Violations are therefore easiest to find
  at *small* `b`, which is the regime `FleetTraceBoundRH.RH_of_zero_trace_small_b_bound` already
  localised the criterion to.
* under RH the data is a nonnegative measure **on `ℝ`**, so by Widder's theorem `signedTrace` is
  the unique nonnegative heat evolution of it; an off-line zero puts mass off `ℝ` and the
  solution stops being nonnegative.  That is the same mechanism as the de Bruijn–Newman flow
  (`FleetDeBruijnNewman`), here on the prime side instead of on `Ξ`.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology
open scoped Real
open OffLineDetection Reduction ZeroSumLimit GaussianTest PrincipalPartDischarge

namespace FleetSignedTrace

/-- The Gaussian zero trace with its **sign** kept. -/
def signedTrace (b α : ℝ) : ℝ := (∑' x : Index, gaussHat b α (ordinate (canonical x))).re

/-- **Under RH the signed trace is nonnegative at every `(b, α)`**, because every ordinate is
real and `gaussHat` at a real argument is a positive real. -/
theorem signedTrace_nonneg_of_RH (hRH : RiemannHypothesis) {b : ℝ} (hb : 0 < b) (α : ℝ) :
    0 ≤ signedTrace b α := by
  classical
  have hreal : ∀ z : Index, t z = (((t z).re : ℝ) : ℂ) := by
    intro z
    have hre : (canonical z).re = 1 / 2 := riemannHypothesis_iff.mp hRH _ z.1.2
    have him : (t z).im = 0 := by rw [t_im, hre]; norm_num
    exact Complex.ext rfl (by simpa using him)
  set F : Index → ℝ := fun z =>
    Real.sqrt (π / b) * Real.exp (-((t z).re - α) ^ 2 / (4 * b)) with hF
  have hFeq : ∀ z : Index, gaussHat b α (ordinate (canonical z)) = ((F z : ℝ) : ℂ) := by
    intro z
    have hz : ordinate (canonical z) = t z := rfl
    rw [hz, hreal z, gaussHat_real hb]
  have hFnn : ∀ z, 0 ≤ F z := fun z => by rw [hF]; positivity
  have hsumC : Summable (fun z : Index => gaussHat b α (ordinate (canonical z))) :=
    (GaussianTraceFormula.gaussian_formula_zeros hb α).summable
  have hsumF : Summable F := by
    have hc : Summable (fun z : Index => ((F z : ℝ) : ℂ)) := hsumC.congr (fun z => hFeq z)
    exact Complex.summable_ofReal.mp hc
  have hts : ∑' z : Index, gaussHat b α (ordinate (canonical z)) = ((∑' z, F z : ℝ) : ℂ) := by
    rw [tsum_congr hFeq, ← Complex.ofReal_tsum]
  rw [signedTrace, hts, Complex.ofReal_re]
  exact tsum_nonneg hFnn

/-- **A negative signed trace at one point disproves RH.**  By
`FleetPrimePoleBoundRH.zero_trace_eq_rhs` the left side equals
`poleTerm + archimedean - primeSumSym`, so this is one inequality in the primes — no norm, no
limsup, no quantifier over `b`. -/
theorem not_RH_of_signedTrace_neg {b : ℝ} (hb : 0 < b) {α : ℝ} (h : signedTrace b α < 0) :
    ¬ RiemannHypothesis :=
  fun hRH => absurd (signedTrace_nonneg_of_RH hRH hb α) (not_le.mpr h)

/-- Contrapositive form: RH forces the sign at every point. -/
theorem signedTrace_nonneg_iff_not_witness {b : ℝ} (hb : 0 < b) :
    (∀ α : ℝ, 0 ≤ signedTrace b α) ∨ ¬ RiemannHypothesis := by
  by_cases h : ∀ α : ℝ, 0 ≤ signedTrace b α
  · exact Or.inl h
  · push_neg at h
    obtain ⟨α, hα⟩ := h
    exact Or.inr (not_RH_of_signedTrace_neg hb hα)

/-- The norm criteria discard this: `FleetSimpleZeros.normTrace` is `√(b/π)` times the *norm*
of the same sum, so it cannot see the sign.  When the trace is a nonnegative real the two carry
the same information; when it is negative only `signedTrace` records it. -/
theorem normTrace_eq_abs (b α : ℝ) :
    FleetSimpleZeros.normTrace b α
      = Real.sqrt (b / π) * ‖∑' x : Index, gaussHat b α (ordinate (canonical x))‖ := rfl

/-! ## Even moments of the trace: the bridge the abstract moment test was missing -/

/-- The `k`-th moment of the zero trace about the centre `α`, scaled by the window. -/
def traceMom (b α : ℝ) (k : ℕ) : ℝ :=
  (∑' x : Index, gaussHat b α (ordinate (canonical x))
      * ((ordinate (canonical x) - (α : ℂ)) / (Real.sqrt (2 * b) : ℂ)) ^ k).re

/-- **Under RH every even moment of the trace is nonnegative.**  This is the step
`FleetHankelAtoms.offline_of_mom_even_neg` needs and does not have: that theorem is stated for
an abstract real pair `(a, x)`, so its contrapositive only says "some weight is negative".  Here
the weights and nodes are produced *from* RH, so the conclusion is about `ζ`. -/
theorem traceMom_even_nonneg_of_RH (hRH : RiemannHypothesis) {b : ℝ} (hb : 0 < b) (α : ℝ)
    (m : ℕ)
    (hsum : Summable (fun x : Index => gaussHat b α (ordinate (canonical x))
      * ((ordinate (canonical x) - (α : ℂ)) / (Real.sqrt (2 * b) : ℂ)) ^ (2 * m))) :
    0 ≤ traceMom b α (2 * m) := by
  classical
  have hs2 : (0:ℝ) < Real.sqrt (2 * b) := Real.sqrt_pos.mpr (by linarith)
  have hreal : ∀ z : Index, t z = (((t z).re : ℝ) : ℂ) := by
    intro z
    have hre : (canonical z).re = 1 / 2 := riemannHypothesis_iff.mp hRH _ z.1.2
    have him : (t z).im = 0 := by rw [t_im, hre]; norm_num
    exact Complex.ext rfl (by simpa using him)
  set F : Index → ℝ := fun z =>
    Real.sqrt (π / b) * Real.exp (-((t z).re - α) ^ 2 / (4 * b))
      * (((t z).re - α) / Real.sqrt (2 * b)) ^ (2 * m) with hF
  have hFeq : ∀ z : Index, gaussHat b α (ordinate (canonical z))
      * ((ordinate (canonical z) - (α : ℂ)) / (Real.sqrt (2 * b) : ℂ)) ^ (2 * m)
      = ((F z : ℝ) : ℂ) := by
    intro z
    have hz : ordinate (canonical z) = t z := rfl
    rw [hz, hreal z, gaussHat_real hb]
    simp only [hF]
    push_cast
    ring
  have hFnn : ∀ z, 0 ≤ F z := by
    intro z
    have he : F z = Real.sqrt (π / b) * Real.exp (-((t z).re - α) ^ 2 / (4 * b))
        * ((((t z).re - α) / Real.sqrt (2 * b)) ^ 2) ^ m := by
      rw [hF, ← pow_mul]
    rw [he]
    positivity
  have hsumC := hsum
  have hsumF : Summable F := by
    have hc : Summable (fun z : Index => ((F z : ℝ) : ℂ)) := hsumC.congr (fun z => hFeq z)
    exact Complex.summable_ofReal.mp hc
  have hts : (∑' z : Index, gaussHat b α (ordinate (canonical z))
      * ((ordinate (canonical z) - (α : ℂ)) / (Real.sqrt (2 * b) : ℂ)) ^ (2 * m))
      = ((∑' z, F z : ℝ) : ℂ) := by
    rw [tsum_congr hFeq, ← Complex.ofReal_tsum]
  rw [traceMom, hts, Complex.ofReal_re]
  exact tsum_nonneg hFnn

/-- **A negative even trace moment at one `(b, α)` disproves RH.**  The complete chain, with no
abstract `(a, x)` in it. -/
theorem not_RH_of_traceMom_even_neg {b : ℝ} (hb : 0 < b) {α : ℝ} {m : ℕ}
    (hsum : Summable (fun x : Index => gaussHat b α (ordinate (canonical x))
      * ((ordinate (canonical x) - (α : ℂ)) / (Real.sqrt (2 * b) : ℂ)) ^ (2 * m)))
    (h : traceMom b α (2 * m) < 0) : ¬ RiemannHypothesis :=
  fun hRH => absurd (traceMom_even_nonneg_of_RH hRH hb α m hsum) (not_le.mpr h)

/-- `m = 0` recovers the sign test. -/
theorem traceMom_zero (b α : ℝ) : traceMom b α 0 = signedTrace b α := by
  simp [traceMom, signedTrace]

end FleetSignedTrace
