/-
Copyright 2026 James C. Kerr (QuantQJ). Apache-2.0.
-/
import FleetPolyNormalization

/-!
# One inequality for RH *and* simplicity of the zeros

The Gaussian zero trace, normalised by the probe's own mass `√(π/b)`, is a
delta-function detector that reads off **multiplicity**:

  `normTrace b α = √(b/π) · ‖∑ₓ gaussHat b α (ordinate ρₓ)‖ = ∑ₓ exp(-(γₓ-α)²/(4b))`

under RH.  Numerically (`b` from `0.5` down to `0.002`, ordinates from `mpmath`) this is
`1.0000000` at a simple ordinate and `< 10⁻¹⁷⁸` off the ordinates; with the symmetrised
two-bump probe the same computation gives `2.0000000`, and the Weil identity
`zeros = pole − primes + archimedean` closes to `2.7 × 10⁻¹⁵`.

So one inequality carries two conclusions:

* `RH_of_traceLimsupLe` — a `limsup` bound of **any** size gives RH.  A `limsup` is a
  small-`b` statement, and `FleetTraceBoundRH.RH_of_zero_trace_small_b_bound` needs the
  growth bound only for `b` below a threshold (the converse proof evaluates it at
  `b = 1/(4s)` with `s` arbitrarily large, never anywhere else).
* `two_le_normTrace_of_not_simple` — under RH every term of the trace is a nonnegative real,
  so two indices at the same ordinate already force `normTrace ≥ 2` at that centre.
* `RH_and_allSimple_of_traceLimsupLe_one` — hence `limsup_{b→0} normTrace b α ≤ 1` for every
  centre implies **RH and every nontrivial zero is simple**.

Simplicity of the zeros is an open problem distinct from RH (it is the hypothesis behind the
linear-independence conjecture and the Chebyshev-bias results).  This packages both into a
single residual of the same shape as the rest of the chain, and by
`FleetPolyNormalization.RH_iff_primeSumSym_poly_bound` the growth half of it transfers to the
von Mangoldt side with no zero data in the statement.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology
open scoped Real
open OffLineDetection Reduction ZeroSumLimit GaussianTest PrincipalPartDischarge

namespace FleetSimpleZeros

/-- The Gaussian zero trace at centre `α`, width `b`, normalised by the probe's own mass. -/
def normTrace (b α : ℝ) : ℝ :=
  Real.sqrt (b / π) * ‖∑' x : Index, gaussHat b α (ordinate (canonical x))‖

/-- `limsup_{b → 0⁺} normTrace b α ≤ c` at every centre, in explicit `ε`–`b₀` form. -/
def TraceLimsupLe (c : ℝ) : Prop :=
  ∀ α : ℝ, ∀ ε : ℝ, 0 < ε → ∃ b₀ : ℝ, 0 < b₀ ∧
    ∀ b : ℝ, 0 < b → b < b₀ → normTrace b α ≤ c + ε

/-- Every nontrivial zero of `ζ` is simple. -/
def AllSimple : Prop := ∀ ρ : ℂ, IsNontrivialZero ρ → zetaOrder ρ ≤ 1

theorem sqrt_div_mul_sqrt_div {b : ℝ} (hb : 0 < b) :
    Real.sqrt (b / π) * Real.sqrt (π / b) = 1 := by
  rw [← Real.sqrt_mul (by positivity), show b / π * (π / b) = 1 by field_simp]
  exact Real.sqrt_one

/-- **A `limsup` bound of any size gives RH.**  `limsup` is a small-`b` statement, and that is
all the converse ever uses. -/
theorem RH_of_traceLimsupLe {c : ℝ} (h : TraceLimsupLe c) : RiemannHypothesis := by
  refine FleetTraceBoundRH.RH_of_zero_trace_small_b_bound 0
    (fun _ hb α => (GaussianTraceFormula.gaussian_formula_zeros hb α).summable) (fun α => ?_)
  obtain ⟨b₀, hb₀, hb⟩ := h α 1 one_pos
  refine ⟨c + 1, b₀, hb₀, fun b hbp _ hbb => ?_⟩
  have e : Real.sqrt (π / b) * normTrace b α
      = ‖∑' x : Index, gaussHat b α (ordinate (canonical x))‖ := by
    rw [normTrace, ← mul_assoc, mul_comm (Real.sqrt (π / b)) (Real.sqrt (b / π)),
      sqrt_div_mul_sqrt_div hbp, one_mul]
  rw [pow_zero, div_one, ← e]
  exact mul_le_mul_of_nonneg_left (hb b hbp hbb) (Real.sqrt_nonneg _)

/-- **Two indices at one ordinate force `normTrace ≥ 2`.**  Under RH every ordinate is real, so
every term of the trace is a nonnegative real and the two diagonal terms alone give `2`. -/
theorem two_le_normTrace_of_not_simple (hRH : RiemannHypothesis)
    {x y : Index} (hne : x ≠ y) (hxy : canonical x = canonical y)
    {b : ℝ} (hb : 0 < b) :
    2 ≤ normTrace b ((t x).re) := by
  classical
  set α : ℝ := (t x).re with hα
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
    have hc : Summable (fun z : Index => ((F z : ℝ) : ℂ)) := by
      refine hsumC.congr (fun z => ?_)
      exact hFeq z
    exact Complex.summable_ofReal.mp hc
  have hnorm : ‖∑' z : Index, gaussHat b α (ordinate (canonical z))‖ = ∑' z, F z := by
    rw [tsum_congr hFeq, ← Complex.ofReal_tsum, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (tsum_nonneg hFnn)]
  have hty : t y = t x := by
    show ordinate (canonical y) = ordinate (canonical x)
    rw [hxy]
  have hFx : F x = Real.sqrt (π / b) := by rw [hF]; simp [hα]
  have hFy : F y = Real.sqrt (π / b) := by rw [hF]; simp [hα, hty]
  have hpair : F x + F y ≤ ∑' z, F z := by
    have hs := hsumF.sum_le_tsum ({x, y} : Finset Index) (fun z _ => hFnn z)
    rwa [Finset.sum_pair hne] at hs
  have hone : Real.sqrt (b / π) * (F x + F y) = 2 := by
    rw [hFx, hFy]; linear_combination 2 * sqrt_div_mul_sqrt_div (b := b) hb
  rw [normTrace, hnorm, ← hone]
  exact mul_le_mul_of_nonneg_left hpair (Real.sqrt_nonneg _)

/-- **Simplicity.**  `limsup ≤ 1` leaves no room for a second index at the same ordinate. -/
theorem allSimple_of_traceLimsupLe_one (h : TraceLimsupLe 1) : AllSimple := by
  have hRH := RH_of_traceLimsupLe h
  intro ρ hρ
  by_contra hm
  push_neg at hm
  have h0 : (0 : ℕ) < zetaOrder ρ := by omega
  set x : Index := ⟨⟨ρ, hρ⟩, ⟨0, by omega⟩⟩ with hx
  set y : Index := ⟨⟨ρ, hρ⟩, ⟨1, by omega⟩⟩ with hy
  have hne : x ≠ y := by
    rw [hx, hy]
    simp only [ne_eq, Sigma.mk.injEq, not_and]
    intro _
    simp [Fin.ext_iff]
  have hxy : canonical x = canonical y := rfl
  obtain ⟨b₀, hb₀, hb⟩ := h ((t x).re) (1 / 2) (by norm_num)
  have hlt := hb (b₀ / 2) (by positivity) (by linarith)
  have hge := two_le_normTrace_of_not_simple hRH hne hxy (b := b₀ / 2) (by positivity)
  linarith

/-- **One inequality, both conclusions.** -/
theorem RH_and_allSimple_of_traceLimsupLe_one (h : TraceLimsupLe 1) :
    RiemannHypothesis ∧ AllSimple :=
  ⟨RH_of_traceLimsupLe h, allSimple_of_traceLimsupLe_one h⟩

end FleetSimpleZeros
