import FleetPrimePoleBoundRH
import FleetRationalBankCriterion

/-!
# Consequences of the prime-side criterion

1. **Pure prime sum for `|α| ≥ 1/2`.** The pole term is at most `2√(π/b)` there, so the
   pole-minus-primes bound is equivalent to the same bound on the two-sided von Mangoldt sum alone.
2. **The verified range.** If every nontrivial zero with `|Im ρ| ≤ H` lies on the critical line
   (Platt–Trudgian give `H = 3·10¹²`; that is a hypothesis here, not a Lean theorem), then the
   Gaussian zero trace and `poleMinusPrimes` are `O(b^{-1/2})` at every centre `|α| + 1 ≤ H`.
3. **RH gives uniform feasibility.** Under RH, truncations of the zeros themselves satisfy every
   stage of `FleetRationalBankCriterion.Feasible b M n` with one budget
   `M = ∑ 1/(1+γ²)`. With `RH_of_uniform_feasibility` this is an equivalence.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology
open scoped Real
open GaussianTest OffLineDetection Reduction ZeroSumLimit FleetPrimePoleBoundRH

namespace FleetPrimeSideConsequences

/-! ## 1. The pure prime sum -/

/-- Two-sided von Mangoldt prime sum `S_b(α)` for the Gaussian of width `b` at `α`. -/
def primeSumSym (b α : ℝ) : ℂ :=
  GammaExplicitFormula.primeSum (gauss b α)
    + GammaExplicitFormula.primeSum (GammaExplicitFormula.reflect (gauss b α))

/-- Pole term `P_b(α) = ĝ(i/2) + ĝ(-i/2)`. -/
def poleTerm (b α : ℝ) : ℂ :=
  FleetFullLineFourier.h (gauss b α) (I / 2) + FleetFullLineFourier.h (gauss b α) (-I / 2)

lemma poleMinusPrimes_eq (b α : ℝ) :
    poleMinusPrimes b α = poleTerm b α - primeSumSym b α := by
  unfold poleMinusPrimes poleTerm primeSumSym; ring

/-- For `|α| ≥ 1/2` the pole term is at most `2√(π/b)`. -/
theorem norm_poleTerm_le_of_half_le_abs {b α : ℝ} (hb : 0 < b) (hα : (1 / 2 : ℝ) ≤ |α|) :
    ‖poleTerm b α‖ ≤ 2 * Real.sqrt (π / b) := by
  have hsq : (1 / 4 : ℝ) ≤ α ^ 2 := by
    rw [← _root_.sq_abs]; nlinarith [abs_nonneg α]
  have hexp : Real.exp (((1 / 4 : ℝ) - α ^ 2) / (4 * b)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have hp : ‖FleetFullLineFourier.h (gauss b α) (I / 2)‖ ≤ Real.sqrt (π / b) := by
    rw [FleetGaussianDictionaryMember.h_eq_gaussHat, norm_gaussHat hb]
    have him : (I / 2 : ℂ).im ^ 2 - ((I / 2 : ℂ).re - α) ^ 2 = 1 / 4 - α ^ 2 := by
      simp; ring
    rw [him]
    exact mul_le_of_le_one_right (Real.sqrt_nonneg _) hexp
  have hm : ‖FleetFullLineFourier.h (gauss b α) (-I / 2)‖ ≤ Real.sqrt (π / b) := by
    rw [FleetGaussianDictionaryMember.h_eq_gaussHat, norm_gaussHat hb]
    have him : (-I / 2 : ℂ).im ^ 2 - ((-I / 2 : ℂ).re - α) ^ 2 = 1 / 4 - α ^ 2 := by
      simp; ring
    rw [him]
    exact mul_le_of_le_one_right (Real.sqrt_nonneg _) hexp
  unfold poleTerm
  calc ‖FleetFullLineFourier.h (gauss b α) (I / 2) + FleetFullLineFourier.h (gauss b α) (-I / 2)‖
      ≤ ‖FleetFullLineFourier.h (gauss b α) (I / 2)‖ + ‖FleetFullLineFourier.h (gauss b α) (-I / 2)‖ :=
        norm_add_le _ _
    _ ≤ Real.sqrt (π / b) + Real.sqrt (π / b) := add_le_add hp hm
    _ = 2 * Real.sqrt (π / b) := by ring

/-- At a centre with `|α| ≥ 1/2` the pole term drops out of the criterion. -/
theorem poleMinusPrimes_bound_iff_primeSumSym_bound {α : ℝ} (hα : (1 / 2 : ℝ) ≤ |α|) :
    (∃ C' : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 → ‖poleMinusPrimes b α‖ ≤ Real.sqrt (π / b) * C') ↔
    (∃ C'' : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 → ‖primeSumSym b α‖ ≤ Real.sqrt (π / b) * C'') := by
  constructor
  · rintro ⟨C', hC'⟩
    refine ⟨C' + 2, fun b hb hb1 => ?_⟩
    have e : primeSumSym b α = poleTerm b α - poleMinusPrimes b α := by
      rw [poleMinusPrimes_eq]; ring
    rw [e, mul_add]
    calc ‖poleTerm b α - poleMinusPrimes b α‖
        ≤ ‖poleTerm b α‖ + ‖poleMinusPrimes b α‖ := norm_sub_le _ _
      _ ≤ 2 * Real.sqrt (π / b) + Real.sqrt (π / b) * C' :=
          add_le_add (norm_poleTerm_le_of_half_le_abs hb hα) (hC' b hb hb1)
      _ = Real.sqrt (π / b) * C' + Real.sqrt (π / b) * 2 := by ring
  · rintro ⟨C'', hC''⟩
    refine ⟨C'' + 2, fun b hb hb1 => ?_⟩
    rw [poleMinusPrimes_eq, mul_add]
    calc ‖poleTerm b α - primeSumSym b α‖
        ≤ ‖poleTerm b α‖ + ‖primeSumSym b α‖ := norm_sub_le _ _
      _ ≤ 2 * Real.sqrt (π / b) + Real.sqrt (π / b) * C'' :=
          add_le_add (norm_poleTerm_le_of_half_le_abs hb hα) (hC'' b hb hb1)
      _ = Real.sqrt (π / b) * C'' + Real.sqrt (π / b) * 2 := by ring

/-! ## 2. The verified range -/

/-- Zeros up to height `H` on the line (a hypothesis; numerically `H = 3·10¹²`, Platt–Trudgian). -/
def VerifiedTo (H : ℝ) : Prop :=
  ∀ x : Index, |(canonical x).im| ≤ H → (canonical x).re = 1 / 2

/-- **Zero trace bound in the verified range.** -/
theorem zero_trace_bound_of_verified {H : ℝ} (hV : VerifiedTo H) {α : ℝ} (hα : |α| + 1 ≤ H) :
    ∃ C' : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      ‖∑' x : Index, gaussHat b α (ordinate (canonical x))‖ ≤ Real.sqrt (π / b) * C' := by
  obtain ⟨C, hC0, hC⟩ := tail_bound α
  refine ⟨(Zfin α).card + C, fun b hb hb1 => ?_⟩
  have hsum := (GaussianTraceFormula.gaussian_formula_zeros hb α).summable
  change ‖∑' x : Index, gaussHat b α (t x)‖ ≤ _
  rw [tsum_split α (fun x => gaussHat b α (t x)) hsum]
  have hnear : ∀ x ∈ Zfin α, ‖gaussHat b α (t x)‖ ≤ Real.sqrt (π / b) := by
    intro x hx
    have hd := mem_Zfin.mp hx
    have hre : |(canonical x).im| ≤ H := by
      rw [← t_re]
      have := abs_sub_abs_le_abs_sub (t x).re α
      linarith
    have him : (t x).im = 0 := by rw [t_im, hV x hre]; norm_num
    rw [norm_gaussHat hb, him]
    apply mul_le_of_le_one_right (Real.sqrt_nonneg _)
    rw [Real.exp_le_one_iff]
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    nlinarith [sq_nonneg ((t x).re - α)]
  have h1 : ‖∑ x ∈ Zfin α, gaussHat b α (t x)‖ ≤ (Zfin α).card * Real.sqrt (π / b) := by
    refine (norm_sum_le _ _).trans ?_
    have := Finset.sum_le_sum hnear
    simpa using this
  have h2 := hC b hb hb1
  have hE : Real.exp (-3 / (16 * b)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; apply div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  have h3 : Real.sqrt (π / b) * Real.exp (-3 / (16 * b)) * C ≤ Real.sqrt (π / b) * C := by
    have := Real.sqrt_nonneg (π / b)
    have : Real.sqrt (π / b) * Real.exp (-3 / (16 * b)) ≤ Real.sqrt (π / b) :=
      mul_le_of_le_one_right (Real.sqrt_nonneg _) hE
    exact mul_le_mul_of_nonneg_right this hC0
  calc _ ≤ ‖∑ x ∈ Zfin α, gaussHat b α (t x)‖
        + ‖∑' x : Index, (Z α)ᶜ.indicator (fun x => gaussHat b α (t x)) x‖ := norm_add_le _ _
    _ ≤ (Zfin α).card * Real.sqrt (π / b) + Real.sqrt (π / b) * C := add_le_add h1 (h2.trans h3)
    _ = _ := by ring

/-- **Pole-minus-primes bound in the verified range.** -/
theorem pole_prime_bound_of_verified {H : ℝ} (hV : VerifiedTo H) {α : ℝ} (hα : |α| + 1 ≤ H) :
    ∃ C' : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      ‖poleMinusPrimes b α‖ ≤ Real.sqrt (π / b) * C' := by
  obtain ⟨K, hK, hA⟩ := norm_archimedean_le
  obtain ⟨C', hC'⟩ := zero_trace_bound_of_verified hV hα
  refine ⟨C' + ‖(1 / (2 * (Real.pi : ℂ)))‖ * K * (9 + 2 * α ^ 2), fun b hb hb1 => ?_⟩
  have e : poleMinusPrimes b α = FleetFullLineArithmetic.rhs (gauss b α)
      - FleetFullLineArithmetic.archimedean (gauss b α) := by rw [rhs_split]; ring
  rw [e, ← zero_trace_eq_rhs hb α, mul_add]
  exact (norm_sub_le _ _).trans (add_le_add (hC' b hb hb1) (hA α b hb hb1))

/-! ## 3. RH gives uniform feasibility -/

lemma ordinate_real_of_RH (hRH : RiemannHypothesis) (x : Index) :
    ordinate (canonical x) = (((t x).re : ℝ) : ℂ) := by
  have hre : (canonical x).re = 1 / 2 := riemannHypothesis_iff.mp hRH _ x.1.2
  have him : (t x).im = 0 := by rw [t_im, hre]; norm_num
  apply Complex.ext
  · simp [t]
  · simpa [t] using him

/-- **RH ⇒ uniform feasibility at every width.** The atoms are the ordinates of finitely many
zeros; the budget is `∑ₓ 1/(1+γₓ²)`. -/
theorem uniformFeasibility_of_RH (hRH : RiemannHypothesis) {b : ℝ} (hb : 0 < b) :
    FleetRationalBankCriterion.UniformFeasibility b := by
  classical
  set M : ℝ := ∑' x : Index, 1 / (1 + (t x).re ^ 2)
  refine ⟨M, fun n => ?_⟩
  have hfs : ∀ q ∈ FleetRationalBanks.bank n, ∀ᶠ s : Finset Index in atTop,
      dist (∑ x ∈ s, gaussHat b (q : ℝ) (ordinate (canonical x)))
        (FleetFullLineArithmetic.rhs (gauss b (q : ℝ))) < 1 / ((n : ℝ) + 1) := by
    intro q _
    have hs := GaussianTraceFormula.gaussian_formula_zeros hb (q : ℝ)
    rw [← rhs_gauss_eq hb] at hs
    exact hs (Metric.ball_mem_nhds _ (by positivity))
  obtain ⟨s, hs⟩ := ((Filter.eventually_all_finset _).mpr hfs).exists
  refine ⟨s.card, fun i => (t (s.equivFin.symm i)).re, ?_, ?_⟩
  · have e : (∑ i : Fin s.card, (1 + (t (s.equivFin.symm i)).re ^ 2)⁻¹)
        = ∑ x ∈ s, 1 / (1 + (t x).re ^ 2) := by
      rw [Equiv.sum_comp s.equivFin.symm (fun x : s => (1 + (t x).re ^ 2)⁻¹)]
      rw [Finset.sum_coe_sort s (fun x => (1 + (t x).re ^ 2)⁻¹)]
      simp [one_div]
    rw [e]
    exact Summable.sum_le_tsum s (fun x _ => by positivity) summable_inv_one_add_sq_re
  · intro q hq
    have e : (∑ i : Fin s.card, FleetFullLineFourier.h (gauss b (q : ℝ))
          (((t (s.equivFin.symm i)).re : ℝ) : ℂ))
        = ∑ x ∈ s, gaussHat b (q : ℝ) (ordinate (canonical x)) := by
      rw [Equiv.sum_comp s.equivFin.symm
        (fun x : s => FleetFullLineFourier.h (gauss b (q : ℝ)) (((t x).re : ℝ) : ℂ))]
      rw [Finset.sum_coe_sort s (fun x => FleetFullLineFourier.h (gauss b (q : ℝ)) (((t x).re : ℝ) : ℂ))]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [ordinate_real_of_RH hRH x]
      rfl
    rw [e, ← dist_eq_norm]
    exact (hs q hq).le

/-- **RH iff uniform feasibility**, at any fixed width `b > 0`. -/
theorem RH_iff_uniformFeasibility {b : ℝ} (hb : 0 < b) :
    RiemannHypothesis ↔ FleetRationalBankCriterion.UniformFeasibility b :=
  ⟨fun h => uniformFeasibility_of_RH h hb, FleetRationalBankCriterion.RH_of_uniform_feasibility hb⟩

end FleetPrimeSideConsequences
