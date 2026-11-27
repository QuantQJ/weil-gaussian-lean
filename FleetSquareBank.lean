import FleetPrimeTarget

/-!
# Square Gaussian banks: RH makes every bank Hankel form nonnegative

Equally spaced centres `q_k = q₀ + k h`. With `ψ_i(t) = e^{-(t - (q₀ + 2 i h))²/(8b)}`, completing the square gives
`ψ_i ψ_j = W_{ij} e^{-(t - q_{i+j})²/(4b)}`, `W_{ij} = e^{-(i-j)² h²/(4b)}`, so the bank
`φ_a = √(π/b) Σ_{i,j} a_i a_j W_{ij} e^{-(t - q_{i+j})²/(4b)} = √(π/b) (Σ a_i ψ_i)²` is nonnegative by construction.

`bank_form_nonneg_of_RH` : under RH, for every `b > 0`, `q₀`, `h`, `n` and real `a`,
`Σ_{i,j ≤ n} a_i a_j W_{ij} · Re rhs(gauss b q_{i+j}) ≥ 0` (the arithmetic side `rhs`, no zeros in the statement).
`not_RH_of_bank_form_neg` : one negative value of this finite quadratic form disproves RH. The shifted family
(`H⁽¹⁾`) is the same statement with `q₀ + h`. For equally spaced banks these forms describe all nonnegative banks
(Lukács' theorem on `[0,∞)`; not formalized here).
-/

set_option autoImplicit false
noncomputable section
open Complex Finset
open scoped Real
open GaussianTest OffLineDetection Reduction ZeroSumLimit FleetPrimePoleBoundRH

namespace FleetSquareBank

/-- `W_{ij} = e^{-(i-j)² h²/(4b)}`. -/
def W (b h : ℝ) (i j : ℕ) : ℝ := Real.exp (-((i : ℝ) - j) ^ 2 * h ^ 2 / (4 * b))

/-- The bank's quadratic form on the arithmetic side. -/
def bankForm (b q₀ h : ℝ) (n : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1),
    a i * a j * W b h i j * (FleetFullLineArithmetic.rhs (gauss b (q₀ + ((i : ℝ) + j) * h))).re

lemma psi_mul {b : ℝ} (hb : 0 < b) (h q₀ t : ℝ) (i j : ℕ) :
    Real.exp (-(t - (q₀ + 2 * i * h)) ^ 2 / (8 * b)) * Real.exp (-(t - (q₀ + 2 * j * h)) ^ 2 / (8 * b))
      = W b h i j * Real.exp (-(t - (q₀ + ((i : ℝ) + j) * h)) ^ 2 / (4 * b)) := by
  unfold W
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  field_simp
  ring

/-- The bank is a square: `Σ a_i a_j W_{ij} term(q_{i+j}, t) = √(π/b) (Σ a_i ψ_i(t))²`. -/
lemma bank_eq_square {b : ℝ} (hb : 0 < b) (q₀ h t : ℝ) (n : ℕ) (a : ℕ → ℝ) :
    ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1),
        a i * a j * W b h i j * RealSideBound.term b (q₀ + ((i : ℝ) + j) * h) t
      = Real.sqrt (π / b) *
        (∑ i ∈ range (n + 1), a i * Real.exp (-(t - (q₀ + 2 * i * h)) ^ 2 / (8 * b))) ^ 2 := by
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  unfold RealSideBound.term
  have hp := psi_mul hb h q₀ t i j
  have e : (t - (q₀ + ((i : ℝ) + j) * h)) ^ 2 = ((q₀ + ((i : ℝ) + j) * h) - t) ^ 2 := by ring
  rw [show (t - (q₀ + ((i : ℝ) + j) * h)) ^ 2 = (t - (q₀ + ((i : ℝ) + j) * h)) ^ 2 from rfl] at hp
  calc a i * a j * W b h i j * (Real.sqrt (π / b) * Real.exp (-(t - (q₀ + ((i : ℝ) + j) * h)) ^ 2 / (4 * b)))
      = Real.sqrt (π / b) * (a i * a j) * (W b h i j * Real.exp (-(t - (q₀ + ((i : ℝ) + j) * h)) ^ 2 / (4 * b))) := by ring
    _ = _ := by rw [← hp]; ring

/-- Under RH the arithmetic side of a Gaussian is the real zero sum `Σ term`. -/
lemma rhs_re_of_RH (hRH : RiemannHypothesis) {b : ℝ} (hb : 0 < b) (q : ℝ) :
    Summable (fun x : Index => RealSideBound.term b q (t x).re) ∧
    (FleetFullLineArithmetic.rhs (gauss b q)).re = ∑' x : Index, RealSideBound.term b q (t x).re := by
  have hS := (GaussianTraceFormula.gaussian_formula_zeros hb q).summable
  have he : (fun x : Index => gaussHat b q (ordinate (canonical x)))
      = fun x => ((RealSideBound.term b q (t x).re : ℝ) : ℂ) := by
    funext x
    rw [FleetPrimeSideConsequences.ordinate_real_of_RH hRH x, gaussHat_real hb]
    rfl
  rw [he] at hS
  have hSr : Summable (fun x : Index => RealSideBound.term b q (t x).re) := Complex.summable_ofReal.mp hS
  refine ⟨hSr, ?_⟩
  rw [← zero_trace_eq_rhs hb q, he, ← Complex.ofReal_tsum, Complex.ofReal_re]

/-- **RH ⇒ every square-bank Hankel form is nonnegative.** -/
theorem bank_form_nonneg_of_RH (hRH : RiemannHypothesis) {b : ℝ} (hb : 0 < b) (q₀ h : ℝ) (n : ℕ)
    (a : ℕ → ℝ) : 0 ≤ bankForm b q₀ h n a := by
  unfold bankForm
  have key : ∀ i ∈ range (n + 1), ∀ j ∈ range (n + 1),
      a i * a j * W b h i j * (FleetFullLineArithmetic.rhs (gauss b (q₀ + ((i : ℝ) + j) * h))).re
        = ∑' x : Index, a i * a j * W b h i j * RealSideBound.term b (q₀ + ((i : ℝ) + j) * h) (t x).re := by
    intro i _ j _
    rw [(rhs_re_of_RH hRH hb _).2, tsum_mul_left]
  rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => key i hi j hj))]
  have hsum : ∀ i j : ℕ, Summable (fun x : Index =>
      a i * a j * W b h i j * RealSideBound.term b (q₀ + ((i : ℝ) + j) * h) (t x).re) :=
    fun i j => ((rhs_re_of_RH hRH hb _).1).mul_left _
  simp_rw [← Summable.tsum_finsetSum (fun j _ => hsum _ j)]
  rw [← Summable.tsum_finsetSum (fun i _ => summable_sum (fun j _ => hsum i j))]
  refine tsum_nonneg (fun x => ?_)
  rw [bank_eq_square hb q₀ h (t x).re n a]
  positivity

/-- **A single negative bank value disproves RH.** -/
theorem not_RH_of_bank_form_neg {b : ℝ} (hb : 0 < b) {q₀ h : ℝ} {n : ℕ} {a : ℕ → ℝ}
    (hneg : bankForm b q₀ h n a < 0) : ¬ RiemannHypothesis :=
  fun hRH => (not_le.mpr hneg) (bank_form_nonneg_of_RH hRH hb q₀ h n a)

end FleetSquareBank
