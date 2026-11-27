import FleetRationalBankCriterion

/-!
# Conditional finite Gaussian certificates

These lemmas transfer proved scalar or rectangular enclosures of the exact
weighted mass and complex Gaussian residuals to finite-stage feasibility.
The analytic enclosures remain hypotheses: an external interval calculation,
including an Arb output file, is not itself a proof of those hypotheses in Lean.
No finite-stage arithmetic residual enclosure or all-stage feasibility claim is
asserted here.

The final examples check only the weighted masses of explicit rational decimal
coordinates. They do not assert that these coordinates are zeta-zero ordinates,
or that either list satisfies any Gaussian residual constraint.
-/

noncomputable section
namespace FleetFiniteIntervalCertificate
open GaussianTest FleetRationalBankCriterion

/-- The exact complex residual required by the rational-bank criterion. -/
def residual {N : ℕ} (b : ℝ) (x : Fin N → ℝ) (q : ℚ) : ℂ :=
  (∑ i : Fin N, FleetFullLineFourier.h (gauss b (q : ℝ)) (x i)) -
    FleetFullLineArithmetic.rhs (gauss b (q : ℝ))

/-- Rational upper bounds imply feasibility once their enclosures of the exact
analytic quantities are proved. The enclosure hypotheses are not discharged by
this theorem or by an unchecked external numerical certificate. -/
theorem feasible_of_scalar_enclosures {b M : ℝ} {n N : ℕ}
    (x : Fin N → ℝ) (massUpper : ℚ) (errorUpper : ℚ → ℚ)
    (hmass : (∑ i, (1+(x i)^2)⁻¹) ≤ (massUpper : ℝ))
    (herror : ∀ q ∈ FleetRationalBanks.bank n,
      ‖residual b x q‖ ≤ (errorUpper q : ℝ))
    (hmassBudget : (massUpper : ℝ) ≤ M)
    (herrorBudget : ∀ q ∈ FleetRationalBanks.bank n,
      (errorUpper q : ℝ) ≤ 1/((n : ℝ)+1)) : Feasible b M n := by
  exact ⟨N, x, hmass.trans hmassBudget,
    fun q hq => (herror q hq).trans (herrorBudget q hq)⟩

/-- A rectangular complex enclosure gives this conservative norm upper bound.
In particular, no assumption that the imaginary part vanishes is needed. -/
theorem norm_le_box {z : ℂ} {lR uR lI uI : ℝ}
    (hr : lR ≤ z.re ∧ z.re ≤ uR)
    (hi : lI ≤ z.im ∧ z.im ≤ uI) :
    ‖z‖ ≤ max |lR| |uR| + max |lI| |uI| := by
  have hre : |z.re| ≤ max |lR| |uR| := abs_le.mpr ⟨by
    have h := (le_max_left |lR| |uR|)
    linarith [neg_abs_le lR, hr.1], by
    exact hr.2.trans ((le_abs_self uR).trans (le_max_right _ _))⟩
  have him : |z.im| ≤ max |lI| |uI| := abs_le.mpr ⟨by
    have h := (le_max_left |lI| |uI|)
    linarith [neg_abs_le lI, hi.1], by
    exact hi.2.trans ((le_abs_self uI).trans (le_max_right _ _))⟩
  exact (Complex.norm_le_abs_re_add_abs_im z).trans (add_le_add hre him)

/-- Rational rectangles for every exact complex residual imply feasibility if
their norm bounds fit the stage tolerance. Proving `hbox` remains the analytic
certification obligation; this theorem does not import or validate Arb output. -/
theorem feasible_of_rectangular_enclosures {b M : ℝ} {n N : ℕ}
    (x : Fin N → ℝ) (massUpper : ℚ) (loRe hiRe loIm hiIm : ℚ → ℚ)
    (hmass : (∑ i, (1+(x i)^2)⁻¹) ≤ (massUpper : ℝ))
    (hbox : ∀ q ∈ FleetRationalBanks.bank n,
      ((loRe q : ℝ) ≤ (residual b x q).re ∧ (residual b x q).re ≤ (hiRe q : ℝ)) ∧
      ((loIm q : ℝ) ≤ (residual b x q).im ∧ (residual b x q).im ≤ (hiIm q : ℝ)))
    (hmassBudget : (massUpper : ℝ) ≤ M)
    (herrorBudget : ∀ q ∈ FleetRationalBanks.bank n,
      max |(loRe q : ℝ)| |(hiRe q : ℝ)| + max |(loIm q : ℝ)| |(hiIm q : ℝ)| ≤
        1/((n : ℝ)+1)) : Feasible b M n := by
  refine ⟨N,x,hmass.trans hmassBudget,?_⟩
  intro q hq
  exact (norm_le_box (hbox q hq).1 (hbox q hq).2).trans (herrorBudget q hq)

/-- A certified stage also certifies every earlier stage with the same mass
budget: its bank is larger and its residual tolerance is smaller. -/
theorem feasible_mono_stage {b M : ℝ} {m n : ℕ}
    (hmn : m ≤ n) (hf : Feasible b M n) : Feasible b M m := by
  obtain ⟨N,x,hm,he⟩ := hf
  refine ⟨N,x,hm,?_⟩
  intro q hq
  apply (he q (FleetRationalBanks.monotone_bank hmn hq)).trans
  apply one_div_le_one_div_of_le
  · positivity
  · exact_mod_cast Nat.add_le_add_right hmn 1

/-- An elementary denominator comparison for a real coordinate and a parameter
strictly between zero and one. This lemma asserts no infinite zero-sum identity
and does not derive a uniform mass bound for a family of zero ordinates. -/
theorem weighted_mass_le_strip_pair {beta : ℝ} (hbeta : 0 < beta)
    (hbeta1 : beta < 1) (t : ℝ) :
    1/(1+t^2) ≤ beta/(beta^2+t^2)+(1-beta)/((1-beta)^2+t^2) := by
  have hone : 0 < 1-beta := sub_pos.mpr hbeta1
  have hleft : 0 < beta^2+t^2 := by positivity
  have hright : 0 < (1-beta)^2+t^2 := by positivity
  have hlower : beta^2+t^2 ≤ 1+t^2 := by nlinarith
  have hrupper : (1-beta)^2+t^2 ≤ 1+t^2 := by nlinarith
  calc
    1/(1+t^2) = beta/(1+t^2)+(1-beta)/(1+t^2) := by ring
    _ ≤ beta/(beta^2+t^2)+(1-beta)/((1-beta)^2+t^2) :=
      add_le_add (div_le_div_of_nonneg_left hbeta.le hleft hlower)
        (div_le_div_of_nonneg_left (by linarith) hright hrupper)

/-- Eight unit atoms at the exact rational coordinates
±14.134725142, ±21.022039639, ±25.010857580, and ±30.424876126.
The coordinates are terminating decimals, not asserted exact zero heights. -/
def fourPairs : Fin 8 → ℝ := ![
  -(14134725142/1000000000), -(21022039639/1000000000),
  -(25010857580/1000000000), -(30424876126/1000000000),
  14134725142/1000000000, 21022039639/1000000000,
  25010857580/1000000000, 30424876126/1000000000]

/-- Ten unit atoms obtained by adding the exact rational pair ±32.935061588
to the four pairs above. No zero-location or residual claim is attached. -/
def fivePairs : Fin 10 → ℝ := ![
  -(14134725142/1000000000), -(21022039639/1000000000),
  -(25010857580/1000000000), -(30424876126/1000000000),
  -(32935061588/1000000000),
  14134725142/1000000000, 21022039639/1000000000,
  25010857580/1000000000, 30424876126/1000000000,
  32935061588/1000000000]

/-- The four-pair rational list satisfies the mass budget 0.02. -/
theorem fourPairs_mass_le_002 :
    (∑ i, (1+(fourPairs i)^2)⁻¹) ≤ (1/50 : ℝ) := by
  norm_num [fourPairs, Fin.sum_univ_succ]

/-- The five-pair rational list exceeds 0.02. This rejects this particular list
under that budget, not all candidate lists for any stage. -/
theorem fivePairs_mass_gt_002 :
    (1/50 : ℝ) < ∑ i, (1+(fivePairs i)^2)⁻¹ := by
  norm_num [fivePairs, Fin.sum_univ_succ]

/-- The five-pair rational list satisfies the larger mass budget 0.05. -/
theorem fivePairs_mass_le_005 :
    (∑ i, (1+(fivePairs i)^2)⁻¹) ≤ (1/20 : ℝ) := by
  norm_num [fivePairs, Fin.sum_univ_succ]

end FleetFiniteIntervalCertificate
