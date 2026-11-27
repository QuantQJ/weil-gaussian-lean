import FleetFiniteIntervalCertificate

/-!
# Exact rational mass check for the stage-26 candidate

The coordinates below are copied exactly from the `positive_rational_positions`
field of `tools/results/gaussian_bank_reference_stage26_20261001.json`.
They are rational candidate coordinates (rational approximations to the first
three zeta-zero ordinates), with no assertion that they are exact zeta-zero
ordinates.

Stage 26 is the smaller rung of the feasibility ladder: `|bank 26| = 847`
rational centres against `|bank 100| = 12175`, and 6 paired atoms against 66.
By the evenness of both the probe sum and the arithmetic target in the rational
centre, only the `424` distinct absolute centres need checking; the certificate
JSON records `424` passes, `0` failures, `0` inconclusive.

This module proves only the weighted-mass bound for the 6 paired unit atoms —
the `hmass` hypothesis of
`FleetFiniteIntervalCertificate.feasible_of_rectangular_enclosures`.

**Not proved here.** The residual box hypothesis `hbox` of that theorem. The
JSON's enclosures are outward-rounded Arb intervals at 96 bits with analytic
tails (`prime_power_cutoff = 1000`, `u_cutoff = 12`), and it records
`"lean_proof_term": false` itself. Re-deriving them inside Lean is what
`FleetGaussianPrimeTailCertificate`, `FleetArchimedeanTailCertificate`,
`FleetDigammaIntervalCertificate` and `FleetSharpMidpointCertificate` exist for.
No `Feasible` theorem is asserted here.
-/

set_option maxRecDepth 100000

noncomputable section
namespace FleetStage26Witness

/-- The certificate's 3 exact positive rational coordinates, viewed in `ℝ`. -/
def positive : Fin 3 → ℝ := ![
  (7067362571 / 500000000 : ℝ),
  (21022039639 / 1000000000 : ℝ),
  (1250542879 / 50000000 : ℝ)]

/-- The 6 paired atoms: each positive coordinate together with its negative. -/
def coordinates : Fin 6 → ℝ := Fin.append positive (fun i => -positive i)

/-- **The mass bound.** `∑ (1 + xᵢ²)⁻¹ ≤ 1/50` over the 6 paired atoms.
This is the `hmass` input of `feasible_of_rectangular_enclosures`, with
`massUpper = 1/50`. The certificate's `exact_paired_mass` is
`0.01766817…`, inside the `1/50 = 0.02` budget. -/
theorem mass_le_one_fiftieth :
    (∑ i, (1 + (coordinates i) ^ 2)⁻¹) ≤ (1 / 50 : ℝ) := by
  change (∑ i : Fin (3 + 3), (1 + (coordinates i) ^ 2)⁻¹) ≤ (1 / 50 : ℝ)
  rw [Fin.sum_univ_add]
  simp only [coordinates, Fin.append_left, Fin.append_right, neg_sq]
  norm_num [positive, Fin.sum_univ_succ]

/-! ## The margin, as rational arithmetic -/

/-- The certificate's own worst-case box norm (`max_residual_upper`, attained at centre 26)
fits inside the uniform bound `1/70` used below. -/
theorem certificate_max_residual_le_uniform :
    (16830700048660568399138285019 / 1267650600228229401496703205376 : ℚ) ≤ 1 / 70 := by
  norm_num

/-- The uniform bound sits inside the stage-26 tolerance `1/(26+1)`. -/
theorem uniform_within_tolerance : (1 / 70 : ℚ) ≤ 1 / 27 := by norm_num

/-! ## Stage 26 reduced to a single analytic hypothesis -/

/-- **`Feasible 1 (1/50) 26` from one hypothesis.**  Every arithmetic side condition of
`feasible_of_scalar_enclosures` is discharged here — the mass bound, the mass budget, and the
error budget.  What remains is exactly one analytic statement: that the residual at each of the
`847` rational centres of `bank 26` has norm at most `1/70`.

The certificate JSON asserts this with outward-rounded Arb enclosures (`424` distinct absolute
centres by evenness, `424` pass / `0` fail), whose worst box norm is `0.01327708…` — inside
`1/70 = 0.01428571…` by `certificate_max_residual_le_uniform`, itself inside the tolerance
`1/27 = 0.03703703…`.  Those enclosures are **not** Lean proofs; this theorem is what they
would feed. -/
theorem feasible_of_uniform_residual_bound
    (hres : ∀ q ∈ FleetRationalBanks.bank 26,
      ‖FleetFiniteIntervalCertificate.residual 1 coordinates q‖ ≤ (1 / 70 : ℝ)) :
    FleetRationalBankCriterion.Feasible 1 (1 / 50) 26 := by
  refine FleetFiniteIntervalCertificate.feasible_of_scalar_enclosures
    coordinates (1 / 50) (fun _ => 1 / 70) ?_ ?_ ?_ ?_
  · have h := mass_le_one_fiftieth
    push_cast
    exact h
  · intro q hq
    have h := hres q hq
    push_cast
    exact h
  · push_cast
    norm_num
  · intro q _
    push_cast
    norm_num

end FleetStage26Witness

end

#print axioms FleetStage26Witness.mass_le_one_fiftieth
#print axioms FleetStage26Witness.certificate_max_residual_le_uniform
#print axioms FleetStage26Witness.feasible_of_uniform_residual_bound
