import FleetFiniteIntervalCertificate

/-!
# Exact rational mass check for the stage-100 candidate

The coordinates below are copied exactly from the `positive_rational_positions`
field of `tools/results/gaussian_bank_arithmetic_stage100_20261001.json`.
They are rational candidate coordinates, with no assertion that they are exact
zeta-zero ordinates. This module proves only the weighted-mass bound for the
66 paired unit atoms. The external analytic residual enclosures are not imported
as Lean proofs, and no `Feasible` theorem is asserted here.
-/

noncomputable section
namespace FleetStage100Witness

/-- The certificate's 33 exact positive rational coordinates, viewed in ℝ. -/
def positive : Fin 33 → ℝ := ![
  2826945028347/200000000000,
  5255509909693/250000000000,
  12505428790073/500000000000,
  1521243806293/50000000000,
  32935061587739/1000000000000,
  18793089079413/500000000000,
  40918719012147/1000000000000,
  8665414656183/200000000000,
  48005150881167/1000000000000,
  6221729059709/125000000000,
  26485160738857/500000000000,
  56446247697063/1000000000000,
  29673522001301/500000000000,
  6083177852461/100000000000,
  32556272024041/500000000000,
  33539905264747/500000000000,
  34773200855587/500000000000,
  36033578837241/500000000000,
  18926172674771/250000000000,
  617158720551/8000000000,
  79337375020249/1000000000000,
  41455190427043/500000000000,
  84735492980517/1000000000000,
  139880439381/1600000000,
  44404555603817/500000000000,
  46245949635279/500000000000,
  2366283601013/25000000000,
  19174126845649/200000000000,
  49415597109097/500000000000,
  101317851005731/1000000000000,
  103725538040477/1000000000000,
  52723311526233/500000000000,
  53584305580039/500000000000]

/-- The 66 unit atoms at the positive coordinates and their negatives. -/
def coordinates : Fin 66 → ℝ := Fin.append positive (fun i => -positive i)

/-- Kernel-checked rational arithmetic proves only the mass budget 0.05. -/
theorem mass_le_one_twentieth :
    (∑ i, (1+(coordinates i)^2)⁻¹) ≤ (1/20 : ℝ) := by
  change (∑ i : Fin (33+33), (1+(coordinates i)^2)⁻¹) ≤ (1/20 : ℝ)
  rw [Fin.sum_univ_add]
  simp only [coordinates, Fin.append_left, Fin.append_right, neg_sq]
  norm_num [positive, Fin.sum_univ_succ]

end FleetStage100Witness
