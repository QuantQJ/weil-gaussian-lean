/-
OAIExponentTrace: parametric checks on where the exponent 7/8 comes from in the
vendored OpenAI proof (OAI/NumberTheory/DirichletL). Nothing in OAI/ is changed.

What is proved here:
* `hasCubicExponent_of_one_le`: as defined in `CubicSieve/Growth.lean`,
  `HasCubicExponent ξ` already holds for every `ξ ≥ 1` (from `sieveNorm_sharp`),
  so improving `ξ` below 4/3 adds nothing; only removing the `(MN)^(2/3)` term
  would change the sieve input.
* `marked_second_of_first`: the second inverse-marked capacity condition
  `2r + 8W < 3` (Hecke/DetectorRawFiber.lean:76) follows from the first
  `r + 2W < 1` whenever `r ≥ 1/2`; the row count only uses it for `r ≥ 23/37`.
* `kappaPlain_eq`: the plain-moment capacity `3/4 + 2Δ` with `Δ = β - 7/8` is `2β - 1`.
* `signal_exponent_split`, `relative_at_cut`: the arithmetic of 11/16, 3/16, 13/16.
* `gen*` lemmas: the row-count crossing algebra with a general plain-capacity
  coefficient `c` (the code is the case `c = 4/9 = 1/(3·(3/4))`).
* `balancedExponent_at_witness`: the balanced endpoint exponent equals
  `-49/214704` at `(δ, y) = (79/204, 0)`, so the slack in the bottleneck
  inequality is at most `49/214704` there (the code uses `49/440640`).
-/
import OAI.NumberTheory.DirichletL.CubicSieve.Sharp
import OAI.NumberTheory.DirichletL.Endpoint
import OAI.NumberTheory.DirichletL.Detector.CentralExponent

namespace OAIExponentTrace

open OAI.SevenEighths

/-- `HasCubicExponent ξ` holds for every `ξ ≥ 1`: the sharp bound
`M + N + (MN)^(2/3)` dominates `M + N^ξ + (MN)^(2/3)` from below. -/
theorem hasCubicExponent_of_one_le {ξ : ℝ} (hξ : 1 ≤ ξ) :
    CubicSieve.HasCubicExponent ξ := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := CubicSieve.sieveNorm_sharp ε hε
  refine ⟨C, hC, ?_⟩
  intro M N hM hN
  have hN1 : N ≤ N ^ ξ := by
    calc N = N ^ (1 : ℝ) := (Real.rpow_one N).symm
      _ ≤ N ^ ξ := Real.rpow_le_rpow_of_exponent_le hN hξ
  have hpos : 0 ≤ C * (M * N) ^ ε :=
    mul_nonneg hC.le (Real.rpow_nonneg (by nlinarith) _)
  calc CubicSieve.sieveNorm M N ≤ C * (M * N) ^ ε * (M + N + (M * N) ^ (2 / 3 : ℝ)) :=
        hb M N hM hN
    _ ≤ C * (M * N) ^ ε * (M + N ^ ξ + (M * N) ^ (2 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) hpos

/-- In particular the exponent `ξ = 1` is already a theorem for this definition. -/
theorem hasCubicExponent_one : CubicSieve.HasCubicExponent 1 :=
  hasCubicExponent_of_one_le le_rfl

/-- The second inverse-marked capacity condition is implied by the first for `r ≥ 1/2`,
with slack `2r - 1`. -/
theorem marked_second_of_first {r W : ℝ} (hr : 1 / 2 ≤ r) (h : r + 2 * W < 1) :
    2 * r + 8 * W < 4 - 2 * r ∧ 2 * r + 8 * W < 3 := by
  constructor <;> linarith

/-- The plain capacity coefficient `kappaPlain = 3/4 + 2Δ`, with `Δ = β - 7/8`, is `2β - 1`. -/
theorem kappaPlain_eq (β : ℝ) : (3 / 4 : ℝ) + 2 * (β - 7 / 8) = 2 * β - 1 := by ring

/-- Signal normalisation (PrincipalSignalComparison.lean:420): contour centre `5/6`,
source length `17/48` (cube root) and slot total `1/6`. -/
theorem signal_exponent_split :
    (5 / 6 : ℝ) - (17 / 48) / 3 - (1 / 6) / 6 = 11 / 16 ∧
      (11 / 16 : ℝ) + 3 / 16 = 7 / 8 ∧ (13 / 16 : ℝ) = 1 - 3 / 16 := by
  norm_num

/-- The source exponent at the row cut `d = 13/16` is `3/16` plus the endpoint shape. -/
theorem relative_at_cut (δ R q : ℝ) :
    ProbeCentralExponent.sourceExponent ((1 + δ) / 2) (13 / 16) R q =
      3 / 16 + (-(1 / 48) + (2 / 3) * δ + q / 6 - (13 / 16) * (1 - R)) := by
  unfold ProbeCentralExponent.sourceExponent
  ring

/-- The source exponent is affine in the row length `d` with slope `R + δ/2 - 17/50`. -/
theorem sourceExponent_affine_in_d (δ d R q : ℝ) :
    ProbeCentralExponent.sourceExponent ((1 + δ) / 2) d R q =
      ProbeCentralExponent.sourceExponent ((1 + δ) / 2) (13 / 16) R q +
        (d - 13 / 16) * (R + δ / 2 - 17 / 50) := by
  unfold ProbeCentralExponent.sourceExponent
  ring

/-! Row-count crossing with a general plain-capacity coefficient `c`. -/

/-- General denominator `3 - x - 2cx`. -/
noncomputable def genDenominator (c x : ℝ) : ℝ := 3 - x - 2 * c * x
/-- General prime weight `(2 - 2cx)(1 - x)`. -/
noncomputable def genPrimeWeight (c x : ℝ) : ℝ := (2 - 2 * c * x) * (1 - x)
/-- General plain exponent `1 - δ(cx + (2 - 2cx)(t - r))`. -/
noncomputable def genPlainExponent (c δ x t r : ℝ) : ℝ :=
  1 - δ * (c * x + (2 - 2 * c * x) * (t - r))
/-- General crossing point of the inverse and plain exponents. -/
noncomputable def genCrossing (c x t : ℝ) : ℝ :=
  ((2 - 2 * c * x) * t - (1 - c) * x) / genDenominator c x
/-- General short exponent. -/
noncomputable def genShortExponent (c δ x t : ℝ) : ℝ :=
  1 - δ + δ * genPrimeWeight c x / genDenominator c x * (3 / 2 - t)

theorem genDenominator_code (x : ℝ) :
    genDenominator (4 / 9) x = HeckeDetectorRowCount.denominator x := by
  unfold genDenominator HeckeDetectorRowCount.denominator; ring

theorem genPrimeWeight_code (x : ℝ) :
    genPrimeWeight (4 / 9) x = HeckeDetectorRowCount.primeWeight x := by
  unfold genPrimeWeight HeckeDetectorRowCount.primeWeight; ring

theorem genPlainExponent_code (δ x t r : ℝ) :
    genPlainExponent (4 / 9) δ x t r = HeckeDetectorRowCount.plainExponent δ x t r := by
  unfold genPlainExponent HeckeDetectorRowCount.plainExponent; ring

theorem genCrossing_code (x t : ℝ) :
    genCrossing (4 / 9) x t = HeckeDetectorRowCount.crossing x t := by
  unfold genCrossing HeckeDetectorRowCount.crossing
  rw [genDenominator_code]; congr 1; ring

/-- The plain coefficient `c = 4/9` used in the code is `1/(3κ)` at `κ = 3/4`. -/
theorem plain_coefficient_at_kappa : (4 / 9 : ℝ) = 1 / (3 * (3 / 4)) := by norm_num

/-- Inverse and plain exponents agree at the general crossing, and equal the
general short exponent. -/
theorem gen_inverse_at_crossing (c δ x t : ℝ) (hd : genDenominator c x ≠ 0) :
    HeckeDetectorRowCount.inverseExponent δ x (genCrossing c x t) =
      genShortExponent c δ x t := by
  unfold HeckeDetectorRowCount.inverseExponent genCrossing genShortExponent genPrimeWeight
  field_simp
  unfold genDenominator
  ring

theorem gen_plain_at_crossing (c δ x t : ℝ) (hd : genDenominator c x ≠ 0) :
    genPlainExponent c δ x t (genCrossing c x t) = genShortExponent c δ x t := by
  unfold genPlainExponent genCrossing genShortExponent genPrimeWeight
  field_simp
  unfold genDenominator
  ring

/-- The balanced endpoint exponent at `(δ, y) = (79/204, 0)`. -/
theorem balancedExponent_at_witness :
    Endpoint.balancedExponent (79 / 204) 0 = -(49 / 214704) := by
  unfold Endpoint.balancedExponent Endpoint.balancedRowCount Endpoint.balancedCutoff
    Endpoint.balanceDenominator Endpoint.denominator Endpoint.primeWeight
  norm_num

/-- Hence the code's uniform margin `49/440640` is within the attained value. -/
theorem endpoint_margin_window :
    (49 / 440640 : ℝ) ≤ -Endpoint.balancedExponent (79 / 204) 0 ∧
      -Endpoint.balancedExponent (79 / 204) 0 = 49 / 214704 := by
  rw [balancedExponent_at_witness]; norm_num

end OAIExponentTrace
