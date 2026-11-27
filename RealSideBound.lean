import Mathlib

set_option autoImplicit false

/-!
# Real-side bound for Gaussian sums over a tempered real sequence

For a real sequence `γ : ι → ℝ` with `∑ 1/(1 + γᵢ²) < ∞` and a width `0 < b ≤ 1`, the Gaussian
sum `∑ᵢ √(π/b) · exp(−(γᵢ − α)²/(4b))` is bounded by `√(π/b) · C` with `C` independent of `b`:
the sum grows at most like `b^{-1/2}` as `b → 0`.

`term b α x = √(π/b) · exp(−(x − α)²/(4b))` is exactly the modulus of the Gaussian test function's
transform (`GaussianTest.gaussHat`) at a real point; the literal form is kept so downstream glue
can rewrite.
-/

namespace RealSideBound

open Real

/-- The real-side Gaussian term: `√(π/b) · exp(−(x − α)²/(4b))`. -/
noncomputable def term (b α : ℝ) (x : ℝ) : ℝ :=
  Real.sqrt (π / b) * Real.exp (-(x - α) ^ 2 / (4 * b))

variable {ι : Type*} {γ : ι → ℝ}

/-- **Finitely many small terms.** If `∑ 1/(1 + γᵢ²) < ∞` then only finitely many `|γᵢ| ≤ T`:
infinitely many terms `≥ 1/(1 + T²)` would contradict summability. -/
theorem finite_small (hsum : Summable (fun i => 1 / (1 + (γ i) ^ 2))) (T : ℝ) :
    {i | |γ i| ≤ T}.Finite := by
  have hpos : (0 : ℝ) < 1 / (1 + T ^ 2) := by positivity
  have hev : ∀ᶠ i in Filter.cofinite, (1 / (1 + (γ i) ^ 2)) < 1 / (1 + T ^ 2) :=
    hsum.tendsto_cofinite_zero.eventually_lt_const hpos
  rw [Filter.eventually_cofinite] at hev
  refine hev.subset fun i hi => ?_
  simp only [Set.mem_setOf_eq, not_lt]
  have hi' : |γ i| ≤ T := hi
  have hsq : (γ i) ^ 2 ≤ T ^ 2 := by
    have := abs_le.mp hi'
    nlinarith [abs_nonneg (γ i), sq_abs (γ i)]
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- For `0 < b ≤ 1` the Gaussian at width `b` is below the Gaussian at width `1`. -/
theorem exp_bound (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) (α x : ℝ) :
    Real.exp (-(x - α) ^ 2 / (4 * b)) ≤ Real.exp (-(x - α) ^ 2 / 4) := by
  rw [Real.exp_le_exp]
  have h4b : 0 < 4 * b := by positivity
  rw [div_le_div_iff₀ h4b (by norm_num)]
  nlinarith [sq_nonneg (x - α)]

/-- Elementary Gaussian tail bound: for `c > 0`, `exp(−y²/c) ≤ (c + 1)/(1 + y²)`. -/
theorem exp_neg_sq_div_le (c : ℝ) (hc : 0 < c) (y : ℝ) :
    Real.exp (-y ^ 2 / c) ≤ (c + 1) / (1 + y ^ 2) := by
  have h1 : y ^ 2 / c + 1 ≤ Real.exp (y ^ 2 / c) := Real.add_one_le_exp _
  have hpos : 0 < Real.exp (y ^ 2 / c) := Real.exp_pos _
  rw [neg_div, Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ hpos (by positivity)]
  have h2 : c * (y ^ 2 / c + 1) = y ^ 2 + c := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left h1 hc.le, sq_nonneg y]

/-- Shifting the centre: `1/(1 + (x − α)²) ≤ 2(1 + α²)/(1 + x²)`. -/
theorem one_div_shift_le (α x : ℝ) :
    1 / (1 + (x - α) ^ 2) ≤ 2 * (1 + α ^ 2) / (1 + x ^ 2) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (x - α - α), sq_nonneg ((x - α) * α), sq_nonneg (x - α), sq_nonneg α]

/-- Shifted Gaussian tail bound: `exp(−(x − α)²/c) ≤ 2(c + 1)(1 + α²)/(1 + x²)`. -/
theorem exp_neg_sq_shift_le (c : ℝ) (hc : 0 < c) (α x : ℝ) :
    Real.exp (-(x - α) ^ 2 / c) ≤ 2 * (c + 1) * (1 + α ^ 2) / (1 + x ^ 2) := by
  calc Real.exp (-(x - α) ^ 2 / c) ≤ (c + 1) / (1 + (x - α) ^ 2) := exp_neg_sq_div_le c hc _
    _ = (c + 1) * (1 / (1 + (x - α) ^ 2)) := by ring
    _ ≤ (c + 1) * (2 * (1 + α ^ 2) / (1 + x ^ 2)) :=
        mul_le_mul_of_nonneg_left (one_div_shift_le α x) (by linarith)
    _ = 2 * (c + 1) * (1 + α ^ 2) / (1 + x ^ 2) := by ring

/-- The width-`1` Gaussian centred at `α` is dominated by `C/(1 + x²)` with `C = 10(1 + α²)`. -/
theorem gaussian_le_inv_sq (α : ℝ) :
    ∃ C : ℝ, ∀ x : ℝ, Real.exp (-(x - α) ^ 2 / 4) ≤ C / (1 + x ^ 2) := by
  refine ⟨10 * (1 + α ^ 2), fun x => ?_⟩
  have := exp_neg_sq_shift_le 4 (by norm_num) α x
  calc Real.exp (-(x - α) ^ 2 / 4) ≤ 2 * (4 + 1) * (1 + α ^ 2) / (1 + x ^ 2) := this
    _ = 10 * (1 + α ^ 2) / (1 + x ^ 2) := by ring

/-- The Gaussian term is nonnegative. -/
theorem term_nonneg (b α x : ℝ) : 0 ≤ term b α x := by
  unfold term; positivity

/-- **Summability of the Gaussian sum** for every width `b > 0`. -/
theorem summable_term (hsum : Summable (fun i => 1 / (1 + (γ i) ^ 2))) (b : ℝ) (hb : 0 < b)
    (α : ℝ) : Summable (fun i => term b α (γ i)) := by
  have h4b : 0 < 4 * b := by positivity
  refine Summable.of_nonneg_of_le (fun i => term_nonneg b α (γ i)) (fun i => ?_)
    ((hsum.mul_left (Real.sqrt (π / b) * (2 * (4 * b + 1) * (1 + α ^ 2)))))
  unfold term
  have := exp_neg_sq_shift_le (4 * b) h4b α (γ i)
  calc Real.sqrt (π / b) * Real.exp (-(γ i - α) ^ 2 / (4 * b))
      ≤ Real.sqrt (π / b) * (2 * (4 * b + 1) * (1 + α ^ 2) / (1 + (γ i) ^ 2)) :=
        mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg _)
    _ = Real.sqrt (π / b) * (2 * (4 * b + 1) * (1 + α ^ 2)) * (1 / (1 + (γ i) ^ 2)) := by ring

/-- **The `b^{-1/2}` bound.** There is `C` (independent of `b`) with
`∑ᵢ term b α (γᵢ) ≤ √(π/b) · C` for all `0 < b ≤ 1`. -/
theorem tsum_term_le (hsum : Summable (fun i => 1 / (1 + (γ i) ^ 2))) (α : ℝ) :
    ∃ C : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      ∑' i, term b α (γ i) ≤ Real.sqrt (π / b) * C := by
  obtain ⟨C₀, hC₀⟩ := gaussian_le_inv_sq α
  refine ⟨C₀ * ∑' i, 1 / (1 + (γ i) ^ 2), fun b hb hb1 => ?_⟩
  have hle : ∀ i, term b α (γ i) ≤ Real.sqrt (π / b) * C₀ * (1 / (1 + (γ i) ^ 2)) := by
    intro i
    unfold term
    calc Real.sqrt (π / b) * Real.exp (-(γ i - α) ^ 2 / (4 * b))
        ≤ Real.sqrt (π / b) * Real.exp (-(γ i - α) ^ 2 / 4) :=
          mul_le_mul_of_nonneg_left (exp_bound b hb hb1 α (γ i)) (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt (π / b) * (C₀ / (1 + (γ i) ^ 2)) :=
          mul_le_mul_of_nonneg_left (hC₀ (γ i)) (Real.sqrt_nonneg _)
      _ = Real.sqrt (π / b) * C₀ * (1 / (1 + (γ i) ^ 2)) := by ring
  calc ∑' i, term b α (γ i)
      ≤ ∑' i, Real.sqrt (π / b) * C₀ * (1 / (1 + (γ i) ^ 2)) :=
        Summable.tsum_le_tsum hle (summable_term hsum b hb α) (hsum.mul_left _)
    _ = Real.sqrt (π / b) * C₀ * ∑' i, 1 / (1 + (γ i) ^ 2) := tsum_mul_left
    _ = Real.sqrt (π / b) * (C₀ * ∑' i, 1 / (1 + (γ i) ^ 2)) := by ring

/-- The Gaussian sum is nonnegative. -/
theorem tsum_term_nonneg (b α : ℝ) : 0 ≤ ∑' i, term b α (γ i) :=
  tsum_nonneg fun i => term_nonneg b α (γ i)

end RealSideBound
