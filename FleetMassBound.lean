import ZeroDensityUnconditional

/-!
# A uniform weighted-mass bound for the zero ordinates

`FleetRationalBankCriterion.Feasible` is a conjunction of two conditions on a
finite real tuple `x : Fin N → ℝ`:

* a **weighted-mass bound** `∑ i, (1 + (x i)^2)⁻¹ ≤ M`, with one `M` for every stage;
* a **residual bound** against the arithmetic side of the explicit formula.

This file discharges the *first* conjunct for the actual zero ordinates,
unconditionally. The input is `ZeroDensityUnconditional.summable_inv_sq_ordinates`
(`∑ 1/γ² < ∞`), which is itself a consequence of the unconditional
`N(T) = O(T log T)` counting bound proved in `ZeroDensity`.

What this does NOT do: it says nothing about the residual conjunct, which is
where the difficulty of the criterion lives, and it proves nothing about the
Riemann Hypothesis. It removes one of two hypotheses from the criterion's
antecedent in the case of the true ordinates, no more.
-/

namespace FleetMassBound

/-- With `2 ≤ |γ n|`, the weighted mass `(1 + γ²)⁻¹` is dominated by `1/γ²`,
so summability transfers. -/
theorem summable_weighted_mass {γ : ℕ → ℝ} (hγ : ∀ n, 2 ≤ |γ n|)
    (h : Summable fun n => 1 / (γ n) ^ 2) :
    Summable fun n => (1 + (γ n) ^ 2)⁻¹ := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) h
  · positivity
  · have hpos : (0 : ℝ) < (γ n) ^ 2 := by
      have h0 : (0 : ℝ) < |γ n| := lt_of_lt_of_le (by norm_num) (hγ n)
      positivity
    have hle : (γ n) ^ 2 ≤ 1 + (γ n) ^ 2 := by linarith
    rw [one_div]
    exact inv_anti₀ hpos hle

/-- **One constant bounds every finite partial sum of the weighted mass.**
This is the shape the criterion's mass conjunct needs: a single `M`,
independent of the stage. -/
theorem exists_uniform_mass_bound {γ : ℕ → ℝ} (hγ : ∀ n, 2 ≤ |γ n|)
    (h : Summable fun n => 1 / (γ n) ^ 2) :
    ∃ M : ℝ, ∀ s : Finset ℕ, ∑ n ∈ s, (1 + (γ n) ^ 2)⁻¹ ≤ M := by
  have hs := summable_weighted_mass hγ h
  refine ⟨∑' n, (1 + (γ n) ^ 2)⁻¹, fun s => ?_⟩
  exact hs.sum_le_tsum s (fun n _ => by positivity)

/-- **Unconditional.** For any injective enumeration of the nontrivial zeros of
`riemannZeta` with `|Im| ≥ 2`, listed by non-decreasing height, the weighted mass
of every finite subfamily is bounded by a single constant. -/
theorem exists_uniform_mass_bound_zeros
    (zeros : ℕ → ℂ) (hinj : Function.Injective zeros)
    (hz : ∀ n, IsNontrivialZero (zeros n))
    (hγ : ∀ n, 2 ≤ |(zeros n).im|) (hmono : Monotone fun n => |(zeros n).im|) :
    ∃ M : ℝ, ∀ s : Finset ℕ, ∑ n ∈ s, (1 + ((zeros n).im) ^ 2)⁻¹ ≤ M :=
  exists_uniform_mass_bound hγ
    (ZeroDensityUnconditional.summable_inv_sq_ordinates zeros hinj hz hγ hmono)

end FleetMassBound
