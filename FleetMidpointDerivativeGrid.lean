import FleetMidpointQuadrature

/-! Uniform midpoint quadrature using explicit derivative witnesses, so that
the actual finite Gaussian formula can be used without an additional global
`ContDiff` conversion. -/

noncomputable section
namespace FleetMidpointDerivativeGrid
open MeasureTheory Set

theorem uniform_midpoint_error_of_hasDerivAt {f f' f'' : ℝ → ℝ}
    (h1 : ∀ x, HasDerivAt f (f' x) x)
    (h2 : ∀ x, HasDerivAt f' (f'' x) x)
    (a h M : ℝ) (n : ℕ) (hh : 0 ≤ h)
    (hbound : ∀ t ∈ Icc a (a+n*h), |f'' t| ≤ M) :
    |(∫ x in a..(a+n*h), f x) -
      h*∑ k ∈ Finset.range n, f (a+((k : ℝ)+1/2)*h)| ≤ (n : ℝ)*M*h^3/24 := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (h1 x).continuousAt)
  let grid : ℕ → ℝ := fun k => a+(k:ℝ)*h
  have hmono : ∀ k < n, grid k ≤ grid (k+1) := by
    intro k _
    dsimp [grid]
    push_cast
    nlinarith
  have hcell : ∀ k < n, ∀ t ∈ Icc (grid k) (grid (k+1)), |f'' t| ≤ M := by
    intro k hk t ht
    apply hbound t
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have hkn : ((k+1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (show k+1 ≤ n by omega)
    dsimp [grid] at ht
    constructor
    · nlinarith [ht.1, mul_nonneg hk0 hh]
    · nlinarith [ht.2, mul_le_mul_of_nonneg_right hkn hh]
  have hp : |(∫ x in (grid 0)..(grid n), f x) -
      ∑ k ∈ Finset.range n, (grid (k+1)-grid k)*f ((grid k+grid (k+1))/2)| ≤
      ∑ k ∈ Finset.range n, M*(grid (k+1)-grid k)^3/24 := by
    have hs := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (a := grid) (n := n) (fun k _ => hf.intervalIntegrable (grid k) (grid (k+1)))
    rw [← hs, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro k hk
    exact FleetMidpointQuadrature.midpoint_error_of_hasDerivAt
      (hmono k (Finset.mem_range.mp hk)) hf.continuousOn
      (fun t _ => h1 t) (fun t _ => h2 t) (hcell k (Finset.mem_range.mp hk))
  have hw (k : ℕ) : grid (k+1)-grid k = h := by dsimp [grid]; push_cast; ring
  have hm (k : ℕ) : (grid k+grid (k+1))/2 = a+((k : ℝ)+1/2)*h := by
    dsimp [grid]; push_cast; ring
  simp_rw [hw, hm] at hp
  simpa [grid, Finset.mul_sum, mul_assoc, mul_div_assoc] using hp

end FleetMidpointDerivativeGrid
