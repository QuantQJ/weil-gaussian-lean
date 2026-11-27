import FleetLocalAtomicLimit

noncomputable section
open Filter Topology MeasureTheory
namespace FleetEscapeExample

/-- There are n²+1 unit atoms, all at ordinate n. -/
def coordinate (n : ℕ) (_ : Fin (n^2+1)) : ℝ := n

def measure (n : ℕ) : Measure ℝ :=
  ∑ i : Fin (n^2+1), Measure.dirac (coordinate n i)

/-- The inverse-quadratic mass remains exactly one. -/
theorem weighted_sum_eq_one (n : ℕ) :
    (∑ i : Fin (n^2+1), (1+(coordinate n i)^2)⁻¹) = 1 := by
  simp only [coordinate, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one]
  have h : (1+(n : ℝ)^2) ≠ 0 := by positivity
  field_simp
  ring

/-- Compact support alone makes the entire finite trace eventually zero. -/
theorem compact_trace_eventually_zero (φ : ℝ → ℂ) (hφ : HasCompactSupport φ) :
    (fun n => ∑ i : Fin (n^2+1), φ (coordinate n i)) =ᶠ[atTop] 0 := by
  obtain ⟨B, hB⟩ := hφ.isCompact.bddAbove
  have he : ∀ᶠ n : ℕ in atTop, B < (n : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
      (eventually_gt_atTop B)
  filter_upwards [he] with n hn
  have hz : φ (n : ℝ) = 0 := by
    by_contra h
    have := hB (subset_closure (Function.mem_support.mpr h))
    linarith
  simp [coordinate, hz]

theorem compact_trace_tendsto_zero (φ : ℝ → ℂ) (hφ : HasCompactSupport φ) :
    Tendsto (fun n => ∑ i : Fin (n^2+1), φ (coordinate n i)) atTop (𝓝 0) :=
  tendsto_const_nhds.congr' (compact_trace_eventually_zero φ hφ).symm

theorem weighted_integral_eq_one (n : ℕ) :
    (∫ t : ℝ, (1+t^2)⁻¹ ∂measure n) = 1 := by
  rw [measure, FleetLocalAtomicLimit.integral_real_unit_atoms]
  exact weighted_sum_eq_one n

/-- The zero measure is an actual compact-test limit despite the retained weighted mass. -/
theorem compact_test_limit_zero (φ : ℝ → ℂ) (_hc : Continuous φ)
    (hφ : HasCompactSupport φ) :
    Tendsto (fun n => ∫ t, φ t ∂measure n) atTop (𝓝 (∫ t, φ t ∂(0 : Measure ℝ))) := by
  simpa only [measure, FleetAtomicLimit.integral_unit_atoms, integral_zero_measure] using
    compact_trace_tendsto_zero φ hφ

/-- Compact-test convergence does not conserve inverse-quadratic mass. -/
theorem weighted_integrals_not_tendsto_limit_mass :
    ¬ Tendsto (fun n => ∫ t : ℝ, (1+t^2)⁻¹ ∂measure n) atTop
      (𝓝 (∫ t : ℝ, (1+t^2)⁻¹ ∂(0 : Measure ℝ))) := by
  intro h
  simp only [weighted_integral_eq_one, integral_zero_measure] at h
  have he : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds h
  norm_num at he

end FleetEscapeExample
