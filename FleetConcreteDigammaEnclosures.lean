import FleetDigammaPointCertificate

/-! Concrete enclosures produced by the rational evaluator and replayed by
Lean's kernel. These certify point values, not an entire quadrature rule. -/

namespace FleetConcreteDigammaEnclosures
open FleetDigammaPointCertificate FleetRationalInterval
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

theorem psi_quarter :
    (-4229/1000 : ℝ) ≤ (FleetGammaKernel.psi (1/4)).re ∧
      (FleetGammaKernel.psi (1/4)).re ≤ (-4226/1000 : ℝ) := by
  have h := enlarge (b := ⟨-4229/1000, -4226/1000⟩)
    (psiAt_contains 0 (by norm_num)) (by decide +kernel) (by decide +kernel)
  simpa [Contains, FleetDigammaIntervalCertificate.quarterPoint] using h

theorem psi_quarter_add_I :
    (-18/1000 : ℝ) ≤ (FleetGammaKernel.psi (1/4+Complex.I)).re ∧
      (FleetGammaKernel.psi (1/4+Complex.I)).re ≤ (-15/1000 : ℝ) := by
  have h := enlarge (b := ⟨-18/1000, -15/1000⟩)
    (psiAt_contains 1 (by norm_num)) (by decide +kernel) (by decide +kernel)
  simpa [Contains, FleetDigammaIntervalCertificate.quarterPoint] using h

theorem weight_one_hundred :
    (2766/1000 : ℝ) ≤ FleetGammaKernel.weight 100 ∧
      FleetGammaKernel.weight 100 ≤ (2769/1000 : ℝ) := by
  have h := enlarge (b := ⟨2766/1000, 2769/1000⟩)
    (weightAt_contains 100 (by norm_num [abs_div])) (by decide +kernel) (by decide +kernel)
  norm_num [Contains] at h ⊢
  exact h

end FleetConcreteDigammaEnclosures
