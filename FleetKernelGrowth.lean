import FleetGammaGrowth
import FleetTangentBound
import GammaExplicitFormula

namespace FleetKernelGrowth
open Set

/-- The gamma kernel satisfies the logarithmic strip bound needed to move its
vertical contour to the critical line. -/
theorem exists_kernel_log_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Icc (1/2 : ℝ) (3/2), ∀ t : ℝ, 1 ≤ |t| →
      ‖GammaExplicitFormula.gammaKernel ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * (1 + Real.log (2 + |t|)) := by
  obtain ⟨D, hD, hb⟩ := FleetGammaGrowth.exists_strip_bound (1/2) (3/2) (by norm_num)
  let A : ℝ := |Real.log (2 * Real.pi)| + Real.pi
  have hA : 0 ≤ A := add_nonneg (abs_nonneg _) Real.pi_pos.le
  refine ⟨D + A, add_nonneg hD.le hA, ?_⟩
  intro σ hσ t ht
  have hg := hb σ hσ t
  have htan := FleetTangentBound.norm_tan_pi_line_le_two σ t ht
  have hlog : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hpi : ‖(Real.pi : ℂ) / 2‖ = Real.pi / 2 := by
    simp [norm_div, abs_of_pos Real.pi_pos]
  have htrig : ‖(Real.pi : ℂ) / 2 *
      Complex.tan ((Real.pi : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I) / 2)‖ ≤ Real.pi := by
    rw [norm_mul, hpi]
    nlinarith [Real.pi_pos]
  have hc : ‖-(Real.log (2 * Real.pi) : ℂ)‖ = |Real.log (2 * Real.pi)| := by
    simp
  unfold GammaExplicitFormula.gammaKernel
  calc
    _ ≤ ‖-(Real.log (2 * Real.pi) : ℂ) +
          deriv Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) /
            Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ +
        ‖(Real.pi : ℂ) / 2 * Complex.tan
          ((Real.pi : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I) / 2)‖ := norm_sub_le _ _
    _ ≤ (‖-(Real.log (2 * Real.pi) : ℂ)‖ +
          ‖deriv Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) /
            Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖) + Real.pi :=
      add_le_add (norm_add_le _ _) htrig
    _ ≤ |Real.log (2 * Real.pi)| + D * (1 + Real.log (2 + |t|)) + Real.pi := by
      rw [hc]
      linarith
    _ ≤ (D + A) * (1 + Real.log (2 + |t|)) := by
      have ha := mul_nonneg hA hlog
      dsimp only [A] at *
      nlinarith


end FleetKernelGrowth
