import FleetFullLineFourier
import FleetExponentialEnvelope

noncomputable section
namespace FleetExponentialFourierBound
open MeasureTheory Complex FleetExponentialEnvelope FleetFullLineFourier

theorem weighted_norm_h_le {g : ℝ → ℂ} {E : ℝ} (hE : 0 ≤ E)
    (hg : ContDiff ℝ 2 g)
    (h0 : ∀ u, ‖g u‖ ≤ E * envelope 3 u)
    (h1 : ∀ u, ‖deriv g u‖ ≤ E * envelope 3 u)
    (h2 : ∀ u, ‖deriv (deriv g) u‖ ≤ E * envelope 3 u) (t : ℝ) :
    (1+t^2)*‖h g (t : ℂ)‖ ≤ 4*E/3 := by
  have hc1 : ContDiff ℝ 1 (deriv g) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1+1) g from hg)).2.2
  have hc2 : Continuous (deriv (deriv g)) := by
    have hc : ContDiff ℝ 0 (deriv (deriv g)) :=
      (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (0+1) (deriv g) from hc1)).2.2
    exact hc.continuous
  have hi0 := integrable_of_bound (by norm_num : (0:ℝ)<3) hE hg.continuous.aestronglyMeasurable h0
  have hi1 := integrable_of_bound (by norm_num : (0:ℝ)<3) hE hc1.continuous.aestronglyMeasurable h1
  have hi2 := integrable_of_bound (by norm_num : (0:ℝ)<3) hE hc2.aestronglyMeasurable h2
  have hb0 := integral_norm_le (by norm_num : (0:ℝ)<3) hE hg.continuous.aestronglyMeasurable h0
  have hb2 := integral_norm_le (by norm_num : (0:ℝ)<3) hE hc2.aestronglyMeasurable h2
  have hh := FleetFullLineFourier.weighted_norm_h_le hg hi0 hi1 hi2 t
  linarith

/-- Generic imaginary-axis evaluation, including both pole arguments. -/
theorem imaginary_integrable {g : ℝ → ℂ} {E y : ℝ} (hE : 0 ≤ E)
    (hg : AEStronglyMeasurable g) (h0 : ∀ u, ‖g u‖ ≤ E * envelope 3 u)
    (hy : |y| < 3) :
    Integrable (fun u : ℝ => g u * Complex.exp (I * (I*(y : ℂ)) * (u : ℂ))) := by
  have he (u : ℝ) : I*(I*(y : ℂ))*(u : ℂ) = ((-y : ℝ) : ℂ)*(u : ℂ) := by
    push_cast
    calc
      _ = (I*I)*(y : ℂ)*(u : ℂ) := by ring
      _ = _ := by rw [I_mul_I]; ring
  simp_rw [he]
  exact integrable_tilted (by simpa using hy) hE hg h0

theorem imaginary_norm_h_le {g : ℝ → ℂ} {E y : ℝ} (hE : 0 ≤ E)
    (hg : AEStronglyMeasurable g) (h0 : ∀ u, ‖g u‖ ≤ E * envelope 3 u)
    (hy : |y| < 3) : ‖h g (I*(y : ℂ))‖ ≤ 2*E/(3-|y|) := by
  have he (u : ℝ) : I*(I*(y : ℂ))*(u : ℂ) = ((-y : ℝ) : ℂ)*(u : ℂ) := by
    push_cast
    calc
      _ = (I*I)*(y : ℂ)*(u : ℂ) := by ring
      _ = _ := by rw [I_mul_I]; ring
  unfold h
  simp_rw [he]
  exact (norm_integral_le_integral_norm _).trans (by
    simpa using integral_norm_tilted_le (by simpa using hy : |-y| < 3) hE hg h0)

theorem pole_norm_h_le {g : ℝ → ℂ} {E : ℝ} (hE : 0 ≤ E)
    (hg : AEStronglyMeasurable g) (h0 : ∀ u, ‖g u‖ ≤ E * envelope 3 u) :
    ‖h g (I/2)‖ ≤ 4*E/5 ∧ ‖h g (-I/2)‖ ≤ 4*E/5 := by
  constructor
  · have hh := imaginary_norm_h_le hE hg h0 (by norm_num [abs_div] : |(1/2 : ℝ)| < 3)
    norm_num [abs_div] at hh ⊢
    convert hh using 1 <;> ring
  · have hh := imaginary_norm_h_le hE hg h0 (by norm_num [abs_div] : |(-1/2 : ℝ)| < 3)
    norm_num [abs_div] at hh ⊢
    convert hh using 1 <;> ring

end FleetExponentialFourierBound
#print axioms FleetExponentialFourierBound.weighted_norm_h_le
#print axioms FleetExponentialFourierBound.imaginary_norm_h_le
