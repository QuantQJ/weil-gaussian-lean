import FleetSmoothPeriodization
import FleetPeriodizationSupport

noncomputable section
namespace FleetPeriodicReplacement
open FleetSmoothPeriodization FleetPeriodizationSupport

theorem exists_periodic_replacement {R C : ℝ} {F : ℝ → ℂ}
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hF : ContDiff ℝ 2 F)
    (hs : ∀ u, R < |u| → F u = 0)
    (h0 : ∀ u, ‖F u‖ ≤ C) (h1 : ∀ u, ‖deriv F u‖ ≤ C)
    (h2 : ∀ u, ‖deriv (deriv F) u‖ ≤ C) (T : ℝ) (hT : 0 ≤ T) :
    ∃ m : ℕ, 0 < m ∧
      Function.Periodic (periodize (2*Real.pi*m) F) (2*Real.pi*m) ∧
      ContDiff ℝ 2 (periodize (2*Real.pi*m) F) ∧
      (∀ u, |u| < T → periodize (2*Real.pi*m) F u = F u) ∧
      (∀ u, ‖periodize (2*Real.pi*m) F u‖ ≤ C) ∧
      (∀ u, ‖deriv (periodize (2*Real.pi*m) F) u‖ ≤ C) ∧
      (∀ u, ‖deriv (deriv (periodize (2*Real.pi*m) F)) u‖ ≤ C) := by
  obtain ⟨m, hm⟩ := exists_nat_gt ((2*R+T+1)/(2*Real.pi))
  have hp := Real.pi_pos
  have hm' : 2*R+T+1 < (m:ℝ)*(2*Real.pi) := (div_lt_iff₀ (by positivity)).mp hm
  have hm0 : 0 < m := by
    by_contra hn
    have he : m = 0 := Nat.eq_zero_of_not_pos hn
    subst m
    norm_num at hm'
    linarith
  have hP : 0 < 2*Real.pi*(m:ℝ) := by positivity
  have hPR : 2*R < 2*Real.pi*(m:ℝ) := by nlinarith
  have hd := hF.differentiable (by norm_num)
  have hd' : Differentiable ℝ (deriv F) :=
    ((contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1+1) F from hF)).2.2).differentiable one_ne_zero
  have hs' : ∀ u, R < |u| → deriv F u = 0 := fun u hu => deriv_eq_zero_outside hs hu
  have hs'' : ∀ u, R < |u| → deriv (deriv F) u = 0 :=
    fun u hu => deriv_eq_zero_outside hs' hu
  refine ⟨m, hm0, periodic_periodize _ _, contDiff_periodize hP hs hF, ?_, ?_, ?_, ?_⟩
  · intro u hu
    exact central_tsum_eq hR hs (by nlinarith)
  · intro u
    exact norm_tsum_le hR hPR hs hC h0
  · intro u
    rw [deriv_periodize hP hs hd]
    exact norm_tsum_le hR hPR hs' hC h1
  · intro u
    rw [second_deriv_periodize hP hs hd hd']
    exact norm_tsum_le hR hPR hs'' hC h2

end FleetPeriodicReplacement
#print axioms FleetPeriodicReplacement.exists_periodic_replacement
