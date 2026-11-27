import Mathlib

noncomputable section
open Set MeasureTheory
open scoped Interval
namespace FleetPeriodicApproximation

/-- Complex-valued mean-zero control, obtained by integrating differences rather
than asserting that the function vanishes somewhere. -/
theorem norm_le_period_mul_deriv_bound_on {H : ℝ → ℂ} {P C : ℝ}
    (hP : 0 < P) (hC : 0 ≤ C) (hd : Differentiable ℝ H)
    (hb : ∀ s ∈ Icc 0 P, ‖deriv H s‖ ≤ C)
    (hm : (∫ s in (0 : ℝ)..P, H s) = 0) {t : ℝ} (ht : t ∈ Icc 0 P) :
    ‖H t‖ ≤ P * C := by
  have hi : (∫ s in (0 : ℝ)..P, H t - H s) = P • H t := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      (hd.continuous.intervalIntegrable 0 P), intervalIntegral.integral_const, hm]
    simp
  have hb' : ∀ s ∈ Ι (0 : ℝ) P, ‖H t - H s‖ ≤ C * P := by
    intro s hs
    have hs' : s ∈ Icc 0 P := by
      rw [uIoc_of_le hP.le] at hs
      exact ⟨hs.1.le, hs.2⟩
    have hdif := (convex_Icc (0 : ℝ) P).norm_image_sub_le_of_norm_deriv_le
      (fun x _ => hd x) hb hs' ht
    have hdist : ‖t - s‖ ≤ P := by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [ht.1, ht.2, hs'.1, hs'.2]
    exact hdif.trans (mul_le_mul_of_nonneg_left hdist hC)
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hb'
  rw [hi, norm_smul, Real.norm_eq_abs, abs_of_pos hP, sub_zero, abs_of_pos hP] at hnorm
  nlinarith

/-- The preceding estimate extends to every real argument by periodicity. -/
theorem norm_le_period_mul_deriv_bound {H : ℝ → ℂ} {P C : ℝ}
    (hP : 0 < P) (hC : 0 ≤ C) (hp : Function.Periodic H P)
    (hd : Differentiable ℝ H) (hb : ∀ s ∈ Icc 0 P, ‖deriv H s‖ ≤ C)
    (hm : (∫ s in (0 : ℝ)..P, H s) = 0) (t : ℝ) : ‖H t‖ ≤ P * C := by
  have ht : t - (⌊t / P⌋ : ℤ) * P ∈ Icc (0 : ℝ) P :=
    ⟨Int.sub_floor_div_mul_nonneg t hP, (Int.sub_floor_div_mul_lt t hP).le⟩
  have h := norm_le_period_mul_deriv_bound_on hP hC hd hb hm ht
  rwa [hp.sub_int_mul_eq] at h

lemma periodic_deriv {H : ℝ → ℂ} {P : ℝ} (hp : Function.Periodic H P) :
    Function.Periodic (deriv H) P := by
  intro t
  rw [← deriv_comp_add_const]
  congr 1
  exact funext hp

/-- Mean-zero periodic C² errors are controlled in C⁰ and C¹ by their second
derivative. The first derivative's mean is supplied by the fundamental theorem
of calculus and periodic endpoint equality. -/
theorem norm_bounds_of_second_deriv {H : ℝ → ℂ} {P C : ℝ}
    (hP : 0 < P) (hC : 0 ≤ C) (hp : Function.Periodic H P)
    (hd : Differentiable ℝ H) (hdd : Differentiable ℝ (deriv H))
    (hb : ∀ s ∈ Icc 0 P, ‖deriv (deriv H) s‖ ≤ C)
    (hm : (∫ s in (0 : ℝ)..P, H s) = 0) :
    (∀ t, ‖deriv H t‖ ≤ P * C) ∧
      ∀ t, ‖H t‖ ≤ P^2 * C := by
  have hmean : (∫ s in (0 : ℝ)..P, deriv H s) = 0 := by
    rw [intervalIntegral.integral_deriv_eq_sub (fun s _ => hd s)
      (hdd.continuous.intervalIntegrable 0 P)]
    have he : H P = H 0 := by simpa using hp 0
    rw [he, sub_self]
  have hfirst : ∀ t ∈ Icc 0 P, ‖deriv H t‖ ≤ P * C :=
    fun t ht => norm_le_period_mul_deriv_bound_on hP hC hdd hb hmean ht
  refine ⟨fun t => norm_le_period_mul_deriv_bound hP hC (periodic_deriv hp) hdd hb hmean t,
    fun t => ?_⟩
  have h := norm_le_period_mul_deriv_bound hP (mul_nonneg hP.le hC) hp hd hfirst hm t
  nlinarith

end FleetPeriodicApproximation
