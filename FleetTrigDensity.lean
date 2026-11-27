import FleetTrigPrimitive
import Mathlib

noncomputable section
open Set MeasureTheory AddCircle
open scoped BigOperators
namespace FleetTrigDensity

variable {P : ℝ} [Fact (0 < P)]

lemma integral_fourier (k : ℤ) :
    (∫ t : AddCircle P, fourier k t ∂haarAddCircle) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k
    simp [fourier_zero]
  · rw [if_neg hk]
    exact integral_eq_zero_of_add_right_eq_neg
      (fourier_add_half_inv_index hk (Fact.out : 0 < P))

/-- Uniform approximation by an actual finite list of Fourier coefficients. -/
theorem exists_finite_fourier_approx (F : C(AddCircle P, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset ℤ, ∃ c : ℤ → ℂ,
      ∀ t : AddCircle P, ‖F t - ∑ k ∈ s, c k * fourier k t‖ < ε := by
  classical
  have hF : F ∈ (Submodule.span ℂ (range (@fourier P))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]
    trivial
  change F ∈ closure (↑(Submodule.span ℂ (range (@fourier P))) : Set C(AddCircle P, ℂ)) at hF
  obtain ⟨G, hG, hdist⟩ := Metric.mem_closure_iff.mp hF ε hε
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hG
  refine ⟨c.support, c, fun t => ?_⟩
  have ht := ContinuousMap.norm_coe_le_norm
    (F - c.sum (fun k a => a • @fourier P k)) t
  have hval : (c.sum (fun k a => a • @fourier P k)) t =
      ∑ k ∈ c.support, c k * fourier k t := by
    simp [Finsupp.sum, ContinuousMap.sum_apply]
  rw [ContinuousMap.sub_apply, hval] at ht
  exact ht.trans_lt (by simpa [dist_eq_norm] using hdist)

lemma integral_polynomial (s : Finset ℤ) (c : ℤ → ℂ) :
    (∫ t : AddCircle P, (∑ k ∈ s, c k * fourier k t) ∂haarAddCircle) =
      if 0 ∈ s then c 0 else 0 := by
  classical
  rw [MeasureTheory.integral_finsetSum (f := fun k t => c k * fourier k t) s (fun k _ =>
    (integrableOn_univ.mp ((continuous_const.mul (fourier k).continuous).continuousOn.integrableOn_compact isCompact_univ)))]
  simp_rw [MeasureTheory.integral_const_mul, integral_fourier]
  simp

/-- A mean-zero continuous circle function admits uniformly close finite Fourier
polynomials whose constant coefficient is exactly zero. -/
theorem exists_zero_mean_fourier_approx (F : C(AddCircle P, ℂ))
    (hm : (∫ t : AddCircle P, F t ∂haarAddCircle) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset ℤ, ∃ c : ℤ → ℂ, c 0 = 0 ∧
      (∫ t : AddCircle P, (∑ k ∈ s, c k * fourier k t) ∂haarAddCircle) = 0 ∧
      ∀ t : AddCircle P, ‖F t - ∑ k ∈ s, c k * fourier k t‖ < ε := by
  classical
  obtain ⟨s, c, hclose⟩ := exists_finite_fourier_approx F (show 0 < ε / 3 by positivity)
  let Q : AddCircle P → ℂ := fun t => ∑ k ∈ s, c k * fourier k t
  let a : ℂ := if 0 ∈ s then c 0 else 0
  have hQc : Continuous Q := by
    exact continuous_finset_sum s (fun k _ => continuous_const.mul (fourier k).continuous)
  have hQi : Integrable Q haarAddCircle :=
    integrableOn_univ.mp (hQc.continuousOn.integrableOn_compact isCompact_univ)
  have hFi : Integrable F haarAddCircle :=
    integrableOn_univ.mp (F.continuous.continuousOn.integrableOn_compact isCompact_univ)
  have ha : ‖a‖ ≤ ε / 3 := by
    have hi := norm_integral_le_of_norm_le_const (μ := haarAddCircle)
      (Filter.Eventually.of_forall (fun t => (hclose t).le))
    rw [integral_sub hFi hQi, hm] at hi
    have hmeanQ : (∫ t, Q t ∂haarAddCircle) = a := integral_polynomial s c
    rw [hmeanQ] at hi
    simpa using hi
  let d : ℤ → ℂ := fun k => if k = 0 then 0 else c k
  have hpoly (t : AddCircle P) :
      (∑ k ∈ s.erase 0, d k * fourier k t) = Q t - a := by
    have he : (∑ k ∈ s.erase 0, d k * fourier k t) =
        ∑ k ∈ s.erase 0, c k * fourier k t := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [d, (Finset.mem_erase.mp hk).1]
    rw [he]
    by_cases h0 : 0 ∈ s
    · rw [Finset.sum_erase_eq_sub h0]
      simp [Q, a, h0, fourier_zero]
    · simp [Finset.erase_eq_of_notMem h0, Q, a, h0]
  refine ⟨s.erase 0, d, by simp [d], ?_, ?_⟩
  · rw [integral_polynomial]
    simp
  · intro t
    rw [hpoly]
    have h := norm_add_le (F t - Q t) a
    have hq : ‖F t - Q t‖ < ε / 3 := hclose t
    have he : F t - (Q t - a) = (F t - Q t) + a := by ring
    rw [he]
    linarith

end FleetTrigDensity
