import FleetPeriodicC2Density
import FleetGaussianMultiplier

noncomputable section
namespace FleetDampedPeriodicApproximation
open FleetArithmeticContinuity FleetExponentialEnvelope FleetTrigPrimitive

lemma polynomial_contDiff (P : ℝ) (s : Finset ℤ) (c : ℤ → ℂ) (n : ℕ∞) :
    ContDiff ℝ n (polynomial P s c) := by
  unfold polynomial
  simp_rw [fourier_coe_apply]
  apply ContDiff.sum
  intro k hk
  apply contDiff_const.mul
  apply (GaussianTest.contDiff_cexp n).comp
  exact (contDiff_const.mul (GaussianTest.contDiff_ofReal n)).div_const _

lemma Bound.mono {E D : ℝ} {f : ℝ → ℂ} (hf : Bound E f) (hED : E ≤ D) : Bound D f := by
  have hm (u : ℝ) : E*envelope 3 u ≤ D*envelope 3 u :=
    mul_le_mul_of_nonneg_right hED (Real.exp_pos _).le
  exact ⟨hf.smooth, fun u => (hf.zero u).trans (hm u),
    fun u => (hf.first u).trans (hm u), fun u => (hf.second u).trans (hm u)⟩

/-- A periodic C² function admits a finite Fourier polynomial whose Gaussian-damped
error is arbitrarily small in the exponential C² topology. -/
theorem exists_damped_polynomial_approx {a P ε : ℝ} (ha : 0 < a) (hP : 0 < P)
    (hε : 0 < ε) {H : ℝ → ℂ} (hH : ContDiff ℝ 2 H)
    (hp : Function.Periodic H P) :
    ∃ s : Finset ℤ, ∃ c : ℤ → ℂ,
      Bound ε (fun u => (H u-polynomial P s c u)*GaussianTest.gauss a 0 u) := by
  obtain ⟨K, hK, hmul⟩ := FleetGaussianMultiplier.exists_multiplier_bound ha
  let δ : ℝ := ε/(K+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hdH : Differentiable ℝ H := hH.differentiable (by norm_num)
  have hcH' : ContDiff ℝ 1 (deriv H) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1+1) H from hH)).2.2
  have hdH' := hcH'.differentiable (by norm_num)
  have hcH'' : Continuous (deriv (deriv H)) := hcH'.continuous_deriv le_rfl
  obtain ⟨s, c, hb⟩ := FleetPeriodicC2Density.exists_finite_polynomial_C2_approx
    hP hp hdH hdH' hcH'' hδ
  let Q := polynomial P s c
  have hQ : ContDiff ℝ 2 Q := polynomial_contDiff P s c 2
  have hdQ := hQ.differentiable (by norm_num)
  have hdQ' : Differentiable ℝ (deriv Q) :=
    ((contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1+1) Q from hQ)).2.2).differentiable (by norm_num)
  have he : deriv (fun u => H u-Q u) = fun u => deriv H u-deriv Q u := by
    ext u
    exact deriv_sub (hdH u) (hdQ u)
  have h0 : ∀ u, ‖H u-Q u‖ ≤ δ := fun u => (hb u).1
  have h1 : ∀ u, ‖deriv (fun u => H u-Q u) u‖ ≤ δ := by
    intro u
    rw [he]
    exact (hb u).2.1
  have h2 : ∀ u, ‖deriv (deriv (fun u => H u-Q u)) u‖ ≤ δ := by
    intro u
    rw [he, deriv_fun_sub (hdH' u) (hdQ' u)]
    exact (hb u).2.2
  have hm := hmul δ (fun u => H u-Q u) hδ.le (hH.sub hQ) h0 h1 h2
  have hKδ : K*δ ≤ ε := by
    have heq : δ*(K+1) = ε := div_mul_cancel₀ _ (by positivity)
    nlinarith
  exact ⟨s, c, Bound.mono hm hKδ⟩

end FleetDampedPeriodicApproximation
