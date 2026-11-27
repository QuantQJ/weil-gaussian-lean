import FleetGaussianEnvelopeTail
import FleetArithmeticContinuity
import FleetGaussianMultiplier

noncomputable section
open Filter Topology
namespace FleetGaussianPeriodizationTail
open FleetExponentialEnvelope FleetArithmeticContinuity

/-- A Gaussian-polynomial bound whose function vanishes in a sufficiently large
central interval gives a small exponential envelope globally. -/
theorem exists_uniform_tail_envelope {a C ε : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (hε : 0 < ε) (k : ℕ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ f : ℝ → ℂ,
      (∀ u, |u| < R → f u = 0) →
      (∀ u, ‖f u‖ ≤ C*(1+|u|)^k*Real.exp (-a*u^2)) →
      ∀ u, ‖f u‖ ≤ ε*envelope 3 u := by
  obtain ⟨R, hR, htail⟩ := FleetGaussianEnvelopeTail.exists_tail_bound ha k
    (div_pos hε (by positivity : 0 < C+1))
  refine ⟨R, hR, ?_⟩
  intro f hz hb u
  by_cases hu : |u| < R
  · rw [hz u hu, norm_zero]
    exact mul_nonneg hε.le (Real.exp_pos _).le
  · have ht := (htail u (le_of_not_gt hu)).le
    have he : (-a*u^2+3*|u|)+(-3*|u|) = -a*u^2 := by ring
    have hcoeff : C*((1+|u|)^k*Real.exp (-a*u^2+3*|u|)) ≤ ε := by
      have hh := mul_le_mul_of_nonneg_left ht hC
      have hd : (ε/(C+1))*(C+1) = ε := div_mul_cancel₀ _ (by positivity)
      have hpos : 0 ≤ ε/(C+1) := le_of_lt (div_pos hε (by positivity))
      nlinarith
    calc
      ‖f u‖ ≤ C*(1+|u|)^k*Real.exp (-a*u^2) := hb u
      _ = (C*((1+|u|)^k*Real.exp (-a*u^2+3*|u|)))*envelope 3 u := by
        simp only [envelope, mul_assoc, ← Real.exp_add, he]
      _ ≤ ε*envelope 3 u := mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le

/-- One radius works for every C² error with the same Gaussian-polynomial
majorant and zero function/first/second derivatives in the central interval. -/
theorem exists_C2_tail_Bound {a C ε : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (hε : 0 < ε) (k : ℕ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ f : ℝ → ℂ, ContDiff ℝ 2 f →
      (∀ u, |u| < R → f u = 0 ∧ deriv f u = 0 ∧ deriv (deriv f) u = 0) →
      (∀ u, ‖f u‖ ≤ C*(1+|u|)^k*Real.exp (-a*u^2) ∧
        ‖deriv f u‖ ≤ C*(1+|u|)^k*Real.exp (-a*u^2) ∧
        ‖deriv (deriv f) u‖ ≤ C*(1+|u|)^k*Real.exp (-a*u^2)) → Bound ε f := by
  obtain ⟨R, hR, hb⟩ := exists_uniform_tail_envelope ha hC hε k
  refine ⟨R, hR, ?_⟩
  intro f hf hz hm
  exact ⟨hf, hb f (fun u hu => (hz u hu).1) (fun u => (hm u).1),
    hb (deriv f) (fun u hu => (hz u hu).2.1) (fun u => (hm u).2.1),
    hb (deriv (deriv f)) (fun u hu => (hz u hu).2.2) (fun u => (hm u).2.2)⟩

/-- Equality to zero on an open central interval also forces both derivatives to zero there. -/
lemma derivatives_zero_of_central_zero {f : ℝ → ℂ} {R : ℝ}
    (hz : ∀ u, |u| < R → f u = 0) (u : ℝ) (hu : |u| < R) :
    f u = 0 ∧ deriv f u = 0 ∧ deriv (deriv f) u = 0 := by
  have he : f =ᶠ[nhds u] (fun _ => (0 : ℂ)) := by
    have hh : ∀ᶠ v : ℝ in nhds u, |v| < R :=
      continuous_abs.continuousAt (gt_mem_nhds hu)
    filter_upwards [hh] with v hv
    exact hz v hv
  refine ⟨hz u hu, ?_, ?_⟩
  · simpa only [deriv_const] using he.deriv_eq
  · have hd0 : deriv (fun _ : ℝ => (0 : ℂ)) = fun _ => 0 := by ext v; simp
    simpa only [hd0, deriv_const] using he.deriv.deriv_eq

/-- Gaussian damping turns any uniformly bounded C² central-zero error into
an arbitrarily small exponential C² error; the radius is uniform over the error. -/
theorem exists_gaussian_error_tail {a C ε : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (hε : 0 < ε) : ∃ R : ℝ, 0 ≤ R ∧ ∀ H : ℝ → ℂ,
      ContDiff ℝ 2 H → (∀ u, |u| < R → H u = 0) →
      (∀ u, ‖H u‖ ≤ C) → (∀ u, ‖deriv H u‖ ≤ C) →
      (∀ u, ‖deriv (deriv H) u‖ ≤ C) →
      Bound ε (fun u => H u*GaussianTest.gauss a 0 u) := by
  obtain ⟨R, hR, hb⟩ := exists_C2_tail_Bound ha
    (by positivity : 0 ≤ 4*C*(1+2*a+4*a^2)) hε 2
  refine ⟨R, hR, ?_⟩
  intro H hH hz h0 h1 h2
  apply hb (fun u => H u*GaussianTest.gauss a 0 u)
    (hH.mul (GaussianTest.gauss_contDiff a 0 2))
  · apply derivatives_zero_of_central_zero
    intro u hu
    rw [hz u hu, zero_mul]
  · exact FleetGaussianMultiplier.pointwise_polynomial_bound ha hC hH h0 h1 h2

/-- Uniform gluing interface for a function and its periodic replacement. -/
theorem exists_gaussian_gluing_radius {a C ε : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (hε : 0 < ε) : ∃ R : ℝ, 0 ≤ R ∧ ∀ F P : ℝ → ℂ,
      ContDiff ℝ 2 F → ContDiff ℝ 2 P →
      (∀ u, |u| < R → F u = P u) →
      (∀ u, ‖F u‖ ≤ C ∧ ‖deriv F u‖ ≤ C ∧ ‖deriv (deriv F) u‖ ≤ C) →
      (∀ u, ‖P u‖ ≤ C ∧ ‖deriv P u‖ ≤ C ∧ ‖deriv (deriv P) u‖ ≤ C) →
      Bound ε (fun u => (F u-P u)*GaussianTest.gauss a 0 u) := by
  obtain ⟨R, hR, hb⟩ := exists_gaussian_error_tail ha (by positivity : 0 ≤ 2*C) hε
  refine ⟨R, hR, ?_⟩
  intro F P hF hP he hFb hPb
  have hdF := hF.differentiable (by norm_num)
  have hdP := hP.differentiable (by norm_num)
  have hdF' : Differentiable ℝ (deriv F) :=
    ((contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1+1) F from hF)).2.2).differentiable (by norm_num)
  have hdP' : Differentiable ℝ (deriv P) :=
    ((contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1+1) P from hP)).2.2).differentiable (by norm_num)
  have hd : deriv (fun u => F u-P u) = fun u => deriv F u-deriv P u := by
    ext u
    exact deriv_sub (hdF u) (hdP u)
  apply hb (fun u => F u-P u) (hF.sub hP)
  · intro u hu
    rw [he u hu, sub_self]
  · intro u
    exact (norm_sub_le _ _).trans (by linarith [(hFb u).1, (hPb u).1])
  · intro u
    rw [hd]
    exact (norm_sub_le _ _).trans (by linarith [(hFb u).2.1, (hPb u).2.1])
  · intro u
    rw [hd, deriv_fun_sub (hdF' u) (hdP' u)]
    exact (norm_sub_le _ _).trans (by linarith [(hFb u).2.2, (hPb u).2.2])

end FleetGaussianPeriodizationTail
