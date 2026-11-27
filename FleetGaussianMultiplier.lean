import FleetGaussianDictionaryMember

noncomputable section
namespace FleetGaussianMultiplier
open GaussianTest FleetArithmeticContinuity FleetExponentialEnvelope

/-- Multiplication by a fixed Gaussian converts uniform C² control to exponential C² control. -/
theorem exists_multiplier_bound {a : ℝ} (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (δ : ℝ) (H : ℝ → ℂ), 0 ≤ δ → ContDiff ℝ 2 H →
      (∀ u, ‖H u‖ ≤ δ) → (∀ u, ‖deriv H u‖ ≤ δ) →
      (∀ u, ‖deriv (deriv H) u‖ ≤ δ) →
      Bound (K*δ) (fun u => H u * gauss a 0 u) := by
  obtain ⟨E, hE, hG⟩ := FleetGaussianDictionaryMember.exists_bound ha 0
  refine ⟨4*E, by positivity, ?_⟩
  intro δ H hδ hH h0 h1 h2
  let G := gauss a 0
  have hdH := hH.differentiable (by norm_num)
  have hdG := hG.smooth.differentiable (by norm_num)
  have hdH' : Differentiable ℝ (deriv H) :=
    ((contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1+1) H from hH)).2.2).differentiable (by norm_num)
  have hdG' : Differentiable ℝ (deriv G) :=
    ((contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1+1) G from hG.smooth)).2.2).differentiable (by norm_num)
  have d1 : deriv (fun u => H u * G u) = fun u => deriv H u * G u + H u * deriv G u := by
    funext u
    exact ((hdH u).hasDerivAt.mul (hdG u).hasDerivAt).deriv
  have d2 : deriv (deriv (fun u => H u * G u)) = fun u =>
      deriv (deriv H) u * G u + deriv H u * deriv G u +
        (deriv H u * deriv G u + H u * deriv (deriv G) u) := by
    rw [d1]
    funext u
    exact (((hdH' u).hasDerivAt.mul (hdG u).hasDerivAt).add
      ((hdH u).hasDerivAt.mul (hdG' u).hasDerivAt)).deriv
  have hp {x y : ℂ} {u : ℝ} (hx : ‖x‖ ≤ δ) (hy : ‖y‖ ≤ E*envelope 3 u) :
      ‖x*y‖ ≤ δ*(E*envelope 3 u) := by
    rw [norm_mul]
    exact mul_le_mul hx hy (norm_nonneg _) hδ
  have he (u : ℝ) : 0 ≤ E*envelope 3 u := mul_nonneg hE (Real.exp_pos _).le
  refine ⟨hH.mul hG.smooth, ?_, ?_, ?_⟩
  · intro u
    have hh := hp (h0 u) (hG.zero u)
    change ‖H u*G u‖ ≤ _
    nlinarith [mul_nonneg hδ (he u)]
  · intro u
    change ‖deriv (fun u => H u*G u) u‖ ≤ _
    rw [d1]
    have hh := (norm_add_le _ _).trans (add_le_add (hp (h1 u) (hG.zero u)) (hp (h0 u) (hG.first u)))
    nlinarith [mul_nonneg hδ (he u)]
  · intro u
    change ‖deriv (deriv (fun u => H u*G u)) u‖ ≤ _
    rw [d2]
    have hh := (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (hp (h2 u) (hG.zero u)) (hp (h1 u) (hG.first u))))
      ((norm_add_le _ _).trans (add_le_add (hp (h1 u) (hG.first u)) (hp (h0 u) (hG.second u)))))
    nlinarith


/-- Pointwise polynomial-Gaussian control retaining the tail rate. -/
theorem pointwise_polynomial_bound {a δ : ℝ} (ha : 0 < a) (hδ : 0 ≤ δ)
    {H : ℝ → ℂ} (hH : ContDiff ℝ 2 H)
    (h0 : ∀ u, ‖H u‖ ≤ δ) (h1 : ∀ u, ‖deriv H u‖ ≤ δ)
    (h2 : ∀ u, ‖deriv (deriv H) u‖ ≤ δ) (u : ℝ) :
    let B := 4*δ*(1+2*a+4*a^2)*(1+|u|)^2*Real.exp (-a*u^2)
    ‖H u*gauss a 0 u‖ ≤ B ∧
    ‖deriv (fun u => H u*gauss a 0 u) u‖ ≤ B ∧
    ‖deriv (deriv (fun u => H u*gauss a 0 u)) u‖ ≤ B := by
  obtain ⟨E, hE, hG⟩ := FleetGaussianDictionaryMember.exists_bound ha 0
  let G := gauss a 0
  have hdH := hH.differentiable (by norm_num)
  have hdG := hG.smooth.differentiable (by norm_num)
  have hdH' : Differentiable ℝ (deriv H) :=
    ((contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1+1) H from hH)).2.2).differentiable (by norm_num)
  have hdG' : Differentiable ℝ (deriv G) :=
    ((contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1+1) G from hG.smooth)).2.2).differentiable (by norm_num)
  have d1 : deriv (fun u => H u * G u) = fun u => deriv H u * G u + H u * deriv G u := by
    funext u
    exact ((hdH u).hasDerivAt.mul (hdG u).hasDerivAt).deriv
  have d2 : deriv (deriv (fun u => H u * G u)) = fun u =>
      deriv (deriv H) u * G u + deriv H u * deriv G u +
        (deriv H u * deriv G u + H u * deriv (deriv G) u) := by
    rw [d1]
    funext u
    exact (((hdH' u).hasDerivAt.mul (hdG u).hasDerivAt).add
      ((hdH u).hasDerivAt.mul (hdG' u).hasDerivAt)).deriv

  let Q : ℝ := (1+2*a+4*a^2)*(1+|u|)^2
  let W : ℝ := Q*Real.exp (-a*u^2)
  have hu := abs_nonneg u
  have hsq : u^2 = |u|^2 := (sq_abs u).symm
  have hq0 : 1 ≤ Q := by dsimp [Q]; nlinarith [sq_nonneg a, sq_nonneg |u|, mul_nonneg ha.le hu]
  have hq1 : 2*a*|u| ≤ Q := by dsimp [Q]; nlinarith [sq_nonneg a, sq_nonneg |u|, sq_nonneg (a*|u|)]
  have hq2 : 2*a+4*a^2*u^2 ≤ Q := by dsimp [Q]; rw [hsq]; nlinarith [sq_nonneg a, sq_nonneg |u|, mul_nonneg ha.le hu]
  have w0 : ‖G u‖ ≤ W := by
    rw [norm_gauss]
    exact le_mul_of_one_le_left (Real.exp_pos _).le hq0
  have w1 : ‖deriv G u‖ ≤ W := by
    rw [FleetGaussianDictionaryMember.deriv_gauss, norm_mul, norm_gauss]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have hh : ‖gaussD a 0 u‖ ≤ 2*a*|u| := by simpa using norm_gaussD_le ha 0 u
    exact hh.trans hq1
  have w2 : ‖deriv (deriv G) u‖ ≤ W := by
    have hh := FleetGaussianDictionaryMember.norm_deriv2_le ha 0 u
    simp only [abs_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero, mul_zero, zero_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hq2 (Real.exp_pos _).le)
  have hp {x y : ℂ} (hx : ‖x‖ ≤ δ) (hy : ‖y‖ ≤ W) : ‖x*y‖ ≤ δ*W := by
    rw [norm_mul]
    exact mul_le_mul hx hy (norm_nonneg _) hδ
  have hW : 0 ≤ δ*W := mul_nonneg hδ ((norm_nonneg _).trans w0)
  have hv : 4*δ*(1+2*a+4*a^2)*(1+|u|)^2*Real.exp (-a*u^2) = 4*(δ*W) := by dsimp [W,Q]; ring
  dsimp only
  rw [hv]
  refine ⟨?_, ?_, ?_⟩
  · have hh := hp (h0 u) w0
    change ‖H u*G u‖ ≤ _
    linarith
  · change ‖deriv (fun u => H u*G u) u‖ ≤ _
    rw [d1]
    have hh := (norm_add_le _ _).trans (add_le_add (hp (h1 u) w0) (hp (h0 u) w1))
    linarith
  · change ‖deriv (deriv (fun u => H u*G u)) u‖ ≤ _
    rw [d2]
    have hh := (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (hp (h2 u) w0) (hp (h1 u) w1)))
      ((norm_add_le _ _).trans (add_le_add (hp (h1 u) w1) (hp (h0 u) w2))))
    linarith

end FleetGaussianMultiplier
#print axioms FleetGaussianMultiplier.exists_multiplier_bound
#print axioms FleetGaussianMultiplier.pointwise_polynomial_bound
