import FleetTrigDensity

noncomputable section
open Set MeasureTheory AddCircle FleetTrigPrimitive FleetPeriodicApproximation
open scoped BigOperators
namespace FleetPeriodicC2Density

lemma circleLift_continuous {H : ℝ → ℂ} {P : ℝ} (hp : Function.Periodic H P)
    (hc : Continuous H) : Continuous hp.lift := by
  exact continuous_coinduced_dom.2 hc

/-- Periodic second derivatives have mean zero on the normalized circle. -/
lemma second_derivative_mean_zero {H : ℝ → ℂ} {P : ℝ} [Fact (0 < P)]
    (hp : Function.Periodic H P) (hdd : Differentiable ℝ (deriv H))
    (hc : Continuous (deriv (deriv H))) :
    (∫ t : AddCircle P, (periodic_deriv (periodic_deriv hp)).lift t ∂haarAddCircle) = 0 := by
  let F : AddCircle P → ℂ := (periodic_deriv (periodic_deriv hp)).lift
  have he := fourierCoeff_eq_intervalIntegral F 0 (0 : ℝ)
  have hint : (∫ t in (0 : ℝ)..P, deriv (deriv H) t) = 0 := by
    rw [intervalIntegral.integral_deriv_eq_sub (fun t _ => hdd t)
      (hc.intervalIntegrable 0 P)]
    have hp' := periodic_deriv hp
    have hv : deriv H P = deriv H 0 := by simpa using hp' 0
    rw [hv, sub_self]
  simpa [fourierCoeff, fourier_zero, F, hint] using he

/-- Full C² approximation by a finite Fourier polynomial, expressed as an
explicit constant plus the finite second primitive. -/
theorem exists_periodic_C2_approx {H : ℝ → ℂ} {P : ℝ} (hP : 0 < P)
    (hp : Function.Periodic H P) (hd : Differentiable ℝ H)
    (hdd : Differentiable ℝ (deriv H)) (hc : Continuous (deriv (deriv H)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset ℤ, ∃ c : ℤ → ℂ, ∃ A : ℂ, c 0 = 0 ∧
      let Q : ℝ → ℂ := fun t => doublePrimitive P s c t + A
      ∀ t, ‖H t - Q t‖ ≤ ε ∧ ‖deriv H t - deriv Q t‖ ≤ ε ∧
        ‖deriv (deriv H) t - deriv (deriv Q) t‖ ≤ ε := by
  letI : Fact (0 < P) := ⟨hP⟩
  let δ : ℝ := ε / (1 + P + P^2)
  have hδ : 0 < δ := div_pos hε (by positivity)
  let F : C(AddCircle P, ℂ) :=
    ⟨(periodic_deriv (periodic_deriv hp)).lift,
      circleLift_continuous (periodic_deriv (periodic_deriv hp)) hc⟩
  obtain ⟨s, c, hc0, _, hclose⟩ := FleetTrigDensity.exists_zero_mean_fourier_approx
    F (second_derivative_mean_zero hp hdd hc) hδ
  let D := doublePrimitive P s c
  have hD : Differentiable ℝ D := fun t =>
    (hasDerivAt_doublePrimitive hP s c t).differentiableAt
  have hD' : deriv D = primitive P s c := deriv_doublePrimitive hP s c
  have hDd : Differentiable ℝ (deriv D) := by
    rw [hD']
    exact fun t => (hasDerivAt_primitive hP s c hc0 t).differentiableAt
  have hD'' : deriv (deriv D) = polynomial P s c := doublePrimitive_second_deriv hP s c hc0
  let A : ℂ := (P : ℂ)⁻¹ * (∫ t in (0 : ℝ)..P, H t - D t)
  let Q : ℝ → ℂ := fun t => D t + A
  have hQ : Differentiable ℝ Q := hD.add_const A
  have hQ' : deriv Q = deriv D := by ext t; exact deriv_add_const A
  have hQd : Differentiable ℝ (deriv Q) := hQ' ▸ hDd
  let E : ℝ → ℂ := fun t => H t - Q t
  have hE : Differentiable ℝ E := hd.sub hQ
  have hE' : deriv E = fun t => deriv H t - deriv Q t := by
    ext t
    exact deriv_sub (hd t) (hQ t)
  have hEd : Differentiable ℝ (deriv E) := hE' ▸ hdd.sub hQd
  have hE'' : deriv (deriv E) = fun t => deriv (deriv H) t - polynomial P s c t := by
    rw [hE']
    ext t
    rw [deriv_fun_sub (hdd t) (hQd t), hQ', hD'']
  have hDp : Function.Periodic D P :=
    periodic_polynomial P s (fun k => c k / frequency P k / frequency P k)
  have hQp : Function.Periodic Q P := by
    intro t
    simp only [Q, hDp t]
  have hEp : Function.Periodic E P := hp.sub hQp
  have hmean : (∫ t in (0 : ℝ)..P, E t) = 0 := by
    have he : E = fun t => (H t - D t) - A := by ext t; dsimp [E, Q]; ring
    rw [he]
    show ∫ t in (0 : ℝ)..P, (H t - D t) - A = 0
    rw [intervalIntegral.integral_sub (f := fun t => H t - D t)
      ((hd.continuous.sub hD.continuous).intervalIntegrable 0 P) intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp only [sub_zero, Complex.real_smul, A]
    field_simp [ne_of_gt hP]
    ring
  have hsecond : ∀ t, ‖deriv (deriv E) t‖ ≤ δ := by
    intro t
    rw [hE'']
    exact (hclose (t : AddCircle P)).le
  obtain ⟨hfirst, hzero⟩ := norm_bounds_of_second_deriv hP hδ.le hEp hE hEd
    (fun t _ => hsecond t) hmean
  have hscale : δ * (1 + P + P^2) = ε := div_mul_cancel₀ _ (by positivity)
  have hδle : δ ≤ ε := by nlinarith [mul_nonneg hδ.le hP.le, mul_nonneg hδ.le (sq_nonneg P)]
  have hPle : P * δ ≤ ε := by nlinarith [mul_nonneg hδ.le (sq_nonneg P)]
  have hP2le : P^2 * δ ≤ ε := by nlinarith [mul_nonneg hδ.le hP.le]
  refine ⟨s, c, A, hc0, fun t => ⟨(hzero t).trans hP2le, ?_, ?_⟩⟩
  · have h := (hfirst t).trans hPle
    simpa only [hE'] using h
  · change ‖deriv (deriv H) t - deriv (deriv Q) t‖ ≤ ε
    rw [hQ', hD'']
    have h := (hsecond t).trans hδle
    simpa only [hE''] using h

lemma doublePrimitive_add_constant_eq_polynomial (P : ℝ) (s : Finset ℤ)
    (c : ℤ → ℂ) (A : ℂ) :
    (fun t => doublePrimitive P s c t + A) =
      polynomial P (insert 0 s) (fun k => c k / frequency P k / frequency P k +
        if k = 0 then A else 0) := by
  classical
  ext t
  by_cases h0 : (0 : ℤ) ∈ s
  · simp [polynomial, doublePrimitive, primitive, add_mul, Finset.sum_add_distrib,
      h0, fourier_zero, Finset.sum_ite_eq']
  · simp [polynomial, doublePrimitive, primitive, add_mul, Finset.sum_add_distrib,
      h0, fourier_zero, Finset.sum_ite_eq', frequency]

/-- Periodic C² functions admit ordinary finite Fourier polynomial
approximants with simultaneous global error bounds through derivative order two. -/
theorem exists_finite_polynomial_C2_approx {H : ℝ → ℂ} {P : ℝ} (hP : 0 < P)
    (hp : Function.Periodic H P) (hd : Differentiable ℝ H)
    (hdd : Differentiable ℝ (deriv H)) (hc : Continuous (deriv (deriv H)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset ℤ, ∃ c : ℤ → ℂ,
      let Q := polynomial P s c
      ∀ t, ‖H t - Q t‖ ≤ ε ∧ ‖deriv H t - deriv Q t‖ ≤ ε ∧
        ‖deriv (deriv H) t - deriv (deriv Q) t‖ ≤ ε := by
  obtain ⟨s, c, A, _, h⟩ := exists_periodic_C2_approx hP hp hd hdd hc hε
  refine ⟨insert 0 s, (fun k => c k / frequency P k / frequency P k +
    if k = 0 then A else 0), ?_⟩
  change ∀ t, ‖H t - polynomial P (insert 0 s) _ t‖ ≤ ε ∧ _
  rw [← doublePrimitive_add_constant_eq_polynomial]
  exact h

end FleetPeriodicC2Density
