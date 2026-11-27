import Mathlib

noncomputable section
namespace FleetExponentialEnvelope
open MeasureTheory Real

def envelope (b u : ℝ) : ℝ := Real.exp (-b * |u|)

theorem integral_envelope {b : ℝ} (hb : 0 < b) :
    (∫ u, envelope b u) = 2 / b := by
  unfold envelope
  rw [integral_comp_abs (f := fun u => Real.exp (-b*u))]
  have h := integral_exp_neg_mul_rpow (p := (1 : ℝ)) zero_lt_one hb
  simpa [Real.rpow_one, Real.rpow_neg_one, Real.Gamma_add_one, Real.Gamma_one,
    div_eq_mul_inv] using congrArg (fun x : ℝ => 2*x) h

theorem integrable_envelope {b : ℝ} (hb : 0 < b) : Integrable (envelope b) := by
  by_contra hn
  have h := integral_undef hn
  rw [integral_envelope hb] at h
  exact (ne_of_gt (div_pos (by norm_num : (0:ℝ)<2) hb)) h

theorem integrable_of_bound {f : ℝ → ℂ} {E b : ℝ} (hb : 0 < b) (hE : 0 ≤ E)
    (hf : AEStronglyMeasurable f) (hbound : ∀ u, ‖f u‖ ≤ E * envelope b u) :
    Integrable f := by
  apply ((integrable_envelope hb).const_mul E).mono' hf
  exact Filter.Eventually.of_forall hbound

theorem integral_norm_le {f : ℝ → ℂ} {E b : ℝ} (hb : 0 < b) (hE : 0 ≤ E)
    (hf : AEStronglyMeasurable f) (hbound : ∀ u, ‖f u‖ ≤ E * envelope b u) :
    (∫ u, ‖f u‖) ≤ 2 * E / b := by
  have hi := integrable_of_bound hb hE hf hbound
  calc
    (∫ u, ‖f u‖) ≤ ∫ u, E * envelope b u :=
      integral_mono hi.norm ((integrable_envelope hb).const_mul E) hbound
    _ = 2 * E / b := by rw [MeasureTheory.integral_const_mul, integral_envelope hb]; ring

theorem tilted_bound {f : ℝ → ℂ} {E b δ : ℝ} (hE : 0 ≤ E)
    (hbound : ∀ u, ‖f u‖ ≤ E * envelope b u) (u : ℝ) :
    ‖f u * Complex.exp ((δ : ℂ) * (u : ℂ))‖ ≤ E * envelope (b - |δ|) u := by
  rw [norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  calc
    ‖f u‖ * Real.exp (δ*u) ≤ (E * envelope b u) * Real.exp (δ*u) :=
      mul_le_mul_of_nonneg_right (hbound u) (Real.exp_pos _).le
    _ = E * Real.exp (-b * |u| + δ*u) := by rw [envelope, Real.exp_add]; ring
    _ ≤ E * Real.exp (-(b-|δ|)*|u|) := by
      apply mul_le_mul_of_nonneg_left _ hE
      apply Real.exp_le_exp.mpr
      have h := le_abs_self (δ*u)
      rw [abs_mul] at h
      nlinarith
    _ = E * envelope (b-|δ|) u := rfl

theorem integrable_tilted {f : ℝ → ℂ} {E b δ : ℝ} (hδ : |δ| < b) (hE : 0 ≤ E)
    (hf : AEStronglyMeasurable f) (hbound : ∀ u, ‖f u‖ ≤ E * envelope b u) :
    Integrable (fun u : ℝ => f u * Complex.exp ((δ : ℂ) * (u : ℂ))) := by
  apply integrable_of_bound (sub_pos.mpr hδ) hE
  · exact hf.mul (by fun_prop : Continuous (fun u : ℝ => Complex.exp ((δ : ℂ) * (u : ℂ)))).aestronglyMeasurable
  · exact tilted_bound hE hbound

theorem integral_norm_tilted_le {f : ℝ → ℂ} {E b δ : ℝ} (hδ : |δ| < b) (hE : 0 ≤ E)
    (hf : AEStronglyMeasurable f) (hbound : ∀ u, ‖f u‖ ≤ E * envelope b u) :
    (∫ u : ℝ, ‖f u * Complex.exp ((δ : ℂ) * (u : ℂ))‖) ≤ 2 * E / (b - |δ|) := by
  apply integral_norm_le (sub_pos.mpr hδ) hE
  · exact hf.mul (by fun_prop : Continuous (fun u : ℝ => Complex.exp ((δ : ℂ) * (u : ℂ)))).aestronglyMeasurable
  · exact tilted_bound hE hbound

end FleetExponentialEnvelope
#print axioms FleetExponentialEnvelope.integral_envelope

#print axioms FleetExponentialEnvelope.integrable_tilted
#print axioms FleetExponentialEnvelope.integral_norm_tilted_le
