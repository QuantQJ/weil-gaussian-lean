import FleetGaussianDictionaryMember
import Mathlib

noncomputable section
open MeasureTheory

namespace FleetGaussianArchimedeanNormalization

/-- The scalar integral evaluated by the numerical certificate, before its
normalizing factor. -/
def shiftedIntegral (q : ℝ) : ℝ :=
  ∫ u : ℝ, Real.exp (-u^2) * FleetGammaKernel.weight (q+2*u)

lemma integral_change_variables (q : ℝ) :
    (∫ t : ℝ, Real.exp (-(t-q)^2/4) * FleetGammaKernel.weight t) =
      2 * shiftedIntegral q := by
  let f : ℝ → ℝ := fun t => Real.exp (-(t-q)^2/4) * FleetGammaKernel.weight t
  have hs := Measure.integral_comp_mul_left (fun t : ℝ => f (q+t)) 2
  rw [integral_add_left_eq_self f q] at hs
  have he : (fun x : ℝ => f (q+2*x)) =
      (fun x : ℝ => Real.exp (-x^2) * FleetGammaKernel.weight (q+2*x)) := by
    funext x
    dsimp [f]
    congr 2
    ring
  change (∫ x : ℝ, f (q+2*x)) = _ at hs
  rw [he] at hs
  norm_num [abs_div] at hs
  change (∫ t : ℝ, f t) = 2 * shiftedIntegral q
  unfold shiftedIntegral
  linarith

/-- Exact normalization of the original complex archimedean functional into
the real Gaussian integral used by the finite numerical calculation. -/
theorem archimedean_gauss_one (q : ℝ) :
    FleetFullLineArithmetic.archimedean (GaussianTest.gauss 1 q) =
      (((1 / Real.sqrt Real.pi) * shiftedIntegral q : ℝ) : ℂ) := by
  unfold FleetFullLineArithmetic.archimedean
  simp_rw [FleetGaussianDictionaryMember.h_eq_gaussHat,
    GaussianTest.gaussHat_real (by norm_num : (0 : ℝ) < 1)]
  norm_num only [div_one, mul_one]
  simp_rw [← Complex.ofReal_mul]
  rw [integral_complex_ofReal]
  have he : (fun t : ℝ =>
      (Real.sqrt Real.pi * Real.exp (-(t-q)^2/4)) * FleetGammaKernel.weight t) =
      (fun t : ℝ => Real.sqrt Real.pi *
        (Real.exp (-(t-q)^2/4) * FleetGammaKernel.weight t)) := by
    funext t
    ring
  rw [he, MeasureTheory.integral_const_mul, integral_change_variables]
  have hs : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  have hsq := Real.sq_sqrt Real.pi_pos.le
  push_cast
  have hc : (Real.sqrt Real.pi : ℂ)^2 = (Real.pi : ℂ) := by exact_mod_cast hsq
  have hc0 : (Real.sqrt Real.pi : ℂ) ≠ 0 := by exact_mod_cast hs
  have hp0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  linear_combination (shiftedIntegral q : ℂ) * hc

end FleetGaussianArchimedeanNormalization
