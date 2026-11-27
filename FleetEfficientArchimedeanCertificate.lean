import FleetDigammaEfficientCertificate
import FleetArchimedeanTailCertificate

/-! The accelerated finite digamma formula can replace the actual kernel under
the normalized Gaussian integral with the same uniform error. -/

noncomputable section
namespace FleetEfficientArchimedeanCertificate
open Real Set MeasureTheory FleetDigammaEfficientCertificate

def efficientIntegrand (N : ℕ) (q u : ℝ) : ℝ :=
  exp (-u^2) * efficientWeightApprox N (q+2*u)

lemma measurable_efficientIntegrand (N : ℕ) (q : ℝ) :
    Measurable (efficientIntegrand N q) := by
  unfold efficientIntegrand efficientWeightApprox efficientPsiApprox
  fun_prop

lemma norm_integrand_sub_le (N : ℕ) (hN : 2 ≤ N) (q u : ℝ) :
    ‖FleetArchimedeanTailCertificate.integrand q u - efficientIntegrand N q u‖ ≤
      exp (-u^2) * (1/((N:ℝ)-1)^2) := by
  unfold FleetArchimedeanTailCertificate.integrand efficientIntegrand
  rw [← mul_sub, Real.norm_eq_abs, abs_mul, _root_.abs_of_pos (exp_pos _)]
  exact mul_le_mul_of_nonneg_left
    (abs_weight_sub_efficientWeightApprox_le N hN (q+2*u)) (exp_pos _).le

private lemma gaussian_integrable : Integrable (fun u : ℝ => exp (-u^2)) := by
  simpa using integrable_exp_neg_mul_sq (b := (1:ℝ)) (by norm_num)

lemma integrable_integrand_sub (N : ℕ) (hN : 2 ≤ N) (q : ℝ) :
    Integrable (fun u : ℝ =>
      FleetArchimedeanTailCertificate.integrand q u - efficientIntegrand N q u) := by
  have hm := FleetArchimedeanTailCertificate.continuous_integrand q
  apply (gaussian_integrable.mul_const (1/((N:ℝ)-1)^2)).mono'
    (hm.aestronglyMeasurable.sub (measurable_efficientIntegrand N q).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (norm_integrand_sub_le N hN q)

theorem integrable_efficientIntegrand (N : ℕ) (hN : 2 ≤ N) (q : ℝ) :
    Integrable (efficientIntegrand N q) := by
  have h := (FleetArchimedeanTailCertificate.integrable_integrand q).sub
    (integrable_integrand_sub N hN q)
  convert h using 1
  funext u
  dsimp only [Pi.sub_apply]
  ring

/-- Replacement on any measurable window, with no loss proportional to the
window length: the full Gaussian has mass `sqrt pi`. -/
theorem normalized_replacement_bound (N : ℕ) (hN : 2 ≤ N) (q : ℝ) (s : Set ℝ) :
    |(1/sqrt Real.pi) * (∫ u : ℝ in s, FleetArchimedeanTailCertificate.integrand q u) -
      (1/sqrt Real.pi) * (∫ u : ℝ in s, efficientIntegrand N q u)| ≤
        1/((N:ℝ)-1)^2 := by
  let E : ℝ := 1/((N:ℝ)-1)^2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hi := (integrable_integrand_sub N hN q).integrableOn (s := s)
  have hb := integral_mono_ae hi.norm
    ((gaussian_integrable.mul_const E).integrableOn (s := s))
    (Filter.Eventually.of_forall (norm_integrand_sub_le N hN q))
  rw [integral_mul_const] at hb
  have hg : (∫ u : ℝ in s, exp (-u^2)) ≤ sqrt Real.pi := by
    calc
      _ ≤ ∫ u : ℝ, exp (-u^2) := setIntegral_le_integral gaussian_integrable
        (Filter.Eventually.of_forall (fun u => (exp_pos (-u^2)).le))
      _ = sqrt Real.pi := by simpa using integral_gaussian (1:ℝ)
  have hb' := hb.trans (mul_le_mul_of_nonneg_right hg hE)
  have hn := norm_integral_le_integral_norm (fun u : ℝ =>
    FleetArchimedeanTailCertificate.integrand q u - efficientIntegrand N q u)
    (μ := volume.restrict s)
  rw [Real.norm_eq_abs] at hn
  have herr := hn.trans hb'
  rw [integral_sub (FleetArchimedeanTailCertificate.integrable_integrand q).integrableOn
    (integrable_efficientIntegrand N hN q).integrableOn] at herr
  rw [← mul_sub, abs_mul, _root_.abs_of_nonneg (show 0 ≤ 1/sqrt Real.pi by positivity)]
  calc
    _ ≤ (1/sqrt Real.pi) * (sqrt Real.pi * E) :=
      mul_le_mul_of_nonneg_left herr (by positivity)
    _ = E := by field_simp

theorem normalized_replacement_thirty_two (q : ℝ) :
    |(1/sqrt Real.pi) * (∫ u : ℝ in Ioc (-12) 12,
        FleetArchimedeanTailCertificate.integrand q u) -
      (1/sqrt Real.pi) * (∫ u : ℝ in Ioc (-12) 12, efficientIntegrand 32 q u)| ≤
        (1/961 : ℝ) := by
  convert normalized_replacement_bound 32 (by norm_num) q (Ioc (-12) 12) using 1
  norm_num

end FleetEfficientArchimedeanCertificate
