import FleetDigammaIntervalCertificate
import FleetGaussianTail
import FleetArchimedeanFunctionalBound
import Mathlib
import FleetElementaryNumericalInstances

/-!
# Explicit archimedean Gaussian tails

These enclosures concern the actual Gamma kernel. Their proofs use the finite
digamma series identification and the elementary exponential tangent envelope.
-/

noncomputable section
namespace FleetArchimedeanTailCertificate
open Real Set MeasureTheory

def normIntegrand (q u : ℝ) : ℝ :=
  exp (-u^2) * |FleetGammaKernel.weight (q + 2*u)|

def tailOffset (q U : ℝ) : ℝ := U + (22 + 10*|q|)/20

def oneSidedBound (q U : ℝ) : ℝ :=
  20 * exp (-U^2) * (tailOffset q U / (2*U) + 1 / (2*U)^2)

lemma continuous_normIntegrand (q : ℝ) : Continuous (normIntegrand q) := by
  have hw := FleetArchimedeanFunctionalBound.continuous_weight
  unfold normIntegrand
  fun_prop

lemma normIntegrand_nonneg (q u : ℝ) : 0 ≤ normIntegrand q u := by
  unfold normIntegrand
  positivity

theorem translated_envelope (q U v : ℝ) (hU : 0 ≤ U) (hv : 0 ≤ v) :
    normIntegrand q (U+v) ≤
      (20 * exp (-U^2)) * ((tailOffset q U + v) * exp (-(2*U)*v)) := by
  have ha := abs_add_le q (2*(U+v))
  rw [abs_mul, _root_.abs_of_pos (show (0:ℝ)<2 by norm_num),
    _root_.abs_of_nonneg (add_nonneg hU hv)] at ha
  have hw := FleetDigammaIntervalCertificate.abs_weight_le (q+2*(U+v))
  have hw' : |FleetGammaKernel.weight (q+2*(U+v))| ≤ 20*(tailOffset q U+v) := by
    unfold tailOffset
    linarith
  have hexp : exp (-(U+v)^2) ≤ exp (-U^2) * exp (-(2*U)*v) := by
    rw [← exp_add]
    apply exp_le_exp.mpr
    nlinarith [sq_nonneg v]
  unfold normIntegrand
  calc
    _ ≤ exp (-(U+v)^2) * (20*(tailOffset q U+v)) :=
      mul_le_mul_of_nonneg_left hw' (exp_pos _).le
    _ ≤ (exp (-U^2)*exp (-(2*U)*v)) * (20*(tailOffset q U+v)) :=
      mul_le_mul_of_nonneg_right hexp (by unfold tailOffset; positivity)
    _ = _ := by ring

private lemma integrable_linear_exp (L κ : ℝ) (hκ : 0 < κ) :
    IntegrableOn (fun v : ℝ => (L+v)*exp (-κ*v)) (Ioi 0) := by
  have h0 : IntegrableOn (fun v : ℝ => exp (-κ*v)) (Ioi 0) := by
    simpa using (integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := 0) (b := κ) (by norm_num) (by norm_num) hκ)
  have h1 : IntegrableOn (fun v : ℝ => v*exp (-κ*v)) (Ioi 0) := by
    simpa using (integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := 1) (b := κ) (by norm_num) (by norm_num) hκ)
  simp only [add_mul]
  exact (h0.const_mul L).add h1

theorem translated_tail (q U : ℝ) (hU : 0 < U) :
    IntegrableOn (fun v : ℝ => normIntegrand q (U+v)) (Ioi 0) ∧
      (∫ v : ℝ in Ioi 0, normIntegrand q (U+v)) ≤ oneSidedBound q U := by
  have hκ : 0 < 2*U := by positivity
  have hi := (integrable_linear_exp (tailOffset q U) (2*U) hκ).const_mul
    (20 * exp (-U^2))
  have hf : IntegrableOn (fun v : ℝ => normIntegrand q (U+v)) (Ioi 0) := by
    apply hi.mono' ((continuous_normIntegrand q).comp
      (continuous_const.add continuous_id)).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    change ‖normIntegrand q (U+v)‖ ≤ _
    rw [Real.norm_eq_abs, _root_.abs_of_nonneg (normIntegrand_nonneg q (U+v))]
    exact translated_envelope q U v hU.le hv.le
  refine ⟨hf, ?_⟩
  have hb := integral_mono_ae hf hi (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact translated_envelope q U v hU.le hv.le)
  rw [MeasureTheory.integral_const_mul,
    FleetGaussianTail.integral_linear_exp_tail (tailOffset q U) (2*U) hκ] at hb
  exact hb

/-- The positive Gaussian tail in the original integration variable. -/
theorem positive_tail (q U : ℝ) (hU : 0 < U) :
    IntegrableOn (normIntegrand q) (Ioi U) ∧
      (∫ u : ℝ in Ioi U, normIntegrand q u) ≤ oneSidedBound q U := by
  obtain ⟨hi, hb⟩ := translated_tail q U hU
  let H := (Ioi (0:ℝ)).indicator (fun v => normIntegrand q (U+v))
  have hshift : (fun u : ℝ => H (-U+u)) = (Ioi U).indicator (normIntegrand q) := by
    funext u
    by_cases hu : U < u
    · have hv : 0 < -U+u := by linarith
      simp [H, hu, hv, add_neg_cancel_left]
    · have hv : ¬0 < -U+u := by linarith
      simp [H, hu, hv]
  have hH : Integrable H := (integrable_indicator_iff measurableSet_Ioi).mpr hi
  have hfi : IntegrableOn (normIntegrand q) (Ioi U) := by
    apply (integrable_indicator_iff measurableSet_Ioi).mp
    rw [← hshift]
    exact hH.comp_add_left (-U)
  have he : (∫ u : ℝ in Ioi U, normIntegrand q u) =
      ∫ v : ℝ in Ioi 0, normIntegrand q (U+v) := by
    rw [← integral_indicator measurableSet_Ioi, ← hshift,
      integral_add_left_eq_self H (-U)]
    exact integral_indicator measurableSet_Ioi
  exact ⟨hfi, he.trans_le hb⟩

lemma normIntegrand_neg (q u : ℝ) : normIntegrand q (-u) = normIntegrand (-q) u := by
  unfold normIntegrand
  rw [neg_sq]
  have he : q + 2*(-u) = -(-q + 2*u) := by ring
  rw [he, FleetGammaKernel.weight_neg]

/-- The negative Gaussian tail; the endpoint does not affect the integral. -/
theorem negative_tail (q U : ℝ) (hU : 0 < U) :
    IntegrableOn (normIntegrand q) (Iic (-U)) ∧
      (∫ u : ℝ in Iic (-U), normIntegrand q u) ≤ oneSidedBound q U := by
  obtain ⟨hi, hb⟩ := positive_tail (-q) U hU
  have hi' := Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hi
  let H := (Ici U).indicator (normIntegrand (-q))
  have hH : Integrable H := (integrable_indicator_iff measurableSet_Ici).mpr hi'
  have he : (fun u : ℝ => H (-u)) = (Iic (-U)).indicator (normIntegrand q) := by
    funext u
    by_cases hu : u ≤ -U
    · have hv : U ≤ -u := by linarith
      simp [H, hu, hv, normIntegrand_neg]
    · have hv : ¬U ≤ -u := by linarith
      simp [H, hu, hv]
  have hf : IntegrableOn (normIntegrand q) (Iic (-U)) := by
    apply (integrable_indicator_iff measurableSet_Iic).mp
    rw [← he]
    exact hH.comp_neg
  refine ⟨hf, ?_⟩
  rw [← integral_comp_neg_Ioi U (normIntegrand q)]
  simp_rw [normIntegrand_neg]
  simpa [oneSidedBound, tailOffset] using hb

theorem two_sided_tail (q U : ℝ) (hU : 0 < U) :
    IntegrableOn (normIntegrand q) (Ioc (-U) U)ᶜ ∧
      (∫ u : ℝ in (Ioc (-U) U)ᶜ, normIntegrand q u) ≤ 2 * oneSidedBound q U := by
  have he : (Ioc (-U) U)ᶜ = Iic (-U) ∪ Ioi U := by
    ext u
    simp only [mem_compl_iff, mem_Ioc, mem_union, mem_Iic, mem_Ioi,
      not_and_or, not_lt, not_le]
  rw [he]
  obtain ⟨hiN, hbN⟩ := negative_tail q U hU
  obtain ⟨hiP, hbP⟩ := positive_tail q U hU
  refine ⟨integrableOn_union.mpr ⟨hiN, hiP⟩, ?_⟩
  have hd : Disjoint (Iic (-U)) (Ioi U) := by
    apply Set.disjoint_left.mpr
    intro u hu hu'
    have h1 : u ≤ -U := hu
    have h2 : U < u := hu'
    linarith
  rw [setIntegral_union hd measurableSet_Ioi hiN hiP]
  linarith

def integrand (q u : ℝ) : ℝ := exp (-u^2) * FleetGammaKernel.weight (q+2*u)

lemma continuous_integrand (q : ℝ) : Continuous (integrand q) := by
  have hw := FleetArchimedeanFunctionalBound.continuous_weight
  unfold integrand
  fun_prop

lemma norm_integrand (q u : ℝ) : ‖integrand q u‖ = normIntegrand q u := by
  simp [integrand, normIntegrand, Real.norm_eq_abs, abs_mul,
    _root_.abs_of_pos (exp_pos _)]

theorem integrable_normIntegrand (q : ℝ) : Integrable (normIntegrand q) := by
  have ht := (two_sided_tail q 1 (by norm_num)).1
  have hm : IntegrableOn (normIntegrand q) (Ioc (-1) 1) :=
    (continuous_normIntegrand q).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have h := integrableOn_union.mpr ⟨hm, ht⟩
  simpa only [union_compl_self, integrableOn_univ] using h

theorem integrable_integrand (q : ℝ) : Integrable (integrand q) := by
  apply (integrable_normIntegrand q).mono' (continuous_integrand q).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun u => (norm_integrand q u).le)

/-- The full-line integral differs from its finite window by a proved tail. -/
theorem truncation_bound (q U : ℝ) (hU : 0 < U) :
    |(∫ u : ℝ, integrand q u) - (∫ u : ℝ in Ioc (-U) U, integrand q u)| ≤
      2 * oneSidedBound q U := by
  rw [← setIntegral_compl measurableSet_Ioc (integrable_integrand q)]
  have hn := norm_integral_le_integral_norm (fun u : ℝ => integrand q u)
    (μ := volume.restrict (Ioc (-U) U)ᶜ)
  rw [Real.norm_eq_abs] at hn
  simp_rw [norm_integrand] at hn
  exact hn.trans (two_sided_tail q U hU).2

theorem normalized_truncation_bound (q U : ℝ) (hU : 0 < U) :
    |(1 / sqrt Real.pi) * (∫ u : ℝ, integrand q u) -
      (1 / sqrt Real.pi) * (∫ u : ℝ in Ioc (-U) U, integrand q u)| ≤
      (1 / sqrt Real.pi) * (2 * oneSidedBound q U) := by
  rw [← mul_sub, abs_mul,
    _root_.abs_of_nonneg (show 0 ≤ 1 / sqrt Real.pi by positivity)]
  exact mul_le_mul_of_nonneg_left (truncation_bound q U hU) (by positivity)

theorem twice_oneSidedBound_twelve_le {q : ℝ} (hq : |q| ≤ 100) :
    2 * oneSidedBound q 12 ≤ 106 * exp (-144) := by
  unfold oneSidedBound tailOffset
  norm_num
  nlinarith [exp_pos (-144), mul_le_mul_of_nonneg_right hq (exp_pos (-144)).le]

/-- Concrete, kernel-checked tail for the stage-100 archimedean integral.
The deliberately loose decimal bound uses a separately proved exponential
Taylor enclosure, not an external numerical certificate. -/
theorem normalized_truncation_twelve_le {q : ℝ} (hq : |q| ≤ 100) :
    |(1 / sqrt Real.pi) * (∫ u : ℝ, integrand q u) -
      (1 / sqrt Real.pi) * (∫ u : ℝ in Ioc (-12) 12, integrand q u)| ≤
        (1 / 10^21 : ℝ) := by
  have hsqrt : 1 ≤ sqrt Real.pi := by
    nlinarith [sq_sqrt pi_pos.le, sqrt_nonneg Real.pi, pi_gt_three]
  have hinv : 1 / sqrt Real.pi ≤ 1 := (div_le_one (sqrt_pos.2 pi_pos)).mpr hsqrt
  have hb := normalized_truncation_bound q 12 (by norm_num)
  have ht := twice_oneSidedBound_twelve_le hq
  have hpos : 0 ≤ 2 * oneSidedBound q 12 := by
    unfold oneSidedBound tailOffset
    positivity
  have hscale := mul_le_mul_of_nonneg_right hinv hpos
  have he := FleetElementaryNumericalInstances.exp_neg_144_le
  have hscale' : (1 / sqrt Real.pi) * (2 * oneSidedBound q 12) ≤
      2 * oneSidedBound q 12 := by simpa only [one_mul] using hscale
  refine (hb.trans hscale').trans (ht.trans ?_)
  norm_num at he ⊢
  linarith

end FleetArchimedeanTailCertificate
