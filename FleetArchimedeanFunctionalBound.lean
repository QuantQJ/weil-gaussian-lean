import FleetStandardExplicitFormula
import LeftLineBound

noncomputable section
open MeasureTheory Filter Topology Set Complex
namespace FleetArchimedeanFunctionalBound

def logIntegral : ℝ := ∫ t : ℝ, Real.log (|t|+2)/(1+t^2)

lemma logIntegral_nonneg : 0 ≤ logIntegral := by
  apply integral_nonneg
  intro t
  exact div_nonneg (Real.log_nonneg (by linarith [abs_nonneg t])) (by positivity)

/-- Measurability and the pointwise bounds suffice for absolute integrability
and the quantitative norm estimate; no integrability hypothesis is supplied. -/
theorem integral_bound {f G : ℝ → ℂ} (hf : Continuous f)
    (hG : AEStronglyMeasurable G) {B M : ℝ}
    (hB : ∀ t, ‖f t‖ ≤ B*Real.log (|t|+2))
    (hM : ∀ t, ‖G t‖ ≤ M/(1+t^2)) :
    Integrable (fun t => f t*G t) ∧
      ‖∫ t, f t*G t‖ ≤ B*M*logIntegral := by
  have hmajor (t : ℝ) : ‖f t*G t‖ ≤ B*M*(Real.log (|t|+2)/(1+t^2)) := by
    rw [norm_mul]
    calc
      ‖f t‖*‖G t‖ ≤ (B*Real.log (|t|+2))*(M/(1+t^2)) :=
        mul_le_mul (hB t) (hM t) (norm_nonneg _) ((norm_nonneg _).trans (hB t))
      _ = _ := by ring
  have hi := (LeftLineBound.integrable_log_div_one_add_sq.const_mul (B*M)).mono'
    (hf.aestronglyMeasurable.mul hG) (Eventually.of_forall hmajor)
  refine ⟨hi, ?_⟩
  calc
    ‖∫ t, f t*G t‖ ≤ ∫ t, ‖f t*G t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, B*M*(Real.log (|t|+2)/(1+t^2)) :=
      integral_mono hi.norm (LeftLineBound.integrable_log_div_one_add_sq.const_mul (B*M)) hmajor
    _ = B*M*logIntegral := MeasureTheory.integral_const_mul _ _

lemma continuous_critical :
    Continuous (fun t : ℝ => GammaExplicitFormula.gammaKernel (1/2+t*I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hn : (1/2 : ℂ)+t*I ≠ 1 := by
    intro he
    have hr := congrArg Complex.re he
    norm_num at hr
  exact (FleetGammaPole.analyticAt_gammaKernel _ (by norm_num) hn).continuousAt.comp
    (f := fun t : ℝ => (1/2 : ℂ)+t*I) (by fun_prop)

lemma exists_critical_log_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ,
    ‖GammaExplicitFormula.gammaKernel (1/2+t*I)‖ ≤ B*Real.log (|t|+2) := by
  obtain ⟨C, hC⟩ := FleetKernelGrowth.exists_kernel_log_bound
  obtain ⟨D, hD⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    continuous_critical.continuousOn
  refine ⟨2*|D|+3*C, by nlinarith [hC.1, abs_nonneg D], ?_⟩
  intro t
  have hl : (2/3 : ℝ) ≤ Real.log (|t|+2) :=
    LogDerivSegmentBound.two_thirds_le_log_two.trans
      (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t]))
  by_cases ht : 1 ≤ |t|
  · have hh := hC.2 (1/2) (by constructor <;> norm_num) t ht
    push_cast at hh
    rw [add_comm 2] at hh
    have hCL : C ≤ (3/2)*C*Real.log (|t|+2) := by nlinarith [hC.1]
    have hDL : 0 ≤ |D| *Real.log (|t|+2) := mul_nonneg (abs_nonneg D) (by linarith)
    nlinarith [hC.1]
  · have hm : t ∈ Icc (-1 : ℝ) 1 := abs_le.mp (le_of_lt (lt_of_not_ge ht))
    have hh := hD t hm
    have hCL : 0 ≤ C*Real.log (|t|+2) := mul_nonneg hC.1 (by linarith)
    nlinarith [le_abs_self D, abs_nonneg D]

/-- A fixed finite constant controls the actual critical gamma kernel against
any measurable inverse-quadratically bounded trace. -/
theorem exists_critical_integral_bound : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (G : ℝ → ℂ), AEStronglyMeasurable G → ∀ M : ℝ,
      (∀ t, ‖G t‖ ≤ M/(1+t^2)) →
      Integrable (fun t : ℝ => GammaExplicitFormula.gammaKernel (1/2+t*I)*G t) ∧
      ‖∫ t : ℝ, GammaExplicitFormula.gammaKernel (1/2+t*I)*G t‖ ≤ K*M := by
  obtain ⟨B, hB, hb⟩ := exists_critical_log_bound
  refine ⟨B*logIntegral, mul_nonneg hB logIntegral_nonneg, ?_⟩
  intro G hG M hM
  obtain ⟨hi, he⟩ := integral_bound continuous_critical hG hb hM
  refine ⟨hi, ?_⟩
  calc
    _ ≤ B*M*logIntegral := he
    _ = (B*logIntegral)*M := by ring

/-- The same quantitative bound in the conventional real digamma-weight notation. -/
theorem exists_weight_integral_bound : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (G : ℝ → ℂ), AEStronglyMeasurable G → ∀ M : ℝ,
      (∀ t, ‖G t‖ ≤ M/(1+t^2)) →
      Integrable (fun t : ℝ => G t*(FleetGammaKernel.weight t : ℂ)) ∧
      ‖∫ t : ℝ, G t*(FleetGammaKernel.weight t : ℂ)‖ ≤ K*M := by
  obtain ⟨K, hK, hb⟩ := exists_critical_integral_bound
  refine ⟨K, hK, ?_⟩
  intro G hG M hM
  have he : (fun t : ℝ => GammaExplicitFormula.gammaKernel (1/2+t*I)*G t) =
      (fun t : ℝ => G t*(FleetGammaKernel.weight t : ℂ)) := by
    funext t
    rw [FleetGammaKernel.kernel_critical_line]
    change (FleetGammaKernel.weight t : ℂ)*G t = _
    ring
  simpa only [he] using hb G hG M hM

lemma continuous_weight : Continuous FleetGammaKernel.weight := by
  have he : FleetGammaKernel.weight =
      (fun t : ℝ => (GammaExplicitFormula.gammaKernel (1/2+t*I)).re) := by
    funext t
    rw [FleetGammaKernel.kernel_critical_line]
    rfl
  rw [he]
  exact Complex.continuous_re.comp continuous_critical

lemma exists_weight_log_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ,
    |FleetGammaKernel.weight t| ≤ B*Real.log (|t|+2) := by
  obtain ⟨B, hB, hb⟩ := exists_critical_log_bound
  refine ⟨B, hB, ?_⟩
  intro t
  have ht := hb t
  rw [FleetGammaKernel.kernel_critical_line] at ht
  change ‖(FleetGammaKernel.weight t : ℂ)‖ ≤ _ at ht
  simpa only [Complex.norm_real, Real.norm_eq_abs] using ht

end FleetArchimedeanFunctionalBound
