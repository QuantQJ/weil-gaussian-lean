import FleetGammaContour
import FleetGammaKernel

namespace FleetGammaContourLimit
open Complex Filter Topology Set MeasureTheory TestFunctions

/-- The remaining explicit analytic growth obligation. -/
def KernelLogBound (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ σ ∈ Icc (1/2 : ℝ) (3/2), ∀ t : ℝ, 1 ≤ |t| →
    ‖GammaExplicitFormula.gammaKernel (σ + t * I)‖ ≤ C * (1 + Real.log (2 + |t|))

private theorem continuous_critical :
    Continuous (fun t : ℝ => GammaExplicitFormula.gammaKernel (1/2 + t * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hn : (1/2 : ℂ) + t * I ≠ 1 := by
    intro he
    have hr := congrArg Complex.re he
    norm_num at hr
  exact (FleetGammaPole.analyticAt_gammaKernel _ (by norm_num) hn).continuousAt.comp
    (f := fun t : ℝ => (1/2 : ℂ) + t * I) (by fun_prop)

/-- A tail-only kernel bound suffices for absolute convergence on the critical line. -/
theorem integrable_critical {a : ℝ} {g : ℝ → ℂ} (hg : IsTestFn a g)
    {C : ℝ} (hC : KernelLogBound C) :
    Integrable (fun t : ℝ => GammaExplicitFormula.gammaKernel (1/2 + t * I) *
      Gt a g (1/2 - t * I)) := by
  obtain ⟨D, hD⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    continuous_critical.continuousOn
  have hb : ∀ t : ℝ, ‖GammaExplicitFormula.gammaKernel (1/2 + t * I)‖ ≤
      (2 * |D| + 3 * C) * Real.log (|t| + 2) := by
    intro t
    have hl : (2/3 : ℝ) ≤ Real.log (|t|+2) :=
      LogDerivSegmentBound.two_thirds_le_log_two.trans
        (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t]))
    by_cases ht : 1 ≤ |t|
    · have hh := hC.2 (1/2) (by constructor <;> norm_num) t ht
      push_cast at hh
      rw [add_comm 2] at hh
      have hCL : C ≤ (3/2) * C * Real.log (|t|+2) := by nlinarith [hC.1]
      have hDL : 0 ≤ |D| * Real.log (|t|+2) := mul_nonneg (abs_nonneg D) (by linarith)
      nlinarith [hC.1]
    · have hm : t ∈ Icc (-1 : ℝ) 1 := abs_le.mp (le_of_lt (lt_of_not_ge ht))
      have hh := hD t hm
      have hCL : 0 ≤ C * Real.log (|t|+2) := mul_nonneg hC.1 (by linarith)
      nlinarith [le_abs_self D, abs_nonneg D]
  obtain ⟨M, hM0, hM⟩ := Gt_norm_le_div_one_add_sq hg (1/2)
  apply LeftLineBound.integrable_mul_of_log_bound continuous_critical
    ((Gt_continuous hg.continuous).comp (by fun_prop)) hb
  intro t
  simpa [← sub_eq_add_neg] using hM (-t)

/-- A coarse 1/|t| majorant already suffices for the horizontal edges. -/
theorem norm_weighted_tail {a : ℝ} {g : ℝ → ℂ} (hg : IsTestFn a g)
    {C : ℝ} (hC : KernelLogBound C) {σ t : ℝ}
    (hσ : σ ∈ Icc (1/2 : ℝ) (3/2)) (ht : 1 ≤ |t|) :
    ‖GammaExplicitFormula.gammaKernel (σ + t * I) * Gt a g (1 - (σ + t * I))‖ ≤
      4 * C * (C₂ a g * Real.exp a) / |t| := by
  have ht0 : t ≠ 0 := by intro he; simp [he] at ht; linarith
  have habs : 0 < |t| := abs_pos.mpr ht0
  have hlog : Real.log (2+|t|) ≤ 2+|t| :=
    (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have hk := hC.2 σ hσ t ht
  have hkernel : ‖GammaExplicitFormula.gammaKernel (σ + t * I)‖ ≤ 4 * C * |t| := by
    nlinarith [hC.1]
  have hgt := Gt_decay hg (s := 1 - ((σ : ℂ) + t * I)) (by simpa using ht0)
  have hre : (1 - ((σ : ℂ) + t * I)).re = 1-σ := by simp
  have him : (1 - ((σ : ℂ) + t * I)).im = -t := by simp
  rw [hre, him, neg_sq] at hgt
  have hσbound : |1-σ-1/2| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hσ.1, hσ.2]
  have hexp : Real.exp (a * |1-σ-1/2|) ≤ Real.exp a := by
    apply Real.exp_le_exp.mpr
    nlinarith [hg.nonneg]
  have hgtn : ‖Gt a g (1 - ((σ : ℂ) + t * I))‖ ≤ (C₂ a g * Real.exp a) / t^2 :=
    hgt.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (C₂_nonneg hg)) (sq_nonneg t))
  rw [norm_mul]
  calc
    _ ≤ (4*C*|t|) * ((C₂ a g * Real.exp a)/t^2) :=
      mul_le_mul hkernel hgtn (norm_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) hC.1) (abs_nonneg t))
    _ = 4*C*(C₂ a g * Real.exp a)/|t| := by
      rw [← _root_.sq_abs t]
      field_simp

set_option maxHeartbeats 400000 in
/-- Both signed horizontal edges vanish under the stated kernel bound. -/
theorem horizontal_vanish {a : ℝ} {g : ℝ → ℂ} (hg : IsTestFn a g)
    {C : ℝ} (hC : KernelLogBound C) (e : ℝ) (he : |e| = 1) :
    Tendsto (fun T : ℝ => ∫ σ in (1/2 : ℝ)..(3/2),
      GammaExplicitFormula.gammaKernel (σ + (e*T) * I) *
        Gt a g (1 - (σ + (e*T) * I))) atTop (𝓝 0) := by
  have hbound : ∀ᶠ T : ℝ in atTop,
      ‖∫ σ in (1/2 : ℝ)..(3/2),
        GammaExplicitFormula.gammaKernel (σ + (e*T) * I) *
          Gt a g (1 - (σ + (e*T) * I))‖ ≤
        4*C*(C₂ a g * Real.exp a)/T := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have heT : |e*T| = T := by rw [abs_mul, he, one_mul, _root_.abs_of_nonneg (by linarith)]
    have hh := HorizontalDecay.horizontal_integral_norm_le
      (F := fun s => GammaExplicitFormula.gammaKernel s * Gt a g (1-s))
      (a := (1/2 : ℝ)) (b := (3/2 : ℝ)) (by norm_num) (e*T)
      (fun _ => 4*C*(C₂ a g * Real.exp a)/T)
      (by
        intro σ hσ
        have ht : 1 ≤ |e*T| := by rw [heT]; exact hT
        have hh := norm_weighted_tail hg hC (σ := σ) (t := e*T) hσ ht
        rw [heT] at hh
        exact hh)
    norm_num at hh
    exact hh
  apply squeeze_zero_norm' hbound
  have hlim := ((tendsto_const_nhds : Tendsto (fun _ : ℝ => 4*C*(C₂ a g * Real.exp a)) atTop
      (𝓝 (4*C*(C₂ a g * Real.exp a)))).mul tendsto_inv_atTop_zero)
  rw [mul_zero] at hlim
  exact hlim.congr fun x => (div_eq_mul_inv _ _).symm


/-- Conditional only on KernelLogBound: the shifted Gamma term has standard digamma normalization. -/
theorem archimedean_eq_digamma_of_bound {a : ℝ} {g : ℝ → ℂ} (hg : IsTestFn a g)
    {C : ℝ} (hC : KernelLogBound C) :
    GammaExplicitFormula.archimedean a g =
      (1 / (2 * (Real.pi : ℂ))) *
        ∫ t : ℝ, hfun a g (t : ℂ) * (FleetGammaKernel.weight t : ℂ) := by
  let F : ℂ → ℂ := fun s => GammaExplicitFormula.gammaKernel s * Gt a g (1-s)
  have hrfun : (fun t : ℝ => F (3/2 + t*I)) =
      (fun t : ℝ => GammaExplicitFormula.gammaKernel (3/2 + t*I) * Gt a g (-1/2-t*I)) := by
    funext t
    dsimp [F]
    congr 2
    ring
  have hlfun : (fun t : ℝ => F (1/2 + t*I)) =
      (fun t : ℝ => GammaExplicitFormula.gammaKernel (1/2 + t*I) * Gt a g (1/2-t*I)) := by
    funext t
    dsimp [F]
    congr 2
    ring
  have hri : Integrable (fun t : ℝ => F (3/2+t*I)) := by
    rw [hrfun]
    exact GammaExplicitFormula.integrable_gamma hg
  have hli : Integrable (fun t : ℝ => F (1/2+t*I)) := by
    rw [hlfun]
    exact integrable_critical hg hC
  have hR := intervalIntegral_tendsto_integral hri tendsto_neg_atTop_atBot
    (tendsto_id : Tendsto (fun T : ℝ => T) atTop atTop)
  have hL := intervalIntegral_tendsto_integral hli tendsto_neg_atTop_atBot
    (tendsto_id : Tendsto (fun T : ℝ => T) atTop atTop)
  have hB : Tendsto (fun T : ℝ => ∫ σ in (1/2 : ℝ)..(3/2), F (σ-T*I)) atTop (𝓝 0) := by
    simpa [F, ← sub_eq_add_neg] using horizontal_vanish hg hC (-1) (by norm_num)
  have hTop : Tendsto (fun T : ℝ => ∫ σ in (1/2 : ℝ)..(3/2), F (σ+T*I)) atTop (𝓝 0) := by
    simpa [F] using horizontal_vanish hg hC 1 (by norm_num)
  have hlim := ((hB.sub hTop).add (hR.const_mul I)).sub (hL.const_mul I)
  have hfinite : ∀ᶠ T : ℝ in atTop,
      (∫ σ in (1/2 : ℝ)..(3/2), F (σ-T*I)) -
      (∫ σ in (1/2 : ℝ)..(3/2), F (σ+T*I)) +
      I * (∫ t in (-T)..T, F (3/2+t*I)) -
      I * (∫ t in (-T)..T, F (1/2+t*I)) =
        2 * (Real.pi : ℂ) * I * Gt a g 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    simpa [Residue.rectBoundaryIntegral, F, ← sub_eq_add_neg] using FleetGammaContour.gamma_rectangle hg hT
  have he := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hfinite.mono fun _ h => h.symm))
  simp only [sub_self, zero_add] at he
  have hrval : (∫ t : ℝ, F (3/2+t*I)) = GammaExplicitFormula.gammaIntegral a g := by
    rw [hrfun]
    rfl
  have hlval : (∫ t : ℝ, F (1/2+t*I)) =
      ∫ t : ℝ, hfun a g (t : ℂ) * (FleetGammaKernel.weight t : ℂ) := by
    rw [hlfun]
    exact FleetGammaKernel.critical_integral_eq a g
  rw [hrval, hlval] at he
  unfold GammaExplicitFormula.archimedean
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  linear_combination (norm := ring_nf) -I * he
  simp [I_sq]

end FleetGammaContourLimit

#print axioms FleetGammaContourLimit.archimedean_eq_digamma_of_bound
#print axioms FleetGammaContourLimit.integrable_critical
#print axioms FleetGammaContourLimit.horizontal_vanish
