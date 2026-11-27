import GammaExplicitFormula
import PrincipalPartDischarge

namespace FleetGammaPole
open Complex Filter Topology Set

private lemma analyticAt_deriv {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) :
    AnalyticAt ℂ (deriv f) z := by
  obtain ⟨s, hs, hfs⟩ := hf.exists_mem_nhds_analyticOnNhd
  exact hfs.deriv z (mem_of_mem_nhds hs)

private lemma gamma_analytic_pos (s : ℂ) (hs : 0 < s.re) : AnalyticAt ℂ Gamma s := by
  rw [analyticAt_iff_eventually_differentiableAt]
  have hpos : ∀ᶠ z : ℂ in 𝓝 s, 0 < z.re :=
    continuous_re.continuousAt.eventually (Ioi_mem_nhds hs)
  filter_upwards [hpos] with z hz
  apply Complex.differentiableAt_Gamma
  intro n he
  have hh := congrArg Complex.re he
  simp at hh
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

private lemma gamma_analytic_one : AnalyticAt ℂ Gamma (1 : ℂ) :=
  gamma_analytic_pos 1 (by norm_num)

/-- The trigonometric Gamma factor has no zeros in this strip except at 1. -/
theorem cos_ne_zero_in_strip (s : ℂ) (hs : 0 < s.re ∧ s.re < 2) (hs1 : s ≠ 1) :
    cos (Real.pi * s / 2) ≠ 0 := by
  intro hzero
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hzero
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have he : s = 2 * (k : ℂ) + 1 := by
    apply mul_left_cancel₀ hp
    linear_combination 2 * hk
  have hre := congrArg Complex.re he
  simp at hre
  have hlow : (-1 : ℝ) < k := by linarith [hs.1]
  have hhigh : (k : ℝ) < 1 := by linarith [hs.2]
  have hki : (-1 : ℤ) < k := by exact_mod_cast hlow
  have hkj : k < (1 : ℤ) := by exact_mod_cast hhigh
  have hk0 : k = 0 := by omega
  apply hs1
  simpa [hk0] using he

/-- Analyticity of the Gamma kernel off its unique pole in 0 < Re s < 2. -/
theorem analyticAt_gammaKernel (s : ℂ) (hs : 0 < s.re ∧ s.re < 2) (hs1 : s ≠ 1) :
    AnalyticAt ℂ GammaExplicitFormula.gammaKernel s := by
  have hlinear : Differentiable ℂ (fun z : ℂ => (Real.pi : ℂ) * z / 2) :=
    (differentiable_id.const_mul _).div_const _
  have hsin := (Complex.differentiable_sin.comp hlinear).analyticAt s
  have hcos := (Complex.differentiable_cos.comp hlinear).analyticAt s
  have hgamma := gamma_analytic_pos s hs.1
  have hquot := (analyticAt_deriv hgamma).div hgamma (Complex.Gamma_ne_zero_of_re_pos hs.1)
  have ht := hsin.div hcos (cos_ne_zero_in_strip s hs hs1)
  have hk : GammaExplicitFormula.gammaKernel = fun z =>
      -(Real.log (2 * Real.pi) : ℂ) + (deriv Gamma / Gamma) z
        - (Real.pi : ℂ) / 2 * (((sin ∘ fun z : ℂ => (Real.pi : ℂ) * z / 2)
          / (cos ∘ fun z : ℂ => (Real.pi : ℂ) * z / 2)) z) := by
    funext z
    simp only [GammaExplicitFormula.gammaKernel, Complex.tan_eq_sin_div_cos, Pi.div_apply,
      Function.comp_apply]
  rw [hk]
  exact (analyticAt_const.add hquot).sub (analyticAt_const.mul ht)

/-- The Gamma kernel minus its principal part at 1 has a local analytic extension. -/
theorem exists_analytic_regular_part :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 1 ∧
      ∀ᶠ s in 𝓝[≠] (1 : ℂ),
        H s = GammaExplicitFormula.gammaKernel s - 1 / (s - 1) := by
  let f : ℂ → ℂ := fun s => cos (Real.pi * s / 2)
  have hd (s : ℂ) : HasDerivAt f (-sin (Real.pi * s / 2) * ((Real.pi : ℂ) / 2)) s := by
    simpa [f] using (((hasDerivAt_id s).const_mul (Real.pi : ℂ)).div_const 2).ccos
  have hdf : Differentiable ℂ f := fun s => (hd s).differentiableAt
  have hf : AnalyticAt ℂ f 1 := hdf.analyticAt 1
  have hf0 : f 1 = 0 := by simp [f, Complex.cos_pi_div_two]
  let g := dslope f (1 : ℂ)
  have hg : AnalyticAt ℂ g 1 := by
    obtain ⟨p, hp⟩ := hf
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  have hg0 : g 1 ≠ 0 := by
    change dslope f 1 1 ≠ 0
    rw [dslope_same, (hd 1).deriv]
    simp [Complex.sin_pi_div_two, Real.pi_ne_zero]
  have hfactor : ∀ᶠ s in 𝓝 (1 : ℂ), f s = (s - 1) ^ (1 : ℕ) * g s := by
    filter_upwards [] with s
    simpa [g, hf0] using (sub_smul_dslope f (1 : ℂ) s).symm
  have hquot := PrincipalPartDischarge.logDeriv_eventually_eq_of_eventually_eq_pow_mul
    hg hg0 1 hfactor
  let H : ℂ → ℂ := fun s => -(Real.log (2 * Real.pi) : ℂ) + deriv Gamma s / Gamma s + deriv g s / g s
  have hH : AnalyticAt ℂ H 1 :=
    ((analyticAt_const.add ((analyticAt_deriv gamma_analytic_one).div gamma_analytic_one
      (by simp))).add ((analyticAt_deriv hg).div hg hg0))
  refine ⟨H, hH, ?_⟩
  filter_upwards [hquot] with s hs
  have he : deriv f s / f s = -(Real.pi : ℂ) / 2 * tan (Real.pi * s / 2) := by
    rw [(hd s).deriv]
    simp only [f, Complex.tan_eq_sin_div_cos]
    ring
  simp only [Nat.cast_one] at hs
  dsimp [H, GammaExplicitFormula.gammaKernel]
  rw [he] at hs
  linear_combination -hs

/-- A ball version suitable for constructing a holomorphic contour remainder. -/
theorem exists_analytic_regular_part_ball :
    ∃ ε : ℝ, 0 < ε ∧ ∃ H : ℂ → ℂ,
      AnalyticOnNhd ℂ H (Metric.ball (1 : ℂ) ε) ∧
      ∀ s ∈ Metric.ball (1 : ℂ) ε, s ≠ 1 →
        H s = GammaExplicitFormula.gammaKernel s - 1 / (s - 1) := by
  obtain ⟨H, hH, heq⟩ := exists_analytic_regular_part
  rw [eventually_nhdsWithin_iff] at heq
  have hall := hH.eventually_analyticAt.and heq
  obtain ⟨ε, hε, hall⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨ε, hε, H, ?_, ?_⟩
  · intro s hs
    exact (hall hs).1
  · intro s hs hne
    exact (hall hs).2 hne

/-- One analytic regular part works on the full open strip containing both contours. -/
theorem exists_analytic_regular_part_strip :
    ∃ H : ℂ → ℂ,
      AnalyticOnNhd ℂ H {s : ℂ | 0 < s.re ∧ s.re < 2} ∧
      ∀ s : ℂ, 0 < s.re → s.re < 2 → s ≠ 1 →
        H s = GammaExplicitFormula.gammaKernel s - 1 / (s - 1) := by
  classical
  obtain ⟨L, hL, heq⟩ := exists_analytic_regular_part
  let R : ℂ → ℂ := fun s => GammaExplicitFormula.gammaKernel s - 1 / (s - 1)
  let H := Function.update R (1 : ℂ) (L 1)
  have hoff (s : ℂ) (hs : s ≠ 1) : H s = R s := by
    simp [H, Function.update_of_ne hs]
  have hnear : L =ᶠ[𝓝 (1 : ℂ)] H := by
    rw [eventually_nhdsWithin_iff] at heq
    filter_upwards [heq] with s hs
    by_cases hs1 : s = 1
    · subst s
      simp [H]
    · rw [hoff s hs1]
      exact hs hs1
  refine ⟨H, ?_, fun s _ _ hs => hoff s hs⟩
  intro s hs
  by_cases hs1 : s = 1
  · subst s
    exact hL.congr hnear
  · have hR : AnalyticAt ℂ R s :=
      (analyticAt_gammaKernel s hs hs1).sub
        (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hs1))
    apply hR.congr
    filter_upwards [eventually_ne_nhds hs1] with z hz
    exact (hoff z hz).symm

end FleetGammaPole

#print axioms FleetGammaPole.exists_analytic_regular_part
#print axioms FleetGammaPole.exists_analytic_regular_part_ball

#print axioms FleetGammaPole.analyticAt_gammaKernel
#print axioms FleetGammaPole.exists_analytic_regular_part_strip
