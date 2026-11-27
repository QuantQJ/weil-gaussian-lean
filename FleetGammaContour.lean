import FleetGammaPole

namespace FleetGammaContour
open Complex Filter Topology Set Interval MeasureTheory
open TestFunctions Residue

/-- The transformed Gamma kernel has an analytic regular part throughout the contour strip. -/
theorem exists_analytic_weighted_regular_part {a : ℝ} {g : ℝ → ℂ} (hg : IsTestFn a g) :
    ∃ H : ℂ → ℂ,
      AnalyticOnNhd ℂ H {s : ℂ | 0 < s.re ∧ s.re < 2} ∧
      ∀ s : ℂ, 0 < s.re → s.re < 2 → s ≠ 1 →
        GammaExplicitFormula.gammaKernel s * Gt a g (1 - s) =
          H s + Gt a g 0 / (s - 1) := by
  obtain ⟨K, hK, heq⟩ := FleetGammaPole.exists_analytic_regular_part_strip
  let Q : ℂ → ℂ := fun s => Gt a g (1 - s)
  have hQ : Differentiable ℂ Q :=
    (Gt_differentiable hg.continuous).comp (differentiable_id.const_sub 1)
  have hds : Differentiable ℂ (dslope Q 1) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (by simp : (Set.univ : Set ℂ) ∈ 𝓝 (1 : ℂ))).mpr
      hQ.differentiableOn
  refine ⟨fun s => K s * Q s + dslope Q 1 s, ?_, ?_⟩
  · intro s hs
    exact ((hK s hs).mul (hQ.analyticAt s)).add (hds.analyticAt s)
  · intro s hs0 hs2 hs1
    have hf := sub_smul_dslope Q (1 : ℂ) s
    simp only [smul_eq_mul] at hf
    have hq1 : Q 1 = Gt a g 0 := by simp [Q]
    rw [hq1] at hf
    have hk := heq s hs0 hs2 hs1
    change GammaExplicitFormula.gammaKernel s * Q s = _
    have hn : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    field_simp [hn] at hk ⊢
    linear_combination -Q s * hk - hf

/-- All four edges are integrable; their positive height avoids the pole. -/
theorem segmentIntegrable_gamma {a : ℝ} {g : ℝ → ℂ} (hg : IsTestFn a g)
    {T : ℝ} (hT : 0 < T) :
    SegmentIntegrable (fun s => GammaExplicitFormula.gammaKernel s * Gt a g (1 - s))
      ((1 / 2 : ℂ) - T * I) ((3 / 2 : ℂ) + T * I) := by
  let F := fun s => GammaExplicitFormula.gammaKernel s * Gt a g (1 - s)
  have hQ : Differentiable ℂ (fun s : ℂ => Gt a g (1 - s)) :=
    (Gt_differentiable hg.continuous).comp (differentiable_id.const_sub 1)
  have hc (s : ℂ) (hs : 0 < s.re ∧ s.re < 2) (hne : s ≠ 1) : ContinuousAt F s :=
    ((FleetGammaPole.analyticAt_gammaKernel s hs hne).mul (hQ.analyticAt s)).continuousAt
  have hhor (y : ℝ) (hy : y ≠ 0) :
      IntervalIntegrable (fun x : ℝ => F (x + y * I)) volume (1/2) (3/2) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hx' : (1/2 : ℝ) ≤ x ∧ x ≤ 3/2 := by
      rw [uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 3/2)] at hx
      exact hx
    have hne : (x : ℂ) + y * I ≠ 1 := by
      intro he
      have hi := congrArg Complex.im he
      simp at hi
      exact hy hi
    apply ContinuousAt.continuousWithinAt
    exact (hc _ (by simp; constructor <;> linarith) hne).comp (f := fun t : ℝ => (t : ℂ) + y * I)
      (by fun_prop : ContinuousAt (fun t : ℝ => (t : ℂ) + y * I) x)
  have hver (x : ℝ) (hx : 0 < x ∧ x < 2) (hx1 : x ≠ 1) :
      IntervalIntegrable (fun y : ℝ => F (x + y * I)) volume (-T) T := by
    apply Continuous.intervalIntegrable
    apply continuous_iff_continuousAt.mpr
    intro y
    have hne : (x : ℂ) + y * I ≠ 1 := by
      intro he
      have hr := congrArg Complex.re he
      simp at hr
      exact hx1 hr
    exact (hc _ (by simpa using hx) hne).comp (f := fun t : ℝ => (x : ℂ) + t * I)
      (by fun_prop : ContinuousAt (fun t : ℝ => (x : ℂ) + t * I) y)
  simpa [SegmentIntegrable] using
    And.intro (hhor (-T) (neg_ne_zero.mpr hT.ne'))
      (And.intro (hhor T hT.ne')
        (And.intro (hver (3/2) (by norm_num) (by norm_num))
          (hver (1/2) (by norm_num) (by norm_num))))


/-- Finite Gamma contour shift, including the positive residue at s=1. -/
theorem gamma_rectangle {a : ℝ} {g : ℝ → ℂ} (hg : IsTestFn a g)
    {T : ℝ} (hT : 0 < T) :
    rectBoundaryIntegral (fun s => GammaExplicitFormula.gammaKernel s * Gt a g (1 - s))
      ((1 / 2 : ℂ) - T * I) ((3 / 2 : ℂ) + T * I) =
      2 * (Real.pi : ℂ) * I * Gt a g 0 := by
  classical
  obtain ⟨H, hH, heq⟩ := exists_analytic_weighted_regular_part hg
  let z : ℂ := 1 / 2 - T * I
  let w : ℂ := 3 / 2 + T * I
  let p : SimplePole := ⟨1, Gt a g 0⟩
  have hzre : z.re = 1/2 := by simp [z]
  have hwre : w.re = 3/2 := by simp [w]
  have hzim : z.im = -T := by simp [z]
  have hwim : w.im = T := by simp [w]
  have hinstrip (s : ℂ) (hs : s ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]]) :
      0 < s.re ∧ s.re < 2 := by
    rw [mem_reProdIm] at hs
    have hr := hs.1
    rw [hzre, hwre, uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 3/2)] at hr
    constructor <;> linarith [hr.1, hr.2]
  have hmain := ContourShift.rectBoundaryIntegral_eq_of_extension
    (fun s => GammaExplicitFormula.gammaKernel s * Gt a g (1 - s)) H z w
    (by rw [hzre, hwre]; norm_num) (by rw [hzim, hwim]; linarith)
    ({p} : Finset SimplePole)
    (by
      intro q hq
      simp only [Finset.mem_singleton] at hq
      subst q
      simp only [p, hzre, hwre, hzim, hwim, one_re, one_im]
      constructor
      · norm_num
      constructor
      · norm_num
      constructor <;> linarith)
    (by
      intro s hs
      exact (hH s (hinstrip s hs)).differentiableAt.differentiableWithinAt)
    (by
      intro s hs hne
      have hs' := hinstrip s hs
      have hn : s ≠ 1 := hne p (Finset.mem_singleton_self p)
      simpa [principalPart, p] using heq s hs'.1 hs'.2 hn)
    (segmentIntegrable_gamma hg hT)
  simpa [z, w, p] using hmain

end FleetGammaContour

#print axioms FleetGammaContour.exists_analytic_weighted_regular_part

#print axioms FleetGammaContour.segmentIntegrable_gamma
#print axioms FleetGammaContour.gamma_rectangle
