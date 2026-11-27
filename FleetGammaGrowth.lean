import FleetGammaIdentification
import FleetDigammaGrowth

open Complex Set

namespace FleetGammaGrowth

lemma norm_digamma_le {z : ℂ} {δ : ℝ}
    (hd : 0 < δ) (hd1 : δ ≤ 1) (hz : δ ≤ z.re) :
    ‖deriv Complex.Gamma z / Complex.Gamma z‖ ≤
      |Real.eulerMascheroniConstant| +
        (1 + 1 / δ) * (1 + Real.log (2 + ‖z - 1‖)) + 1 / δ := by
  rw [FleetGammaIdentification.digamma_eq_series z (lt_of_lt_of_le hd hz)]
  exact FleetDigammaGrowth.norm_logDerivative_le hd hd1 hz

lemma exists_halfPlane_bound (δ : ℝ) (hd : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, δ ≤ z.re →
      ‖deriv Complex.Gamma z / Complex.Gamma z‖ ≤
        C * (1 + Real.log (2 + ‖z - 1‖)) := by
  obtain ⟨C, hC, hb⟩ := FleetDigammaGrowth.exists_logDerivative_bound δ hd
  refine ⟨C, hC, fun z hz => ?_⟩
  rw [FleetGammaIdentification.digamma_eq_series z (lt_of_lt_of_le hd hz)]
  exact hb z hz

lemma strip_norm_sub_one_le {δ M σ t : ℝ} (hd : 0 < δ) (hσ : σ ∈ Icc δ M) :
    ‖((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖ ≤ |M| + 1 + |t| := by
  have hσ0 : 0 ≤ σ := (lt_of_lt_of_le hd hσ.1).le
  have hm : σ ≤ |M| := hσ.2.trans (le_abs_self M)
  calc
    _ ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ ≤ (‖(σ : ℂ)‖ + ‖(t : ℂ) * Complex.I‖) + ‖(1 : ℂ)‖ := by
      gcongr; exact norm_add_le _ _
    _ = σ + |t| + 1 := by simp [norm_mul, _root_.abs_of_nonneg hσ0]
    _ ≤ |M| + 1 + |t| := by linarith

/-- A uniform logarithmic digamma bound on every closed strip contained in the
right half-plane. No complex Stirling theorem is used. -/
theorem exists_strip_bound (δ M : ℝ) (hd : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Icc δ M, ∀ t : ℝ,
      ‖deriv Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) /
          Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * (1 + Real.log (2 + |t|)) := by
  obtain ⟨C, hC, hb⟩ := exists_halfPlane_bound δ hd
  let L : ℝ := |M| + 3
  have hL : 1 ≤ L := by dsimp only [L]; linarith [abs_nonneg M]
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  refine ⟨C * (1 + Real.log L), mul_pos hC (by linarith), ?_⟩
  intro σ hσ t
  have hz : δ ≤ (((σ : ℂ) + (t : ℂ) * Complex.I).re) := by simpa using hσ.1
  have h := hb ((σ : ℂ) + (t : ℂ) * Complex.I) hz
  have hT : 0 < 2 + |t| := by positivity
  have hlogT : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hn := strip_norm_sub_one_le (t := t) hd hσ
  have harg : 2 + ‖((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖ ≤ L * (2 + |t|) := by
    have hm := mul_nonneg (sub_nonneg.mpr hL) (abs_nonneg t)
    dsimp only [L] at *
    nlinarith
  have hlog : Real.log (2 + ‖((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖) ≤
      Real.log L + Real.log (2 + |t|) := by
    rw [← Real.log_mul (ne_of_gt hL0) (ne_of_gt hT)]
    exact Real.log_le_log (by positivity) harg
  refine h.trans ?_
  have hm := mul_nonneg hlogL hlogT
  have hbracket : 1 + Real.log (2 + ‖((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖) ≤
      (1 + Real.log L) * (1 + Real.log (2 + |t|)) := by nlinarith
  calc
    _ ≤ C * ((1 + Real.log L) * (1 + Real.log (2 + |t|))) :=
      mul_le_mul_of_nonneg_left hbracket hC.le
    _ = C * (1 + Real.log L) * (1 + Real.log (2 + |t|)) := by ring


end FleetGammaGrowth
