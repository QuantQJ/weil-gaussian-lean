import Mathlib

noncomputable section
open Set Filter
open scoped Topology
namespace FleetRealCompactification
attribute [local instance] Classical.propDecidable

def q (t : ℝ) : ℝ := t / (1 + |t|)
def r (s : ℝ) : ℝ := s / (1 - |s|)

lemma abs_q (t : ℝ) : |q t| = |t| / (1 + |t|) := by
  simp [q, abs_div, abs_of_pos (show 0 < 1 + |t| by positivity)]
lemma abs_q_lt_one (t : ℝ) : |q t| < 1 := by
  rw [abs_q, div_lt_one (by positivity : 0 < 1 + |t|)]
  linarith
lemma q_mem_Ioo (t : ℝ) : q t ∈ Ioo (-1 : ℝ) 1 := abs_lt.mp (abs_q_lt_one t)
lemma continuous_q : Continuous q := by
  unfold q
  exact continuous_id.div (continuous_const.add continuous_abs) (fun t => by positivity)
lemma abs_r {s : ℝ} (hs : |s| < 1) : |r s| = |s| / (1 - |s|) := by
  simp [r, abs_div, abs_of_pos (sub_pos.mpr hs)]
lemma r_q (t : ℝ) : r (q t) = t := by
  rw [r, abs_q, q]
  field_simp
  ring
lemma q_r {s : ℝ} (hs : |s| < 1) : q (r s) = s := by
  rw [q, abs_r hs, r]
  field_simp [ne_of_gt (sub_pos.mpr hs)]
  ring
lemma threshold_q {S : ℝ} (hS : 0 ≤ S) (t : ℝ) :
    S / (1 + S) ≤ |q t| ↔ S ≤ |t| := by
  rw [abs_q, div_le_div_iff₀ (by positivity : 0 < 1 + S)
    (by positivity : 0 < 1 + |t|)]
  constructor <;> intro h <;> nlinarith
lemma threshold_r {S s : ℝ} (hS : 0 ≤ S) (hs : |s| < 1) :
    S / (1 + S) ≤ |s| ↔ S ≤ |r s| := by
  simpa only [q_r hs] using threshold_q hS (r s)

lemma continuousAt_r {s : ℝ} (hs : |s| < 1) : ContinuousAt r s := by
  exact continuousAt_id.div (continuousAt_const.sub continuous_abs.continuousAt)
    (ne_of_gt (sub_pos.mpr hs))

def extend (φ : ℝ → ℂ) (s : ℝ) : ℂ := if |s| < 1 then φ (r s) else 0
lemma extend_q (φ : ℝ → ℂ) (t : ℝ) : extend φ (q t) = φ t := by
  simp [extend, abs_q_lt_one, r_q]
lemma extend_one (φ : ℝ → ℂ) : extend φ 1 = 0 := by simp [extend]
lemma extend_neg_one (φ : ℝ → ℂ) : extend φ (-1) = 0 := by simp [extend]

lemma extend_eq_zero_of_lt {φ : ℝ → ℂ} {R : ℝ} (hR : 0 < R)
    (hφ : ∀ t, R < |t| → φ t = 0) {s : ℝ} (hs : q R < |s|) :
    extend φ s = 0 := by
  by_cases hi : |s| < 1
  · simp only [extend, if_pos hi]
    apply hφ
    rw [abs_r hi, lt_div_iff₀ (sub_pos.mpr hi)]
    have h := (div_lt_iff₀ (by positivity : 0 < 1 + R)).mp
      (show R / (1 + R) < |s| by simpa [q, abs_of_pos hR] using hs)
    nlinarith
  · simp [extend, hi]

theorem continuous_extend {φ : ℝ → ℂ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Continuous (extend φ) := by
  obtain ⟨R, hR, hbound⟩ := hc.isBounded.exists_pos_norm_le
  have hzero : ∀ t, R < |t| → φ t = 0 := by
    intro t ht
    by_contra h
    have hb := hbound t (subset_tsupport φ (Function.mem_support.mpr h))
    simp [Real.norm_eq_abs, not_le.mpr ht] at hb
  rw [continuous_iff_continuousAt]
  intro s
  by_cases hi : |s| < 1
  · have he : ∀ᶠ u in 𝓝 s, |u| < 1 := continuous_abs.continuousAt (gt_mem_nhds hi)
    apply (hφ.continuousAt.comp (continuousAt_r hi)).congr_of_eventuallyEq
    filter_upwards [he] with u hu
    simp [extend, hu]
  · have hb : q R < |s| := (q_mem_Ioo R).2.trans_le (le_of_not_gt hi)
    have he : ∀ᶠ u in 𝓝 s, q R < |u| := continuous_abs.continuousAt (lt_mem_nhds hb)
    apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [he] with u hu
    exact extend_eq_zero_of_lt hR hzero hu

end FleetRealCompactification
