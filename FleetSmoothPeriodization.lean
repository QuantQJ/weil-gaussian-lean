import Mathlib

noncomputable section
open Set Filter
open scoped Topology
namespace FleetSmoothPeriodization

def periodize (P : ℝ) (F : ℝ → ℂ) (t : ℝ) : ℂ := ∑' k : ℤ, F (t + k * P)

lemma eventually_finite_shifts {P R : ℝ} (hP : 0 < P) (F : ℝ → ℂ)
    (hs : ∀ u, R < |u| → F u = 0) (t : ℝ) :
    ∃ s : Finset ℤ, ∀ᶠ u in 𝓝 t, ∀ k ∉ s, F (u + k * P) = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((R + |t| + 1) / P)
  have hNP : R + |t| + 1 < (N : ℝ) * P := (div_lt_iff₀ hP).mp hN
  refine ⟨Finset.Icc (-(N : ℤ)) N, ?_⟩
  have he : ∀ᶠ u in 𝓝 t, |u - t| < 1 := by
    filter_upwards [Metric.ball_mem_nhds t (by norm_num : (0 : ℝ) < 1)] with u hu
    simpa [Real.dist_eq] using hu
  filter_upwards [he] with u hu
  intro k hk
  apply hs
  have hkabs : (N : ℝ) < |(k : ℝ)| := by
    by_contra hh
    have hh' := abs_le.mp (le_of_not_gt hh)
    apply hk
    apply Finset.mem_Icc.mpr
    constructor
    · exact_mod_cast hh'.1
    · exact_mod_cast hh'.2
  have huabs : |u| ≤ |u-t| + |t| := by
    simpa using abs_add_le (u-t) t
  have htri : |(k : ℝ)| * P ≤ |u + k*P| + |u| := by
    have h := abs_sub (u + k*P) u
    simpa [abs_mul, abs_of_pos hP] using h
  have hmul := mul_lt_mul_of_pos_right hkabs hP
  linarith

lemma eventually_eq_finite_sum {P R : ℝ} (hP : 0 < P) (F : ℝ → ℂ)
    (hs : ∀ u, R < |u| → F u = 0) (t : ℝ) :
    ∃ s : Finset ℤ, periodize P F =ᶠ[𝓝 t] (fun u => ∑ k ∈ s, F (u + k*P)) := by
  obtain ⟨s, he⟩ := eventually_finite_shifts hP F hs t
  refine ⟨s, he.mono fun u hu => ?_⟩
  exact tsum_eq_sum hu

/-- Periodization of a compactly supported smooth function is smooth. The proof
reduces to a fixed finite shift sum on a neighborhood of each argument. -/
theorem contDiff_periodize {P R : ℝ} (hP : 0 < P) {F : ℝ → ℂ}
    (hs : ∀ u, R < |u| → F u = 0) {n : ℕ∞} (hf : ContDiff ℝ n F) :
    ContDiff ℝ n (periodize P F) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  obtain ⟨s, he⟩ := eventually_eq_finite_sum hP F hs t
  have hc : ContDiff ℝ n (fun u => ∑ k ∈ s, F (u+k*P)) :=
    ContDiff.sum (fun k _ => hf.comp (contDiff_id.add contDiff_const))
  exact hc.contDiffAt.congr_of_eventuallyEq he

lemma periodic_periodize (P : ℝ) (F : ℝ → ℂ) :
    Function.Periodic (periodize P F) P := by
  intro t
  unfold periodize
  have he := (Equiv.addRight (1 : ℤ)).tsum_eq (fun k : ℤ => F (t + k*P))
  convert he using 1
  congr 1
  ext k
  congr 1
  change t + P + (k : ℝ)*P = t + ((k + 1 : ℤ) : ℝ)*P
  push_cast
  ring

/-- Differentiation commutes with periodization because the shift sum is locally finite. -/
theorem deriv_periodize {P R : ℝ} (hP : 0 < P) {F : ℝ → ℂ}
    (hs : ∀ u, R < |u| → F u = 0) (hf : Differentiable ℝ F) :
    deriv (periodize P F) = periodize P (deriv F) := by
  funext t
  obtain ⟨s, he⟩ := eventually_finite_shifts hP F hs t
  have heq : periodize P F =ᶠ[𝓝 t] (fun u => ∑ k ∈ s, F (u+k*P)) :=
    he.mono fun u hu => tsum_eq_sum hu
  rw [heq.deriv_eq, deriv_fun_sum]
  · simp only [deriv_comp_add_const]
    symm
    apply tsum_eq_sum
    intro k hk
    have hz : (fun u => F (u + k*P)) =ᶠ[𝓝 t] (fun _ => 0) :=
      he.mono fun u hu => hu k hk
    simpa [deriv_comp_add_const] using hz.deriv_eq
  · intro k hk
    exact (hf (t+k*P)).comp t (differentiableAt_id.add_const _)

/-- Derivatives vanish outside the same closed support interval. -/
theorem deriv_eq_zero_outside {R : ℝ} {F : ℝ → ℂ}
    (hs : ∀ u, R < |u| → F u = 0) {t : ℝ} (ht : R < |t|) :
    deriv F t = 0 := by
  have he : ∀ᶠ u in 𝓝 t, R < |u| :=
    (isOpen_lt continuous_const continuous_abs).mem_nhds ht
  have hz : F =ᶠ[𝓝 t] (fun _ => 0) := he.mono fun u hu => hs u hu
  simpa using hz.deriv_eq

theorem second_deriv_periodize {P R : ℝ} (hP : 0 < P) {F : ℝ → ℂ}
    (hs : ∀ u, R < |u| → F u = 0) (hf : Differentiable ℝ F)
    (hf' : Differentiable ℝ (deriv F)) :
    deriv (deriv (periodize P F)) = periodize P (deriv (deriv F)) := by
  rw [deriv_periodize hP hs hf]
  exact deriv_periodize hP (fun u hu => deriv_eq_zero_outside hs hu) hf'

/-- The three regularity assumptions consumed by periodic C² density are
preserved, with exact derivative identities rather than additional hypotheses. -/
theorem periodize_C2 {P R : ℝ} (hP : 0 < P) {F : ℝ → ℂ}
    (hs : ∀ u, R < |u| → F u = 0) (hf : Differentiable ℝ F)
    (hf' : Differentiable ℝ (deriv F)) (hf'' : Continuous (deriv (deriv F))) :
    Differentiable ℝ (periodize P F) ∧
    Differentiable ℝ (deriv (periodize P F)) ∧
    Continuous (deriv (deriv (periodize P F))) := by
  have hd : ∀ G : ℝ → ℂ, (∀ u, R < |u| → G u = 0) →
      Differentiable ℝ G → Differentiable ℝ (periodize P G) := by
    intro G hsG hdG t
    obtain ⟨s, he⟩ := eventually_eq_finite_sum hP G hsG t
    have hdS : Differentiable ℝ (fun u => ∑ k ∈ s, G (u+k*P)) := by
      have h := Differentiable.sum (𝕜 := ℝ) (u := s) (A := fun (k : ℤ) (u : ℝ) => G (u + k*P))
        (fun k _ => hdG.comp ((differentiable_id (𝕜 := ℝ)).add_const ((k : ℝ) * P)))
      simpa only [Finset.sum_fn] using h
    exact (hdS t).congr_of_eventuallyEq he
  have hs' : ∀ u, R < |u| → deriv F u = 0 :=
    fun u hu => deriv_eq_zero_outside hs hu
  have hs'' : ∀ u, R < |u| → deriv (deriv F) u = 0 :=
    fun u hu => deriv_eq_zero_outside hs' hu
  refine ⟨hd F hs hf, ?_, ?_⟩
  · rw [deriv_periodize hP hs hf]
    exact hd (deriv F) hs' hf'
  · rw [second_deriv_periodize hP hs hf hf']
    exact (contDiff_periodize hP hs'' (contDiff_zero.mpr hf'')).continuous

end FleetSmoothPeriodization
