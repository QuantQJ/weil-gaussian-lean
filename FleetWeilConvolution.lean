import FleetWeilCriterion
import TestFunctions

/-!
# Weil criterion, part 1: the autocorrelation `g ⋆ g(−·)` and its transform

For a real, compactly supported, smooth `g`, the function `f = g ⋆ (x ↦ g (−x))` appearing in
Formal Conjectures' `weil_positivity_criterion` is smooth, compactly supported, and its
Fourier–Laplace transform factors: `ft f z = ft g z · ft g (−z)` for every complex `z`
(`ft g z = ∫ g(u) e^{i z u} du`, the convention of `TestFunctions.hfun`).
The two moment conditions of `IsTestFunction` are `ft g (∓ i/2) = 0`.
-/

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped Convolution ContDiff

namespace FleetWeilCriterion

/-- The Fourier–Laplace transform `∫ g(u) e^{i z u} du` (the `hfun` convention). -/
def ft (g : ℝ → ℝ) (z : ℂ) : ℂ := ∫ u : ℝ, (g u : ℂ) * Complex.exp (I * z * u)

/-- The autocorrelation `g ⋆ (x ↦ g (−x))`, exactly as written in the Formal Conjectures statement. -/
def auto (g : ℝ → ℝ) : ℝ → ℝ := g ⋆ fun x ↦ g (-x)

lemma auto_apply (g : ℝ → ℝ) (x : ℝ) : auto g x = ∫ t, g t * g (t - x) := by
  simp only [auto, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul, neg_sub]

/-- A vanishing radius for a compactly supported function. -/
lemma exists_radius {g : ℝ → ℝ} (hg : HasCompactSupport g) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x, A < |x| → g x = 0 := by
  obtain ⟨A, hA⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hg.isCompact.isBounded
  refine ⟨max A 0, le_max_right _ _, fun x hx => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have := hA hmem
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  have := le_max_left A 0
  linarith

lemma hasCompactSupport_of_radius {E : Type*} [NormedAddCommGroup E] {g : ℝ → E} {A : ℝ}
    (hA : ∀ x, A < |x| → g x = 0) : HasCompactSupport g := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -A) (b := A)) (fun x hx => hA x ?_)
  by_contra h
  push Not at h
  exact hx (abs_le.mp h)

lemma auto_vanish {g : ℝ → ℝ} {A : ℝ} (hA : ∀ x, A < |x| → g x = 0) :
    ∀ x, 2 * A < |x| → auto g x = 0 := by
  intro x hx
  rw [auto_apply]
  have h0 : (fun t => g t * g (t - x)) = fun _ => 0 := by
    funext t
    by_cases ht : A < |t|
    · rw [hA t ht, zero_mul]
    · push Not at ht
      have : A < |t - x| := by
        have := abs_sub_abs_le_abs_sub x t
        rw [abs_sub_comm] at this
        linarith
      rw [hA _ this, mul_zero]
  rw [h0, integral_zero]

lemma auto_contDiff {g : ℝ → ℝ} (hc : HasCompactSupport g) (hs : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (auto g) := by
  have hloc : LocallyIntegrable (fun x : ℝ => g (-x)) volume :=
    (hs.continuous.comp continuous_neg).locallyIntegrable
  exact hc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hs hloc

/-- Product-space integrability of the Fubini integrand. -/
lemma integrable_fubini {g : ℝ → ℝ} (hcont : Continuous g) {A : ℝ}
    (hA : ∀ x, A < |x| → g x = 0) (z : ℂ) :
    Integrable (fun p : ℝ × ℝ => (g p.1 : ℂ) * (g (p.1 - p.2) : ℂ) * Complex.exp (I * z * p.2))
      (volume.prod volume) := by
  have hc : Continuous (fun p : ℝ × ℝ =>
      (g p.1 : ℂ) * (g (p.1 - p.2) : ℂ) * Complex.exp (I * z * p.2)) := by fun_prop
  apply hc.integrable_of_hasCompactSupport
  refine HasCompactSupport.intro ((isCompact_Icc (a := -A) (b := A)).prod
    (isCompact_Icc (a := -(2 * A)) (b := 2 * A))) ?_
  intro p hp
  simp only [Set.mem_prod, Set.mem_Icc, not_and_or, not_le] at hp
  by_cases h1 : A < |p.1|
  · simp [hA _ h1]
  · push Not at h1
    have h2 : 2 * A < |p.2| := by
      rcases hp with h | h
      · exfalso; rcases h with h | h <;> linarith [abs_le.mp h1]
      · rcases h with h | h
        · rw [abs_of_neg (by linarith [abs_nonneg p.1, abs_le.mp h1])]; linarith
        · rw [abs_of_pos (by linarith [abs_nonneg p.1, abs_le.mp h1])]; linarith
    have : A < |p.1 - p.2| := by
      have := abs_sub_abs_le_abs_sub p.2 p.1
      rw [abs_sub_comm p.2 p.1] at this
      linarith
    simp [hA _ this]

/-- **Factorisation of the transform of the autocorrelation**, at every complex point. -/
theorem ft_auto {g : ℝ → ℝ} (hcont : Continuous g) {A : ℝ}
    (hA : ∀ x, A < |x| → g x = 0) (z : ℂ) :
    ft (auto g) z = ft g z * ft g (-z) := by
  have hI := integrable_fubini hcont hA z
  have step1 : ft (auto g) z =
      ∫ x : ℝ, ∫ t : ℝ, (g t : ℂ) * (g (t - x) : ℂ) * Complex.exp (I * z * x) := by
    unfold ft
    congr 1
    funext x
    rw [auto_apply, ← integral_complex_ofReal, ← integral_mul_const]
    congr 1
    funext t
    push_cast
    ring
  have hswap := integral_integral_swap (μ := volume) (ν := volume)
    (f := fun t x : ℝ => (g t : ℂ) * (g (t - x) : ℂ) * Complex.exp (I * z * x)) hI
  rw [step1, ← hswap]
  have inner : ∀ t : ℝ, (∫ x : ℝ, (g t : ℂ) * (g (t - x) : ℂ) * Complex.exp (I * z * x)) =
      ((g t : ℂ) * Complex.exp (I * z * t)) * ft g (-z) := by
    intro t
    have hsub := integral_sub_left_eq_self
      (fun v : ℝ => (g t : ℂ) * (g v : ℂ) * Complex.exp (I * z * (t - v))) (μ := volume) t
    have he : (fun x : ℝ => (g t : ℂ) * (g (t - x) : ℂ) * Complex.exp (I * z * x)) =
        fun x : ℝ => (g t : ℂ) * (g (t - x) : ℂ) * Complex.exp (I * z * ((t : ℂ) - ((t - x : ℝ) : ℂ))) := by
      funext x
      push_cast
      ring_nf
    rw [he, hsub]
    unfold ft
    rw [← integral_const_mul]
    congr 1
    funext v
    rw [show I * z * ((t : ℂ) - (v : ℂ)) = I * z * t + I * (-z) * v by ring, Complex.exp_add]
    ring
  simp_rw [inner]
  rw [integral_mul_const]
  rfl

/-- `ft g (−i/2) = ∫ g(x) e^{x/2} dx`. -/
lemma ft_neg_half_I (g : ℝ → ℝ) : ft g (-(I / 2)) = ((∫ x, g x * Real.exp (x / 2) : ℝ) : ℂ) := by
  unfold ft
  rw [← integral_complex_ofReal]
  congr 1
  funext u
  push_cast
  congr 2
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `ft g (i/2) = ∫ g(x) e^{−x/2} dx`. -/
lemma ft_half_I (g : ℝ → ℝ) : ft g (I / 2) = ((∫ x, g x * Real.exp (-x / 2) : ℝ) : ℂ) := by
  unfold ft
  rw [← integral_complex_ofReal]
  congr 1
  funext u
  push_cast
  congr 2
  ring_nf
  rw [Complex.I_sq]
  ring

lemma ft_conj (g : ℝ → ℝ) (t : ℝ) : ft g (-(t : ℂ)) = (starRingEnd ℂ) (ft g t) := by
  unfold ft
  rw [← integral_conj]
  congr 1
  funext u
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- On the real line the factorised transform is `|ft g t|² ≥ 0`. -/
lemma ft_mul_ft_neg_real (g : ℝ → ℝ) (t : ℝ) :
    ft g t * ft g (-(t : ℂ)) = ((Complex.normSq (ft g t) : ℝ) : ℂ) := by
  rw [ft_conj, Complex.mul_conj]

/-! ## Vanishing radius ⇒ vanishing derivatives, `hfun = ft`, and `IsTestFn` -/

lemma deriv_vanish {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : ℝ → E} {B : ℝ}
    (hF : ∀ u, B < |u| → F u = 0) :
    ∀ u, B < |u| → deriv F u = 0 := by
  intro u hu
  have ho : IsOpen {v : ℝ | B < |v|} := isOpen_lt continuous_const continuous_abs
  have he : F =ᶠ[𝓝 u] fun _ => 0 := by
    filter_upwards [ho.mem_nhds hu] with v hv
    exact hF v hv
  rw [he.deriv_eq]
  simp

/-- `hfun a F z = ∫ F u e^{i z u}` over the whole line when `F` vanishes off `(−a, a)`. -/
lemma hfun_eq_integral {F : ℝ → ℂ} {a B : ℝ} (hB : 0 ≤ B) (hBa : B < a)
    (hF : ∀ u, B < |u| → F u = 0)
    (z : ℂ) : TestFunctions.hfun a F z = ∫ u : ℝ, F u * Complex.exp (I * z * u) := by
  unfold TestFunctions.hfun
  have hB0 : -a ≤ a := by linarith
  rw [intervalIntegral.integral_of_le hB0, ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro u hu
  have : B < |u| := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hu
    rcases hu with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  rw [hF u this, zero_mul]

lemma hfun_ofReal_eq_ft {f : ℝ → ℝ} {a B : ℝ} (hB : 0 ≤ B) (hBa : B < a)
    (hf : ∀ u, B < |u| → f u = 0)
    (z : ℂ) : TestFunctions.hfun a (fun u => (f u : ℂ)) z = ft f z :=
  hfun_eq_integral hB hBa (fun u hu => by simp [hf u hu]) z

/-- A `C²` function vanishing for `|u| > B` is a test function on `[−a, a]` for every `a > B ≥ 0`. -/
lemma isTestFn_of_vanish {F : ℝ → ℂ} {a B : ℝ} (hB : 0 ≤ B) (hBa : B < a) (hc : ContDiff ℝ 2 F)
    (hF : ∀ u, B < |u| → F u = 0) : TestFunctions.IsTestFn a F := by
  have ha : B < |a| := by rw [abs_of_pos (by linarith)]; exact hBa
  have ha' : B < |-a| := by rw [abs_neg]; exact ha
  exact ⟨by linarith, hc, hF _ ha', hF _ ha, deriv_vanish hF _ ha', deriv_vanish hF _ ha⟩

end FleetWeilCriterion
