import FleetWeilOffLine

/-!
# Weil criterion, part 4b: Weil positivity ⇒ RH

From `WeilPositivity` (the right-hand side of Formal Conjectures' `weil_positivity_criterion`):

1. For the probe `h = φ/4 − φ''` (`φ` a smooth bump) and its translates `h(·−L) ± h(·+L)`, the
   explicit formula `weil_explicit_formula` gives `Re ∑ₓ W(tₓ)(2 ± 2 cos(2 tₓ L)) ≥ 0` with
   `W(z) = ft h z · ft h (−z)`, so `|Re ∑ₓ W(tₓ) cos(tₓ y)| ≤ Re ∑ₓ W(tₓ)` for every real `y`.
2. Integrating against `e^{−by²} cos(αy)` gives
   `Re ∑ₓ W(tₓ)(ĝ_{b,α}(tₓ) + ĝ_{b,α}(−tₓ)) ≥ −2 (Re ∑ₓ W(tₓ)) √(π/b)`.
3. `OffLine.false_of_dominant` on the family `{tₓ} ∪ {−tₓ}` rules out an off-line zero; the bump
   is chosen after the dominant point `p`, so that `W p ≠ 0`.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Topology Set MeasureTheory
open scoped Real ComplexConjugate ContDiff

namespace FleetWeilCriterion

namespace WeilRH

open OffLine
open GaussianTest (gaussHat gaussHat_eq norm_gaussHat)

/-! ## Integrability and linearity of `ft` -/

lemma integrable_ft_integrand {g : ℝ → ℝ} (hg : Continuous g) {A : ℝ}
    (hA : ∀ x, A < |x| → g x = 0) (z : ℂ) :
    Integrable (fun u : ℝ => (g u : ℂ) * Complex.exp (I * z * u)) := by
  apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
  exact hasCompactSupport_of_radius (A := A) (fun x hx => by simp [hA x hx])

lemma ft_sub {g₁ g₂ : ℝ → ℝ} (h1 : Continuous g₁) (h2 : Continuous g₂) {A : ℝ}
    (hA1 : ∀ x, A < |x| → g₁ x = 0) (hA2 : ∀ x, A < |x| → g₂ x = 0) (z : ℂ) :
    ft (fun u => g₁ u - g₂ u) z = ft g₁ z - ft g₂ z := by
  unfold ft
  rw [← integral_sub (integrable_ft_integrand h1 hA1 z) (integrable_ft_integrand h2 hA2 z)]
  congr 1; funext u; push_cast; ring

lemma ft_add {g₁ g₂ : ℝ → ℝ} (h1 : Continuous g₁) (h2 : Continuous g₂) {A : ℝ}
    (hA1 : ∀ x, A < |x| → g₁ x = 0) (hA2 : ∀ x, A < |x| → g₂ x = 0) (z : ℂ) :
    ft (fun u => g₁ u + g₂ u) z = ft g₁ z + ft g₂ z := by
  unfold ft
  rw [← integral_add (integrable_ft_integrand h1 hA1 z) (integrable_ft_integrand h2 hA2 z)]
  congr 1; funext u; push_cast; ring

lemma ft_const_mul (c : ℝ) (g : ℝ → ℝ) (z : ℂ) : ft (fun u => c * g u) z = c * ft g z := by
  unfold ft
  rw [← integral_const_mul]
  congr 1; funext u; push_cast; ring

lemma ft_translate (g : ℝ → ℝ) (L : ℝ) (z : ℂ) :
    ft (fun u => g (u - L)) z = Complex.exp (I * z * L) * ft g z := by
  unfold ft
  rw [← integral_const_mul]
  have := integral_sub_right_eq_self
    (fun v : ℝ => (g v : ℂ) * Complex.exp (I * z * ((v + L : ℝ) : ℂ))) (μ := volume) L
  simp only [sub_add_cancel] at this
  rw [this]
  congr 1; funext v
  rw [show I * z * ((v + L : ℝ) : ℂ) = I * z * L + I * z * v by push_cast; ring, Complex.exp_add]
  ring

/-! ## The probe -/

/-- A smooth bump of outer radius `r`. -/
def bumpOf (r : ℝ) (hr : 0 < r) : ContDiffBump (0 : ℝ) := ⟨r / 2, r, by positivity, by linarith⟩

variable {r : ℝ} (hr : 0 < r)

lemma bump_vanish : ∀ u, r < |u| → (bumpOf r hr) u = 0 := by
  intro u hu
  apply Function.notMem_support.mp
  rw [ContDiffBump.support_eq]
  simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, not_lt]
  exact hu.le.trans' (le_of_eq rfl)

lemma bump_admissible : Admissible (bumpOf r hr) (r + 1) r where
  smooth := (bumpOf r hr).contDiff
  B_nonneg := hr.le
  B_lt := by linarith
  vanish := bump_vanish hr

/-- The probe `h = φ/4 − φ''`. -/
def probe (r : ℝ) (hr : 0 < r) (u : ℝ) : ℝ :=
  (1 / 4 : ℝ) * (bumpOf r hr) u - deriv (deriv (bumpOf r hr)) u

lemma probe_smooth : ContDiff ℝ ∞ (probe r hr) := by
  have h1 : ContDiff ℝ ∞ (⇑(bumpOf r hr)) := (bumpOf r hr).contDiff
  have h2 : ContDiff ℝ ∞ (deriv (deriv (⇑(bumpOf r hr)))) := by
    simpa using h1.iterate_deriv 2
  exact (contDiff_const.mul h1).sub h2

lemma probe_vanish : ∀ u, r < |u| → probe r hr u = 0 := by
  intro u hu
  have hA := bump_admissible hr
  simp only [probe, bump_vanish hr u hu, hA.deriv.deriv.vanish u hu, mul_zero, sub_zero]

lemma ft_probe (z : ℂ) : ft (probe r hr) z = (1 / 4 + z ^ 2) * ft (bumpOf r hr) z := by
  have hA := bump_admissible hr
  have hc1 : Continuous (fun u => (1 / 4 : ℝ) * (bumpOf r hr) u) :=
    continuous_const.mul hA.continuous
  have hc2 : Continuous (deriv (deriv (⇑(bumpOf r hr)))) := hA.deriv.deriv.continuous
  have hv1 : ∀ x, r < |x| → (1 / 4 : ℝ) * (bumpOf r hr) x = 0 := fun x hx => by
    simp [bump_vanish hr x hx]
  have hsub := ft_sub hc1 hc2 hv1 hA.deriv.deriv.vanish z
  have hd2 : ft (deriv (deriv (⇑(bumpOf r hr)))) z = -z ^ 2 * ft (bumpOf r hr) z := by
    have := hA.hfun_deriv2 z
    rwa [show cF (deriv (deriv (⇑(bumpOf r hr)))) = fun u => ((deriv (deriv (⇑(bumpOf r hr))) u : ℝ) : ℂ)
        from rfl, hfun_ofReal_eq_ft hA.B_nonneg hA.B_lt hA.deriv.deriv.vanish,
      show cF (⇑(bumpOf r hr)) = fun u => (((bumpOf r hr) u : ℝ) : ℂ) from rfl,
      hfun_ofReal_eq_ft hA.B_nonneg hA.B_lt hA.vanish] at this
  unfold probe
  rw [hsub, ft_const_mul, hd2]
  push_cast
  ring

lemma isTestFunction_probe : IsTestFunction (probe r hr) := by
  constructor
  · have h := ft_neg_half_I (probe r hr)
    rw [ft_probe] at h
    have h0 : (1 / 4 + (-(I / 2)) ^ 2 : ℂ) = 0 := by ring_nf; rw [Complex.I_sq]; ring
    rw [h0, zero_mul] at h
    exact_mod_cast h.symm
  · have h := ft_half_I (probe r hr)
    rw [ft_probe] at h
    have h0 : (1 / 4 + (I / 2) ^ 2 : ℂ) = 0 := by ring_nf; rw [Complex.I_sq]; ring
    rw [h0, zero_mul] at h
    exact_mod_cast h.symm

/-- The bump transform has positive real part on `r |Re z| ≤ 1`. -/
lemma re_ft_bump_pos {z : ℂ} (hz : r * |z.re| ≤ 1) : 0 < (ft (bumpOf r hr) z).re := by
  have hA := bump_admissible hr
  set φ := bumpOf r hr
  have hint := integrable_ft_integrand hA.continuous hA.vanish z
  have hκ : 0 < Real.cos 1 := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], by
    linarith [Real.pi_gt_three]⟩
  set c : ℝ := Real.cos 1 * Real.exp (-(|z.im| * r)) with hc
  have hc0 : 0 < c := by positivity
  have hlow : ∀ u : ℝ, c * φ u ≤ ((φ u : ℂ) * Complex.exp (I * z * u)).re := by
    intro u
    by_cases hu : r < |u|
    · rw [bump_vanish hr u hu]; simp
    · push Not at hu
      rw [Complex.re_ofReal_mul, Complex.exp_re]
      have hre : (I * z * (u : ℂ)).re = -(z.im * u) := by simp
      have him : (I * z * (u : ℂ)).im = z.re * u := by simp
      rw [hre, him, mul_comm c]
      refine mul_le_mul_of_nonneg_left ?_ φ.nonneg
      have h1 : Real.exp (-(|z.im| * r)) ≤ Real.exp (-(z.im * u)) := by
        apply Real.exp_le_exp.2
        have : z.im * u ≤ |z.im| * r := by
          calc z.im * u ≤ |z.im * u| := le_abs_self _
            _ = |z.im| * |u| := abs_mul _ _
            _ ≤ |z.im| * r := mul_le_mul_of_nonneg_left hu (abs_nonneg _)
        linarith
      have h2 : Real.cos 1 ≤ Real.cos (z.re * u) := by
        rw [← Real.cos_abs (z.re * u)]
        apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_gt_three])
        rw [abs_mul]
        calc |z.re| * |u| ≤ |z.re| * r := mul_le_mul_of_nonneg_left hu (abs_nonneg _)
          _ = r * |z.re| := mul_comm _ _
          _ ≤ 1 := hz
      rw [hc]
      calc Real.cos 1 * Real.exp (-(|z.im| * r)) ≤ Real.cos (z.re * u) * Real.exp (-(z.im * u)) :=
            mul_le_mul h2 h1 (Real.exp_pos _).le (by linarith)
        _ = Real.exp (-(z.im * u)) * Real.cos (z.re * u) := mul_comm _ _
  have hφint : Integrable (fun u => c * φ u) :=
    (hA.continuous.integrable_of_hasCompactSupport (hasCompactSupport_of_radius hA.vanish)).const_mul c
  have hmono := integral_mono hφint hint.re hlow
  rw [integral_const_mul] at hmono
  have hpos : 0 < c * ∫ u, φ u := mul_pos hc0 φ.integral_pos
  unfold ft
  rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm _ hint]
  simp only [Complex.reCLM_apply]
  simp only [RCLike.re_to_complex] at hmono
  linarith

/-! ## Bounds on the probe transform -/

/-- The zero ordinates of the canonical enumeration. -/
abbrev tz (x : ZeroSumLimit.Index) : ℂ := OffLineDetection.t x

lemma probe_isTestFn : TestFunctions.IsTestFn (r + 1) (cF (probe r hr)) :=
  isTestFn_of_vanish hr.le (by linarith)
    (Complex.ofRealCLM.contDiff.comp ((probe_smooth hr).of_le (by norm_cast)))
    (fun u hu => by simp [cF, probe_vanish hr u hu])

lemma ft_probe_eq_hfun (z : ℂ) :
    ft (probe r hr) z = TestFunctions.hfun (r + 1) (cF (probe r hr)) z :=
  (hfun_ofReal_eq_ft hr.le (by linarith) (probe_vanish hr) z).symm

/-- `‖ft h z‖ ≤ CB` on the strip `|Im z| ≤ 1/2`. -/
lemma exists_ft_probe_bound : ∃ CB : ℝ, 0 ≤ CB ∧ ∀ z : ℂ, |z.im| ≤ 1 / 2 →
    ‖ft (probe r hr) z‖ ≤ CB := by
  set I0 := ∫ u in (-(r + 1))..(r + 1), ‖cF (probe r hr) u‖
  have hI0 : 0 ≤ I0 := intervalIntegral.integral_nonneg (by linarith) (fun u _ => norm_nonneg _)
  refine ⟨I0 * Real.exp ((r + 1) * (1 / 2)), by positivity, fun z hz => ?_⟩
  rw [ft_probe_eq_hfun, ← TestFunctions.Gt_half_add_I_mul]
  refine (TestFunctions.Gt_bound (probe_isTestFn hr) _).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hI0
  have : (1 / 2 + I * z).re - 1 / 2 = -z.im := by simp
  rw [this, abs_neg]
  exact mul_le_mul_of_nonneg_left hz (by linarith)

/-- The weight `W(z) = ft h z · ft h (−z)`. -/
def Wt (r : ℝ) (hr : 0 < r) (z : ℂ) : ℂ := ft (probe r hr) z * ft (probe r hr) (-z)

lemma Wt_neg (z : ℂ) : Wt r hr (-z) = Wt r hr z := by
  unfold Wt; rw [neg_neg, mul_comm]

lemma ft_conj_general (g : ℝ → ℝ) (z : ℂ) : ft g (conj z) = conj (ft g (-z)) := by
  unfold ft
  rw [← integral_conj]
  congr 1; funext u
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_neg]
  ring

lemma Wt_conj (z : ℂ) : Wt r hr (conj z) = conj (Wt r hr z) := by
  unfold Wt
  rw [ft_conj_general, ← map_neg, ft_conj_general, neg_neg, map_mul, mul_comm]

lemma abs_im_tz_le (x : ZeroSumLimit.Index) : |(tz x).im| ≤ 1 / 2 :=
  (OffLineDetection.abs_t_im_lt x).le

lemma summable_norm_Wt : Summable (fun x : ZeroSumLimit.Index => ‖Wt r hr (tz x)‖) := by
  obtain ⟨CB, hCB0, hCB⟩ := exists_ft_probe_bound hr
  have hs := (ZeroSumLimit.summable_norm_Gt ZeroSumLimit.multEnum_canonical
    (probe_isTestFn hr)).mul_right CB
  refine hs.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_)
  unfold Wt
  rw [norm_mul]
  have h1 : ft (probe r hr) (tz x) =
      TestFunctions.Gt (r + 1) (cF (probe r hr)) (ZeroSumLimit.canonical x) := by
    rw [ft_probe_eq_hfun, TestFunctions.Gt_at_ordinate]; rfl
  rw [h1]
  refine mul_le_mul_of_nonneg_left (hCB _ ?_) (norm_nonneg _)
  rw [Complex.neg_im, abs_neg]; exact abs_im_tz_le x

lemma norm_cos_le (w : ℂ) : ‖Complex.cos w‖ ≤ Real.exp |w.im| := by
  rw [Complex.cos, norm_div, Complex.norm_two]
  have h1 : ‖Complex.exp (w * I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.2; simp [neg_le_abs]
  have h2 : ‖Complex.exp (-w * I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.2; simp [le_abs_self]
  have := norm_add_le (Complex.exp (w * I)) (Complex.exp (-w * I))
  linarith

lemma norm_cos_tz_le (x : ZeroSumLimit.Index) (y : ℝ) :
    ‖Complex.cos (tz x * y)‖ ≤ Real.exp (|y| / 2) := by
  refine (norm_cos_le _).trans (Real.exp_le_exp.2 ?_)
  have : (tz x * (y : ℂ)).im = (tz x).im * y := by simp
  rw [this, abs_mul]
  have := abs_im_tz_le x
  nlinarith [abs_nonneg y, abs_nonneg (tz x).im]

lemma summable_Wt_cos (y : ℝ) :
    Summable (fun x : ZeroSumLimit.Index => Wt r hr (tz x) * Complex.cos (tz x * y)) := by
  refine Summable.of_norm_bounded ((summable_norm_Wt hr).mul_right (Real.exp (|y| / 2))) (fun x => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_cos_tz_le x y) (norm_nonneg _)

/-! ## Translates of the probe and the bound on `Φ` -/

/-- `h(u − L) + σ h(u + L)`. -/
def trans (r : ℝ) (hr : 0 < r) (σ L : ℝ) (u : ℝ) : ℝ :=
  probe r hr (u - L) + σ * probe r hr (u + L)

lemma trans_vanish (σ L : ℝ) : ∀ u, r + |L| < |u| → trans r hr σ L u = 0 := by
  intro u hu
  have h1 : r < |u - L| := by
    have := abs_sub_abs_le_abs_sub u L; linarith
  have h2 : r < |u + L| := by
    have := abs_sub_abs_le_abs_sub u (-L)
    rw [abs_neg, sub_neg_eq_add] at this; linarith
  simp [trans, probe_vanish hr _ h1, probe_vanish hr _ h2]

lemma trans_smooth (σ L : ℝ) : ContDiff ℝ ∞ (trans r hr σ L) := by
  have h := probe_smooth hr
  exact (h.comp (contDiff_id.sub contDiff_const)).add
    (contDiff_const.mul (h.comp (contDiff_id.add contDiff_const)))

lemma ft_trans (σ L : ℝ) (z : ℂ) :
    ft (trans r hr σ L) z = ft (probe r hr) z *
      (Complex.exp (I * z * L) + σ * Complex.exp (-(I * z * L))) := by
  have hc := (probe_smooth hr).continuous
  have hv1 : ∀ u, r + |L| < |u| → probe r hr (u - L) = 0 := by
    intro u hu; exact probe_vanish hr _ (by have := abs_sub_abs_le_abs_sub u L; linarith)
  have hv2 : ∀ u, r + |L| < |u| → σ * probe r hr (u + L) = 0 := by
    intro u hu
    have := abs_sub_abs_le_abs_sub u (-L)
    rw [abs_neg, sub_neg_eq_add] at this
    simp [probe_vanish hr _ (by linarith : r < |u + L|)]
  unfold trans
  rw [ft_add (g₁ := fun u => probe r hr (u - L)) (g₂ := fun u => σ * probe r hr (u + L))
    (hc.comp (continuous_id.sub continuous_const))
    (continuous_const.mul (hc.comp (continuous_id.add continuous_const))) hv1 hv2]
  rw [ft_const_mul, ft_translate]
  have : ft (fun u => probe r hr (u + L)) z = Complex.exp (I * z * ((-L : ℝ) : ℂ)) * ft (probe r hr) z := by
    rw [← ft_translate]; congr 1; funext u; rw [sub_neg_eq_add]
  rw [this]
  push_cast
  ring_nf

lemma isTestFunction_trans (σ L : ℝ) : IsTestFunction (trans r hr σ L) := by
  constructor
  · have h := ft_neg_half_I (trans r hr σ L)
    rw [ft_trans, ft_neg_half_I, (isTestFunction_probe hr).1] at h
    simp only [Complex.ofReal_zero, zero_mul] at h
    exact_mod_cast h.symm
  · have h := ft_half_I (trans r hr σ L)
    rw [ft_trans, ft_half_I, (isTestFunction_probe hr).2] at h
    simp only [Complex.ofReal_zero, zero_mul] at h
    exact_mod_cast h.symm

lemma ft_trans_mul (σ L : ℝ) (hσ : σ ^ 2 = 1) (z : ℂ) :
    ft (trans r hr σ L) z * ft (trans r hr σ L) (-z) =
      Wt r hr z * (2 + 2 * σ * Complex.cos (z * (2 * L))) := by
  rw [ft_trans, ft_trans]
  unfold Wt
  have hσC : (σ : ℂ) ^ 2 = 1 := by exact_mod_cast hσ
  have e1 : Complex.exp (I * z * L) * Complex.exp (-(I * z * L)) = 1 := by
    rw [← Complex.exp_add]; simp
  rw [Complex.cos]
  have e2 : Complex.exp (z * (2 * L) * I) = Complex.exp (I * z * L) ^ 2 := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have e3 : Complex.exp (-(z * (2 * L)) * I) = Complex.exp (-(I * z * L)) ^ 2 := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [e2, e3]
  have e4 : Complex.exp (I * -z * L) = Complex.exp (-(I * z * L)) := by congr 1; ring
  have e5 : Complex.exp (-(I * -z * L)) = Complex.exp (I * z * L) := by congr 1; ring
  rw [e4, e5]
  set a := Complex.exp (I * z * L)
  set b := Complex.exp (-(I * z * L))
  linear_combination (ft (probe r hr) z * ft (probe r hr) (-z)) * ((1 + (σ : ℂ) ^ 2) * e1 + hσC)

/-! ## From Weil positivity to a bound on `Φ(y) = ∑ₓ W(tₓ) cos(tₓ y)` -/

lemma re_tsum_nonneg_of_weil (hW : WeilPositivity) {g : ℝ → ℝ} (hs : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (ht : IsTestFunction g) :
    0 ≤ (∑' x : ZeroSumLimit.Index, ft g (tz x) * ft g (-(tz x))).re := by
  have hE := weil_explicit_formula ZeroSumLimit.multEnum_canonical hs hc ht
  have heq : (∑' x : ZeroSumLimit.Index, ft g (tz x) * ft g (-(tz x))) =
      -((weilSum (auto g) : ℝ) : ℂ) := hE.tsum_eq
  rw [heq, Complex.neg_re, Complex.ofReal_re]
  have h := hW ⟨⟨g, hs.continuous⟩, hc⟩ hs ht
  change weilSum (auto g) ≤ 0 at h
  linarith

theorem Phi_bound (hW : WeilPositivity) (y : ℝ) :
    |(∑' x : ZeroSumLimit.Index, Wt r hr (tz x) * Complex.cos (tz x * y)).re| ≤
      (∑' x : ZeroSumLimit.Index, Wt r hr (tz x)).re := by
  have hS1 : Summable (fun x : ZeroSumLimit.Index => Wt r hr (tz x)) := (summable_norm_Wt hr).of_norm
  have hS2 := summable_Wt_cos hr y
  have key : ∀ σ : ℝ, σ ^ 2 = 1 → 0 ≤ 2 * (∑' x : ZeroSumLimit.Index, Wt r hr (tz x)).re +
      2 * σ * (∑' x : ZeroSumLimit.Index, Wt r hr (tz x) * Complex.cos (tz x * y)).re := by
    intro σ hσ
    have h0 := re_tsum_nonneg_of_weil hW (trans_smooth hr σ (y / 2))
      (hasCompactSupport_of_radius (trans_vanish hr σ (y / 2))) (isTestFunction_trans hr σ (y / 2))
    simp_rw [ft_trans_mul hr σ (y / 2) hσ] at h0
    have hfun : (fun x : ZeroSumLimit.Index => Wt r hr (tz x) *
        (2 + 2 * (σ : ℂ) * Complex.cos (tz x * (2 * ((y / 2 : ℝ) : ℂ))))) =
        fun x => ((2 : ℝ) : ℂ) * Wt r hr (tz x) +
          ((2 * σ : ℝ) : ℂ) * (Wt r hr (tz x) * Complex.cos (tz x * y)) := by
      funext x; push_cast; ring_nf
    rw [hfun, (hS1.mul_left _).tsum_add (hS2.mul_left _), tsum_mul_left, tsum_mul_left,
      Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul] at h0
    linarith
  have h1 := key 1 (by norm_num)
  have h2 := key (-1) (by norm_num)
  rw [abs_le]
  constructor <;> linarith

/-! ## Gaussian smoothing -/

lemma integrable_gauss_mul {b : ℝ} (hb : 0 < b) (β : ℝ) (c : ℂ) :
    Integrable (fun y : ℝ => GaussianTest.gauss b β y * Complex.exp (I * c * y)) := by
  have hbr : 0 < (b : ℂ).re := by simpa using hb
  refine (integrable_cexp_quadratic hbr (I * (c - β)) 0).congr (Eventually.of_forall fun y => ?_)
  simp only [GaussianTest.gauss]
  rw [← Complex.exp_add]
  congr 1; ring

lemma gaussHat_neg_alpha {b : ℝ} (hb : 0 < b) (α : ℝ) (z : ℂ) :
    gaussHat b (-α) z = gaussHat b α (-z) := by
  rw [gaussHat_eq hb, gaussHat_eq hb]
  congr 3; push_cast; ring

/-- `∫ cos(zy) e^{−by²} cos(αy) dy = (ĝ_{b,α}(z) + ĝ_{b,α}(−z)) / 2`. -/
theorem integral_cos_mul_gauss {b : ℝ} (hb : 0 < b) (α : ℝ) (z : ℂ) :
    ∫ y : ℝ, Complex.cos (z * y) * ((Real.exp (-b * y ^ 2) * Real.cos (α * y) : ℝ) : ℂ) =
      (1 / 2) * (gaussHat b α z + gaussHat b α (-z)) := by
  have hpt : ∀ y : ℝ, Complex.cos (z * y) * ((Real.exp (-b * y ^ 2) * Real.cos (α * y) : ℝ) : ℂ) =
      (1 / 4) * ((GaussianTest.gauss b α y * Complex.exp (I * z * y) +
        GaussianTest.gauss b α y * Complex.exp (I * (-z) * y)) +
        (GaussianTest.gauss b (-α) y * Complex.exp (I * z * y) +
        GaussianTest.gauss b (-α) y * Complex.exp (I * (-z) * y))) := by
    intro y
    set E1 := Complex.exp (-(b : ℂ) * (y : ℂ) ^ 2)
    set Ap := Complex.exp (I * (α : ℂ) * y)
    set Am := Complex.exp (-(I * (α : ℂ) * y))
    have g1 : GaussianTest.gauss b α y = E1 * Am := by
      simp only [GaussianTest.gauss, E1, Am]; rw [← Complex.exp_add]; congr 1
    have g2 : GaussianTest.gauss b (-α) y = E1 * Ap := by
      simp only [GaussianTest.gauss, E1, Ap]; rw [← Complex.exp_add]; congr 1; push_cast; try ring
    have hw : ((Real.exp (-b * y ^ 2) * Real.cos (α * y) : ℝ) : ℂ) = E1 * ((Ap + Am) / 2) := by
      rw [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_cos, Complex.cos]
      simp only [E1, Ap, Am]
      congr 2
      · push_cast; ring
      · congr 1 <;> congr 1 <;> push_cast <;> ring
    have hc : Complex.cos (z * y) = (Complex.exp (I * z * y) + Complex.exp (I * (-z) * y)) / 2 := by
      rw [Complex.cos]; congr 2 <;> congr 1 <;> ring
    rw [hw, hc, g1, g2]
    ring
  simp_rw [hpt]
  have i1 := integrable_gauss_mul hb α z
  have i2 := integrable_gauss_mul hb α (-z)
  have i3 := integrable_gauss_mul hb (-α) z
  have i4 := integrable_gauss_mul hb (-α) (-z)
  rw [integral_const_mul, integral_add ?_ ?_, integral_add i1 i2, integral_add i3 i4]
  rotate_left
  · exact i1.add i2
  · exact i3.add i4
  have e1 : ∫ y : ℝ, GaussianTest.gauss b α y * Complex.exp (I * z * y) = gaussHat b α z := rfl
  have e2 : ∫ y : ℝ, GaussianTest.gauss b α y * Complex.exp (I * (-z) * y) = gaussHat b α (-z) := rfl
  have e3 : ∫ y : ℝ, GaussianTest.gauss b (-α) y * Complex.exp (I * z * y) = gaussHat b (-α) z := rfl
  have e4 : ∫ y : ℝ, GaussianTest.gauss b (-α) y * Complex.exp (I * (-z) * y) =
      gaussHat b (-α) (-z) := rfl
  rw [e1, e2, e3, e4, gaussHat_neg_alpha hb, gaussHat_neg_alpha hb, neg_neg]
  ring

lemma integrable_exp_abs_gauss {b : ℝ} (hb : 0 < b) :
    Integrable (fun y : ℝ => Real.exp (|y| / 2) * Real.exp (-b * y ^ 2)) := by
  have hbr : 0 < (b : ℂ).re := by simpa using hb
  have h1 := (integrable_cexp_quadratic hbr (1 / 2) 0).norm
  have h2 := (integrable_cexp_quadratic hbr (-(1 / 2)) 0).norm
  refine (h1.add h2).mono' (by fun_prop) (Eventually.of_forall fun y => ?_)
  simp only [Pi.add_apply, Complex.norm_exp]
  rw [Real.norm_eq_abs, abs_of_pos (by positivity), ← Real.exp_add]
  have e1 : (-(b : ℂ) * (y : ℂ) ^ 2 + 1 / 2 * y + 0).re = -b * y ^ 2 + y / 2 := by
    simp [sq]; ring
  have e2 : (-(b : ℂ) * (y : ℂ) ^ 2 + -(1 / 2) * y + 0).re = -b * y ^ 2 - y / 2 := by
    simp [sq]; ring
  rw [e1, e2]
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy, show y / 2 + -b * y ^ 2 = -b * y ^ 2 + y / 2 by ring]
    linarith [Real.exp_pos (-b * y ^ 2 - y / 2)]
  · rw [abs_of_nonpos hy, show -y / 2 + -b * y ^ 2 = -b * y ^ 2 - y / 2 by ring]
    linarith [Real.exp_pos (-b * y ^ 2 + y / 2)]

/-- **The smoothed bound.** `Re ∑ₓ W(tₓ)(ĝ(tₓ) + ĝ(−tₓ)) ≥ −2 (Re ∑ₓ W(tₓ)) √(π/b)`. -/
theorem gauss_bound (hW : WeilPositivity) {b : ℝ} (hb : 0 < b) (α : ℝ) :
    -(Real.sqrt (π / b) * (2 * (∑' x : ZeroSumLimit.Index, Wt r hr (tz x)).re)) ≤
      (∑' x : ZeroSumLimit.Index, Wt r hr (tz x) *
        (gaussHat b α (tz x) + gaussHat b α (-(tz x)))).re := by
  set K0 := (∑' x : ZeroSumLimit.Index, Wt r hr (tz x)).re
  set w : ℝ → ℝ := fun y => Real.exp (-b * y ^ 2) * Real.cos (α * y) with hw
  set F : ZeroSumLimit.Index → ℝ → ℂ :=
    fun x y => Wt r hr (tz x) * (Complex.cos (tz x * y) * (w y : ℂ)) with hF
  set J := ∫ y : ℝ, Real.exp (|y| / 2) * Real.exp (-b * y ^ 2)
  have hJint := integrable_exp_abs_gauss hb
  have hFb : ∀ x y, ‖F x y‖ ≤ ‖Wt r hr (tz x)‖ * (Real.exp (|y| / 2) * Real.exp (-b * y ^ 2)) := by
    intro x y
    simp only [hF, hw, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [abs_of_pos (Real.exp_pos _)]
    have hc := Real.abs_cos_le_one (α * y)
    have := norm_cos_tz_le x y
    calc ‖Complex.cos (tz x * y)‖ * (Real.exp (-b * y ^ 2) * |Real.cos (α * y)|)
        ≤ Real.exp (|y| / 2) * (Real.exp (-b * y ^ 2) * 1) := by
          apply mul_le_mul this (mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le)
            (by positivity) (Real.exp_pos _).le
      _ = _ := by ring
  have hFc : ∀ x, Continuous (F x) := fun x => by simp only [hF, hw]; fun_prop
  have hFint : ∀ x, Integrable (F x) := fun x =>
    (hJint.const_mul ‖Wt r hr (tz x)‖).mono' (hFc x).aestronglyMeasurable
      (Eventually.of_forall (hFb x))
  have hFnorm : ∀ x, ∫ y, ‖F x y‖ ≤ ‖Wt r hr (tz x)‖ * J := by
    intro x
    rw [← integral_const_mul]
    exact integral_mono (hFint x).norm (hJint.const_mul _) (hFb x)
  have hsumJ : Summable (fun x : ZeroSumLimit.Index => ‖Wt r hr (tz x)‖ * J) :=
    (summable_norm_Wt hr).mul_right J
  have hFval : ∀ x, ∫ y, F x y = Wt r hr (tz x) * ((1 / 2) * (gaussHat b α (tz x) + gaussHat b α (-(tz x)))) := by
    intro x
    simp only [hF]
    rw [integral_const_mul, integral_cos_mul_gauss hb α]
  -- the real-valued function `R y = Re Φ(y) · w(y)`
  set R : ℝ → ℝ := fun y =>
    (∑' x : ZeroSumLimit.Index, Wt r hr (tz x) * Complex.cos (tz x * y)).re * w y with hR
  have hRsum : ∀ y, R y = ∑' x, (F x y).re := by
    intro y
    simp only [hR, hF]
    rw [← Complex.re_mul_ofReal, ← tsum_mul_right,
      Complex.re_tsum ((summable_Wt_cos hr y).mul_right _)]
    congr 1; funext x; ring_nf
  -- bound on `∫ R`
  have hRbound : |∫ y, R y| ≤ K0 * Real.sqrt (π / b) := by
    have hg : Integrable (fun y : ℝ => K0 * Real.exp (-b * y ^ 2)) :=
      (integrable_exp_neg_mul_sq hb).const_mul K0
    have h := norm_integral_le_of_norm_le (f := R) hg (Eventually.of_forall fun y => ?_)
    · rw [Real.norm_eq_abs, integral_const_mul, integral_gaussian] at h
      exact h
    · simp only [hR, hw, Real.norm_eq_abs, abs_mul]
      have hP := Phi_bound hr hW y
      rw [abs_of_pos (Real.exp_pos _)]
      have hc := Real.abs_cos_le_one (α * y)
      have hK0 : 0 ≤ K0 := (abs_nonneg _).trans hP
      calc _ ≤ K0 * (Real.exp (-b * y ^ 2) * 1) :=
            mul_le_mul hP (mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le) (by positivity) hK0
        _ = _ := by ring
  -- `∫ R = Re ∑ ∫ F`
  have hRint : ∫ y, R y = (∑' x, ∫ y, F x y).re := by
    simp_rw [hRsum]
    have hint : ∀ x, Integrable (fun y => (F x y).re) := fun x => (hFint x).re
    have hsum : Summable (fun x => ∫ y, ‖(F x y).re‖) := by
      refine hsumJ.of_nonneg_of_le (fun x => integral_nonneg fun y => norm_nonneg _) (fun x => ?_)
      refine le_trans (integral_mono (hint x).norm (hFint x).norm (fun y => ?_)) (hFnorm x)
      simp only [Real.norm_eq_abs]
      exact Complex.abs_re_le_norm _
    rw [← integral_tsum_of_summable_integral_norm hint hsum]
    have hs2 : Summable (fun x => ∫ y, F x y) := by
      refine Summable.of_norm_bounded hsumJ (fun x => ?_)
      exact (norm_integral_le_integral_norm _).trans (hFnorm x)
    rw [Complex.re_tsum hs2]
    congr 1; funext x
    have := integral_re (hFint x)
    simpa using this
  have hmain : (∑' x : ZeroSumLimit.Index, Wt r hr (tz x) *
      (gaussHat b α (tz x) + gaussHat b α (-(tz x)))).re = 2 * ∫ y, R y := by
    rw [hRint]
    simp_rw [hFval]
    have : (fun x : ZeroSumLimit.Index => Wt r hr (tz x) *
        ((1 / 2) * (gaussHat b α (tz x) + gaussHat b α (-(tz x))))) =
        fun x => ((1 / 2 : ℝ) : ℂ) * (Wt r hr (tz x) * (gaussHat b α (tz x) + gaussHat b α (-(tz x)))) := by
      funext x; push_cast; ring
    rw [this, tsum_mul_left, Complex.re_ofReal_mul]
    ring
  rw [hmain]
  have := (abs_le.mp hRbound).1
  linarith

/-! ## The doubled family `{tₓ} ∪ {−tₓ}` -/

/-- The ordinates together with their negatives. -/
def τ2 : ZeroSumLimit.Index ⊕ ZeroSumLimit.Index → ℂ := Sum.elim tz (fun x => -(tz x))

lemma strip_τ2 : Strip τ2 where
  im_sq := by
    rintro (x | x)
    · exact OffLineDetection.t_im_sq_lt x
    · simpa [τ2] using OffLineDetection.t_im_sq_lt x
  finite := by
    intro α
    refine (((OffLineDetection.Z_finite α).image Sum.inl).union
      ((OffLineDetection.Z_finite (-α)).image Sum.inr)).subset ?_
    rintro (x | x) hx
    · exact Or.inl ⟨x, hx, rfl⟩
    · refine Or.inr ⟨x, ?_, rfl⟩
      change |(OffLineDetection.t x).re - -α| < 1
      have hx' : |(-(tz x)).re - α| < 1 := hx
      rw [Complex.neg_re, show -(tz x).re - α = -((tz x).re - -α) by ring, abs_neg] at hx'
      exact hx'
  summable := by
    apply Summable.sum
    · exact OffLineDetection.summable_inv_one_add_sq_re
    · simpa [τ2, Function.comp_def] using OffLineDetection.summable_inv_one_add_sq_re

lemma τ2_inl (x : ZeroSumLimit.Index) : τ2 (Sum.inl x) = tz x := rfl
lemma τ2_inr (x : ZeroSumLimit.Index) : τ2 (Sum.inr x) = -(tz x) := rfl

lemma tsum_τ2 {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (α : ℝ) {CW : ℝ}
    (hWb : ∀ i, ‖Wt r hr (τ2 i)‖ ≤ CW) :
    (∑' i, Wt r hr (τ2 i) * gaussHat b α (τ2 i)) =
      ∑' x : ZeroSumLimit.Index, Wt r hr (tz x) * (gaussHat b α (tz x) + gaussHat b α (-(tz x))) := by
  set f : ZeroSumLimit.Index ⊕ ZeroSumLimit.Index → ℂ := fun i => Wt r hr (τ2 i) * gaussHat b α (τ2 i)
    with hf
  have hs : Summable f := summable_weighted strip_τ2 hb hb1 α (fun i => Wt r hr (τ2 i)) hWb
  have h1 : Summable (fun x => f (Sum.inl x)) := hs.comp_injective Sum.inl_injective
  have h2 : Summable (fun x => f (Sum.inr x)) := hs.comp_injective Sum.inr_injective
  have hsplit : ∑' i, f i = ∑' x, f (Sum.inl x) + ∑' x, f (Sum.inr x) := Summable.tsum_sum h1 h2
  rw [hsplit, ← h1.tsum_add h2]
  congr 1; funext x
  simp only [hf, τ2_inl, τ2_inr, Wt_neg]
  ring

/-! ## Weil positivity ⇒ RH -/

lemma one_quarter_add_sq_ne {p : ℂ} (hp : p.im ^ 2 < 1 / 4) : (1 / 4 + p ^ 2 : ℂ) ≠ 0 := by
  intro h0
  have hre : 1 / 4 + (p.re ^ 2 - p.im ^ 2) = 0 := by
    have := congrArg Complex.re h0
    simp only [Complex.add_re, sq, Complex.mul_re, Complex.zero_re] at this
    norm_num at this
    nlinarith
  have him : p.re * p.im = 0 := by
    have := congrArg Complex.im h0
    simp only [Complex.add_im, sq, Complex.mul_im, Complex.zero_im] at this
    norm_num at this
    linarith
  rcases mul_eq_zero.mp him with h | h
  · rw [h] at hre; nlinarith
  · rw [h] at hre; nlinarith [sq_nonneg p.re]

/-- **Weil positivity ⇒ RH**: the right-hand side of Formal Conjectures' `weil_positivity_criterion`
implies Mathlib's `RiemannHypothesis`. -/
theorem RH_of_weilPositivity (hW : WeilPositivity) : RiemannHypothesis := by
  apply Reduction.RH_of_nontrivial_zeros_on_critical_line
  intro ρ hρ
  obtain ⟨x, hx⟩ := ZeroSumLimit.multEnum_canonical.exists_index hρ
  have him : (tz x).im = 0 := by
    by_contra hne
    have hτ := strip_τ2
    obtain ⟨α, M, ε, p, S, hM, hε, hθ, hS, hSne, hSp, hSM, hgap⟩ :=
      exists_dominant hτ (i₀ := Sum.inl x) hne
    obtain ⟨i, hi⟩ := hSne
    have hpim : p.im ^ 2 < 1 / 4 := by
      have := hτ.im_sq i
      rcases hSp i hi with h | h
      · rwa [h] at this
      · rw [h] at this; simpa using this
    have hr : 0 < 1 / (|p.re| + 1) := by positivity
    set r := 1 / (|p.re| + 1)
    have hrp : r * |p.re| ≤ 1 := by
      simp only [r]
      rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
      linarith
    have hWp : Wt r hr p ≠ 0 := by
      unfold Wt
      rw [ft_probe, ft_probe, neg_sq]
      have h1 := re_ft_bump_pos hr hrp
      have h2 := re_ft_bump_pos hr (z := -p) (by rw [Complex.neg_re, abs_neg]; exact hrp)
      have hq := one_quarter_add_sq_ne hpim
      refine mul_ne_zero (mul_ne_zero hq ?_) (mul_ne_zero hq ?_)
      · intro h0; rw [h0] at h1; simp at h1
      · intro h0; rw [h0] at h2; simp at h2
    obtain ⟨CB, hCB0, hCB⟩ := exists_ft_probe_bound hr
    have hWb : ∀ j, ‖Wt r hr (τ2 j)‖ ≤ CB * CB := by
      intro j
      have hj : |(τ2 j).im| ≤ 1 / 2 := by
        have := hτ.im_sq j
        rw [← abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        exact (sq_le_sq.mp (by nlinarith))
      unfold Wt
      rw [norm_mul]
      exact mul_le_mul (hCB _ hj) (hCB _ (by rw [Complex.neg_im, abs_neg]; exact hj))
        (norm_nonneg _) hCB0
    refine false_of_dominant hτ hM hε hθ hS ⟨i, hi⟩ hSp hSM hgap (Wt r hr) hWp (Wt_conj hr p)
      (by positivity) hWb (K := 2 * (∑' y : ZeroSumLimit.Index, Wt r hr (tz y)).re) ?_
    intro b hb hb1
    rw [tsum_τ2 hr hb hb1 α hWb]
    exact gauss_bound hr hW hb α
  rw [show tz x = OffLineDetection.t x from rfl, OffLineDetection.t_im, hx] at him
  linarith

end WeilRH

open WeilRH in
/-- **Formal Conjectures' `weil_positivity_criterion`, proved.** -/
theorem weil_positivity_criterion : WeilPositivityCriterion :=
  ⟨weilPositivity_of_RH, RH_of_weilPositivity⟩

end FleetWeilCriterion
