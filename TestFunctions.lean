import Mathlib
import Reduction
import ExplicitFormula
import HorizontalDecay

/-!
# Test functions for the explicit formula: the transform `Gt` and its decay

For a test function `g : ℝ → ℂ` living on `[-a, a]` we define the two-sided Laplace
transform centred at `½`,

  `Gt a g s := ∫ u in -a..a, g u · exp ((s − ½) u)`,

so that `Gt a g (½ + i t) = ∫ g(u) e^{i t u} du =: hfun a g t` is the "h" of the explicit
formula, and on the line `s = c + 2πiξ` of `ExplicitFormula` it is a Fourier transform
`𝓕 (g · e^{(c−½)u}) (−ξ)` in Mathlib's normalisation.

**Proven unconditionally** (for `IsTestFn a g`: `0 ≤ a`, `g ∈ C²(ℝ)`, `g` and `g'`
vanish at `±a`; continuity alone where noted):

* `Gt_differentiable` — `Gt a g` is entire (differentiation under the integral).
* `Gt_bound` — `‖Gt a g s‖ ≤ (∫‖g‖) · exp (a |Re s − ½|)`.
* `sq_mul_Gt_eq` / `Gt_decay` — two integrations by parts give
  `(s−½)² Gt a g s = ∫ g'' e^{(s−½)u}` and hence
  `‖Gt a g s‖ ≤ C₂ · exp (a |Re s − ½|) / (Im s)²` with `C₂ = ∫‖g''‖`.
* `Gt_at_ordinate` — `Gt a g ρ = hfun a g (ordinate ρ)` (pure algebra).
* `integrable_on_vertical_line` — `t ↦ Gt a g (σ + i t)` is integrable on `ℝ`.
* `horizontal_vanishing` — if `‖F(σ + iT)‖ ≤ B (log T)²` on `σ₁ ≤ σ ≤ σ₂`, `T ≥ 4`, then
  `∫ σ in σ₁..σ₂, F(σ+iT) Gt a g (σ+iT) → 0` as `T → ∞`.
* `Gt_line_eq_fourier`, `Gt_half_line_eq_fourier` — the relation to Mathlib's `𝓕`.

**Hypothesis-dependent:** `horizontal_vanishing` takes the polylog growth bound on `F`
as an explicit hypothesis (nothing here proves any bound on `ζ'/ζ`).

**Not proven:** nothing about `ζ`; this file is pure test-function analysis.
No `sorry`, no custom axioms.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Complex Filter Topology Set
open scoped FourierTransform Real

namespace TestFunctions

/-! ## Definitions -/

/-- The two-sided Laplace transform of `g` on `[-a, a]`, centred at `½`. -/
def Gt (a : ℝ) (g : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ u in (-a)..a, g u * Complex.exp ((s - 1 / 2) * u)

/-- The "h" of the explicit formula: `hfun a g t = ∫ g(u) e^{i t u} du`. -/
def hfun (a : ℝ) (g : ℝ → ℂ) (t : ℂ) : ℂ :=
  ∫ u in (-a)..a, g u * Complex.exp (I * t * u)

/-- The `L¹` norm of `g''` on `[-a, a]` — the constant in the decay bound. -/
def C₂ (a : ℝ) (g : ℝ → ℂ) : ℝ := ∫ u in (-a)..a, ‖deriv (deriv g) u‖

/-- The test-function class: `0 ≤ a`, `g` is `C²` on `ℝ`, and `g`, `g'` vanish at `±a`. -/
structure IsTestFn (a : ℝ) (g : ℝ → ℂ) : Prop where
  nonneg : 0 ≤ a
  smooth : ContDiff ℝ 2 g
  left : g (-a) = 0
  right : g a = 0
  deriv_left : deriv g (-a) = 0
  deriv_right : deriv g a = 0

/-! ## Regularity consequences of `C²` -/

/-- A test function is continuous. -/
lemma IsTestFn.continuous {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) : Continuous g :=
  h.smooth.continuous

/-- A test function is differentiable. -/
lemma IsTestFn.differentiable {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) : Differentiable ℝ g :=
  h.smooth.differentiable (by norm_num)

/-- The derivative of a test function is `C¹`. -/
lemma IsTestFn.contDiff_deriv {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) :
    ContDiff ℝ 1 (deriv g) := by
  have h2 : ContDiff ℝ (1 + 1) g := by rw [one_add_one_eq_two]; exact h.smooth
  exact (contDiff_succ_iff_deriv.mp h2).2.2

/-- The derivative of a test function is continuous. -/
lemma IsTestFn.continuous_deriv {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) :
    Continuous (deriv g) :=
  h.contDiff_deriv.continuous

/-- The derivative of a test function is differentiable. -/
lemma IsTestFn.differentiable_deriv {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) :
    Differentiable ℝ (deriv g) :=
  h.contDiff_deriv.differentiable (by norm_num)

/-- The second derivative of a test function is continuous. -/
lemma IsTestFn.continuous_deriv2 {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) :
    Continuous (deriv (deriv g)) :=
  h.contDiff_deriv.continuous_deriv le_rfl

/-- `C₂ a g ≥ 0`. -/
lemma C₂_nonneg {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) : 0 ≤ C₂ a g :=
  intervalIntegral.integral_nonneg (by linarith [h.nonneg]) fun _ _ => norm_nonneg _

/-! ## The exponential kernel `u ↦ exp (w u)` -/

/-- `d/du exp (w u) = w exp (w u)` for real `u`. -/
lemma hasDerivAt_exp_mul_ofReal (w : ℂ) (u : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.exp (w * x)) (w * Complex.exp (w * u)) u := by
  have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 u := (hasDerivAt_id u).ofReal_comp
  have h2 : HasDerivAt (fun x : ℝ => w * (x : ℂ)) (w * 1) u := h1.const_mul w
  have h3 := h2.cexp
  convert h3 using 1
  ring

/-- `‖exp (w u)‖ = exp (Re w · u)` for real `u`. -/
lemma norm_exp_mul_ofReal (w : ℂ) (u : ℝ) :
    ‖Complex.exp (w * u)‖ = Real.exp (w.re * u) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- For `|u| ≤ a`, `‖exp (w u)‖ ≤ exp (a |Re w|)`. -/
lemma norm_exp_mul_ofReal_le {w : ℂ} {a u : ℝ} (hu : |u| ≤ a) :
    ‖Complex.exp (w * u)‖ ≤ Real.exp (a * |w.re|) := by
  rw [norm_exp_mul_ofReal]
  apply Real.exp_le_exp.mpr
  calc w.re * u ≤ |w.re * u| := le_abs_self _
    _ = |w.re| * |u| := abs_mul _ _
    _ ≤ |w.re| * a := mul_le_mul_of_nonneg_left hu (abs_nonneg _)
    _ = a * |w.re| := mul_comm _ _

/-- The generic trivial bound: for continuous `φ`,
`‖∫ u in -a..a, φ u e^{w u}‖ ≤ (∫ ‖φ‖) · exp (a |Re w|)`. -/
lemma norm_integral_mul_exp_le {a : ℝ} (ha : 0 ≤ a) {φ : ℝ → ℂ} (hφ : Continuous φ) (w : ℂ) :
    ‖∫ u in (-a)..a, φ u * Complex.exp (w * u)‖
      ≤ (∫ u in (-a)..a, ‖φ u‖) * Real.exp (a * |w.re|) := by
  have hab : -a ≤ a := by linarith
  calc ‖∫ u in (-a)..a, φ u * Complex.exp (w * u)‖
      ≤ ∫ u in (-a)..a, ‖φ u * Complex.exp (w * u)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ u in (-a)..a, ‖φ u‖ * Real.exp (a * |w.re|) := by
        apply intervalIntegral.integral_mono_on hab
        · exact (by fun_prop : Continuous fun u : ℝ =>
            ‖φ u * Complex.exp (w * u)‖).intervalIntegrable _ _
        · exact (by fun_prop : Continuous fun u : ℝ =>
            ‖φ u‖ * Real.exp (a * |w.re|)).intervalIntegrable _ _
        · intro u hu
          rw [norm_mul]
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          apply norm_exp_mul_ofReal_le
          exact abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
    _ = (∫ u in (-a)..a, ‖φ u‖) * Real.exp (a * |w.re|) := by
        rw [intervalIntegral.integral_mul_const]

/-! ## (2) The trivial bound -/

/-- **Trivial bound.** `‖Gt a g s‖ ≤ (∫ ‖g‖) · exp (a |Re s − ½|)`. -/
theorem Gt_bound {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) (s : ℂ) :
    ‖Gt a g s‖ ≤ (∫ u in (-a)..a, ‖g u‖) * Real.exp (a * |s.re - 1 / 2|) := by
  have hre : (s - 1 / 2).re = s.re - 1 / 2 := by simp
  have := norm_integral_mul_exp_le h.nonneg h.continuous (s - 1 / 2)
  rw [hre] at this
  exact this

/-! ## (1) Entirety of `Gt` -/

/-- Differentiation under the integral sign: `Gt a g` has derivative
`∫ u g(u) e^{(s−½)u}` at every `s`, for `g` continuous. -/
theorem hasDerivAt_Gt {a : ℝ} {g : ℝ → ℂ} (hg : Continuous g) (s₀ : ℂ) :
    HasDerivAt (Gt a g)
      (∫ u in (-a)..a, g u * ((u : ℂ) * Complex.exp ((s₀ - 1 / 2) * u))) s₀ := by
  set K : ℝ := |s₀.re - 1 / 2| + 1 with hK
  have hbc : Continuous fun u : ℝ => ‖g u‖ * (|u| * Real.exp (K * |u|)) :=
    hg.norm.mul (continuous_abs.mul (Real.continuous_exp.comp (continuous_const.mul continuous_abs)))
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := -a) (b := a)
    (F := fun (s : ℂ) (u : ℝ) => g u * Complex.exp ((s - 1 / 2) * u))
    (F' := fun (s : ℂ) (u : ℝ) => g u * ((u : ℂ) * Complex.exp ((s - 1 / 2) * u)))
    (x₀ := s₀) (s := Metric.ball s₀ 1)
    (bound := fun u : ℝ => ‖g u‖ * (|u| * Real.exp (K * |u|)))
    (Metric.ball_mem_nhds s₀ one_pos)
    (Eventually.of_forall fun s => Continuous.aestronglyMeasurable
      (show Continuous (fun u : ℝ => g u * Complex.exp ((s - 1 / 2) * u)) by fun_prop))
    ((show Continuous (fun u : ℝ => g u * Complex.exp ((s₀ - 1 / 2) * u)) by
      fun_prop).intervalIntegrable _ _)
    (Continuous.aestronglyMeasurable
      (show Continuous (fun u : ℝ => g u * ((u : ℂ) * Complex.exp ((s₀ - 1 / 2) * u))) by
        fun_prop))
    (Eventually.of_forall fun u _ s hs => ?_)
    (hbc.intervalIntegrable _ _)
    (Eventually.of_forall fun u _ s _ => ?_)
  · exact key.2
  · -- the dominating bound on the ball `‖s − s₀‖ < 1`
    simp only [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rw [norm_exp_mul_ofReal]
    apply Real.exp_le_exp.mpr
    have h1 : |s.re - s₀.re| ≤ 1 := by
      have := Complex.abs_re_le_norm (s - s₀)
      rw [Complex.sub_re] at this
      have hd : ‖s - s₀‖ < 1 := by
        rw [Metric.mem_ball, Complex.dist_eq] at hs
        exact hs
      linarith
    have h2 : (s - 1 / 2).re = s.re - 1 / 2 := by simp
    rw [h2]
    calc (s.re - 1 / 2) * u ≤ |s.re - 1 / 2| * |u| := by
          rw [← abs_mul]; exact le_abs_self _
      _ ≤ K * |u| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          rw [hK]
          calc |s.re - 1 / 2| = |(s₀.re - 1 / 2) + (s.re - s₀.re)| := by ring_nf
            _ ≤ |s₀.re - 1 / 2| + |s.re - s₀.re| := abs_add_le _ _
            _ ≤ |s₀.re - 1 / 2| + 1 := by linarith
  · -- the pointwise derivative in `s`
    have h1 : HasDerivAt (fun s : ℂ => (s - 1 / 2) * (u : ℂ)) (1 * (u : ℂ)) s :=
      ((hasDerivAt_id s).sub_const _).mul_const _
    have h2 := (h1.cexp).const_mul (g u)
    convert h2 using 1
    ring

/-- **`Gt a g` is entire** for `g` continuous. -/
theorem Gt_differentiable {a : ℝ} {g : ℝ → ℂ} (hg : Continuous g) :
    Differentiable ℂ (Gt a g) :=
  fun s => (hasDerivAt_Gt (a := a) hg s).differentiableAt

/-- `Gt a g` is continuous for `g` continuous. -/
theorem Gt_continuous {a : ℝ} {g : ℝ → ℂ} (hg : Continuous g) : Continuous (Gt a g) :=
  (Gt_differentiable hg).continuous

/-! ## (3) Decay in `Im s`: two integrations by parts -/

/-- **Two integrations by parts.** `(s − ½)² · Gt a g s = ∫ g''(u) e^{(s−½)u}`;
the boundary terms vanish because `g(±a) = g'(±a) = 0`. -/
theorem sq_mul_Gt_eq {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) (s : ℂ) :
    (s - 1 / 2) ^ 2 * Gt a g s
      = ∫ u in (-a)..a, deriv (deriv g) u * Complex.exp ((s - 1 / 2) * u) := by
  set w : ℂ := s - 1 / 2 with hw
  have hE : ∀ u : ℝ,
      HasDerivAt (fun x : ℝ => Complex.exp (w * x)) (w * Complex.exp (w * u)) u :=
    hasDerivAt_exp_mul_ofReal w
  have hE' : ∀ u : ℝ, HasDerivAt (fun x : ℝ => w * Complex.exp (w * x))
      (w * (w * Complex.exp (w * u))) u :=
    fun u => (hE u).const_mul w
  have hg1 : ∀ u : ℝ, HasDerivAt g (deriv g u) u := fun u => (h.differentiable u).hasDerivAt
  have hg2 : ∀ u : ℝ, HasDerivAt (deriv g) (deriv (deriv g) u) u :=
    fun u => (h.differentiable_deriv u).hasDerivAt
  -- first IBP: ∫ g · (w² E) = [g · wE] − ∫ g' · wE
  have ibp1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -a) (b := a)
    (u := g) (v := fun x : ℝ => w * Complex.exp (w * x))
    (u' := deriv g) (v' := fun x : ℝ => w * (w * Complex.exp (w * x)))
    (fun x _ => hg1 x) (fun x _ => hE' x)
    (h.continuous_deriv.intervalIntegrable _ _)
    ((show Continuous fun x : ℝ => w * (w * Complex.exp (w * x)) by
      fun_prop).intervalIntegrable _ _)
  -- second IBP: ∫ g' · wE = [g' · E] − ∫ g'' · E
  have ibp2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -a) (b := a)
    (u := deriv g) (v := fun x : ℝ => Complex.exp (w * x))
    (u' := deriv (deriv g)) (v' := fun x : ℝ => w * Complex.exp (w * x))
    (fun x _ => hg2 x) (fun x _ => hE x)
    (h.continuous_deriv2.intervalIntegrable _ _)
    ((show Continuous fun x : ℝ => w * Complex.exp (w * x) by fun_prop).intervalIntegrable _ _)
  simp only [h.left, h.right, h.deriv_left, h.deriv_right, zero_mul, sub_zero, zero_sub]
    at ibp1 ibp2
  have hG : ∫ u in (-a)..a, g u * (w * (w * Complex.exp (w * u))) = w ^ 2 * Gt a g s := by
    rw [Gt, ← intervalIntegral.integral_const_mul]
    congr 1
    funext u
    rw [← hw]
    ring
  rw [← hG, ibp1, ibp2, neg_neg]

/-- **Decay bound.** For `Im s ≠ 0`,
`‖Gt a g s‖ ≤ C₂ a g · exp (a |Re s − ½|) / (Im s)²`. -/
theorem Gt_decay {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) {s : ℂ} (hs : s.im ≠ 0) :
    ‖Gt a g s‖ ≤ C₂ a g * Real.exp (a * |s.re - 1 / 2|) / s.im ^ 2 := by
  have him0 : (s - 1 / 2).im = s.im := by simp
  have hw : (s - 1 / 2) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    intro h0
    apply hs
    rw [← him0, h0, Complex.zero_im]
  have heq : Gt a g s
      = (∫ u in (-a)..a, deriv (deriv g) u * Complex.exp ((s - 1 / 2) * u)) / (s - 1 / 2) ^ 2 := by
    rw [eq_div_iff hw, mul_comm]
    exact sq_mul_Gt_eq h s
  have hnum := norm_integral_mul_exp_le h.nonneg h.continuous_deriv2 (s - 1 / 2)
  have hre : (s - 1 / 2).re = s.re - 1 / 2 := by simp
  rw [hre] at hnum
  have him : s.im ^ 2 ≤ ‖(s - 1 / 2) ^ 2‖ := by
    rw [norm_pow]
    have h1 : |(s - 1 / 2).im| ≤ ‖s - 1 / 2‖ := Complex.abs_im_le_norm _
    rw [him0] at h1
    calc s.im ^ 2 = |s.im| ^ 2 := (_root_.sq_abs _).symm
      _ ≤ ‖s - 1 / 2‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hpos : 0 < s.im ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hs))
  rw [heq, norm_div]
  calc ‖∫ u in (-a)..a, deriv (deriv g) u * Complex.exp ((s - 1 / 2) * u)‖ / ‖(s - 1 / 2) ^ 2‖
      ≤ ‖∫ u in (-a)..a, deriv (deriv g) u * Complex.exp ((s - 1 / 2) * u)‖ / s.im ^ 2 :=
        div_le_div_of_nonneg_left (norm_nonneg _) hpos him
    _ ≤ C₂ a g * Real.exp (a * |s.re - 1 / 2|) / s.im ^ 2 :=
        div_le_div_of_nonneg_right hnum hpos.le

/-! ## (4) Value at a zero = `hfun` of its ordinate -/

/-- `Gt a g (½ + i t) = hfun a g t`. -/
theorem Gt_half_add_I_mul (a : ℝ) (g : ℝ → ℂ) (t : ℂ) :
    Gt a g (1 / 2 + I * t) = hfun a g t := by
  unfold Gt hfun
  congr 1
  funext u
  congr 2
  ring

/-- **Value at a zero.** `Gt a g ρ = hfun a g (ordinate ρ)`, since
`ρ − ½ = i · ordinate ρ`. -/
theorem Gt_at_ordinate (a : ℝ) (g : ℝ → ℂ) (ρ : ℂ) :
    Gt a g ρ = hfun a g (Reduction.ordinate ρ) := by
  have hρ : ∀ u : ℝ, (ρ - 1 / 2) * (u : ℂ) = I * (-I * (ρ - 1 / 2)) * u := fun u => by
    linear_combination ((ρ - 1 / 2) * (u : ℂ)) * Complex.I_sq
  unfold Gt hfun Reduction.ordinate
  congr 1
  funext u
  rw [hρ u]

/-! ## Relation to Mathlib's Fourier transform -/

/-- On the line `s = c + 2πiξ` of `ExplicitFormula`, for `g` supported in `[-a, a]`:
`Gt a g (line c ξ) = 𝓕 (u ↦ g u e^{(c−½)u}) (−ξ)` (Mathlib's `𝓕 f w = ∫ e^{−2πi v w} f v`). -/
theorem Gt_line_eq_fourier {a : ℝ} (ha : 0 ≤ a) {g : ℝ → ℂ}
    (hsupp : ∀ u, u ∉ Icc (-a) a → g u = 0) (c ξ : ℝ) :
    Gt a g (ExplicitFormula.line c ξ)
      = 𝓕 (fun u : ℝ => g u * Complex.exp (((c - 1 / 2 : ℝ) : ℂ) * u)) (-ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (-a) a) ?_]
  · rw [integral_Icc_eq_integral_Ioc, Gt, intervalIntegral.integral_of_le (by linarith)]
    congr 1
    funext u
    rw [smul_eq_mul, mul_comm (Complex.exp _), mul_assoc, ← Complex.exp_add]
    congr 2
    simp only [ExplicitFormula.line]
    push_cast
    ring
  · intro u hu
    simp [hsupp u hu]

/-- On the critical line, for `g` supported in `[-a, a]`:
`Gt a g (½ + 2πiξ) = 𝓕 g (−ξ)`. -/
theorem Gt_half_line_eq_fourier {a : ℝ} (ha : 0 ≤ a) {g : ℝ → ℂ}
    (hsupp : ∀ u, u ∉ Icc (-a) a → g u = 0) (ξ : ℝ) :
    Gt a g (1 / 2 + 2 * π * ξ * I) = 𝓕 g (-ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (-a) a) ?_]
  · rw [integral_Icc_eq_integral_Ioc, Gt, intervalIntegral.integral_of_le (by linarith)]
    congr 1
    funext u
    rw [smul_eq_mul, mul_comm (Complex.exp _)]
    congr 2
    push_cast
    ring
  · intro u hu
    simp [hsupp u hu]

/-! ## (5) Integrability on vertical lines -/

/-- Uniform majorant on a vertical line: `‖Gt a g (σ + i t)‖ ≤ M / (1 + t²)`. -/
theorem Gt_norm_le_div_one_add_sq {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) (σ : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, ‖Gt a g (σ + t * I)‖ ≤ M / (1 + t ^ 2) := by
  set B : ℝ := (∫ u in (-a)..a, ‖g u‖) * Real.exp (a * |σ - 1 / 2|) with hBdef
  set D : ℝ := C₂ a g * Real.exp (a * |σ - 1 / 2|) with hDdef
  have hB : 0 ≤ B :=
    mul_nonneg (intervalIntegral.integral_nonneg (by linarith [h.nonneg]) fun _ _ => norm_nonneg _)
      (Real.exp_pos _).le
  have hD : 0 ≤ D := mul_nonneg (C₂_nonneg h) (Real.exp_pos _).le
  refine ⟨2 * (B + D), by positivity, fun t => ?_⟩
  have hre : (σ + t * I).re = σ := by simp
  have him : (σ + t * I).im = t := by simp
  have h1 : ‖Gt a g (σ + t * I)‖ ≤ B := by
    have := Gt_bound h (σ + t * I)
    rwa [hre] at this
  have hpos : 0 < 1 + t ^ 2 := by positivity
  by_cases ht : t ^ 2 ≤ 1
  · rw [le_div_iff₀ hpos]
    nlinarith
  · push_neg at ht
    have ht0 : t ≠ 0 := by
      intro h0
      rw [h0] at ht
      norm_num at ht
    have h2 : ‖Gt a g (σ + t * I)‖ ≤ D / t ^ 2 := by
      have := Gt_decay h (s := σ + t * I) (by rw [him]; exact ht0)
      rwa [hre, him] at this
    refine h2.trans ?_
    rw [div_le_div_iff₀ (by positivity) hpos]
    nlinarith

/-- **Integrability on vertical lines.** `t ↦ Gt a g (σ + i t)` is integrable on `ℝ`. -/
theorem integrable_on_vertical_line {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) (σ : ℝ) :
    Integrable (fun t : ℝ => Gt a g (σ + t * I)) := by
  obtain ⟨M, _, hbound⟩ := Gt_norm_le_div_one_add_sq h σ
  have hcont : Continuous (fun t : ℝ => Gt a g (σ + t * I)) :=
    (Gt_continuous (a := a) h.continuous).comp (by fun_prop)
  refine (integrable_inv_one_add_sq.const_mul M).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [← div_eq_mul_inv]
  exact hbound t

/-! ## (6) Horizontal segments vanish -/

/-- **Horizontal vanishing.** If `‖F (σ + iT)‖ ≤ B (log T)²` for `T ≥ 4` and `σ ∈ [σ₁, σ₂]`
(this polylog bound is the explicit hypothesis), then
`∫ σ in σ₁..σ₂, F (σ + iT) · Gt a g (σ + iT) → 0` as `T → +∞`,
via the decay `‖Gt‖ ≤ C₂ e^{aM} / T²`, `M = max |σ₁ − ½| |σ₂ − ½|`. -/
theorem horizontal_vanishing {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) {σ₁ σ₂ : ℝ} (hσ : σ₁ ≤ σ₂)
    (F : ℂ → ℂ) (B : ℝ)
    (hF : ∀ T : ℝ, 4 ≤ T → ∀ σ ∈ Icc σ₁ σ₂, ‖F (σ + T * I)‖ ≤ B * (Real.log T) ^ 2) :
    Tendsto (fun T : ℝ => ∫ σ in σ₁..σ₂, F (σ + T * I) * Gt a g (σ + T * I)) atTop (𝓝 0) := by
  set M : ℝ := max |σ₁ - 1 / 2| |σ₂ - 1 / 2| with hM
  set K : ℝ := C₂ a g * Real.exp (a * M) with hKdef
  refine HorizontalDecay.horizontal_integral_tendsto_zero_filter
    (F := fun z => F z * Gt a g z) hσ atTop
    (fun T => B * K * (Real.log T / T) ^ 2) ?_ ?_
  · filter_upwards [eventually_ge_atTop 4] with T hT
    intro σ hσ'
    have hT0 : 0 < T := by linarith
    have hre : (σ + T * I).re = σ := by simp
    have him : (σ + T * I).im = T := by simp
    have h1 := hF T hT σ hσ'
    have hσM : |σ - 1 / 2| ≤ M := by
      rcases hσ' with ⟨hl, hr⟩
      rcases le_or_gt (1 / 2) σ with hh | hh
      · calc |σ - 1 / 2| = σ - 1 / 2 := abs_of_nonneg (by linarith)
          _ ≤ σ₂ - 1 / 2 := by linarith
          _ ≤ |σ₂ - 1 / 2| := le_abs_self _
          _ ≤ M := le_max_right _ _
      · calc |σ - 1 / 2| = -(σ - 1 / 2) := abs_of_neg (by linarith)
          _ ≤ -(σ₁ - 1 / 2) := by linarith
          _ ≤ |σ₁ - 1 / 2| := neg_le_abs _
          _ ≤ M := le_max_left _ _
    have h2 : ‖Gt a g (σ + T * I)‖ ≤ K / T ^ 2 := by
      have := Gt_decay h (s := σ + T * I) (by rw [him]; exact hT0.ne')
      rw [hre, him] at this
      refine this.trans ?_
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (C₂_nonneg h)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hσM h.nonneg
    have hBn : 0 ≤ B * Real.log T ^ 2 := (norm_nonneg _).trans h1
    calc ‖F (σ + T * I) * Gt a g (σ + T * I)‖
        = ‖F (σ + T * I)‖ * ‖Gt a g (σ + T * I)‖ := norm_mul _ _
      _ ≤ (B * Real.log T ^ 2) * (K / T ^ 2) := mul_le_mul h1 h2 (norm_nonneg _) hBn
      _ = B * K * (Real.log T / T) ^ 2 := by rw [div_pow]; ring
  · have h0 : Tendsto (fun T : ℝ => B * K * (Real.log T ^ 1 / (1 * T + 0)) ^ 2) atTop
        (𝓝 (B * K * 0 ^ 2)) :=
      ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).pow 2).const_mul (B * K)
    simp only [pow_one, one_mul, add_zero, zero_pow two_ne_zero, mul_zero] at h0
    exact h0

end TestFunctions

end
