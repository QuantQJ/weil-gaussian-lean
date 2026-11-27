import TestFunctions
import Mathlib

/-!
# Gaussian test functions

Gaussian test functions `gauss b α u = exp (−b u² − i α u)` with closed-form
Fourier–Laplace transforms, smooth cutoffs `gaussR R b α = cutoff R · gauss b α`
making them `IsTestFn R`, and *weighted* second-derivative bounds uniform in the
cutoff radius `R ≥ 2`.

**Cutoff convention.** `cutoff R u = bump (u / R)` where `bump : ContDiffBump (0 : ℝ)`
has `rIn = 1/2`, `rOut = 1`. Hence `cutoff R = 1` on `|u| ≤ R/2` (the plateau) and
`cutoff R = 0` on `|u| ≥ R`, for `R > 0`; derivatives scale by `1/R` and `1/R²`,
so they are bounded uniformly in `R ≥ 2`.

**Square root convention.** Mathlib has no `Complex.sqrt`; the prefactor `√(π/b)` is
written as `((Real.sqrt (π / b) : ℝ) : ℂ)` (equal to `(π/b)^(1/2 : ℂ)` since `π/b > 0`).

**Limits** are taken over `R : ℕ` with `atTop` (`hfun (R:ℝ) (gaussR R b α) t → gaussHat b α t`).

Standard Mathlib foundations only (see `AxiomAudit.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Complex Filter Topology Set
open scoped Real ContDiff

namespace GaussianTest

open TestFunctions

/-! ## Definitions -/

/-- The Gaussian `exp (−b u² − i α u)`. -/
def gauss (b α : ℝ) (u : ℝ) : ℂ :=
  Complex.exp (-(b : ℂ) * (u : ℂ) ^ 2 - I * (α : ℂ) * (u : ℂ))

/-- Its Fourier–Laplace transform `∫ gauss b α u · e^{i t u}`. -/
def gaussHat (b α : ℝ) (t : ℂ) : ℂ := ∫ u : ℝ, gauss b α u * Complex.exp (I * t * u)

/-- The full-line version of `Gt`: `∫ g u · e^{(s − ½) u}`. -/
def GtInf (g : ℝ → ℂ) (s : ℂ) : ℂ := ∫ u : ℝ, g u * Complex.exp ((s - 1 / 2) * u)

/-- A fixed smooth bump on `ℝ`: `1` on `[−1/2, 1/2]`, `0` outside `(−1, 1)`. -/
def bump : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The cutoff at radius `R`: `cutoff R u = bump (u / R)`. -/
def cutoff (R : ℝ) (u : ℝ) : ℝ := bump (u / R)

/-- The truncated Gaussian. -/
def gaussR (R b α : ℝ) (u : ℝ) : ℂ := (cutoff R u : ℂ) * gauss b α u

/-- `d/du` of the exponent of `gauss`: `−2 b u − i α`. -/
def gaussD (b α : ℝ) (u : ℝ) : ℂ := -2 * (b : ℂ) * (u : ℂ) - I * (α : ℂ)

/-! ## The bump and the cutoff -/

lemma bump_contDiff (n : ℕ∞) : ContDiff ℝ n (⇑bump) := bump.contDiff

lemma bump_differentiable : Differentiable ℝ (⇑bump) :=
  (bump_contDiff 1).differentiable (by simp)

lemma bump_deriv_contDiff : ContDiff ℝ ∞ (deriv (⇑bump)) :=
  (contDiff_infty_iff_deriv.mp (bump_contDiff ⊤)).2

lemma bump_deriv_differentiable : Differentiable ℝ (deriv (⇑bump)) :=
  (contDiff_infty_iff_deriv.mp bump_deriv_contDiff).1

lemma bump_deriv_continuous : Continuous (deriv (⇑bump)) := bump_deriv_contDiff.continuous

lemma bump_deriv2_continuous : Continuous (deriv (deriv (⇑bump))) :=
  (contDiff_infty_iff_deriv.mp bump_deriv_contDiff).2.continuous

lemma bump_hasCompactSupport : HasCompactSupport (⇑bump) := bump.hasCompactSupport

/-- The first two derivatives of the fixed bump are bounded. -/
lemma bump_deriv_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, |deriv (⇑bump) x| ≤ K ∧ |deriv (deriv (⇑bump)) x| ≤ K := by
  obtain ⟨C₁, h₁⟩ :=
    bump_deriv_continuous.bounded_above_of_compact_support bump_hasCompactSupport.deriv
  obtain ⟨C₂, h₂⟩ :=
    bump_deriv2_continuous.bounded_above_of_compact_support bump_hasCompactSupport.deriv.deriv
  refine ⟨max C₁ C₂, ?_, fun x => ⟨?_, ?_⟩⟩
  · exact le_trans (norm_nonneg _) ((h₁ 0).trans (le_max_left _ _))
  · rw [← Real.norm_eq_abs]; exact (h₁ x).trans (le_max_left _ _)
  · rw [← Real.norm_eq_abs]; exact (h₂ x).trans (le_max_right _ _)

lemma cutoff_nonneg (R u : ℝ) : 0 ≤ cutoff R u := bump.nonneg

lemma cutoff_le_one (R u : ℝ) : cutoff R u ≤ 1 := bump.le_one

lemma abs_cutoff_le_one (R u : ℝ) : |cutoff R u| ≤ 1 :=
  abs_le.mpr ⟨by linarith [cutoff_nonneg R u], cutoff_le_one R u⟩

/-- Plateau: `cutoff R = 1` on `|u| ≤ R/2`. -/
lemma cutoff_eq_one {R u : ℝ} (hR : 0 < R) (hu : |u| ≤ R / 2) : cutoff R u = 1 := by
  apply bump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_div, abs_of_pos hR]
  show |u| / R ≤ 1 / 2
  rw [div_le_iff₀ hR]; linarith

/-- Support: `cutoff R = 0` on `|u| ≥ R`. -/
lemma cutoff_eq_zero {R u : ℝ} (hR : 0 < R) (hu : R ≤ |u|) : cutoff R u = 0 := by
  apply bump.zero_of_le_dist
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hR]
  show (1 : ℝ) ≤ |u| / R
  rw [le_div_iff₀ hR]; linarith

lemma cutoff_contDiff (R : ℝ) (n : ℕ∞) : ContDiff ℝ n (cutoff R) :=
  (bump_contDiff n).comp (contDiff_id.div_const R)

lemma continuous_cutoff (R : ℝ) : Continuous (cutoff R) := (cutoff_contDiff R 0).continuous

lemma hasDerivAt_cutoff (R u : ℝ) :
    HasDerivAt (cutoff R) (deriv (⇑bump) (u / R) / R) u := by
  have h := (bump_differentiable (u / R)).hasDerivAt.comp u ((hasDerivAt_id' u).div_const R)
  exact h.congr_deriv (by ring)

lemma deriv_cutoff (R : ℝ) : deriv (cutoff R) = fun u => deriv (⇑bump) (u / R) / R :=
  funext fun u => (hasDerivAt_cutoff R u).deriv

lemma hasDerivAt_deriv_cutoff (R u : ℝ) :
    HasDerivAt (deriv (cutoff R)) (deriv (deriv (⇑bump)) (u / R) / R / R) u := by
  rw [deriv_cutoff]
  have h := ((bump_deriv_differentiable (u / R)).hasDerivAt.comp u
    ((hasDerivAt_id' u).div_const R)).div_const R
  exact h.congr_deriv (by ring)

lemma deriv2_cutoff (R : ℝ) :
    deriv (deriv (cutoff R)) = fun u => deriv (deriv (⇑bump)) (u / R) / R / R :=
  funext fun u => (hasDerivAt_deriv_cutoff R u).deriv

lemma continuous_deriv_cutoff (R : ℝ) : Continuous (deriv (cutoff R)) := by
  rw [deriv_cutoff]
  exact (bump_deriv_continuous.comp (continuous_id.div_const R)).div_const R

lemma continuous_deriv2_cutoff (R : ℝ) : Continuous (deriv (deriv (cutoff R))) := by
  rw [deriv2_cutoff]
  exact ((bump_deriv2_continuous.comp (continuous_id.div_const R)).div_const R).div_const R

/-- **Uniform derivative bounds** for the cutoff, `R ≥ 2`. -/
theorem cutoff_deriv_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 2 ≤ R → ∀ u : ℝ,
      |deriv (cutoff R) u| ≤ K ∧ |deriv (deriv (cutoff R)) u| ≤ K := by
  obtain ⟨K, hK0, hK⟩ := bump_deriv_bound
  refine ⟨K, hK0, fun R hR u => ?_⟩
  have hR0 : 0 < R := by linarith
  have hR1 : 1 ≤ R := by linarith
  rw [(hasDerivAt_cutoff R u).deriv, (hasDerivAt_deriv_cutoff R u).deriv]
  obtain ⟨h1, h2⟩ := hK (u / R)
  constructor
  · rw [abs_div, abs_of_pos hR0, div_le_iff₀ hR0]
    calc |deriv (⇑bump) (u / R)| ≤ K := h1
      _ ≤ K * R := le_mul_of_one_le_right hK0 hR1
  · rw [abs_div, abs_div, abs_of_pos hR0, div_le_iff₀ hR0, div_le_iff₀ hR0]
    calc |deriv (deriv (⇑bump)) (u / R)| ≤ K := h2
      _ ≤ K * R := le_mul_of_one_le_right hK0 hR1
      _ ≤ K * R * R := le_mul_of_one_le_right (by positivity) hR1

/-- The cutoff has a global minimum `0` at any `|u| ≥ R`, so its derivative vanishes there. -/
lemma deriv_cutoff_eq_zero {R u : ℝ} (hR : 0 < R) (hu : R ≤ |u|) : deriv (cutoff R) u = 0 := by
  apply IsLocalMin.deriv_eq_zero
  apply Filter.Eventually.of_forall
  intro x
  rw [cutoff_eq_zero hR hu]
  exact cutoff_nonneg R x

/-! ## The Gaussian and its derivatives -/

@[fun_prop]
lemma contDiff_ofReal (n : ℕ∞) : ContDiff ℝ n (fun x : ℝ => (x : ℂ)) :=
  Complex.ofRealCLM.contDiff

@[fun_prop]
lemma contDiff_cexp (n : ℕ∞) : ContDiff ℝ n Complex.exp := Complex.contDiff_exp

lemma gauss_contDiff (b α : ℝ) (n : ℕ∞) : ContDiff ℝ n (gauss b α) := by
  unfold gauss
  fun_prop

lemma continuous_gauss (b α : ℝ) : Continuous (gauss b α) := (gauss_contDiff b α 0).continuous

lemma continuous_gaussD (b α : ℝ) : Continuous (gaussD b α) := by
  unfold gaussD; fun_prop

lemma norm_gauss (b α u : ℝ) : ‖gauss b α u‖ = Real.exp (-b * u ^ 2) := by
  unfold gauss
  rw [Complex.norm_exp]
  congr 1
  simp [pow_two, Complex.mul_re, Complex.mul_im]

lemma hasDerivAt_ofReal (u : ℝ) : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 u :=
  (hasDerivAt_id u).ofReal_comp

lemma hasDerivAt_gauss (b α u : ℝ) :
    HasDerivAt (gauss b α) (gaussD b α u * gauss b α u) u := by
  have h1 := hasDerivAt_ofReal u
  have h2 := (((h1.mul h1).const_mul (-(b : ℂ))).sub (h1.const_mul (I * (α : ℂ)))).cexp
  unfold gauss gaussD
  convert h2 using 1
  · funext y
    simp only [Pi.sub_apply, Pi.mul_apply]
    ring_nf
  · simp only [Pi.sub_apply, Pi.mul_apply]
    ring_nf

lemma hasDerivAt_gaussD (b α u : ℝ) : HasDerivAt (gaussD b α) (-2 * (b : ℂ)) u := by
  have h := ((hasDerivAt_ofReal u).const_mul (-2 * (b : ℂ))).sub_const (I * (α : ℂ))
  unfold gaussD
  convert h using 1
  ring

lemma hasDerivAt_gauss' (b α u : ℝ) :
    HasDerivAt (fun x => gaussD b α x * gauss b α x)
      ((-2 * (b : ℂ) + gaussD b α u ^ 2) * gauss b α u) u := by
  have h := (hasDerivAt_gaussD b α u).mul (hasDerivAt_gauss b α u)
  convert h using 1
  ring

lemma norm_gaussD_le {b : ℝ} (hb : 0 < b) (α u : ℝ) : ‖gaussD b α u‖ ≤ 2 * b * |u| + |α| := by
  unfold gaussD
  calc ‖-2 * (b : ℂ) * (u : ℂ) - I * (α : ℂ)‖
      ≤ ‖-2 * (b : ℂ) * (u : ℂ)‖ + ‖I * (α : ℂ)‖ := norm_sub_le _ _
    _ = 2 * b * |u| + |α| := by
        simp [norm_mul, abs_of_pos hb]

/-! ## Derivatives of the truncated Gaussian -/

/-- First derivative of `gaussR`. -/
def gaussR1 (R b α : ℝ) (u : ℝ) : ℂ :=
  ((deriv (cutoff R) u : ℝ) : ℂ) * gauss b α u + (cutoff R u : ℂ) * (gaussD b α u * gauss b α u)

/-- Second derivative of `gaussR`. -/
def gaussR2 (R b α : ℝ) (u : ℝ) : ℂ :=
  ((deriv (deriv (cutoff R)) u : ℝ) : ℂ) * gauss b α u
    + 2 * ((deriv (cutoff R) u : ℝ) : ℂ) * (gaussD b α u * gauss b α u)
    + (cutoff R u : ℂ) * ((-2 * (b : ℂ) + gaussD b α u ^ 2) * gauss b α u)

lemma hasDerivAt_gaussR (R b α u : ℝ) : HasDerivAt (gaussR R b α) (gaussR1 R b α u) u := by
  have hc : HasDerivAt (cutoff R) (deriv (cutoff R) u) u :=
    (hasDerivAt_cutoff R u).differentiableAt.hasDerivAt
  unfold gaussR gaussR1
  exact hc.ofReal_comp.mul (hasDerivAt_gauss b α u)

lemma deriv_gaussR (R b α : ℝ) : deriv (gaussR R b α) = gaussR1 R b α :=
  funext fun u => (hasDerivAt_gaussR R b α u).deriv

lemma hasDerivAt_gaussR1 (R b α u : ℝ) : HasDerivAt (gaussR1 R b α) (gaussR2 R b α u) u := by
  have hc : HasDerivAt (cutoff R) (deriv (cutoff R) u) u :=
    (hasDerivAt_cutoff R u).differentiableAt.hasDerivAt
  have hc' : HasDerivAt (deriv (cutoff R)) (deriv (deriv (cutoff R)) u) u :=
    (hasDerivAt_deriv_cutoff R u).differentiableAt.hasDerivAt
  have h := (hc'.ofReal_comp.mul (hasDerivAt_gauss b α u)).add
    (hc.ofReal_comp.mul (hasDerivAt_gauss' b α u))
  unfold gaussR1 gaussR2
  convert h using 1
  ring

lemma deriv2_gaussR (R b α : ℝ) : deriv (deriv (gaussR R b α)) = gaussR2 R b α := by
  rw [deriv_gaussR]
  exact funext fun u => (hasDerivAt_gaussR1 R b α u).deriv

lemma gaussR_contDiff (R b α : ℝ) (n : ℕ∞) : ContDiff ℝ n (gaussR R b α) := by
  unfold gaussR
  have h1 := cutoff_contDiff R n
  have h2 := gauss_contDiff b α n
  fun_prop

lemma continuous_gaussR (R b α : ℝ) : Continuous (gaussR R b α) :=
  (gaussR_contDiff R b α 0).continuous

lemma continuous_gaussR2 (R b α : ℝ) : Continuous (gaussR2 R b α) := by
  unfold gaussR2
  have h1 := continuous_gauss b α
  have h2 := continuous_gaussD b α
  have h3 := continuous_cutoff R
  have h4 := continuous_deriv_cutoff R
  have h5 := continuous_deriv2_cutoff R
  fun_prop

/-! ## Test-function properties of `gaussR` -/

/-- `gaussR` vanishes outside `[−R, R]`. -/
theorem gaussR_support {R : ℝ} (hR : 2 ≤ R) (b α : ℝ) :
    ∀ u : ℝ, R < |u| → gaussR R b α u = 0 := by
  intro u hu
  rw [gaussR, cutoff_eq_zero (by linarith) hu.le]
  simp

/-- `gaussR = gauss` on the plateau `|u| ≤ R/2`. -/
theorem gaussR_eq_of_small {R : ℝ} (hR : 2 ≤ R) (b α : ℝ) :
    ∀ u : ℝ, |u| ≤ R / 2 → gaussR R b α u = gauss b α u := by
  intro u hu
  rw [gaussR, cutoff_eq_one (by linarith) hu]
  simp

/-- **`gaussR R b α` is a test function on `[−R, R]`** for `R ≥ 2`. -/
theorem gaussR_isTestFn {R : ℝ} (hR : 2 ≤ R) (b α : ℝ) : IsTestFn R (gaussR R b α) where
  nonneg := by linarith
  smooth := gaussR_contDiff R b α 2
  left := by
    rw [gaussR, cutoff_eq_zero (by linarith) (by rw [abs_neg, abs_of_pos (by linarith)])]
    simp
  right := by
    rw [gaussR, cutoff_eq_zero (by linarith) (by rw [abs_of_pos (by linarith)])]
    simp
  deriv_left := by
    have h : R ≤ |-R| := by rw [abs_neg, abs_of_pos (by linarith)]
    rw [deriv_gaussR, gaussR1, deriv_cutoff_eq_zero (by linarith) h,
      cutoff_eq_zero (by linarith) h]
    simp
  deriv_right := by
    have h : R ≤ |R| := by rw [abs_of_pos (by linarith)]
    rw [deriv_gaussR, gaussR1, deriv_cutoff_eq_zero (by linarith) h,
      cutoff_eq_zero (by linarith) h]
    simp

/-! ## Closed forms -/

lemma ofReal_sqrt_pi_div {b : ℝ} (hb : 0 < b) :
    ((Real.sqrt (π / b) : ℝ) : ℂ) = ((π : ℂ) / b) ^ (1 / 2 : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
  push_cast
  ring_nf

/-- **Closed form of the transform.** `gaussHat b α t = √(π/b) · exp (−(t − α)² / (4b))`. -/
theorem gaussHat_eq {b : ℝ} (hb : 0 < b) (α : ℝ) (t : ℂ) :
    gaussHat b α t = (Real.sqrt (π / b) : ℂ) * Complex.exp (-(t - α) ^ 2 / (4 * b)) := by
  have hb' : (-(b : ℂ)).re < 0 := by simp [hb]
  have h := integral_cexp_quadratic hb' (I * (t - α)) 0
  have heq : ∀ u : ℝ, gauss b α u * Complex.exp (I * t * u)
      = Complex.exp (-(b : ℂ) * u ^ 2 + (I * (t - α)) * u + 0) := by
    intro u
    unfold gauss
    rw [← Complex.exp_add]
    congr 1
    ring
  unfold gaussHat
  simp_rw [heq]
  rw [h, ofReal_sqrt_pi_div hb, neg_neg]
  congr 2
  simp only [zero_sub, mul_pow, I_sq, mul_neg, div_neg, neg_neg]
  ring

/-- `‖gaussHat b α t‖ = √(π/b) · exp ((Im t² − (Re t − α)²) / (4b))`. -/
theorem norm_gaussHat {b : ℝ} (hb : 0 < b) (α : ℝ) (t : ℂ) :
    ‖gaussHat b α t‖ = Real.sqrt (π / b) * Real.exp ((t.im ^ 2 - (t.re - α) ^ 2) / (4 * b)) := by
  rw [gaussHat_eq hb, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    _root_.abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_exp]
  congr 2
  rw [show (4 * (b : ℂ)) = ((4 * b : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_re]
  congr 1
  simp [pow_two, Complex.mul_re, Complex.mul_im]

/-- For real `x`, `gaussHat b α x` is real and positive: `√(π/b) · exp (−(x − α)² / (4b))`. -/
theorem gaussHat_real {b : ℝ} (hb : 0 < b) (α x : ℝ) :
    gaussHat b α x = ((Real.sqrt (π / b) * Real.exp (-(x - α) ^ 2 / (4 * b)) : ℝ) : ℂ) := by
  rw [gaussHat_eq hb]
  push_cast
  ring_nf

/-- **Closed form of the Laplace transform.**
`GtInf (gauss b α) s = √(π/b) · exp ((s − ½ − i α)² / (4b))`. -/
theorem GtInf_gauss {b : ℝ} (hb : 0 < b) (α : ℝ) (s : ℂ) :
    GtInf (gauss b α) s
      = (Real.sqrt (π / b) : ℂ) * Complex.exp ((s - 1 / 2 - I * α) ^ 2 / (4 * b)) := by
  have hb' : (-(b : ℂ)).re < 0 := by simp [hb]
  have h := integral_cexp_quadratic hb' (s - 1 / 2 - I * α) 0
  have heq : ∀ u : ℝ, gauss b α u * Complex.exp ((s - 1 / 2) * u)
      = Complex.exp (-(b : ℂ) * u ^ 2 + (s - 1 / 2 - I * α) * u + 0) := by
    intro u
    unfold gauss
    rw [← Complex.exp_add]
    congr 1
    ring
  unfold GtInf
  simp_rw [heq]
  rw [h, ofReal_sqrt_pi_div hb, neg_neg]
  congr 2
  rw [zero_sub, mul_neg, div_neg, neg_neg]

/-! ## Weighted decay bounds for general test functions -/

/-- **Weighted decay bound.** For `Im s ≠ 0`,
`‖Gt a g s‖ ≤ (∫ ‖g''(u)‖ e^{|Re s − ½| |u|} du) / (Im s)²`. -/
theorem Gt_bound_weighted {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) (s : ℂ) (hs : s.im ≠ 0) :
    ‖Gt a g s‖
      ≤ (∫ u in (-a)..a, ‖deriv (deriv g) u‖ * Real.exp (|s.re - 1 / 2| * |u|)) / s.im ^ 2 := by
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
  have hab : -a ≤ a := by linarith [h.nonneg]
  have hre : (s - 1 / 2).re = s.re - 1 / 2 := by simp
  have hnum : ‖∫ u in (-a)..a, deriv (deriv g) u * Complex.exp ((s - 1 / 2) * u)‖
      ≤ ∫ u in (-a)..a, ‖deriv (deriv g) u‖ * Real.exp (|s.re - 1 / 2| * |u|) := by
    refine (intervalIntegral.norm_integral_le_integral_norm hab).trans ?_
    apply intervalIntegral.integral_mono_on hab
    · exact ((h.continuous_deriv2.mul (by fun_prop)).norm).intervalIntegrable _ _
    · exact (h.continuous_deriv2.norm.mul (by fun_prop)).intervalIntegrable _ _
    · intro u _
      rw [norm_mul, norm_exp_mul_ofReal, hre]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Real.exp_le_exp.mpr
      calc (s.re - 1 / 2) * u ≤ |(s.re - 1 / 2) * u| := le_abs_self _
        _ = |s.re - 1 / 2| * |u| := abs_mul _ _
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
    _ ≤ _ := div_le_div_of_nonneg_right hnum hpos.le

/-- **Weighted decay bound for `hfun`.** For `Re t ≠ 0`,
`‖hfun a g t‖ ≤ (∫ ‖g''(u)‖ e^{|Im t| |u|} du) / (Re t)²`. -/
theorem hfun_bound_weighted {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) (t : ℂ) (ht : t.re ≠ 0) :
    ‖hfun a g t‖
      ≤ (∫ u in (-a)..a, ‖deriv (deriv g) u‖ * Real.exp (|t.im| * |u|)) / t.re ^ 2 := by
  rw [← Gt_half_add_I_mul]
  have h1 : (1 / 2 + I * t).im = t.re := by simp
  have h2 : (1 / 2 + I * t).re - 1 / 2 = -t.im := by simp
  have := Gt_bound_weighted h (1 / 2 + I * t) (by rw [h1]; exact ht)
  rwa [h1, h2, abs_neg] at this

/-! ## The Gaussian majorant -/

/-- **Gaussian beats exponential and polynomial.**
`(A₀ + A₁|u| + A₂u²) e^{−b u²} e^{c|u|} ≤ C e^{−(b/4) u²}`. -/
theorem majorant {b c : ℝ} (hb : 0 < b) (hc : 0 ≤ c) (A₀ A₁ A₂ : ℝ)
    (h0 : 0 ≤ A₀) (h1 : 0 ≤ A₁) (h2 : 0 ≤ A₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ,
      (A₀ + A₁ * |u| + A₂ * u ^ 2) * Real.exp (-b * u ^ 2) * Real.exp (c * |u|)
        ≤ C * Real.exp (-(b / 4) * u ^ 2) := by
  refine ⟨(A₀ + A₁ * (1 + 4 / b) + A₂ * (4 / b)) * Real.exp (c ^ 2 / (2 * b)),
    by positivity, fun u => ?_⟩
  set E : ℝ := Real.exp (b / 4 * u ^ 2) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hpoly : A₀ + A₁ * |u| + A₂ * u ^ 2 ≤ (A₀ + A₁ * (1 + 4 / b) + A₂ * (4 / b)) * E := by
    have e1 : b / 4 * u ^ 2 + 1 ≤ E := Real.add_one_le_exp _
    have e3 : (1 : ℝ) ≤ E := by rw [hE, Real.one_le_exp_iff]; positivity
    have hu : |u| ≤ 1 + u ^ 2 := by
      nlinarith [abs_nonneg u, _root_.sq_abs u, sq_nonneg (|u| - 1)]
    have e2 : u ^ 2 ≤ 4 / b * E := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hb]; nlinarith [sq_nonneg u]
    calc A₀ + A₁ * |u| + A₂ * u ^ 2 ≤ A₀ * 1 + A₁ * (1 + u ^ 2) + A₂ * u ^ 2 := by nlinarith
      _ ≤ A₀ * E + A₁ * (E + 4 / b * E) + A₂ * (4 / b * E) := by gcongr
      _ = (A₀ + A₁ * (1 + 4 / b) + A₂ * (4 / b)) * E := by ring
  have hexp : Real.exp (c * |u|) ≤ Real.exp (c ^ 2 / (2 * b)) * Real.exp (b / 2 * u ^ 2) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have hsq : 0 ≤ (b * |u| - c) ^ 2 := sq_nonneg _
    have : c ^ 2 / (2 * b) + b / 2 * u ^ 2 = (b ^ 2 * u ^ 2 + c ^ 2) / (2 * b) := by
      field_simp; ring
    rw [this, le_div_iff₀ (by positivity)]
    nlinarith [_root_.sq_abs u]
  have hcomb : E * Real.exp (-b * u ^ 2) * Real.exp (b / 2 * u ^ 2)
      = Real.exp (-(b / 4) * u ^ 2) := by
    rw [hE, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc (A₀ + A₁ * |u| + A₂ * u ^ 2) * Real.exp (-b * u ^ 2) * Real.exp (c * |u|)
      ≤ ((A₀ + A₁ * (1 + 4 / b) + A₂ * (4 / b)) * E) * Real.exp (-b * u ^ 2)
          * (Real.exp (c ^ 2 / (2 * b)) * Real.exp (b / 2 * u ^ 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le) hexp
          (Real.exp_pos _).le (by positivity)
    _ = (A₀ + A₁ * (1 + 4 / b) + A₂ * (4 / b)) * Real.exp (c ^ 2 / (2 * b))
          * (E * Real.exp (-b * u ^ 2) * Real.exp (b / 2 * u ^ 2)) := by ring
    _ = _ := by rw [hcomb]

lemma integrable_gaussian_quarter {b : ℝ} (hb : 0 < b) (C : ℝ) :
    Integrable (fun u : ℝ => C * Real.exp (-(b / 4) * u ^ 2)) :=
  (integrable_exp_neg_mul_sq (by positivity)).const_mul C

/-! ## Pointwise bounds on `gaussR` and its second derivative -/

lemma norm_gaussR_le (R b α u : ℝ) : ‖gaussR R b α u‖ ≤ Real.exp (-b * u ^ 2) := by
  rw [gaussR, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_gauss]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (abs_cutoff_le_one R u)

lemma norm_gaussR2_le {b : ℝ} (hb : 0 < b) (α : ℝ) {Kc : ℝ} (hKc0 : 0 ≤ Kc) {R : ℝ}
    (hK : ∀ u : ℝ, |deriv (cutoff R) u| ≤ Kc ∧ |deriv (deriv (cutoff R)) u| ≤ Kc) (u : ℝ) :
    ‖gaussR2 R b α u‖
      ≤ ((Kc + 2 * Kc * |α| + 2 * b + α ^ 2) + (4 * Kc * b + 4 * b * |α|) * |u|
          + 4 * b ^ 2 * u ^ 2) * Real.exp (-b * u ^ 2) := by
  obtain ⟨h1, h2⟩ := hK u
  have hg := norm_gauss b α u
  have hD := norm_gaussD_le hb α u
  set E : ℝ := Real.exp (-b * u ^ 2) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  set P : ℝ := 2 * b * |u| + |α| with hP
  have hP0 : 0 ≤ P := by positivity
  have hD2 : ‖-2 * (b : ℂ) + gaussD b α u ^ 2‖ ≤ 2 * b + P ^ 2 := by
    calc ‖-2 * (b : ℂ) + gaussD b α u ^ 2‖
        ≤ ‖-2 * (b : ℂ)‖ + ‖gaussD b α u ^ 2‖ := norm_add_le _ _
      _ = 2 * b + ‖gaussD b α u‖ ^ 2 := by
          rw [norm_pow]; simp [abs_of_pos hb]
      _ ≤ 2 * b + P ^ 2 := by gcongr
  have t1 : ‖((deriv (deriv (cutoff R)) u : ℝ) : ℂ) * gauss b α u‖ ≤ Kc * E := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hg]
    exact mul_le_mul_of_nonneg_right h2 hE0
  have t2 : ‖2 * ((deriv (cutoff R) u : ℝ) : ℂ) * (gaussD b α u * gauss b α u)‖ ≤ 2 * Kc * (P * E) := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hg, RCLike.norm_two]
    have := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 2)
    exact mul_le_mul this (mul_le_mul_of_nonneg_right hD hE0) (by positivity) (by positivity)
  have t3 : ‖(cutoff R u : ℂ) * ((-2 * (b : ℂ) + gaussD b α u ^ 2) * gauss b α u)‖
      ≤ 1 * ((2 * b + P ^ 2) * E) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, hg]
    exact mul_le_mul (abs_cutoff_le_one R u) (mul_le_mul_of_nonneg_right hD2 hE0)
      (by positivity) (by norm_num)
  calc ‖gaussR2 R b α u‖
      ≤ ‖((deriv (deriv (cutoff R)) u : ℝ) : ℂ) * gauss b α u‖
          + ‖2 * ((deriv (cutoff R) u : ℝ) : ℂ) * (gaussD b α u * gauss b α u)‖
          + ‖(cutoff R u : ℂ) * ((-2 * (b : ℂ) + gaussD b α u ^ 2) * gauss b α u)‖ :=
        norm_add₃_le
    _ ≤ Kc * E + 2 * Kc * (P * E) + 1 * ((2 * b + P ^ 2) * E) := add_le_add (add_le_add t1 t2) t3
    _ = _ := by
        rw [hP]
        linear_combination (4 * b ^ 2 * E) * _root_.sq_abs u + E * _root_.sq_abs α

/-! ## Uniform weighted integrals -/

/-- **Uniform weighted `L¹` bound on `gaussR''`.** The constant `K` does not depend on `R ≥ 2`. -/
theorem gaussR_weighted_uniform {b : ℝ} (hb : 0 < b) (α : ℝ) (c : ℝ) (hc : 0 ≤ c) :
    ∃ K : ℝ, ∀ R : ℝ, 2 ≤ R →
      ∫ u in (-R)..R, ‖deriv (deriv (gaussR R b α)) u‖ * Real.exp (c * |u|) ≤ K := by
  obtain ⟨Kc, hKc0, hKc⟩ := cutoff_deriv_bound
  obtain ⟨C, hC0, hC⟩ := majorant hb hc (Kc + 2 * Kc * |α| + 2 * b + α ^ 2)
    (4 * Kc * b + 4 * b * |α|) (4 * b ^ 2) (by positivity) (by positivity) (by positivity)
  have hint := integrable_gaussian_quarter hb C
  refine ⟨∫ u : ℝ, C * Real.exp (-(b / 4) * u ^ 2), fun R hR => ?_⟩
  have hR0 : -R ≤ R := by linarith
  have hpt : ∀ u : ℝ, ‖deriv (deriv (gaussR R b α)) u‖ * Real.exp (c * |u|)
      ≤ C * Real.exp (-(b / 4) * u ^ 2) := by
    intro u
    refine le_trans ?_ (hC u)
    rw [deriv2_gaussR]
    exact mul_le_mul_of_nonneg_right (norm_gaussR2_le hb α hKc0 (hKc R hR) u) (Real.exp_pos _).le
  have hcont : Continuous fun u : ℝ => ‖deriv (deriv (gaussR R b α)) u‖ * Real.exp (c * |u|) := by
    rw [deriv2_gaussR]
    exact (continuous_gaussR2 R b α).norm.mul (by fun_prop)
  calc ∫ u in (-R)..R, ‖deriv (deriv (gaussR R b α)) u‖ * Real.exp (c * |u|)
      ≤ ∫ u in (-R)..R, C * Real.exp (-(b / 4) * u ^ 2) :=
        intervalIntegral.integral_mono_on hR0 (hcont.intervalIntegrable _ _)
          hint.intervalIntegrable (fun u _ => hpt u)
    _ = ∫ u in Ioc (-R) R, C * Real.exp (-(b / 4) * u ^ 2) := intervalIntegral.integral_of_le hR0
    _ ≤ ∫ u : ℝ, C * Real.exp (-(b / 4) * u ^ 2) :=
        setIntegral_le_integral hint (Eventually.of_forall fun u => by positivity)

/-- **Uniform weighted `L¹` bound on `gaussR`** (zeroth order). -/
theorem gaussR_sup_uniform {b : ℝ} (hb : 0 < b) (α : ℝ) (c : ℝ) (hc : 0 ≤ c) :
    ∃ K : ℝ, ∀ R : ℝ, 2 ≤ R →
      ∫ u in (-R)..R, ‖gaussR R b α u‖ * Real.exp (c * |u|) ≤ K := by
  obtain ⟨C, hC0, hC⟩ := majorant hb hc 1 0 0 zero_le_one le_rfl le_rfl
  have hint := integrable_gaussian_quarter hb C
  refine ⟨∫ u : ℝ, C * Real.exp (-(b / 4) * u ^ 2), fun R hR => ?_⟩
  have hR0 : -R ≤ R := by linarith
  have hpt : ∀ u : ℝ, ‖gaussR R b α u‖ * Real.exp (c * |u|)
      ≤ C * Real.exp (-(b / 4) * u ^ 2) := by
    intro u
    refine le_trans ?_ (hC u)
    have := mul_le_mul_of_nonneg_right (norm_gaussR_le R b α u) (Real.exp_pos (c * |u|)).le
    refine this.trans (le_of_eq ?_)
    ring
  have hcont : Continuous fun u : ℝ => ‖gaussR R b α u‖ * Real.exp (c * |u|) :=
    (continuous_gaussR R b α).norm.mul (by fun_prop)
  calc ∫ u in (-R)..R, ‖gaussR R b α u‖ * Real.exp (c * |u|)
      ≤ ∫ u in (-R)..R, C * Real.exp (-(b / 4) * u ^ 2) :=
        intervalIntegral.integral_mono_on hR0 (hcont.intervalIntegrable _ _)
          hint.intervalIntegrable (fun u _ => hpt u)
    _ = ∫ u in Ioc (-R) R, C * Real.exp (-(b / 4) * u ^ 2) := intervalIntegral.integral_of_le hR0
    _ ≤ ∫ u : ℝ, C * Real.exp (-(b / 4) * u ^ 2) :=
        setIntegral_le_integral hint (Eventually.of_forall fun u => by positivity)

/-! ## Convergence as the cutoff radius `R → ∞` (over `R : ℕ`) -/

/-- Generic dominated-convergence statement: for any `w : ℂ`,
`∫_{-R}^{R} gaussR R b α u · e^{w u} → ∫_ℝ gauss b α u · e^{w u}` as `R → ∞` in `ℕ`. -/
theorem tendsto_gaussR_integral {b : ℝ} (hb : 0 < b) (α : ℝ) (w : ℂ) :
    Tendsto (fun R : ℕ => ∫ u in (-(R : ℝ))..R, gaussR R b α u * Complex.exp (w * u)) atTop
      (𝓝 (∫ u : ℝ, gauss b α u * Complex.exp (w * u))) := by
  obtain ⟨C, hC0, hC⟩ := majorant hb (abs_nonneg w.re) 1 0 0 zero_le_one le_rfl le_rfl
  have hint := integrable_gaussian_quarter hb C
  have hdom := tendsto_integral_of_dominated_convergence (μ := volume)
    (F := fun (n : ℕ) (u : ℝ) => gaussR n b α u * Complex.exp (w * u))
    (f := fun u : ℝ => gauss b α u * Complex.exp (w * u))
    (fun u : ℝ => C * Real.exp (-(b / 4) * u ^ 2))
    (fun n => ((continuous_gaussR n b α).mul (by fun_prop)).aestronglyMeasurable)
    hint
    (fun n => Eventually.of_forall fun u => ?_)
    (Eventually.of_forall fun u => ?_)
  · refine hdom.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro u hu
    have hu' : (n : ℝ) < |u| := by
      rw [mem_Icc, not_and_or] at hu
      rcases hu with h | h
      · push_neg at h
        rw [abs_of_neg (by linarith)]; linarith
      · push_neg at h
        rw [abs_of_pos (by linarith)]; exact h
    rw [gaussR_support hn' b α u hu', zero_mul]
  · -- the domination
    rw [norm_mul, norm_exp_mul_ofReal]
    calc ‖gaussR n b α u‖ * Real.exp (w.re * u)
        ≤ Real.exp (-b * u ^ 2) * Real.exp (|w.re| * |u|) := by
          apply mul_le_mul (norm_gaussR_le n b α u) _ (Real.exp_pos _).le (Real.exp_pos _).le
          apply Real.exp_le_exp.mpr
          calc w.re * u ≤ |w.re * u| := le_abs_self _
            _ = |w.re| * |u| := abs_mul _ _
      _ = (1 + 0 * |u| + 0 * u ^ 2) * Real.exp (-b * u ^ 2) * Real.exp (|w.re| * |u|) := by ring
      _ ≤ C * Real.exp (-(b / 4) * u ^ 2) := hC u
  · -- the pointwise limit
    apply tendsto_const_nhds.congr'
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_ge_atTop (2 * |u| + 2))] with n hn
    have h2 : (2 : ℝ) ≤ n := by linarith [abs_nonneg u]
    rw [gaussR_eq_of_small h2 b α u (by linarith)]

/-- **`hfun R (gaussR R b α) t → gaussHat b α t`** as `R → ∞` in `ℕ`. -/
theorem tendsto_gaussR_hfun {b : ℝ} (hb : 0 < b) (α : ℝ) (t : ℂ) :
    Tendsto (fun R : ℕ => hfun R (gaussR R b α) t) atTop (𝓝 (gaussHat b α t)) := by
  unfold hfun gaussHat
  exact tendsto_gaussR_integral hb α (I * t)

/-- **`Gt R (gaussR R b α) s → GtInf (gauss b α) s`** as `R → ∞` in `ℕ`. -/
theorem tendsto_gaussR_Gt {b : ℝ} (hb : 0 < b) (α : ℝ) (s : ℂ) :
    Tendsto (fun R : ℕ => Gt R (gaussR R b α) s) atTop (𝓝 (GtInf (gauss b α) s)) := by
  unfold Gt GtInf
  exact tendsto_gaussR_integral hb α (s - 1 / 2)

end GaussianTest

end
