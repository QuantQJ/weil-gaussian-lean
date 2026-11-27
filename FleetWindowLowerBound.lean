import FleetHeadContourConverse
import Kerr.Zeta.Conjugation
import Mathlib

/-!
# A positive lower bound for the window; no negative window rate

`headWindow b α = ∫ ‖M_N(1/2+it)‖² e^{-(t−α)²/(4b)} dt`, `N = cut b = ⌊e^{1.1/b}⌋` (`FleetHeadContourConverse`).

* `headWindow_lower` : there is `b₀ > 0` with `headWindow b 1 + headWindow b (−1) ≥ 2π√b / Z1` for all
  `0 < b ≤ b₀`, `Z1 = 300√(4π) + 800√(8π)`; with `headWindow_neg` (the window is even in `α`),
  `headWindow_one_lower` : `headWindow b 1 ≥ π√b / Z1`. No hypothesis.
* `not_windowRate_of_neg` : `¬ WindowRate c` for every `c < 0`; `windowRate_nonneg`;
  `zeroDev_sq_half_le_of_windowRate` / `not_windowRate_of_lt'` : `WindowRate c ⇒ D²/2 ≤ c` with no side
  condition; `sInf_windowRate_eq` : the infimum over all real admissible rates is `windowRateInf`.

Method. Pair `M_N` with `ζ` instead of `ζ'`. With `Φ = LGw · M_N` (`FleetHeadContourGauss`):
1. On `Re w = 3/2`, `M_N(w) ζ(w) = Σ_{m ≤ N} μ(m) Σ_n (mn)^{-w}` and the Mellin inversion of the kernel give
   `(1/2π) ∫ Φ ζ = Ssum = Σ_{m ≤ N} μ(m) Σ_n kernel(mn)` (`Ssum_eq_line_integral`).
2. `Φ ζ` has a simple pole at `1` with residue `Φ(1)`; the rectangle/line shift (`line_shiftZ`) gives
   `∫_{Re=1/2} Φ ζ = 2π (Ssum − Φ(1))`.
3. Regrouping by `k = mn`: `Ssum = Σ_k (Σ_{m ≤ N, m | k} μ(m)) kernel(k)`; the coefficient is `[k = 1]` for
   `k ≤ N` (Möbius inversion), `kernel(1) = 2`, and for `k > N` (so `log k > 1.1/b`) the coefficient is
   `≤ d(k) ≤ 2√k` and `|kernel(k)| ≤ 2k^{-8/5}`: `|Ssum − 2| ≤ Σ_{k > N} 4k^{-11/10} → 0` (`abs_Ssum_sub_two_le`).
   At `α = 1`, `‖Φ(1)‖ ≤ 2√(π/b) e^{-3/(16b)}(1 + 1.1/b) → 0`.
4. Cauchy–Schwarz in each Gaussian weight (`cs_window`) and `∫ ‖ζ(1/2+it)‖² e^{-(t∓1)²/4b} ≤ Z1 √b`
   (`zeta_half_window`) turn `2π ≤ 2π‖Ssum − Φ(1)‖` into the lower bound.

The zero exhibited in `FleetFirstZero` is not used: the lower bound comes from the `k = 1` term of the
mollifier identity `M_N ζ = 1 + Σ_{k > N} (…) k^{-w}`, which holds whether or not `ζ` has zeros.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set MeasureTheory intervalIntegral
open scoped Real ComplexConjugate

namespace FleetWindowLowerBound
open FleetHeadContour RectangleWinding

/-! ## Shifting `∫ Φ ζ` from `Re w = 3/2` to the critical line -/

/-- The entire part of `Φ ζ`. -/
def KZ (Φ : ℂ → ℂ) (s : ℂ) : ℂ := Φ s * zetaReg s + dslope Φ 1 s

lemma differentiable_KZ {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) : Differentiable ℂ (KZ Φ) := by
  have hd : Differentiable ℂ (dslope Φ 1) := by
    rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]
    exact hΦ.differentiableOn
  exact (hΦ.mul differentiable_zetaReg).add hd

lemma decompZ {Φ : ℂ → ℂ} {s : ℂ} (hs : s ≠ 1) :
    Φ s * riemannZeta s = KZ Φ s + Φ 1 * (s - 1)⁻¹ := by
  rw [riemannZeta_eq_zetaReg hs]
  unfold KZ
  rw [dslope_of_ne _ hs, slope_def_field]
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field_simp
  ring

/-- `∮ Φ ζ = 2πi Φ(1)` around `1`. -/
theorem rect_shiftZ {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) {x₁ x₂ y₁ y₂ : ℝ}
    (hx₁ : x₁ < 1) (hx₂ : 1 < x₂) (hy₁ : y₁ < 0) (hy₂ : 0 < y₂) :
    rectInt (fun s => Φ s * riemannZeta s) x₁ x₂ y₁ y₂ = 2 * π * I * Φ 1 := by
  have hx₁' := hx₁.ne; have hx₂' := hx₂.ne'; have hy₁' := hy₁.ne; have hy₂' := hy₂.ne'
  rw [rectInt_congr (fun s hs => decompZ (Φ := Φ) hs) hx₁' hx₂' hy₁' hy₂']
  have hK := differentiable_KZ hΦ
  have cK := edgeCont_of_continuous hK.continuous x₁ x₂ y₁ y₂
  have c1 : EdgeCont (fun s => Φ 1 * (s - 1)⁻¹) x₁ x₂ y₁ y₂ :=
    edgeCont_of_continuousOn (continuousOn_const.mul continuousOn_inv_sub) hx₁' hx₂' hy₁' hy₂'
  rw [rectInt_add cK c1, rectInt_const_mul, rectInt_eq_zero_of_differentiable hK,
    rect_winding 1 x₁ x₂ y₁ y₂ (by simpa using hx₁) (by simpa using hx₂) (by simpa using hy₁)
      (by simpa using hy₂)]
  ring

/-- **Line shift for `Φ ζ`.** -/
theorem line_shiftZ {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    (h3 : Integrable (fun y : ℝ => Φ (((3 / 2 : ℝ) : ℂ) + y * I) * riemannZeta (((3 / 2 : ℝ) : ℂ) + y * I)))
    (h1 : Integrable (fun y : ℝ => Φ (((1 / 2 : ℝ) : ℂ) + y * I) * riemannZeta (((1 / 2 : ℝ) : ℂ) + y * I)))
    (htop : Tendsto (fun T : ℝ => ∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ),
      Φ ((x : ℂ) + T * I) * riemannZeta ((x : ℂ) + T * I)) atTop (𝓝 0))
    (hbot : Tendsto (fun T : ℝ => ∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ),
      Φ ((x : ℂ) + ((-T : ℝ) : ℂ) * I) * riemannZeta ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) atTop (𝓝 0)) :
    (∫ y : ℝ, Φ (((3 / 2 : ℝ) : ℂ) + y * I) * riemannZeta (((3 / 2 : ℝ) : ℂ) + y * I))
      - (∫ y : ℝ, Φ (((1 / 2 : ℝ) : ℂ) + y * I) * riemannZeta (((1 / 2 : ℝ) : ℂ) + y * I))
      = 2 * π * Φ 1 := by
  set f : ℂ → ℂ := fun s => Φ s * riemannZeta s with hf
  have hV3 := intervalIntegral_tendsto_integral h3 tendsto_neg_atTop_atBot tendsto_id
  have hV1 := intervalIntegral_tendsto_integral h1 tendsto_neg_atTop_atBot tendsto_id
  have hlim : Tendsto (fun T : ℝ => rectInt f (1 / 2) (3 / 2) (-T) T) atTop
      (𝓝 (0 - 0 + I * (∫ y : ℝ, f (((3 / 2 : ℝ) : ℂ) + y * I))
        - I * (∫ y : ℝ, f (((1 / 2 : ℝ) : ℂ) + y * I)))) := by
    unfold rectInt
    exact ((hbot.sub htop).add (hV3.const_mul I)).sub (hV1.const_mul I)
  have hconst : ∀ᶠ T : ℝ in atTop, rectInt f (1 / 2) (3 / 2) (-T) T = 2 * π * I * Φ 1 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact rect_shiftZ hΦ (by norm_num) (by norm_num) (by linarith) hT
  have heq := tendsto_nhds_unique (hlim.congr' hconst) tendsto_const_nhds
  have hI : I ≠ 0 := I_ne_zero
  have : I * ((∫ y : ℝ, f (((3 / 2 : ℝ) : ℂ) + y * I)) - (∫ y : ℝ, f (((1 / 2 : ℝ) : ℂ) + y * I)))
      = I * (2 * π * Φ 1) := by
    rw [mul_sub]; linear_combination heq
  exact mul_left_cancel₀ hI this


/-! ## Bounds on the strip `1/2 ≤ Re ≤ 3/2` -/

lemma norm_zeta_strip_le {x y : ℝ} (hx1 : 1 / 2 ≤ x) (hx2 : x ≤ 3 / 2)
    (hs : 1 / 2 ≤ ‖(x : ℂ) + y * I - 1‖) : ‖riemannZeta ((x : ℂ) + y * I)‖ ≤ 10 + 5 * |y| := by
  have hne : (x : ℂ) + y * I ≠ 1 := by
    intro h; rw [h, sub_self, norm_zero] at hs; norm_num at hs
  rw [riemannZeta_eq_zetaReg hne]
  have hre : ((x : ℂ) + y * I).re = x := by simp
  have h1 := norm_zetaReg_le (s := (x : ℂ) + y * I) (by rw [hre]; linarith)
  have hsn : ‖(x : ℂ) + y * I‖ ≤ 3 / 2 + |y| := by
    calc ‖(x : ℂ) + y * I‖ ≤ ‖(x : ℂ)‖ + ‖(y : ℂ) * I‖ := norm_add_le _ _
      _ = |x| + |y| := by simp
      _ ≤ 3 / 2 + |y| := by rw [abs_of_pos (by linarith)]; linarith
  have h2 : ‖((x : ℂ) + y * I - 1)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    calc ‖(x : ℂ) + y * I - 1‖⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hs
      _ = 2 := by norm_num
  calc ‖zetaReg ((x : ℂ) + y * I) + ((x : ℂ) + y * I - 1)⁻¹‖
      ≤ ‖zetaReg ((x : ℂ) + y * I)‖ + ‖((x : ℂ) + y * I - 1)⁻¹‖ := norm_add_le _ _
    _ ≤ 5 * (3 / 2 + |y|) + 2 := by nlinarith
    _ ≤ 10 + 5 * |y| := by linarith

lemma norm_fZ_strip_le {b : ℝ} (hb : 0 < b) (α : ℝ) (M : ℕ) {x y : ℝ} (hx1 : 1 / 2 ≤ x) (hx2 : x ≤ 3 / 2)
    (hs : 1 / 2 ≤ ‖(x : ℂ) + y * I - 1‖) :
    ‖Phi b α M ((x : ℂ) + y * I) * riemannZeta ((x : ℂ) + y * I)‖
      ≤ Real.sqrt (π / b) * Real.exp (1 / (4 * b)) * (M + 1) * (10 + 5 * |y|) *
        (Real.exp (-(y + α) ^ 2 / (4 * b)) + Real.exp (-(y - α) ^ 2 / (4 * b))) := by
  have hre : ((x : ℂ) + y * I).re = x := by simp
  have hL := norm_LGw_le b α x y
  have hM := norm_Mpoly_le M (w := (x : ℂ) + y * I) (by rw [hre]; linarith)
  have hZ := norm_zeta_strip_le hx1 hx2 hs
  have hE : Real.exp ((x - 1 / 2) ^ 2 / (4 * b)) ≤ Real.exp (1 / (4 * b)) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have hG : 0 ≤ Real.exp (-(y + α) ^ 2 / (4 * b)) + Real.exp (-(y - α) ^ 2 / (4 * b)) := by positivity
  unfold Phi
  rw [norm_mul, norm_mul]
  calc ‖LGw b α ((x : ℂ) + y * I)‖ * ‖Mpoly M ((x : ℂ) + y * I)‖ * ‖riemannZeta ((x : ℂ) + y * I)‖
      ≤ (Real.sqrt (π / b) * Real.exp (1 / (4 * b)) *
          (Real.exp (-(y + α) ^ 2 / (4 * b)) + Real.exp (-(y - α) ^ 2 / (4 * b)))) * (M + 1)
        * (10 + 5 * |y|) := by
        gcongr
        calc ‖LGw b α ((x : ℂ) + y * I)‖ ≤ _ := hL
          _ ≤ _ := by gcongr
    _ = _ := by ring

lemma half_le_norm_line {x : ℝ} (hx : |x - 1| = 1 / 2) (y : ℝ) : 1 / 2 ≤ ‖(x : ℂ) + y * I - 1‖ := by
  have := Complex.abs_re_le_norm ((x : ℂ) + y * I - 1)
  simp at this; linarith

lemma integrable_fZ_line {b : ℝ} (hb : 0 < b) (α : ℝ) (M : ℕ) {x : ℝ} (hx1 : 1 / 2 ≤ x) (hx2 : x ≤ 3 / 2)
    (hx : |x - 1| = 1 / 2) :
    Integrable (fun y : ℝ => Phi b α M ((x : ℂ) + y * I) * riemannZeta ((x : ℂ) + y * I)) := by
  have hx1' : x ≠ 1 := by intro h; rw [h] at hx; norm_num at hx
  set C := Real.sqrt (π / b) * Real.exp (1 / (4 * b)) * (M + 1) with hC
  refine integrable_of_gauss_bound hb α (C * 10) (C * 5) ?_ (fun y => ?_)
  · refine ((differentiable_Phi b α M).continuous.comp (continuous_line x)).mul ?_
    exact continuous_iff_continuousAt.mpr fun y =>
      (differentiableAt_riemannZeta (line_ne_one hx1' y)).continuousAt.comp (x := y)
        (continuous_line x).continuousAt
  · have := norm_fZ_strip_le hb α M hx1 hx2 (half_le_norm_line hx y)
    calc _ ≤ _ := this
      _ = _ := by rw [hC]; ring

lemma tendsto_horizontalZ {b : ℝ} (hb : 0 < b) (α : ℝ) (M : ℕ) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    Tendsto (fun T : ℝ => ∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ),
      Phi b α M ((x : ℂ) + ((σ * T : ℝ) : ℂ) * I)
        * riemannZeta ((x : ℂ) + ((σ * T : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
  set C := Real.sqrt (π / b) * Real.exp (1 / (4 * b)) * (M + 1) with hC
  have hmaj : Tendsto (fun T : ℝ => C * ((10 + 5 * T) * Real.exp (-(T - (-α)) ^ 2 / (4 * b))
      + (10 + 5 * T) * Real.exp (-(T - α) ^ 2 / (4 * b)))) atTop (𝓝 0) := by
    have := ((tendsto_lin_gauss hb (-α) 10 5).add (tendsto_lin_gauss hb α 10 5)).const_mul C
    simpa using this
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hmaj
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hσT : |σ * T| = T := by
    rcases hσ with rfl | rfl <;> simp [abs_of_pos (by linarith : (0 : ℝ) < T)]
  have hb' := intervalIntegral.norm_integral_le_of_norm_le_const (a := (1 / 2 : ℝ)) (b := 3 / 2)
    (C := C * (10 + 5 * T) * (Real.exp (-((σ * T) + α) ^ 2 / (4 * b))
      + Real.exp (-((σ * T) - α) ^ 2 / (4 * b))))
    (f := fun x : ℝ => Phi b α M ((x : ℂ) + ((σ * T : ℝ) : ℂ) * I)
        * riemannZeta ((x : ℂ) + ((σ * T : ℝ) : ℂ) * I))
    (fun x hx => by
      have hx' := Set.uIoc_subset_uIcc hx
      rw [Set.uIcc_of_le (by norm_num)] at hx'
      have hn : 1 / 2 ≤ ‖(x : ℂ) + ((σ * T : ℝ) : ℂ) * I - 1‖ := by
        have := Complex.abs_im_le_norm ((x : ℂ) + ((σ * T : ℝ) : ℂ) * I - 1)
        have him : ((x : ℂ) + ((σ * T : ℝ) : ℂ) * I - 1).im = σ * T := by simp
        rw [him, hσT] at this; linarith
      have := norm_fZ_strip_le hb α M (x := x) (y := σ * T) hx'.1 hx'.2 hn
      rw [hσT] at this
      simpa [hC, mul_assoc] using this)
  refine hb'.trans (le_of_eq ?_)
  have hsym : Real.exp (-((σ * T) + α) ^ 2 / (4 * b)) + Real.exp (-((σ * T) - α) ^ 2 / (4 * b))
      = Real.exp (-(T - (-α)) ^ 2 / (4 * b)) + Real.exp (-(T - α) ^ 2 / (4 * b)) := by
    rcases hσ with rfl | rfl
    · ring_nf
    · ring_nf
  rw [hsym]
  norm_num
  ring

/-- **Critical-line form**: `∫ Φ(3/2+it) ζ(3/2+it) dt = 2π Φ(1) + ∫ Φ(1/2+it) ζ(1/2+it) dt`. -/
theorem pairing_shift {b : ℝ} (hb : 0 < b) (α : ℝ) (M : ℕ) :
    (∫ y : ℝ, Phi b α M (((3 / 2 : ℝ) : ℂ) + y * I) * riemannZeta (((3 / 2 : ℝ) : ℂ) + y * I))
      - (∫ y : ℝ, Phi b α M (((1 / 2 : ℝ) : ℂ) + y * I) * riemannZeta (((1 / 2 : ℝ) : ℂ) + y * I))
      = 2 * π * Phi b α M 1 :=
  line_shiftZ (differentiable_Phi b α M)
    (integrable_fZ_line hb α M (by norm_num) (by norm_num) (by norm_num))
    (integrable_fZ_line hb α M (by norm_num) (by norm_num) (by norm_num [abs_of_neg]))
    (by simpa using tendsto_horizontalZ hb α M 1 (Or.inl rfl))
    (by simpa using tendsto_horizontalZ hb α M (-1) (Or.inr rfl))


/-! ## The line `Re w = 3/2`: the Dirichlet-series side -/

/-- `Σ_{n ≥ 1} kernel b α (m n)`. -/
def innerZ (b α : ℝ) (m : ℕ) : ℝ := ∑' n : ℕ, FleetMollifierTail.kernel b α ((m : ℝ) * ((n : ℝ) + 1))

/-- The finite Möbius sum `Σ_{m ≤ M} μ(m) Σ_n kernel(m n)`. -/
def Ssum (b α : ℝ) (M : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (M + 1), (ArithmeticFunction.moebius m : ℝ) * innerZ b α m

lemma summable_add_one_rpow_neg {c : ℝ} (hc : 1 < c) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-c) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : -c < -1))
  simpa using h

theorem innerZ_eq_line_integral {b : ℝ} (hb : 0 < b) (α : ℝ) {m : ℕ} (hm : 1 ≤ m) {c : ℝ} (hc : 1 < c) :
    ((innerZ b α m : ℝ) : ℂ) = (1 / (2 * π) : ℂ) *
      ∫ t : ℝ, LGw b α ((c : ℂ) + t * I) * (m : ℂ) ^ (-((c : ℂ) + t * I))
        * riemannZeta ((c : ℂ) + t * I) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set x : ℕ → ℝ := fun n => (m : ℝ) * ((n : ℝ) + 1) with hx
  have hxpos : ∀ n, 0 < x n := fun n => by simp only [hx]; positivity
  set F : ℕ → ℝ → ℂ := fun n t => LGw b α ((c : ℂ) + t * I) * ((x n : ℝ) : ℂ) ^ (-((c : ℂ) + t * I))
    with hF
  have hFint : ∀ n, Integrable (F n) := fun n => integrable_LGw_cpow hb α c (hxpos n)
  have hFnorm : ∀ n t, ‖F n t‖ = x n ^ (-c) * ‖LGw b α ((c : ℂ) + t * I)‖ := by
    intro n t
    simp only [hF, norm_mul, norm_ofReal_cpow_line (hxpos n)]
    ring
  set KL := ∫ t : ℝ, ‖LGw b α ((c : ℂ) + t * I)‖ with hKL
  have hFsum : Summable fun n => ∫ t, ‖F n t‖ := by
    have e : (fun n => ∫ t, ‖F n t‖)
        = fun n : ℕ => ((m : ℝ) ^ (-c) * KL) * (((n : ℝ) + 1) ^ (-c)) := by
      funext n
      simp_rw [hFnorm n]
      rw [MeasureTheory.integral_const_mul]
      simp only [hx]
      rw [Real.mul_rpow hmR.le (by positivity)]
      ring
    rw [e]
    exact (summable_add_one_rpow_neg hc).mul_left _
  have hterm : ∀ n : ℕ, ((FleetMollifierTail.kernel b α ((m : ℝ) * ((n : ℝ) + 1)) : ℝ) : ℂ)
      = (1 / (2 * π) : ℂ) * ∫ t, F n t := by
    intro n
    rw [kernel_eq_integral hb α c (hxpos n)]
  unfold innerZ
  rw [Complex.ofReal_tsum, tsum_congr hterm, tsum_mul_left,
    integral_tsum_of_summable_integral_norm hFint hFsum]
  congr 1
  congr 1
  funext t
  have hw : 1 < ((c : ℂ) + t * I).re := by simpa using hc
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hw, ← tsum_mul_left]
  congr 1
  funext n
  simp only [hF, hx]
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hmR.le (by positivity), one_div,
    ← Complex.cpow_neg]
  push_cast
  ring

/-- **`2π · Ssum = ∫ Φ(3/2+it) ζ(3/2+it) dt`.** -/
theorem Ssum_eq_line_integral {b : ℝ} (hb : 0 < b) (α : ℝ) (M : ℕ) :
    ((Ssum b α M : ℝ) : ℂ) = (1 / (2 * π) : ℂ) *
      ∫ t : ℝ, Phi b α M (((3 / 2 : ℝ) : ℂ) + t * I) * riemannZeta (((3 / 2 : ℝ) : ℂ) + t * I) := by
  set c : ℝ := 3 / 2 with hc
  set G : ℕ → ℝ → ℂ := fun m t => LGw b α ((c : ℂ) + t * I) * (m : ℂ) ^ (-((c : ℂ) + t * I))
        * riemannZeta ((c : ℂ) + t * I) with hG
  have hGint : ∀ m : ℕ, 1 ≤ m → Integrable (G m) := by
    intro m hm
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hmR.ne'
    have hc1 : c ≠ 1 := by rw [hc]; norm_num
    set C := Real.sqrt (π / b) * Real.exp (1 / (4 * b)) with hC
    refine integrable_of_gauss_bound hb α (C * 10) (C * 5) ?_ (fun y => ?_)
    · refine ((differentiable_LGw b α).continuous.comp (continuous_line c)).mul
        ((continuous_line c).neg.const_cpow (Or.inl hm0)) |>.mul ?_
      exact continuous_iff_continuousAt.mpr fun y =>
        (differentiableAt_riemannZeta (line_ne_one hc1 y)).continuousAt.comp (x := y)
          (continuous_line c).continuousAt
    · have hL := norm_LGw_le b α c y
      have hp : ‖(m : ℂ) ^ (-((c : ℂ) + y * I))‖ ≤ 1 := by
        have := norm_ofReal_cpow_line hmR c y
        rw [show ((m : ℝ) : ℂ) = (m : ℂ) by push_cast; rfl] at this
        rw [this]
        exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm) (by rw [hc]; norm_num)
      have hZ := norm_zeta_strip_le (x := c) (y := y) (by rw [hc]; norm_num) (by rw [hc])
        (half_le_norm_line (by rw [hc]; norm_num [abs_of_pos]) y)
      have hE : Real.exp ((c - 1 / 2) ^ 2 / (4 * b)) = Real.exp (1 / (4 * b)) := by
        rw [hc]; norm_num
      rw [hE] at hL
      have hG0 : 0 ≤ Real.exp (-(y + α) ^ 2 / (4 * b)) + Real.exp (-(y - α) ^ 2 / (4 * b)) := by positivity
      simp only [hG, norm_mul]
      calc ‖LGw b α ((c : ℂ) + y * I)‖ * ‖(m : ℂ) ^ (-((c : ℂ) + y * I))‖ * ‖riemannZeta ((c : ℂ) + y * I)‖
          ≤ (C * (Real.exp (-(y + α) ^ 2 / (4 * b)) + Real.exp (-(y - α) ^ 2 / (4 * b)))) * 1
            * (10 + 5 * |y|) := by
            gcongr
        _ = _ := by ring
  have hstep : ∀ m ∈ Finset.range (M + 1),
      (((ArithmeticFunction.moebius m : ℝ) * innerZ b α m : ℝ) : ℂ)
        = (1 / (2 * π) : ℂ) * ∫ t, (ArithmeticFunction.moebius m : ℂ) * G m t := by
    intro m _
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    rw [Complex.ofReal_mul, innerZ_eq_line_integral hb α hm (by rw [hc]; norm_num : (1 : ℝ) < c),
      MeasureTheory.integral_const_mul]
    push_cast
    ring
  unfold Ssum
  rw [Complex.ofReal_sum, Finset.sum_congr rfl hstep, ← Finset.mul_sum, ← MeasureTheory.integral_finsetSum]
  · congr 1
    congr 1
    funext t
    simp only [hG, Phi, Mpoly, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  · intro m _
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    exact (hGint m hm).const_mul _


/-! ## Divisor counting and the Möbius sum over divisors -/

theorem card_divisors_le_two_sqrt (k : ℕ) : ((k.divisors.card : ℕ) : ℝ) ≤ 2 * Real.sqrt k := by
  classical
  set A := k.divisors.filter (fun d => d * d ≤ k) with hA
  set B := k.divisors.filter (fun d => ¬ d * d ≤ k) with hB
  have hsplit : k.divisors.card = A.card + B.card := (Finset.card_filter_add_card_filter_not _).symm
  have hA' : A.card ≤ Nat.sqrt k := by
    have : A ⊆ Finset.Icc 1 (Nat.sqrt k) := by
      intro d hd
      simp only [hA, Finset.mem_filter, Nat.mem_divisors] at hd
      simp only [Finset.mem_Icc]
      refine ⟨Nat.pos_of_dvd_of_pos hd.1.1 (Nat.pos_of_ne_zero hd.1.2), Nat.le_sqrt.mpr hd.2⟩
    simpa using Finset.card_le_card this
  have hB' : B.card ≤ A.card := by
    refine Finset.card_le_card_of_injOn (fun d => k / d) ?_ ?_
    · intro d hd
      simp only [hB, Finset.coe_filter, Set.mem_ofPred_eq, Nat.mem_divisors] at hd
      simp only [hA, Finset.coe_filter, Set.mem_ofPred_eq, Nat.mem_divisors]
      obtain ⟨⟨hdk, hk⟩, hdd⟩ := hd
      refine ⟨⟨Nat.div_dvd_of_dvd hdk, hk⟩, ?_⟩
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdk (Nat.pos_of_ne_zero hk)
      have hlt : k / d < d := by
        rw [Nat.div_lt_iff_lt_mul hd0]; push Not at hdd; exact hdd
      calc k / d * (k / d) ≤ k / d * d := Nat.mul_le_mul_left _ hlt.le
        _ = k := Nat.div_mul_cancel hdk
    · intro d1 hd1 d2 hd2 h
      simp only [hB, Finset.coe_filter, Set.mem_ofPred_eq, Nat.mem_divisors] at hd1 hd2
      have := congrArg (fun x => k / x) h
      simp only at this
      rwa [Nat.div_div_self hd1.1.1 hd1.1.2, Nat.div_div_self hd2.1.1 hd2.1.2] at this
  have hs := Real.nat_sqrt_le_real_sqrt (a := k)
  have : ((k.divisors.card : ℕ) : ℝ) ≤ 2 * (Nat.sqrt k : ℝ) := by
    rw [hsplit]; push_cast
    have h1 : (A.card : ℝ) ≤ Nat.sqrt k := by exact_mod_cast hA'
    have h2 : (B.card : ℝ) ≤ A.card := by exact_mod_cast hB'
    linarith
  linarith

theorem sum_moebius_filter {M k : ℕ} (hk : 1 ≤ k) (hkM : k ≤ M) :
    ∑ m ∈ (Finset.range (M + 1)).filter (· ∣ k), (ArithmeticFunction.moebius m : ℝ)
      = if k = 1 then 1 else 0 := by
  have hf : (Finset.range (M + 1)).filter (· ∣ k) = k.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
    constructor
    · rintro ⟨_, h⟩; exact ⟨h, by omega⟩
    · rintro ⟨h, _⟩; exact ⟨by have := Nat.le_of_dvd hk h; omega, h⟩
  rw [hf]
  have h := congrArg (fun f : ArithmeticFunction ℤ => f k) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  have h' := congrArg (fun z : ℤ => (z : ℝ)) h
  push_cast at h'
  rw [h']

/-! ## The kernel -/

lemma abs_kernel_le (b α : ℝ) (x : ℝ) :
    |FleetMollifierTail.kernel b α x| ≤ 2 * Real.exp (-Real.log x / 2 - b * Real.log x ^ 2) := by
  unfold FleetMollifierTail.kernel
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos (Real.exp_pos _)]
  have := Real.abs_cos_le_one (α * Real.log x)
  nlinarith [Real.exp_pos (-Real.log x / 2 - b * Real.log x ^ 2)]

lemma kernel_one (b α : ℝ) : FleetMollifierTail.kernel b α 1 = 2 := by
  simp [FleetMollifierTail.kernel]

lemma abs_kernel_le_rpow {b : ℝ} (hb : 0 < b) (α : ℝ) {x : ℝ} (hx : 0 < x) :
    |FleetMollifierTail.kernel b α x| ≤ 2 * Real.exp (1 / b) * x ^ (-(5 / 2 : ℝ)) := by
  refine (abs_kernel_le b α x).trans ?_
  set L := Real.log x
  have hrp : x ^ (-(5 / 2 : ℝ)) = Real.exp (L * (-(5 / 2 : ℝ))) := Real.rpow_def_of_pos hx _
  rw [hrp, mul_assoc, ← Real.exp_add]
  have key : b * L ^ 2 - 2 * L + 1 / b = (b * L - 1) ^ 2 / b := by field_simp; ring
  have h0 : 0 ≤ (b * L - 1) ^ 2 / b := by positivity
  have : -L / 2 - b * L ^ 2 ≤ 1 / b + L * (-(5 / 2 : ℝ)) := by linarith
  gcongr

lemma abs_kernel_le_tail {b : ℝ} (hb : 0 < b) (α : ℝ) {x : ℝ} (hx : 0 < x)
    (hL : 11 / (10 * b) ≤ Real.log x) :
    |FleetMollifierTail.kernel b α x| ≤ 2 * x ^ (-(8 / 5 : ℝ)) := by
  refine (abs_kernel_le b α x).trans ?_
  set L := Real.log x
  have hrp : x ^ (-(8 / 5 : ℝ)) = Real.exp (L * (-(8 / 5 : ℝ))) := Real.rpow_def_of_pos hx _
  rw [hrp]
  have hL0 : 0 ≤ L := le_trans (by positivity) hL
  have hbL : 11 / 10 ≤ b * L := by
    have := mul_le_mul_of_nonneg_left hL hb.le
    rwa [show b * (11 / (10 * b)) = 11 / 10 by field_simp] at this
  have : -L / 2 - b * L ^ 2 ≤ L * (-(8 / 5 : ℝ)) := by nlinarith
  gcongr

lemma summable_kernel_bound {b : ℝ} :
    Summable fun k : ℕ => 2 * Real.exp (1 / b) * (k : ℝ) ^ (-(5 / 2 : ℝ)) :=
  (Real.summable_nat_rpow.mpr (by norm_num)).mul_left _

/-! ## `Ssum = 2 + (terms with k > M)` -/

/-- The multiples-of-`m` indicator of the kernel. -/
def fk (b α : ℝ) (m k : ℕ) : ℝ := if m ∣ k ∧ k ≠ 0 then FleetMollifierTail.kernel b α k else 0

lemma abs_fk_le {b : ℝ} (hb : 0 < b) (α : ℝ) (m k : ℕ) :
    |fk b α m k| ≤ 2 * Real.exp (1 / b) * (k : ℝ) ^ (-(5 / 2 : ℝ)) := by
  unfold fk
  split_ifs with h
  · exact abs_kernel_le_rpow hb α (by exact_mod_cast Nat.pos_of_ne_zero h.2)
  · simp only [abs_zero]; positivity

lemma summable_fk {b : ℝ} (hb : 0 < b) (α : ℝ) (m : ℕ) : Summable (fk b α m) :=
  Summable.of_norm_bounded summable_kernel_bound fun k => by
    rw [Real.norm_eq_abs]; exact abs_fk_le hb α m k

lemma moebius_mul_innerZ (b α : ℝ) (m : ℕ) :
    (ArithmeticFunction.moebius m : ℝ) * innerZ b α m
      = (ArithmeticFunction.moebius m : ℝ) * ∑' k : ℕ, fk b α m k := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  congr 1
  unfold innerZ
  have hinj : Function.Injective (fun n : ℕ => m * (n + 1)) := by
    intro a c h; simp only at h
    have := Nat.eq_of_mul_eq_mul_left hm h; omega
  rw [← hinj.tsum_eq (f := fk b α m)]
  · congr 1; funext n
    have hc : m ∣ m * (n + 1) ∧ m * (n + 1) ≠ 0 := ⟨Dvd.intro _ rfl, by positivity⟩
    simp only [fk]
    rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
    push_cast; ring_nf
  · intro k hk
    simp only [Function.mem_support, fk] at hk
    split_ifs at hk with h
    · obtain ⟨⟨j, rfl⟩, h0⟩ := h
      have hj : j ≠ 0 := by rintro rfl; simp at h0
      exact ⟨j - 1, by simp only; congr 1; omega⟩
    · exact absurd rfl hk

lemma Ssum_eq_tsum {b : ℝ} (hb : 0 < b) (α : ℝ) (M : ℕ) :
    Ssum b α M = ∑' k : ℕ, ∑ m ∈ Finset.range (M + 1), (ArithmeticFunction.moebius m : ℝ) * fk b α m k := by
  unfold Ssum
  rw [Finset.sum_congr rfl fun m _ => moebius_mul_innerZ b α m, Summable.tsum_finsetSum]
  · exact Finset.sum_congr rfl fun m _ => (tsum_mul_left).symm
  · intro m _; exact (summable_fk hb α m).mul_left _

lemma sum_fk_eq (b α : ℝ) (M k : ℕ) (hk : k ≠ 0) :
    ∑ m ∈ Finset.range (M + 1), (ArithmeticFunction.moebius m : ℝ) * fk b α m k
      = (∑ m ∈ (Finset.range (M + 1)).filter (· ∣ k), (ArithmeticFunction.moebius m : ℝ))
        * FleetMollifierTail.kernel b α k := by
  rw [Finset.sum_filter, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [fk]
  split_ifs with h1 h2 h2 <;> simp_all


/-- The tail majorant `Σ_{j ≥ 0} 4 (j + M + 1)^{-11/10}`. -/
def tailMaj (M : ℕ) : ℝ := ∑' j : ℕ, 4 * ((j : ℝ) + ((M + 1 : ℕ) : ℝ)) ^ (-(11 / 10 : ℝ))

lemma summable_four_rpow : Summable fun k : ℕ => 4 * (k : ℝ) ^ (-(11 / 10 : ℝ)) :=
  (Real.summable_nat_rpow.mpr (by norm_num)).mul_left _

/-- **`|Ssum − 2|` is bounded by the tail majorant**, when every `k > M` has `log k ≥ 1.1/b`. -/
theorem abs_Ssum_sub_two_le {b : ℝ} (hb : 0 < b) (α : ℝ) {M : ℕ} (hM : 1 ≤ M)
    (hlog : ∀ k : ℕ, M < k → 11 / (10 * b) ≤ Real.log k) :
    |Ssum b α M - 2| ≤ tailMaj M := by
  set A : ℕ → ℝ := fun k => ∑ m ∈ Finset.range (M + 1), (ArithmeticFunction.moebius m : ℝ) * fk b α m k
    with hA
  set E : ℕ → ℝ := fun k => A k - if k = 1 then 2 else 0 with hE
  set g : ℕ → ℝ := fun k => if M < k then 4 * (k : ℝ) ^ (-(11 / 10 : ℝ)) else 0 with hg
  have hAs : Summable A := by
    simp only [hA]
    exact summable_sum fun m _ => (summable_fk hb α m).mul_left _
  have hEk : ∀ k, |E k| ≤ g k := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [hE, hA, hg, fk]
    simp only [hE, hA, hg]
    rw [sum_fk_eq b α M k hk0.ne']
    by_cases hkM : M < k
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hkM), ite_eq_right_of_eq_false _ _ (eq_false (by omega : k ≠ 1)), sub_zero,
        abs_mul]
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
      have h1 : |∑ m ∈ (Finset.range (M + 1)).filter (· ∣ k), (ArithmeticFunction.moebius m : ℝ)|
          ≤ 2 * Real.sqrt k := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        have hsub : (Finset.range (M + 1)).filter (· ∣ k) ⊆ k.divisors := by
          intro m hm
          simp only [Finset.mem_filter] at hm
          exact Nat.mem_divisors.mpr ⟨hm.2, hk0.ne'⟩
        calc ∑ m ∈ (Finset.range (M + 1)).filter (· ∣ k), |(ArithmeticFunction.moebius m : ℝ)|
            ≤ ∑ m ∈ (Finset.range (M + 1)).filter (· ∣ k), (1 : ℝ) :=
              Finset.sum_le_sum fun m _ => FleetMollifierTail.moebius_abs_le m
          _ ≤ ∑ m ∈ k.divisors, (1 : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; norm_num)
          _ = (k.divisors.card : ℝ) := by simp
          _ ≤ 2 * Real.sqrt k := card_divisors_le_two_sqrt k
      have h2 := abs_kernel_le_tail hb α hkR (hlog k hkM)
      have hsq : Real.sqrt k * (k : ℝ) ^ (-(8 / 5 : ℝ)) = (k : ℝ) ^ (-(11 / 10 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hkR]; norm_num
      calc |∑ m ∈ (Finset.range (M + 1)).filter (· ∣ k), (ArithmeticFunction.moebius m : ℝ)|
            * |FleetMollifierTail.kernel b α k|
          ≤ (2 * Real.sqrt k) * (2 * (k : ℝ) ^ (-(8 / 5 : ℝ))) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = 4 * (k : ℝ) ^ (-(11 / 10 : ℝ)) := by rw [← hsq]; ring
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hkM), sum_moebius_filter hk0 (by omega)]
      split_ifs with h
      · subst h; simp only [Nat.cast_one, kernel_one]; norm_num
      · simp
  have hgs : Summable g := by
    refine Summable.of_norm_bounded summable_four_rpow fun k => ?_
    simp only [hg]
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    · simp only [norm_zero]; positivity
  have hEs : Summable E := by
    refine Summable.of_norm_bounded hgs fun k => ?_
    rw [Real.norm_eq_abs]; exact hEk k
  have hSum : Ssum b α M - 2 = ∑' k, E k := by
    rw [Ssum_eq_tsum hb α M]
    simp only [hE]
    rw [Summable.tsum_sub hAs ⟨_, hasSum_ite_eq 1 (2 : ℝ)⟩, tsum_ite_eq]
  have hgt : ∑' k, g k = tailMaj M := by
    rw [← hgs.sum_add_tsum_nat_add (M + 1)]
    have h0 : ∑ i ∈ Finset.range (M + 1), g i = 0 :=
      Finset.sum_eq_zero fun i hi => by
        simp only [hg]; rw [ite_eq_right_of_eq_false _ _ (eq_false (by simp at hi; omega))]
    rw [h0, zero_add]
    unfold tailMaj
    congr 1; funext j
    simp only [hg]
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
    push_cast; ring_nf
  rw [hSum, ← hgt]
  calc |∑' k, E k| = ‖∑' k, E k‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' k, ‖E k‖ := norm_tsum_le_tsum_norm (hEs.norm)
    _ ≤ ∑' k, g k := by
        refine hEs.norm.tsum_le_tsum (fun k => ?_) hgs
        rw [Real.norm_eq_abs]; exact hEk k

/-- The tail majorant tends to `0`. -/
lemma tendsto_tailMaj : Tendsto tailMaj atTop (𝓝 0) := by
  have h := tendsto_sum_nat_add (fun k : ℕ => 4 * (k : ℝ) ^ (-(11 / 10 : ℝ)))
  have h' := h.comp (tendsto_add_atTop_nat 1)
  refine h'.congr fun M => ?_
  simp only [Function.comp, tailMaj]
  congr 1; funext j; push_cast; ring_nf


/-! ## The critical line: Cauchy–Schwarz against the window -/

/-- `‖ζ(1/2+it)‖ ≤ 10 + 5|t|`. -/
lemma norm_zeta_half_le (t : ℝ) : ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖ ≤ 10 + 5 * |t| :=
  norm_zeta_strip_le (by norm_num) (by norm_num) (half_le_norm_line (by norm_num [abs_of_neg]) t)

/-- The constant of the `ζ` window: `∫ ‖ζ(1/2+it)‖² e^{-(t−β)²/4b} dt ≤ Zq β √b`. -/
def Zq (β : ℝ) : ℝ := (200 + 100 * β ^ 2) * Real.sqrt (4 * π) + 800 * Real.sqrt (8 * π)

lemma Zq_pos (β : ℝ) : 0 < Zq β := by unfold Zq; positivity

lemma continuous_zeta_half : Continuous fun t : ℝ => riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I) :=
  continuous_iff_continuousAt.mpr fun y =>
    (differentiableAt_riemannZeta (line_ne_one (by norm_num) y)).continuousAt.comp (x := y)
      (continuous_line _).continuousAt

lemma zeta_sq_le (β t : ℝ) :
    ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 ≤ (200 + 100 * β ^ 2) + 100 * (t - β) ^ 2 := by
  have hz := norm_zeta_half_le t
  have h1 : ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 ≤ (10 + 5 * |t|) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hz 2
  have h2 : (10 + 5 * |t|) ^ 2 ≤ 200 + 50 * t ^ 2 := by
    nlinarith [sq_nonneg (10 - 5 * |t|), _root_.sq_abs t]
  nlinarith [sq_nonneg (t - 2 * β)]

/-- **`ζ` window on the critical line**: integrable, and `≤ Zq β √b` for `0 < b ≤ 1`. -/
theorem zeta_half_window {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (β : ℝ) :
    Integrable (fun t : ℝ => ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2
      * Real.exp (-(t - β) ^ 2 / (4 * b))) ∧
    ∫ t : ℝ, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 * Real.exp (-(t - β) ^ 2 / (4 * b))
      ≤ Zq β * Real.sqrt b := by
  set g : ℝ → ℝ := fun t => (200 + 100 * β ^ 2) * Real.exp (-(t - β) ^ 2 / (4 * b))
    + 800 * b * Real.exp (-(t - β) ^ 2 / (8 * b)) with hg
  have hgi : Integrable g :=
    ((integrable_gauss_scale (by positivity) β).const_mul _).add
      ((integrable_gauss_scale (by positivity) β).const_mul _)
  have hpt : ∀ t : ℝ, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2
      * Real.exp (-(t - β) ^ 2 / (4 * b)) ≤ g t := by
    intro t
    have hsq := zeta_sq_le β t
    have hE := Real.exp_pos (-(t - β) ^ 2 / (4 * b))
    have hs := sq_gauss_le hb (t - β)
    calc ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 * Real.exp (-(t - β) ^ 2 / (4 * b))
        ≤ ((200 + 100 * β ^ 2) + 100 * (t - β) ^ 2) * Real.exp (-(t - β) ^ 2 / (4 * b)) :=
          mul_le_mul_of_nonneg_right hsq hE.le
      _ = (200 + 100 * β ^ 2) * Real.exp (-(t - β) ^ 2 / (4 * b))
          + 100 * ((t - β) ^ 2 * Real.exp (-(t - β) ^ 2 / (4 * b))) := by ring
      _ ≤ g t := by simp only [hg]; nlinarith
  have hint : Integrable (fun t : ℝ => ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2
      * Real.exp (-(t - β) ^ 2 / (4 * b))) := by
    refine Integrable.mono' hgi ?_ (ae_of_all _ fun t => ?_)
    · exact ((continuous_zeta_half.norm.pow 2).mul (by fun_prop)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, _root_.abs_of_nonneg (by positivity)]
      exact hpt t
  refine ⟨hint, ?_⟩
  have hsb : Real.sqrt (π * (4 * b)) = Real.sqrt (4 * π) * Real.sqrt b := by
    rw [← Real.sqrt_mul (by positivity)]; ring_nf
  have hsb8 : Real.sqrt (π * (8 * b)) = Real.sqrt (8 * π) * Real.sqrt b := by
    rw [← Real.sqrt_mul (by positivity)]; ring_nf
  calc ∫ t : ℝ, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2 * Real.exp (-(t - β) ^ 2 / (4 * b))
      ≤ ∫ t, g t := integral_mono hint hgi hpt
    _ = (200 + 100 * β ^ 2) * Real.sqrt (π * (4 * b)) + 800 * b * Real.sqrt (π * (8 * b)) := by
        simp only [hg]
        rw [integral_add ((integrable_gauss_scale (by positivity) β).const_mul _)
          ((integrable_gauss_scale (by positivity) β).const_mul _), MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul,
          integral_gauss_scale (by positivity), integral_gauss_scale (by positivity)]
    _ ≤ Zq β * Real.sqrt b := by
        rw [hsb, hsb8]
        unfold Zq
        have h8 : 0 ≤ Real.sqrt (8 * π) * Real.sqrt b := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hb1 h8]

/-- **Cauchy–Schwarz in the Gaussian weight**:
`∫ ‖M‖‖ζ‖ e^{-(t−β)²/4b} ≤ √(headWindow b β) √(∫ ‖ζ‖² e^{-(t−β)²/4b})`. -/
theorem cs_window {b : ℝ} (hb : 0 < b) (β : ℝ) :
    Integrable (fun t : ℝ => ‖Mpoly (FleetFiniteHeadRH.cut b) (((1 / 2 : ℝ) : ℂ) + t * I)‖
      * ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖ * Real.exp (-(t - β) ^ 2 / (4 * b))) ∧
    ∫ t : ℝ, ‖Mpoly (FleetFiniteHeadRH.cut b) (((1 / 2 : ℝ) : ℂ) + t * I)‖
      * ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖ * Real.exp (-(t - β) ^ 2 / (4 * b))
      ≤ Real.sqrt (headWindow b β) * Real.sqrt (∫ t : ℝ, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2
          * Real.exp (-(t - β) ^ 2 / (4 * b))) := by
  set N := FleetFiniteHeadRH.cut b
  set m : ℝ → ℝ := fun t => ‖Mpoly N (((1 / 2 : ℝ) : ℂ) + t * I)‖ with hm
  set z : ℝ → ℝ := fun t => ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖ with hz
  set w : ℝ → ℝ := fun t => Real.exp (-(t - β) ^ 2 / (4 * b)) with hw
  have hX := integrable_M_window hb N β
  have hZ : Integrable (fun t : ℝ => z t ^ 2 * w t) := by
    -- `ζ` window integrability holds for every `b > 0` (the bound below needs no `b ≤ 1`)
    refine Integrable.mono' (((integrable_gauss_scale (d := 4 * b) (by positivity) β).const_mul
      (200 + 100 * β ^ 2)).add (((integrable_gauss_scale (d := 8 * b) (by positivity) β).const_mul
      (800 * b)))) ?_ (ae_of_all _ fun t => ?_)
    · exact ((continuous_zeta_half.norm.pow 2).mul (by fun_prop)).aestronglyMeasurable
    · have hsq := zeta_sq_le β t
      have hE := Real.exp_pos (-(t - β) ^ 2 / (4 * b))
      have hs := sq_gauss_le hb (t - β)
      rw [Real.norm_eq_abs, _root_.abs_of_nonneg (by positivity)]
      simp only [hz, hw, Pi.add_apply]
      nlinarith [mul_le_mul_of_nonneg_right hsq hE.le]
  have hcont_m : Continuous m :=
    ((differentiable_Mpoly N).continuous.comp (continuous_line (1 / 2))).norm
  have hMZ : Integrable (fun t : ℝ => m t * z t * w t) := by
    refine Integrable.mono' ((hX.add hZ).div_const 2) ?_ (ae_of_all _ fun t => ?_)
    · exact ((hcont_m.mul continuous_zeta_half.norm).mul (by fun_prop)).aestronglyMeasurable
    · have hw0 : 0 ≤ w t := (Real.exp_pos _).le
      have hm0 : 0 ≤ m t := norm_nonneg _
      have hz0 : 0 ≤ z t := norm_nonneg _
      rw [Real.norm_eq_abs, _root_.abs_of_nonneg (by positivity)]
      simp only [Pi.add_apply]
      nlinarith [mul_nonneg (sq_nonneg (m t - z t)) hw0]
  refine ⟨hMZ, ?_⟩
  apply le_sqrt_mul_of_forall (integral_nonneg fun t => by positivity)
    (integral_nonneg fun t => by positivity)
  intro l hl
  have hpt : ∀ t, 2 * (m t * z t * w t) ≤ l * (m t ^ 2 * w t) + (z t ^ 2 * w t) / l := by
    intro t
    have hw0 : 0 ≤ w t := (Real.exp_pos _).le
    have key : 2 * (m t * z t) ≤ l * m t ^ 2 + z t ^ 2 / l := by
      have : 0 ≤ (l * m t - z t) ^ 2 / l := by positivity
      have e : (l * m t - z t) ^ 2 / l = l * m t ^ 2 - 2 * (m t * z t) + z t ^ 2 / l := by
        field_simp; ring
      linarith
    have := mul_le_mul_of_nonneg_right key hw0
    calc 2 * (m t * z t * w t) = 2 * (m t * z t) * w t := by ring
      _ ≤ (l * m t ^ 2 + z t ^ 2 / l) * w t := this
      _ = _ := by ring
  have hX' : Integrable (fun t : ℝ => m t ^ 2 * w t) := hX
  have hint : ∫ t, 2 * (m t * z t * w t) ≤ ∫ t, (l * (m t ^ 2 * w t) + z t ^ 2 * w t / l) :=
    integral_mono (hMZ.const_mul 2) ((hX'.const_mul l).add (hZ.div_const l)) hpt
  rw [MeasureTheory.integral_const_mul, integral_add (hX'.const_mul l) (hZ.div_const l),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_div] at hint
  exact hint


/-- The window-weighted mixed integral `∫ ‖M_{cut b}‖ ‖ζ‖ e^{-(t−β)²/4b}` on the critical line. -/
def mixI (b β : ℝ) : ℝ :=
  ∫ t : ℝ, ‖Mpoly (FleetFiniteHeadRH.cut b) (((1 / 2 : ℝ) : ℂ) + t * I)‖
    * ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖ * Real.exp (-(t - β) ^ 2 / (4 * b))

lemma mixI_le {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (β : ℝ) :
    mixI b β ≤ Real.sqrt (headWindow b β) * Real.sqrt (Zq β * Real.sqrt b) := by
  refine (cs_window hb β).2.trans ?_
  gcongr
  exact (zeta_half_window hb hb1 β).2

/-- **The critical-line pairing is bounded by the windows**:
`2π ‖Ssum − Φ(1)‖ ≤ √(π/b) (mixI(−α) + mixI(α))`. -/
theorem two_pi_norm_le {b : ℝ} (hb : 0 < b) (α : ℝ) :
    2 * π * ‖((Ssum b α (FleetFiniteHeadRH.cut b) : ℝ) : ℂ) - Phi b α (FleetFiniteHeadRH.cut b) 1‖
      ≤ Real.sqrt (π / b) * (mixI b (-α) + mixI b α) := by
  set N := FleetFiniteHeadRH.cut b
  have hshift := pairing_shift hb α N
  have hS := Ssum_eq_line_integral hb α N
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hJ : (∫ y : ℝ, Phi b α N (((1 / 2 : ℝ) : ℂ) + y * I) * riemannZeta (((1 / 2 : ℝ) : ℂ) + y * I))
      = 2 * π * (((Ssum b α N : ℝ) : ℂ) - Phi b α N 1) := by
    rw [hS]
    have : (2 * π : ℂ) * ((1 / (2 * π) : ℂ) *
        ∫ t : ℝ, Phi b α N (((3 / 2 : ℝ) : ℂ) + t * I) * riemannZeta (((3 / 2 : ℝ) : ℂ) + t * I))
        = ∫ t : ℝ, Phi b α N (((3 / 2 : ℝ) : ℂ) + t * I) * riemannZeta (((3 / 2 : ℝ) : ℂ) + t * I) := by
      rw [← mul_assoc, mul_one_div_cancel (mul_ne_zero two_ne_zero hpi), one_mul]
    rw [mul_sub, this]
    linear_combination -hshift
  have hnorm : ‖2 * (π : ℂ) * (((Ssum b α N : ℝ) : ℂ) - Phi b α N 1)‖
      = 2 * π * ‖((Ssum b α N : ℝ) : ℂ) - Phi b α N 1‖ := by
    rw [norm_mul, norm_mul]; simp [abs_of_pos Real.pi_pos]
  rw [← hnorm, ← hJ]
  have h1 := (cs_window hb (-α)).1
  have h2 := (cs_window hb α).1
  have hpt : ∀ t : ℝ, ‖Phi b α N (((1 / 2 : ℝ) : ℂ) + t * I) * riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖
      ≤ Real.sqrt (π / b) *
        (‖Mpoly N (((1 / 2 : ℝ) : ℂ) + t * I)‖ * ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖
            * Real.exp (-(t - -α) ^ 2 / (4 * b))
          + ‖Mpoly N (((1 / 2 : ℝ) : ℂ) + t * I)‖ * ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖
            * Real.exp (-(t - α) ^ 2 / (4 * b))) := by
    intro t
    have hL := norm_LGw_le b α (1 / 2) t
    rw [show ((1 / 2 : ℝ) - 1 / 2) ^ 2 / (4 * b) = 0 by ring, Real.exp_zero, mul_one] at hL
    rw [show t + α = t - -α by ring] at hL
    unfold Phi
    rw [norm_mul, norm_mul]
    have hm0 := norm_nonneg (Mpoly N (((1 / 2 : ℝ) : ℂ) + t * I))
    have hz0 := norm_nonneg (riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I))
    calc ‖LGw b α (((1 / 2 : ℝ) : ℂ) + t * I)‖ * ‖Mpoly N (((1 / 2 : ℝ) : ℂ) + t * I)‖
          * ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖
        ≤ (Real.sqrt (π / b) * (Real.exp (-(t - -α) ^ 2 / (4 * b)) + Real.exp (-(t - α) ^ 2 / (4 * b))))
          * ‖Mpoly N (((1 / 2 : ℝ) : ℂ) + t * I)‖ * ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖ := by
          gcongr
      _ = _ := by ring
  have hmaj : Integrable (fun t : ℝ => Real.sqrt (π / b) *
        (‖Mpoly N (((1 / 2 : ℝ) : ℂ) + t * I)‖ * ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖
            * Real.exp (-(t - -α) ^ 2 / (4 * b))
          + ‖Mpoly N (((1 / 2 : ℝ) : ℂ) + t * I)‖ * ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖
            * Real.exp (-(t - α) ^ 2 / (4 * b)))) := (h1.add h2).const_mul _
  calc ‖∫ y : ℝ, Phi b α N (((1 / 2 : ℝ) : ℂ) + y * I) * riemannZeta (((1 / 2 : ℝ) : ℂ) + y * I)‖
      ≤ ∫ y : ℝ, ‖Phi b α N (((1 / 2 : ℝ) : ℂ) + y * I) * riemannZeta (((1 / 2 : ℝ) : ℂ) + y * I)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, Real.sqrt (π / b) *
        (‖Mpoly N (((1 / 2 : ℝ) : ℂ) + t * I)‖ * ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖
            * Real.exp (-(t - -α) ^ 2 / (4 * b))
          + ‖Mpoly N (((1 / 2 : ℝ) : ℂ) + t * I)‖ * ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖
            * Real.exp (-(t - α) ^ 2 / (4 * b))) :=
        integral_mono (integrable_fZ_line hb α N (by norm_num) (by norm_num)
          (by norm_num [abs_of_neg])).norm hmaj hpt
    _ = Real.sqrt (π / b) * (mixI b (-α) + mixI b α) := by
        rw [MeasureTheory.integral_const_mul, integral_add h1 h2]
        rfl


/-! ## The residue `Φ(1)` at `α = 1`, and the lower bound -/

lemma norm_Phi_one_le {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    ‖Phi b 1 (FleetFiniteHeadRH.cut b) 1‖
      ≤ 2 * Real.sqrt (π / b) * Real.exp (-(3 / (16 * b))) * (1 + 11 / (10 * b)) := by
  set N := FleetFiniteHeadRH.cut b
  have hL := norm_LGw_le b 1 1 0
  have e1 : ((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I = 1 := by simp
  rw [e1] at hL
  have e2 : Real.exp ((1 - 1 / 2) ^ 2 / (4 * b)) *
      (Real.exp (-(0 + 1) ^ 2 / (4 * b)) + Real.exp (-(0 - 1) ^ 2 / (4 * b)))
      = 2 * Real.exp (-(3 / (16 * b))) := by
    rw [show (-(0 + 1 : ℝ) ^ 2 / (4 * b)) = -1 / (4 * b) by ring,
      show (-(0 - 1 : ℝ) ^ 2 / (4 * b)) = -1 / (4 * b) by ring, ← two_mul, mul_left_comm,
      ← Real.exp_add]
    congr 2; field_simp; ring
  have hM := norm_Mpoly_le_harm N (σ := 1) le_rfl (w := 1) (by simp)
  rw [sub_self, Real.rpow_zero, one_mul] at hM
  have hlog := log_cut_le hb hb1
  unfold Phi
  rw [norm_mul]
  calc ‖LGw b 1 1‖ * ‖Mpoly N 1‖
      ≤ (Real.sqrt (π / b) * (2 * Real.exp (-(3 / (16 * b))))) * (1 + 11 / (10 * b)) := by
        apply mul_le_mul _ (by linarith) (norm_nonneg _) (by positivity)
        rw [mul_assoc] at hL; rw [← e2]; exact hL
    _ = _ := by ring

lemma sqrt_le_one_add {u : ℝ} (hu : 0 ≤ u) : Real.sqrt u ≤ 1 + u := by
  rw [Real.sqrt_le_left (by linarith)]; nlinarith

lemma tendsto_quad_exp {c : ℝ} (hc : 0 < c) (A B D : ℝ) :
    Tendsto (fun u : ℝ => (A + B * u + D * u ^ 2) * Real.exp (-(c * u))) atTop (𝓝 0) := by
  have h0 := (isLittleO_pow_exp_pos_mul_atTop 0 hc).tendsto_div_nhds_zero
  have h1 := (isLittleO_pow_exp_pos_mul_atTop 1 hc).tendsto_div_nhds_zero
  have h2 := (isLittleO_pow_exp_pos_mul_atTop 2 hc).tendsto_div_nhds_zero
  have h := ((h0.const_mul A).add (h1.const_mul B)).add (h2.const_mul D)
  simp only [mul_zero, add_zero] at h
  refine h.congr fun u => ?_
  rw [Real.exp_neg]
  simp only [pow_zero, pow_one]
  ring

lemma tendsto_cut : Tendsto FleetFiniteHeadRH.cut (𝓝[>] 0) atTop := by
  have h1 : Tendsto (fun b : ℝ => 11 / (10 * b)) (𝓝[>] 0) atTop := by
    have := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop (by norm_num : (0 : ℝ) < 11 / 10)
    refine this.congr fun b => ?_
    field_simp
  exact tendsto_nat_floor_atTop.comp (Real.tendsto_exp_atTop.comp h1)

/-- The error allowance `tailMaj (cut b) + 2√π (1 + 1/b)(1 + 11/(10b)) e^{-3/(16b)}` tends to `0`. -/
lemma tendsto_err :
    Tendsto (fun b : ℝ => tailMaj (FleetFiniteHeadRH.cut b) +
      2 * Real.sqrt π * (1 + b⁻¹) * (1 + 11 / 10 * b⁻¹) * Real.exp (-(3 / 16 * b⁻¹))) (𝓝[>] 0) (𝓝 0) := by
  have hA := tendsto_tailMaj.comp tendsto_cut
  have hB : Tendsto (fun u : ℝ => 2 * Real.sqrt π * (1 + u) * (1 + 11 / 10 * u) * Real.exp (-(3 / 16 * u)))
      atTop (𝓝 0) := by
    have := tendsto_quad_exp (c := 3 / 16) (by norm_num) (2 * Real.sqrt π) (2 * Real.sqrt π * (21 / 10))
      (2 * Real.sqrt π * (11 / 10))
    refine this.congr fun u => ?_
    ring
  have := hA.add (hB.comp tendsto_inv_nhdsGT_zero)
  simpa using this

/-- The `ζ`-window constant at `β = ±1`. -/
def Z1 : ℝ := 300 * Real.sqrt (4 * π) + 800 * Real.sqrt (8 * π)

lemma Zq_one : Zq 1 = Z1 := by unfold Zq Z1; norm_num
lemma Zq_neg_one : Zq (-1) = Z1 := by unfold Zq Z1; norm_num
lemma Z1_pos : 0 < Z1 := by rw [← Zq_one]; exact Zq_pos 1

/-- **Positive lower bound for the window** (no hypothesis): there is `b₀ > 0` with
`headWindow b 1 + headWindow b (−1) ≥ 2π √b / Z1` for all `0 < b ≤ b₀`, where
`Z1 = 300√(4π) + 800√(8π)`. In particular the window is not exponentially small as `b → 0`. -/
theorem headWindow_lower :
    ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b ≤ b₀ →
      2 * π * Real.sqrt b / Z1 ≤ headWindow b 1 + headWindow b (-1) := by
  have hev : ∀ᶠ b in 𝓝[>] (0 : ℝ), tailMaj (FleetFiniteHeadRH.cut b) +
      2 * Real.sqrt π * (1 + b⁻¹) * (1 + 11 / 10 * b⁻¹) * Real.exp (-(3 / 16 * b⁻¹)) < 1 :=
    tendsto_err.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨min (u / 2) 1, lt_min (half_pos hu) one_pos, fun b hb hbu => ?_⟩
  have hb1 : b ≤ 1 := hbu.trans (min_le_right _ _)
  have hbU : b ∈ Set.Ioo 0 u := ⟨hb, by linarith [hbu.trans (min_le_left _ _)]⟩
  have herr := hsub hbU
  simp only [Set.mem_ofPred_eq] at herr
  set N := FleetFiniteHeadRH.cut b
  -- the lower side
  have hN1 : 1 ≤ N := cut_pos hb hb1
  have hlogk : ∀ k : ℕ, N < k → 11 / (10 * b) ≤ Real.log k := by
    intro k hk
    have hk' : Real.exp (11 / (10 * b)) < k := by
      have := Nat.lt_floor_add_one (Real.exp (11 / (10 * b)))
      have hNdef : ((⌊Real.exp (11 / (10 * b))⌋₊ : ℕ) : ℝ) = N := rfl
      rw [hNdef] at this
      have hk1 : (N : ℝ) + 1 ≤ k := by exact_mod_cast hk
      linarith
    have hk0 : (0 : ℝ) < k := lt_trans (Real.exp_pos _) hk'
    exact ((Real.lt_log_iff_exp_lt hk0).mpr hk').le
  have hS := abs_Ssum_sub_two_le hb 1 hN1 hlogk
  have hP := norm_Phi_one_le hb hb1
  have hR : 2 * Real.sqrt (π / b) * Real.exp (-(3 / (16 * b))) * (1 + 11 / (10 * b))
      ≤ 2 * Real.sqrt π * (1 + b⁻¹) * (1 + 11 / 10 * b⁻¹) * Real.exp (-(3 / 16 * b⁻¹)) := by
    have e1 : Real.sqrt (π / b) = Real.sqrt π * Real.sqrt b⁻¹ := by
      rw [div_eq_mul_inv, Real.sqrt_mul Real.pi_pos.le]
    have e2 : 3 / (16 * b) = 3 / 16 * b⁻¹ := by field_simp
    have e3 : 11 / (10 * b) = 11 / 10 * b⁻¹ := by field_simp
    rw [e1, e2, e3]
    have hs := sqrt_le_one_add (inv_nonneg.mpr hb.le)
    have hp : 0 ≤ 2 * Real.sqrt π * Real.exp (-(3 / 16 * b⁻¹)) * (1 + 11 / 10 * b⁻¹) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hs hp]
  have hlow : 1 ≤ ‖((Ssum b 1 N : ℝ) : ℂ) - Phi b 1 N 1‖ := by
    have h1 : ‖((Ssum b 1 N : ℝ) : ℂ)‖ - ‖Phi b 1 N 1‖ ≤ ‖((Ssum b 1 N : ℝ) : ℂ) - Phi b 1 N 1‖ :=
      norm_sub_norm_le _ _
    have hRpos : 0 ≤ 2 * Real.sqrt π * (1 + b⁻¹) * (1 + 11 / 10 * b⁻¹) * Real.exp (-(3 / 16 * b⁻¹)) := by
      positivity
    have h2 : 2 - tailMaj N ≤ ‖((Ssum b 1 N : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      have := abs_le.mp hS
      have hS0 : 0 ≤ Ssum b 1 N := by linarith
      rw [abs_of_nonneg hS0]; linarith
    linarith
  -- the upper side
  have hmain := two_pi_norm_le hb 1
  have hI1 := mixI_le hb hb1 1
  have hI2 := mixI_le hb hb1 (-1)
  rw [Zq_one] at hI1
  rw [Zq_neg_one] at hI2
  set W1 := headWindow b 1
  set W2 := headWindow b (-1)
  have hW1 : 0 ≤ W1 := integral_nonneg fun t => by positivity
  have hW2 : 0 ≤ W2 := integral_nonneg fun t => by positivity
  set q := Real.sqrt (Z1 * Real.sqrt b)
  have hq : 0 < q := Real.sqrt_pos.mpr (mul_pos Z1_pos (Real.sqrt_pos.mpr hb))
  have hsp : 0 < Real.sqrt (π / b) := Real.sqrt_pos.mpr (div_pos Real.pi_pos hb)
  -- `2π ≤ √(π/b) q (√W1 + √W2)`
  have key : 2 * π ≤ Real.sqrt (π / b) * q * (Real.sqrt W1 + Real.sqrt W2) := by
    have := mul_le_mul_of_nonneg_left hlow (by positivity : (0 : ℝ) ≤ 2 * π)
    have h3 : Real.sqrt (π / b) * (mixI b (-1) + mixI b 1)
        ≤ Real.sqrt (π / b) * q * (Real.sqrt W1 + Real.sqrt W2) := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hsp.le
      linarith
    linarith
  -- square: `(2π)² ≤ (π/b) q² (√W1 + √W2)² ≤ (π/b) Z1 √b · 2 (W1 + W2)`
  have hsq1 : (Real.sqrt W1 + Real.sqrt W2) ^ 2 ≤ 2 * (W1 + W2) := by
    nlinarith [sq_nonneg (Real.sqrt W1 - Real.sqrt W2), Real.sq_sqrt hW1, Real.sq_sqrt hW2]
  have hq2 : q ^ 2 = Z1 * Real.sqrt b := Real.sq_sqrt (mul_pos Z1_pos (Real.sqrt_pos.mpr hb)).le
  have hs2 : Real.sqrt (π / b) ^ 2 = π / b := Real.sq_sqrt (by positivity)
  set A := Real.sqrt (π / b) * q with hAdef
  have hA : A ^ 2 = π / b * (Z1 * Real.sqrt b) := by rw [hAdef, mul_pow, hs2, hq2]
  have h0 : 0 ≤ 2 * π := by positivity
  have h7 : (2 * π) ^ 2 ≤ A ^ 2 * (Real.sqrt W1 + Real.sqrt W2) ^ 2 := by
    have := pow_le_pow_left₀ h0 key 2
    calc (2 * π) ^ 2 ≤ (A * (Real.sqrt W1 + Real.sqrt W2)) ^ 2 := this
      _ = A ^ 2 * (Real.sqrt W1 + Real.sqrt W2) ^ 2 := mul_pow _ _ _
  have h8 : (2 * π) ^ 2 ≤ A ^ 2 * (2 * (W1 + W2)) :=
    h7.trans (mul_le_mul_of_nonneg_left hsq1 (sq_nonneg _))
  set s := Real.sqrt b with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr hb
  have hsb : s ^ 2 = b := Real.sq_sqrt hb.le
  have h9 : A ^ 2 * (2 * (W1 + W2)) = 2 * π * (Z1 * (W1 + W2)) / s := by
    rw [hA, ← hsb]; field_simp
  rw [h9, le_div_iff₀ hs] at h8
  have h10 : 2 * π * (2 * π * s) ≤ 2 * π * (Z1 * (W1 + W2)) := by nlinarith
  have h11 : 2 * π * s ≤ Z1 * (W1 + W2) := le_of_mul_le_mul_left h10 (by positivity)
  rw [div_le_iff₀ Z1_pos]
  linarith


/-! ## Consequences for the window rate -/

/-- `e^{c/b} b^{-1/2} → 0` as `b → 0⁺` when `c < 0`. -/
lemma tendsto_exp_div_sqrt {c : ℝ} (hc : c < 0) (K : ℝ) :
    Tendsto (fun b : ℝ => K * Real.exp (c * b⁻¹) * Real.sqrt b⁻¹) (𝓝[>] 0) (𝓝 0) := by
  have hmaj : Tendsto (fun u : ℝ => (|K| + |K| * u + 0 * u ^ 2) * Real.exp (-(-c * u))) atTop (𝓝 0) :=
    tendsto_quad_exp (by linarith) _ _ _
  have hmaj' := hmaj.comp tendsto_inv_nhdsGT_zero
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun b => norm_nonneg _) ?_ hmaj'
  filter_upwards [self_mem_nhdsWithin] with b hb
  have hb' : 0 < b := hb
  have hu : 0 ≤ b⁻¹ := inv_nonneg.mpr hb'.le
  have hs := sqrt_le_one_add hu
  simp only [Function.comp, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have e : -(-c * b⁻¹) = c * b⁻¹ := by ring
  rw [e]
  have hE := Real.exp_pos (c * b⁻¹)
  have hK := abs_nonneg K
  nlinarith [mul_le_mul_of_nonneg_left hs (mul_nonneg hK hE.le)]

/-- **No negative window rate**: `W(c)` fails for every `c < 0`, unconditionally. -/
theorem not_windowRate_of_neg {c : ℝ} (hc : c < 0) : ¬ WindowRate c := by
  intro h
  obtain ⟨C₁, hC₁⟩ := h 1 (by norm_num)
  obtain ⟨C₂, hC₂⟩ := h (-1) (by norm_num)
  obtain ⟨b₀, hb₀, hlow⟩ := headWindow_lower
  have hev : ∀ᶠ b in 𝓝[>] (0 : ℝ),
      (|C₁| + |C₂|) * Real.exp (c * b⁻¹) * Real.sqrt b⁻¹ < 2 * π / Z1 :=
    (tendsto_exp_div_sqrt hc (|C₁| + |C₂|)).eventually (gt_mem_nhds (div_pos (by positivity) Z1_pos))
  have hev2 : ∀ᶠ b in 𝓝[>] (0 : ℝ), b < min b₀ 1 := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min hb₀ one_pos)] with b hb using hb.2
  obtain ⟨b, ⟨h1, h2⟩, hb⟩ := ((hev.and hev2).and self_mem_nhdsWithin).exists
  have hb' : 0 < b := hb
  have hbb₀ : b ≤ b₀ := (h2.trans_le (min_le_left _ _)).le
  have hb1 : b ≤ 1 := (h2.trans_le (min_le_right _ _)).le
  have hL := hlow b hb' hbb₀
  have hW1 := (hC₁ b hb' hb1).trans (mul_le_mul_of_nonneg_right (le_abs_self C₁) (Real.exp_pos _).le)
  have hW2 := (hC₂ b hb' hb1).trans (mul_le_mul_of_nonneg_right (le_abs_self C₂) (Real.exp_pos _).le)
  have hcb : c / b = c * b⁻¹ := div_eq_mul_inv c b
  rw [hcb] at hW1 hW2
  have hs : Real.sqrt b * Real.sqrt b⁻¹ = 1 := by
    rw [← Real.sqrt_mul hb'.le, mul_inv_cancel₀ hb'.ne', Real.sqrt_one]
  have hsp : 0 < Real.sqrt b⁻¹ := Real.sqrt_pos.mpr (inv_pos.mpr hb')
  have key : 2 * π * Real.sqrt b / Z1 ≤ (|C₁| + |C₂|) * Real.exp (c * b⁻¹) := by linarith
  have := mul_le_mul_of_nonneg_right key hsp.le
  rw [div_mul_eq_mul_div, mul_assoc, hs, mul_one] at this
  linarith

/-- Every admissible window rate is nonnegative. -/
theorem windowRate_nonneg {c : ℝ} (h : WindowRate c) : 0 ≤ c :=
  not_lt.mp fun hc => not_windowRate_of_neg hc h

/-- **`D²/2 ≤ c` for every admissible rate `c`**, with no side condition (the `c < 0` case of
`not_windowRate_of_lt` is `not_windowRate_of_neg`). -/
theorem zeroDev_sq_half_le_of_windowRate {c : ℝ} (h : WindowRate c) : zeroDev ^ 2 / 2 ≤ c := by
  by_contra hlt
  push Not at hlt
  exact not_windowRate_of_lt hlt (Or.inl (windowRate_nonneg h)) h

theorem not_windowRate_of_lt' {c : ℝ} (hc : c < zeroDev ^ 2 / 2) : ¬ WindowRate c :=
  fun h => absurd (zeroDev_sq_half_le_of_windowRate h) (not_le.mpr hc)

/-- The infimum over **all** real admissible rates is `windowRateInf` (the restriction `c ≥ 0` in its
definition is automatic). -/
theorem sInf_windowRate_eq : sInf {c : ℝ | WindowRate c} = windowRateInf := by
  unfold windowRateInf
  congr 1
  ext c
  exact ⟨fun h => ⟨windowRate_nonneg h, h⟩, fun h => h.2⟩


/-! ## Symmetry `α ↦ −α` -/

lemma Mpoly_conj (N : ℕ) (w : ℂ) : Mpoly N (conj w) = conj (Mpoly N w) := by
  unfold Mpoly
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, ← Kerr.ZetaConj.natCast_cpow_conj, map_neg]
  simp

/-- The window is even in `α` (`M_N` has real coefficients). -/
theorem headWindow_neg (b α : ℝ) : headWindow b (-α) = headWindow b α := by
  unfold headWindow
  rw [← integral_neg_eq_self]
  congr 1
  funext t
  have e : (((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) = conj (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) := by
    apply Complex.ext <;> simp
  rw [e, Mpoly_conj, Complex.norm_conj]
  congr 2
  ring

/-- **Positive lower bound for the window at one centre**: there is `b₀ > 0` with
`headWindow b 1 ≥ π √b / Z1` for `0 < b ≤ b₀`. -/
theorem headWindow_one_lower :
    ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b ≤ b₀ → π * Real.sqrt b / Z1 ≤ headWindow b 1 := by
  obtain ⟨b₀, hb₀, h⟩ := headWindow_lower
  refine ⟨b₀, hb₀, fun b hb hbb => ?_⟩
  have := h b hb hbb
  rw [headWindow_neg] at this
  have e : 2 * π * Real.sqrt b / Z1 = 2 * (π * Real.sqrt b / Z1) := by ring
  linarith

end FleetWindowLowerBound
