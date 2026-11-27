import FleetHeadContourLine
import RectangleWinding

/-!
# Shifting the head integral from `Re w = 3/2` to the critical line

`f(w) = Φ(w)(−ζ'(w))`, `Φ = LGw · Mpoly` entire. Off `w = 1`,
`f = K + Φ(1)(w−1)^{-2} + Φ'(1)(w−1)^{-1}` with `K = −Φ·zetaReg' + dslope (dslope Φ 1) 1` entire. Hence on
every rectangle around `1` (`rect_shift`): `∮ f = 2πi Φ'(1)` (Cauchy for `K`, an exact derivative for
`(w−1)^{-2}`, the winding number for `(w−1)^{-1}` from `RectangleWinding`).

Letting the height go to infinity (`line_shift`, Gaussian decay of `LGw` against linear growth of `ζ'`):

* `head_eq_critical_line`:
  `head b α M = Φ'(1) + (1/2π) ∫_ℝ LGw(1/2+it) M_M(1/2+it) (−ζ'(1/2+it)) dt`,
  where `LGw(1/2+it) = LG(−it)` and `Φ'(1) = d/dw[LG(1/2−w) M_M(w)]_{w=1}`.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set MeasureTheory intervalIntegral
open scoped Real

namespace FleetHeadContour

open RectangleWinding

/-! ## Rectangle integrals -/

lemma rectInt_eq_zero_of_differentiable {K : ℂ → ℂ} (hK : Differentiable ℂ K) (x₁ x₂ y₁ y₂ : ℝ) :
    rectInt K x₁ x₂ y₁ y₂ = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn K
    ((x₁ : ℂ) + y₁ * I) ((x₂ : ℂ) + y₂ * I) hK.differentiableOn
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero,
    add_zero, add_im, mul_im, zero_add, zero_mul, smul_eq_mul] at h
  unfold rectInt
  exact h

/-- Continuity along the four edges. -/
def EdgeCont (q : ℂ → ℂ) (x₁ x₂ y₁ y₂ : ℝ) : Prop :=
  Continuous (fun x : ℝ => q ((x : ℂ) + y₁ * I)) ∧ Continuous (fun x : ℝ => q ((x : ℂ) + y₂ * I)) ∧
  Continuous (fun y : ℝ => q ((x₂ : ℂ) + y * I)) ∧ Continuous (fun y : ℝ => q ((x₁ : ℂ) + y * I))

lemma edgeCont_of_continuous {q : ℂ → ℂ} (hq : Continuous q) (x₁ x₂ y₁ y₂ : ℝ) :
    EdgeCont q x₁ x₂ y₁ y₂ :=
  ⟨by fun_prop, by fun_prop, by fun_prop, by fun_prop⟩

lemma horiz_ne_one {y : ℝ} (hy : y ≠ 0) (x : ℝ) : (x : ℂ) + y * I ≠ 1 := by
  intro h; apply hy; have := congrArg Complex.im h; simpa using this

lemma edgeCont_of_continuousOn {q : ℂ → ℂ} (hq : ContinuousOn q {s : ℂ | s ≠ 1}) {x₁ x₂ y₁ y₂ : ℝ}
    (hx₁ : x₁ ≠ 1) (hx₂ : x₂ ≠ 1) (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) : EdgeCont q x₁ x₂ y₁ y₂ :=
  ⟨hq.comp_continuous (by fun_prop) (fun x => horiz_ne_one hy₁ x),
   hq.comp_continuous (by fun_prop) (fun x => horiz_ne_one hy₂ x),
   hq.comp_continuous (by fun_prop) (fun y => line_ne_one hx₂ y),
   hq.comp_continuous (by fun_prop) (fun y => line_ne_one hx₁ y)⟩

lemma rectInt_add {f g : ℂ → ℂ} {x₁ x₂ y₁ y₂ : ℝ} (hf : EdgeCont f x₁ x₂ y₁ y₂)
    (hg : EdgeCont g x₁ x₂ y₁ y₂) :
    rectInt (fun s => f s + g s) x₁ x₂ y₁ y₂ = rectInt f x₁ x₂ y₁ y₂ + rectInt g x₁ x₂ y₁ y₂ := by
  unfold rectInt
  rw [integral_add (hf.1.intervalIntegrable _ _) (hg.1.intervalIntegrable _ _),
    integral_add (hf.2.1.intervalIntegrable _ _) (hg.2.1.intervalIntegrable _ _),
    integral_add (hf.2.2.1.intervalIntegrable _ _) (hg.2.2.1.intervalIntegrable _ _),
    integral_add (hf.2.2.2.intervalIntegrable _ _) (hg.2.2.2.intervalIntegrable _ _)]
  ring

lemma rectInt_const_mul (c : ℂ) (f : ℂ → ℂ) (x₁ x₂ y₁ y₂ : ℝ) :
    rectInt (fun s => c * f s) x₁ x₂ y₁ y₂ = c * rectInt f x₁ x₂ y₁ y₂ := by
  unfold rectInt
  simp only [intervalIntegral.integral_const_mul]
  ring

lemma rectInt_congr {f g : ℂ → ℂ} (h : ∀ s, s ≠ 1 → f s = g s) {x₁ x₂ y₁ y₂ : ℝ}
    (hx₁ : x₁ ≠ 1) (hx₂ : x₂ ≠ 1) (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) :
    rectInt f x₁ x₂ y₁ y₂ = rectInt g x₁ x₂ y₁ y₂ := by
  unfold rectInt
  have e1 : (fun x : ℝ => f ((x : ℂ) + y₁ * I)) = fun x : ℝ => g ((x : ℂ) + y₁ * I) :=
    funext fun x => h _ (horiz_ne_one hy₁ x)
  have e2 : (fun x : ℝ => f ((x : ℂ) + y₂ * I)) = fun x : ℝ => g ((x : ℂ) + y₂ * I) :=
    funext fun x => h _ (horiz_ne_one hy₂ x)
  have e3 : (fun y : ℝ => f ((x₂ : ℂ) + y * I)) = fun y : ℝ => g ((x₂ : ℂ) + y * I) :=
    funext fun y => h _ (line_ne_one hx₂ y)
  have e4 : (fun y : ℝ => f ((x₁ : ℂ) + y * I)) = fun y : ℝ => g ((x₁ : ℂ) + y * I) :=
    funext fun y => h _ (line_ne_one hx₁ y)
  rw [e1, e2, e3, e4]

/-! ## `(w−1)^{-2}` is an exact derivative -/

lemma hasDerivAt_neg_inv_sub_one {s : ℂ} (hs : s ≠ 1) :
    HasDerivAt (fun z : ℂ => -(z - 1)⁻¹) ((s - 1) ^ 2)⁻¹ s := by
  have h := (((hasDerivAt_id s).sub_const (1 : ℂ)).inv (sub_ne_zero.mpr hs)).neg
  convert h using 1
  · funext z; simp [Pi.neg_apply, Pi.inv_apply]
  · simp only [id]; ring

lemma continuousOn_inv_sq : ContinuousOn (fun s : ℂ => ((s - 1) ^ 2)⁻¹) {s : ℂ | s ≠ 1} :=
  ContinuousOn.inv₀ (by fun_prop) (fun s hs => pow_ne_zero 2 (sub_ne_zero.mpr hs))

lemma continuousOn_inv_sub : ContinuousOn (fun s : ℂ => (s - 1)⁻¹) {s : ℂ | s ≠ 1} :=
  ContinuousOn.inv₀ (by fun_prop) (fun s hs => sub_ne_zero.mpr hs)

lemma horiz_ftc {y : ℝ} (hy : y ≠ 0) (a b : ℝ) :
    ∫ x in a..b, ((((x : ℂ) + y * I) - 1) ^ 2)⁻¹
      = (-((((b : ℂ) + y * I) - 1))⁻¹) - (-((((a : ℂ) + y * I) - 1))⁻¹) := by
  refine integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => -((((x : ℂ) + y * I) - 1))⁻¹)
    (fun x _ => ?_) ?_
  · have hp : HasDerivAt (fun x : ℝ => (x : ℂ) + y * I) 1 x := by
      simpa using ((hasDerivAt_id x).ofReal_comp).add_const ((y : ℂ) * I)
    have := (hasDerivAt_neg_inv_sub_one (horiz_ne_one hy x)).comp x hp
    convert this using 1 <;> first | rfl | simp
  · exact (continuousOn_inv_sq.comp_continuous (by fun_prop)
      (fun x => horiz_ne_one hy x)).intervalIntegrable _ _

lemma vert_ftc {x : ℝ} (hx : x ≠ 1) (a b : ℝ) :
    I * ∫ y in a..b, ((((x : ℂ) + y * I) - 1) ^ 2)⁻¹
      = (-((((x : ℂ) + b * I) - 1))⁻¹) - (-((((x : ℂ) + a * I) - 1))⁻¹) := by
  rw [← intervalIntegral.integral_const_mul]
  refine integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => -((((x : ℂ) + y * I) - 1))⁻¹)
    (fun y _ => ?_) ?_
  · have hp : HasDerivAt (fun y : ℝ => (x : ℂ) + y * I) I y := by
      simpa using (((hasDerivAt_id y).ofReal_comp).mul_const I).const_add (x : ℂ)
    have := (hasDerivAt_neg_inv_sub_one (line_ne_one hx y)).comp y hp
    convert this using 1 <;> first | rfl | ring
  · exact (continuous_const.mul (continuousOn_inv_sq.comp_continuous (by fun_prop)
      (fun y => line_ne_one hx y))).intervalIntegrable _ _

lemma rectInt_inv_sq {x₁ x₂ y₁ y₂ : ℝ} (hx₁ : x₁ ≠ 1) (hx₂ : x₂ ≠ 1) (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) :
    rectInt (fun s => ((s - 1) ^ 2)⁻¹) x₁ x₂ y₁ y₂ = 0 := by
  unfold rectInt
  rw [horiz_ftc hy₁, horiz_ftc hy₂, vert_ftc hx₂, vert_ftc hx₁]
  ring

/-! ## The finite rectangle -/

/-- The entire part of `Φ(−ζ')`. -/
def Kpart (Φ : ℂ → ℂ) (s : ℂ) : ℂ := -(Φ s * deriv zetaReg s) + dslope (dslope Φ 1) 1 s

lemma differentiable_Kpart {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) : Differentiable ℂ (Kpart Φ) := by
  have hz : Differentiable ℂ (deriv zetaReg) := by
    have h := (contDiff_succ_iff_deriv (n := 1)).mp (differentiable_zetaReg.contDiff (n := 1 + 1))
    exact h.2.2.differentiable (by norm_num)
  have hd : Differentiable ℂ (dslope (dslope Φ 1) 1) := by
    rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem,
      Complex.differentiableOn_dslope Filter.univ_mem]
    exact hΦ.differentiableOn
  unfold Kpart
  exact ((hΦ.mul hz).neg).add hd

lemma decomp {Φ : ℂ → ℂ} {s : ℂ} (hs : s ≠ 1) :
    Φ s * (-deriv riemannZeta s)
      = Kpart Φ s + Φ 1 * ((s - 1) ^ 2)⁻¹ + deriv Φ 1 * (s - 1)⁻¹ := by
  rw [deriv_riemannZeta_eq hs]
  unfold Kpart
  rw [dslope_of_ne _ hs, slope_def_field, dslope_of_ne _ hs, dslope_same, slope_def_field]
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field_simp
  ring

/-- **The rectangle identity**: `∮ Φ(−ζ') = 2πi Φ'(1)` around `1`. -/
theorem rect_shift {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ) {x₁ x₂ y₁ y₂ : ℝ}
    (hx₁ : x₁ < 1) (hx₂ : 1 < x₂) (hy₁ : y₁ < 0) (hy₂ : 0 < y₂) :
    rectInt (fun s => Φ s * (-deriv riemannZeta s)) x₁ x₂ y₁ y₂ = 2 * π * I * deriv Φ 1 := by
  have hx₁' := hx₁.ne; have hx₂' := hx₂.ne'; have hy₁' := hy₁.ne; have hy₂' := hy₂.ne'
  rw [rectInt_congr (fun s hs => decomp (Φ := Φ) hs) hx₁' hx₂' hy₁' hy₂']
  have hK := differentiable_Kpart hΦ
  have cK := edgeCont_of_continuous hK.continuous x₁ x₂ y₁ y₂
  have c2 : EdgeCont (fun s => Φ 1 * ((s - 1) ^ 2)⁻¹) x₁ x₂ y₁ y₂ :=
    edgeCont_of_continuousOn (continuousOn_const.mul continuousOn_inv_sq) hx₁' hx₂' hy₁' hy₂'
  have c1 : EdgeCont (fun s => deriv Φ 1 * (s - 1)⁻¹) x₁ x₂ y₁ y₂ :=
    edgeCont_of_continuousOn (continuousOn_const.mul continuousOn_inv_sub) hx₁' hx₂' hy₁' hy₂'
  have cK2 : EdgeCont (fun s => Kpart Φ s + Φ 1 * ((s - 1) ^ 2)⁻¹) x₁ x₂ y₁ y₂ :=
    ⟨cK.1.add c2.1, cK.2.1.add c2.2.1, cK.2.2.1.add c2.2.2.1, cK.2.2.2.add c2.2.2.2⟩
  rw [rectInt_add cK2 c1, rectInt_add cK c2, rectInt_const_mul, rectInt_const_mul,
    rectInt_eq_zero_of_differentiable hK, rectInt_inv_sq hx₁' hx₂' hy₁' hy₂',
    rect_winding 1 x₁ x₂ y₁ y₂ (by simpa using hx₁) (by simpa using hx₂) (by simpa using hy₁)
      (by simpa using hy₂)]
  ring

/-! ## Letting the height go to infinity -/

/-- **Abstract line shift.** If `Φ(−ζ')` is integrable on `Re = 1/2` and `Re = 3/2` and its horizontal
integrals over `[1/2, 3/2]` at heights `±T` tend to `0`, then
`∫ f(3/2 + iy) dy − ∫ f(1/2 + iy) dy = 2π Φ'(1)`. -/
theorem line_shift {Φ : ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    (h3 : Integrable (fun y : ℝ => Φ (((3 / 2 : ℝ) : ℂ) + y * I) * (-deriv riemannZeta (((3 / 2 : ℝ) : ℂ) + y * I))))
    (h1 : Integrable (fun y : ℝ => Φ (((1 / 2 : ℝ) : ℂ) + y * I) * (-deriv riemannZeta (((1 / 2 : ℝ) : ℂ) + y * I))))
    (htop : Tendsto (fun T : ℝ => ∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ),
      Φ ((x : ℂ) + T * I) * (-deriv riemannZeta ((x : ℂ) + T * I))) atTop (𝓝 0))
    (hbot : Tendsto (fun T : ℝ => ∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ),
      Φ ((x : ℂ) + ((-T : ℝ) : ℂ) * I) * (-deriv riemannZeta ((x : ℂ) + ((-T : ℝ) : ℂ) * I))) atTop (𝓝 0)) :
    (∫ y : ℝ, Φ (((3 / 2 : ℝ) : ℂ) + y * I) * (-deriv riemannZeta (((3 / 2 : ℝ) : ℂ) + y * I)))
      - (∫ y : ℝ, Φ (((1 / 2 : ℝ) : ℂ) + y * I) * (-deriv riemannZeta (((1 / 2 : ℝ) : ℂ) + y * I)))
      = 2 * π * deriv Φ 1 := by
  set f : ℂ → ℂ := fun s => Φ s * (-deriv riemannZeta s) with hf
  have hV3 := intervalIntegral_tendsto_integral h3 tendsto_neg_atTop_atBot tendsto_id
  have hV1 := intervalIntegral_tendsto_integral h1 tendsto_neg_atTop_atBot tendsto_id
  have hlim : Tendsto (fun T : ℝ => rectInt f (1 / 2) (3 / 2) (-T) T) atTop
      (𝓝 (0 - 0 + I * (∫ y : ℝ, f (((3 / 2 : ℝ) : ℂ) + y * I))
        - I * (∫ y : ℝ, f (((1 / 2 : ℝ) : ℂ) + y * I)))) := by
    unfold rectInt
    exact ((hbot.sub htop).add (hV3.const_mul I)).sub (hV1.const_mul I)
  have hconst : ∀ᶠ T : ℝ in atTop, rectInt f (1 / 2) (3 / 2) (-T) T = 2 * π * I * deriv Φ 1 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact rect_shift hΦ (by norm_num) (by norm_num) (by linarith) hT
  have heq := tendsto_nhds_unique (hlim.congr' hconst) tendsto_const_nhds
  have hI : I ≠ 0 := I_ne_zero
  have : I * ((∫ y : ℝ, f (((3 / 2 : ℝ) : ℂ) + y * I)) - (∫ y : ℝ, f (((1 / 2 : ℝ) : ℂ) + y * I)))
      = I * (2 * π * deriv Φ 1) := by
    rw [mul_sub]; linear_combination heq
  exact mul_left_cancel₀ hI this

/-! ## Decay of the horizontal sides -/

lemma tendsto_lin_exp {k : ℝ} (hk : 0 < k) (A B : ℝ) :
    Tendsto (fun T : ℝ => (A + B * T) * Real.exp (-(k * T))) atTop (𝓝 0) := by
  have h0 := (isLittleO_pow_exp_pos_mul_atTop 0 hk).tendsto_div_nhds_zero
  have h1 := (isLittleO_pow_exp_pos_mul_atTop 1 hk).tendsto_div_nhds_zero
  have h := (h0.const_mul A).add (h1.const_mul B)
  simp only [mul_zero, add_zero] at h
  refine h.congr fun T => ?_
  rw [Real.exp_neg]
  simp only [pow_zero, pow_one]
  ring

lemma gauss_le_exp_lin {b : ℝ} (hb : 0 < b) (β : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    Real.exp (-(T - β) ^ 2 / (4 * b)) ≤ Real.exp (β ^ 2 / (4 * b)) * Real.exp (-(1 / (8 * b) * T)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : (T - β) ^ 2 ≥ T ^ 2 / 2 - β ^ 2 := by nlinarith [sq_nonneg (T - 2 * β)]
  have h2 : T ^ 2 ≥ T := by nlinarith
  have e : β ^ 2 / (4 * b) + -(1 / (8 * b) * T) = (2 * β ^ 2 - T) / (8 * b) := by
    field_simp; ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

lemma tendsto_lin_gauss {b : ℝ} (hb : 0 < b) (β A B : ℝ) :
    Tendsto (fun T : ℝ => (A + B * T) * Real.exp (-(T - β) ^ 2 / (4 * b))) atTop (𝓝 0) := by
  have hk : 0 < 1 / (8 * b) := by positivity
  have hmaj := (tendsto_lin_exp hk (|A|) (|B|)).const_mul (Real.exp (β ^ 2 / (4 * b)))
  rw [mul_zero] at hmaj
  have habs : Tendsto (fun T : ℝ => |(A + B * T) * Real.exp (-(T - β) ^ 2 / (4 * b))|) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun T => abs_nonneg _) ?_ hmaj
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hAB : |A + B * T| ≤ |A| + |B| * T := by
      calc |A + B * T| ≤ |A| + |B * T| := abs_add_le _ _
        _ = |A| + |B| * T := by rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < T)]
    calc |A + B * T| * Real.exp (-(T - β) ^ 2 / (4 * b))
        ≤ (|A| + |B| * T) * (Real.exp (β ^ 2 / (4 * b)) * Real.exp (-(1 / (8 * b) * T))) :=
          mul_le_mul hAB (gauss_le_exp_lin hb β hT) (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr habs

/-- The pointwise bound on the strip `1/2 ≤ x ≤ 3/2`, `|y| ≥ 1`. -/
lemma norm_f_strip_le {b : ℝ} (hb : 0 < b) (α : ℝ) (M : ℕ) {x y : ℝ} (hx : x ∈ Set.uIcc (1 / 2 : ℝ) (3 / 2))
    (hy : 1 ≤ |y|) :
    ‖Phi b α M ((x : ℂ) + y * I) * (-deriv riemannZeta ((x : ℂ) + y * I))‖
      ≤ Real.sqrt (π / b) * Real.exp (1 / (4 * b)) * (M + 1) * (36 + 20 * |y|) *
        (Real.exp (-(y + α) ^ 2 / (4 * b)) + Real.exp (-(y - α) ^ 2 / (4 * b))) := by
  rw [Set.uIcc_of_le (by norm_num)] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hre : ((x : ℂ) + y * I).re = x := by simp
  have hne : (x : ℂ) + y * I ≠ 1 := by
    intro h; have := congrArg Complex.im h; simp at this; rw [this] at hy; norm_num at hy
  have hL := norm_LGw_le b α x y
  have hM := norm_Mpoly_le M (w := (x : ℂ) + y * I) (by rw [hre]; linarith)
  have hZ := norm_deriv_zeta_le (s := (x : ℂ) + y * I) (by rw [hre]; exact hx1) hne
  have hs1 : 1 ≤ ‖(x : ℂ) + y * I - 1‖ := by
    have := Complex.abs_im_le_norm ((x : ℂ) + y * I - 1)
    simp at this; linarith
  have hinv : (‖(x : ℂ) + y * I - 1‖ ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  have hsn : ‖(x : ℂ) + y * I‖ ≤ 3 / 2 + |y| := by
    calc ‖(x : ℂ) + y * I‖ ≤ ‖(x : ℂ)‖ + ‖(y : ℂ) * I‖ := norm_add_le _ _
      _ = |x| + |y| := by simp
      _ ≤ 3 / 2 + |y| := by rw [abs_of_pos (by linarith)]; linarith
  have hE : Real.exp ((x - 1 / 2) ^ 2 / (4 * b)) ≤ Real.exp (1 / (4 * b)) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have hZ' : ‖deriv riemannZeta ((x : ℂ) + y * I)‖ ≤ 36 + 20 * |y| := by linarith
  have hG : 0 ≤ Real.exp (-(y + α) ^ 2 / (4 * b)) + Real.exp (-(y - α) ^ 2 / (4 * b)) := by positivity
  unfold Phi
  rw [norm_mul, norm_mul, norm_neg]
  calc ‖LGw b α ((x : ℂ) + y * I)‖ * ‖Mpoly M ((x : ℂ) + y * I)‖ * ‖deriv riemannZeta ((x : ℂ) + y * I)‖
      ≤ (Real.sqrt (π / b) * Real.exp (1 / (4 * b)) *
          (Real.exp (-(y + α) ^ 2 / (4 * b)) + Real.exp (-(y - α) ^ 2 / (4 * b)))) * (M + 1)
        * (36 + 20 * |y|) := by
        gcongr
        calc ‖LGw b α ((x : ℂ) + y * I)‖ ≤ _ := hL
          _ ≤ _ := by gcongr
    _ = _ := by ring

lemma tendsto_horizontal {b : ℝ} (hb : 0 < b) (α : ℝ) (M : ℕ) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    Tendsto (fun T : ℝ => ∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ),
      Phi b α M ((x : ℂ) + ((σ * T : ℝ) : ℂ) * I)
        * (-deriv riemannZeta ((x : ℂ) + ((σ * T : ℝ) : ℂ) * I))) atTop (𝓝 0) := by
  set C := Real.sqrt (π / b) * Real.exp (1 / (4 * b)) * (M + 1) with hC
  have hmaj : Tendsto (fun T : ℝ => C * ((36 + 20 * T) * Real.exp (-(T - (-α)) ^ 2 / (4 * b))
      + (36 + 20 * T) * Real.exp (-(T - α) ^ 2 / (4 * b)))) atTop (𝓝 0) := by
    have := ((tendsto_lin_gauss hb (-α) 36 20).add (tendsto_lin_gauss hb α 36 20)).const_mul C
    simpa using this
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hmaj
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hσT : |σ * T| = T := by
    rcases hσ with rfl | rfl <;> simp [abs_of_pos (by linarith : (0 : ℝ) < T)]
  have hb' := intervalIntegral.norm_integral_le_of_norm_le_const (a := (1 / 2 : ℝ)) (b := 3 / 2)
    (C := C * (36 + 20 * T) * (Real.exp (-((σ * T) + α) ^ 2 / (4 * b))
      + Real.exp (-((σ * T) - α) ^ 2 / (4 * b))))
    (f := fun x : ℝ => Phi b α M ((x : ℂ) + ((σ * T : ℝ) : ℂ) * I)
        * (-deriv riemannZeta ((x : ℂ) + ((σ * T : ℝ) : ℂ) * I)))
    (fun x hx => by
      have := norm_f_strip_le hb α M (x := x) (y := σ * T) (Set.uIoc_subset_uIcc hx)
        (by rw [hσT]; exact hT)
      rw [hσT] at this
      simpa [hC, mul_assoc] using this)
  refine hb'.trans (le_of_eq ?_)
  have hsym : Real.exp (-((σ * T) + α) ^ 2 / (4 * b)) + Real.exp (-((σ * T) - α) ^ 2 / (4 * b))
      = Real.exp (-(T - (-α)) ^ 2 / (4 * b)) + Real.exp (-(T - α) ^ 2 / (4 * b)) := by
    rcases hσ with rfl | rfl
    · ring_nf
    · ring_nf; try rw [add_comm]
  rw [hsym]
  norm_num
  ring

/-! ## The critical-line form of the head -/

lemma integrable_f_line {b : ℝ} (hb : 0 < b) (α : ℝ) (M : ℕ) {x : ℝ} (hx : 1 / 2 ≤ x) (hx1 : x ≠ 1) :
    Integrable (fun y : ℝ => Phi b α M ((x : ℂ) + y * I) * (-deriv riemannZeta ((x : ℂ) + y * I))) := by
  have h := integrable_line hb α hx hx1 (h := fun t => Mpoly M ((x : ℂ) + t * I))
    ((differentiable_Mpoly M).continuous.comp (continuous_line x)) (H := M + 1)
    (fun t => norm_Mpoly_le M (by simp; linarith))
  simpa [Phi] using h

/-- **The exact contour identity (3)**:
`head b α M = Φ'(1) + (1/2π) ∫_ℝ LGw(1/2+it) M_M(1/2+it) (−ζ'(1/2+it)) dt`,
with `Φ = LGw · Mpoly`, i.e. `LGw(1/2+it) = LG(−it)` and `Φ'(1) = d/dw[LG(1/2−w) M_M(w)]_{w=1}`. -/
theorem head_eq_critical_line {b : ℝ} (hb : 0 < b) (α : ℝ) (M : ℕ) :
    ((FleetFiniteHeadRH.head b α M : ℝ) : ℂ) = deriv (Phi b α M) 1 + (1 / (2 * π) : ℂ) *
      ∫ t : ℝ, LGw b α (((1 / 2 : ℝ) : ℂ) + t * I) * Mpoly M (((1 / 2 : ℝ) : ℂ) + t * I)
        * (-deriv riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)) := by
  have hshift := line_shift (differentiable_Phi b α M)
    (integrable_f_line hb α M (by norm_num) (by norm_num))
    (integrable_f_line hb α M (by norm_num) (by norm_num))
    (by simpa using tendsto_horizontal hb α M 1 (Or.inl rfl))
    (by simpa using tendsto_horizontal hb α M (-1) (Or.inr rfl))
  rw [head_eq_line_integral hb α M (c := 3 / 2) (by norm_num)]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e : ∫ t : ℝ, Phi b α M (((3 / 2 : ℝ) : ℂ) + t * I) * (-deriv riemannZeta (((3 / 2 : ℝ) : ℂ) + t * I))
      = (∫ t : ℝ, Phi b α M (((1 / 2 : ℝ) : ℂ) + t * I) * (-deriv riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)))
        + 2 * π * deriv (Phi b α M) 1 := by
    rw [← hshift]; ring
  rw [e]
  simp only [Phi]
  rw [mul_add, add_comm]
  congr 1
  field_simp

end FleetHeadContour
