import FleetSmoothWindowStripRep

/-!
# Moving the `w`-line of `I_x`: the contour identities

`f_x(w) = Φ_x(w)(−ζ'(w))`, `Φ_x(w) = LG(1/2 − w) P_b(w − x)` (entire). Then `I_x = ∫ f_x(2 + it) dt`
(`Ix_eq`), and:

* `Ix_eq_left` : for `1/4 + r ≤ a < 1`, `I_x = ∫ f_x(a + it) dt + 2π Φ_x'(1)`.
* `Ix_eq_right`: for `a > 1`, `I_x = ∫ f_x(a + it) dt`.
* `Ix_eq_bump` : for `a₁ ≤ a₂`, `a₂ > 1`, `τ > 0`, and `a₁ ≥ 1/4 + r`:
  `I_x = ∫_{t>τ} f_x(a₁+it) + ∫_{t≤−τ} f_x(a₁+it) + ∫_{−τ}^{τ} f_x(a₂+it) + i∫_{a₁}^{a₂} f_x(σ+iτ) − i∫_{a₁}^{a₂} f_x(σ−iτ)`.

Bounds used: `‖ζ'(s)‖ ≤ ‖s−1‖^{-2} + 5(‖s‖ + r)/r` on `Re s ≥ 1/4 + r` (`norm_deriv_zeta_le_r`, Cauchy estimate
on a circle of radius `r`), and `‖ζ'(s)‖ ≤ Λ₁(Re s) = Σ log n · n^{-Re s}` on `Re s > 1`.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace FleetSmoothWindow

open FleetLandauTransfer FleetHeadContour

/-- `Φ_x(w) = LG(1/2 − w) P_b(w − x)`. -/
def Phix (b α x : ℝ) (u : ℂ) : ℂ := LGw b α u * Psm b (u - x)

/-- `f_x(w) = Φ_x(w)(−ζ'(w))`. -/
def fx (b α x : ℝ) (u : ℂ) : ℂ := Phix b α x u * (-deriv riemannZeta u)

theorem differentiable_Phix {b : ℝ} (hb : 0 < b) (α x : ℝ) : Differentiable ℂ (Phix b α x) :=
  (differentiable_LGw b α).mul ((differentiable_Psm hb).comp (differentiable_id.sub_const _))

lemma differentiable_deriv_zetaReg : Differentiable ℂ (deriv zetaReg) := by
  have h := (contDiff_succ_iff_deriv (n := 1)).mp (differentiable_zetaReg.contDiff (n := 1 + 1))
  exact h.2.2.differentiable (by norm_num)

lemma differentiableAt_deriv_zeta {s : ℂ} (hs : s ≠ 1) : DifferentiableAt ℂ (deriv riemannZeta) s := by
  have hev : (fun z : ℂ => deriv zetaReg z - ((z - 1) ^ 2)⁻¹) =ᶠ[𝓝 s] deriv riemannZeta := by
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz
    exact (deriv_riemannZeta_eq hz).symm
  have hd : DifferentiableAt ℂ (fun z : ℂ => deriv zetaReg z - ((z - 1) ^ 2)⁻¹) s :=
    (differentiable_deriv_zetaReg s).sub
      (((differentiableAt_id.sub_const 1).pow 2).inv (pow_ne_zero 2 (sub_ne_zero.mpr hs)))
  exact hd.congr_of_eventuallyEq hev.symm

theorem differentiableAt_fx {b : ℝ} (hb : 0 < b) (α x : ℝ) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (fx b α x) s :=
  (differentiable_Phix hb α x s).mul (differentiableAt_deriv_zeta hs).neg

lemma continuousOn_fx {b : ℝ} (hb : 0 < b) (α x : ℝ) : ContinuousOn (fx b α x) {s : ℂ | s ≠ 1} :=
  fun _ hs => (differentiableAt_fx hb α x hs).continuousAt.continuousWithinAt

lemma continuous_fx_line {b : ℝ} (hb : 0 < b) (α x : ℝ) {a : ℝ} (ha : a ≠ 1) :
    Continuous (fun t : ℝ => fx b α x ((a : ℂ) + t * I)) :=
  (continuousOn_fx hb α x).comp_continuous (continuous_line a) (fun t => line_ne_one ha t)

lemma continuous_fx_horiz {b : ℝ} (hb : 0 < b) (α x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    Continuous (fun σ : ℝ => fx b α x ((σ : ℂ) + y * I)) :=
  (continuousOn_fx hb α x).comp_continuous (by fun_prop) (fun σ => horiz_ne_one hy σ)

lemma Ix_eq {b : ℝ} (α x : ℝ) : Ix b α x = ∫ t : ℝ, fx b α x (((2 : ℝ) : ℂ) + t * I) := by
  unfold Ix fx Phix Fline
  congr 1; funext t; ring

/-! ## Bounds for `ζ'` -/

/-- **Cauchy estimate with radius `r`**: `‖ζ'(s)‖ ≤ ‖s−1‖^{-2} + 5(‖s‖ + r)/r` on `Re s ≥ 1/4 + r`, `s ≠ 1`. -/
theorem norm_deriv_zeta_le_r {r : ℝ} (hr : 0 < r) {s : ℂ} (hs : 1 / 4 + r ≤ s.re) (hs1 : s ≠ 1) :
    ‖deriv riemannZeta s‖ ≤ (‖s - 1‖ ^ 2)⁻¹ + 5 * (‖s‖ + r) / r := by
  have hreg : ‖deriv zetaReg s‖ ≤ 5 * (‖s‖ + r) / r := by
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := s) (R := r)
      (C := 5 * (‖s‖ + r)) (f := zetaReg) hr differentiable_zetaReg.diffContOnCl ?_
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    have hre : |(z - s).re| ≤ r := by rw [← hz]; exact Complex.abs_re_le_norm _
    have hzre : 1 / 4 ≤ z.re := by rw [sub_re] at hre; linarith [(abs_le.mp hre).1]
    have hzn : ‖z‖ ≤ ‖s‖ + r := by
      calc ‖z‖ = ‖s + (z - s)‖ := by ring_nf
        _ ≤ ‖s‖ + ‖z - s‖ := norm_add_le _ _
        _ = ‖s‖ + r := by rw [hz]
    calc ‖zetaReg z‖ ≤ 5 * ‖z‖ := norm_zetaReg_le hzre
      _ ≤ 5 * (‖s‖ + r) := by linarith
  rw [deriv_riemannZeta_eq hs1]
  calc ‖deriv zetaReg s - ((s - 1) ^ 2)⁻¹‖ ≤ ‖deriv zetaReg s‖ + ‖((s - 1) ^ 2)⁻¹‖ := norm_sub_le _ _
    _ ≤ 5 * (‖s‖ + r) / r + (‖s - 1‖ ^ 2)⁻¹ := by rw [norm_inv, norm_pow]; linarith
    _ = _ := by ring

/-- The linear form: if `d ≤ ‖s − 1‖` then `‖ζ'(s)‖ ≤ (d^{-2} + 5(|Re s| + r)/r) + (5/r)|Im s|`. -/
theorem norm_deriv_zeta_le_lin {r d : ℝ} (hr : 0 < r) (hd : 0 < d) {s : ℂ} (hs : 1 / 4 + r ≤ s.re)
    (hsd : d ≤ ‖s - 1‖) :
    ‖deriv riemannZeta s‖ ≤ ((d ^ 2)⁻¹ + 5 * (|s.re| + r) / r) + (5 / r) * |s.im| := by
  have hs1 : s ≠ 1 := by intro h; rw [h, sub_self, norm_zero] at hsd; linarith
  have h := norm_deriv_zeta_le_r hr hs hs1
  have h1 : (‖s - 1‖ ^ 2)⁻¹ ≤ (d ^ 2)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_left₀ hd.le hsd 2)
  have h2 : ‖s‖ ≤ |s.re| + |s.im| := by
    calc ‖s‖ = ‖(s.re : ℂ) + (s.im : ℂ) * I‖ := by rw [re_add_im]
      _ ≤ ‖(s.re : ℂ)‖ + ‖(s.im : ℂ) * I‖ := norm_add_le _ _
      _ = |s.re| + |s.im| := by simp
  have h3 : 5 * (‖s‖ + r) / r ≤ 5 * (|s.re| + r) / r + (5 / r) * |s.im| := by
    rw [show 5 * (|s.re| + r) / r + (5 / r) * |s.im| = 5 * (|s.re| + |s.im| + r) / r by field_simp; ring]
    gcongr
  linarith

/-- `Λ₁(σ) = Σ_n log(n+2) (n+2)^{-σ}`. -/
def Lam1 (σ : ℝ) : ℝ := ∑' n : ℕ, Real.log ((n : ℝ) + 2) * ((n : ℝ) + 2) ^ (-σ)

theorem norm_deriv_zeta_le_Lam1 {s : ℂ} (hs : 1 < s.re) : ‖deriv riemannZeta s‖ ≤ Lam1 s.re := by
  rw [← norm_neg, neg_deriv_zeta_eq_tsum hs]
  have hsum := summable_log_rpow hs
  have hn : ∀ n : ℕ, ‖(Real.log ((n : ℝ) + 2) : ℂ) * ((((n : ℝ) + 2 : ℝ)) : ℂ) ^ (-s)‖
      = Real.log ((n : ℝ) + 2) * ((n : ℝ) + 2) ^ (-s.re) := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])),
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), neg_re]
  unfold Lam1
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr hn))
  exact hsum.congr fun n => (hn n).symm

lemma Lam1_le {σ₀ σ : ℝ} (hσ₀ : 1 < σ₀) (hσ : σ₀ ≤ σ) :
    Lam1 σ ≤ Lam1 σ₀ * (2 : ℝ) ^ (σ₀ - σ) := by
  unfold Lam1
  rw [← tsum_mul_right]
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_log_rpow (by linarith))
    ((summable_log_rpow hσ₀).mul_right _)
  have hn2 : (2 : ℝ) ≤ n + 2 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hL : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith)
  have e : ((n : ℝ) + 2) ^ (-σ) = ((n : ℝ) + 2) ^ (-σ₀) * ((n : ℝ) + 2) ^ (σ₀ - σ) := by
    rw [← Real.rpow_add (by linarith)]; congr 1; ring
  rw [e]
  have h1 : ((n : ℝ) + 2) ^ (σ₀ - σ) ≤ (2 : ℝ) ^ (σ₀ - σ) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hn2 (by linarith)
  have h2 : 0 ≤ ((n : ℝ) + 2) ^ (-σ₀) := by positivity
  calc Real.log ((n : ℝ) + 2) * (((n : ℝ) + 2) ^ (-σ₀) * ((n : ℝ) + 2) ^ (σ₀ - σ))
      ≤ Real.log ((n : ℝ) + 2) * (((n : ℝ) + 2) ^ (-σ₀) * (2 : ℝ) ^ (σ₀ - σ)) := by gcongr
    _ = _ := by ring

lemma Lam1_nonneg (σ : ℝ) : 0 ≤ Lam1 σ :=
  tsum_nonneg fun n => mul_nonneg (Real.log_nonneg (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]))
    (by positivity)

/-! ## Pointwise bounds for `f_x` -/

lemma norm_Phix_le {b : ℝ} (hb : 0 < b) (α x : ℝ) {η : ℝ} (hη : 0 < η) (σ y : ℝ) :
    ‖Phix b α x ((σ : ℂ) + y * I)‖ ≤ Real.sqrt (π / b) * Real.exp ((σ - 1 / 2) ^ 2 / (4 * b)) *
      (Real.exp (-(y + α) ^ 2 / (4 * b)) + Real.exp (-(y - α) ^ 2 / (4 * b)))
      * (Sz η * Real.exp (max 0 (1 + η - (σ - x)) ^ 2 / (4 * b))) := by
  unfold Phix
  rw [norm_mul]
  have h1 := norm_LGw_le b α σ y
  have h2 := norm_Psm_le hb hη ((σ : ℂ) + y * I - x)
  have hre : ((σ : ℂ) + y * I - x).re = σ - x := by simp
  rw [hre] at h2
  gcongr

/-- A strip bound with `ζ'` of linear growth: for `a₁ ≤ σ ≤ a₂`, `1/4 + r ≤ a₁`, `d ≤ ‖σ + iy − 1‖`. -/
lemma norm_fx_le {b : ℝ} (hb : 0 < b) (α x : ℝ) {η r d : ℝ} (hη : 0 < η) (hr : 0 < r) (hd : 0 < d)
    {a₁ a₂ σ y : ℝ} (ha₁ : 1 / 4 + r ≤ a₁) (hσ₁ : a₁ ≤ σ) (hσ₂ : σ ≤ a₂)
    (hsd : d ≤ ‖(σ : ℂ) + y * I - 1‖) :
    ‖fx b α x ((σ : ℂ) + y * I)‖ ≤
      (Real.sqrt (π / b) * Real.exp (((|a₁| + |a₂| + 1) ^ 2) / (4 * b))
        * (Sz η * Real.exp (max 0 (1 + η - (a₁ - x)) ^ 2 / (4 * b))))
      * (((d ^ 2)⁻¹ + 5 * (|a₁| + |a₂| + r) / r) + (5 / r) * |y|)
      * (Real.exp (-(y + α) ^ 2 / (4 * b)) + Real.exp (-(y - α) ^ 2 / (4 * b))) := by
  unfold fx
  rw [norm_mul, norm_neg]
  have h1 := norm_Phix_le hb α x hη σ y
  have hre : ((σ : ℂ) + y * I).re = σ := by simp
  have him : ((σ : ℂ) + y * I).im = y := by simp
  have h2 := norm_deriv_zeta_le_lin hr hd (s := (σ : ℂ) + y * I) (by rw [hre]; linarith) hsd
  rw [hre, him] at h2
  have hS := Sz_nonneg η
  have hσabs : |σ| ≤ |a₁| + |a₂| := by
    rw [abs_le]; constructor <;> cases abs_cases a₁ <;> cases abs_cases a₂ <;> linarith
  have e1 : (σ - 1 / 2) ^ 2 ≤ (|a₁| + |a₂| + 1) ^ 2 := by
    have : |σ - 1 / 2| ≤ |a₁| + |a₂| + 1 := by
      calc |σ - 1 / 2| ≤ |σ| + |1 / 2| := abs_sub _ _
        _ ≤ _ := by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; linarith
    calc (σ - 1 / 2) ^ 2 = |σ - 1 / 2| ^ 2 := (sq_abs _).symm
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) this 2
  have e2 : max 0 (1 + η - (σ - x)) ≤ max 0 (1 + η - (a₁ - x)) := max_le_max le_rfl (by linarith)
  have e3 : max 0 (1 + η - (σ - x)) ^ 2 ≤ max 0 (1 + η - (a₁ - x)) ^ 2 :=
    pow_le_pow_left₀ (le_max_left _ _) e2 2
  have h2' : ‖deriv riemannZeta ((σ : ℂ) + y * I)‖
      ≤ ((d ^ 2)⁻¹ + 5 * (|a₁| + |a₂| + r) / r) + (5 / r) * |y| := by
    refine h2.trans ?_
    have : 5 * (|σ| + r) / r ≤ 5 * (|a₁| + |a₂| + r) / r := by gcongr
    linarith
  have hG : 0 ≤ Real.exp (-(y + α) ^ 2 / (4 * b)) + Real.exp (-(y - α) ^ 2 / (4 * b)) := by positivity
  calc ‖Phix b α x ((σ : ℂ) + y * I)‖ * ‖deriv riemannZeta ((σ : ℂ) + y * I)‖
      ≤ (Real.sqrt (π / b) * Real.exp ((σ - 1 / 2) ^ 2 / (4 * b)) *
          (Real.exp (-(y + α) ^ 2 / (4 * b)) + Real.exp (-(y - α) ^ 2 / (4 * b)))
          * (Sz η * Real.exp (max 0 (1 + η - (σ - x)) ^ 2 / (4 * b))))
        * (((d ^ 2)⁻¹ + 5 * (|a₁| + |a₂| + r) / r) + (5 / r) * |y|) :=
        mul_le_mul h1 h2' (norm_nonneg _) (by positivity)
    _ ≤ (Real.sqrt (π / b) * Real.exp (((|a₁| + |a₂| + 1) ^ 2) / (4 * b)) *
          (Real.exp (-(y + α) ^ 2 / (4 * b)) + Real.exp (-(y - α) ^ 2 / (4 * b)))
          * (Sz η * Real.exp (max 0 (1 + η - (a₁ - x)) ^ 2 / (4 * b))))
        * (((d ^ 2)⁻¹ + 5 * (|a₁| + |a₂| + r) / r) + (5 / r) * |y|) := by
        have : 0 ≤ ((d ^ 2)⁻¹ + 5 * (|a₁| + |a₂| + r) / r) + (5 / r) * |y| := by positivity
        gcongr
    _ = _ := by ring

/-- Integrability of `f_x` on a vertical line `Re = a`, `1/4 + r ≤ a`, `a ≠ 1`. -/
lemma integrable_fx_line {b : ℝ} (hb : 0 < b) (α x : ℝ) {r : ℝ} (hr : 0 < r) {a : ℝ}
    (ha : 1 / 4 + r ≤ a) (ha1 : a ≠ 1) :
    Integrable (fun t : ℝ => fx b α x ((a : ℂ) + t * I)) := by
  have hd : 0 < |a - 1| := abs_pos.mpr (sub_ne_zero.mpr ha1)
  set K := Real.sqrt (π / b) * Real.exp (((|a| + |a| + 1) ^ 2) / (4 * b))
    * (Sz 1 * Real.exp (max 0 (1 + 1 - (a - x)) ^ 2 / (4 * b)))
  have hK : 0 ≤ K := by have := Sz_nonneg 1; positivity
  refine integrable_of_gauss_bound hb α (K * ((|a - 1| ^ 2)⁻¹ + 5 * (|a| + |a| + r) / r)) (K * (5 / r))
    (continuous_fx_line hb α x ha1) fun t => ?_
  have hsd : |a - 1| ≤ ‖(a : ℂ) + t * I - 1‖ := by
    have := Complex.abs_re_le_norm ((a : ℂ) + t * I - 1)
    simpa using this
  refine (norm_fx_le hb α x one_pos hr hd ha le_rfl le_rfl hsd).trans (le_of_eq ?_)
  ring

lemma tendsto_horiz_fx {b : ℝ} (hb : 0 < b) (α x : ℝ) {r : ℝ} (hr : 0 < r) {a₁ a₂ : ℝ}
    (ha₁ : 1 / 4 + r ≤ a₁) (ha : a₁ ≤ a₂) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    Tendsto (fun T : ℝ => ∫ s in a₁..a₂, fx b α x ((s : ℂ) + ((σ * T : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
  set K := Real.sqrt (π / b) * Real.exp (((|a₁| + |a₂| + 1) ^ 2) / (4 * b))
    * (Sz 1 * Real.exp (max 0 (1 + 1 - (a₁ - x)) ^ 2 / (4 * b)))
  have hK : 0 ≤ K := by have := Sz_nonneg 1; positivity
  set A := K * ((1 ^ 2)⁻¹ + 5 * (|a₁| + |a₂| + r) / r)
  set B := K * (5 / r)
  have hlim : Tendsto (fun T : ℝ => (A + B * T) * Real.exp (-(T - (-α)) ^ 2 / (4 * b))
      + (A + B * T) * Real.exp (-(T - α) ^ 2 / (4 * b))) atTop (𝓝 0) := by
    simpa using (tendsto_lin_gauss hb (-α) A B).add (tendsto_lin_gauss hb α A B)
  refine tendsto_horiz_of_bound hlim fun T hT s hs => ?_
  rw [uIcc_of_le ha] at hs
  have hσT : |σ * T| = T := by
    rcases hσ with rfl | rfl <;> simp [abs_of_pos (by linarith : (0 : ℝ) < T)]
  have hsd : (1 : ℝ) ≤ ‖(s : ℂ) + ((σ * T : ℝ) : ℂ) * I - 1‖ := by
    have := Complex.abs_im_le_norm ((s : ℂ) + ((σ * T : ℝ) : ℂ) * I - 1)
    simp only [sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
      zero_add, one_im, sub_zero] at this
    rw [hσT] at this; linarith
  refine (norm_fx_le hb α x one_pos hr one_pos ha₁ hs.1 hs.2 hsd).trans (le_of_eq ?_)
  rw [hσT]
  have hsym : Real.exp (-(σ * T + α) ^ 2 / (4 * b)) + Real.exp (-(σ * T - α) ^ 2 / (4 * b))
      = Real.exp (-(T - (-α)) ^ 2 / (4 * b)) + Real.exp (-(T - α) ^ 2 / (4 * b)) := by
    rcases hσ with rfl | rfl
    · ring_nf
    · ring_nf; try rw [add_comm]
  rw [hsym]
  simp only [A, B]
  ring

/-! ## The contour identities for `I_x` -/

/-- **Left of the pole**: `I_x = ∫ f_x(a + it) dt + 2π Φ_x'(1)` for `1/4 + r ≤ a < 1`. -/
theorem Ix_eq_left {b : ℝ} (hb : 0 < b) (α x : ℝ) {r : ℝ} (hr : 0 < r) {a : ℝ} (ha : 1 / 4 + r ≤ a)
    (ha1 : a < 1) :
    Ix b α x = (∫ t : ℝ, fx b α x ((a : ℂ) + t * I)) + 2 * π * deriv (Phix b α x) 1 := by
  rw [Ix_eq]
  have h := line_shift_one (differentiable_Phix hb α x) ha1 (by norm_num : (1 : ℝ) < 2)
    (integrable_fx_line hb α x hr ha ha1.ne) (integrable_fx_line hb α x hr (by linarith) (by norm_num))
    (by have ht := tendsto_horiz_fx hb α x hr ha (a₂ := 2) (by linarith) 1 (Or.inl rfl)
        simp only [one_mul] at ht; exact ht)
    (by have ht := tendsto_horiz_fx hb α x hr ha (a₂ := 2) (by linarith) (-1) (Or.inr rfl)
        simp only [neg_one_mul] at ht; exact ht)
  unfold fx
  linear_combination h

/-- **Right of the pole**: `I_x = ∫ f_x(a + it) dt` for `a > 1`. -/
theorem Ix_eq_right {b : ℝ} (hb : 0 < b) (α x : ℝ) {a : ℝ} (ha1 : 1 < a) :
    Ix b α x = ∫ t : ℝ, fx b α x ((a : ℂ) + t * I) := by
  rw [Ix_eq]
  have hr : (0 : ℝ) < 1 / 4 := by norm_num
  have hdiff : ∀ {a₁ a₂ : ℝ}, 1 < a₁ → ∀ z : ℂ, a₁ ≤ z.re → z.re ≤ a₂ → DifferentiableAt ℂ (fx b α x) z :=
    fun h1 z hz _ => differentiableAt_fx hb α x (fun h => by rw [h] at hz; simp at hz; linarith)
  rcases le_total a 2 with h | h
  · exact (line_shift_zero h (hdiff ha1) (integrable_fx_line hb α x hr (by linarith) ha1.ne')
      (integrable_fx_line hb α x hr (by linarith) (by norm_num))
      (by simpa using tendsto_horiz_fx hb α x hr (by linarith) h 1 (Or.inl rfl))
      (by simpa using tendsto_horiz_fx hb α x hr (by linarith) h (-1) (Or.inr rfl))).symm
  · exact line_shift_zero h (hdiff (by norm_num : (1 : ℝ) < 2))
      (integrable_fx_line hb α x hr (by linarith) (by norm_num))
      (integrable_fx_line hb α x hr (by linarith) ha1.ne')
      (by simpa using tendsto_horiz_fx hb α x hr (by norm_num) h 1 (Or.inl rfl))
      (by simpa using tendsto_horiz_fx hb α x hr (by norm_num) h (-1) (Or.inr rfl))

/-- **The bumped contour**: for `1/4 + r ≤ a₁ ≤ a₂`, `1 < a₂`, `τ > 0`. -/
theorem Ix_eq_bump {b : ℝ} (hb : 0 < b) (α x : ℝ) {r : ℝ} (hr : 0 < r) {a₁ a₂ τ : ℝ}
    (ha₁ : 1 / 4 + r ≤ a₁) (ha : a₁ ≤ a₂) (ha₂ : 1 < a₂) (hτ : 0 < τ) (ha₁1 : a₁ ≠ 1) :
    Ix b α x = (∫ t in Ioi τ, fx b α x ((a₁ : ℂ) + t * I))
      + (∫ t in Iic (-τ), fx b α x ((a₁ : ℂ) + t * I))
      + (∫ t in (-τ)..τ, fx b α x ((a₂ : ℂ) + t * I))
      + I * (∫ s in a₁..a₂, fx b α x ((s : ℂ) + τ * I))
      - I * (∫ s in a₁..a₂, fx b α x ((s : ℂ) + ((-τ : ℝ) : ℂ) * I)) := by
  rw [Ix_eq_right hb α x ha₂]
  have i1 := integrable_fx_line hb α x hr ha₁ ha₁1
  have i2 := integrable_fx_line hb α x hr (by linarith) ha₂.ne'
  have hup := half_strip_upper (f := fx b α x) ha (τ := τ)
    (fun z _ _ hz => differentiableAt_fx hb α x (fun h => by rw [h] at hz; simp at hz; linarith))
    i1.integrableOn i2.integrableOn
    (by simpa using tendsto_horiz_fx hb α x hr ha₁ ha 1 (Or.inl rfl))
  have hlo := half_strip_lower (f := fx b α x) ha (τ := τ)
    (fun z _ _ hz => differentiableAt_fx hb α x (fun h => by rw [h] at hz; simp at hz; linarith))
    i1.integrableOn i2.integrableOn
    (by simpa using tendsto_horiz_fx hb α x hr ha₁ ha (-1) (Or.inr rfl))
  have hsplit1 := intervalIntegral.integral_Iic_add_Ioi (f := fun t : ℝ => fx b α x ((a₂ : ℂ) + t * I))
    (b := τ) i2.integrableOn i2.integrableOn
  have hsplit2 := intervalIntegral.integral_Iic_sub_Iic (f := fun t : ℝ => fx b α x ((a₂ : ℂ) + t * I))
    (a := -τ) (b := τ) i2.integrableOn i2.integrableOn
  rw [← hsplit1, hup]
  linear_combination hsplit2 + hlo

end FleetSmoothWindow
