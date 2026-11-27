import FleetSmoothWindowStripPieces

/-!
# Trivial pieces of `I_x`: the far-left line and the bump around `w = 1`

* `rmm_line_bound`: on `Re w = 1/2` (used for `x < θ − 1/4`, where `P_b(w − x)` sits at `Re = 1/2 − x > 1/2`
  and only its trivial bound is used):
  `e^{-x²/(4b)} ‖∫ f_x(1/2+it) dt‖ ≤ √(π/b) S_η e^{(m² − x²)/(4b)} · 2(39 + 20|α|) K₀`,
  `m = max 0 (1/2 + η + x)`.
* `bump_bound`: for `x ∈ [1/2 − κ, 1/2 + κ]`, `x ≠ 1/2`, the contour `Re w = 1/2 + x` (`|t| ≥ τ`) with the bump
  `Re w = 1 + κ₀` (`|t| ≤ τ`): window pieces plus `√(π/b) · const · e^{E_b/(4b)}`,
  `E_b = (1/2+κ₀)² − (|α|−τ)² + (1/2+η)² − (1/2−κ)²`.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set MeasureTheory
open scoped Real Interval

namespace FleetSmoothWindow

open FleetLandauTransfer FleetHeadContour

lemma gauss_four {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (x : ℝ) :
    Real.exp (-x ^ 2 / (4 * b)) ≤ 4 * (1 + x ^ 2)⁻¹ := by
  have h1 : Real.exp (-x ^ 2 / (4 * b)) ≤ Real.exp (-x ^ 2 / 4) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg x]
  have h2 : 1 + x ^ 2 / 4 ≤ Real.exp (x ^ 2 / 4) := by
    have := Real.add_one_le_exp (x ^ 2 / 4); linarith
  have hpos : 0 < 1 + x ^ 2 := by positivity
  refine h1.trans ?_
  have h3 : Real.exp (-x ^ 2 / 4) * (1 + x ^ 2 / 4) ≤ 1 := by
    rw [show -x ^ 2 / 4 = -(x ^ 2 / 4) by ring, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
    linarith
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  nlinarith [h3, Real.exp_pos (-x ^ 2 / 4)]

lemma gauss_lin_bound {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (β : ℝ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    Integrable (fun t : ℝ => Real.exp (-(t - β) ^ 2 / (4 * b)) * (A + B * |t|)) ∧
    ∫ t : ℝ, Real.exp (-(t - β) ^ 2 / (4 * b)) * (A + B * |t|) ≤ (A + B + B * |β|) * K0 := by
  set L := A + B + B * |β|
  have hpt : ∀ t : ℝ, Real.exp (-(t - β) ^ 2 / (4 * b)) * (A + B * |t|)
      ≤ L * (Real.exp (2 * b) * Real.exp (-(t - β) ^ 2 / (4 * (2 * b)))) := by
    intro t
    have hh : A + B * |t| ≤ L * (1 + |t - β|) := by
      have : |t| ≤ |β| + |t - β| := by
        calc |t| = |β + (t - β)| := by ring_nf
          _ ≤ |β| + |t - β| := abs_add_le _ _
      simp only [L]
      nlinarith [mul_nonneg hA (abs_nonneg (t - β)), mul_nonneg (mul_nonneg hB (abs_nonneg β)) (abs_nonneg (t - β)),
        mul_le_mul_of_nonneg_left this hB, mul_nonneg hB (abs_nonneg (t - β))]
    have h2 := one_add_abs_le_exp_gauss hb (t - β)
    have hL : 0 ≤ L := by positivity
    calc Real.exp (-(t - β) ^ 2 / (4 * b)) * (A + B * |t|)
        ≤ Real.exp (-(t - β) ^ 2 / (4 * b)) * (L * (1 + |t - β|)) := by gcongr
      _ = L * ((1 + |t - β|) * Real.exp (-(t - β) ^ 2 / (4 * b))) := by ring
      _ ≤ _ := by gcongr
  have imaj : Integrable (fun t : ℝ => L * (Real.exp (2 * b) * Real.exp (-(t - β) ^ 2 / (4 * (2 * b))))) :=
    ((FleetHeadContour.integrable_gauss_shift (by positivity : 0 < 2 * b) β).const_mul _).const_mul _
  have ig : Integrable (fun t : ℝ => Real.exp (-(t - β) ^ 2 / (4 * b)) * (A + B * |t|)) := by
    refine imaj.mono' (by fun_prop) (ae_of_all _ fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt t
  refine ⟨ig, (integral_mono ig imaj hpt).trans ?_⟩
  rw [integral_const_mul, integral_const_mul, integral_gauss_shift (by positivity : 0 < 2 * b)]
  have hL : 0 ≤ L := by positivity
  unfold K0
  have h8 : Real.exp (2 * b) ≤ Real.exp 8 := Real.exp_le_exp.mpr (by linarith)
  have hs : Real.sqrt (4 * π * (2 * b)) ≤ Real.sqrt (8 * π) := Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])
  gcongr

/-- **The far-left line `Re w = 1/2`.** -/
theorem rmm_line_bound {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (α x : ℝ) {η : ℝ} (hη : 0 < η) :
    Real.exp (-x ^ 2 / (4 * b)) * ‖∫ t : ℝ, fx b α x (((1 / 2 : ℝ) : ℂ) + t * I)‖
      ≤ Real.sqrt (π / b) * Sz η * Real.exp ((max 0 (1 / 2 + η + x) ^ 2 - x ^ 2) / (4 * b))
        * (2 * ((39 + 20 * |α|) * K0)) := by
  set m := max 0 (1 / 2 + η + x)
  set K := Real.sqrt (π / b) * Sz η * Real.exp (m ^ 2 / (4 * b))
  have hS := Sz_nonneg η
  have hK : 0 ≤ K := by positivity
  obtain ⟨ip, Ip⟩ := gauss_lin_bound hb hb1 (-α) (A := 19) (B := 20) (by norm_num) (by norm_num)
  obtain ⟨im, Im⟩ := gauss_lin_bound hb hb1 α (A := 19) (B := 20) (by norm_num) (by norm_num)
  rw [abs_neg] at Ip
  set g : ℝ → ℝ := fun t => K * (Real.exp (-(t - -α) ^ 2 / (4 * b)) * (19 + 20 * |t|)
    + Real.exp (-(t - α) ^ 2 / (4 * b)) * (19 + 20 * |t|))
  have ig : Integrable g := (ip.add im).const_mul _
  have hpt : ∀ t : ℝ, ‖fx b α x (((1 / 2 : ℝ) : ℂ) + t * I)‖ ≤ g t := by
    intro t
    unfold fx
    rw [norm_mul, norm_neg]
    have h1 := norm_Phix_le hb α x hη (1 / 2) t
    have e0 : Real.exp (((1 / 2 : ℝ) - 1 / 2) ^ 2 / (4 * b)) = 1 := by norm_num
    have e1 : (1 + η - ((1 / 2 : ℝ) - x)) = 1 / 2 + η + x := by ring
    rw [e0, mul_one, e1] at h1
    have h2 := norm_deriv_zeta_line (x := 1 / 2) le_rfl (by norm_num) t
    have hc : (|(1 / 2 : ℝ) - 1| ^ 2)⁻¹ + 20 * (|(1 / 2 : ℝ)| + |t|) + 5 = 19 + 20 * |t| := by
      rw [show |(1 / 2 : ℝ) - 1| = 1 / 2 by norm_num [abs_of_neg], abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      ring
    rw [hc] at h2
    calc ‖Phix b α x (((1 / 2 : ℝ) : ℂ) + ↑t * I)‖ * ‖deriv riemannZeta (((1 / 2 : ℝ) : ℂ) + ↑t * I)‖
        ≤ (Real.sqrt (π / b) * (Real.exp (-(t + α) ^ 2 / (4 * b)) + Real.exp (-(t - α) ^ 2 / (4 * b)))
          * (Sz η * Real.exp (m ^ 2 / (4 * b)))) * (19 + 20 * |t|) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = g t := by simp only [g, K, sub_neg_eq_add]; ring
  have hn : ‖∫ t : ℝ, fx b α x (((1 / 2 : ℝ) : ℂ) + t * I)‖ ≤ ∫ t, g t :=
    norm_integral_le_of_norm_le ig (ae_of_all _ hpt)
  have hIg : ∫ t, g t ≤ K * (2 * ((39 + 20 * |α|) * K0)) := by
    simp only [g]
    rw [integral_const_mul, integral_add ip im]
    have : (19 + 20 + 20 * |α|) * K0 = (39 + 20 * |α|) * K0 := by ring
    rw [this] at Ip Im
    gcongr; linarith
  have hE : Real.exp (-x ^ 2 / (4 * b)) * Real.exp (m ^ 2 / (4 * b))
      = Real.exp ((m ^ 2 - x ^ 2) / (4 * b)) := by rw [← Real.exp_add]; congr 1; ring
  calc Real.exp (-x ^ 2 / (4 * b)) * ‖∫ t : ℝ, fx b α x (((1 / 2 : ℝ) : ℂ) + t * I)‖
      ≤ Real.exp (-x ^ 2 / (4 * b)) * (K * (2 * ((39 + 20 * |α|) * K0))) := by
        gcongr; exact hn.trans hIg
    _ = _ := by simp only [K]; rw [← hE]; ring

/-- `e^{-(t+α)²/(4b)} + e^{-(t−α)²/(4b)} ≤ 2 e^{-(|α|−τ)²/(4b)}` for `|t| ≤ τ ≤ |α|`. -/
lemma Gsum_le {b : ℝ} (hb : 0 < b) {α τ t : ℝ} (hτα : τ ≤ |α|) (ht : |t| ≤ τ) :
    Real.exp (-(t + α) ^ 2 / (4 * b)) + Real.exp (-(t - α) ^ 2 / (4 * b))
      ≤ 2 * Real.exp (-(|α| - τ) ^ 2 / (4 * b)) := by
  have h0 : 0 ≤ |α| - τ := by linarith
  have g1 : Real.exp (-(t + α) ^ 2 / (4 * b)) ≤ Real.exp (-(|α| - τ) ^ 2 / (4 * b)) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : |α| - τ ≤ |t + α| := by
      have := abs_sub_abs_le_abs_sub α (-t)
      rw [abs_neg, sub_neg_eq_add, add_comm] at this; linarith
    nlinarith [sq_abs (t + α), pow_le_pow_left₀ h0 this 2]
  have g2 : Real.exp (-(t - α) ^ 2 / (4 * b)) ≤ Real.exp (-(|α| - τ) ^ 2 / (4 * b)) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : |α| - τ ≤ |t - α| := by
      have := abs_sub_abs_le_abs_sub α t
      rw [abs_sub_comm] at this; linarith
    nlinarith [sq_abs (t - α), pow_le_pow_left₀ h0 this 2]
  linarith

/-- The bump exponent combination. -/
lemma bump_exp {b : ℝ} (hb : 0 < b) {A₁ B₁ C₁ x κ₀ η κ α τ : ℝ}
    (hA : A₁ ≤ (1 / 2 + κ₀) ^ 2) (hC : C₁ ≤ (1 / 2 + η) ^ 2) (hx : (1 / 2 - κ) ^ 2 ≤ x ^ 2)
    (hB : B₁ = (|α| - τ) ^ 2) :
    Real.exp (-x ^ 2 / (4 * b)) * (Real.exp (A₁ / (4 * b)) * Real.exp (-B₁ / (4 * b)) * Real.exp (C₁ / (4 * b)))
      ≤ Real.exp (((1 / 2 + κ₀) ^ 2 - (|α| - τ) ^ 2 + (1 / 2 + η) ^ 2 - (1 / 2 - κ) ^ 2) / (4 * b)) := by
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp, hB]
  rw [show -x ^ 2 / (4 * b) + (A₁ / (4 * b) + -(|α| - τ) ^ 2 / (4 * b) + C₁ / (4 * b))
      = (-x ^ 2 + A₁ - (|α| - τ) ^ 2 + C₁) / (4 * b) by ring]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

/-- **The bump region.** -/
theorem bump_bound {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) {α c Cp Cm : ℝ}
    (hWm : smoothWindow b α ≤ Cm * Real.exp (c / b)) (hWp : smoothWindow b (-α) ≤ Cp * Real.exp (c / b))
    {η κ κ₀ τ x : ℝ} (hη : 0 < η) (hκ : 0 < κ) (hκκ₀ : κ ≤ κ₀) (hκ₀ : κ₀ ≤ 1 / 4) (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (hτα : τ ≤ |α|) (hx1 : 1 / 2 - κ ≤ x) (hx2 : x ≤ 1 / 2 + κ) (hx : x ≠ 1 / 2) :
    Real.exp (-x ^ 2 / (4 * b)) * ‖Ix b α x‖
      ≤ Real.sqrt (π / b) * (2 * (((τ ^ 2)⁻¹ + 45) + 20 + 20 * |α|) * Real.exp (c / (2 * b))
          * (Cp + Cm + 2 * K0) / 2)
        + Real.sqrt (π / b) * (2 * Sz η * (2 * τ * Lam1 (1 + κ₀) + 2 * ((τ ^ 2)⁻¹ + 45 + 20 * τ)))
          * Real.exp (((1 / 2 + κ₀) ^ 2 - (|α| - τ) ^ 2 + (1 / 2 + η) ^ 2 - (1 / 2 - κ) ^ 2) / (4 * b)) := by
  set Eb := ((1 / 2 + κ₀) ^ 2 - (|α| - τ) ^ 2 + (1 / 2 + η) ^ 2 - (1 / 2 - κ) ^ 2)
  set a₁ := 1 / 2 + x
  set a₂ := 1 + κ₀
  have hS := Sz_nonneg η
  have hx0 : 0 ≤ x := by linarith
  have ha₁ : 1 / 4 + 1 / 4 ≤ a₁ := by simp only [a₁]; linarith
  have ha : a₁ ≤ a₂ := by simp only [a₁, a₂]; linarith
  have ha₂ : 1 < a₂ := by simp only [a₂]; linarith
  have ha₁1 : a₁ ≠ 1 := by simp only [a₁]; intro h; apply hx; linarith
  have hid := Ix_eq_bump hb α x (r := 1 / 4) (by norm_num) ha₁ ha ha₂ hτ ha₁1
  -- the vertical pieces
  have hzv : ∀ t : ℝ, τ ≤ |t| → ‖deriv riemannZeta ((((1 / 2 + x : ℝ)) : ℂ) + t * I)‖
      ≤ ((τ ^ 2)⁻¹ + 45) + 20 * |t| := by
    intro t ht
    have hsd : τ ≤ ‖(((1 / 2 + x : ℝ)) : ℂ) + t * I - 1‖ := by
      have := Complex.abs_im_le_norm ((((1 / 2 + x : ℝ)) : ℂ) + t * I - 1)
      have him : ((((1 / 2 + x : ℝ)) : ℂ) + t * I - 1).im = t := by simp
      rw [him] at this; linarith
    have h := norm_deriv_zeta_le_lin (r := 1 / 4) (by norm_num) hτ
      (s := (((1 / 2 + x : ℝ)) : ℂ) + t * I) (by simp; linarith) hsd
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero,
      add_im, mul_im, zero_add] at h
    have habs : |1 / 2 + x| ≤ 2 := by rw [abs_le]; constructor <;> linarith
    have : 5 * (|1 / 2 + x| + 1 / 4) / (1 / 4) ≤ 45 := by
      rw [div_le_iff₀ (by norm_num)]; linarith
    norm_num at h this ⊢
    linarith
  have V1 := window_line_bound hb hb1 (A := (τ ^ 2)⁻¹ + 45) (B := 20) (by positivity) (by norm_num) hWm hWp x
    (S := Ioi τ) measurableSet_Ioi (fun t ht => hzv t (by rw [mem_Ioi] at ht; rw [abs_of_pos (by linarith)]; linarith))
  have V2 := window_line_bound hb hb1 (A := (τ ^ 2)⁻¹ + 45) (B := 20) (by positivity) (by norm_num) hWm hWp x
    (S := Iic (-τ)) measurableSet_Iic (fun t ht => hzv t (by rw [mem_Iic] at ht; rw [abs_of_neg (by linarith)]; linarith))
  -- the middle segment `Re w = a₂`, `|t| ≤ τ`
  have hmid : ∀ t ∈ Ι (-τ) τ, Real.exp (-x ^ 2 / (4 * b)) * ‖fx b α x ((a₂ : ℂ) + t * I)‖
      ≤ Real.sqrt (π / b) * (2 * Sz η * Lam1 (1 + κ₀)) * Real.exp (Eb / (4 * b)) := by
    intro t ht
    have ht' : |t| ≤ τ := by
      rw [uIoc_of_le (by linarith)] at ht; rw [abs_le]; exact ⟨ht.1.le, ht.2⟩
    unfold fx
    rw [norm_mul, norm_neg]
    have h1 := norm_Phix_le hb α x hη a₂ t
    have h2 := norm_deriv_zeta_le_Lam1 (s := (a₂ : ℂ) + t * I) (by simpa using ha₂)
    have hre : ((a₂ : ℂ) + t * I).re = a₂ := by simp
    rw [hre] at h2
    have hG := Gsum_le hb hτα ht'
    have hA1 : (a₂ - 1 / 2) ^ 2 ≤ (1 / 2 + κ₀) ^ 2 := by simp only [a₂]; nlinarith
    have hm : max 0 (1 + η - (a₂ - x)) ^ 2 ≤ (1 / 2 + η) ^ 2 :=
      pow_le_pow_left₀ (le_max_left _ _) (max_le (by linarith) (by simp only [a₂]; linarith)) 2
    have hxx : (1 / 2 - κ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by linarith) hx1 2
    have hL := Lam1_nonneg a₂
    have hL2 : Lam1 a₂ ≤ Lam1 (1 + κ₀) := le_rfl
    have key := bump_exp hb (A₁ := (a₂ - 1 / 2) ^ 2) (B₁ := (|α| - τ) ^ 2)
      (C₁ := max 0 (1 + η - (a₂ - x)) ^ 2) hA1 hm hxx rfl
    calc Real.exp (-x ^ 2 / (4 * b)) * (‖Phix b α x ((a₂ : ℂ) + t * I)‖ * ‖deriv riemannZeta ((a₂ : ℂ) + t * I)‖)
        ≤ Real.exp (-x ^ 2 / (4 * b)) * ((Real.sqrt (π / b) * Real.exp ((a₂ - 1 / 2) ^ 2 / (4 * b)) *
            (2 * Real.exp (-(|α| - τ) ^ 2 / (4 * b))) * (Sz η * Real.exp (max 0 (1 + η - (a₂ - x)) ^ 2 / (4 * b))))
            * Lam1 a₂) := by
          gcongr
          exact h1.trans (by gcongr)
      _ = Real.sqrt (π / b) * (2 * Sz η * Lam1 a₂) * (Real.exp (-x ^ 2 / (4 * b)) *
            (Real.exp ((a₂ - 1 / 2) ^ 2 / (4 * b)) * Real.exp (-(|α| - τ) ^ 2 / (4 * b))
            * Real.exp (max 0 (1 + η - (a₂ - x)) ^ 2 / (4 * b)))) := by ring
      _ ≤ _ := by gcongr
  have M := intervalIntegral.norm_integral_le_of_norm_le_const (a := -τ) (b := τ)
    (f := fun t => Real.exp (-x ^ 2 / (4 * b)) * fx b α x ((a₂ : ℂ) + t * I))
    (C := Real.sqrt (π / b) * (2 * Sz η * Lam1 (1 + κ₀)) * Real.exp (Eb / (4 * b)))
    (fun t ht => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hmid t ht)
  rw [intervalIntegral.integral_const_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    show |τ - -τ| = 2 * τ by rw [abs_of_pos (by linarith)]; ring] at M
  -- the horizontal segments
  have hhor : ∀ (y : ℝ), |y| = τ → ∀ σ ∈ Ι a₁ a₂, Real.exp (-x ^ 2 / (4 * b)) * ‖fx b α x ((σ : ℂ) + y * I)‖
      ≤ Real.sqrt (π / b) * (2 * Sz η * ((τ ^ 2)⁻¹ + 45 + 20 * τ)) * Real.exp (Eb / (4 * b)) := by
    intro y hy σ hσ
    rw [uIoc_of_le ha] at hσ
    have hσ1 : 1 / 2 + x < σ := hσ.1
    have hσ2 : σ ≤ 1 + κ₀ := hσ.2
    unfold fx
    rw [norm_mul, norm_neg]
    have h1 := norm_Phix_le hb α x hη σ y
    have hsd : τ ≤ ‖(σ : ℂ) + y * I - 1‖ := by
      have := Complex.abs_im_le_norm ((σ : ℂ) + y * I - 1); simp at this; linarith
    have h2 := norm_deriv_zeta_le_lin (r := 1 / 4) (by norm_num) hτ (s := (σ : ℂ) + y * I)
      (by simp; linarith [hσ.1]) hsd
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero,
      add_im, mul_im, zero_add] at h2
    have hσabs : |σ| ≤ 2 := by rw [abs_le]; constructor <;> linarith [hσ.1, hσ.2]
    have h2' : ‖deriv riemannZeta ((σ : ℂ) + y * I)‖ ≤ (τ ^ 2)⁻¹ + 45 + 20 * τ := by
      have : 5 * (|σ| + 1 / 4) / (1 / 4) ≤ 45 := by rw [div_le_iff₀ (by norm_num)]; linarith
      rw [hy] at h2; norm_num at h2 this ⊢; linarith
    have hG := Gsum_le hb hτα (t := y) hy.le
    have hA1 : (σ - 1 / 2) ^ 2 ≤ (1 / 2 + κ₀) ^ 2 := by
      have h0 : 0 ≤ σ - 1 / 2 := by linarith [hσ.1]
      exact pow_le_pow_left₀ h0 (by linarith [hσ.2]) 2
    have hm : max 0 (1 + η - (σ - x)) ^ 2 ≤ (1 / 2 + η) ^ 2 :=
      pow_le_pow_left₀ (le_max_left _ _) (max_le (by linarith) (by linarith)) 2
    have hxx : (1 / 2 - κ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by linarith) hx1 2
    have key := bump_exp hb (A₁ := (σ - 1 / 2) ^ 2) (B₁ := (|α| - τ) ^ 2)
      (C₁ := max 0 (1 + η - (σ - x)) ^ 2) hA1 hm hxx rfl
    calc Real.exp (-x ^ 2 / (4 * b)) * (‖Phix b α x ((σ : ℂ) + y * I)‖ * ‖deriv riemannZeta ((σ : ℂ) + y * I)‖)
        ≤ Real.exp (-x ^ 2 / (4 * b)) * ((Real.sqrt (π / b) * Real.exp ((σ - 1 / 2) ^ 2 / (4 * b)) *
            (2 * Real.exp (-(|α| - τ) ^ 2 / (4 * b))) * (Sz η * Real.exp (max 0 (1 + η - (σ - x)) ^ 2 / (4 * b))))
            * ((τ ^ 2)⁻¹ + 45 + 20 * τ)) := by
          gcongr
          exact h1.trans (by gcongr)
      _ = Real.sqrt (π / b) * (2 * Sz η * ((τ ^ 2)⁻¹ + 45 + 20 * τ)) * (Real.exp (-x ^ 2 / (4 * b)) *
            (Real.exp ((σ - 1 / 2) ^ 2 / (4 * b)) * Real.exp (-(|α| - τ) ^ 2 / (4 * b))
            * Real.exp (max 0 (1 + η - (σ - x)) ^ 2 / (4 * b)))) := by ring
      _ ≤ _ := by gcongr
  have hlen : |a₂ - a₁| ≤ 1 := by rw [abs_le]; simp only [a₁, a₂]; constructor <;> linarith
  have Hb : ∀ y : ℝ, |y| = τ → Real.exp (-x ^ 2 / (4 * b)) * ‖∫ s in a₁..a₂, fx b α x ((s : ℂ) + y * I)‖
      ≤ Real.sqrt (π / b) * (2 * Sz η * ((τ ^ 2)⁻¹ + 45 + 20 * τ)) * Real.exp (Eb / (4 * b)) := by
    intro y hy
    have H := intervalIntegral.norm_integral_le_of_norm_le_const (a := a₁) (b := a₂)
      (f := fun s => Real.exp (-x ^ 2 / (4 * b)) * fx b α x ((s : ℂ) + y * I))
      (C := Real.sqrt (π / b) * (2 * Sz η * ((τ ^ 2)⁻¹ + 45 + 20 * τ)) * Real.exp (Eb / (4 * b)))
      (fun s hs => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hhor y hy s hs)
    rw [intervalIntegral.integral_const_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] at H
    have hC : 0 ≤ Real.sqrt (π / b) * (2 * Sz η * ((τ ^ 2)⁻¹ + 45 + 20 * τ)) * Real.exp (Eb / (4 * b)) := by
      positivity
    calc _ ≤ _ := H
      _ ≤ _ := by nlinarith [abs_nonneg (a₂ - a₁)]
  have H1 := Hb τ (abs_of_pos hτ)
  have H2 := Hb (-τ) (by rw [abs_neg, abs_of_pos hτ])
  -- assemble
  rw [hid]
  set e := Real.exp (-x ^ 2 / (4 * b))
  have he : 0 < e := Real.exp_pos _
  have tri : ‖(∫ t in Ioi τ, fx b α x ((a₁ : ℂ) + t * I)) + (∫ t in Iic (-τ), fx b α x ((a₁ : ℂ) + t * I))
      + (∫ t in (-τ)..τ, fx b α x ((a₂ : ℂ) + t * I))
      + I * (∫ s in a₁..a₂, fx b α x ((s : ℂ) + τ * I))
      - I * (∫ s in a₁..a₂, fx b α x ((s : ℂ) + ((-τ : ℝ) : ℂ) * I))‖
      ≤ ‖∫ t in Ioi τ, fx b α x ((a₁ : ℂ) + t * I)‖ + ‖∫ t in Iic (-τ), fx b α x ((a₁ : ℂ) + t * I)‖
        + ‖∫ t in (-τ)..τ, fx b α x ((a₂ : ℂ) + t * I)‖
        + ‖∫ s in a₁..a₂, fx b α x ((s : ℂ) + τ * I)‖
        + ‖∫ s in a₁..a₂, fx b α x ((s : ℂ) + ((-τ : ℝ) : ℂ) * I)‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_I, one_mul]
    refine add_le_add ((norm_add_le _ _).trans ?_) le_rfl
    rw [norm_mul, norm_I, one_mul]
    refine add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl
  calc e * ‖_‖ ≤ e * (‖∫ t in Ioi τ, fx b α x ((a₁ : ℂ) + t * I)‖ + ‖∫ t in Iic (-τ), fx b α x ((a₁ : ℂ) + t * I)‖
        + ‖∫ t in (-τ)..τ, fx b α x ((a₂ : ℂ) + t * I)‖
        + ‖∫ s in a₁..a₂, fx b α x ((s : ℂ) + τ * I)‖
        + ‖∫ s in a₁..a₂, fx b α x ((s : ℂ) + ((-τ : ℝ) : ℂ) * I)‖) := by gcongr
    _ = e * ‖∫ t in Ioi τ, fx b α x ((a₁ : ℂ) + t * I)‖ + e * ‖∫ t in Iic (-τ), fx b α x ((a₁ : ℂ) + t * I)‖
        + e * ‖∫ t in (-τ)..τ, fx b α x ((a₂ : ℂ) + t * I)‖
        + e * ‖∫ s in a₁..a₂, fx b α x ((s : ℂ) + τ * I)‖
        + e * ‖∫ s in a₁..a₂, fx b α x ((s : ℂ) + ((-τ : ℝ) : ℂ) * I)‖ := by ring
    _ ≤ Real.sqrt (π / b) * ((((τ ^ 2)⁻¹ + 45) + 20 + 20 * |α|) * Real.exp (c / (2 * b)) * (Cp + Cm + 2 * K0) / 2)
        + Real.sqrt (π / b) * ((((τ ^ 2)⁻¹ + 45) + 20 + 20 * |α|) * Real.exp (c / (2 * b)) * (Cp + Cm + 2 * K0) / 2)
        + Real.sqrt (π / b) * (2 * Sz η * Lam1 (1 + κ₀)) * Real.exp (Eb / (4 * b)) * (2 * τ)
        + Real.sqrt (π / b) * (2 * Sz η * ((τ ^ 2)⁻¹ + 45 + 20 * τ)) * Real.exp (Eb / (4 * b))
        + Real.sqrt (π / b) * (2 * Sz η * ((τ ^ 2)⁻¹ + 45 + 20 * τ)) * Real.exp (Eb / (4 * b)) := by
        refine add_le_add (add_le_add (add_le_add (add_le_add V1 V2) M) H1) ?_
        simpa using H2
    _ = _ := by ring

end FleetSmoothWindow
