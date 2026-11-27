import FleetSmoothWindowStripBound

/-!
# The pieces of `I_x`: window pieces, trivial pieces, residues

Window pieces (the `w`-line at `Re w = 1/2 + x`, where `P_b(w − x)` is on the critical line):
`e^{-x²/(4b)} ‖∫_S f_x(1/2 + x + it) dt‖ ≤ √(π/b) L e^{c/(2b)} (C₊ + C₋ + 2K₀)/2` (`window_line_bound`), from
the smooth window at `±α` (`≤ C_± e^{c/b}`) and a linear bound `A + B|t|` for `ζ'` on `S`
(`L = A + B + B|α|`, `K₀ = e⁸√(8π)`), via the weighted AM-GM inequality with weight `L e^{-c/(2b)}`.

Residue: `e^{-x²/(4b)} ‖Φ_x'(1)‖ ≤ (2/ρ) √(π/b) S_η e^{E/(4b)}`,
`E = (1/2+ρ)² − (|α|−ρ)² + (η+ρ)(η+ρ+1)` (`residue_bound`, Cauchy estimate on `|w − 1| = ρ`, `x ≤ 1/2`).
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace FleetSmoothWindow

open FleetLandauTransfer FleetHeadContour

/-- `K₀ = e⁸ √(8π)`. -/
def K0 : ℝ := Real.exp 8 * Real.sqrt (8 * π)

lemma K0_nonneg : 0 ≤ K0 := by unfold K0; positivity

/-- **Weighted AM-GM against the window.** -/
theorem window_lin_le {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) {β c C A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (hW : smoothWindow b β ≤ C * Real.exp (c / b)) :
    Integrable (fun t : ℝ => Real.exp (-(t - β) ^ 2 / (4 * b)) *
      ((A + B * |t|) * ‖Psm b (((1 / 2 : ℝ) : ℂ) + t * I)‖)) ∧
    ∫ t : ℝ, Real.exp (-(t - β) ^ 2 / (4 * b)) * ((A + B * |t|) * ‖Psm b (((1 / 2 : ℝ) : ℂ) + t * I)‖)
      ≤ (A + B + B * |β|) * Real.exp (c / (2 * b)) * (C + K0) / 2 := by
  set L := A + B + B * |β|
  have hL : 0 < L := by positivity
  set lam := L * Real.exp (-(c / (2 * b)))
  have hlam : 0 < lam := by positivity
  set G : ℝ → ℝ := fun t => Real.exp (-(t - β) ^ 2 / (4 * b))
  set p : ℝ → ℝ := fun t => ‖Psm b (((1 / 2 : ℝ) : ℂ) + t * I)‖
  set h : ℝ → ℝ := fun t => A + B * |t|
  have hh : ∀ t, h t ≤ L * (1 + |t - β|) := by
    intro t
    have : |t| ≤ |β| + |t - β| := by
      calc |t| = |β + (t - β)| := by ring_nf
        _ ≤ |β| + |t - β| := abs_add_le _ _
    simp only [h, L]
    nlinarith [mul_nonneg hA.le (abs_nonneg (t - β)), mul_nonneg (mul_nonneg hB (abs_nonneg β)) (abs_nonneg (t - β)),
      mul_le_mul_of_nonneg_left this hB, mul_nonneg hB (abs_nonneg (t - β))]
  have hh0 : ∀ t, 0 ≤ h t := fun t => by simp only [h]; positivity
  -- `h² G` is integrable, with integral `≤ L² K₀`
  have hG8 : ∀ t, h t ^ 2 * G t ≤ L ^ 2 * (Real.exp (8 * b) * Real.exp (-(t - β) ^ 2 / (4 * (2 * b)))) := by
    intro t
    have h1 : h t ^ 2 ≤ (L * (1 + |t - β|)) ^ 2 := pow_le_pow_left₀ (hh0 t) (hh t) 2
    have h2 := two_abs_le_exp_gauss hb (t - β)
    calc h t ^ 2 * G t ≤ (L * (1 + |t - β|)) ^ 2 * G t := by gcongr
      _ = L ^ 2 * ((1 + |t - β|) ^ 2 * G t) := by ring
      _ ≤ _ := by gcongr
  have ihG : Integrable (fun t => h t ^ 2 * G t) := by
    refine Integrable.mono' (((FleetHeadContour.integrable_gauss_shift (by positivity : 0 < 2 * b) β).const_mul
      (Real.exp (8 * b))).const_mul (L ^ 2)) (by fun_prop) (ae_of_all _ fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hG8 t
  have IhG : ∫ t, h t ^ 2 * G t ≤ L ^ 2 * K0 := by
    calc ∫ t, h t ^ 2 * G t ≤ ∫ t, L ^ 2 * (Real.exp (8 * b) * Real.exp (-(t - β) ^ 2 / (4 * (2 * b)))) :=
          integral_mono ihG (((FleetHeadContour.integrable_gauss_shift (by positivity : 0 < 2 * b) β).const_mul
            _).const_mul _) hG8
      _ = L ^ 2 * (Real.exp (8 * b) * Real.sqrt (4 * π * (2 * b))) := by
          rw [integral_const_mul, integral_const_mul, integral_gauss_shift (by positivity : 0 < 2 * b)]
      _ ≤ L ^ 2 * K0 := by
          unfold K0
          have h8 : Real.exp (8 * b) ≤ Real.exp 8 := Real.exp_le_exp.mpr (by linarith)
          have hs : Real.sqrt (4 * π * (2 * b)) ≤ Real.sqrt (8 * π) :=
            Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])
          gcongr
  have ipG : Integrable (fun t => p t ^ 2 * G t) := integrable_window hb β
  have IpG : ∫ t, p t ^ 2 * G t ≤ C * Real.exp (c / b) := hW
  -- pointwise AM-GM
  have hpt : ∀ t, G t * (h t * p t) ≤ (lam * (p t ^ 2 * G t) + (1 / lam) * (h t ^ 2 * G t)) / 2 := by
    intro t
    have hG0 : 0 ≤ G t := (Real.exp_pos _).le
    have key : h t * p t ≤ (lam * p t ^ 2 + h t ^ 2 / lam) / 2 := by
      have hsq : 0 ≤ (lam * p t - h t) ^ 2 / lam := div_nonneg (sq_nonneg _) hlam.le
      have e : (lam * p t - h t) ^ 2 / lam = lam * p t ^ 2 + h t ^ 2 / lam - 2 * (h t * p t) := by
        field_simp; ring
      linarith
    calc G t * (h t * p t) ≤ G t * ((lam * p t ^ 2 + h t ^ 2 / lam) / 2) := mul_le_mul_of_nonneg_left key hG0
      _ = _ := by field_simp
  have imaj : Integrable (fun t => (lam * (p t ^ 2 * G t) + (1 / lam) * (h t ^ 2 * G t)) / 2) :=
    ((ipG.const_mul lam).add (ihG.const_mul (1 / lam))).div_const 2
  have iprod : Integrable (fun t => G t * (h t * p t)) := by
    refine Integrable.mono' imaj ?_ (ae_of_all _ fun t => ?_)
    · have : Continuous p := ((continuous_Psm hb).comp (continuous_line (1 / 2))).norm
      exact (by fun_prop : Continuous G).mul ((by fun_prop : Continuous h).mul this) |>.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by have := hh0 t; positivity)]
      exact hpt t
  refine ⟨iprod, ?_⟩
  have hint : ∫ t, G t * (h t * p t) ≤ (lam * (C * Real.exp (c / b)) + (1 / lam) * (L ^ 2 * K0)) / 2 := by
    calc ∫ t, G t * (h t * p t)
        ≤ ∫ t, (lam * (p t ^ 2 * G t) + (1 / lam) * (h t ^ 2 * G t)) / 2 := integral_mono iprod imaj hpt
      _ = (lam * (∫ t, p t ^ 2 * G t) + (1 / lam) * ∫ t, h t ^ 2 * G t) / 2 := by
          rw [integral_div, integral_add (ipG.const_mul _) (ihG.const_mul _), integral_const_mul,
            integral_const_mul]
      _ ≤ _ := div_le_div_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left IpG hlam.le)
            (mul_le_mul_of_nonneg_left IhG (one_div_pos.mpr hlam).le)) (by norm_num)
  refine hint.trans (le_of_eq ?_)
  have e1 : lam * (C * Real.exp (c / b)) = L * C * Real.exp (c / (2 * b)) := by
    simp only [lam]
    have : Real.exp (-(c / (2 * b))) * Real.exp (c / b) = Real.exp (c / (2 * b)) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    rw [show L * Real.exp (-(c / (2 * b))) * (C * Real.exp (c / b))
      = L * C * (Real.exp (-(c / (2 * b))) * Real.exp (c / b)) by ring, this]
  have e2 : (1 / lam) * (L ^ 2 * K0) = L * K0 * Real.exp (c / (2 * b)) := by
    simp only [lam]
    rw [Real.exp_neg]
    field_simp
  rw [e1, e2]
  ring

/-- **Window piece.** `a = 1/2 + x`; on `S`, `‖ζ'(a + it)‖ ≤ A + B|t|`. -/
theorem window_line_bound {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) {α c Cp Cm A B : ℝ} (hA : 0 < A)
    (hB : 0 ≤ B) (hWm : smoothWindow b α ≤ Cm * Real.exp (c / b))
    (hWp : smoothWindow b (-α) ≤ Cp * Real.exp (c / b)) (x : ℝ) {S : Set ℝ} (hS : MeasurableSet S)
    (hz : ∀ t ∈ S, ‖deriv riemannZeta ((((1 / 2 + x : ℝ)) : ℂ) + t * I)‖ ≤ A + B * |t|) :
    Real.exp (-x ^ 2 / (4 * b)) * ‖∫ t in S, fx b α x ((((1 / 2 + x : ℝ)) : ℂ) + t * I)‖
      ≤ Real.sqrt (π / b) * ((A + B + B * |α|) * Real.exp (c / (2 * b)) * (Cp + Cm + 2 * K0) / 2) := by
  set p : ℝ → ℝ := fun t => ‖Psm b (((1 / 2 : ℝ) : ℂ) + t * I)‖
  set h : ℝ → ℝ := fun t => A + B * |t|
  set Gp : ℝ → ℝ := fun t => Real.exp (-(t - -α) ^ 2 / (4 * b))
  set Gm : ℝ → ℝ := fun t => Real.exp (-(t - α) ^ 2 / (4 * b))
  obtain ⟨ip, Ip⟩ := window_lin_le hb hb1 hA hB hWp
  obtain ⟨im, Im⟩ := window_lin_le hb hb1 hA hB hWm
  rw [abs_neg] at Ip
  set E := Real.exp (x ^ 2 / (4 * b))
  set g : ℝ → ℝ := fun t => Real.sqrt (π / b) * E * (Gp t * (h t * p t) + Gm t * (h t * p t))
  have ig : Integrable g := (ip.add im).const_mul _
  have hg0 : ∀ t, 0 ≤ g t := fun t => by simp only [g, h, p, Gp, Gm]; positivity
  have hpt : ∀ t ∈ S, ‖fx b α x ((((1 / 2 + x : ℝ)) : ℂ) + t * I)‖ ≤ g t := by
    intro t ht
    unfold fx Phix
    rw [norm_mul, norm_mul, norm_neg]
    have h1 := norm_LGw_le b α (1 / 2 + x) t
    have e : ((((1 / 2 + x : ℝ)) : ℂ) + t * I) - x = ((1 / 2 : ℝ) : ℂ) + t * I := by push_cast; ring
    rw [e]
    have h3 := hz t ht
    have hp : ‖Psm b (((1 / 2 : ℝ) : ℂ) + t * I)‖ = p t := rfl
    rw [hp]
    rw [show (1 / 2 + x - 1 / 2 : ℝ) = x by ring] at h1
    have hGp : Real.exp (-(t + α) ^ 2 / (4 * b)) = Gp t := by simp only [Gp, sub_neg_eq_add]
    rw [hGp] at h1
    have hp0 : 0 ≤ p t := norm_nonneg _
    calc ‖LGw b α ((((1 / 2 + x : ℝ)) : ℂ) + t * I)‖ * p t * ‖deriv riemannZeta ((((1 / 2 + x : ℝ)) : ℂ) + t * I)‖
        ≤ (Real.sqrt (π / b) * E * (Gp t + Gm t)) * p t * h t := by gcongr
      _ = g t := by simp only [g]; ring
  have hnorm : ‖∫ t in S, fx b α x ((((1 / 2 + x : ℝ)) : ℂ) + t * I)‖ ≤ ∫ t, g t := by
    calc ‖∫ t in S, fx b α x ((((1 / 2 + x : ℝ)) : ℂ) + t * I)‖ ≤ ∫ t in S, g t :=
          norm_integral_le_of_norm_le ig.integrableOn ((ae_restrict_iff' hS).mpr (ae_of_all _ hpt))
      _ ≤ ∫ t, g t := setIntegral_le_integral ig (ae_of_all _ hg0)
  have hIg : ∫ t, g t ≤ Real.sqrt (π / b) * E *
      ((A + B + B * |α|) * Real.exp (c / (2 * b)) * (Cp + Cm + 2 * K0) / 2) := by
    simp only [g]
    rw [integral_const_mul, integral_add ip im]
    have : 0 ≤ Real.sqrt (π / b) * E := by positivity
    calc Real.sqrt (π / b) * E * ((∫ t, Gp t * (h t * p t)) + ∫ t, Gm t * (h t * p t))
        ≤ Real.sqrt (π / b) * E * ((A + B + B * |α|) * Real.exp (c / (2 * b)) * (Cp + K0) / 2
          + (A + B + B * |α|) * Real.exp (c / (2 * b)) * (Cm + K0) / 2) := by gcongr
      _ = _ := by ring
  have hEE : Real.exp (-x ^ 2 / (4 * b)) * E = 1 := by
    simp only [E]; rw [← Real.exp_add]; simp [neg_div]
  calc Real.exp (-x ^ 2 / (4 * b)) * ‖∫ t in S, fx b α x ((((1 / 2 + x : ℝ)) : ℂ) + t * I)‖
      ≤ Real.exp (-x ^ 2 / (4 * b)) * (Real.sqrt (π / b) * E *
          ((A + B + B * |α|) * Real.exp (c / (2 * b)) * (Cp + Cm + 2 * K0) / 2)) := by
        gcongr; exact hnorm.trans hIg
    _ = _ := by rw [show Real.exp (-x ^ 2 / (4 * b)) * (Real.sqrt (π / b) * E *
          ((A + B + B * |α|) * Real.exp (c / (2 * b)) * (Cp + Cm + 2 * K0) / 2))
          = (Real.exp (-x ^ 2 / (4 * b)) * E) * (Real.sqrt (π / b) *
          ((A + B + B * |α|) * Real.exp (c / (2 * b)) * (Cp + Cm + 2 * K0) / 2)) by ring, hEE, one_mul]

/-- **Residue piece.** For `0 < ρ ≤ 1/2`, `ρ ≤ |α|`, and `D` with `(max 0 (η+ρ+x))² ≤ x² + D`:
`e^{-x²/(4b)} ‖Φ_x'(1)‖ ≤ (2/ρ) √(π/b) S_η e^{E/(4b)}`, `E = (1/2+ρ)² − (|α|−ρ)² + D`. -/
theorem residue_bound {b : ℝ} (hb : 0 < b) (α x : ℝ) {η ρ D : ℝ} (hη : 0 < η) (hρ : 0 < ρ) (hρ2 : ρ ≤ 1 / 2)
    (hρα : ρ ≤ |α|) (hD : max 0 (η + ρ + x) ^ 2 ≤ x ^ 2 + D) :
    Real.exp (-x ^ 2 / (4 * b)) * ‖deriv (Phix b α x) 1‖
      ≤ 2 / ρ * Real.sqrt (π / b) * Sz η *
        Real.exp (((1 / 2 + ρ) ^ 2 - (|α| - ρ) ^ 2 + D) / (4 * b)) := by
  set E := ((1 / 2 + ρ) ^ 2 - (|α| - ρ) ^ 2 + D)
  set Cb := Real.exp (x ^ 2 / (4 * b)) * (2 * Real.sqrt (π / b) * Sz η * Real.exp (E / (4 * b)))
  have hS := Sz_nonneg η
  have hsph : ∀ z ∈ Metric.sphere (1 : ℂ) ρ, ‖Phix b α x z‖ ≤ Cb := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    have hre : |z.re - 1| ≤ ρ := by
      have := Complex.abs_re_le_norm (z - 1); rw [hz] at this; simpa using this
    have him : |z.im| ≤ ρ := by
      have := Complex.abs_im_le_norm (z - 1); rw [hz] at this; simpa using this
    have hz' : z = (z.re : ℂ) + z.im * I := (re_add_im z).symm
    have hbz := norm_Phix_le hb α x hη z.re z.im
    rw [← hz'] at hbz
    refine hbz.trans ?_
    have h1 : (z.re - 1 / 2) ^ 2 ≤ (1 / 2 + ρ) ^ 2 := by
      rw [abs_le] at hre
      nlinarith [hre.1, hre.2]
    have hG1 : -(z.im + α) ^ 2 ≤ -(|α| - ρ) ^ 2 := by
      have : |α| - ρ ≤ |z.im + α| := by
        have := abs_sub_abs_le_abs_sub α (-z.im)
        rw [abs_neg, sub_neg_eq_add, add_comm] at this; linarith
      have h0 : 0 ≤ |α| - ρ := by linarith
      nlinarith [sq_abs (z.im + α), pow_le_pow_left₀ h0 this 2]
    have hG2 : -(z.im - α) ^ 2 ≤ -(|α| - ρ) ^ 2 := by
      have : |α| - ρ ≤ |z.im - α| := by
        have := abs_sub_abs_le_abs_sub α z.im
        rw [abs_sub_comm] at this; linarith
      have h0 : 0 ≤ |α| - ρ := by linarith
      nlinarith [sq_abs (z.im - α), pow_le_pow_left₀ h0 this 2]
    have hm : max 0 (1 + η - (z.re - x)) ^ 2 ≤ x ^ 2 + D := by
      rw [abs_le] at hre
      have h1 : max 0 (1 + η - (z.re - x)) ≤ max 0 (η + ρ + x) := max_le_max le_rfl (by linarith [hre.1])
      exact (pow_le_pow_left₀ (le_max_left _ _) h1 2).trans hD
    have e1 : Real.exp ((z.re - 1 / 2) ^ 2 / (4 * b)) * (Real.exp (-(z.im + α) ^ 2 / (4 * b))
        + Real.exp (-(z.im - α) ^ 2 / (4 * b))) * Real.exp (max 0 (1 + η - (z.re - x)) ^ 2 / (4 * b))
        ≤ 2 * Real.exp (x ^ 2 / (4 * b)) * Real.exp (E / (4 * b)) := by
      have a1 : Real.exp ((z.re - 1 / 2) ^ 2 / (4 * b)) * Real.exp (-(z.im + α) ^ 2 / (4 * b))
          * Real.exp (max 0 (1 + η - (z.re - x)) ^ 2 / (4 * b))
          ≤ Real.exp (x ^ 2 / (4 * b)) * Real.exp (E / (4 * b)) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
        rw [show (z.re - 1 / 2) ^ 2 / (4 * b) + -(z.im + α) ^ 2 / (4 * b)
            + max 0 (1 + η - (z.re - x)) ^ 2 / (4 * b)
            = ((z.re - 1 / 2) ^ 2 + -(z.im + α) ^ 2 + max 0 (1 + η - (z.re - x)) ^ 2) / (4 * b) by ring,
          show x ^ 2 / (4 * b) + E / (4 * b) = (x ^ 2 + E) / (4 * b) by ring]
        apply div_le_div_of_nonneg_right _ (by positivity)
        simp only [E]; linarith
      have a2 : Real.exp ((z.re - 1 / 2) ^ 2 / (4 * b)) * Real.exp (-(z.im - α) ^ 2 / (4 * b))
          * Real.exp (max 0 (1 + η - (z.re - x)) ^ 2 / (4 * b))
          ≤ Real.exp (x ^ 2 / (4 * b)) * Real.exp (E / (4 * b)) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
        rw [show (z.re - 1 / 2) ^ 2 / (4 * b) + -(z.im - α) ^ 2 / (4 * b)
            + max 0 (1 + η - (z.re - x)) ^ 2 / (4 * b)
            = ((z.re - 1 / 2) ^ 2 + -(z.im - α) ^ 2 + max 0 (1 + η - (z.re - x)) ^ 2) / (4 * b) by ring,
          show x ^ 2 / (4 * b) + E / (4 * b) = (x ^ 2 + E) / (4 * b) by ring]
        apply div_le_div_of_nonneg_right _ (by positivity)
        simp only [E]; linarith
      nlinarith
    calc Real.sqrt (π / b) * Real.exp ((z.re - 1 / 2) ^ 2 / (4 * b)) *
          (Real.exp (-(z.im + α) ^ 2 / (4 * b)) + Real.exp (-(z.im - α) ^ 2 / (4 * b)))
          * (Sz η * Real.exp (max 0 (1 + η - (z.re - x)) ^ 2 / (4 * b)))
        = Real.sqrt (π / b) * Sz η * (Real.exp ((z.re - 1 / 2) ^ 2 / (4 * b)) *
          (Real.exp (-(z.im + α) ^ 2 / (4 * b)) + Real.exp (-(z.im - α) ^ 2 / (4 * b)))
          * Real.exp (max 0 (1 + η - (z.re - x)) ^ 2 / (4 * b))) := by ring
      _ ≤ Real.sqrt (π / b) * Sz η * (2 * Real.exp (x ^ 2 / (4 * b)) * Real.exp (E / (4 * b))) := by
          gcongr
      _ = Cb := by simp only [Cb]; ring
  have hd := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ
    (differentiable_Phix hb α x).diffContOnCl hsph
  have hEE : Real.exp (-x ^ 2 / (4 * b)) * Real.exp (x ^ 2 / (4 * b)) = 1 := by
    rw [← Real.exp_add]; simp [neg_div]
  calc Real.exp (-x ^ 2 / (4 * b)) * ‖deriv (Phix b α x) 1‖ ≤ Real.exp (-x ^ 2 / (4 * b)) * (Cb / ρ) := by
        gcongr
    _ = _ := by
        simp only [Cb]
        rw [show Real.exp (-x ^ 2 / (4 * b)) * (Real.exp (x ^ 2 / (4 * b)) *
            (2 * Real.sqrt (π / b) * Sz η * Real.exp (E / (4 * b))) / ρ)
            = (Real.exp (-x ^ 2 / (4 * b)) * Real.exp (x ^ 2 / (4 * b))) *
            (2 * Real.sqrt (π / b) * Sz η * Real.exp (E / (4 * b)) / ρ) by ring, hEE]
        field_simp

end FleetSmoothWindow
