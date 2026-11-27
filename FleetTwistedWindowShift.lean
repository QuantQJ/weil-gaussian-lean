import FleetHeadContourStrip
import FleetTwistedWindowGrowth

/-!
# The twisted Möbius polynomial, the twisted window, and the twisted head on the critical line

For a Dirichlet character `χ` mod `N`:

* `MpolyChi χ M w = Σ_{m ≤ M} μ(m) χ(m) m^{-w}` (for `N = 1` this is `Mpoly`: `MpolyChi_modOne`);
* `twistedWindow χ b α = ∫ ‖MpolyChi χ (cut b) (1/2+it)‖² e^{-(t−α)²/(4b)} dt`;
* `headChi χ b α M = (1/2π) ∫ LGw(3/2+it) MpolyChi χ M (3/2+it) (−L'(3/2+it,χ)) dt`
  (the twisted analogue of `FleetHeadContourLine.head_eq_line_integral`).

For `χ ≠ 1` the function `L(·,χ)` is entire, so the contour shift of `FleetHeadContourShift` has
**no residue term** (`headChi_eq_critical_line`):

`headChi χ b α M = (1/2π) ∫ LGw(1/2+it) MpolyChi χ M (1/2+it) (−L'(1/2+it,χ)) dt`.

The linear growth of `L'` (`FleetTwistedWindowGrowth.norm_deriv_LFunction_le`) replaces
`norm_deriv_zeta_le`. Cauchy–Schwarz in the Gaussian weight (`norm_crit_integral_le`) then gives
`norm_headChi_le_of_windows`: `‖headChi‖ ≤ √(π/b)/(2π) · (√(X₁ K(α)) + √(X₂ K(−α)))` from window
bounds `X₁` at `α` and `X₂` at `−α`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace FleetTwistedWindow

open FleetHeadContour RectangleWinding

variable {N : ℕ} [NeZero N]

/-! ## The twisted Möbius polynomial and the twisted window -/

/-- `Σ_{m ≤ M} μ(m) χ(m) m^{-w}` (the `m = 0` term vanishes). -/
def MpolyChi (χ : DirichletCharacter ℂ N) (M : ℕ) (w : ℂ) : ℂ :=
  ∑ m ∈ Finset.range (M + 1), (ArithmeticFunction.moebius m : ℂ) * χ (m : ZMod N) * (m : ℂ) ^ (-w)

/-- **The twisted window** `∫ ‖MpolyChi χ (cut b) (1/2+it)‖² e^{-(t−α)²/(4b)} dt`. -/
def twistedWindow (χ : DirichletCharacter ℂ N) (b α : ℝ) : ℝ :=
  ∫ t : ℝ, ‖MpolyChi χ (FleetFiniteHeadRH.cut b) (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2
    * Real.exp (-(t - α) ^ 2 / (4 * b))

/-- For the character mod `1`, `MpolyChi` is the untwisted `Mpoly`. -/
theorem MpolyChi_modOne (χ : DirichletCharacter ℂ 1) : MpolyChi χ = Mpoly := by
  funext M w
  unfold MpolyChi Mpoly
  refine Finset.sum_congr rfl fun m _ => ?_
  have h : χ (m : ZMod 1) = 1 := congrFun DirichletCharacter.modOne_eq_one m
  rw [h, mul_one]

theorem differentiable_MpolyChi (χ : DirichletCharacter ℂ N) (M : ℕ) :
    Differentiable ℂ (MpolyChi χ M) := by
  unfold MpolyChi
  have : (fun w : ℂ => ∑ m ∈ Finset.range (M + 1),
      (ArithmeticFunction.moebius m : ℂ) * χ (m : ZMod N) * (m : ℂ) ^ (-w))
      = fun w : ℂ => ∑ m ∈ Finset.range (M + 1),
        (fun w : ℂ => (ArithmeticFunction.moebius m : ℂ) * χ (m : ZMod N) * (m : ℂ) ^ (-w)) w := rfl
  rw [this]
  apply Differentiable.fun_sum
  intro m _
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    exact (differentiable_const _).mul
      (fun w => (differentiableAt_neg_iff.mpr differentiableAt_id).const_cpow (Or.inl hm'))

lemma norm_moebius_chi_cpow_le (χ : DirichletCharacter ℂ N) (m : ℕ) {w : ℂ} (hw : 0 ≤ w.re) :
    ‖(ArithmeticFunction.moebius m : ℂ) * χ (m : ZMod N) * (m : ℂ) ^ (-w)‖ ≤ 1 := by
  rw [norm_mul, norm_mul]
  have h0 := norm_moebius_cpow_le m hw
  rw [norm_mul] at h0
  have h1 := DirichletCharacter.norm_le_one χ (m : ZMod N)
  have hp : 0 ≤ ‖(ArithmeticFunction.moebius m : ℂ)‖ := norm_nonneg _
  calc ‖(ArithmeticFunction.moebius m : ℂ)‖ * ‖χ (m : ZMod N)‖ * ‖(m : ℂ) ^ (-w)‖
      ≤ ‖(ArithmeticFunction.moebius m : ℂ)‖ * 1 * ‖(m : ℂ) ^ (-w)‖ := by gcongr
    _ ≤ 1 := by rw [mul_one]; exact h0

theorem norm_MpolyChi_le (χ : DirichletCharacter ℂ N) (M : ℕ) {w : ℂ} (hw : 0 ≤ w.re) :
    ‖MpolyChi χ M w‖ ≤ M + 1 := by
  unfold MpolyChi
  calc _ ≤ ∑ m ∈ Finset.range (M + 1),
        ‖(ArithmeticFunction.moebius m : ℂ) * χ (m : ZMod N) * (m : ℂ) ^ (-w)‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.range (M + 1), (1 : ℝ) :=
        Finset.sum_le_sum fun m _ => norm_moebius_chi_cpow_le χ m hw
    _ = M + 1 := by simp

/-! ## `L'(·,χ)` on vertical lines -/

/-- `‖L'(x+it,χ)‖ ≤ (20N|x| + 5N + 4) + 20N|t|` for `x ≥ 1/2`. -/
theorem norm_deriv_L_line (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {x : ℝ} (hx : 1 / 2 ≤ x) (t : ℝ) :
    ‖deriv (DirichletCharacter.LFunction χ) ((x : ℂ) + t * I)‖
      ≤ (20 * N * |x| + 5 * N + 4) + 20 * N * |t| := by
  have hre : ((x : ℂ) + t * I).re = x := by simp
  have h := norm_deriv_LFunction_le χ hχ (s := (x : ℂ) + t * I) (by rw [hre]; exact hx)
  have h3 : ‖(x : ℂ) + t * I‖ ≤ |x| + |t| := by
    calc ‖(x : ℂ) + t * I‖ ≤ ‖(x : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = |x| + |t| := by simp
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  nlinarith

lemma continuous_deriv_L (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    Continuous (deriv (DirichletCharacter.LFunction χ)) :=
  ((DirichletCharacter.differentiable_LFunction hχ).contDiff (n := 1)).continuous_deriv le_rfl

/-- **Integrability on a vertical line** `Re = x ≥ 1/2` of `LGw · h · (−L')` for bounded continuous `h`. -/
theorem integrable_line_chi (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {b : ℝ} (hb : 0 < b) (α : ℝ)
    {x : ℝ} (hx : 1 / 2 ≤ x) {h : ℝ → ℂ} (hh : Continuous h) {H : ℝ} (hH : ∀ t, ‖h t‖ ≤ H) :
    Integrable (fun t : ℝ => LGw b α ((x : ℂ) + t * I) * h t
      * (-deriv (DirichletCharacter.LFunction χ) ((x : ℂ) + t * I))) := by
  have hH0 : 0 ≤ H := (norm_nonneg _).trans (hH 0)
  set K := Real.sqrt (π / b) * Real.exp ((x - 1 / 2) ^ 2 / (4 * b)) with hK
  have hK0 : 0 ≤ K := by positivity
  set A := 20 * N * |x| + 5 * N + 4 with hA
  refine integrable_of_gauss_bound hb α (K * H * A) (K * H * (20 * N)) ?_ (fun t => ?_)
  · exact (((differentiable_LGw b α).continuous.comp (continuous_line x)).mul hh).mul
      ((continuous_deriv_L χ hχ).comp (continuous_line x)).neg
  · have h1 := norm_LGw_le b α x t
    have h2 := hH t
    have h3 := norm_deriv_L_line χ hχ hx t
    have hE : 0 ≤ Real.exp (-(t + α) ^ 2 / (4 * b)) + Real.exp (-(t - α) ^ 2 / (4 * b)) := by positivity
    rw [norm_mul, norm_mul, norm_neg]
    calc ‖LGw b α ((x : ℂ) + t * I)‖ * ‖h t‖ * ‖deriv (DirichletCharacter.LFunction χ) ((x : ℂ) + t * I)‖
        ≤ (K * (Real.exp (-(t + α) ^ 2 / (4 * b)) + Real.exp (-(t - α) ^ 2 / (4 * b)))) * H
          * (A + 20 * N * |t|) := by gcongr
    _ = (K * H * A + K * H * (20 * N) * |t|) *
          (Real.exp (-(t + α) ^ 2 / (4 * b)) + Real.exp (-(t - α) ^ 2 / (4 * b))) := by ring

/-! ## The contour shift for an entire integrand -/

/-- **Line shift without residue.** For an entire `f` that is integrable on `Re = 1/2` and `Re = 3/2`
and whose horizontal integrals over `[1/2, 3/2]` at heights `±T` tend to `0`,
`∫ f(3/2 + iy) dy = ∫ f(1/2 + iy) dy`. -/
theorem line_shift_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h3 : Integrable (fun y : ℝ => f (((3 / 2 : ℝ) : ℂ) + y * I)))
    (h1 : Integrable (fun y : ℝ => f (((1 / 2 : ℝ) : ℂ) + y * I)))
    (htop : Tendsto (fun T : ℝ => ∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ), f ((x : ℂ) + T * I)) atTop (𝓝 0))
    (hbot : Tendsto (fun T : ℝ => ∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ), f ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
      atTop (𝓝 0)) :
    (∫ y : ℝ, f (((3 / 2 : ℝ) : ℂ) + y * I)) = ∫ y : ℝ, f (((1 / 2 : ℝ) : ℂ) + y * I) := by
  have hV3 := intervalIntegral_tendsto_integral h3 tendsto_neg_atTop_atBot tendsto_id
  have hV1 := intervalIntegral_tendsto_integral h1 tendsto_neg_atTop_atBot tendsto_id
  have hlim : Tendsto (fun T : ℝ => rectInt f (1 / 2) (3 / 2) (-T) T) atTop
      (𝓝 (0 - 0 + I * (∫ y : ℝ, f (((3 / 2 : ℝ) : ℂ) + y * I))
        - I * (∫ y : ℝ, f (((1 / 2 : ℝ) : ℂ) + y * I)))) := by
    unfold rectInt
    exact ((hbot.sub htop).add (hV3.const_mul I)).sub (hV1.const_mul I)
  have hconst : ∀ T : ℝ, rectInt f (1 / 2) (3 / 2) (-T) T = 0 :=
    fun T => rectInt_eq_zero_of_differentiable hf _ _ _ _
  simp only [hconst] at hlim
  have heq := tendsto_nhds_unique tendsto_const_nhds hlim
  have hI : I ≠ 0 := I_ne_zero
  have : I * ((∫ y : ℝ, f (((3 / 2 : ℝ) : ℂ) + y * I)) - (∫ y : ℝ, f (((1 / 2 : ℝ) : ℂ) + y * I)))
      = I * 0 := by rw [mul_sub]; linear_combination -heq
  exact sub_eq_zero.mp (mul_left_cancel₀ hI this)

/-! ## The twisted head and its critical-line form -/

/-- `Φ_χ(w) = LG(1/2 − w) · MpolyChi χ M w`. -/
def PhiChi (χ : DirichletCharacter ℂ N) (b α : ℝ) (M : ℕ) (w : ℂ) : ℂ := LGw b α w * MpolyChi χ M w

/-- **The twisted head** `(1/2π) ∫ Φ_χ(3/2+it) (−L'(3/2+it,χ)) dt`. -/
def headChi (χ : DirichletCharacter ℂ N) (b α : ℝ) (M : ℕ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ t : ℝ, PhiChi χ b α M (((3 / 2 : ℝ) : ℂ) + t * I)
    * (-deriv (DirichletCharacter.LFunction χ) (((3 / 2 : ℝ) : ℂ) + t * I))

lemma integrable_PhiChi_line (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {b : ℝ} (hb : 0 < b) (α : ℝ)
    (M : ℕ) {x : ℝ} (hx : 1 / 2 ≤ x) :
    Integrable (fun y : ℝ => PhiChi χ b α M ((x : ℂ) + y * I)
      * (-deriv (DirichletCharacter.LFunction χ) ((x : ℂ) + y * I))) := by
  have h := integrable_line_chi χ hχ hb α hx (h := fun t => MpolyChi χ M ((x : ℂ) + t * I))
    ((differentiable_MpolyChi χ M).continuous.comp (continuous_line x)) (H := M + 1)
    (fun t => norm_MpolyChi_le χ M (by simp; linarith))
  simpa [PhiChi] using h

lemma norm_fChi_strip_le (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {b : ℝ} (hb : 0 < b) (α : ℝ)
    (M : ℕ) {x y : ℝ} (hx : x ∈ Set.uIcc (1 / 2 : ℝ) (3 / 2)) :
    ‖PhiChi χ b α M ((x : ℂ) + y * I) * (-deriv (DirichletCharacter.LFunction χ) ((x : ℂ) + y * I))‖
      ≤ Real.sqrt (π / b) * Real.exp (1 / (4 * b)) * (M + 1) * ((35 * N + 4) + 20 * N * |y|) *
        (Real.exp (-(y + α) ^ 2 / (4 * b)) + Real.exp (-(y - α) ^ 2 / (4 * b))) := by
  rw [Set.uIcc_of_le (by norm_num)] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hre : ((x : ℂ) + y * I).re = x := by simp
  have hL := norm_LGw_le b α x y
  have hM := norm_MpolyChi_le χ M (w := (x : ℂ) + y * I) (by rw [hre]; linarith)
  have hZ := norm_deriv_L_line χ hχ hx1 y
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hZ' : ‖deriv (DirichletCharacter.LFunction χ) ((x : ℂ) + y * I)‖ ≤ (35 * N + 4) + 20 * N * |y| := by
    rw [abs_of_pos (by linarith : (0 : ℝ) < x)] at hZ
    nlinarith
  have hE : Real.exp ((x - 1 / 2) ^ 2 / (4 * b)) ≤ Real.exp (1 / (4 * b)) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have hG : 0 ≤ Real.exp (-(y + α) ^ 2 / (4 * b)) + Real.exp (-(y - α) ^ 2 / (4 * b)) := by positivity
  unfold PhiChi
  rw [norm_mul, norm_mul, norm_neg]
  calc ‖LGw b α ((x : ℂ) + y * I)‖ * ‖MpolyChi χ M ((x : ℂ) + y * I)‖
        * ‖deriv (DirichletCharacter.LFunction χ) ((x : ℂ) + y * I)‖
      ≤ (Real.sqrt (π / b) * Real.exp (1 / (4 * b)) *
          (Real.exp (-(y + α) ^ 2 / (4 * b)) + Real.exp (-(y - α) ^ 2 / (4 * b)))) * (M + 1)
        * ((35 * N + 4) + 20 * N * |y|) := by
        gcongr
        calc ‖LGw b α ((x : ℂ) + y * I)‖ ≤ _ := hL
          _ ≤ _ := by gcongr
    _ = _ := by ring

lemma tendsto_horizontal_chi (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {b : ℝ} (hb : 0 < b) (α : ℝ)
    (M : ℕ) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    Tendsto (fun T : ℝ => ∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ),
      PhiChi χ b α M ((x : ℂ) + ((σ * T : ℝ) : ℂ) * I)
        * (-deriv (DirichletCharacter.LFunction χ) ((x : ℂ) + ((σ * T : ℝ) : ℂ) * I))) atTop (𝓝 0) := by
  set C := Real.sqrt (π / b) * Real.exp (1 / (4 * b)) * (M + 1) with hC
  set A : ℝ := 35 * N + 4 with hA
  set B : ℝ := 20 * N with hB
  have hmaj : Tendsto (fun T : ℝ => C * ((A + B * T) * Real.exp (-(T - (-α)) ^ 2 / (4 * b))
      + (A + B * T) * Real.exp (-(T - α) ^ 2 / (4 * b)))) atTop (𝓝 0) := by
    have := ((tendsto_lin_gauss hb (-α) A B).add (tendsto_lin_gauss hb α A B)).const_mul C
    simpa using this
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hmaj
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hσT : |σ * T| = T := by
    rcases hσ with rfl | rfl <;> simp [abs_of_pos (by linarith : (0 : ℝ) < T)]
  have hb' := intervalIntegral.norm_integral_le_of_norm_le_const (a := (1 / 2 : ℝ)) (b := 3 / 2)
    (C := C * (A + B * T) * (Real.exp (-((σ * T) + α) ^ 2 / (4 * b))
      + Real.exp (-((σ * T) - α) ^ 2 / (4 * b))))
    (f := fun x : ℝ => PhiChi χ b α M ((x : ℂ) + ((σ * T : ℝ) : ℂ) * I)
        * (-deriv (DirichletCharacter.LFunction χ) ((x : ℂ) + ((σ * T : ℝ) : ℂ) * I)))
    (fun x hx => by
      have := norm_fChi_strip_le χ hχ hb α M (x := x) (y := σ * T) (Set.uIoc_subset_uIcc hx)
      rw [hσT] at this
      simpa [hC, hA, hB, mul_assoc] using this)
  refine hb'.trans (le_of_eq ?_)
  have hsym : Real.exp (-((σ * T) + α) ^ 2 / (4 * b)) + Real.exp (-((σ * T) - α) ^ 2 / (4 * b))
      = Real.exp (-(T - (-α)) ^ 2 / (4 * b)) + Real.exp (-(T - α) ^ 2 / (4 * b)) := by
    rcases hσ with rfl | rfl
    · ring_nf
    · ring_nf; try rw [add_comm]
  rw [hsym]
  norm_num
  ring

/-- **The twisted contour identity** (no residue: `L(·,χ)` is entire for `χ ≠ 1`):
`headChi χ b α M = (1/2π) ∫ LGw(1/2+it) MpolyChi χ M (1/2+it) (−L'(1/2+it,χ)) dt`. -/
theorem headChi_eq_critical_line (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {b : ℝ} (hb : 0 < b)
    (α : ℝ) (M : ℕ) :
    headChi χ b α M = (1 / (2 * π) : ℂ) *
      ∫ t : ℝ, LGw b α (((1 / 2 : ℝ) : ℂ) + t * I) * MpolyChi χ M (((1 / 2 : ℝ) : ℂ) + t * I)
        * (-deriv (DirichletCharacter.LFunction χ) (((1 / 2 : ℝ) : ℂ) + t * I)) := by
  have hdiff : Differentiable ℂ (fun s => PhiChi χ b α M s * (-deriv (DirichletCharacter.LFunction χ) s)) := by
    have hd2 : Differentiable ℂ (deriv (DirichletCharacter.LFunction χ)) := by
      have h := (contDiff_succ_iff_deriv (n := 1)).mp
        ((DirichletCharacter.differentiable_LFunction hχ).contDiff (n := 1 + 1))
      exact h.2.2.differentiable (by norm_num)
    exact ((differentiable_LGw b α).mul (differentiable_MpolyChi χ M)).mul hd2.neg
  have hshift := line_shift_entire hdiff
    (integrable_PhiChi_line χ hχ hb α M (x := 3 / 2) (by norm_num))
    (integrable_PhiChi_line χ hχ hb α M (x := 1 / 2) (by norm_num))
    (by simpa using tendsto_horizontal_chi χ hχ hb α M 1 (Or.inl rfl))
    (by simpa using tendsto_horizontal_chi χ hχ hb α M (-1) (Or.inr rfl))
  unfold headChi
  rw [hshift]
  simp only [PhiChi]

/-! ## Windows of functions of linear growth, and Cauchy–Schwarz -/

/-- The window constant for a function bounded by `A + B|t|`. -/
def Kc (A B β : ℝ) : ℝ := (2 * A ^ 2 + 4 * B ^ 2 * β ^ 2) * Real.sqrt (4 * π) + 32 * B ^ 2 * Real.sqrt (8 * π)

lemma Kc_nonneg (A B β : ℝ) : 0 ≤ Kc A B β := by unfold Kc; positivity

/-- **Window of a function of linear growth.** `‖g t‖ ≤ A + B|t|` (`A, B ≥ 0`) gives
`∫ ‖g t‖² e^{-(t−β)²/4b} dt ≤ Kc A B β` for `0 < b ≤ 1`. -/
theorem window_of_linear {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (β : ℝ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    {g : ℝ → ℂ} (hg : Continuous g) (hgb : ∀ t, ‖g t‖ ≤ A + B * |t|) :
    Integrable (fun t : ℝ => ‖g t‖ ^ 2 * Real.exp (-(t - β) ^ 2 / (4 * b))) ∧
    ∫ t : ℝ, ‖g t‖ ^ 2 * Real.exp (-(t - β) ^ 2 / (4 * b)) ≤ Kc A B β := by
  set G : ℝ → ℝ := fun t => (2 * A ^ 2 + 4 * B ^ 2 * β ^ 2) * Real.exp (-(t - β) ^ 2 / (4 * b))
    + (32 * B ^ 2) * Real.exp (-(t - β) ^ 2 / (8 * b)) with hG
  have hGi : Integrable G :=
    ((integrable_gauss_scale (by positivity) β).const_mul _).add
      ((integrable_gauss_scale (by positivity) β).const_mul _)
  have hpt : ∀ t : ℝ, ‖g t‖ ^ 2 * Real.exp (-(t - β) ^ 2 / (4 * b)) ≤ G t := by
    intro t
    have h0 := norm_nonneg (g t)
    have hsq : ‖g t‖ ^ 2 ≤ (2 * A ^ 2 + 4 * B ^ 2 * β ^ 2) + 4 * B ^ 2 * (t - β) ^ 2 := by
      have h1 : ‖g t‖ ^ 2 ≤ (A + B * |t|) ^ 2 := pow_le_pow_left₀ h0 (hgb t) 2
      have h2 : (A + B * |t|) ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 * t ^ 2 := by
        nlinarith [sq_nonneg (A - B * |t|), _root_.sq_abs t]
      nlinarith [sq_nonneg (t - 2 * β), sq_nonneg B]
    have hE := Real.exp_pos (-(t - β) ^ 2 / (4 * b))
    have hs := sq_gauss_le hb (t - β)
    have hE8 := Real.exp_pos (-(t - β) ^ 2 / (8 * b))
    have hb8 : 8 * b * Real.exp (-(t - β) ^ 2 / (8 * b)) ≤ 8 * Real.exp (-(t - β) ^ 2 / (8 * b)) := by
      nlinarith
    have hB2 : 0 ≤ 4 * B ^ 2 := by positivity
    calc ‖g t‖ ^ 2 * Real.exp (-(t - β) ^ 2 / (4 * b))
        ≤ ((2 * A ^ 2 + 4 * B ^ 2 * β ^ 2) + 4 * B ^ 2 * (t - β) ^ 2) * Real.exp (-(t - β) ^ 2 / (4 * b)) :=
          mul_le_mul_of_nonneg_right hsq hE.le
      _ = (2 * A ^ 2 + 4 * B ^ 2 * β ^ 2) * Real.exp (-(t - β) ^ 2 / (4 * b))
          + 4 * B ^ 2 * ((t - β) ^ 2 * Real.exp (-(t - β) ^ 2 / (4 * b))) := by ring
      _ ≤ G t := by
          simp only [hG]
          have := mul_le_mul_of_nonneg_left (hs.trans hb8) hB2
          nlinarith
  have hint : Integrable (fun t : ℝ => ‖g t‖ ^ 2 * Real.exp (-(t - β) ^ 2 / (4 * b))) := by
    refine Integrable.mono' hGi ?_ (ae_of_all _ fun t => ?_)
    · exact ((hg.norm.pow 2).mul (by fun_prop)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, _root_.abs_of_nonneg (by positivity)]
      exact hpt t
  refine ⟨hint, ?_⟩
  calc ∫ t : ℝ, ‖g t‖ ^ 2 * Real.exp (-(t - β) ^ 2 / (4 * b))
      ≤ ∫ t, G t := integral_mono hint hGi hpt
    _ = (2 * A ^ 2 + 4 * B ^ 2 * β ^ 2) * Real.sqrt (π * (4 * b)) + 32 * B ^ 2 * Real.sqrt (π * (8 * b)) := by
        simp only [hG]
        rw [integral_add ((integrable_gauss_scale (by positivity) β).const_mul _)
          ((integrable_gauss_scale (by positivity) β).const_mul _), integral_const_mul, integral_const_mul,
          integral_gauss_scale (by positivity), integral_gauss_scale (by positivity)]
    _ ≤ Kc A B β := by
        unfold Kc
        have h4 : Real.sqrt (π * (4 * b)) ≤ Real.sqrt (4 * π) := Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])
        have h8 : Real.sqrt (π * (8 * b)) ≤ Real.sqrt (8 * π) := Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])
        have hc : 0 ≤ 2 * A ^ 2 + 4 * B ^ 2 * β ^ 2 := by positivity
        have hc2 : 0 ≤ 32 * B ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h4 hc, mul_le_mul_of_nonneg_left h8 hc2]

/-- **Cauchy–Schwarz on the critical line.** For continuous `m, d` with `‖m‖ ≤ H` and
`‖d t‖ ≤ A + B|t|`, and window bounds `∫ ‖m‖² e^{-(t∓α)²/4b} ≤ X₁, X₂`:
`‖∫ LGw(1/2+it) m(t) d(t) dt‖ ≤ √(π/b) (√X₁ √(Kc A B α) + √X₂ √(Kc A B (−α)))`. -/
theorem norm_crit_integral_le {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (α : ℝ) {m d : ℝ → ℂ}
    (cm : Continuous m) (cd : Continuous d) {H : ℝ} (hH : ∀ t, ‖m t‖ ≤ H)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hd : ∀ t, ‖d t‖ ≤ A + B * |t|)
    {X₁ X₂ : ℝ} (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂)
    (h₁ : ∫ t : ℝ, ‖m t‖ ^ 2 * Real.exp (-(t - α) ^ 2 / (4 * b)) ≤ X₁)
    (h₂ : ∫ t : ℝ, ‖m t‖ ^ 2 * Real.exp (-(t - -α) ^ 2 / (4 * b)) ≤ X₂) :
    ‖∫ t : ℝ, LGw b α (((1 / 2 : ℝ) : ℂ) + t * I) * m t * d t‖
      ≤ Real.sqrt (π / b) * (Real.sqrt X₁ * Real.sqrt (Kc A B α) + Real.sqrt X₂ * Real.sqrt (Kc A B (-α))) := by
  set sq := Real.sqrt (π / b) with hsq
  have hsq0 : 0 ≤ sq := Real.sqrt_nonneg _
  have hH0 : 0 ≤ H := (norm_nonneg _).trans (hH 0)
  set wp : ℝ → ℝ := fun t => Real.exp (-(t - -α) ^ 2 / (4 * b)) with hwp
  set wm : ℝ → ℝ := fun t => Real.exp (-(t - α) ^ 2 / (4 * b)) with hwm
  set Mn : ℝ → ℝ := fun t => ‖m t‖ with hMn
  set Zn : ℝ → ℝ := fun t => ‖d t‖ with hZn
  have cMn : Continuous Mn := cm.norm
  have cZn : Continuous Zn := cd.norm
  have cwp : Continuous wp := by simp only [hwp]; fun_prop
  have cwm : Continuous wm := by simp only [hwm]; fun_prop
  have hwp0 : ∀ t, 0 ≤ wp t := fun t => (Real.exp_pos _).le
  have hwm0 : ∀ t, 0 ≤ wm t := fun t => (Real.exp_pos _).le
  have iMw : ∀ β : ℝ, Integrable (fun t => Mn t ^ 2 * Real.exp (-(t - β) ^ 2 / (4 * b))) := by
    intro β
    refine Integrable.mono' ((integrable_gauss_scale (d := 4 * b) (by positivity) β).const_mul (H ^ 2))
      ((cMn.pow 2).mul (by fun_prop)).aestronglyMeasurable (ae_of_all _ fun t => ?_)
    rw [Real.norm_eq_abs, _root_.abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hH t) 2) (Real.exp_pos _).le
  have iMp : Integrable (fun t => Mn t ^ 2 * wp t) := iMw (-α)
  have iMm : Integrable (fun t => Mn t ^ 2 * wm t) := iMw α
  have zp := window_of_linear hb hb1 (-α) hA hB cd hd
  have zm := window_of_linear hb hb1 α hA hB cd hd
  have iZp : Integrable (fun t => Zn t ^ 2 * wp t) := zp.1
  have iZm : Integrable (fun t => Zn t ^ 2 * wm t) := zm.1
  have amgm : ∀ t, Mn t * Zn t ≤ (Mn t ^ 2 + Zn t ^ 2) / 2 := fun t => by
    nlinarith [sq_nonneg (Mn t - Zn t)]
  have iprod : ∀ w : ℝ → ℝ, Continuous w → (∀ t, 0 ≤ w t) →
      Integrable (fun t => Mn t ^ 2 * w t) → Integrable (fun t => Zn t ^ 2 * w t) →
      Integrable (fun t => w t * (Mn t * Zn t)) := by
    intro w cw hw0 iM iZ
    refine Integrable.mono' ((iM.add iZ).div_const 2)
      ((cw.mul (cMn.mul cZn)).aestronglyMeasurable) (ae_of_all _ fun t => ?_)
    have hn : 0 ≤ w t * (Mn t * Zn t) :=
      mul_nonneg (hw0 t) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    have := mul_le_mul_of_nonneg_left (amgm t) (hw0 t)
    calc w t * (Mn t * Zn t) ≤ w t * ((Mn t ^ 2 + Zn t ^ 2) / 2) := this
      _ = (Mn t ^ 2 * w t + Zn t ^ 2 * w t) / 2 := by ring
  have iHp := iprod wp cwp hwp0 iMp iZp
  have iHm := iprod wm cwm hwm0 iMm iZm
  have cs : ∀ w : ℝ → ℝ, (∀ t, 0 ≤ w t) →
      Integrable (fun t => Mn t ^ 2 * w t) → Integrable (fun t => Zn t ^ 2 * w t) →
      Integrable (fun t => w t * (Mn t * Zn t)) → ∀ X Z : ℝ, 0 ≤ X → 0 ≤ Z →
      ∫ t, Mn t ^ 2 * w t ≤ X → ∫ t, Zn t ^ 2 * w t ≤ Z →
      ∫ t, w t * (Mn t * Zn t) ≤ Real.sqrt X * Real.sqrt Z := by
    intro w hw0 iM iZ iH X Z hX hZ0 hMX hZX
    refine le_sqrt_mul_of_forall hX hZ0 fun l hl => ?_
    have hpt : ∀ t, w t * (Mn t * Zn t)
        ≤ (l / 2) * (Mn t ^ 2 * w t) + (1 / (2 * l)) * (Zn t ^ 2 * w t) := by
      intro t
      have hsqd : l * Mn t ^ 2 + Zn t ^ 2 / l - 2 * (Mn t * Zn t) = (l * Mn t - Zn t) ^ 2 / l := by
        field_simp; ring
      have hnn : 0 ≤ (l * Mn t - Zn t) ^ 2 / l := div_nonneg (sq_nonneg _) hl.le
      have hk : Mn t * Zn t ≤ (l * Mn t ^ 2 + Zn t ^ 2 / l) / 2 := by linarith
      calc w t * (Mn t * Zn t) ≤ w t * ((l * Mn t ^ 2 + Zn t ^ 2 / l) / 2) :=
            mul_le_mul_of_nonneg_left hk (hw0 t)
        _ = (l / 2) * (Mn t ^ 2 * w t) + (1 / (2 * l)) * (Zn t ^ 2 * w t) := by
            field_simp
    have hI : ∫ t, w t * (Mn t * Zn t)
        ≤ (l / 2) * (∫ t, Mn t ^ 2 * w t) + (1 / (2 * l)) * ∫ t, Zn t ^ 2 * w t := by
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add (iM.const_mul _) (iZ.const_mul _)]
      exact integral_mono iH ((iM.const_mul _).add (iZ.const_mul _)) hpt
    have hl2 : 0 ≤ l / 2 := by positivity
    have hl3 : 0 ≤ 1 / (2 * l) := by positivity
    have e : Z / l = 2 * ((1 / (2 * l)) * Z) := by field_simp
    have hA' := mul_le_mul_of_nonneg_left hMX hl2
    have hB' := mul_le_mul_of_nonneg_left hZX hl3
    rw [e]
    nlinarith
  have csp := cs wp hwp0 iMp iZp iHp X₂ (Kc A B (-α)) hX₂ (Kc_nonneg _ _ _) h₂ zp.2
  have csm := cs wm hwm0 iMm iZm iHm X₁ (Kc A B α) hX₁ (Kc_nonneg _ _ _) h₁ zm.2
  set F : ℝ → ℂ := fun t => LGw b α (((1 / 2 : ℝ) : ℂ) + t * I) * m t * d t with hF
  have hFG : ∀ t, ‖F t‖ ≤ sq * (wp t * (Mn t * Zn t)) + sq * (wm t * (Mn t * Zn t)) := by
    intro t
    have hL := norm_LGw_le b α (1 / 2) t
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
      Real.exp_zero, mul_one] at hL
    have hwpe : Real.exp (-(t + α) ^ 2 / (4 * b)) = wp t := by simp only [hwp, sub_neg_eq_add]
    rw [hwpe] at hL
    have hMn0 : 0 ≤ Mn t := norm_nonneg _
    have hZn0 : 0 ≤ Zn t := norm_nonneg _
    simp only [hF, norm_mul]
    change ‖LGw b α (((1 / 2 : ℝ) : ℂ) + t * I)‖ * Mn t * Zn t ≤ _
    calc ‖LGw b α (((1 / 2 : ℝ) : ℂ) + t * I)‖ * Mn t * Zn t
        ≤ (sq * (wp t + wm t)) * Mn t * Zn t := by
          apply mul_le_mul_of_nonneg_right _ hZn0
          apply mul_le_mul_of_nonneg_right _ hMn0
          simpa [hwm] using hL
      _ = _ := by ring
  have hFi : Integrable F := by
    refine Integrable.mono' ((iHp.const_mul sq).add (iHm.const_mul sq)) ?_ (ae_of_all _ hFG)
    exact ((((differentiable_LGw b α).continuous.comp (continuous_line (1 / 2))).mul cm).mul
      cd).aestronglyMeasurable
  calc ‖∫ t, F t‖ ≤ ∫ t, ‖F t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, (sq * (wp t * (Mn t * Zn t)) + sq * (wm t * (Mn t * Zn t))) :=
        integral_mono hFi.norm ((iHp.const_mul _).add (iHm.const_mul _)) hFG
    _ = sq * (∫ t, wp t * (Mn t * Zn t)) + sq * ∫ t, wm t * (Mn t * Zn t) := by
        rw [integral_add (iHp.const_mul _) (iHm.const_mul _), integral_const_mul, integral_const_mul]
    _ ≤ sq * (Real.sqrt X₂ * Real.sqrt (Kc A B (-α))) + sq * (Real.sqrt X₁ * Real.sqrt (Kc A B α)) :=
        add_le_add (mul_le_mul_of_nonneg_left csp hsq0) (mul_le_mul_of_nonneg_left csm hsq0)
    _ = _ := by ring

/-- **The twisted head from the two twisted windows** (`χ ≠ 1`, `0 < b ≤ 1`):
`‖headChi χ b α (cut b)‖ ≤ √(π/b)/(2π) (√X₁ √(Kc A B α) + √X₂ √(Kc A B (−α)))`, with
`A = 15N + 4`, `B = 20N`, `X₁ ≥ twistedWindow χ b α`, `X₂ ≥ twistedWindow χ b (−α)`. -/
theorem norm_headChi_le_of_windows (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {b : ℝ} (hb : 0 < b)
    (hb1 : b ≤ 1) (α : ℝ) {X₁ X₂ : ℝ} (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂)
    (h₁ : twistedWindow χ b α ≤ X₁) (h₂ : twistedWindow χ b (-α) ≤ X₂) :
    ‖headChi χ b α (FleetFiniteHeadRH.cut b)‖ ≤ Real.sqrt (π / b) / (2 * π) *
      (Real.sqrt X₁ * Real.sqrt (Kc (15 * N + 4) (20 * N) α)
        + Real.sqrt X₂ * Real.sqrt (Kc (15 * N + 4) (20 * N) (-α))) := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hd : ∀ t : ℝ, ‖-deriv (DirichletCharacter.LFunction χ) (((1 / 2 : ℝ) : ℂ) + t * I)‖
      ≤ (15 * N + 4) + 20 * N * |t| := by
    intro t
    rw [norm_neg]
    have := norm_deriv_L_line χ hχ (x := 1 / 2) le_rfl t
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
    linarith
  have hmain := norm_crit_integral_le hb hb1 α
    (m := fun t => MpolyChi χ (FleetFiniteHeadRH.cut b) (((1 / 2 : ℝ) : ℂ) + t * I))
    (d := fun t => -deriv (DirichletCharacter.LFunction χ) (((1 / 2 : ℝ) : ℂ) + t * I))
    ((differentiable_MpolyChi χ _).continuous.comp (continuous_line _))
    ((continuous_deriv_L χ hχ).comp (continuous_line _)).neg
    (H := FleetFiniteHeadRH.cut b + 1) (fun t => norm_MpolyChi_le χ _ (by simp))
    (by positivity) (by positivity) hd hX₁ hX₂ h₁ h₂
  rw [headChi_eq_critical_line χ hχ hb α, norm_mul]
  have hc : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    rw [show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hc]
  calc 1 / (2 * π) * ‖∫ t : ℝ, LGw b α (((1 / 2 : ℝ) : ℂ) + t * I)
        * MpolyChi χ (FleetFiniteHeadRH.cut b) (((1 / 2 : ℝ) : ℂ) + t * I)
        * (-deriv (DirichletCharacter.LFunction χ) (((1 / 2 : ℝ) : ℂ) + t * I))‖
      ≤ 1 / (2 * π) * (Real.sqrt (π / b) * (Real.sqrt X₁ * Real.sqrt (Kc (15 * N + 4) (20 * N) α)
        + Real.sqrt X₂ * Real.sqrt (Kc (15 * N + 4) (20 * N) (-α)))) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = _ := by ring

end FleetTwistedWindow
