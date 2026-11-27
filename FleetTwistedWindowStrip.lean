import FleetTwistedWindowDetect

/-!
# Twisted window rate ⇒ zero strip for `L(s,χ)`, and the family version

For a nonprincipal Dirichlet character `χ` mod `N`:

* `TwistedWindowRate χ c` : for every `α ∈ ℝ` there is `C` with `twistedWindow χ b α ≤ C e^{c/b}`
  (`0 < b ≤ 1`).
* `norm_primeLine_le_head` : the Gaussian prime line `∫ LGw(3/2+it) (L'/L)(3/2+it,χ) dt` differs from
  `2π · headChi χ b α (cut b)` by at most `√(π/b) · 10√(4π) K'` (the Möbius tail `Σ_{m > cut b}`,
  through `1/L = Σ μχ m^{-w}` on `Re w = 3/2`).
* `zeros_right_of_twisted_window_rate` : rate `c` ⇒ every zero of `L(·,χ)` with `Re ρ > 1/2` has
  `Re ρ − 1/2 ≤ √(2c)`.
* `twistedWindow_inv` : `twistedWindow χ⁻¹ b α = twistedWindow χ b (−α)`, so the rate passes to `χ⁻¹`.
* `zeros_in_strip_of_twisted_window_rate` : for **primitive** `χ ≠ 1`, every zero with `Re ρ > 0` has
  `|Re ρ − 1/2| ≤ √(2c)` (functional equation `IsPrimitive.completedLFunction_one_sub`).
* `betaStar_le_of_uniform_rate` (family) : for a family of nonprincipal characters with a common rate `c`,
  `β* = sup({1/2} ∪ {Re ρ : 1/2 ≤ Re ρ ≤ 1, L(ρ,χᵢ) = 0}) ≤ 1/2 + √(2c)`.
* `familyDev_le_of_uniform_rate` (family, primitive) : `D = sup |Re ρ − 1/2|` over the zeros with
  `Re ρ > 0` of all members is `≤ √(2c)`.
* `betaStarWithZeta_le` : the same `β*` bound for `{ζ} ∪` family, with `ζ` entering through the existing
  `FleetHeadContour.zeros_in_strip_of_window_rate`.

**ζ-specific steps of the ζ chain and their replacements here.**
* Pole of `ζ` at `1` (residue term `Φ'(1)` in `head_eq_critical_line`, its Cauchy bound, and the pole term
  of the explicit formula): `L(·,χ)` is entire for `χ ≠ 1` (Mathlib `differentiable_LFunction`), so the
  shift has no residue (`headChi_eq_critical_line`) and the bound has no polynomial loss in `1/b`.
* Growth of `ζ'` on `Re ≥ 1/2` (Euler–Maclaurin, `ZetaGrowth`): Abel summation with `|Σ_{m<n} χ(m)| ≤ N`
  (`FleetTwistedWindowGrowth`).
* Möbius tail of the head (`FleetMollifierTail`, `primeSumSym_sub_head`): `1/L = Σ μχ m^{-w}` on
  `Re w = 3/2` (Mathlib `LSeries.mul_mu_eq_one`), `norm_primeLine_le_head`.
* Zero side (global Gaussian explicit formula with the archimedean term, zero counting, `Index`):
  replaced by the finite-rectangle argument `zero_detect`, which needs only `L` entire, `L ≠ 0` on
  `Re ≥ 1` (Mathlib `LFunction_ne_zero_of_one_le_re`) and `L'/L` bounded on `Re = 3/2`
  (Mathlib `LSeries_twist_vonMangoldt_eq`).
* Low centres `|α| < 1/2` (verified zero-free region `VerifiedTo (3/2)` for `ζ`): not needed (no pole);
  the rate is assumed at every `α ∈ ℝ`.
* Functional equation (left half of the strip): Mathlib `IsPrimitive.completedLFunction_one_sub`, which
  sends a zero of `L(·,χ)` to a zero of `L(·,χ⁻¹)`; `twistedWindow_inv` carries the rate to `χ⁻¹`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Complex Filter Topology Set MeasureTheory
open scoped Real LSeries.notation

namespace FleetTwistedWindow

open FleetHeadContour

variable {N : ℕ} [NeZero N]

/-- **Twisted window rate `c`**: `twistedWindow χ b α ≤ C e^{c/b}` at every centre `α`, `0 < b ≤ 1`. -/
def TwistedWindowRate (χ : DirichletCharacter ℂ N) (c : ℝ) : Prop :=
  ∀ α : ℝ, ∃ C : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 → twistedWindow χ b α ≤ C * Real.exp (c / b)

/-! ## Dirichlet series on `Re = 3/2` -/

lemma norm_LSeries_le_of_re (f : ℕ → ℂ) {σ : ℝ} (hf : LSeriesSummable f σ) {s : ℂ} (hs : s.re = σ) :
    ‖LSeries f s‖ ≤ ∑' n, ‖LSeries.term f σ n‖ := by
  have hn : ∀ n, ‖LSeries.term f s n‖ = ‖LSeries.term f σ n‖ := by
    intro n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hs, Complex.ofReal_re]
  have hsum : Summable (fun n => ‖LSeries.term f s n‖) :=
    (summable_norm_iff.mpr hf).congr fun n => (hn n).symm
  unfold LSeries
  refine (norm_tsum_le_tsum_norm hsum).trans (le_of_eq ?_)
  exact tsum_congr hn

lemma abscissa_lt_three_halves (χ : DirichletCharacter ℂ N) :
    LSeries.abscissaOfAbsConv ↗χ < ((3 / 2 : ℝ) : EReal) := by
  rw [DirichletCharacter.abscissaOfAbsConv_eq_one (NeZero.ne N) χ]
  exact_mod_cast (by norm_num : (1 : ℝ) < 3 / 2)

lemma re_line (t : ℝ) : (((3 / 2 : ℝ) : ℂ) + t * I).re = 3 / 2 := by simp

/-- `L'/L = −L(χΛ)` on `Re > 1`. -/
lemma logDeriv_eq_neg_LSeries (χ : DirichletCharacter ℂ N) {w : ℂ} (hw : 1 < w.re) :
    deriv (DirichletCharacter.LFunction χ) w / DirichletCharacter.LFunction χ w
      = -LSeries (↗χ * ↗ArithmeticFunction.vonMangoldt) w := by
  rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hw, DirichletCharacter.LFunction_eq_LSeries χ hw,
    DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hw, neg_div, neg_neg]

/-- The constant `B` bounding `‖L'/L‖` on `Re = 3/2`. -/
def Bchi (χ : DirichletCharacter ℂ N) : ℝ :=
  ∑' n, ‖LSeries.term (↗χ * ↗ArithmeticFunction.vonMangoldt) (3 / 2 : ℝ) n‖

lemma norm_logDeriv_le_Bchi (χ : DirichletCharacter ℂ N) (t : ℝ) :
    ‖deriv (DirichletCharacter.LFunction χ) (((3 / 2 : ℝ) : ℂ) + t * I)
      / DirichletCharacter.LFunction χ (((3 / 2 : ℝ) : ℂ) + t * I)‖ ≤ Bchi χ := by
  rw [logDeriv_eq_neg_LSeries χ (by rw [re_line]; norm_num), norm_neg]
  exact norm_LSeries_le_of_re _ (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ (by norm_num))
    (re_line t)

/-- The constant `K'` bounding `‖L'‖` on `Re = 3/2`. -/
def Kchi (χ : DirichletCharacter ℂ N) : ℝ :=
  ∑' n, ‖LSeries.term (LSeries.logMul ↗χ) (3 / 2 : ℝ) n‖

lemma norm_deriv_le_Kchi (χ : DirichletCharacter ℂ N) (t : ℝ) :
    ‖deriv (DirichletCharacter.LFunction χ) (((3 / 2 : ℝ) : ℂ) + t * I)‖ ≤ Kchi χ := by
  have hw : 1 < (((3 / 2 : ℝ) : ℂ) + t * I).re := by rw [re_line]; norm_num
  have habs : LSeries.abscissaOfAbsConv ↗χ < ((((3 / 2 : ℝ) : ℂ) + t * I).re : EReal) := by
    rw [re_line]; exact abscissa_lt_three_halves χ
  rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hw, LSeries_deriv habs, norm_neg]
  exact norm_LSeries_le_of_re _ (LSeriesSummable_logMul_of_lt_re
    (by simpa using abscissa_lt_three_halves χ)) (re_line t)

lemma Kchi_nonneg (χ : DirichletCharacter ℂ N) : 0 ≤ Kchi χ := tsum_nonneg fun _ => norm_nonneg _

/-! ## The Möbius tail on `Re = 3/2` -/

lemma MpolyChi_eq_sum_term (χ : DirichletCharacter ℂ N) (M : ℕ) (w : ℂ) :
    MpolyChi χ M w = ∑ n ∈ Finset.range (M + 1),
      LSeries.term (↗χ * ↗ArithmeticFunction.moebius) w n := by
  unfold MpolyChi
  refine Finset.sum_congr rfl fun n _ => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn, Complex.cpow_neg, div_eq_mul_inv]
  simp only [Pi.mul_apply]
  ring

/-- `‖1/L(w) − MpolyChi χ M w‖ ≤ 5 (M+1)^{-1/4}` on `Re w = 3/2`. -/
lemma norm_inv_sub_MpolyChi_le (χ : DirichletCharacter ℂ N) (M : ℕ) (t : ℝ) :
    ‖(DirichletCharacter.LFunction χ (((3 / 2 : ℝ) : ℂ) + t * I))⁻¹
      - MpolyChi χ M (((3 / 2 : ℝ) : ℂ) + t * I)‖ ≤ 5 * ((M : ℝ) + 1) ^ (-(1 / 4 : ℝ)) := by
  set w : ℂ := ((3 / 2 : ℝ) : ℂ) + t * I with hw
  have hw1 : 1 < w.re := by rw [hw, re_line]; norm_num
  set f := ↗χ * ↗ArithmeticFunction.moebius with hf
  have hsum : LSeriesSummable f w :=
    DirichletCharacter.LSeriesSummable_mul χ (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hw1)
  have hinv : (DirichletCharacter.LFunction χ w)⁻¹ = LSeries f w := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ hw1]
    exact inv_eq_of_mul_eq_one_right (DirichletCharacter.LSeries.mul_mu_eq_one χ hw1)
  rw [hinv, MpolyChi_eq_sum_term]
  unfold LSeries
  rw [← hsum.sum_add_tsum_nat_add (M + 1), add_sub_cancel_left]
  have hterm : ∀ n : ℕ, ‖LSeries.term f w (n + (M + 1))‖
      ≤ ((M : ℝ) + 1) ^ (-(1 / 4 : ℝ)) * ((n : ℝ) + 1) ^ (-(1 + 1 / 4 : ℝ)) := by
    intro n
    rw [LSeries.norm_term_eq, if_neg (show n + (M + 1) ≠ 0 by omega)]
    have hwre : w.re = 3 / 2 := by rw [hw, re_line]
    rw [hwre]
    have hnum : ‖f (n + (M + 1))‖ ≤ 1 := by
      simp only [hf, Pi.mul_apply, norm_mul]
      have h1 := DirichletCharacter.norm_le_one χ ((n + (M + 1) : ℕ) : ZMod N)
      have h2 : ‖(ArithmeticFunction.moebius (n + (M + 1)) : ℂ)‖ ≤ 1 := by
        have := FleetMollifierTail.moebius_abs_le (n + (M + 1))
        rw [show (ArithmeticFunction.moebius (n + (M + 1)) : ℂ)
          = ((ArithmeticFunction.moebius (n + (M + 1)) : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_real, Real.norm_eq_abs]
        exact this
      calc ‖χ ((n + (M + 1) : ℕ) : ZMod N)‖ * ‖(ArithmeticFunction.moebius (n + (M + 1)) : ℂ)‖
          ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
        _ = 1 := by ring
    have hk : (0 : ℝ) < ((n + (M + 1) : ℕ) : ℝ) := by positivity
    have hk' : (((n + (M + 1) : ℕ) : ℝ)) = ((n : ℝ) + 1) + M := by push_cast; ring
    have hpow : (((n + (M + 1) : ℕ) : ℝ)) ^ (3 / 2 : ℝ)
        = (((n + (M + 1) : ℕ) : ℝ)) ^ (1 / 4 : ℝ) * (((n + (M + 1) : ℕ) : ℝ)) ^ (1 + 1 / 4 : ℝ) := by
      rw [← Real.rpow_add hk]; norm_num
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    have hA : ((M : ℝ) + 1) ^ (1 / 4 : ℝ) ≤ (((n + (M + 1) : ℕ) : ℝ)) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by rw [hk']; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]) (by norm_num)
    have hB : ((n : ℝ) + 1) ^ (1 + 1 / 4 : ℝ) ≤ (((n + (M + 1) : ℕ) : ℝ)) ^ (1 + 1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by rw [hk']; linarith [(M.cast_nonneg : (0 : ℝ) ≤ M)]) (by norm_num)
    have hApos : 0 < ((M : ℝ) + 1) ^ (1 / 4 : ℝ) := by positivity
    have hBpos : 0 < ((n : ℝ) + 1) ^ (1 + 1 / 4 : ℝ) := by positivity
    rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity), ← mul_inv, div_eq_mul_inv]
    calc ‖f (n + (M + 1))‖ * ((((n + (M + 1) : ℕ) : ℝ)) ^ (3 / 2 : ℝ))⁻¹
        ≤ 1 * ((((n + (M + 1) : ℕ) : ℝ)) ^ (3 / 2 : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_right hnum (by positivity)
      _ ≤ (((M : ℝ) + 1) ^ (1 / 4 : ℝ) * ((n : ℝ) + 1) ^ (1 + 1 / 4 : ℝ))⁻¹ := by
          rw [one_mul, hpow]
          exact inv_anti₀ (by positivity) (mul_le_mul hA hB hBpos.le (by positivity))
  have hK := ZetaGrowth.tsum_add_one_rpow_le (p := 1 / 4) (by norm_num)
  have hsr := ZetaGrowth.summable_add_one_rpow (a := -(1 + 1 / 4)) (by norm_num)
  calc ‖∑' n : ℕ, LSeries.term f w (n + (M + 1))‖
      ≤ ∑' n : ℕ, ((M : ℝ) + 1) ^ (-(1 / 4 : ℝ)) * ((n : ℝ) + 1) ^ (-(1 + 1 / 4 : ℝ)) :=
        tsum_of_norm_bounded (hsr.mul_left _).hasSum hterm
    _ = ((M : ℝ) + 1) ^ (-(1 / 4 : ℝ)) * ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(1 + 1 / 4 : ℝ)) := tsum_mul_left
    _ ≤ ((M : ℝ) + 1) ^ (-(1 / 4 : ℝ)) * 5 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        norm_num at hK ⊢; linarith
    _ = 5 * ((M : ℝ) + 1) ^ (-(1 / 4 : ℝ)) := by ring

lemma cut_tail_le {b : ℝ} (hb : 0 < b) :
    ((FleetFiniteHeadRH.cut b : ℝ) + 1) ^ (-(1 / 4 : ℝ)) ≤ Real.exp (-(11 / (40 * b))) := by
  have h1 : Real.exp (11 / (10 * b)) < (FleetFiniteHeadRH.cut b : ℝ) + 1 := Nat.lt_floor_add_one _
  have h2 : Real.exp (-(11 / (40 * b))) = (Real.exp (11 / (10 * b))) ^ (-(1 / 4 : ℝ)) := by
    rw [← Real.exp_mul]; congr 1; field_simp; ring
  rw [h2]
  exact Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) h1.le (by norm_num)

/-- **Prime line versus twisted head.** -/
theorem norm_primeLine_le_head (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {b : ℝ} (hb : 0 < b)
    (hb1 : b ≤ 1) (α : ℝ) :
    ‖primeLine (DirichletCharacter.LFunction χ) b α‖
      ≤ 2 * π * ‖headChi χ b α (FleetFiniteHeadRH.cut b)‖
        + Real.sqrt (π / b) * (10 * Real.sqrt (4 * π) * Kchi χ) := by
  set M := FleetFiniteHeadRH.cut b with hM
  set Lf := DirichletCharacter.LFunction χ with hLf
  set g1 : ℝ → ℂ := fun t => LGw b α (((3 / 2 : ℝ) : ℂ) + t * I)
    * (deriv Lf (((3 / 2 : ℝ) : ℂ) + t * I) / Lf (((3 / 2 : ℝ) : ℂ) + t * I)) with hg1
  set g2 : ℝ → ℂ := fun t => PhiChi χ b α M (((3 / 2 : ℝ) : ℂ) + t * I)
    * (-deriv Lf (((3 / 2 : ℝ) : ℂ) + t * I)) with hg2
  have hne : ∀ t : ℝ, Lf (((3 / 2 : ℝ) : ℂ) + t * I) ≠ 0 := fun t =>
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by rw [re_line]; norm_num)
  have hLd : Differentiable ℂ Lf := DirichletCharacter.differentiable_LFunction hχ
  have hg1c : Continuous g1 := by
    refine ((differentiable_LGw b α).continuous.comp (continuous_line _)).mul ?_
    refine continuous_iff_continuousAt.mpr fun y => ?_
    exact (((differentiable_deriv_of_entire hLd).continuous.comp (continuous_line _)).continuousAt).div
      ((hLd.continuous.comp (continuous_line _)).continuousAt) (hne y)
  have hg1i : Integrable g1 := by
    refine Integrable.mono' ((integrable_LGw_line hb α (3 / 2)).norm.mul_const (Bchi χ))
      hg1c.aestronglyMeasurable (ae_of_all _ fun y => ?_)
    simp only [hg1, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_logDeriv_le_Bchi χ y) (norm_nonneg _)
  have hg2i : Integrable g2 := integrable_PhiChi_line χ hχ hb α M (x := 3 / 2) (by norm_num)
  have hpl : primeLine Lf b α = ∫ t, g1 t := rfl
  have hhd : 2 * π * headChi χ b α M = ∫ t, g2 t := by
    unfold headChi
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [← mul_assoc, show (2 * π : ℂ) * (1 / (2 * π)) = 1 by field_simp, one_mul]
  -- the pointwise bound on `g1 + g2`
  set E : ℝ := Real.exp (-(11 / (40 * b))) with hE
  set h : ℝ → ℝ := fun t => Real.sqrt (π / b) * Real.exp (1 / (4 * b)) * (Kchi χ * (5 * E))
    * (Real.exp (-(t + α) ^ 2 / (4 * b)) + Real.exp (-(t - α) ^ 2 / (4 * b))) with hh
  have hpt : ∀ t, ‖g1 t + g2 t‖ ≤ h t := by
    intro t
    set w : ℂ := ((3 / 2 : ℝ) : ℂ) + t * I with hw
    have e : g1 t + g2 t = LGw b α w * deriv Lf w * ((Lf w)⁻¹ - MpolyChi χ M w) := by
      simp only [hg1, hg2, PhiChi, hw]
      rw [div_eq_mul_inv]; ring
    rw [e, norm_mul, norm_mul]
    have hL := norm_LGw_le b α (3 / 2) t
    have e2 : ((3 / 2 : ℝ) - 1 / 2) ^ 2 / (4 * b) = 1 / (4 * b) := by norm_num
    rw [e2] at hL
    have hD := norm_deriv_le_Kchi χ t
    have hT := (norm_inv_sub_MpolyChi_le χ M t).trans
      (mul_le_mul_of_nonneg_left (cut_tail_le hb) (by norm_num))
    have hKc := Kchi_nonneg χ
    calc ‖LGw b α w‖ * ‖deriv Lf w‖ * ‖(Lf w)⁻¹ - MpolyChi χ M w‖
        ≤ (Real.sqrt (π / b) * Real.exp (1 / (4 * b)) *
            (Real.exp (-(t + α) ^ 2 / (4 * b)) + Real.exp (-(t - α) ^ 2 / (4 * b)))) * Kchi χ * (5 * E) := by
          gcongr
      _ = h t := by simp only [hh]; ring
  have hhi : Integrable h := by
    have i1 : Integrable (fun t : ℝ => Real.exp (-(t + α) ^ 2 / (4 * b))) := by
      have := integrable_gauss_scale (d := 4 * b) (by positivity) (-α)
      refine this.congr (ae_of_all _ fun t => ?_)
      simp only [sub_neg_eq_add]
    exact (i1.add (integrable_gauss_scale (d := 4 * b) (by positivity) α)).const_mul _
  have hint_h : ∫ t, h t ≤ Real.sqrt (π / b) * (10 * Real.sqrt (4 * π) * Kchi χ) := by
    have i1 : Integrable (fun t : ℝ => Real.exp (-(t + α) ^ 2 / (4 * b))) := by
      have := integrable_gauss_scale (d := 4 * b) (by positivity) (-α)
      refine this.congr (ae_of_all _ fun t => ?_)
      simp only [sub_neg_eq_add]
    have e1 : ∫ t : ℝ, Real.exp (-(t + α) ^ 2 / (4 * b)) = Real.sqrt (π * (4 * b)) := by
      have := integral_gauss_scale (d := 4 * b) (by positivity) (-α)
      simpa only [sub_neg_eq_add] using this
    simp only [hh]
    rw [MeasureTheory.integral_const_mul, integral_add i1 (integrable_gauss_scale (by positivity) α), e1,
      integral_gauss_scale (by positivity)]
    have hEE : Real.exp (1 / (4 * b)) * E ≤ 1 := by
      rw [hE, ← Real.exp_add, Real.exp_le_one_iff]
      rw [show 1 / (4 * b) + -(11 / (40 * b)) = -(1 / (40 * b)) by field_simp; ring]
      have : 0 ≤ 1 / (40 * b) := by positivity
      linarith
    have h4 : Real.sqrt (π * (4 * b)) ≤ Real.sqrt (4 * π) := Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])
    have hKc := Kchi_nonneg χ
    have hs0 := Real.sqrt_nonneg (π / b)
    have hs4 := Real.sqrt_nonneg (π * (4 * b))
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    have key : Real.exp (1 / (4 * b)) * (Kchi χ * (5 * E)) * (Real.sqrt (π * (4 * b)) + Real.sqrt (π * (4 * b)))
        ≤ 10 * Real.sqrt (4 * π) * Kchi χ := by
      have : Real.exp (1 / (4 * b)) * (Kchi χ * (5 * E)) * (Real.sqrt (π * (4 * b)) + Real.sqrt (π * (4 * b)))
          = 10 * (Real.exp (1 / (4 * b)) * E) * Real.sqrt (π * (4 * b)) * Kchi χ := by ring
      rw [this]
      have a1 : (Real.exp (1 / (4 * b)) * E) * Real.sqrt (π * (4 * b)) ≤ 1 * Real.sqrt (4 * π) :=
        mul_le_mul hEE h4 hs4 zero_le_one
      nlinarith
    calc Real.sqrt (π / b) * Real.exp (1 / (4 * b)) * (Kchi χ * (5 * E))
          * (Real.sqrt (π * (4 * b)) + Real.sqrt (π * (4 * b)))
        = Real.sqrt (π / b) * (Real.exp (1 / (4 * b)) * (Kchi χ * (5 * E))
          * (Real.sqrt (π * (4 * b)) + Real.sqrt (π * (4 * b)))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left key hs0
  have hsumint : ‖∫ t, (g1 t + g2 t)‖ ≤ Real.sqrt (π / b) * (10 * Real.sqrt (4 * π) * Kchi χ) :=
    (norm_integral_le_of_norm_le hhi (ae_of_all _ hpt)).trans hint_h
  rw [integral_add hg1i hg2i, ← hpl, ← hhd] at hsumint
  have hn2 : ‖2 * π * headChi χ b α M‖ = 2 * π * ‖headChi χ b α M‖ := by
    rw [norm_mul, show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc ‖primeLine Lf b α‖ = ‖(primeLine Lf b α + 2 * π * headChi χ b α M) - 2 * π * headChi χ b α M‖ := by
        ring_nf
    _ ≤ ‖primeLine Lf b α + 2 * π * headChi χ b α M‖ + ‖2 * π * headChi χ b α M‖ := norm_sub_le _ _
    _ ≤ _ := by rw [hn2]; linarith

/-! ## The strip theorem for one character -/

lemma sqrt_exp_eq (x : ℝ) : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
  rw [show Real.exp x = Real.exp (x / 2) ^ 2 by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring,
    Real.sqrt_sq (Real.exp_pos _).le]

/-- **Twisted window rate ⇒ right half of the strip.** For `χ ≠ 1` with twisted window rate `c ≥ 0`,
every zero of `L(·,χ)` with `Re ρ > 1/2` satisfies `Re ρ − 1/2 ≤ √(2c)`. -/
theorem zeros_right_of_twisted_window_rate (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {c : ℝ}
    (hc : 0 ≤ c) (h : TwistedWindowRate χ c) {ρ : ℂ}
    (hρ : DirichletCharacter.LFunction χ ρ = 0) (hre : 1 / 2 < ρ.re) :
    ρ.re - 1 / 2 ≤ Real.sqrt (2 * c) := by
  have hdet := zero_detect
    (DirichletCharacter.differentiable_LFunction hχ)
    (fun w hw => DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hw)
    (B := Bchi χ) (norm_logDeriv_le_Bchi χ) (c := c / 2) (by positivity) ?_ hρ hre
  · have h2 : (ρ.re - 1 / 2) ^ 2 ≤ 2 * c := by linarith
    exact (le_abs_self _).trans (Real.abs_le_sqrt h2)
  intro α
  obtain ⟨C₁, hC₁⟩ := h α
  obtain ⟨C₂, hC₂⟩ := h (-α)
  set K₁ := Kc (15 * N + 4) (20 * N) α with hK₁
  set K₂ := Kc (15 * N + 4) (20 * N) (-α) with hK₂
  refine ⟨(Real.sqrt |C₁| * Real.sqrt K₁ + Real.sqrt |C₂| * Real.sqrt K₂)
    + 10 * Real.sqrt (4 * π) * Kchi χ, fun b hb hb1 => ?_⟩
  set E := Real.exp (c / b) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have w₁ : twistedWindow χ b α ≤ |C₁| * E :=
    (hC₁ b hb hb1).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hE0.le)
  have w₂ : twistedWindow χ b (-α) ≤ |C₂| * E :=
    (hC₂ b hb hb1).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hE0.le)
  have hH := norm_headChi_le_of_windows χ hχ hb hb1 α (by positivity) (by positivity) w₁ w₂
  have hP := norm_primeLine_le_head χ hχ hb hb1 α
  set F := Real.exp (c / 2 / b) with hF
  have hF1 : 1 ≤ F := Real.one_le_exp (by positivity)
  have hsE : Real.sqrt E = F := by rw [hE, sqrt_exp_eq, hF]; congr 1; ring
  have hs1 : Real.sqrt (|C₁| * E) = Real.sqrt |C₁| * F := by
    rw [Real.sqrt_mul (abs_nonneg _), hsE]
  have hs2 : Real.sqrt (|C₂| * E) = Real.sqrt |C₂| * F := by
    rw [Real.sqrt_mul (abs_nonneg _), hsE]
  rw [hs1, hs2] at hH
  have hsq := Real.sqrt_nonneg (π / b)
  have hpi : 0 < 2 * π := by positivity
  have hD : 0 ≤ 10 * Real.sqrt (4 * π) * Kchi χ := by have := Kchi_nonneg χ; positivity
  have hA : 0 ≤ Real.sqrt |C₁| * Real.sqrt K₁ + Real.sqrt |C₂| * Real.sqrt K₂ := by positivity
  have h2H : 2 * π * ‖headChi χ b α (FleetFiniteHeadRH.cut b)‖
      ≤ Real.sqrt (π / b) * ((Real.sqrt |C₁| * Real.sqrt K₁ + Real.sqrt |C₂| * Real.sqrt K₂) * F) := by
    have := mul_le_mul_of_nonneg_left hH hpi.le
    calc 2 * π * ‖headChi χ b α (FleetFiniteHeadRH.cut b)‖
        ≤ 2 * π * (Real.sqrt (π / b) / (2 * π) * (Real.sqrt |C₁| * F * Real.sqrt K₁
          + Real.sqrt |C₂| * F * Real.sqrt K₂)) := this
      _ = _ := by field_simp
  calc ‖primeLine (DirichletCharacter.LFunction χ) b α‖
      ≤ Real.sqrt (π / b) * ((Real.sqrt |C₁| * Real.sqrt K₁ + Real.sqrt |C₂| * Real.sqrt K₂) * F)
        + Real.sqrt (π / b) * (10 * Real.sqrt (4 * π) * Kchi χ) := hP.trans (add_le_add h2H le_rfl)
    _ ≤ Real.sqrt (π / b) * ((Real.sqrt |C₁| * Real.sqrt K₁ + Real.sqrt |C₂| * Real.sqrt K₂) * F)
        + Real.sqrt (π / b) * (10 * Real.sqrt (4 * π) * Kchi χ * F) := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hD hF1) hsq)
    _ = Real.sqrt (π / b) * (((Real.sqrt |C₁| * Real.sqrt K₁ + Real.sqrt |C₂| * Real.sqrt K₂)
        + 10 * Real.sqrt (4 * π) * Kchi χ) * Real.exp (c / 2 / b)) := by rw [hF]; ring

/-! ## `χ⁻¹`: the window at `−α` -/

lemma MpolyChi_inv_eq_conj (χ : DirichletCharacter ℂ N) (M : ℕ) (t : ℝ) :
    MpolyChi χ⁻¹ M (((1 / 2 : ℝ) : ℂ) + t * I)
      = (starRingEnd ℂ) (MpolyChi χ M (((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)) := by
  unfold MpolyChi
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, map_mul, map_intCast]
  have hχ : (starRingEnd ℂ) (χ (m : ZMod N)) = χ⁻¹ (m : ZMod N) := MulChar.star_apply' χ _
  rw [hχ]
  congr 1
  have harg : (m : ℂ).arg ≠ π := by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
  have hc := Complex.cpow_conj (m : ℂ) (-(((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)) harg
  rw [Complex.conj_natCast] at hc
  have e : (starRingEnd ℂ) (-(((1 / 2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)) = -(((1 / 2 : ℝ) : ℂ) + t * I) := by
    apply Complex.ext <;> simp
  rw [e] at hc
  exact hc

/-- **`twistedWindow χ⁻¹ b α = twistedWindow χ b (−α)`.** -/
theorem twistedWindow_inv (χ : DirichletCharacter ℂ N) (b α : ℝ) :
    twistedWindow χ⁻¹ b α = twistedWindow χ b (-α) := by
  unfold twistedWindow
  set G : ℝ → ℝ := fun u => ‖MpolyChi χ (FleetFiniteHeadRH.cut b) (((1 / 2 : ℝ) : ℂ) + u * I)‖ ^ 2
    * Real.exp (-(-u - α) ^ 2 / (4 * b)) with hG
  have h1 : (fun t : ℝ => ‖MpolyChi χ⁻¹ (FleetFiniteHeadRH.cut b) (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2
      * Real.exp (-(t - α) ^ 2 / (4 * b))) = fun t => G (-t) := by
    funext t
    rw [MpolyChi_inv_eq_conj, RCLike.norm_conj]
    simp only [hG, neg_neg]
  rw [h1, integral_neg_eq_self (fun t => G t) volume]
  congr 1; funext u
  simp only [hG]
  congr 3
  ring

theorem TwistedWindowRate.inv {χ : DirichletCharacter ℂ N} {c : ℝ} (h : TwistedWindowRate χ c) :
    TwistedWindowRate χ⁻¹ c := by
  intro α
  obtain ⟨C, hC⟩ := h (-α)
  exact ⟨C, fun b hb hb1 => by rw [twistedWindow_inv]; exact hC b hb hb1⟩

/-! ## Both halves, for primitive characters -/

lemma gammaFactor_ne_zero (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def]; exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · rw [h.gammaFactor_def]; exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)

lemma level_ne_one {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) : N ≠ 1 := by
  intro hN
  subst hN
  exact hχ χ.level_one

/-- **Reflection of zeros** (functional equation): for primitive `χ ≠ 1`, a zero `ρ` of `L(·,χ)` with
`Re ρ > 0` gives the zero `1 − ρ` of `L(·,χ⁻¹)`. -/
theorem LFunction_inv_one_sub_eq_zero (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {ρ : ℂ} (hρ : DirichletCharacter.LFunction χ ρ = 0) (hre : 0 < ρ.re) :
    DirichletCharacter.LFunction χ⁻¹ (1 - ρ) = 0 := by
  have hN1 := level_ne_one hχ
  have hgf := gammaFactor_ne_zero χ hre
  have hcomp : DirichletCharacter.completedLFunction χ ρ = 0 := by
    have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ ρ (Or.inr hN1)
    rw [hρ, eq_comm, div_eq_zero_iff] at h
    exact h.resolve_right hgf
  have hprim' : (χ⁻¹).IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact hprim
  have hfe := DirichletCharacter.IsPrimitive.completedLFunction_one_sub hprim' ρ
  rw [inv_inv, hcomp, mul_zero] at hfe
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - ρ) (Or.inr hN1), hfe, zero_div]

/-- **Twisted window rate ⇒ strip** (primitive `χ ≠ 1`): every zero of `L(·,χ)` with `Re ρ > 0`
satisfies `|Re ρ − 1/2| ≤ √(2c)`. -/
theorem zeros_in_strip_of_twisted_window_rate (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {c : ℝ} (hc : 0 ≤ c) (h : TwistedWindowRate χ c) {ρ : ℂ}
    (hρ : DirichletCharacter.LFunction χ ρ = 0) (hre : 0 < ρ.re) :
    |ρ.re - 1 / 2| ≤ Real.sqrt (2 * c) := by
  rcases lt_trichotomy ρ.re (1 / 2) with hlt | heq | hgt
  · have h1 := LFunction_inv_one_sub_eq_zero χ hχ hprim hρ hre
    have hχ' : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ
    have h2 := zeros_right_of_twisted_window_rate χ⁻¹ hχ' hc h.inv h1 (by simp; linarith)
    rw [abs_of_neg (by linarith)]
    rw [Complex.sub_re, Complex.one_re] at h2
    linarith
  · rw [heq, sub_self, abs_zero]; exact Real.sqrt_nonneg _
  · rw [abs_of_pos (by linarith)]
    exact zeros_right_of_twisted_window_rate χ hχ hc h hρ hgt

/-! ## The family version -/

section Family

variable {ι : Type*} {Nf : ι → ℕ} [∀ i, NeZero (Nf i)] (χf : (i : ι) → DirichletCharacter ℂ (Nf i))

/-- `β*` of the family (as in the quasi-RH paper, eq. (1.1b), for Dirichlet characters):
`sup ({1/2} ∪ {Re ρ : 1/2 ≤ Re ρ ≤ 1, L(ρ,χᵢ) = 0 for some i})`. -/
def betaStar : ℝ :=
  sSup ({1 / 2} ∪ {x : ℝ | ∃ i : ι, ∃ ρ : ℂ, DirichletCharacter.LFunction (χf i) ρ = 0 ∧
    1 / 2 ≤ ρ.re ∧ ρ.re ≤ 1 ∧ x = ρ.re})

/-- **Family version, `β*` form.** A twisted window rate `c` common to a family of nonprincipal
characters gives `β* ≤ 1/2 + √(2c)`. -/
theorem betaStar_le_of_uniform_rate (hχ : ∀ i, χf i ≠ 1) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, TwistedWindowRate (χf i) c) : betaStar χf ≤ 1 / 2 + Real.sqrt (2 * c) := by
  unfold betaStar
  refine csSup_le ⟨1 / 2, Or.inl rfl⟩ fun x hx => ?_
  rcases hx with hx | ⟨i, ρ, hρ, hre, -, rfl⟩
  · rw [Set.mem_singleton_iff] at hx; rw [hx]; linarith [Real.sqrt_nonneg (2 * c)]
  · rcases eq_or_lt_of_le hre with heq | hgt
    · rw [← heq]; linarith [Real.sqrt_nonneg (2 * c)]
    · have := zeros_right_of_twisted_window_rate (χf i) (hχ i) hc (h i) hρ hgt
      linarith

/-- `D_family = sup |Re ρ − 1/2|` over the zeros with `Re ρ > 0` of all members. -/
def familyDev : ℝ :=
  sSup {d : ℝ | ∃ i : ι, ∃ ρ : ℂ, DirichletCharacter.LFunction (χf i) ρ = 0 ∧ 0 < ρ.re ∧
    d = |ρ.re - 1 / 2|}

/-- **Family version, `D` form** (primitive nonprincipal members): `D_family ≤ √(2c)`. -/
theorem familyDev_le_of_uniform_rate (hχ : ∀ i, χf i ≠ 1) (hprim : ∀ i, (χf i).IsPrimitive) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ i, TwistedWindowRate (χf i) c) : familyDev χf ≤ Real.sqrt (2 * c) := by
  unfold familyDev
  refine Real.sSup_le (fun d hd => ?_) (Real.sqrt_nonneg _)
  obtain ⟨i, ρ, hρ, hre, rfl⟩ := hd
  exact zeros_in_strip_of_twisted_window_rate (χf i) (hχ i) (hprim i) hc (h i) hρ hre

/-- `β*` of `{ζ} ∪` the family: the zeros of `ζ` with `1/2 ≤ Re ρ ≤ 1` are added to the set. -/
def betaStarWithZeta : ℝ :=
  sSup ({1 / 2} ∪ {x : ℝ | ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ ρ.re ≤ 1 ∧ x = ρ.re}
    ∪ {x : ℝ | ∃ i : ι, ∃ ρ : ℂ, DirichletCharacter.LFunction (χf i) ρ = 0 ∧
      1 / 2 ≤ ρ.re ∧ ρ.re ≤ 1 ∧ x = ρ.re})

/-- **Family version with the trivial character.** The untwisted window rate `c` of
`FleetHeadContourStrip.zeros_in_strip_of_window_rate` (centres `|α| ≥ 1/2`) together with a common twisted
rate `c` for a family of nonprincipal characters gives `β*({ζ} ∪ family) ≤ 1/2 + √(2c)`. -/
theorem betaStarWithZeta_le (hχ : ∀ i, χf i ≠ 1) {c : ℝ} (hc : 0 ≤ c)
    (hζ : ∀ α : ℝ, 1 / 2 ≤ |α| → ∃ C : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      ∫ t : ℝ, ‖Mpoly (FleetFiniteHeadRH.cut b) (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2
        * Real.exp (-(t - α) ^ 2 / (4 * b)) ≤ C * Real.exp (c / b))
    (h : ∀ i, TwistedWindowRate (χf i) c) : betaStarWithZeta χf ≤ 1 / 2 + Real.sqrt (2 * c) := by
  have hstripζ := zeros_in_strip_of_window_rate hc hζ
  unfold betaStarWithZeta
  refine csSup_le ⟨1 / 2, Or.inl (Or.inl rfl)⟩ fun x hx => ?_
  have hs0 := Real.sqrt_nonneg (2 * c)
  rcases hx with (hx | ⟨ρ, hρ, hre, hre1, rfl⟩) | ⟨i, ρ, hρ, hre, -, rfl⟩
  · rw [Set.mem_singleton_iff] at hx; rw [hx]; linarith
  · have hnt : Reduction.IsNontrivialZero ρ := by
      refine ⟨hρ, ?_, ?_⟩
      · rintro ⟨n, rfl⟩
        have : (-2 * ((n : ℂ) + 1)).re < 0 := by simp; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
        linarith
      · rintro rfl
        exact riemannZeta_one_ne_zero hρ
    obtain ⟨xi, hxi⟩ := ZeroSumLimit.multEnum_canonical.exists_index hnt
    have := hstripζ xi
    rw [hxi] at this
    have := le_abs_self (ρ.re - 1 / 2)
    linarith
  · rcases eq_or_lt_of_le hre with heq | hgt
    · rw [← heq]; linarith
    · have := zeros_right_of_twisted_window_rate (χf i) (hχ i) hc (h i) hρ hgt
      linarith

end Family

end FleetTwistedWindow
