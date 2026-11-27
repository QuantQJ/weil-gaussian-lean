import FleetSmoothWindowStripRegions
import FleetExponentLadder

/-!
# Smooth window rate `c` ⇒ strip `√(2c)`, and the exact optimal rate `D²/2`

From `primeSumSym_eq_double` (`√(4πb) S_b(α) = (1/2π) ∫ e^{-x²/(4b)} I_x dx`) and the per-`x` contour
bounds, for `|α| > 1/2` and every `ε ∈ (0,1]`:

  `e^{-x²/(4b)} ‖I_x‖ ≤ √(π/b) M (e^{c/(2b)} + e^{ε/b}) (1 + x²)^{-1}`   (`Ix_bound`, `x ≠ 1/2`)

with `M` depending on `α`, `ε` and the two window constants at `±α` (not on `b`, `x`). Regions, with
`τ = min((|α| − 1/2)/2, 1)` and `θ = min(ε/16, τ/16, 1/64)`:
* `x < θ − 1/4`: `w`-line `Re = 1/2`, trivial bound for `P_b` at `Re = 1/2 − x`, plus the residue at `w = 1`;
* `θ − 1/4 ≤ x ≤ 1/2 − θ`: `w`-line `Re = 1/2 + x` (window) plus the residue;
* `|x − 1/2| < θ`: the line `Re = 1/2 + x` for `|t| ≥ τ`, bumped to `Re = 1 + 2θ` for `|t| ≤ τ` (this needs
  `|α| > 1/2`);
* `x ≥ 1/2 + θ`: `w`-line `Re = 1/2 + x` (window), `‖ζ'‖ ≤ Λ₁(1/2 + x) ≪ 2^{-x}`.

Hence `‖S_b(α)‖ ≤ √(π/b) C e^{(c/2 + 2ε)/b}` (`primeSumSym_le_of_smoothWindow`), and the exponent ladder gives
`zeros_in_strip_of_smoothWindow`: every nontrivial zero has `|Re ρ − 1/2| ≤ √(2c)`.

With `smoothWindowRate_of_strip` (`FleetSmoothWindowConverse`): `smoothWindowRateInf = zeroDev² / 2`
(`smoothWindowRateInf_eq`), with no hypothesis.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set MeasureTheory
open scoped Real Interval

namespace FleetSmoothWindow

open FleetLandauTransfer FleetHeadContour OffLineDetection Reduction ZeroSumLimit GaussianTest

lemma Lam1_pos (σ : ℝ) (hσ : 1 < σ) : 0 < Lam1 σ := by
  unfold Lam1
  refine Summable.tsum_pos (summable_log_rpow hσ) (fun n => mul_nonneg
    (Real.log_nonneg (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])) (by positivity)) 0 ?_
  simp only [Nat.cast_zero, zero_add]
  exact mul_pos (Real.log_pos (by norm_num)) (by positivity)

lemma inv_one_add_sq_ge {x : ℝ} (hx : |x| ≤ 1) : 1 ≤ 2 * (1 + x ^ 2)⁻¹ := by
  have h : x ^ 2 ≤ 1 := by
    have := sq_abs x; nlinarith [abs_nonneg x]
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]; linarith

/-- The common parameter facts. -/
structure Params (α ε θ τ : ℝ) : Prop where
  hθ : 0 < θ
  hθε : θ ≤ ε / 16
  hθτ : θ ≤ τ / 16
  hθ1 : θ ≤ 1 / 64
  hτ : 0 < τ
  hτ1 : τ ≤ 1
  hατ : 1 / 2 + 2 * τ ≤ |α|

/-- The residue piece, uniformly for `x ≤ 1/2`. -/
lemma residue_final {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) {α ε θ τ : ℝ} (P : Params α ε θ τ) {x : ℝ}
    (hx : x ≤ 1 / 2) :
    Real.exp (-x ^ 2 / (4 * b)) * ‖2 * π * deriv (Phix b α x) 1‖
      ≤ Real.sqrt (π / b) * (2 * π * (2 / θ * Sz θ * 4)) * (1 + x ^ 2)⁻¹ := by
  obtain ⟨hθ, hθε, hθτ, hθ1, hτ, hτ1, hατ⟩ := P
  have hS := Sz_nonneg θ
  have hρα : θ ≤ |α| := by linarith
  have hαθ : 1 / 2 + τ ≤ |α| - θ := by linarith
  have hsq : (1 / 2 + τ) ^ 2 ≤ (|α| - θ) ^ 2 := pow_le_pow_left₀ (by linarith) hαθ 2
  have hn : ‖(2 * π * deriv (Phix b α x) 1 : ℂ)‖ = 2 * π * ‖deriv (Phix b α x) 1‖ := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [hn]
  have key : Real.exp (-x ^ 2 / (4 * b)) * ‖deriv (Phix b α x) 1‖
      ≤ 2 / θ * Real.sqrt (π / b) * Sz θ * (4 * (1 + x ^ 2)⁻¹) := by
    rcases le_or_gt x (-1) with h1 | h1
    · have hD : max 0 (θ + θ + x) ^ 2 ≤ x ^ 2 + -x ^ 2 := by
        rw [max_eq_left (by linarith)]; simp
      have R := residue_bound hb α x (D := -x ^ 2) hθ hθ (by linarith) hρα hD
      refine R.trans ?_
      have hE : Real.exp (((1 / 2 + θ) ^ 2 - (|α| - θ) ^ 2 + -x ^ 2) / (4 * b)) ≤ Real.exp (-x ^ 2 / (4 * b)) := by
        apply Real.exp_le_exp.mpr
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith
      have h4 := gauss_four hb hb1 x
      have : 0 ≤ 2 / θ * Real.sqrt (π / b) * Sz θ := by positivity
      gcongr
      exact hE.trans h4
    · have hD : max 0 (θ + θ + x) ^ 2 ≤ x ^ 2 + (θ + θ) * (θ + θ + 1) := by
        rcases le_total (θ + θ + x) 0 with h | h
        · rw [max_eq_left h]; nlinarith [sq_nonneg x]
        · rw [max_eq_right h]; nlinarith
      have R := residue_bound hb α x (D := (θ + θ) * (θ + θ + 1)) hθ hθ (by linarith) hρα hD
      refine R.trans ?_
      have hE : Real.exp (((1 / 2 + θ) ^ 2 - (|α| - θ) ^ 2 + (θ + θ) * (θ + θ + 1)) / (4 * b)) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
        nlinarith
      have hx1 : |x| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      have h2 := inv_one_add_sq_ge hx1
      have : 0 ≤ 2 / θ * Real.sqrt (π / b) * Sz θ := by positivity
      calc 2 / θ * Real.sqrt (π / b) * Sz θ *
            Real.exp (((1 / 2 + θ) ^ 2 - (|α| - θ) ^ 2 + (θ + θ) * (θ + θ + 1)) / (4 * b))
          ≤ 2 / θ * Real.sqrt (π / b) * Sz θ * 1 := by gcongr
        _ ≤ 2 / θ * Real.sqrt (π / b) * Sz θ * (4 * (1 + x ^ 2)⁻¹) := by
            gcongr; have := inv_pos.mpr (by positivity : (0 : ℝ) < 1 + x ^ 2); linarith
  calc Real.exp (-x ^ 2 / (4 * b)) * (2 * π * ‖deriv (Phix b α x) 1‖)
      = 2 * π * (Real.exp (-x ^ 2 / (4 * b)) * ‖deriv (Phix b α x) 1‖) := by ring
    _ ≤ 2 * π * (2 / θ * Real.sqrt (π / b) * Sz θ * (4 * (1 + x ^ 2)⁻¹)) := by gcongr
    _ = _ := by ring

/-- Region (a): `x < θ − 1/4`. -/
lemma region_a {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) {α ε θ τ c : ℝ} (P : Params α ε θ τ) (hc : 0 ≤ c)
    {x : ℝ} (hx : x < θ - 1 / 4) :
    Real.exp (-x ^ 2 / (4 * b)) * ‖Ix b α x‖
      ≤ Real.sqrt (π / b) * (Sz θ * (2 * ((39 + 20 * |α|) * K0)) * 4 + 2 * π * (2 / θ * Sz θ * 4))
        * (Real.exp (c / (2 * b)) + Real.exp (ε / b)) * (1 + x ^ 2)⁻¹ := by
  have P' := P
  obtain ⟨hθ, hθε, hθτ, hθ1, hτ, hτ1, hατ⟩ := P
  have hS := Sz_nonneg θ
  have hK := K0_nonneg
  have hid := Ix_eq_left hb α x (r := 1 / 4) (a := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  have R1 := rmm_line_bound hb hb1 α x hθ
  have R2 := residue_final hb hb1 P' (x := x) (by linarith)
  -- the exponential factor of the line piece
  have hE : Real.exp ((max 0 (1 / 2 + θ + x) ^ 2 - x ^ 2) / (4 * b)) ≤ 4 * Real.exp (ε / b) * (1 + x ^ 2)⁻¹ := by
    rcases le_total (1 / 2 + θ + x) 0 with h | h
    · rw [max_eq_left h, show ((0 : ℝ) ^ 2 - x ^ 2) = -x ^ 2 by ring]
      have h4 := gauss_four hb hb1 x
      have h1 : 1 ≤ Real.exp (ε / b) := Real.one_le_exp (div_nonneg (by linarith) hb.le)
      have : 0 ≤ (1 + x ^ 2)⁻¹ := by positivity
      nlinarith
    · rw [max_eq_right h]
      have hx1 : |x| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      have h2 := inv_one_add_sq_ge hx1
      have hexp : Real.exp (((1 / 2 + θ + x) ^ 2 - x ^ 2) / (4 * b)) ≤ Real.exp (ε / b) := by
        apply Real.exp_le_exp.mpr
        rw [div_le_div_iff₀ (by positivity) hb]
        have : (1 / 2 + θ + x) ^ 2 - x ^ 2 ≤ 4 * ε := by nlinarith
        nlinarith
      have h0 := Real.exp_pos (ε / b)
      nlinarith
  rw [hid]
  have tri : ‖(∫ t : ℝ, fx b α x (((1 / 2 : ℝ) : ℂ) + t * I)) + 2 * π * deriv (Phix b α x) 1‖
      ≤ ‖∫ t : ℝ, fx b α x (((1 / 2 : ℝ) : ℂ) + t * I)‖ + ‖(2 * π * deriv (Phix b α x) 1 : ℂ)‖ := norm_add_le _ _
  have he1 : 1 ≤ Real.exp (ε / b) := Real.one_le_exp (div_nonneg (by linarith) hb.le)
  have hc0 : 0 ≤ Real.exp (c / (2 * b)) := (Real.exp_pos _).le
  have hinv : 0 ≤ (1 + x ^ 2)⁻¹ := by positivity
  have hsq : 0 ≤ Real.sqrt (π / b) := Real.sqrt_nonneg _
  calc Real.exp (-x ^ 2 / (4 * b)) * ‖(∫ t : ℝ, fx b α x (((1 / 2 : ℝ) : ℂ) + t * I)) + 2 * π * deriv (Phix b α x) 1‖
      ≤ Real.exp (-x ^ 2 / (4 * b)) * ‖∫ t : ℝ, fx b α x (((1 / 2 : ℝ) : ℂ) + t * I)‖
        + Real.exp (-x ^ 2 / (4 * b)) * ‖(2 * π * deriv (Phix b α x) 1 : ℂ)‖ := by
        rw [← mul_add]; gcongr
    _ ≤ Real.sqrt (π / b) * Sz θ * (4 * Real.exp (ε / b) * (1 + x ^ 2)⁻¹) * (2 * ((39 + 20 * |α|) * K0))
        + Real.sqrt (π / b) * (2 * π * (2 / θ * Sz θ * 4)) * (1 + x ^ 2)⁻¹ := by
        refine add_le_add (R1.trans ?_) R2
        gcongr
    _ ≤ _ := by
        have hA : 0 ≤ Sz θ * (2 * ((39 + 20 * |α|) * K0)) * 4 := by positivity
        have hB : 0 ≤ 2 * π * (2 / θ * Sz θ * 4) := by positivity
        nlinarith [mul_nonneg (mul_nonneg hsq hA) (mul_nonneg hc0 hinv),
          mul_nonneg (mul_nonneg hsq hB) (mul_nonneg hc0 hinv),
          mul_nonneg (mul_nonneg hsq hB) (mul_nonneg (by linarith : (0 : ℝ) ≤ Real.exp (ε / b) - 1) hinv)]

/-- Region (b): `θ − 1/4 ≤ x ≤ 1/2 − θ`. -/
lemma region_b {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) {α ε θ τ c Cp Cm : ℝ} (P : Params α ε θ τ)
    (hCp : 0 ≤ Cp) (hCm : 0 ≤ Cm)
    (hWm : smoothWindow b α ≤ Cm * Real.exp (c / b)) (hWp : smoothWindow b (-α) ≤ Cp * Real.exp (c / b))
    {x : ℝ} (hx1 : θ - 1 / 4 ≤ x) (hx2 : x ≤ 1 / 2 - θ) :
    Real.exp (-x ^ 2 / (4 * b)) * ‖Ix b α x‖
      ≤ Real.sqrt (π / b) * (2 * ((((θ ^ 2)⁻¹ + 5 * (1 + θ) / θ) + 5 / θ + 5 / θ * |α|) * (Cp + Cm + 2 * K0) / 2)
          + 2 * π * (2 / θ * Sz θ * 4))
        * (Real.exp (c / (2 * b)) + Real.exp (ε / b)) * (1 + x ^ 2)⁻¹ := by
  have P' := P
  obtain ⟨hθ, hθε, hθτ, hθ1, hτ, hτ1, hατ⟩ := P
  have hS := Sz_nonneg θ
  have hK := K0_nonneg
  have hid := Ix_eq_left hb α x (r := θ) (a := 1 / 2 + x) hθ (by linarith) (by linarith)
  set A := (θ ^ 2)⁻¹ + 5 * (1 + θ) / θ
  set B := 5 / θ
  have hz : ∀ t ∈ (univ : Set ℝ), ‖deriv riemannZeta ((((1 / 2 + x : ℝ)) : ℂ) + t * I)‖ ≤ A + B * |t| := by
    intro t _
    have hre : ((((1 / 2 + x : ℝ)) : ℂ) + t * I).re = 1 / 2 + x := by simp
    have him : ((((1 / 2 + x : ℝ)) : ℂ) + t * I).im = t := by simp
    have hsd : θ ≤ ‖(((1 / 2 + x : ℝ)) : ℂ) + t * I - 1‖ := by
      have := Complex.abs_re_le_norm ((((1 / 2 + x : ℝ)) : ℂ) + t * I - 1)
      have e : ((((1 / 2 + x : ℝ)) : ℂ) + t * I - 1).re = x - 1 / 2 := by simp; ring
      rw [e, abs_of_neg (by linarith)] at this; linarith
    have h := norm_deriv_zeta_le_lin hθ hθ (s := (((1 / 2 + x : ℝ)) : ℂ) + t * I) (by rw [hre]; linarith) hsd
    rw [hre, him] at h
    have habs : |1 / 2 + x| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    have : 5 * (|1 / 2 + x| + θ) / θ ≤ 5 * (1 + θ) / θ := by gcongr
    simp only [A, B]
    linarith
  have W := window_line_bound hb hb1 (A := A) (B := B) (by positivity) (by positivity) hWm hWp x
    MeasurableSet.univ hz
  rw [Measure.restrict_univ] at W
  have R2 := residue_final hb hb1 P' (x := x) (by linarith)
  have hx1' : |x| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have h2 := inv_one_add_sq_ge hx1'
  have he1 : 1 ≤ Real.exp (ε / b) := Real.one_le_exp (div_nonneg (by linarith) hb.le)
  have hc0 : 0 ≤ Real.exp (c / (2 * b)) := (Real.exp_pos _).le
  have hinv : 0 ≤ (1 + x ^ 2)⁻¹ := by positivity
  have hsq : 0 ≤ Real.sqrt (π / b) := Real.sqrt_nonneg _
  rw [hid]
  set L := (A + B + B * |α|) * (Cp + Cm + 2 * K0) / 2
  have hL : 0 ≤ L := by positivity
  have hR : 0 ≤ 2 * π * (2 / θ * Sz θ * 4) := by positivity
  calc Real.exp (-x ^ 2 / (4 * b)) * ‖(∫ t : ℝ, fx b α x ((((1 / 2 + x : ℝ)) : ℂ) + t * I))
        + 2 * π * deriv (Phix b α x) 1‖
      ≤ Real.exp (-x ^ 2 / (4 * b)) * ‖∫ t : ℝ, fx b α x ((((1 / 2 + x : ℝ)) : ℂ) + t * I)‖
        + Real.exp (-x ^ 2 / (4 * b)) * ‖(2 * π * deriv (Phix b α x) 1 : ℂ)‖ := by
        rw [← mul_add]; gcongr; exact norm_add_le _ _
    _ ≤ Real.sqrt (π / b) * ((A + B + B * |α|) * Real.exp (c / (2 * b)) * (Cp + Cm + 2 * K0) / 2)
        + Real.sqrt (π / b) * (2 * π * (2 / θ * Sz θ * 4)) * (1 + x ^ 2)⁻¹ := add_le_add W R2
    _ = Real.sqrt (π / b) * L * Real.exp (c / (2 * b))
        + Real.sqrt (π / b) * (2 * π * (2 / θ * Sz θ * 4)) * (1 + x ^ 2)⁻¹ := by simp only [L]; ring
    _ ≤ _ := by
        nlinarith [mul_nonneg (mul_nonneg hsq hL) (mul_nonneg hc0 hinv), mul_nonneg (mul_nonneg hsq hL) hc0,
          mul_le_mul_of_nonneg_left h2 (mul_nonneg (mul_nonneg hsq hL) hc0),
          mul_nonneg (mul_nonneg hsq hR) (mul_nonneg hc0 hinv),
          mul_nonneg (mul_nonneg hsq hR) (mul_nonneg (by linarith : (0 : ℝ) ≤ Real.exp (ε / b) - 1) hinv),
          mul_nonneg (mul_nonneg hsq hL) (mul_nonneg (Real.exp_pos (ε / b)).le hinv)]

/-- Region (c): `|x − 1/2| < θ`, `x ≠ 1/2` (the bump). -/
lemma region_c {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) {α ε θ τ c Cp Cm : ℝ} (P : Params α ε θ τ)
    (hCp : 0 ≤ Cp) (hCm : 0 ≤ Cm)
    (hWm : smoothWindow b α ≤ Cm * Real.exp (c / b)) (hWp : smoothWindow b (-α) ≤ Cp * Real.exp (c / b))
    {x : ℝ} (hx1 : 1 / 2 - θ < x) (hx2 : x < 1 / 2 + θ) (hx : x ≠ 1 / 2) :
    Real.exp (-x ^ 2 / (4 * b)) * ‖Ix b α x‖
      ≤ Real.sqrt (π / b) * (2 * ((2 * (((τ ^ 2)⁻¹ + 45) + 20 + 20 * |α|) * (Cp + Cm + 2 * K0) / 2)
          + 2 * Sz θ * (2 * τ * Lam1 (1 + 2 * θ) + 2 * ((τ ^ 2)⁻¹ + 45 + 20 * τ))))
        * (Real.exp (c / (2 * b)) + Real.exp (ε / b)) * (1 + x ^ 2)⁻¹ := by
  obtain ⟨hθ, hθε, hθτ, hθ1, hτ, hτ1, hατ⟩ := P
  have hS := Sz_nonneg θ
  have hK := K0_nonneg
  have hτα : τ ≤ |α| := by linarith
  have B := bump_bound hb hb1 hWm hWp (η := θ) (κ := θ) (κ₀ := 2 * θ) (τ := τ) (x := x) hθ hθ (by linarith)
    (by linarith) hτ hτ1 hτα hx1.le hx2.le hx
  have hαt : 1 / 2 + τ ≤ |α| - τ := by linarith
  have hsq2 : (1 / 2 + τ) ^ 2 ≤ (|α| - τ) ^ 2 := pow_le_pow_left₀ (by linarith) hαt 2
  have hEb : Real.exp (((1 / 2 + 2 * θ) ^ 2 - (|α| - τ) ^ 2 + (1 / 2 + θ) ^ 2 - (1 / 2 - θ) ^ 2) / (4 * b))
      ≤ Real.exp (ε / b) := by
    apply Real.exp_le_exp.mpr
    have h0 : ((1 / 2 + 2 * θ) ^ 2 - (|α| - τ) ^ 2 + (1 / 2 + θ) ^ 2 - (1 / 2 - θ) ^ 2) ≤ 0 := by nlinarith
    have : ((1 / 2 + 2 * θ) ^ 2 - (|α| - τ) ^ 2 + (1 / 2 + θ) ^ 2 - (1 / 2 - θ) ^ 2) / (4 * b) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg h0 (by positivity)
    have : 0 ≤ ε / b := div_nonneg (by linarith) hb.le
    linarith
  have hx1' : |x| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have h2 := inv_one_add_sq_ge hx1'
  have hc0 : 0 ≤ Real.exp (c / (2 * b)) := (Real.exp_pos _).le
  have he0 : 0 ≤ Real.exp (ε / b) := (Real.exp_pos _).le
  have hinv : 0 ≤ (1 + x ^ 2)⁻¹ := by positivity
  have hsq : 0 ≤ Real.sqrt (π / b) := Real.sqrt_nonneg _
  set L := 2 * (((τ ^ 2)⁻¹ + 45) + 20 + 20 * |α|) * (Cp + Cm + 2 * K0) / 2
  set Q := 2 * Sz θ * (2 * τ * Lam1 (1 + 2 * θ) + 2 * ((τ ^ 2)⁻¹ + 45 + 20 * τ))
  have hL : 0 ≤ L := by positivity
  have hQ : 0 ≤ Q := by have := Lam1_nonneg (1 + 2 * θ); positivity
  refine B.trans ?_
  calc Real.sqrt (π / b) * (2 * (((τ ^ 2)⁻¹ + 45) + 20 + 20 * |α|) * Real.exp (c / (2 * b))
          * (Cp + Cm + 2 * K0) / 2)
        + Real.sqrt (π / b) * (2 * Sz θ * (2 * τ * Lam1 (1 + 2 * θ) + 2 * ((τ ^ 2)⁻¹ + 45 + 20 * τ)))
          * Real.exp (((1 / 2 + 2 * θ) ^ 2 - (|α| - τ) ^ 2 + (1 / 2 + θ) ^ 2 - (1 / 2 - θ) ^ 2) / (4 * b))
      ≤ Real.sqrt (π / b) * L * Real.exp (c / (2 * b)) + Real.sqrt (π / b) * Q * Real.exp (ε / b) := by
        have e : Real.sqrt (π / b) * (2 * (((τ ^ 2)⁻¹ + 45) + 20 + 20 * |α|) * Real.exp (c / (2 * b))
          * (Cp + Cm + 2 * K0) / 2) = Real.sqrt (π / b) * L * Real.exp (c / (2 * b)) := by simp only [L]; ring
        rw [e]
        gcongr
    _ ≤ _ := by
        nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg (mul_nonneg hsq hL) hc0),
          mul_le_mul_of_nonneg_left h2 (mul_nonneg (mul_nonneg hsq hQ) he0),
          mul_nonneg (mul_nonneg hsq hL) (mul_nonneg he0 hinv),
          mul_nonneg (mul_nonneg hsq hQ) (mul_nonneg hc0 hinv)]

/-- Region (d): `x ≥ 1/2 + θ`. -/
lemma region_d {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) {α ε θ τ c Cp Cm : ℝ} (P : Params α ε θ τ)
    (hCp : 0 ≤ Cp) (hCm : 0 ≤ Cm)
    (hWm : smoothWindow b α ≤ Cm * Real.exp (c / b)) (hWp : smoothWindow b (-α) ≤ Cp * Real.exp (c / b))
    {x : ℝ} (hx : 1 / 2 + θ ≤ x) :
    Real.exp (-x ^ 2 / (4 * b)) * ‖Ix b α x‖
      ≤ Real.sqrt (π / b) * (Lam1 (1 + θ) * 18 * (Cp + Cm + 2 * K0) / 2)
        * (Real.exp (c / (2 * b)) + Real.exp (ε / b)) * (1 + x ^ 2)⁻¹ := by
  obtain ⟨hθ, hθε, hθτ, hθ1, hτ, hτ1, hατ⟩ := P
  have hK := K0_nonneg
  have ha : 1 < 1 / 2 + x := by linarith
  have hid := Ix_eq_right hb α x (a := 1 / 2 + x) ha
  have hz : ∀ t ∈ (univ : Set ℝ), ‖deriv riemannZeta ((((1 / 2 + x : ℝ)) : ℂ) + t * I)‖
      ≤ Lam1 (1 / 2 + x) + 0 * |t| := by
    intro t _
    have h := norm_deriv_zeta_le_Lam1 (s := (((1 / 2 + x : ℝ)) : ℂ) + t * I) (by simpa using ha)
    have hre : ((((1 / 2 + x : ℝ)) : ℂ) + t * I).re = 1 / 2 + x := by simp
    rw [hre] at h; linarith
  have W := window_line_bound hb hb1 (A := Lam1 (1 / 2 + x)) (B := 0) (Lam1_pos _ ha) le_rfl hWm hWp x
    MeasurableSet.univ hz
  rw [Measure.restrict_univ, ← hid] at W
  have hΛ := Lam1_le (σ₀ := 1 + θ) (σ := 1 / 2 + x) (by linarith) (by linarith)
  have h2 : (2 : ℝ) ^ (1 + θ - (1 / 2 + x)) ≤ 18 * (1 + x ^ 2)⁻¹ := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    have hl := Real.log_two_gt_d9
    have hl0 : 0 ≤ Real.log 2 := by linarith
    have e1 : Real.exp (Real.log 2 * (1 + θ - (1 / 2 + x))) ≤ Real.exp (Real.log 2) * Real.exp (-((1 / 2) * |x|)) := by
      rw [← Real.exp_add, Real.exp_le_exp, abs_of_nonneg (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_left (by linarith : θ ≤ 1 / 2) hl0,
        mul_le_mul_of_nonneg_right (by linarith : (1 / 2 : ℝ) ≤ Real.log 2) (by linarith : (0 : ℝ) ≤ x)]
    rw [Real.exp_log (by norm_num)] at e1
    have e2 := exp_neg_abs_le (k := 1 / 2) (by norm_num) x
    norm_num at e2
    linarith
  have hΛ0 := Lam1_nonneg (1 + θ)
  have hc0 : 0 ≤ Real.exp (c / (2 * b)) := (Real.exp_pos _).le
  have he0 : 0 ≤ Real.exp (ε / b) := (Real.exp_pos _).le
  have hsq : 0 ≤ Real.sqrt (π / b) := Real.sqrt_nonneg _
  have hC : 0 ≤ (Cp + Cm + 2 * K0) / 2 := by positivity
  refine W.trans ?_
  have hLam : Lam1 (1 / 2 + x) ≤ Lam1 (1 + θ) * (18 * (1 + x ^ 2)⁻¹) :=
    hΛ.trans (mul_le_mul_of_nonneg_left h2 hΛ0)
  calc Real.sqrt (π / b) * ((Lam1 (1 / 2 + x) + 0 + 0 * |α|) * Real.exp (c / (2 * b)) * (Cp + Cm + 2 * K0) / 2)
      = Real.sqrt (π / b) * (Lam1 (1 / 2 + x) * ((Cp + Cm + 2 * K0) / 2)) * Real.exp (c / (2 * b)) := by ring
    _ ≤ Real.sqrt (π / b) * ((Lam1 (1 + θ) * (18 * (1 + x ^ 2)⁻¹)) * ((Cp + Cm + 2 * K0) / 2))
        * Real.exp (c / (2 * b)) := by gcongr
    _ ≤ _ := by
        have hinv : 0 ≤ (1 + x ^ 2)⁻¹ := by positivity
        have : 0 ≤ Real.sqrt (π / b) * (Lam1 (1 + θ) * 18 * (Cp + Cm + 2 * K0) / 2) * (1 + x ^ 2)⁻¹ := by
          positivity
        nlinarith

/-- **The per-`x` bound.** -/
theorem Ix_bound {α ε c Cp Cm : ℝ} (hα : 1 / 2 < |α|) (hε : 0 < ε) (hc : 0 ≤ c) (hCp : 0 ≤ Cp) (hCm : 0 ≤ Cm)
    (hWm : ∀ b : ℝ, 0 < b → b ≤ 1 → smoothWindow b α ≤ Cm * Real.exp (c / b))
    (hWp : ∀ b : ℝ, 0 < b → b ≤ 1 → smoothWindow b (-α) ≤ Cp * Real.exp (c / b)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ b : ℝ, 0 < b → b ≤ 1 → ∀ x : ℝ, x ≠ 1 / 2 →
      Real.exp (-x ^ 2 / (4 * b)) * ‖Ix b α x‖
        ≤ Real.sqrt (π / b) * M * (Real.exp (c / (2 * b)) + Real.exp (ε / b)) * (1 + x ^ 2)⁻¹ := by
  set τ := min ((|α| - 1 / 2) / 2) 1
  set θ := min (ε / 16) (min (τ / 16) (1 / 64))
  have hτ : 0 < τ := lt_min (by linarith) one_pos
  have hθ : 0 < θ := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have P : Params α ε θ τ :=
    { hθ := hθ, hθε := min_le_left _ _, hθτ := (min_le_right _ _).trans (min_le_left _ _),
      hθ1 := (min_le_right _ _).trans (min_le_right _ _), hτ := hτ, hτ1 := min_le_right _ _,
      hατ := by have := min_le_left ((|α| - 1 / 2) / 2) 1; linarith }
  have hS := Sz_nonneg θ
  have hK := K0_nonneg
  set Ma := Sz θ * (2 * ((39 + 20 * |α|) * K0)) * 4 + 2 * π * (2 / θ * Sz θ * 4)
  set Mb := 2 * ((((θ ^ 2)⁻¹ + 5 * (1 + θ) / θ) + 5 / θ + 5 / θ * |α|) * (Cp + Cm + 2 * K0) / 2)
          + 2 * π * (2 / θ * Sz θ * 4)
  set Mc := 2 * ((2 * (((τ ^ 2)⁻¹ + 45) + 20 + 20 * |α|) * (Cp + Cm + 2 * K0) / 2)
          + 2 * Sz θ * (2 * τ * Lam1 (1 + 2 * θ) + 2 * ((τ ^ 2)⁻¹ + 45 + 20 * τ)))
  set Md := Lam1 (1 + θ) * 18 * (Cp + Cm + 2 * K0) / 2
  have hMa : 0 ≤ Ma := by positivity
  have hMb : 0 ≤ Mb := by positivity
  have hMc : 0 ≤ Mc := by have := Lam1_nonneg (1 + 2 * θ); positivity
  have hMd : 0 ≤ Md := by have := Lam1_nonneg (1 + θ); positivity
  refine ⟨Ma + Mb + Mc + Md, by positivity, fun b hb hb1 x hx => ?_⟩
  have hE : 0 ≤ Real.sqrt (π / b) * (Real.exp (c / (2 * b)) + Real.exp (ε / b)) * (1 + x ^ 2)⁻¹ := by positivity
  have mono : ∀ Mi : ℝ, Mi ≤ Ma + Mb + Mc + Md →
      Real.sqrt (π / b) * Mi * (Real.exp (c / (2 * b)) + Real.exp (ε / b)) * (1 + x ^ 2)⁻¹
        ≤ Real.sqrt (π / b) * (Ma + Mb + Mc + Md) * (Real.exp (c / (2 * b)) + Real.exp (ε / b)) * (1 + x ^ 2)⁻¹ := by
    intro Mi hMi
    have := mul_le_mul_of_nonneg_left hMi hE
    nlinarith
  rcases lt_or_ge x (θ - 1 / 4) with h1 | h1
  · exact (region_a hb hb1 P hc h1).trans (mono Ma (by linarith))
  · rcases le_or_gt x (1 / 2 - θ) with h2 | h2
    · exact (region_b hb hb1 P hCp hCm (hWm b hb hb1) (hWp b hb hb1) h1 h2).trans (mono Mb (by linarith))
    · rcases lt_or_ge x (1 / 2 + θ) with h3 | h3
      · exact (region_c hb hb1 P hCp hCm (hWm b hb hb1) (hWp b hb hb1) h2 h3 hx).trans (mono Mc (by linarith))
      · exact (region_d hb hb1 P hCp hCm (hWm b hb hb1) (hWp b hb hb1) h3).trans (mono Md (by linarith))

/-! ## The prime sum, and the ladder -/

lemma ae_ne_half : ∀ᵐ x : ℝ, x ≠ 1 / 2 := by
  rw [ae_iff]
  have : {a : ℝ | ¬a ≠ 1 / 2} = {1 / 2} := by ext; simp
  rw [this]; exact Real.volume_singleton

/-- **The prime sum under a smooth window bound** at `±α`, `|α| > 1/2`:
`‖S_b(α)‖ ≤ √(π/b) C e^{(c/2 + 2ε)/b}` for every `ε > 0`. -/
theorem primeSumSym_le_of_smoothWindow {α ε c Cp Cm : ℝ} (hα : 1 / 2 < |α|) (hε : 0 < ε) (hc : 0 ≤ c)
    (hCp : 0 ≤ Cp) (hCm : 0 ≤ Cm)
    (hWm : ∀ b : ℝ, 0 < b → b ≤ 1 → smoothWindow b α ≤ Cm * Real.exp (c / b))
    (hWp : ∀ b : ℝ, 0 < b → b ≤ 1 → smoothWindow b (-α) ≤ Cp * Real.exp (c / b)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : ℝ, 0 < b → b ≤ 1 →
      ‖FleetPrimeSideConsequences.primeSumSym b α‖ ≤ Real.sqrt (π / b) * (C * Real.exp ((c / 2 + 2 * ε) / b)) := by
  obtain ⟨M, hM, hI⟩ := Ix_bound hα hε hc hCp hCm hWm hWp
  refine ⟨2 * M / ε, by positivity, fun b hb hb1 => ?_⟩
  set E := Real.exp (c / (2 * b)) + Real.exp (ε / b)
  have hE0 : 0 ≤ E := by positivity
  set g : ℝ → ℝ := fun x => Real.sqrt (π / b) * M * E * (1 + x ^ 2)⁻¹
  have ig : Integrable g := integrable_inv_one_add_sq.const_mul _
  have hpt : ∀ᵐ x : ℝ, ‖((Real.exp (-x ^ 2 / (4 * b)) : ℝ) : ℂ) * Ix b α x‖ ≤ g x := by
    filter_upwards [ae_ne_half] with x hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hI b hb hb1 x hx
  have hint := norm_integral_le_of_norm_le ig hpt
  have hIg : ∫ x, g x = Real.sqrt (π / b) * M * E * π := by
    simp only [g]; rw [integral_const_mul, integral_univ_inv_one_add_sq]
  have hrep := primeSumSym_eq_double hb α
  have hsq0 : 0 < Real.sqrt (4 * π * b) := Real.sqrt_pos.mpr (by positivity)
  have hkey : Real.sqrt (4 * π * b) * ‖FleetPrimeSideConsequences.primeSumSym b α‖
      ≤ Real.sqrt (π / b) * M * E / 2 := by
    have : ‖(Real.sqrt (4 * π * b) : ℂ) * FleetPrimeSideConsequences.primeSumSym b α‖
        = Real.sqrt (4 * π * b) * ‖FleetPrimeSideConsequences.primeSumSym b α‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsq0]
    rw [← this, hrep, norm_mul]
    have h2 : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
      rw [show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [h2]
    calc 1 / (2 * π) * ‖∫ x : ℝ, ((Real.exp (-x ^ 2 / (4 * b)) : ℝ) : ℂ) * Ix b α x‖
        ≤ 1 / (2 * π) * (Real.sqrt (π / b) * M * E * π) := by rw [← hIg]; gcongr
      _ = _ := by field_simp
  -- `√(4πb) ≥ b` and `ε/b ≤ e^{ε/b}`
  have hsb : b ≤ Real.sqrt (4 * π * b) := by
    calc b = Real.sqrt (b ^ 2) := (Real.sqrt_sq hb.le).symm
      _ ≤ Real.sqrt (4 * π * b) := Real.sqrt_le_sqrt (by
          nlinarith [mul_le_mul_of_nonneg_left hb1 hb.le, Real.pi_gt_three, mul_pos hb Real.pi_pos])
  have heb : ε / b ≤ Real.exp (ε / b) := by linarith [Real.add_one_le_exp (ε / b)]
  have hEle : E ≤ 2 * Real.exp ((c / 2 + ε) / b) := by
    have h1 : Real.exp (c / (2 * b)) ≤ Real.exp ((c / 2 + ε) / b) := by
      apply Real.exp_le_exp.mpr; rw [div_le_div_iff₀ (by positivity) hb]; nlinarith
    have h2 : Real.exp (ε / b) ≤ Real.exp ((c / 2 + ε) / b) := by
      apply Real.exp_le_exp.mpr; apply div_le_div_of_nonneg_right _ hb.le; linarith
    simp only [E]; linarith
  have hsq : 0 ≤ Real.sqrt (π / b) := Real.sqrt_nonneg _
  have hfin : Real.sqrt (π / b) * M * E / 2
      ≤ Real.sqrt (4 * π * b) * (Real.sqrt (π / b) * (2 * M / ε * Real.exp ((c / 2 + 2 * ε) / b))) := by
    have e3 : Real.exp ((c / 2 + 2 * ε) / b) = Real.exp (ε / b) * Real.exp ((c / 2 + ε) / b) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    rw [e3]
    have hF := Real.exp_pos ((c / 2 + ε) / b)
    have step1 : Real.sqrt (π / b) * M * E / 2 ≤ Real.sqrt (π / b) * M * Real.exp ((c / 2 + ε) / b) := by
      have := mul_le_mul_of_nonneg_left hEle (mul_nonneg hsq hM); nlinarith
    have step2 : Real.sqrt (π / b) * M * Real.exp ((c / 2 + ε) / b)
        = b * (Real.sqrt (π / b) * (2 * M / ε * ((ε / b) * Real.exp ((c / 2 + ε) / b)))) / 2 := by
      field_simp
    have step3 : b * (Real.sqrt (π / b) * (2 * M / ε * ((ε / b) * Real.exp ((c / 2 + ε) / b)))) / 2
        ≤ Real.sqrt (4 * π * b) * (Real.sqrt (π / b) * (2 * M / ε * (Real.exp (ε / b) * Real.exp ((c / 2 + ε) / b)))) := by
      have hA : 0 ≤ Real.sqrt (π / b) * (2 * M / ε * ((ε / b) * Real.exp ((c / 2 + ε) / b))) := by positivity
      have hB : Real.sqrt (π / b) * (2 * M / ε * ((ε / b) * Real.exp ((c / 2 + ε) / b)))
          ≤ Real.sqrt (π / b) * (2 * M / ε * (Real.exp (ε / b) * Real.exp ((c / 2 + ε) / b))) := by gcongr
      have hB0 : 0 ≤ Real.sqrt (π / b) * (2 * M / ε * (Real.exp (ε / b) * Real.exp ((c / 2 + ε) / b))) := by
        positivity
      nlinarith [mul_le_mul hsb hB hA hsq0.le]
    linarith
  have := hkey.trans hfin
  exact le_of_mul_le_mul_left this hsq0

/-- **Smooth window rate `c` ⇒ strip `√(2c)`.** If at every centre `|α| > 1/2` the smooth window grows at
most like `C e^{c/b}` (`0 < b ≤ 1`, `C` may depend on `α`), then every nontrivial zero satisfies
`|Re ρ − 1/2| ≤ √(2c)`. -/
theorem zeros_in_strip_of_smoothWindow {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ α : ℝ, 1 / 2 < |α| → ∃ C : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 → smoothWindow b α ≤ C * Real.exp (c / b)) :
    ∀ x : Index, |(canonical x).re - 1 / 2| ≤ Real.sqrt (2 * c) := by
  have hstrip : ∀ ε : ℝ, 0 < ε → ∀ x : Index,
      |(canonical x).re - 1 / 2| ≤ 2 * Real.sqrt (c / 2 + 2 * ε) := by
    intro ε hε
    apply FleetExponentLadder.zeros_in_strip_of_pole_prime_exp_bound (by positivity)
    intro α
    by_cases hα : 1 / 2 < |α|
    · obtain ⟨Cm, hCm⟩ := h α hα
      obtain ⟨Cp, hCp⟩ := h (-α) (by rwa [abs_neg])
      have absC : ∀ (β C : ℝ), (∀ b : ℝ, 0 < b → b ≤ 1 → smoothWindow b β ≤ C * Real.exp (c / b)) →
          ∀ b : ℝ, 0 < b → b ≤ 1 → smoothWindow b β ≤ |C| * Real.exp (c / b) :=
        fun β C hC b hb hb1 => (hC b hb hb1).trans
          (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)
      obtain ⟨C, hC0, hC⟩ := primeSumSym_le_of_smoothWindow hα hε hc (abs_nonneg Cp) (abs_nonneg Cm)
        (absC α Cm hCm) (absC (-α) Cp hCp)
      refine ⟨C + 2, fun b hb hb1 => ?_⟩
      have hE : 1 ≤ Real.exp ((c / 2 + 2 * ε) / b) := Real.one_le_exp (by positivity)
      have hsq := Real.sqrt_nonneg (π / b)
      have h1 := hC b hb hb1
      have h4 := FleetPrimeSideConsequences.norm_poleTerm_le_of_half_le_abs hb hα.le
      rw [FleetPrimeSideConsequences.poleMinusPrimes_eq]
      calc ‖FleetPrimeSideConsequences.poleTerm b α - FleetPrimeSideConsequences.primeSumSym b α‖
          ≤ ‖FleetPrimeSideConsequences.poleTerm b α‖ + ‖FleetPrimeSideConsequences.primeSumSym b α‖ :=
            norm_sub_le _ _
        _ ≤ 2 * Real.sqrt (π / b) + Real.sqrt (π / b) * (C * Real.exp ((c / 2 + 2 * ε) / b)) := add_le_add h4 h1
        _ ≤ Real.sqrt (π / b) * ((C + 2) * Real.exp ((c / 2 + 2 * ε) / b)) := by
            nlinarith [mul_le_mul_of_nonneg_left hE hsq]
    · push Not at hα
      obtain ⟨C', hC'⟩ := FleetPrimeSideConsequences.pole_prime_bound_of_verified
        FleetLowZeroFree.verifiedTo_three_halves (α := α) (by linarith)
      refine ⟨|C'|, fun b hb hb1 => ?_⟩
      have hE : 1 ≤ Real.exp ((c / 2 + 2 * ε) / b) := Real.one_le_exp (by positivity)
      have hsq := Real.sqrt_nonneg (π / b)
      calc ‖FleetPrimePoleBoundRH.poleMinusPrimes b α‖ ≤ Real.sqrt (π / b) * C' := hC' b hb hb1
        _ ≤ Real.sqrt (π / b) * |C'| := mul_le_mul_of_nonneg_left (le_abs_self _) hsq
        _ ≤ Real.sqrt (π / b) * (|C'| * Real.exp ((c / 2 + 2 * ε) / b)) := by
            apply mul_le_mul_of_nonneg_left _ hsq
            nlinarith [abs_nonneg C']
  intro x
  set d := |(canonical x).re - 1 / 2|
  have hd0 : 0 ≤ d := abs_nonneg _
  have hsq : (d / 2) ^ 2 ≤ c / 2 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have h1 := hstrip (ε / 2) (by positivity) x
    have h2 : d / 2 ≤ Real.sqrt (c / 2 + 2 * (ε / 2)) := by linarith
    have := (Real.le_sqrt (by positivity) (by positivity)).mp h2
    linarith
  have h3 : d / 2 ≤ Real.sqrt (c / 2) := (Real.le_sqrt (by positivity) (by positivity)).mpr hsq
  have h4 : Real.sqrt (2 * c) = 2 * Real.sqrt (c / 2) := by
    rw [show 2 * c = 2 ^ 2 * (c / 2) by ring, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [h4]
  linarith

/-! ## The optimal smooth rate -/

/-- `SmoothWindowRate c` (`c ≥ 0`) ⇒ `D ≤ √(2c)`, `D = sup |Re ρ − 1/2|`. -/
theorem zeroDev_le_of_smoothWindowRate {c : ℝ} (hc : 0 ≤ c) (h : SmoothWindowRate c) :
    zeroDev ≤ Real.sqrt (2 * c) := by
  have hs := zeros_in_strip_of_smoothWindow hc (fun α _ => h α)
  refine (zeroDev_le_iff (Real.sqrt_nonneg _)).mpr fun ρ hρ => ?_
  obtain ⟨x, hx⟩ := multEnum_canonical.exists_index hρ
  rw [← hx]; exact hs x

/-- The optimal smooth window rate `inf {c ≥ 0 | SmoothWindowRate c}`. -/
def smoothWindowRateInf : ℝ := sInf {c : ℝ | 0 ≤ c ∧ SmoothWindowRate c}

/-- **The exact optimal smooth rate**: `inf {c ≥ 0 | SmoothWindowRate c} = D²/2`, `D = sup |Re ρ − 1/2|`
(no hypothesis). -/
theorem smoothWindowRateInf_eq : smoothWindowRateInf = zeroDev ^ 2 / 2 := by
  have hne : (1 / 8 + 1 : ℝ) ∈ {c : ℝ | 0 ≤ c ∧ SmoothWindowRate c} :=
    ⟨by norm_num, smoothWindowRate_one_eighth one_pos⟩
  have hbdd : BddBelow {c : ℝ | 0 ≤ c ∧ SmoothWindowRate c} := ⟨0, fun _ h => h.1⟩
  have hD := zeroDev_nonneg
  apply le_antisymm
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hs : StripBound zeroDev := fun ρ hρ => le_zeroDev hρ
    exact csInf_le hbdd ⟨by positivity, smoothWindowRate_of_strip hD hs hε⟩
  · refine le_csInf ⟨_, hne⟩ fun c hc => ?_
    have h1 := zeroDev_le_of_smoothWindowRate hc.1 hc.2
    have h2 : zeroDev ^ 2 ≤ 2 * c := by
      calc zeroDev ^ 2 ≤ Real.sqrt (2 * c) ^ 2 := pow_le_pow_left₀ hD h1 2
        _ = 2 * c := Real.sq_sqrt (by linarith [hc.1])
    linarith

/-- No smooth rate below `D²/2`. -/
theorem not_smoothWindowRate_of_lt {c : ℝ} (hc0 : 0 ≤ c) (hc : c < zeroDev ^ 2 / 2) : ¬ SmoothWindowRate c := by
  intro h
  have h1 := zeroDev_le_of_smoothWindowRate hc0 h
  have h2 : zeroDev ^ 2 ≤ 2 * c :=
    (pow_le_pow_left₀ zeroDev_nonneg h1 2).trans (le_of_eq (Real.sq_sqrt (by linarith)))
  linarith

/-- **RH ⟺ every positive smooth rate.** -/
theorem RH_iff_smoothWindowRate : RiemannHypothesis ↔ ∀ c : ℝ, 0 < c → SmoothWindowRate c := by
  rw [RH_iff_zeroDev_eq_zero]
  constructor
  · intro hD c hc
    have hs : StripBound 0 := fun ρ hρ => by have := le_zeroDev hρ; rwa [hD] at this
    have := smoothWindowRate_of_strip le_rfl hs hc
    simpa using this
  · intro h
    have hD := zeroDev_nonneg
    have hsq : zeroDev ^ 2 ≤ 0 := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have h1 := zeroDev_le_of_smoothWindowRate (by positivity) (h (ε / 2) (by positivity))
      have := (pow_le_pow_left₀ hD h1 2).trans (le_of_eq (Real.sq_sqrt (by positivity)))
      linarith
    nlinarith

/-- **The `QuasiRH` instance of the optimal rate**: `QuasiRH` ⇒ `inf rate ≤ 9/128`. -/
theorem smoothWindowRateInf_le_of_quasiRH (hQ : QuasiRHWiring.QuasiRH) : smoothWindowRateInf ≤ 9 / 128 := by
  rw [smoothWindowRateInf_eq]
  have h := (zeroDev_le_iff (by norm_num : (0 : ℝ) ≤ 3 / 8)).mpr (stripBound_of_quasiRH hQ)
  have := pow_le_pow_left₀ zeroDev_nonneg h 2
  nlinarith

/-- Unconditionally `inf rate ≤ 1/8`. -/
theorem smoothWindowRateInf_le_one_eighth : smoothWindowRateInf ≤ 1 / 8 := by
  rw [smoothWindowRateInf_eq]
  have := pow_le_pow_left₀ zeroDev_nonneg zeroDev_le_half 2
  nlinarith

end FleetSmoothWindow
