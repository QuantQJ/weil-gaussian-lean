import FleetHeadContourSubexp

/-!
# Window rate ⇒ quantitative strip, via Cauchy–Schwarz

`FleetHeadContourSubexp.head_le_of_window_at` bounds the critical-line integral with the pointwise
AM-GM inequality `|M||ζ'| ≤ (|M|² + |ζ'|²)/2`, which makes the window integral `X` enter linearly.
Cauchy–Schwarz in the Gaussian weight,
`∫ |M||ζ'| w ≤ √(∫ |M|² w) · √(∫ |ζ'|² w)`,
makes it enter as `√X`. That halves the exponent: a window growth `e^{c/b}` becomes a head growth
`e^{(c/2)/b}` (up to `e^{ε/b}`).

* `le_sqrt_mul_of_forall`      : if `2J ≤ λX + Z/λ` for every `λ > 0` then `J ≤ √X √Z`
                                 (the weighted AM-GM family, optimised: Cauchy–Schwarz).
* `head_le_of_window_at_cs`    : `|head b α (cut b)| ≤ √(π/b) (A (1/b + (11/10)(1/b)²) + (√(X₁ Zc α) + √(X₂ Zc α))/(2π))`,
                                 `A = 2 e^{(1+|α|)/2} e^{11/10}`.
* `strip_of_head_exp`          : the fixed-exponent form of `head_exp_ladder`: a head bound `√(π/b) C e^{c/b}` at every
                                 `|α| ≥ 1/2` confines every zero to `|Re ρ − 1/2| ≤ 2√c`.
* `zeros_in_strip_of_window_rate` : a window bound `C e^{c/b}` at every `|α| ≥ 1/2` confines every zero to
                                 `|Re ρ − 1/2| ≤ √(2c)`.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set MeasureTheory
open scoped Real
open OffLineDetection Reduction ZeroSumLimit GaussianTest

namespace FleetHeadContour

/-- **Optimised weighted AM-GM.** If `2J ≤ λX + Z/λ` for every `λ > 0`, then `J ≤ √X · √Z`. -/
lemma le_sqrt_mul_of_forall {J X Z : ℝ} (hX : 0 ≤ X) (hZ : 0 ≤ Z)
    (h : ∀ l : ℝ, 0 < l → 2 * J ≤ l * X + Z / l) : J ≤ Real.sqrt X * Real.sqrt Z := by
  set x := Real.sqrt X with hx
  set z := Real.sqrt Z with hz
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have hxx : x * x = X := Real.mul_self_sqrt hX
  have hzz : z * z = Z := Real.mul_self_sqrt hZ
  have key : ∀ δ : ℝ, 0 < δ → 2 * J ≤ 2 * (x * z) + δ * (x + z) := by
    intro δ hδ
    have hxδ : 0 < x + δ := by linarith
    have hzδ : 0 < z + δ := by linarith
    have hl : 0 < (z + δ) / (x + δ) := div_pos hzδ hxδ
    have h0 := h _ hl
    have h1 : (z + δ) / (x + δ) * X ≤ (z + δ) * x := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hxδ, ← hxx]
      nlinarith [mul_nonneg (mul_nonneg hzδ.le hx0) hδ.le]
    have h2 : Z / ((z + δ) / (x + δ)) ≤ z * (x + δ) := by
      rw [div_div_eq_mul_div, div_le_iff₀ hzδ, ← hzz]
      nlinarith [mul_nonneg (mul_nonneg hz0 hxδ.le) hδ.le]
    nlinarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hs : 0 < x + z + 1 := by linarith
  have hδ : 0 < ε / (x + z + 1) := div_pos hε hs
  have hk := key _ hδ
  have hb : ε / (x + z + 1) * (x + z) ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hs]
    nlinarith
  linarith

/-- **Head bound at one `b` from the two window integrals, Cauchy–Schwarz form.** -/
theorem head_le_of_window_at_cs {α : ℝ} (hα : 1 / 2 ≤ |α|) {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    {X₁ X₂ : ℝ} (hX₁ : 0 ≤ X₁) (hX₂ : 0 ≤ X₂)
    (h₁ : ∫ t : ℝ, ‖Mpoly (FleetFiniteHeadRH.cut b) (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2
        * Real.exp (-(t - α) ^ 2 / (4 * b)) ≤ X₁)
    (h₂ : ∫ t : ℝ, ‖Mpoly (FleetFiniteHeadRH.cut b) (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2
        * Real.exp (-(t - -α) ^ 2 / (4 * b)) ≤ X₂) :
    |FleetFiniteHeadRH.head b α (FleetFiniteHeadRH.cut b)| ≤ Real.sqrt (π / b) *
      (2 * Real.exp ((1 + |α|) / 2) * Real.exp (11 / 10) * ((1 / b) + (11 / 10) * (1 / b) ^ 2)
        + (Real.sqrt (X₁ * Zc α) + Real.sqrt (X₂ * Zc α)) / (2 * π)) := by
  set M := FleetFiniteHeadRH.cut b with hM
  set sq := Real.sqrt (π / b) with hsq
  have hsq0 : 0 ≤ sq := Real.sqrt_nonneg _
  set u := 1 / b with hu
  set wp : ℝ → ℝ := fun t => Real.exp (-(t - -α) ^ 2 / (4 * b)) with hwp
  set wm : ℝ → ℝ := fun t => Real.exp (-(t - α) ^ 2 / (4 * b)) with hwm
  set Mn : ℝ → ℝ := fun t => ‖Mpoly M (((1 / 2 : ℝ) : ℂ) + t * I)‖ with hMn
  set Zn : ℝ → ℝ := fun t => ‖deriv riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖ with hZn
  have hZc0 : 0 ≤ Zc α := by unfold Zc; positivity
  have iMp : Integrable (fun t => Mn t ^ 2 * wp t) := integrable_M_window hb M (-α)
  have iMm : Integrable (fun t => Mn t ^ 2 * wm t) := integrable_M_window hb M α
  have hZcneg : Zc (-α) = Zc α := by unfold Zc; ring
  have iZp : Integrable (fun t => Zn t ^ 2 * wp t) := (zeta_window hb hb1 (-α)).1
  have iZm : Integrable (fun t => Zn t ^ 2 * wm t) := (zeta_window hb hb1 α).1
  have bZp : ∫ t, Zn t ^ 2 * wp t ≤ Zc α := by
    have := (zeta_window hb hb1 (-α)).2; rw [hZcneg] at this; exact this
  have bZm : ∫ t, Zn t ^ 2 * wm t ≤ Zc α := (zeta_window hb hb1 α).2
  have cMn : Continuous Mn :=
    ((differentiable_Mpoly M).continuous.comp (continuous_line (1 / 2))).norm
  have cZn : Continuous Zn :=
    (continuous_deriv_zeta_line (x := 1 / 2) (by norm_num)).norm
  have cwp : Continuous wp := by simp only [hwp]; fun_prop
  have cwm : Continuous wm := by simp only [hwm]; fun_prop
  have hwp0 : ∀ t, 0 ≤ wp t := fun t => (Real.exp_pos _).le
  have hwm0 : ∀ t, 0 ≤ wm t := fun t => (Real.exp_pos _).le
  -- the weighted products `w |M| |ζ'|`
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
  -- Cauchy–Schwarz for each weight
  have cs : ∀ w : ℝ → ℝ, (∀ t, 0 ≤ w t) →
      Integrable (fun t => Mn t ^ 2 * w t) → Integrable (fun t => Zn t ^ 2 * w t) →
      Integrable (fun t => w t * (Mn t * Zn t)) → ∀ X : ℝ, 0 ≤ X →
      ∫ t, Mn t ^ 2 * w t ≤ X → ∫ t, Zn t ^ 2 * w t ≤ Zc α →
      ∫ t, w t * (Mn t * Zn t) ≤ Real.sqrt X * Real.sqrt (Zc α) := by
    intro w hw0 iM iZ iH X hX hMX hZX
    refine le_sqrt_mul_of_forall hX hZc0 fun l hl => ?_
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
    have e : Zc α / l = 2 * ((1 / (2 * l)) * Zc α) := by field_simp
    have hA := mul_le_mul_of_nonneg_left hMX hl2
    have hB := mul_le_mul_of_nonneg_left hZX hl3
    rw [e]
    nlinarith
  have csp := cs wp hwp0 iMp iZp iHp X₂ hX₂ h₂ bZp
  have csm := cs wm hwm0 iMm iZm iHm X₁ hX₁ h₁ bZm
  -- the critical-line integrand
  set F : ℝ → ℂ := fun t => LGw b α (((1 / 2 : ℝ) : ℂ) + t * I) * Mpoly M (((1 / 2 : ℝ) : ℂ) + t * I)
      * (-deriv riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)) with hF
  have hFi : Integrable F := by
    have := integrable_f_line hb α M (x := 1 / 2) (by norm_num) (by norm_num)
    simpa [Phi, hF] using this
  have hFG : ∀ t, ‖F t‖ ≤ sq * (wp t * (Mn t * Zn t)) + sq * (wm t * (Mn t * Zn t)) := by
    intro t
    have hL := norm_LGw_le b α (1 / 2) t
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
      Real.exp_zero, mul_one] at hL
    have hwpe : Real.exp (-(t + α) ^ 2 / (4 * b)) = wp t := by simp only [hwp, sub_neg_eq_add]
    rw [hwpe] at hL
    have hMn0 : 0 ≤ Mn t := norm_nonneg _
    have hZn0 : 0 ≤ Zn t := norm_nonneg _
    simp only [hF, norm_mul, norm_neg]
    change ‖LGw b α (((1 / 2 : ℝ) : ℂ) + t * I)‖ * Mn t * Zn t ≤ _
    calc ‖LGw b α (((1 / 2 : ℝ) : ℂ) + t * I)‖ * Mn t * Zn t
        ≤ (sq * (wp t + wm t)) * Mn t * Zn t := by
          apply mul_le_mul_of_nonneg_right _ hZn0
          apply mul_le_mul_of_nonneg_right _ hMn0
          simpa [hwm] using hL
      _ = _ := by ring
  have hInt : ‖∫ t, F t‖ ≤ sq * (Real.sqrt X₂ * Real.sqrt (Zc α) + Real.sqrt X₁ * Real.sqrt (Zc α)) := by
    calc ‖∫ t, F t‖ ≤ ∫ t, ‖F t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t, (sq * (wp t * (Mn t * Zn t)) + sq * (wm t * (Mn t * Zn t))) :=
          integral_mono hFi.norm ((iHp.const_mul _).add (iHm.const_mul _)) hFG
      _ = sq * (∫ t, wp t * (Mn t * Zn t)) + sq * ∫ t, wm t * (Mn t * Zn t) := by
          rw [integral_add (iHp.const_mul _) (iHm.const_mul _), integral_const_mul, integral_const_mul]
      _ ≤ sq * (Real.sqrt X₂ * Real.sqrt (Zc α)) + sq * (Real.sqrt X₁ * Real.sqrt (Zc α)) :=
          add_le_add (mul_le_mul_of_nonneg_left csp hsq0) (mul_le_mul_of_nonneg_left csm hsq0)
      _ = _ := by ring
  -- the pole term
  have hR := norm_deriv_Phi_one_le hb hb1 hα M
  have hMb := cut_rpow_le hb
  have hlog := log_cut_le hb hb1
  have hR' : ‖deriv (Phi b α M) 1‖ ≤
      sq * (2 * Real.exp ((1 + |α|) / 2) * Real.exp (11 / 10) * (u + (11 / 10) * u ^ 2)) := by
    refine hR.trans ?_
    have h1 : (M : ℝ) ^ b * (1 + Real.log M) ≤ Real.exp (11 / 10) * (1 + 11 / (10 * b)) :=
      mul_le_mul hMb (by linarith) (by positivity) (Real.exp_pos _).le
    have e : u + (11 / 10) * u ^ 2 = (1 + 11 / (10 * b)) / b := by rw [hu]; field_simp
    rw [e]
    have hk : 0 ≤ 2 * Real.sqrt (π / b) * Real.exp ((1 + |α|) / 2) := by positivity
    calc 2 * Real.sqrt (π / b) * Real.exp ((1 + |α|) / 2) * ((M : ℝ) ^ b * (1 + Real.log M)) / b
        ≤ 2 * Real.sqrt (π / b) * Real.exp ((1 + |α|) / 2) * (Real.exp (11 / 10) * (1 + 11 / (10 * b))) / b :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hk) hb.le
      _ = _ := by rw [hsq]; ring
  have hid := head_eq_critical_line hb α M
  have hhead : |FleetFiniteHeadRH.head b α M| ≤ ‖deriv (Phi b α M) 1‖ + (1 / (2 * π)) * ‖∫ t, F t‖ := by
    have : ‖((FleetFiniteHeadRH.head b α M : ℝ) : ℂ)‖ = |FleetFiniteHeadRH.head b α M| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [← this, hid]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_mul]
    congr 2
    rw [show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hInt' : (1 / (2 * π)) * ‖∫ t, F t‖
      ≤ sq * ((Real.sqrt (X₁ * Zc α) + Real.sqrt (X₂ * Zc α)) / (2 * π)) := by
    rw [Real.sqrt_mul hX₁, Real.sqrt_mul hX₂]
    calc (1 / (2 * π)) * ‖∫ t, F t‖
        ≤ (1 / (2 * π)) * (sq * (Real.sqrt X₂ * Real.sqrt (Zc α) + Real.sqrt X₁ * Real.sqrt (Zc α))) :=
          mul_le_mul_of_nonneg_left hInt (by positivity)
      _ = _ := by ring
  calc |FleetFiniteHeadRH.head b α M| ≤ ‖deriv (Phi b α M) 1‖ + (1 / (2 * π)) * ‖∫ t, F t‖ := hhead
    _ ≤ sq * (2 * Real.exp ((1 + |α|) / 2) * Real.exp (11 / 10) * (u + (11 / 10) * u ^ 2))
        + sq * ((Real.sqrt (X₁ * Zc α) + Real.sqrt (X₂ * Zc α)) / (2 * π)) := add_le_add hR' hInt'
    _ = _ := by ring

/-- **Fixed-exponent head ladder.** A head bound `√(π/b) C e^{c/b}` at every `|α| ≥ 1/2` confines every
nontrivial zero to `|Re ρ − 1/2| ≤ 2√c`. (The argument of `head_exp_ladder`, at one exponent `c`.) -/
theorem strip_of_head_exp {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ α : ℝ, 1 / 2 ≤ |α| → ∃ C : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      |FleetFiniteHeadRH.head b α (FleetFiniteHeadRH.cut b)| ≤ Real.sqrt (π / b) * (C * Real.exp (c / b))) :
    ∀ x : Index, |(canonical x).re - 1 / 2| ≤ 2 * Real.sqrt c := by
  apply FleetExponentLadder.zeros_in_strip_of_pole_prime_exp_bound hc
  intro α
  by_cases hα : 1 / 2 ≤ |α|
  · obtain ⟨C, hC⟩ := h α hα
    refine ⟨|C| + 10, fun b hb hb1 => ?_⟩
    have hE : 1 ≤ Real.exp (c / b) := Real.one_le_exp (div_nonneg hc hb.le)
    have hsq := Real.sqrt_nonneg (π / b)
    have h1 := hC b hb hb1
    have h2 := FleetFiniteHeadRH.primeSumSym_sub_head hb hb1 α
    have h3 := FleetFiniteHeadRH.exp_tail_le hb hb1
    have h4 := FleetPrimeSideConsequences.norm_poleTerm_le_of_half_le_abs hb hα
    have hh : ‖(FleetFiniteHeadRH.head b α (FleetFiniteHeadRH.cut b) : ℂ)‖
        = |FleetFiniteHeadRH.head b α (FleetFiniteHeadRH.cut b)| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    have h5 : ‖FleetPrimeSideConsequences.primeSumSym b α‖
        ≤ |FleetFiniteHeadRH.head b α (FleetFiniteHeadRH.cut b)| + 8 * Real.exp (-51 / (80 * b)) := by
      have := norm_le_insert' (FleetPrimeSideConsequences.primeSumSym b α)
        (FleetFiniteHeadRH.head b α (FleetFiniteHeadRH.cut b) : ℂ)
      rw [hh] at this; linarith
    rw [FleetPrimeSideConsequences.poleMinusPrimes_eq]
    have hCC : C * Real.exp (c / b) ≤ |C| * Real.exp (c / b) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
    calc ‖FleetPrimeSideConsequences.poleTerm b α - FleetPrimeSideConsequences.primeSumSym b α‖
        ≤ ‖FleetPrimeSideConsequences.poleTerm b α‖ + ‖FleetPrimeSideConsequences.primeSumSym b α‖ :=
          norm_sub_le _ _
      _ ≤ 2 * Real.sqrt (π / b) + (Real.sqrt (π / b) * (|C| * Real.exp (c / b)) + Real.sqrt (π / b) * 8) := by
          nlinarith [mul_le_mul_of_nonneg_left hCC hsq]
      _ ≤ Real.sqrt (π / b) * ((|C| + 10) * Real.exp (c / b)) := by
          nlinarith [mul_le_mul_of_nonneg_left hE hsq, abs_nonneg C]
  · push Not at hα
    obtain ⟨C', hC'⟩ := FleetPrimeSideConsequences.pole_prime_bound_of_verified
      FleetLowZeroFree.verifiedTo_three_halves (α := α) (by linarith)
    refine ⟨|C'|, fun b hb hb1 => ?_⟩
    have hE : 1 ≤ Real.exp (c / b) := Real.one_le_exp (div_nonneg hc hb.le)
    have hsq := Real.sqrt_nonneg (π / b)
    calc ‖FleetPrimePoleBoundRH.poleMinusPrimes b α‖ ≤ Real.sqrt (π / b) * C' := hC' b hb hb1
      _ ≤ Real.sqrt (π / b) * |C'| := mul_le_mul_of_nonneg_left (le_abs_self _) hsq
      _ ≤ Real.sqrt (π / b) * (|C'| * Real.exp (c / b)) := by
          apply mul_le_mul_of_nonneg_left _ hsq
          nlinarith [abs_nonneg C']

/-- **Window rate ⇒ strip.** If at every centre `|α| ≥ 1/2` the window integral of `M_{cut b}` grows at most
like `C e^{c/b}` (`0 < b ≤ 1`), then every nontrivial zero satisfies `|Re ρ − 1/2| ≤ √(2c)`. -/
theorem zeros_in_strip_of_window_rate {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ α : ℝ, 1 / 2 ≤ |α| → ∃ C : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      ∫ t : ℝ, ‖Mpoly (FleetFiniteHeadRH.cut b) (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2
        * Real.exp (-(t - α) ^ 2 / (4 * b)) ≤ C * Real.exp (c / b)) :
    ∀ x : Index, |(canonical x).re - 1 / 2| ≤ Real.sqrt (2 * c) := by
  -- for every `ε > 0`, the strip of half-width `2√(c/2 + ε)`
  have hstrip : ∀ ε : ℝ, 0 < ε → ∀ x : Index,
      |(canonical x).re - 1 / 2| ≤ 2 * Real.sqrt (c / 2 + ε) := by
    intro ε hε
    apply strip_of_head_exp (by positivity)
    intro α hα
    obtain ⟨C₁, hC₁⟩ := h α hα
    obtain ⟨C₂, hC₂⟩ := h (-α) (by rwa [abs_neg])
    set A := 2 * Real.exp ((1 + |α|) / 2) * Real.exp (11 / 10) with hA
    have hA0 : 0 ≤ A := by positivity
    have hZ0 : 0 ≤ Zc α := by unfold Zc; positivity
    refine ⟨A * ((Nat.factorial 1 / ε ^ 1) + (11 / 10) * (Nat.factorial 2 / ε ^ 2))
      + (Real.sqrt (|C₁| * Zc α) + Real.sqrt (|C₂| * Zc α)) / (2 * π), fun b hb hb1 => ?_⟩
    set E := Real.exp (c / b) with hE
    have hE0 : 0 < E := Real.exp_pos _
    have w₁ := (hC₁ b hb hb1).trans (mul_le_mul_of_nonneg_right (le_abs_self C₁) hE0.le)
    have w₂ := (hC₂ b hb hb1).trans (mul_le_mul_of_nonneg_right (le_abs_self C₂) hE0.le)
    have hmain := head_le_of_window_at_cs hα hb hb1 (mul_nonneg (abs_nonneg C₁) hE0.le)
      (mul_nonneg (abs_nonneg C₂) hE0.le) w₁ w₂
    rw [← hA] at hmain
    refine hmain.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
    set u := 1 / b with hu
    have hu0 : 0 ≤ u := by positivity
    set F := Real.exp ((c / 2 + ε) / b) with hF
    have hF0 : 0 ≤ F := (Real.exp_pos _).le
    have hFu : (c / 2 + ε) / b = (c / 2 + ε) * u := by rw [hu]; ring
    -- polynomial part: `u^j ≤ (j!/ε^j) e^{εu} ≤ (j!/ε^j) F`
    have hεF : Real.exp (ε * u) ≤ F := by
      rw [hF, hFu, Real.exp_le_exp]; nlinarith
    have p1 := pow_le_exp 1 hε hu0
    have p2 := pow_le_exp 2 hε hu0
    rw [pow_one] at p1
    have q1 : u ≤ (Nat.factorial 1 / ε ^ 1) * F :=
      p1.trans (mul_le_mul_of_nonneg_left hεF (by positivity))
    have q2 : u ^ 2 ≤ (Nat.factorial 2 / ε ^ 2) * F :=
      p2.trans (mul_le_mul_of_nonneg_left hεF (by positivity))
    have t1 : A * (u + (11 / 10) * u ^ 2)
        ≤ A * ((Nat.factorial 1 / ε ^ 1) + (11 / 10) * (Nat.factorial 2 / ε ^ 2)) * F := by
      have hh : u + (11 / 10) * u ^ 2
          ≤ ((Nat.factorial 1 / ε ^ 1) + (11 / 10) * (Nat.factorial 2 / ε ^ 2)) * F := by
        nlinarith
      calc A * (u + (11 / 10) * u ^ 2)
          ≤ A * (((Nat.factorial 1 / ε ^ 1) + (11 / 10) * (Nat.factorial 2 / ε ^ 2)) * F) :=
            mul_le_mul_of_nonneg_left hh hA0
        _ = _ := by ring
    -- square-root part: `√(|C| E Zc) = √(|C| Zc) √E ≤ √(|C| Zc) F`
    have hsE : Real.sqrt E ≤ F := by
      have hFF : E ≤ F ^ 2 := by
        rw [hE, hF, ← Real.exp_nat_mul, Real.exp_le_exp]
        rw [div_eq_mul_one_div c b, div_eq_mul_one_div (c / 2 + ε) b, ← hu]
        push_cast
        nlinarith
      calc Real.sqrt E ≤ Real.sqrt (F ^ 2) := Real.sqrt_le_sqrt hFF
        _ = F := Real.sqrt_sq hF0
    have sq1 : Real.sqrt (|C₁| * E * Zc α) ≤ Real.sqrt (|C₁| * Zc α) * F := by
      rw [show |C₁| * E * Zc α = (|C₁| * Zc α) * E by ring,
        Real.sqrt_mul (mul_nonneg (abs_nonneg _) hZ0)]
      exact mul_le_mul_of_nonneg_left hsE (Real.sqrt_nonneg _)
    have sq2 : Real.sqrt (|C₂| * E * Zc α) ≤ Real.sqrt (|C₂| * Zc α) * F := by
      rw [show |C₂| * E * Zc α = (|C₂| * Zc α) * E by ring,
        Real.sqrt_mul (mul_nonneg (abs_nonneg _) hZ0)]
      exact mul_le_mul_of_nonneg_left hsE (Real.sqrt_nonneg _)
    have hpi : 0 < 2 * π := by positivity
    have t2 : (Real.sqrt (|C₁| * E * Zc α) + Real.sqrt (|C₂| * E * Zc α)) / (2 * π)
        ≤ (Real.sqrt (|C₁| * Zc α) + Real.sqrt (|C₂| * Zc α)) / (2 * π) * F := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hpi.le
      linarith
    calc A * (u + (11 / 10) * u ^ 2)
          + (Real.sqrt (|C₁| * E * Zc α) + Real.sqrt (|C₂| * E * Zc α)) / (2 * π)
        ≤ A * ((Nat.factorial 1 / ε ^ 1) + (11 / 10) * (Nat.factorial 2 / ε ^ 2)) * F
          + (Real.sqrt (|C₁| * Zc α) + Real.sqrt (|C₂| * Zc α)) / (2 * π) * F := add_le_add t1 t2
      _ = _ := by ring
  -- let `ε → 0`
  intro x
  set d := |(canonical x).re - 1 / 2| with hd
  have hd0 : 0 ≤ d := abs_nonneg _
  have hsq : (d / 2) ^ 2 ≤ c / 2 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have h1 := hstrip ε hε x
    have h2 : d / 2 ≤ Real.sqrt (c / 2 + ε) := by linarith
    exact (Real.le_sqrt (by positivity) (by positivity)).mp h2
  have h3 : d / 2 ≤ Real.sqrt (c / 2) := (Real.le_sqrt (by positivity) (by positivity)).mpr hsq
  have h4 : Real.sqrt (2 * c) = 2 * Real.sqrt (c / 2) := by
    rw [show 2 * c = 2 ^ 2 * (c / 2) by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  rw [h4]
  linarith

end FleetHeadContour
