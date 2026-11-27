import FleetHeadContourRH

/-!
# Subexponential window bound ⇒ RH

`FleetHeadContourRH.RH_of_window_meanSquare` assumes a *polynomial* window bound
`∫ |M_{cut b}(1/2+it)|² e^{-(t−α)²/(4b)} dt ≤ C / b^k`. The exponent ladder
(`head_exp_ladder`) only needs a loss `e^{c/b}` for every `c > 0`, so the hypothesis can be
weakened to a **subexponential** one:

`WindowSubexpBound`: for every `|α| ≥ 1/2` and every `c > 0` there is `C` with
`∫_ℝ |M_{cut b}(1/2+it)|² e^{-(t−α)²/(4b)} dt ≤ C e^{c/b}` for all `0 < b ≤ 1`.

* `windowSubexp_of_meanSquare` : the polynomial hypothesis implies this one.
* `head_le_of_window_at`       : the head bound at a single `b` from the two window integrals.
* `RH_of_window_subexp`        : `WindowSubexpBound → RiemannHypothesis`.

Why the weakening matters (paper-level, not formalized here): with the sharp cutoff the window
integral is driven by `S(N) = Σ_{n ≤ N} μ(n) n^{-1/2-iα}` at `N = cut b`. Under RH one has only
`S(N) ≪ exp(A log N / log log N)` (Titchmarsh, *Theory of the Riemann zeta-function*, §14.25), which
is `e^{o(1/b)}`: subexponential, but not known to be polynomial in `1/b`. So the polynomial
hypothesis is not known to follow from RH, while the subexponential one is expected to.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace FleetHeadContour

/-- **The subexponential window hypothesis.** -/
def WindowSubexpBound : Prop :=
  ∀ α : ℝ, 1 / 2 ≤ |α| → ∀ c : ℝ, 0 < c → ∃ C : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
    ∫ t : ℝ, ‖Mpoly (FleetFiniteHeadRH.cut b) (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2
      * Real.exp (-(t - α) ^ 2 / (4 * b)) ≤ C * Real.exp (c / b)

/-- The polynomial window hypothesis implies the subexponential one. -/
theorem windowSubexp_of_meanSquare (h : WindowMeanSquareBound) : WindowSubexpBound := by
  intro α hα c hc
  obtain ⟨C, k, hC⟩ := h α hα
  refine ⟨|C| * (k.factorial / c ^ k), fun b hb hb1 => (hC b hb hb1).trans ?_⟩
  have hu : (0 : ℝ) ≤ 1 / b := by positivity
  have hp := pow_le_exp k hc hu
  have e1 : C / b ^ k = C * (1 / b) ^ k := by rw [one_div_pow, div_eq_mul_one_div]
  have e2 : c * (1 / b) = c / b := by ring
  rw [e2] at hp
  rw [e1]
  calc C * (1 / b) ^ k ≤ |C| * (1 / b) ^ k :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * ((k.factorial / c ^ k) * Real.exp (c / b)) := mul_le_mul_of_nonneg_left hp (abs_nonneg C)
    _ = _ := by ring

/-- **Head bound at one `b`** from the two window integrals (at `α` and `−α`). -/
theorem head_le_of_window_at {α : ℝ} (hα : 1 / 2 ≤ |α|) {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) {X₁ X₂ : ℝ}
    (h₁ : ∫ t : ℝ, ‖Mpoly (FleetFiniteHeadRH.cut b) (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2
        * Real.exp (-(t - α) ^ 2 / (4 * b)) ≤ X₁)
    (h₂ : ∫ t : ℝ, ‖Mpoly (FleetFiniteHeadRH.cut b) (((1 / 2 : ℝ) : ℂ) + t * I)‖ ^ 2
        * Real.exp (-(t - -α) ^ 2 / (4 * b)) ≤ X₂) :
    |FleetFiniteHeadRH.head b α (FleetFiniteHeadRH.cut b)| ≤ Real.sqrt (π / b) *
      (2 * Real.exp ((1 + |α|) / 2) * Real.exp (11 / 10) * ((1 / b) + (11 / 10) * (1 / b) ^ 2)
        + (|X₁| + |X₂| + 2 * Zc α) / (4 * π)) := by
  set M := FleetFiniteHeadRH.cut b with hM
  set sq := Real.sqrt (π / b) with hsq
  have hsq0 : 0 ≤ sq := Real.sqrt_nonneg _
  set u := 1 / b with hu
  set wp : ℝ → ℝ := fun t => Real.exp (-(t - -α) ^ 2 / (4 * b)) with hwp
  set wm : ℝ → ℝ := fun t => Real.exp (-(t - α) ^ 2 / (4 * b)) with hwm
  set Mn : ℝ → ℝ := fun t => ‖Mpoly M (((1 / 2 : ℝ) : ℂ) + t * I)‖ with hMn
  set Zn : ℝ → ℝ := fun t => ‖deriv riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)‖ with hZn
  have iMp : Integrable (fun t => Mn t ^ 2 * wp t) := integrable_M_window hb M (-α)
  have iMm : Integrable (fun t => Mn t ^ 2 * wm t) := integrable_M_window hb M α
  have hZcneg : Zc (-α) = Zc α := by unfold Zc; ring
  have iZp : Integrable (fun t => Zn t ^ 2 * wp t) := (zeta_window hb hb1 (-α)).1
  have iZm : Integrable (fun t => Zn t ^ 2 * wm t) := (zeta_window hb hb1 α).1
  have bZp : ∫ t, Zn t ^ 2 * wp t ≤ Zc α := by
    have := (zeta_window hb hb1 (-α)).2; rw [hZcneg] at this; exact this
  have bZm : ∫ t, Zn t ^ 2 * wm t ≤ Zc α := (zeta_window hb hb1 α).2
  have iM2 : Integrable (fun t => Mn t ^ 2 * wp t + Mn t ^ 2 * wm t) := iMp.add iMm
  have iZ2 : Integrable (fun t => Zn t ^ 2 * wp t + Zn t ^ 2 * wm t) := iZp.add iZm
  set F : ℝ → ℂ := fun t => LGw b α (((1 / 2 : ℝ) : ℂ) + t * I) * Mpoly M (((1 / 2 : ℝ) : ℂ) + t * I)
      * (-deriv riemannZeta (((1 / 2 : ℝ) : ℂ) + t * I)) with hF
  have hFi : Integrable F := by
    have := integrable_f_line hb α M (x := 1 / 2) (by norm_num) (by norm_num)
    simpa [Phi, hF] using this
  set G : ℝ → ℝ := fun t => (sq / 2) * ((Mn t ^ 2 * wp t + Mn t ^ 2 * wm t) + (Zn t ^ 2 * wp t + Zn t ^ 2 * wm t))
    with hG
  have hGi : Integrable G := (iM2.add iZ2).const_mul _
  have hFG : ∀ t, ‖F t‖ ≤ G t := by
    intro t
    have hL := norm_LGw_le b α (1 / 2) t
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
      Real.exp_zero, mul_one] at hL
    have hwpe : Real.exp (-(t + α) ^ 2 / (4 * b)) = wp t := by simp only [hwp, sub_neg_eq_add]
    rw [hwpe] at hL
    have hMn0 : 0 ≤ Mn t := norm_nonneg _
    have hZn0 : 0 ≤ Zn t := norm_nonneg _
    have hamgm : Mn t * Zn t ≤ (Mn t ^ 2 + Zn t ^ 2) / 2 := by nlinarith [sq_nonneg (Mn t - Zn t)]
    simp only [hF, norm_mul, norm_neg]
    change ‖LGw b α (((1 / 2 : ℝ) : ℂ) + t * I)‖ * Mn t * Zn t ≤ G t
    calc ‖LGw b α (((1 / 2 : ℝ) : ℂ) + t * I)‖ * Mn t * Zn t
        ≤ (sq * (wp t + wm t)) * Mn t * Zn t := by
          apply mul_le_mul_of_nonneg_right _ hZn0
          apply mul_le_mul_of_nonneg_right _ hMn0
          simpa [hwm] using hL
      _ = (sq * (wp t + wm t)) * (Mn t * Zn t) := by ring
      _ ≤ (sq * (wp t + wm t)) * ((Mn t ^ 2 + Zn t ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left hamgm (by simp only [hwp, hwm]; positivity)
      _ = G t := by simp only [hG]; ring
  have hInt : ‖∫ t, F t‖ ≤ (sq / 2) * ((|X₁| + |X₂|) + 2 * Zc α) := by
    calc ‖∫ t, F t‖ ≤ ∫ t, ‖F t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t, G t := integral_mono hFi.norm hGi hFG
      _ = (sq / 2) * (((∫ t, Mn t ^ 2 * wp t) + ∫ t, Mn t ^ 2 * wm t)
            + ((∫ t, Zn t ^ 2 * wp t) + ∫ t, Zn t ^ 2 * wm t)) := by
          simp only [hG]
          rw [integral_const_mul, integral_add iM2 iZ2, integral_add iMp iMm,
            integral_add iZp iZm]
      _ ≤ (sq / 2) * ((|X₂| + |X₁|) + (Zc α + Zc α)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have a1 : ∫ t, Mn t ^ 2 * wp t ≤ |X₂| := h₂.trans (le_abs_self _)
          have a2 : ∫ t, Mn t ^ 2 * wm t ≤ |X₁| := h₁.trans (le_abs_self _)
          exact add_le_add (add_le_add a1 a2) (add_le_add bZp bZm)
      _ = (sq / 2) * ((|X₁| + |X₂|) + 2 * Zc α) := by ring
  have hR := norm_deriv_Phi_one_le hb hb1 hα M
  have hMb := cut_rpow_le hb
  have hlog := log_cut_le hb hb1
  have hR' : ‖deriv (Phi b α M) 1‖ ≤ sq * (2 * Real.exp ((1 + |α|) / 2) * Real.exp (11 / 10) * (u + (11 / 10) * u ^ 2)) := by
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
  have hInt' : (1 / (2 * π)) * ‖∫ t, F t‖ ≤ sq * ((|X₁| + |X₂| + 2 * Zc α) / (4 * π)) := by
    calc (1 / (2 * π)) * ‖∫ t, F t‖ ≤ (1 / (2 * π)) * ((sq / 2) * ((|X₁| + |X₂|) + 2 * Zc α)) :=
          mul_le_mul_of_nonneg_left hInt (by positivity)
      _ = _ := by ring
  calc |FleetFiniteHeadRH.head b α M| ≤ ‖deriv (Phi b α M) 1‖ + (1 / (2 * π)) * ‖∫ t, F t‖ := hhead
    _ ≤ sq * (2 * Real.exp ((1 + |α|) / 2) * Real.exp (11 / 10) * (u + (11 / 10) * u ^ 2))
        + sq * ((|X₁| + |X₂| + 2 * Zc α) / (4 * π)) := add_le_add hR' hInt'
    _ = _ := by ring

/-- **Subexponential window bound ⇒ RH.** -/
theorem RH_of_window_subexp (h : WindowSubexpBound) : RiemannHypothesis := by
  apply head_exp_ladder
  intro c hc α hα
  obtain ⟨C₁, h₁⟩ := h α hα c hc
  obtain ⟨C₂, h₂⟩ := h (-α) (by rwa [abs_neg]) c hc
  set A := 2 * Real.exp ((1 + |α|) / 2) * Real.exp (11 / 10) with hA
  have hA0 : 0 ≤ A := by positivity
  have hZ0 : 0 ≤ Zc α := by unfold Zc; positivity
  refine ⟨A * ((Nat.factorial 1 / c ^ 1) + (11 / 10) * (Nat.factorial 2 / c ^ 2))
    + (|C₁| + |C₂| + 2 * Zc α) / (4 * π), fun b hb hb1 => ?_⟩
  have hmain := head_le_of_window_at hα hb hb1 (h₁ b hb hb1) (h₂ b hb hb1)
  rw [← hA] at hmain
  set u := 1 / b with hu
  have hu0 : 0 ≤ u := by positivity
  have hcu : c / b = c * u := by rw [hu]; ring
  rw [hcu] at hmain ⊢
  set E := Real.exp (c * u) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  have p1 := pow_le_exp 1 hc hu0
  have p2 := pow_le_exp 2 hc hu0
  rw [pow_one] at p1
  rw [← hE] at p1 p2
  refine hmain.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
  have hpi : 0 < 4 * π := by positivity
  have t1 : A * (u + (11 / 10) * u ^ 2) ≤ A * ((Nat.factorial 1 / c ^ 1) + (11 / 10) * (Nat.factorial 2 / c ^ 2)) * E := by
    have hh : u + (11 / 10) * u ^ 2 ≤ ((Nat.factorial 1 / c ^ 1) + (11 / 10) * (Nat.factorial 2 / c ^ 2)) * E := by
      nlinarith
    calc A * (u + (11 / 10) * u ^ 2) ≤ A * (((Nat.factorial 1 / c ^ 1) + (11 / 10) * (Nat.factorial 2 / c ^ 2)) * E) :=
          mul_le_mul_of_nonneg_left hh hA0
      _ = _ := by ring
  have hX1 : |C₁ * E| = |C₁| * E := by rw [abs_mul, abs_of_pos hE0]
  have hX2 : |C₂ * E| = |C₂| * E := by rw [abs_mul, abs_of_pos hE0]
  rw [hX1, hX2]
  have t2 : (|C₁| * E + |C₂| * E + 2 * Zc α) / (4 * π) ≤ (|C₁| + |C₂| + 2 * Zc α) / (4 * π) * E := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hpi.le
    have r3 : 2 * Zc α ≤ 2 * Zc α * E := le_mul_of_one_le_right (by positivity) hE1
    nlinarith
  linarith

end FleetHeadContour
