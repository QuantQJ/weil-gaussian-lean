import PsiPrimeSide

/-!
# The main term `Gt a (w L η) 1 = x - 1` up to the smoothing window

`TestFunctions.Gt a g s = ∫_{-a}^{a} g u * exp ((s - 1/2) u)`.  At `s = 1` the weight is
`exp (u/2)`, which combines with the `exp (u/2)` built into `w L η` to give exactly `e^u`:

  `Gt (L+1) (w L η) 1 = ∫_{-(L+1)}^{L+1} e^u * window L η u du = ∫_0^L e^u * window L η u du`.

Since `window` is `1` on `[η, L - η]`, `0` outside `[0, L]`, and in `[0,1]` throughout, that
integral is sandwiched between `e^{L-η} - e^η` and `e^L - 1`.  With `x = e^L` the upper end is
`x - 1`, the classical main term, and the gap is `O(ηx)` — the same size as the prime-side
smoothing loss, so one choice `η ≍ x^{-1/8}` controls both.
-/

set_option autoImplicit false

noncomputable section

open Real intervalIntegral

namespace PsiMainTerm

open PsiTestFunction PsiPrimeSide

/-! ## The integrand -/

/-- The main-term integrand `e^u * window L η u`. -/
def integrand (L η u : ℝ) : ℝ := Real.exp u * window L η u

theorem continuous_integrand (L η : ℝ) : Continuous (integrand L η) :=
  Real.continuous_exp.mul (window_contDiff L η (n := 1)).continuous

theorem integrable_integrand (L η a b : ℝ) :
    IntervalIntegrable (integrand L η) MeasureTheory.volume a b :=
  (continuous_integrand L η).intervalIntegrable a b

theorem integrand_nonneg (L η u : ℝ) : 0 ≤ integrand L η u :=
  mul_nonneg (Real.exp_pos u).le (window_nonneg L η u)

theorem integrand_le_exp (L η u : ℝ) : integrand L η u ≤ Real.exp u := by
  unfold integrand
  nlinarith [window_le_one L η u, window_nonneg L η u, (Real.exp_pos u).le]

theorem integrand_eq_zero_of_nonpos {L η u : ℝ} (hη : 0 < η) (hu : u ≤ 0) :
    integrand L η u = 0 := by
  unfold integrand
  rw [window_eq_zero_of_nonpos hη hu, mul_zero]

theorem integrand_eq_zero_of_ge {L η u : ℝ} (hη : 0 < η) (hu : L ≤ u) :
    integrand L η u = 0 := by
  unfold integrand
  rw [window_eq_zero_of_ge hη hu, mul_zero]

theorem integrand_eq_exp {L η u : ℝ} (hη : 0 < η) (h1 : η ≤ u) (h2 : u ≤ L - η) :
    integrand L η u = Real.exp u := by
  unfold integrand
  rw [window_eq_one hη h1 h2, mul_one]

/-! ## `Gt` at `s = 1` is that integral -/

theorem pointwise (L η u : ℝ) :
    w L η u * Complex.exp (((1 : ℂ) - 1 / 2) * (u : ℂ)) = ((integrand L η u : ℝ) : ℂ) := by
  have hexp : Complex.exp (((1 : ℂ) - 1 / 2) * (u : ℂ)) = ((Real.exp (u / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hhalf : Real.exp (u / 2) * Real.exp (u / 2) = Real.exp u := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold w wR integrand
  rw [hexp, ← Complex.ofReal_mul]
  congr 1
  calc Real.exp (u / 2) * window L η u * Real.exp (u / 2)
      = Real.exp (u / 2) * Real.exp (u / 2) * window L η u := by ring
    _ = Real.exp u * window L η u := by rw [hhalf]

/-- **The main term as a real integral.** -/
theorem Gt_one_eq (L η : ℝ) :
    TestFunctions.Gt (L + 1) (w L η) 1
      = ((∫ u in (-(L + 1))..(L + 1), integrand L η u : ℝ) : ℂ) := by
  unfold TestFunctions.Gt
  rw [← intervalIntegral.integral_ofReal]
  exact intervalIntegral.integral_congr (fun u _ => pointwise L η u)

/-! ## Localisation to `[0, L]` -/

theorem integral_localise {L η : ℝ} (hη : 0 < η) (hL : 0 ≤ L) :
    (∫ u in (-(L + 1))..(L + 1), integrand L η u) = ∫ u in (0 : ℝ)..L, integrand L η u := by
  have zlo : (∫ u in (-(L + 1))..(0 : ℝ), integrand L η u) = 0 := by
    rw [intervalIntegral.integral_congr
      (g := fun _ : ℝ => (0 : ℝ)) (fun u hu => ?_), intervalIntegral.integral_zero]
    rw [Set.uIcc_of_le (by linarith)] at hu
    exact integrand_eq_zero_of_nonpos hη hu.2
  have zhi : (∫ u in L..(L + 1), integrand L η u) = 0 := by
    rw [intervalIntegral.integral_congr
      (g := fun _ : ℝ => (0 : ℝ)) (fun u hu => ?_), intervalIntegral.integral_zero]
    rw [Set.uIcc_of_le (by linarith)] at hu
    exact integrand_eq_zero_of_ge hη hu.1
  have s1 := intervalIntegral.integral_add_adjacent_intervals
    (integrable_integrand L η (-(L + 1)) 0) (integrable_integrand L η 0 (L + 1))
  have s2 := intervalIntegral.integral_add_adjacent_intervals
    (integrable_integrand L η 0 L) (integrable_integrand L η L (L + 1))
  rw [zhi, add_zero] at s2
  rw [← s1, zlo, zero_add, ← s2]

/-! ## The sandwich -/

/-- **Upper bound:** the window is at most `1`. -/
theorem mainTerm_le {L η : ℝ} (hL : 0 ≤ L) :
    (∫ u in (0 : ℝ)..L, integrand L η u) ≤ Real.exp L - 1 := by
  have h := intervalIntegral.integral_mono_on hL
    (integrable_integrand L η 0 L)
    (Real.continuous_exp.intervalIntegrable 0 L)
    (fun u _ => integrand_le_exp L η u)
  rwa [integral_exp, Real.exp_zero] at h

/-- **Lower bound:** everything on the plateau `[η, L - η]` is counted at full weight. -/
theorem le_mainTerm {L η : ℝ} (hη : 0 < η) (h2η : 2 * η ≤ L) :
    Real.exp (L - η) - Real.exp η ≤ ∫ u in (0 : ℝ)..L, integrand L η u := by
  have hηL : η ≤ L - η := by linarith
  have hplateau : (∫ u in η..(L - η), integrand L η u) = Real.exp (L - η) - Real.exp η := by
    rw [intervalIntegral.integral_congr
      (g := Real.exp) (fun u hu => ?_), integral_exp]
    rw [Set.uIcc_of_le hηL] at hu
    exact integrand_eq_exp hη hu.1 hu.2
  have s1 := intervalIntegral.integral_add_adjacent_intervals
    (integrable_integrand L η 0 η) (integrable_integrand L η η (L - η))
  have s2 := intervalIntegral.integral_add_adjacent_intervals
    (integrable_integrand L η 0 (L - η)) (integrable_integrand L η (L - η) L)
  have n1 : 0 ≤ ∫ u in (0 : ℝ)..η, integrand L η u :=
    intervalIntegral.integral_nonneg hη.le (fun u _ => integrand_nonneg L η u)
  have n2 : 0 ≤ ∫ u in (L - η)..L, integrand L η u :=
    intervalIntegral.integral_nonneg (by linarith) (fun u _ => integrand_nonneg L η u)
  rw [← s2, ← s1, hplateau]
  linarith

/-- **The main term is `x - 1` up to the smoothing window.**  For `x = e^L`:
`x e^{-η} - e^η ≤ Gt (L+1) (w L η) 1 ≤ x - 1`, the gap being `O(ηx)`. -/
theorem mainTerm_sandwich {L η : ℝ} (hη : 0 < η) (h2η : 2 * η ≤ L) :
    Real.exp (L - η) - Real.exp η
        ≤ (∫ u in (-(L + 1))..(L + 1), integrand L η u) ∧
      (∫ u in (-(L + 1))..(L + 1), integrand L η u) ≤ Real.exp L - 1 := by
  have hL : 0 ≤ L := by linarith
  rw [integral_localise hη hL]
  exact ⟨le_mainTerm hη h2η, mainTerm_le hL⟩

end PsiMainTerm

end

#print axioms PsiMainTerm.Gt_one_eq
#print axioms PsiMainTerm.integral_localise
#print axioms PsiMainTerm.mainTerm_sandwich
