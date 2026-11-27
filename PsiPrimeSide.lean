import PsiTestFunction
import FleetStandardExplicitFormula

/-!
# The prime side of the explicit formula collapses to `ψ`

With `g = PsiTestFunction.w L η`, the generic term of
`GammaExplicitFormula.primeSum g = ∑' n, Λ n * n^{-1/2} * g (log n)` simplifies completely:
`g (log n) = exp ((log n)/2) * window (log n) = √n * window (log n)`, and the `√n` cancels the
`n^{-1/2}`.  So

  `primeSum (w L η) = ∑' n, Λ n * window L η (log n)`,

a **real** sum with no cpow and no complex analysis left in it.  Since `window` is `1` on the
plateau `[η, L - η]`, `0` outside `[0, L]`, and in `[0,1]` throughout, that sum is sandwiched
between `ψ (x e^{-η})` and `ψ x` for `x = e^L`.
-/

set_option autoImplicit false

noncomputable section

open Real Finset
open scoped ArithmeticFunction

namespace PsiPrimeSide

open PsiTestFunction

/-! ## The Chebyshev function -/

/-- `ψ y = ∑_{n ≤ y} Λ n`. -/
def psi (y : ℝ) : ℝ := ∑ n ∈ range (⌊y⌋₊ + 1), Λ n

theorem psi_nonneg (y : ℝ) : 0 ≤ psi y :=
  Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

/-! ## The cancellation `n^{-1/2} · √n = 1` -/

/-- For `0 < n`, the `n^{-1/2}` of the explicit formula exactly cancels the `exp((log n)/2)`
built into the test function. -/
theorem rpow_mul_exp_log (n : ℕ) (hn : 0 < n) :
    ((n : ℝ) ^ (-(1 / 2) : ℝ)) * Real.exp (Real.log n / 2) = 1 := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1 : Real.exp (Real.log n / 2) = (n : ℝ) ^ ((1 / 2 : ℝ)) := by
    rw [Real.rpow_def_of_pos hn']
    ring_nf
  rw [h1, ← Real.rpow_add hn']
  norm_num

/-- The generic term of the prime side, simplified. -/
theorem term_eq (L η : ℝ) (n : ℕ) :
    (Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2) : ℂ) * w L η (Real.log n)
      = ((Λ n * window L η (Real.log n) : ℝ) : ℂ) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [ArithmeticFunction.map_zero]
  · have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hnc : ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) := by norm_cast
    have hexp : (-(1 / 2) : ℂ) = ((-(1 / 2) : ℝ) : ℂ) := by norm_num
    rw [hnc, hexp, ← Complex.ofReal_cpow hn'.le]
    unfold w wR
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    have hc := rpow_mul_exp_log n hn
    calc Λ n * ((n : ℝ) ^ (-(1 / 2) : ℝ))
            * (Real.exp (Real.log n / 2) * window L η (Real.log n))
        = (Λ n * window L η (Real.log n))
            * (((n : ℝ) ^ (-(1 / 2) : ℝ)) * Real.exp (Real.log n / 2)) := by ring
      _ = (Λ n * window L η (Real.log n)) * 1 := by rw [hc]
      _ = Λ n * window L η (Real.log n) := by ring

/-! ## The prime side as a finite real sum -/

/-- Terms beyond `e^L` vanish: the window is supported in `[0, L]`. -/
theorem term_eq_zero_of_gt {L η : ℝ} (hη : 0 < η) {n : ℕ}
    (hn : ⌊Real.exp L⌋₊ + 1 ≤ n) :
    (Λ n * window L η (Real.log n) : ℝ) = 0 := by
  have hpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := lt_of_lt_of_le (Nat.succ_pos _) hn
    exact_mod_cast this
  have hgt : Real.exp L < (n : ℝ) := by
    have h1 : Real.exp L < (⌊Real.exp L⌋₊ + 1 : ℕ) := by
      exact_mod_cast Nat.lt_floor_add_one (Real.exp L)
    have h2 : ((⌊Real.exp L⌋₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hlog : L ≤ Real.log n := by
    rw [← Real.log_exp L]
    exact (Real.log_le_log (Real.exp_pos L) hgt.le)
  rw [window_eq_zero_of_ge hη hlog, mul_zero]

/-- **The prime side is a finite real sum.** -/
theorem primeSum_eq {L η : ℝ} (hη : 0 < η) :
    GammaExplicitFormula.primeSum (w L η)
      = ((∑ n ∈ range (⌊Real.exp L⌋₊ + 1), Λ n * window L η (Real.log n) : ℝ) : ℂ) := by
  unfold GammaExplicitFormula.primeSum
  rw [show (fun n : ℕ => (Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2) : ℂ) * w L η (Real.log n))
      = fun n : ℕ => ((Λ n * window L η (Real.log n) : ℝ) : ℂ) from
    funext fun n => term_eq L η n]
  rw [← Complex.ofReal_tsum]
  congr 1
  refine tsum_eq_sum (fun n hn => ?_)
  refine term_eq_zero_of_gt hη ?_
  simpa [Finset.mem_range, Nat.not_lt] using hn

/-! ## The reflected prime sum vanishes -/

/-- **One-sided support kills the reflected term.** `reflect g u = g (-u)`, and `w L η` vanishes
on `u ≤ 0`, so every term of `primeSum (reflect (w L η))` is zero. This is what makes the
two-sided explicit formula usable for `ψ` at no cost. -/
theorem primeSum_reflect_eq_zero {L η : ℝ} (hη : 0 < η) :
    GammaExplicitFormula.primeSum (GammaExplicitFormula.reflect (w L η)) = 0 := by
  unfold GammaExplicitFormula.primeSum GammaExplicitFormula.reflect
  convert tsum_zero with n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [ArithmeticFunction.map_zero]
  · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have : w L η (-Real.log n) = 0 :=
      w_eq_zero_of_nonpos hη (by
        have := Real.log_nonneg h1
        linarith)
    rw [this, mul_zero]

/-! ## The window is a `[0,1]`-valued cutoff -/

theorem ramp_nonneg (η u : ℝ) : 0 ≤ ramp η u := Real.smoothTransition.nonneg _

theorem ramp_le_one (η u : ℝ) : ramp η u ≤ 1 := Real.smoothTransition.le_one _

theorem window_nonneg (L η u : ℝ) : 0 ≤ window L η u :=
  mul_nonneg (ramp_nonneg _ _) (ramp_nonneg _ _)

theorem window_le_one (L η u : ℝ) : window L η u ≤ 1 :=
  mul_le_one₀ (ramp_le_one _ _) (ramp_nonneg _ _) (ramp_le_one _ _)

/-! ## The sandwich `ψ(x e^{-η}) ≤ prime side ≤ ψ(x)` -/

/-- The prime side as a real number. -/
def realPrimeSum (L η : ℝ) : ℝ :=
  ∑ n ∈ range (⌊Real.exp L⌋₊ + 1), Λ n * window L η (Real.log n)

theorem primeSum_eq_real {L η : ℝ} (hη : 0 < η) :
    GammaExplicitFormula.primeSum (w L η) = ((realPrimeSum L η : ℝ) : ℂ) :=
  primeSum_eq hη

/-- **Upper bound.** The window is at most `1`, so the prime side is at most `ψ x`. -/
theorem realPrimeSum_le (L η : ℝ) : realPrimeSum L η ≤ psi (Real.exp L) := by
  unfold realPrimeSum psi
  refine Finset.sum_le_sum fun n _ => ?_
  have h0 : (0 : ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  nlinarith [window_le_one L η (Real.log n), window_nonneg L η (Real.log n)]

/-- On the plateau the window is exactly `1`: every prime power `n ≥ 2` with
`n ≤ e^{L-η}` contributes its full `Λ n`, provided the smoothing width is below `log 2`. -/
theorem window_log_eq_one {L η : ℝ} (hη : 0 < η) (hη2 : η < Real.log 2) {n : ℕ}
    (h2 : 2 ≤ n) (hub : (n : ℝ) ≤ Real.exp (L - η)) :
    window L η (Real.log n) = 1 := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2
  refine window_eq_one hη (le_of_lt (lt_of_lt_of_le hη2 ?_)) ?_
  · exact Real.log_le_log (by norm_num) hn2
  · have := Real.log_le_log (by positivity) hub
    rwa [Real.log_exp] at this

/-- **Lower bound.** Everything up to `x e^{-η}` is counted in full. -/
theorem le_realPrimeSum {L η : ℝ} (hη : 0 < η) (hη2 : η < Real.log 2) :
    psi (Real.exp (L - η)) ≤ realPrimeSum L η := by
  have hsub : range (⌊Real.exp (L - η)⌋₊ + 1) ⊆ range (⌊Real.exp L⌋₊ + 1) := by
    refine Finset.range_subset_range.mpr (Nat.succ_le_succ (Nat.floor_le_floor ?_))
    exact Real.exp_le_exp.mpr (by linarith)
  have hkey : psi (Real.exp (L - η))
      = ∑ n ∈ range (⌊Real.exp (L - η)⌋₊ + 1), Λ n * window L η (Real.log n) := by
    unfold psi
    refine Finset.sum_congr rfl fun n hn => ?_
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · interval_cases n
      · simp [ArithmeticFunction.map_zero]
      · simp [ArithmeticFunction.vonMangoldt_apply_one]
    · have hub : (n : ℝ) ≤ Real.exp (L - η) := by
        have h1 : n ≤ ⌊Real.exp (L - η)⌋₊ := by
          simpa [Finset.mem_range, Nat.lt_succ_iff] using hn
        calc (n : ℝ) ≤ (⌊Real.exp (L - η)⌋₊ : ℝ) := by exact_mod_cast h1
          _ ≤ Real.exp (L - η) := Nat.floor_le (Real.exp_pos _).le
      rw [window_log_eq_one hη hη2 hge hub, mul_one]
  rw [hkey]
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => ?_
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (window_nonneg _ _ _)

/-- **The prime side is `ψ` up to the smoothing window.**  With `x = e^L`, the prime side of
the explicit formula for `w L η` lies between `ψ (x e^{-η})` and `ψ x`.  Choosing
`η ≍ x^{-1/8}` makes the gap `O(x^{7/8})`, matching the target error. -/
theorem primeSide_sandwich {L η : ℝ} (hη : 0 < η) (hη2 : η < Real.log 2) :
    psi (Real.exp (L - η)) ≤ realPrimeSum L η ∧ realPrimeSum L η ≤ psi (Real.exp L) :=
  ⟨le_realPrimeSum hη hη2, realPrimeSum_le L η⟩

end PsiPrimeSide

end

#print axioms PsiPrimeSide.primeSum_eq
#print axioms PsiPrimeSide.primeSum_reflect_eq_zero
#print axioms PsiPrimeSide.term_eq
#print axioms PsiPrimeSide.primeSide_sandwich
