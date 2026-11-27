import ExplicitFormula
import TestFunctions
import Mathlib

/-!
# The prime side on the right line `Re s = 3/2`, as a Laplace transform

`ExplicitFormula.explicit_formula_arithmetic_half` writes the integral of `−ζ'/ζ` against an
integrable test function `φ` along `Re s = c > 1` as `Σ_n Λ(n) n^{−c} 𝓕φ(log n)`. Here we take
`c = 3/2` and `φ ξ := Gt a g (line (3/2) ξ) = ∫_{-a}^{a} g(u) e^{(1 + 2πiξ) u} du`, the
two-sided Laplace transform of `TestFunctions`, and **compute** `𝓕φ`.

Since `φ = 𝓕⁻ ψ` with `ψ(u) = g(u) e^{u}` (Mathlib's `𝓕⁻ f w = ∫ e^{2πi v w} f v dv`), the Fourier
inversion theorem (`Continuous.fourier_inversion_inv`) gives `𝓕 φ = ψ`, so
`𝓕φ(log n) = n · g(log n)` and the prime side collapses to the classical
`Σ_n Λ(n) n^{−1/2} g(log n)`.

**Proven unconditionally** (for `IsTestFn a g`):
* `phi_integrable`, `psi_integrable`, `fourier_phi_eq_psi` — the analytic inputs and `𝓕 φ = ψ`.
* `rightLine_eq_primeSide_indicator` / `hasSum_rightLine_indicator` — with no support
  hypothesis on `g`: the sum carries `(Icc (-a) a).indicator g (log n)`.
* `rightLine_eq_primeSide` / `hasSum_rightLine` / `summable_primeSide` — for `g` supported in
  `[-a, a]` (`hsupp : ∀ u, a < |u| → g u = 0`):
  `∫ (−ζ'/ζ)(3/2 + 2πiξ) Gt a g (3/2 + 2πiξ) dξ = Σ_n Λ(n) n^{−1/2} g(log n)`.
* `rightLine_eq_primeSide_t` — the same with the line parametrised by `t = 2πξ`
  (a factor `2π` appears).
* `rightLine_eq_primeSide_rpow` — the sum with a real `n^{-1/2}` instead of a complex power.

**Hypothesis-dependent:** nothing. **Not proven:** nothing about the left line or the zeros;
this file is the arithmetic half only. No `sorry`, no custom axioms.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Complex Filter Topology Set
open scoped FourierTransform Real ArithmeticFunction

namespace PrimeSideLaplace

open TestFunctions ExplicitFormula

/-! ## The two functions `φ` (on the line) and `ψ` (on the `u`-axis) -/

/-- `φ ξ := Gt a g (3/2 + 2πiξ)`: the Laplace transform restricted to the right line. -/
def phi (a : ℝ) (g : ℝ → ℂ) (ξ : ℝ) : ℂ := Gt a g (line (3 / 2) ξ)

/-- `ψ u := g u · e^{u}`; it is `𝓕 φ`. -/
def psi (g : ℝ → ℂ) (u : ℝ) : ℂ := g u * Complex.exp (u : ℂ)

/-- The support hypothesis in the `Icc` form used by `TestFunctions.Gt_line_eq_fourier`. -/
lemma supp_Icc {a : ℝ} {g : ℝ → ℂ} (hsupp : ∀ u, a < |u| → g u = 0) :
    ∀ u, u ∉ Icc (-a) a → g u = 0 := by
  intro u hu
  apply hsupp
  rw [mem_Icc, not_and_or, not_le, not_le] at hu
  rcases hu with h | h
  · exact lt_abs.mpr (Or.inr (by linarith))
  · exact lt_abs.mpr (Or.inl h)

/-! ## Regularity of `ψ` -/

lemma psi_continuous {g : ℝ → ℂ} (hg : Continuous g) : Continuous (psi g) := by
  unfold psi
  fun_prop

/-- `ψ` vanishes off `[-a, a]` (given the support hypothesis). -/
lemma psi_eq_zero {a : ℝ} {g : ℝ → ℂ} (hsupp : ∀ u, a < |u| → g u = 0) :
    ∀ u, u ∉ Icc (-a) a → psi g u = 0 := by
  intro u hu
  simp [psi, supp_Icc hsupp u hu]

lemma psi_integrable {a : ℝ} {g : ℝ → ℂ} (hg : Continuous g)
    (hsupp : ∀ u, a < |u| → g u = 0) : Integrable (psi g) :=
  ((psi_continuous hg).integrableOn_Icc (a := -a) (b := a)).integrable_of_forall_notMem_eq_zero
    (psi_eq_zero hsupp)

/-! ## Regularity of `φ` -/

lemma phi_continuous {a : ℝ} {g : ℝ → ℂ} (hg : Continuous g) : Continuous (phi a g) := by
  unfold phi
  exact (Gt_continuous (a := a) hg).comp (by unfold line; fun_prop)

/-- `φ` is integrable on `ℝ`: `Gt` is integrable on vertical lines (`Gt_decay`), and
`ξ ↦ 2πξ` is a change of variables. -/
theorem phi_integrable {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) : Integrable (phi a g) := by
  have h1 := (integrable_on_vertical_line h (3 / 2 : ℝ)).comp_mul_left' (R := 2 * π)
    Real.two_pi_pos.ne'
  refine h1.congr (Eventually.of_forall fun ξ => ?_)
  simp only [phi, line]
  congr 2
  push_cast
  ring

/-! ## `φ = 𝓕⁻ ψ` and `𝓕 φ = ψ` -/

/-- `φ ξ = 𝓕⁻ ψ ξ`, from `TestFunctions.Gt_line_eq_fourier` with `c − ½ = 1`. -/
theorem phi_eq_fourierInv_psi {a : ℝ} (ha : 0 ≤ a) {g : ℝ → ℂ}
    (hsupp : ∀ u, a < |u| → g u = 0) (ξ : ℝ) : phi a g ξ = 𝓕⁻ (psi g) ξ := by
  rw [phi, Gt_line_eq_fourier ha (supp_Icc hsupp) (3 / 2) ξ,
    Real.fourierInv_eq_fourier_neg]
  have hf : (fun u : ℝ => g u * Complex.exp (((3 / 2 - 1 / 2 : ℝ) : ℂ) * (u : ℂ))) = psi g := by
    funext u
    simp only [psi]
    norm_num
  rw [hf]

/-- `φ = 𝓕⁻ ψ` as functions. -/
theorem phi_eq_fourierInv_psi' {a : ℝ} (ha : 0 ≤ a) {g : ℝ → ℂ}
    (hsupp : ∀ u, a < |u| → g u = 0) : phi a g = 𝓕⁻ (psi g) :=
  funext (phi_eq_fourierInv_psi ha hsupp)

/-- `𝓕 ψ w = φ (−w)`. -/
theorem fourier_psi_eq {a : ℝ} (ha : 0 ≤ a) {g : ℝ → ℂ}
    (hsupp : ∀ u, a < |u| → g u = 0) (w : ℝ) : 𝓕 (psi g) w = phi a g (-w) := by
  rw [phi_eq_fourierInv_psi ha hsupp, Real.fourierInv_eq_fourier_neg, neg_neg]

/-- `𝓕 ψ` is integrable (it is `φ ∘ neg`). -/
theorem fourier_psi_integrable {a : ℝ} (ha : 0 ≤ a) {g : ℝ → ℂ}
    (hsupp : ∀ u, a < |u| → g u = 0) (hint : Integrable (phi a g)) :
    Integrable (𝓕 (psi g)) := by
  have : 𝓕 (psi g) = fun w => phi a g (-w) := funext (fourier_psi_eq ha hsupp)
  rw [this]
  exact hint.comp_neg

/-- **Fourier inversion:** `𝓕 φ = ψ`, i.e. `𝓕 (Gt a g (3/2 + 2πi ·)) u = g u e^{u}`. -/
theorem fourier_phi_eq_psi {a : ℝ} (ha : 0 ≤ a) {g : ℝ → ℂ} (hg : Continuous g)
    (hsupp : ∀ u, a < |u| → g u = 0) (hint : Integrable (phi a g)) :
    𝓕 (phi a g) = psi g := by
  rw [phi_eq_fourierInv_psi' ha hsupp]
  exact Continuous.fourier_fourierInv_eq (psi_continuous hg) (psi_integrable hg hsupp)
    (fourier_psi_integrable ha hsupp hint)

/-! ## The coefficient identity `Λ(n) n^{−3/2} · ψ(log n) = Λ(n) n^{−1/2} g(log n)` -/

/-- `ψ (log n) = n · g (log n)` for `n ≥ 1`. -/
lemma psi_log {g : ℝ → ℂ} {n : ℕ} (hn : n ≠ 0) :
    psi g (Real.log n) = (n : ℂ) * g (Real.log n) := by
  have hpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  simp only [psi]
  rw [← Complex.ofReal_exp, Real.exp_log hpos, Complex.ofReal_natCast, mul_comm]

/-- `n^{−3/2} · n = n^{−1/2}` in `ℂ`, for `n ≥ 1`. -/
lemma rpow_neg_three_halves_mul {n : ℕ} (hn : n ≠ 0) :
    (((n : ℝ) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * (n : ℂ) = (n : ℂ) ^ (-(1 / 2) : ℂ) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [Complex.ofReal_cpow n.cast_nonneg, Complex.ofReal_natCast]
  have : (-(1 / 2) : ℂ) = ((-(3 / 2 : ℝ) : ℝ) : ℂ) + 1 := by push_cast; ring
  rw [this, Complex.cpow_add _ _ hn0, Complex.cpow_one]

/-- The coefficient identity, all `n`. -/
theorem coeff_mul_psi_eq (g : ℝ → ℂ) (n : ℕ) :
    ((coeff (3 / 2) n : ℝ) : ℂ) * psi g (Real.log n)
      = (Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2) : ℂ) * g (Real.log n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [coeff_zero]
  · rw [psi_log hn, coeff, Complex.ofReal_mul, ← rpow_neg_three_halves_mul hn]
    ring

/-! ## The main identification -/

/-- **Core statement**, with the analytic inputs as hypotheses: for `g` continuous, supported in
`[-a, a]`, and with `φ` integrable,
`Σ_n Λ(n) n^{−1/2} g(log n) = ∫ (−ζ'/ζ)(3/2 + 2πiξ) · Gt a g (3/2 + 2πiξ) dξ`
(absolutely convergent `HasSum`). -/
theorem hasSum_rightLine_core {a : ℝ} (ha : 0 ≤ a) {g : ℝ → ℂ} (hg : Continuous g)
    (hsupp : ∀ u, a < |u| → g u = 0) (hint : Integrable (phi a g)) :
    HasSum (fun n : ℕ => (Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2) : ℂ) * g (Real.log n))
      (∫ ξ : ℝ, (-deriv riemannZeta (line (3 / 2) ξ) / riemannZeta (line (3 / 2) ξ))
        * Gt a g (line (3 / 2) ξ)) := by
  have key := hasSum_primeSide (c := 3 / 2) (by norm_num) hint
  rw [fourier_phi_eq_psi ha hg hsupp hint] at key
  convert key using 1
  · funext n
    exact (coeff_mul_psi_eq g n).symm
  · rfl

/-- **The right line is the prime side** (`HasSum` form), for a test function supported in
`[-a, a]`. -/
theorem hasSum_rightLine {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g)
    (hsupp : ∀ u, a < |u| → g u = 0) :
    HasSum (fun n : ℕ => (Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2) : ℂ) * g (Real.log n))
      (∫ ξ : ℝ, (-deriv riemannZeta (line (3 / 2) ξ) / riemannZeta (line (3 / 2) ξ))
        * Gt a g (line (3 / 2) ξ)) :=
  hasSum_rightLine_core h.nonneg h.continuous hsupp (phi_integrable h)

/-- **THE RIGHT LINE IS THE PRIME SIDE.** For `g` a test function supported in `[-a, a]`,

  `∫ (−ζ'/ζ)(3/2 + 2πiξ) · Gt a g (3/2 + 2πiξ) dξ = Σ_n Λ(n) n^{−1/2} g(log n)`. -/
theorem rightLine_eq_primeSide {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g)
    (hsupp : ∀ u, a < |u| → g u = 0) :
    ∫ ξ : ℝ, (-deriv riemannZeta (line (3 / 2) ξ) / riemannZeta (line (3 / 2) ξ))
        * Gt a g (line (3 / 2) ξ)
      = ∑' n : ℕ, (Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2) : ℂ) * g (Real.log n) :=
  (hasSum_rightLine h hsupp).tsum_eq.symm

/-- The prime side is absolutely convergent. -/
theorem summable_primeSide {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g)
    (hsupp : ∀ u, a < |u| → g u = 0) :
    Summable fun n : ℕ => (Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2) : ℂ) * g (Real.log n) :=
  (hasSum_rightLine h hsupp).summable

/-- The same sum with a real power `n^{−1/2}`. -/
theorem rightLine_eq_primeSide_rpow {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g)
    (hsupp : ∀ u, a < |u| → g u = 0) :
    ∫ ξ : ℝ, (-deriv riemannZeta (line (3 / 2) ξ) / riemannZeta (line (3 / 2) ξ))
        * Gt a g (line (3 / 2) ξ)
      = ∑' n : ℕ, ((Λ n * (n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * g (Real.log n) := by
  rw [rightLine_eq_primeSide h hsupp]
  congr 1
  funext n
  rw [Complex.ofReal_mul, Complex.ofReal_cpow n.cast_nonneg, Complex.ofReal_natCast]
  push_cast
  ring

/-- **Parametrised by `t = 2πξ`:**
`∫ (−ζ'/ζ)(3/2 + it) · Gt a g (3/2 + it) dt = 2π · Σ_n Λ(n) n^{−1/2} g(log n)`. -/
theorem rightLine_eq_primeSide_t {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g)
    (hsupp : ∀ u, a < |u| → g u = 0) :
    ∫ t : ℝ, (-deriv riemannZeta ((3 / 2 : ℝ) + t * I) / riemannZeta ((3 / 2 : ℝ) + t * I))
        * Gt a g ((3 / 2 : ℝ) + t * I)
      = 2 * π * ∑' n : ℕ, (Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2) : ℂ) * g (Real.log n) := by
  rw [← rightLine_eq_primeSide h hsupp]
  have hchg := Measure.integral_comp_mul_left
    (fun t : ℝ => (-deriv riemannZeta ((3 / 2 : ℝ) + t * I) / riemannZeta ((3 / 2 : ℝ) + t * I))
      * Gt a g ((3 / 2 : ℝ) + t * I)) (2 * π)
  have hline : ∀ ξ : ℝ, ((3 / 2 : ℝ) : ℂ) + ((2 * π * ξ : ℝ) : ℂ) * I = line (3 / 2) ξ := by
    intro ξ
    simp only [line]
    push_cast
    ring
  simp only [hline, abs_of_pos (inv_pos.mpr Real.two_pi_pos), Complex.real_smul] at hchg
  rw [hchg]
  have h2π : (2 * (π : ℂ)) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  push_cast
  rw [← mul_assoc, mul_inv_cancel₀ h2π, one_mul]

/-! ## Without a support hypothesis: the indicator form -/

/-- `Gt` only sees `g` on `[-a, a]`. -/
lemma Gt_indicator {a : ℝ} (ha : 0 ≤ a) (g : ℝ → ℂ) (s : ℂ) :
    Gt a ((Icc (-a) a).indicator g) s = Gt a g s := by
  unfold Gt
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le (by linarith)] at hu
  simp [indicator_of_mem hu]

/-- The truncation `(Icc (-a) a).indicator g` is continuous when `g (±a) = 0`. -/
lemma continuous_indicator_of_testFn {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) :
    Continuous ((Icc (-a) a).indicator g) := by
  apply h.continuous.indicator
  intro u hu
  rw [frontier_Icc (by linarith [h.nonneg])] at hu
  rcases hu with rfl | rfl
  · exact h.left
  · exact h.right

lemma indicator_supp {a : ℝ} (g : ℝ → ℂ) :
    ∀ u, a < |u| → (Icc (-a) a).indicator g u = 0 := by
  intro u hu
  apply indicator_of_notMem
  rw [mem_Icc, not_and_or, not_le, not_le]
  rcases lt_abs.mp hu with h | h
  · right; exact h
  · left; linarith

/-- **`HasSum` form without a support hypothesis:** for any `IsTestFn a g`,
`Σ_n Λ(n) n^{−1/2} 𝟙_{[-a,a]}(log n) g(log n) = ∫ (−ζ'/ζ)(3/2 + 2πiξ) Gt a g (3/2 + 2πiξ) dξ`. -/
theorem hasSum_rightLine_indicator {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) :
    HasSum (fun n : ℕ => (Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2) : ℂ)
        * (Icc (-a) a).indicator g (Real.log n))
      (∫ ξ : ℝ, (-deriv riemannZeta (line (3 / 2) ξ) / riemannZeta (line (3 / 2) ξ))
        * Gt a g (line (3 / 2) ξ)) := by
  have hGt : ∀ s, Gt a ((Icc (-a) a).indicator g) s = Gt a g s := Gt_indicator h.nonneg g
  have hint : Integrable (phi a ((Icc (-a) a).indicator g)) := by
    have : phi a ((Icc (-a) a).indicator g) = phi a g := by
      funext ξ
      simp only [phi, hGt]
    rw [this]
    exact phi_integrable h
  have key := hasSum_rightLine_core h.nonneg (continuous_indicator_of_testFn h)
    (indicator_supp g) hint
  simp only [hGt] at key
  exact key

/-- **The right line is the prime side, without a support hypothesis.** -/
theorem rightLine_eq_primeSide_indicator {a : ℝ} {g : ℝ → ℂ} (h : IsTestFn a g) :
    ∫ ξ : ℝ, (-deriv riemannZeta (line (3 / 2) ξ) / riemannZeta (line (3 / 2) ξ))
        * Gt a g (line (3 / 2) ξ)
      = ∑' n : ℕ, (Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2) : ℂ)
          * (Icc (-a) a).indicator g (Real.log n) :=
  (hasSum_rightLine_indicator h).tsum_eq.symm

end PrimeSideLaplace

end
