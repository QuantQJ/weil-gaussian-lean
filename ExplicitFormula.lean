import Mathlib

/-!
# The explicit formula, step 1 of 2: the prime side on a vertical line

Weil's explicit formula equates three things: a sum over the nontrivial zeros
of `ζ`, a sum over prime powers weighted by the von Mangoldt function `Λ`, and
an archimedean (Γ-factor) term. Its proof has two halves:

1. **The arithmetic half.** On a vertical line `Re s = c > 1`, `−ζ'/ζ(s) =
   Σ_n Λ(n) n^{−s}`, so integrating `−ζ'/ζ` against a test function along the
   line and exchanging sum and integral turns the zeta side into the
   **prime side** `Σ_n Λ(n) n^{−c} ĝ(log n)`. Everything here is absolutely
   convergent.
2. **The analytic half.** Shift the contour from `Re s = c` to `Re s = 1 − c`;
   the residues at the pole `s = 1` and at every zero `ρ` produce the zero
   side, and the functional equation produces the Γ-term. This needs the
   residue theorem, the Hadamard structure of `ζ`, and a zero-density bound
   to control the horizontal segments.

**This module proves half 1 completely** (`vertical_line_eq_prime_sum`),
with the sum–integral exchange justified by dominated convergence and the
Dirichlet series taken from Mathlib (`LSeries_vonMangoldt_eq_deriv_riemannZeta_div`).
Half 2 is **not** proven and is not stated as a theorem: the pinned Mathlib
has neither the residue theorem nor the Hadamard product for `ζ`, so there is
no honest way to state it that would not be an assumption in disguise.

Conventions: the line is parametrized as `s = c + 2πiξ`, `ξ ∈ ℝ`, so that
Mathlib's Fourier transform `𝓕 g (w) = ∫ e^{−2πi ξ w} g(ξ) dξ` appears with no
stray constants: `n^{−s} = n^{−c} e^{−2πi ξ log n}`.

No `sorry`, no custom axioms.
-/

noncomputable section
open MeasureTheory Real Complex Filter
open scoped LSeries.notation FourierTransform ArithmeticFunction

namespace ExplicitFormula

/-! ## The prime-side coefficients -/

/-- The prime-side weight `Λ(n) · n^{−c}` (real, nonnegative; zero unless `n`
is a prime power). -/
def coeff (c : ℝ) (n : ℕ) : ℝ := Λ n * (n : ℝ) ^ (-c)

lemma coeff_nonneg (c : ℝ) (n : ℕ) : 0 ≤ coeff c n :=
  mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg n.cast_nonneg _)

lemma coeff_zero (c : ℝ) : coeff c 0 = 0 := by
  simp [coeff]

/-- The coefficients are summable for `c > 1` — this is the absolute
convergence of `−ζ'/ζ` on `Re s > 1`, transported from Mathlib's
`LSeriesSummable_vonMangoldt`. -/
theorem coeff_summable {c : ℝ} (hc : 1 < c) : Summable (coeff c) := by
  have hs : LSeriesSummable ↗Λ (c : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc)
  have hnorm : Summable fun n => ‖LSeries.term ↗Λ (c : ℂ) n‖ :=
    summable_norm_iff.mpr hs
  refine hnorm.congr ?_
  intro n
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [coeff]
  · simp only [hn, if_false, Complex.ofReal_re]
    rw [Complex.norm_real, Real.norm_eq_abs,
      _root_.abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, coeff,
      Real.rpow_neg n.cast_nonneg, div_eq_mul_inv]

/-! ## The Dirichlet term on the line `s = c + 2πiξ` -/

/-- The point on the vertical line. -/
def line (c ξ : ℝ) : ℂ := (c : ℂ) + 2 * π * ξ * I

lemma line_re (c ξ : ℝ) : (line c ξ).re = c := by
  simp [line]

/-- The oscillating factor `e^{−2πi ξ log n}`. -/
def osc (ξ : ℝ) (n : ℕ) : ℂ := Complex.exp (((-2 * π * ξ * Real.log n : ℝ) : ℂ) * I)

lemma norm_osc (ξ : ℝ) (n : ℕ) : ‖osc ξ n‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

lemma continuous_osc (n : ℕ) : Continuous fun ξ => osc ξ n := by
  unfold osc
  fun_prop

/-- **The Dirichlet term factorizes on the line:**
`Λ(n) / n^{c + 2πiξ} = (Λ(n) n^{−c}) · e^{−2πi ξ log n}`. -/
theorem term_eq (c ξ : ℝ) (n : ℕ) :
    LSeries.term ↗Λ (line c ξ) n = (coeff c n : ℂ) * osc ξ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero, coeff_zero]
  · rw [LSeries.term_of_ne_zero hn]
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    -- n^{c + 2πiξ} = n^c · exp(2πiξ · log n)
    have hcpow : (n : ℂ) ^ (line c ξ)
        = ((n : ℝ) ^ c : ℝ) * Complex.exp ((2 * (π : ℂ) * ξ * I) * Real.log n) := by
      rw [line, Complex.cpow_add _ _ hn0, Complex.ofReal_cpow hnpos.le, Complex.ofReal_natCast,
        Complex.cpow_def_of_ne_zero hn0 (2 * (π : ℂ) * ξ * I), ← Complex.natCast_log]
      ring_nf
    rw [hcpow, coeff, osc, Real.rpow_neg hnpos.le, Complex.ofReal_mul, Complex.ofReal_inv,
      div_eq_mul_inv, mul_inv]
    have hEO : (Complex.exp ((2 * (π : ℂ) * ξ * I) * Real.log n))⁻¹
        = Complex.exp (((-2 * π * ξ * Real.log n : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_neg]
      congr 1
      push_cast
      ring
    rw [hEO]
    ring

/-- The full Dirichlet series on the line: `−ζ'/ζ(c + 2πiξ) = Σ_n coeff n · osc ξ n`. -/
theorem hasSum_line {c : ℝ} (hc : 1 < c) (ξ : ℝ) :
    HasSum (fun n => (coeff c n : ℂ) * osc ξ n)
      (-deriv riemannZeta (line c ξ) / riemannZeta (line c ξ)) := by
  have hre : 1 < (line c ξ).re := by rw [line_re]; exact hc
  have hs : LSeriesSummable ↗Λ (line c ξ) := ArithmeticFunction.LSeriesSummable_vonMangoldt hre
  have h : HasSum (LSeries.term ↗Λ (line c ξ)) (LSeries ↗Λ (line c ξ)) := hs.hasSum
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre] at h
  convert h using 1
  funext n
  exact (term_eq c ξ n).symm

/-! ## The main theorem: zeta side on the line = prime side -/

/-- The zeta side: `−ζ'/ζ` integrated against a test function along `Re s = c`. -/
def zetaSide (c : ℝ) (g : ℝ → ℂ) : ℂ :=
  ∫ ξ : ℝ, (-deriv riemannZeta (line c ξ) / riemannZeta (line c ξ)) * g ξ

/-- The prime side: `Σ_n Λ(n) n^{−c} · ĝ(log n)`, where `ĝ = 𝓕 g` is Mathlib's
Fourier transform. Only prime powers `n = p^k` contribute, with `Λ(p^k) = log p`. -/
def primeSide (c : ℝ) (g : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, (coeff c n : ℂ) * 𝓕 g (Real.log n)

/-- Each term of the prime side is the integral of the corresponding Dirichlet
term against `g` — this is just the definition of the Fourier transform. -/
theorem integral_term_eq (c : ℝ) (g : ℝ → ℂ) (n : ℕ) :
    ∫ ξ : ℝ, (coeff c n : ℂ) * osc ξ n * g ξ = (coeff c n : ℂ) * 𝓕 g (Real.log n) := by
  rw [Real.fourier_real_eq_integral_exp_smul, ← MeasureTheory.integral_const_mul]
  congr 1
  ext ξ
  simp only [osc, smul_eq_mul]
  ring

/-- **THE EXPLICIT FORMULA, ARITHMETIC HALF.** For `c > 1` and any integrable
test function `g`,

  `∫ (−ζ'/ζ)(c + 2πiξ) g(ξ) dξ = Σ_n Λ(n) n^{−c} · 𝓕g(log n)`,

with the right-hand side absolutely convergent. The exchange of `Σ` and `∫` is
dominated convergence with the summable majorant `Λ(n) n^{−c} ‖g(ξ)‖`. -/
theorem hasSum_primeSide {c : ℝ} (hc : 1 < c) {g : ℝ → ℂ} (hg : Integrable g) :
    HasSum (fun n : ℕ => (coeff c n : ℂ) * 𝓕 g (Real.log n)) (zetaSide c g) := by
  have hcs := coeff_summable hc
  -- the family F n ξ = coeff n · osc ξ n · g ξ, dominated by coeff n · ‖g ξ‖
  have key : HasSum (fun n : ℕ => ∫ ξ : ℝ, (coeff c n : ℂ) * osc ξ n * g ξ)
      (∫ ξ : ℝ, (-deriv riemannZeta (line c ξ) / riemannZeta (line c ξ)) * g ξ) :=
    hasSum_integral_of_dominated_convergence (fun n ξ => coeff c n * ‖g ξ‖)
      (fun n => ((continuous_const.mul (continuous_osc n)).aestronglyMeasurable).mul
        hg.aestronglyMeasurable)
      (fun n => Filter.Eventually.of_forall fun ξ => by
        rw [norm_mul, norm_mul, norm_osc, mul_one, Complex.norm_real, Real.norm_eq_abs,
          _root_.abs_of_nonneg (coeff_nonneg c n)])
      (Filter.Eventually.of_forall fun ξ => hcs.mul_right ‖g ξ‖)
      (by
        have hb : (fun ξ => ∑' n, coeff c n * ‖g ξ‖) = (fun ξ => (∑' n, coeff c n) * ‖g ξ‖) := by
          funext ξ
          exact tsum_mul_right
        rw [hb]
        exact hg.norm.const_mul _)
      (Filter.Eventually.of_forall fun ξ => (hasSum_line hc ξ).mul_right (g ξ))
  -- rewrite each integral as a Fourier coefficient
  unfold zetaSide
  convert key using 1
  funext n
  exact (integral_term_eq c g n).symm

/-- The prime side converges absolutely and equals the zeta side. -/
theorem vertical_line_eq_prime_sum {c : ℝ} (hc : 1 < c) {g : ℝ → ℂ} (hg : Integrable g) :
    zetaSide c g = primeSide c g :=
  ((hasSum_primeSide hc hg).tsum_eq).symm

/-- Absolute convergence of the prime side. -/
theorem primeSide_summable {c : ℝ} (hc : 1 < c) {g : ℝ → ℂ} (hg : Integrable g) :
    Summable fun n : ℕ => (coeff c n : ℂ) * 𝓕 g (Real.log n) :=
  (hasSum_primeSide hc hg).summable

/-- Unfolded form, for readers who want to see `−ζ'/ζ` and `Λ` explicitly. -/
theorem explicit_formula_arithmetic_half {c : ℝ} (hc : 1 < c) {g : ℝ → ℂ}
    (hg : Integrable g) :
    ∫ ξ : ℝ, (-deriv riemannZeta ((c : ℂ) + 2 * π * ξ * I)
        / riemannZeta ((c : ℂ) + 2 * π * ξ * I)) * g ξ
      = ∑' n : ℕ, ((Λ n * (n : ℝ) ^ (-c) : ℝ) : ℂ) * 𝓕 g (Real.log n) :=
  vertical_line_eq_prime_sum hc hg

end ExplicitFormula

end
