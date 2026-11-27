import GaussianTraceFormula
import GammaExplicitFormula

noncomputable section
open Complex
open scoped ArithmeticFunction

namespace FleetPrimeFunctionalBound

/-- A fixed exponential rate 3 is enough for the intended Gaussian density topology. -/
def ExponentialBound (E : ℝ) (g : ℝ → ℂ) : Prop :=
  ∀ u, ‖g u‖ ≤ E * Real.exp (-3 * |u|)

def term (g : ℝ → ℂ) (n : ℕ) : ℂ :=
  (Λ n : ℂ) * (n : ℂ)^(-(1/2) : ℂ) * g (Real.log n)

theorem norm_term_le {E : ℝ} (hE : 0 ≤ E) {g : ℝ → ℂ}
    (hg : ExponentialBound E g) (n : ℕ) : ‖term g n‖ ≤ E / (n : ℝ)^2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [term]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hΛ : Λ n ≤ (n : ℝ) :=
    ArithmeticFunction.vonMangoldt_le_log.trans (by linarith [Real.log_le_sub_one_of_pos hn0])
  have hexp : Real.exp (-3 * |Real.log n|) = 1 / (n : ℝ)^3 := by
    rw [_root_.abs_of_nonneg hlog, show -3 * Real.log (n : ℝ) = -(3 * Real.log n) by ring,
      Real.exp_neg]
    have he : Real.exp ((3 : ℕ)*Real.log (n : ℝ)) = (n : ℝ)^3 := by
      rw [Real.exp_nat_mul, Real.exp_log hn0]
    norm_num at he
    rw [he, one_div]
  have hg' : ‖g (Real.log n)‖ ≤ E / (n : ℝ)^3 := by
    simpa only [hexp, mul_one_div] using hg (Real.log n)
  have hΛ0 : (0 : ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  rw [term, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, _root_.abs_of_nonneg hΛ0]
  calc
    Λ n * ‖(n : ℂ)^(-(1/2) : ℂ)‖ * ‖g (Real.log n)‖
      ≤ (n : ℝ) * (E / (n : ℝ)^3) := by
        apply mul_le_mul _ hg' (norm_nonneg _) hn0.le
        calc
          Λ n * ‖(n : ℂ)^(-(1/2) : ℂ)‖ ≤ Λ n * 1 :=
            mul_le_mul_of_nonneg_left (GaussianTraceFormula.norm_natCast_cpow_neg_half_le n) hΛ0
          _ ≤ (n : ℝ) := by simpa using hΛ
    _ = E / (n : ℝ)^2 := by field_simp

theorem summable_terms {E : ℝ} (hE : 0 ≤ E) {g : ℝ → ℂ}
    (hg : ExponentialBound E g) : Summable (term g) := by
  apply Summable.of_norm_bounded (g := fun n : ℕ => E / (n : ℝ)^2)
    ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left E |>.congr (fun n => by ring))
  exact norm_term_le hE hg

/-- Absolute convergence and a quantitative bound for the untruncated prime functional. -/
theorem norm_primeSum_le {E : ℝ} (hE : 0 ≤ E) {g : ℝ → ℂ}
    (hg : ExponentialBound E g) :
    ‖GammaExplicitFormula.primeSum g‖ ≤ E * ∑' n : ℕ, 1/(n : ℝ)^2 := by
  have hs := summable_terms hE hg
  have hb : Summable (fun n : ℕ => E / (n : ℝ)^2) := by
    simpa only [mul_one_div] using (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left E
  change ‖∑' n, term g n‖ ≤ _
  calc
    ‖∑' n, term g n‖ ≤ ∑' n, ‖term g n‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n : ℕ, E / (n : ℝ)^2 := Summable.tsum_le_tsum (norm_term_le hE hg) hs.norm hb
    _ = E * ∑' n : ℕ, 1/(n : ℝ)^2 := by simp only [← mul_one_div E, tsum_mul_left]

theorem bound_reflect {E : ℝ} {g : ℝ → ℂ} (hg : ExponentialBound E g) :
    ExponentialBound E (GammaExplicitFormula.reflect g) := by
  intro u
  simpa only [GammaExplicitFormula.reflect, abs_neg] using hg (-u)

/-- Subtraction is justified by absolute convergence of both prime series. -/
theorem primeSum_sub {f g : ℝ → ℂ}
    (hf : Summable (term f)) (hg : Summable (term g)) :
    GammaExplicitFormula.primeSum (fun u => f u - g u) =
      GammaExplicitFormula.primeSum f - GammaExplicitFormula.primeSum g := by
  unfold GammaExplicitFormula.primeSum
  simp_rw [mul_sub]
  exact hf.tsum_sub hg

theorem norm_primeSum_sub_le {E : ℝ} (hE : 0 ≤ E) {f g : ℝ → ℂ}
    (hf : Summable (term f)) (hg : Summable (term g))
    (hd : ExponentialBound E (fun u => f u - g u)) :
    ‖GammaExplicitFormula.primeSum f - GammaExplicitFormula.primeSum g‖ ≤
      E * ∑' n : ℕ, 1/(n : ℝ)^2 := by
  rw [← primeSum_sub hf hg]
  exact norm_primeSum_le hE hd

end FleetPrimeFunctionalBound
