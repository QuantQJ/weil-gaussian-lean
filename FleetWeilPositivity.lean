import FleetWeilArchimedean
import FleetWeilNonArch
import OffLineDetection

/-!
# Weil criterion, part 3: the explicit formula in Formal Conjectures' normalisation, and RH ⇒ Weil positivity

For real `g ∈ C_c^∞(ℝ)` with the two moment conditions of `IsTestFunction`, and any enumeration
with multiplicity of the nontrivial zeros (`ZeroSumLimit.MultEnum`),

  `∑ᵢ ft g (tᵢ) · ft g (−tᵢ) = −(weilArchimedean f + ∑'ₚ weilNonArchimedean p f)`,   `f = g ⋆ g(−·)`,

where `tᵢ = −i (ρᵢ − ½)` (`weil_explicit_formula`). Under RH every `tᵢ` is real and the summand is
`|ft g tᵢ|² ≥ 0`, which gives the right-hand side of Formal Conjectures' `weil_positivity_criterion`
(`weilPositivity_of_RH`).
-/

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped Real ContDiff ArithmeticFunction CompactlySupported Convolution

namespace FleetWeilCriterion

/-- Formal Conjectures' Weil functional `W(f) = weilArchimedean f + Σ'ₚ weilNonArchimedean p f`. -/
def weilSum (f : ℝ → ℝ) : ℝ := weilArchimedean f + ∑' p : Nat.Primes, weilNonArchimedean p f

lemma weilNonArchimedean_eq_fleet (p : ℕ) (f : ℝ → ℝ) :
    weilNonArchimedean p f = FleetWeilNonArch.weilNonArchimedean p f := rfl

lemma primeSum_cast (f : ℝ → ℝ) :
    ∑' n : ℕ, (Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2) : ℂ) * (cF f (Real.log n) + cF f (-Real.log n)) =
      ((FleetWeilNonArch.vonMangoldtSum f : ℝ) : ℂ) := by
  unfold FleetWeilNonArch.vonMangoldtSum
  rw [Complex.ofReal_tsum]
  congr 1
  funext n
  simp only [cF]
  push_cast
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
  push_cast
  ring

/-- **The explicit formula with Formal Conjectures' factors**, for any admissible real `f`. -/
theorem explicit_formula_weilSum {ι : Type*} {zeros : ι → ℂ} (hz : ZeroSumLimit.MultEnum zeros)
    {f : ℝ → ℝ} {a B : ℝ} (h : Admissible f a B) :
    HasSum (fun i => TestFunctions.hfun a (cF f) (Reduction.ordinate (zeros i)))
      (TestFunctions.Gt a (cF f) 0 + TestFunctions.Gt a (cF f) 1 - ((weilSum f : ℝ) : ℂ)) := by
  have hE := FleetStandardExplicitFormula.explicit_formula_standard hz h.isTestFn h.supp
  rw [standardArchimedean_eq_neg_weilArchimedean h, primeSum_cast] at hE
  have hp : ∑' p : Nat.Primes, weilNonArchimedean p f = FleetWeilNonArch.vonMangoldtSum f :=
    FleetWeilNonArch.sum_weilNonArchimedean_eq h.vanish
  convert hE using 1
  unfold weilSum
  rw [hp]
  push_cast
  ring

lemma Gt_zero_eq (a : ℝ) (F : ℝ → ℂ) : TestFunctions.Gt a F 0 = TestFunctions.hfun a F (I / 2) := by
  rw [← TestFunctions.Gt_half_add_I_mul]
  congr 1
  ring_nf
  rw [Complex.I_sq]
  ring

lemma Gt_one_eq (a : ℝ) (F : ℝ → ℂ) :
    TestFunctions.Gt a F 1 = TestFunctions.hfun a F (-(I / 2)) := by
  rw [← TestFunctions.Gt_half_add_I_mul]
  congr 1
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The autocorrelation of a smooth compactly supported real function is admissible. -/
lemma admissible_auto {g : ℝ → ℝ} (hs : ContDiff ℝ ∞ g) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ x, A < |x| → g x = 0) : Admissible (auto g) (2 * A + 1) (2 * A) where
  smooth := auto_contDiff (hasCompactSupport_of_radius hA) hs
  B_nonneg := by linarith
  B_lt := by linarith
  vanish := auto_vanish hA

/-- **Weil's explicit formula, Formal Conjectures' normalisation.** For real `g ∈ C_c^∞` satisfying
`IsTestFunction`, `∑ᵢ ft g (tᵢ) ft g (−tᵢ) = −W(g ⋆ g(−·))` over any enumeration with multiplicity. -/
theorem weil_explicit_formula {ι : Type*} {zeros : ι → ℂ} (hz : ZeroSumLimit.MultEnum zeros)
    {g : ℝ → ℝ} (hs : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (ht : IsTestFunction g) :
    HasSum (fun i => ft g (Reduction.ordinate (zeros i)) * ft g (-Reduction.ordinate (zeros i)))
      (-((weilSum (auto g) : ℝ) : ℂ)) := by
  obtain ⟨A, hA0, hA⟩ := exists_radius hc
  have h := admissible_auto hs hA0 hA
  have hE := explicit_formula_weilSum hz h
  have hft : ∀ z : ℂ, TestFunctions.hfun (2 * A + 1) (cF (auto g)) z = ft g z * ft g (-z) := by
    intro z
    rw [show cF (auto g) = fun u => ((auto g u : ℝ) : ℂ) from rfl,
      hfun_ofReal_eq_ft h.B_nonneg h.B_lt h.vanish, ft_auto hs.continuous hA]
  rw [Gt_zero_eq, Gt_one_eq, hft, hft, neg_neg, ft_half_I, ft_neg_half_I, ht.1, ht.2] at hE
  simp only [Complex.ofReal_zero, mul_zero, zero_add, zero_sub] at hE
  simpa only [hft] using hE

/-- Under RH every ordinate is real. -/
lemma ordinate_real_of_RH (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : Reduction.IsNontrivialZero ρ) :
    Reduction.ordinate ρ = (((Reduction.ordinate ρ).re : ℝ) : ℂ) := by
  have hre : ρ.re = 1 / 2 := hRH ρ hρ.1 hρ.2.1 hρ.2.2
  apply Complex.ext
  · simp
  · simp [Reduction.ordinate_im, hre]

/-- The Weil functional on `g ⋆ g(−·)` is minus a sum of `|ft g (tᵢ)|²` under RH. -/
theorem weilSum_auto_nonpos_of_RH (hRH : RiemannHypothesis) {g : ℝ → ℝ} (hs : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (ht : IsTestFunction g) : weilSum (auto g) ≤ 0 := by
  have hE := weil_explicit_formula ZeroSumLimit.multEnum_canonical hs hc ht
  have hre := Complex.hasSum_re hE
  have hnn : ∀ x : ZeroSumLimit.Index, 0 ≤ (ft g (Reduction.ordinate (ZeroSumLimit.canonical x)) *
      ft g (-Reduction.ordinate (ZeroSumLimit.canonical x))).re := by
    intro x
    rw [ordinate_real_of_RH hRH (ZeroSumLimit.multEnum_canonical.nontrivial x),
      ft_mul_ft_neg_real, Complex.ofReal_re]
    exact Complex.normSq_nonneg _
  have := hre.nonneg hnn
  simp only [Complex.neg_re, Complex.ofReal_re] at this
  linarith

/-- **RH ⇒ the right-hand side of Formal Conjectures' `weil_positivity_criterion`.** -/
theorem weilPositivity_of_RH (hRH : RiemannHypothesis) : WeilPositivity := by
  intro g hs ht
  exact weilSum_auto_nonpos_of_RH hRH hs g.hasCompactSupport ht

end FleetWeilCriterion
