import FleetArithmeticBoundRH
import FleetGaussianDictionaryMember

/-!
# RH as a bound on the pole and prime terms alone

`FleetArithmeticBoundRH.RH_iff_arithmetic_bound` is stated for `weilRHSInf`, whose left-line piece
is exponentially large in `1/b`. This file passes to the standard arithmetic side
`FleetFullLineArithmetic.rhs = poles + archimedean − primes` and removes the archimedean piece:

* `rhs_gauss_eq` : `rhs (gauss b α) = weilRHSInf (gauss b α)` for every `b > 0`
  (both are limits of the truncated Gaussians `gaussR R b α`).
* `norm_archimedean_le` : `‖archimedean (gauss b α)‖ ≤ √(π/b) · A α` for `0 < b ≤ 1`.
* `RH_iff_pole_prime_bound` : RH holds iff for every centre `α` there is `C'` with
  `‖poleMinusPrimes b α‖ ≤ √(π/b) · C'` for all `0 < b ≤ 1`, where
  `poleMinusPrimes b α = ĝ(i/2) + ĝ(-i/2) − Σ Λ(n) n^{-1/2} (g(log n) + g(-log n))`, `g = gauss b α`.

The right-hand side contains no zero and no Gamma factor: the two pole values are elementary and the
rest is the von Mangoldt sum. The bound is not asserted here; it is equivalent to RH.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology MeasureTheory
open scoped Real ArithmeticFunction
open GaussianTest TestFunctions OffLineDetection Reduction ZeroSumLimit

namespace FleetPrimePoleBoundRH

/-! ## The truncations converge in the standard arithmetic side -/

theorem exists_uniform_h_real {b : ℝ} (hb : 0 < b) (α : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ R : ℝ, 2 ≤ R → ∀ t : ℝ,
      ‖hfun R (gaussR R b α) (t : ℂ)‖ ≤ M / (1 + t ^ 2) := by
  obtain ⟨K₀, hK₀⟩ := gaussR_sup_uniform hb α 0 le_rfl
  obtain ⟨K₂, hK₂⟩ := gaussR_weighted_uniform hb α 0 le_rfl
  refine ⟨2 * (|K₀| + |K₂|), by positivity, fun R hR t => ?_⟩
  have hR0 : (0 : ℝ) ≤ R := by linarith
  rw [← Gt_half_add_I_mul]
  have hre : |(1 / 2 + I * (t : ℂ)).re - 1 / 2| = 0 := by simp
  have him : (1 / 2 + I * (t : ℂ)).im = t := by simp
  have h1 : ‖Gt R (gaussR R b α) (1 / 2 + I * t)‖ ≤ |K₀| := by
    refine (GaussianTraceFormula.Gt_norm_le_weighted hR0 (continuous_gaussR R b α) _).trans ?_
    rw [hre]
    exact (hK₀ R hR).trans (le_abs_self _)
  have hpos : 0 < 1 + t ^ 2 := by positivity
  by_cases ht : t ^ 2 ≤ 1
  · rw [le_div_iff₀ hpos]
    nlinarith [abs_nonneg K₀, abs_nonneg K₂, norm_nonneg (Gt R (gaussR R b α) (1 / 2 + I * t))]
  · push_neg at ht
    have ht0 : t ≠ 0 := by
      rintro rfl
      norm_num at ht
    have h2 : ‖Gt R (gaussR R b α) (1 / 2 + I * t)‖ ≤ |K₂| / t ^ 2 := by
      have := Gt_bound_weighted (gaussR_isTestFn hR b α) (1 / 2 + I * t) (by rw [him]; exact ht0)
      rw [him, hre] at this
      refine this.trans ?_
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact (hK₂ R hR).trans (le_abs_self _)
    refine h2.trans ?_
    rw [div_le_div_iff₀ (by positivity) hpos]
    nlinarith [abs_nonneg K₀, abs_nonneg K₂]

theorem h_gaussR_eq {R : ℝ} (hR : 2 ≤ R) (b α : ℝ) (z : ℂ) :
    FleetFullLineFourier.h (gaussR R b α) z = hfun R (gaussR R b α) z :=
  FleetFullLineFourier.h_eq_hfun (gaussR_isTestFn hR b α) (gaussR_support hR b α) z

theorem tendsto_h {b : ℝ} (hb : 0 < b) (α : ℝ) (z : ℂ) :
    Tendsto (fun R : ℕ => FleetFullLineFourier.h (gaussR R b α) z) atTop
      (𝓝 (FleetFullLineFourier.h (gauss b α) z)) := by
  apply (tendsto_gaussR_hfun hb α z).congr'
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop 2)]
    with R hR
  exact (h_gaussR_eq hR b α z).symm

theorem tendsto_archimedean {b : ℝ} (hb : 0 < b) (α : ℝ) :
    Tendsto (fun R : ℕ => FleetFullLineArithmetic.archimedean (gaussR R b α)) atTop
      (𝓝 (FleetFullLineArithmetic.archimedean (gauss b α))) := by
  obtain ⟨K, hK, hk⟩ := FleetArchimedeanFunctionalBound.exists_weight_integral_bound
  obtain ⟨M, hM0, hM⟩ := exists_uniform_h_real hb α
  let D : ℝ → ℂ := fun t => ((M / (1 + t ^ 2) : ℝ) : ℂ)
  have hDm : AEStronglyMeasurable D := by
    apply Continuous.aestronglyMeasurable
    apply Complex.continuous_ofReal.comp
    exact continuous_const.div (by fun_prop) (fun t => by positivity)
  have hDb : ∀ t : ℝ, ‖D t‖ ≤ M / (1 + t ^ 2) := by
    intro t
    simp only [D, Complex.norm_real, Real.norm_eq_abs]
    rw [_root_.abs_of_nonneg (by positivity)]
  have hdom := (hk D hDm M hDb).1
  unfold FleetFullLineArithmetic.archimedean
  apply Tendsto.const_mul
  rw [← Filter.tendsto_add_atTop_iff_nat 2]
  have hcast : ∀ n : ℕ, (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := fun n => by
    push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  refine tendsto_integral_of_dominated_convergence
    (F := fun (n : ℕ) (t : ℝ) => FleetFullLineFourier.h (gaussR ((n + 2 : ℕ) : ℝ) b α) t
      * (FleetGammaKernel.weight t : ℂ))
    (fun t => ‖D t * (FleetGammaKernel.weight t : ℂ)‖) ?_ hdom.norm ?_ ?_
  · intro n
    have hG : AEStronglyMeasurable
        (fun t : ℝ => FleetFullLineFourier.h (gaussR ((n + 2 : ℕ) : ℝ) b α) t) := by
      apply Continuous.aestronglyMeasurable
      simp_rw [h_gaussR_eq (hcast n), ← Gt_half_add_I_mul]
      exact (Gt_continuous (continuous_gaussR _ b α)).comp (by fun_prop)
    refine (hk _ hG M (fun t => ?_)).1.aestronglyMeasurable
    rw [h_gaussR_eq (hcast n)]
    exact hM _ (hcast n) t
  · intro n
    refine Eventually.of_forall fun t => ?_
    rw [norm_mul]
    show _ ≤ ‖D t * (FleetGammaKernel.weight t : ℂ)‖
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [h_gaussR_eq (hcast n)]
    refine (hM _ (hcast n) t).trans (le_of_eq ?_)
    simp only [D, Complex.norm_real, Real.norm_eq_abs]
    rw [_root_.abs_of_nonneg (by positivity)]
  · refine Eventually.of_forall fun t => ?_
    apply Tendsto.mul_const
    exact (tendsto_h hb α (t : ℂ)).comp (tendsto_add_atTop_nat 2)

theorem tendsto_primeSum_reflect {b : ℝ} (hb : 0 < b) (α : ℝ) :
    Tendsto (fun R : ℕ =>
        GammaExplicitFormula.primeSum (GammaExplicitFormula.reflect (gaussR R b α))) atTop
      (𝓝 (GammaExplicitFormula.primeSum (GammaExplicitFormula.reflect (gauss b α)))) := by
  unfold GammaExplicitFormula.primeSum GammaExplicitFormula.reflect
  apply tendsto_tsum_of_dominated_convergence (GaussianTraceFormula.summable_primeBound hb)
  · intro n
    apply Tendsto.const_mul
    apply tendsto_const_nhds.congr'
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_ge_atTop (2 * |Real.log n| + 2))] with R hR
    have h2 : (2 : ℝ) ≤ R := by linarith [abs_nonneg (Real.log n)]
    rw [gaussR_eq_of_small h2 b α _ (by rw [abs_neg]; linarith)]
  · refine Eventually.of_forall fun R n => ?_
    have hΛ : (0 : ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, _root_.abs_of_nonneg hΛ]
    unfold GaussianTraceFormula.primeBound
    have hg := norm_gaussR_le R b α (-Real.log n)
    rw [neg_sq] at hg
    calc Λ n * ‖(n : ℂ) ^ (-(1 / 2) : ℂ)‖ * ‖gaussR R b α (-Real.log n)‖
        ≤ Λ n * 1 * Real.exp (-b * (Real.log n) ^ 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left
            (GaussianTraceFormula.norm_natCast_cpow_neg_half_le n) hΛ) hg (norm_nonneg _)
            (by positivity)
      _ = _ := by ring

theorem tendsto_rhs {b : ℝ} (hb : 0 < b) (α : ℝ) :
    Tendsto (fun R : ℕ => FleetFullLineArithmetic.rhs (gaussR R b α)) atTop
      (𝓝 (FleetFullLineArithmetic.rhs (gauss b α))) := by
  unfold FleetFullLineArithmetic.rhs
  have hp : Tendsto (fun R : ℕ => GammaExplicitFormula.primeSum (gaussR R b α)) atTop
      (𝓝 (GammaExplicitFormula.primeSum (gauss b α))) := by
    unfold GammaExplicitFormula.primeSum
    exact GaussianTraceFormula.tendsto_primeSum hb α
  exact ((((tendsto_h hb α (I / 2)).add (tendsto_h hb α (-I / 2))).add
    (tendsto_archimedean hb α)).sub hp).sub (tendsto_primeSum_reflect hb α)

/-- **The standard arithmetic side of a Gaussian equals the contour form.** -/
theorem rhs_gauss_eq {b : ℝ} (hb : 0 < b) (α : ℝ) :
    FleetFullLineArithmetic.rhs (gauss b α) = GaussianTraceFormula.weilRHSInf (gauss b α) := by
  have h2 : Tendsto (fun R : ℕ => FleetFullLineArithmetic.rhs (gaussR R b α)) atTop
      (𝓝 (GaussianTraceFormula.weilRHSInf (gauss b α))) := by
    apply (GaussianTraceFormula.tendsto_weilRHS hb α).congr'
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop 2)]
      with R hR
    rw [FleetFullLineArithmetic.rhs_eq_gammaRHS (gaussR_isTestFn hR b α) (gaussR_support hR b α),
      GammaExplicitFormula.weilRHS_eq_gammaRHS (gaussR_isTestFn hR b α) (gaussR_support hR b α)]
  exact tendsto_nhds_unique (tendsto_rhs hb α) h2

/-- **Zero trace = standard arithmetic side**, for every width and centre. -/
theorem zero_trace_eq_rhs {b : ℝ} (hb : 0 < b) (α : ℝ) :
    ∑' x : Index, gaussHat b α (ordinate (canonical x)) = FleetFullLineArithmetic.rhs (gauss b α) := by
  rw [rhs_gauss_eq hb]
  exact FleetArithmeticBoundRH.zero_trace_eq_arithmetic hb α

/-! ## The archimedean piece is `O(b^{-1/2})` -/

lemma exp_quarter_le (x α t : ℝ) (hx : x = t - α) :
    Real.exp (-x ^ 2 / 4) ≤ (9 + 2 * α ^ 2) / (1 + t ^ 2) := by
  have hpos : 0 < 1 + t ^ 2 := by positivity
  have hE : 1 + x ^ 2 / 4 ≤ Real.exp (x ^ 2 / 4) := by
    have := Real.add_one_le_exp (x ^ 2 / 4); linarith
  have hE1 : 1 ≤ Real.exp (x ^ 2 / 4) := by nlinarith [sq_nonneg x]
  have ht : t ^ 2 ≤ 2 * x ^ 2 + 2 * α ^ 2 := by subst hx; nlinarith [sq_nonneg (t + α), sq_nonneg (t - 2 * α)]
  rw [le_div_iff₀ hpos, show -x ^ 2 / 4 = -(x ^ 2 / 4) by ring, Real.exp_neg]
  rw [← div_eq_inv_mul, div_le_iff₀ (Real.exp_pos _)]
  nlinarith [sq_nonneg α, Real.exp_pos (x ^ 2 / 4)]

theorem norm_h_gauss_real_le {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (α t : ℝ) :
    ‖FleetFullLineFourier.h (gauss b α) (t : ℂ)‖
      ≤ (Real.sqrt (π / b) * (9 + 2 * α ^ 2)) / (1 + t ^ 2) := by
  rw [FleetGaussianDictionaryMember.h_eq_gaussHat, norm_gaussHat hb]
  simp only [Complex.ofReal_im, Complex.ofReal_re]
  rw [mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  refine le_trans ?_ (exp_quarter_le (t - α) α t rfl)
  apply Real.exp_le_exp.mpr
  have h4 : 0 < 4 * b := by positivity
  rw [show ((0 : ℝ) ^ 2 - (t - α) ^ 2) / (4 * b) = -((t - α) ^ 2 / (4 * b)) by ring,
    show -(t - α) ^ 2 / 4 = -((t - α) ^ 2 / 4) by ring, neg_le_neg_iff]
  apply div_le_div_of_nonneg_left (sq_nonneg _) h4 (by linarith)

theorem norm_archimedean_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ (α b : ℝ), 0 < b → b ≤ 1 →
    ‖FleetFullLineArithmetic.archimedean (gauss b α)‖
      ≤ Real.sqrt (π / b) * (‖(1 / (2 * (Real.pi : ℂ)))‖ * K * (9 + 2 * α ^ 2)) := by
  obtain ⟨K, hK, hk⟩ := FleetArchimedeanFunctionalBound.exists_weight_integral_bound
  refine ⟨K, hK, fun α b hb hb1 => ?_⟩
  have hG : AEStronglyMeasurable (fun t : ℝ => FleetFullLineFourier.h (gauss b α) (t : ℂ)) := by
    apply Continuous.aestronglyMeasurable
    simp_rw [FleetGaussianDictionaryMember.h_gauss_eq hb]
    fun_prop
  have hb' := (hk _ hG _ (norm_h_gauss_real_le hb hb1 α)).2
  unfold FleetFullLineArithmetic.archimedean
  rw [norm_mul]
  calc ‖(1 / (2 * (Real.pi : ℂ)))‖ * ‖∫ t : ℝ, FleetFullLineFourier.h (gauss b α) (t : ℂ)
          * (FleetGammaKernel.weight t : ℂ)‖
      ≤ ‖(1 / (2 * (Real.pi : ℂ)))‖ * (K * (Real.sqrt (π / b) * (9 + 2 * α ^ 2))) :=
        mul_le_mul_of_nonneg_left hb' (norm_nonneg _)
    _ = _ := by ring

/-! ## The criterion -/

/-- Pole values minus the two-sided von Mangoldt sum, for the Gaussian of width `b` at `α`. -/
def poleMinusPrimes (b α : ℝ) : ℂ :=
  FleetFullLineFourier.h (gauss b α) (I / 2) + FleetFullLineFourier.h (gauss b α) (-I / 2)
    - GammaExplicitFormula.primeSum (gauss b α)
    - GammaExplicitFormula.primeSum (GammaExplicitFormula.reflect (gauss b α))

lemma rhs_split (b α : ℝ) :
    FleetFullLineArithmetic.rhs (gauss b α)
      = poleMinusPrimes b α + FleetFullLineArithmetic.archimedean (gauss b α) := by
  unfold FleetFullLineArithmetic.rhs poleMinusPrimes; ring

/-- **RH iff the pole-minus-primes functional is `O(b^{-1/2})` at every centre.** No zero and no
Gamma factor appears on the right. -/
theorem RH_iff_pole_prime_bound :
    RiemannHypothesis ↔ ∀ α : ℝ, ∃ C' : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      ‖poleMinusPrimes b α‖ ≤ Real.sqrt (π / b) * C' := by
  obtain ⟨K, hK, hA⟩ := norm_archimedean_le
  rw [FleetTraceBoundRH.RH_iff_zero_trace_bound']
  constructor
  · intro h α
    obtain ⟨C', hC'⟩ := h α
    refine ⟨C' + ‖(1 / (2 * (Real.pi : ℂ)))‖ * K * (9 + 2 * α ^ 2), fun b hb hb1 => ?_⟩
    have e : poleMinusPrimes b α = FleetFullLineArithmetic.rhs (gauss b α)
        - FleetFullLineArithmetic.archimedean (gauss b α) := by rw [rhs_split]; ring
    rw [e, ← zero_trace_eq_rhs hb α, mul_add]
    exact (norm_sub_le _ _).trans (add_le_add (hC' b hb hb1) (hA α b hb hb1))
  · intro h α
    obtain ⟨C', hC'⟩ := h α
    refine ⟨C' + ‖(1 / (2 * (Real.pi : ℂ)))‖ * K * (9 + 2 * α ^ 2), fun b hb hb1 => ?_⟩
    rw [zero_trace_eq_rhs hb α, rhs_split, mul_add]
    exact (norm_add_le _ _).trans (add_le_add (hC' b hb hb1) (hA α b hb hb1))

end FleetPrimePoleBoundRH
