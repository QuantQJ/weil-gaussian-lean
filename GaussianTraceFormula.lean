import GaussianTest
import TraceInterface
import ExplicitFormulaZeroSide
import Mathlib

/-!
# The explicit formula for Gaussian test functions

The explicit formula (`ExplicitFormulaZeroSide`, packaged as `TraceInterface.weilRHS` /
`TraceInterface.RealizesExplicitFormula`) is proven for compactly supported `C²` test functions
`IsTestFn a g`. Here it is extended to the Gaussian test functions
`gauss b α u = exp (−b u² − i α u)` by the cutoff limit `R → ∞` (over `R : ℕ`), using the
truncations `gaussR R b α` of `GaussianTest` and their uniform (in `R ≥ 2`) weighted bounds.

* `leftLineInf g`, `weilRHSInf g` — the full-line versions of `leftLine` and `weilRHS`.
* `tendsto_weilRHS`: `weilRHS R (gaussR R b α) → weilRHSInf (gauss b α)`
  (pole term, prime sum by Tannery, left line by dominated convergence).
* `tendsto_hfun_sum`: for any spectrum `t : ι → ℂ` with `|Im t i| ≤ ½`, finitely many
  `|Re t i| ≤ 1` and `∑ 1/(Re t i)² < ∞`, the spectral sums `∑ᵢ hfun R (gaussR R b α) (t i)`
  converge to `∑ᵢ gaussHat b α (t i)` (Tannery with the weighted decay bounds).
* `gaussian_formula_zeros`: the explicit formula for `gauss b α` at the zeros (canonical
  enumeration), unconditionally.
* `gaussian_formula_real`: the same for any real spectrum `γ` with `∑ 1/(1+γᵢ²) < ∞` that
  realizes the explicit formula (`RealSpectrumRealizes γ`).
* `gaussian_trace_eq`: for such `γ`, `∑ᵢ gaussHat b α (γ i) = ∑ₓ gaussHat b α (ordinate (canonical x))`.

Standard Mathlib foundations only (see `AxiomAudit.lean`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Complex Filter Topology Set TestFunctions GaussianTest TraceInterface
  ExplicitFormulaZeroSide ZeroSumLimit Reduction
open scoped Real ArithmeticFunction

namespace GaussianTraceFormula

/-! ## Definitions -/

/-- The full-line archimedean functional: `∫ (ζ'/ζ)(−½ + it) · GtInf g (−½ + it) dt`. -/
def leftLineInf (g : ℝ → ℂ) : ℂ :=
  ∫ t : ℝ, deriv riemannZeta (-1/2 + t * I) / riemannZeta (-1/2 + t * I) * GtInf g (-1/2 + t * I)

/-- The full-line right-hand side of the explicit formula. -/
def weilRHSInf (g : ℝ → ℂ) : ℂ :=
  GtInf g 1 - (∑' n : ℕ, (Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2) : ℂ) * g (Real.log n))
    - 1 / (2 * π) * leftLineInf g

/-! ## Weighted trivial bounds (uniform in the support radius) -/

/-- `‖Gt a g s‖ ≤ ∫_{-a}^{a} ‖g u‖ e^{|Re s − ½| |u|} du` — the trivial bound with the weight kept
inside, so that it is uniform in `a` for the truncated Gaussians. -/
theorem Gt_norm_le_weighted {a : ℝ} (ha : 0 ≤ a) {g : ℝ → ℂ} (hg : Continuous g) (s : ℂ) :
    ‖Gt a g s‖ ≤ ∫ u in (-a)..a, ‖g u‖ * Real.exp (|s.re - 1 / 2| * |u|) := by
  have hab : -a ≤ a := by linarith
  have hre : (s - 1 / 2).re = s.re - 1 / 2 := by simp
  unfold Gt
  refine (intervalIntegral.norm_integral_le_integral_norm hab).trans ?_
  apply intervalIntegral.integral_mono_on hab
  · exact ((hg.mul (by fun_prop)).norm).intervalIntegrable _ _
  · exact (hg.norm.mul (by fun_prop)).intervalIntegrable _ _
  · intro u _
    rw [norm_mul, norm_exp_mul_ofReal, hre]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    calc (s.re - 1 / 2) * u ≤ |(s.re - 1 / 2) * u| := le_abs_self _
      _ = |s.re - 1 / 2| * |u| := abs_mul _ _

/-- Monotonicity of the weighted integral in the weight exponent. -/
theorem weighted_integral_mono {a : ℝ} (ha : 0 ≤ a) {φ : ℝ → ℂ} (hφ : Continuous φ) {c c' : ℝ}
    (hc : c ≤ c') :
    ∫ u in (-a)..a, ‖φ u‖ * Real.exp (c * |u|)
      ≤ ∫ u in (-a)..a, ‖φ u‖ * Real.exp (c' * |u|) := by
  apply intervalIntegral.integral_mono_on (by linarith)
  · exact (hφ.norm.mul (by fun_prop)).intervalIntegrable _ _
  · exact (hφ.norm.mul (by fun_prop)).intervalIntegrable _ _
  · intro u _
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc (abs_nonneg _))

lemma continuous_deriv2_gaussR (R b α : ℝ) : Continuous (deriv (deriv (gaussR R b α))) := by
  rw [deriv2_gaussR]
  exact continuous_gaussR2 R b α

/-! ## The left line -/

/-- **Uniform decay of `Gt R (gaussR R b α)` on the left line:** `‖Gt R (gaussR R b α) (−½ + it)‖
≤ M / (1 + t²)` with `M` independent of `R ≥ 2`. -/
theorem exists_uniform_Gt_left_line {b : ℝ} (hb : 0 < b) (α : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ R : ℝ, 2 ≤ R → ∀ t : ℝ,
      ‖Gt R (gaussR R b α) (-1/2 + t * I)‖ ≤ M / (1 + t ^ 2) := by
  obtain ⟨K₀, hK₀⟩ := gaussR_sup_uniform hb α 1 zero_le_one
  obtain ⟨K₂, hK₂⟩ := gaussR_weighted_uniform hb α 1 zero_le_one
  refine ⟨2 * (|K₀| + |K₂|), by positivity, fun R hR t => ?_⟩
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hre : (-1/2 + t * I : ℂ).re - 1 / 2 = -1 := by simp; norm_num
  have him : (-1/2 + t * I : ℂ).im = t := by simp
  have h1 : ‖Gt R (gaussR R b α) (-1/2 + t * I)‖ ≤ |K₀| := by
    refine (Gt_norm_le_weighted hR0 (continuous_gaussR R b α) _).trans ?_
    rw [hre, abs_neg, abs_one]
    exact (hK₀ R hR).trans (le_abs_self _)
  have hpos : 0 < 1 + t ^ 2 := by positivity
  by_cases ht : t ^ 2 ≤ 1
  · rw [le_div_iff₀ hpos]
    nlinarith [abs_nonneg K₀, abs_nonneg K₂, norm_nonneg (Gt R (gaussR R b α) (-1/2 + t * I))]
  · push_neg at ht
    have ht0 : t ≠ 0 := by
      rintro rfl
      norm_num at ht
    have h2 : ‖Gt R (gaussR R b α) (-1/2 + t * I)‖ ≤ |K₂| / t ^ 2 := by
      have := Gt_bound_weighted (gaussR_isTestFn hR b α) (-1/2 + t * I) (by rw [him]; exact ht0)
      rw [him, hre, abs_neg, abs_one] at this
      refine this.trans ?_
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact (hK₂ R hR).trans (le_abs_self _)
    refine h2.trans ?_
    rw [div_le_div_iff₀ (by positivity) hpos]
    nlinarith [abs_nonneg K₀, abs_nonneg K₂]

/-- **The left line converges:** `leftLine R (gaussR R b α) → leftLineInf (gauss b α)`. -/
theorem tendsto_leftLine {b : ℝ} (hb : 0 < b) (α : ℝ) :
    Tendsto (fun R : ℕ => leftLine R (gaussR R b α)) atTop (𝓝 (leftLineInf (gauss b α))) := by
  obtain ⟨B, hB⟩ := LeftLineBound.norm_logDeriv_zeta_left_line_all
  obtain ⟨M, hM0, hM⟩ := exists_uniform_Gt_left_line hb α
  have hB0 : 0 ≤ B := by
    have h0 := hB 0
    have hlog : 0 < Real.log (|(0 : ℝ)| + 2) := by
      rw [abs_zero, zero_add]; exact Real.log_pos (by norm_num)
    have hn := norm_nonneg (deriv riemannZeta (-1/2 + (0 : ℝ) * I) / riemannZeta (-1/2 + (0 : ℝ) * I))
    by_contra hneg
    push_neg at hneg
    have hm := mul_neg_of_neg_of_pos hneg hlog
    exact absurd (h0.trans_lt hm) (not_lt.mpr (norm_nonneg _))
  rw [← Filter.tendsto_add_atTop_iff_nat 2]
  unfold leftLine leftLineInf
  refine tendsto_integral_of_dominated_convergence
    (F := fun (n : ℕ) (t : ℝ) => deriv riemannZeta (-1/2 + t * I) / riemannZeta (-1/2 + t * I)
      * Gt ((n + 2 : ℕ) : ℝ) (gaussR ((n + 2 : ℕ) : ℝ) b α) (-1/2 + t * I))
    (fun t : ℝ => B * M * (Real.log (|t| + 2) / (1 + t ^ 2))) ?_ ?_ ?_ ?_
  · intro n
    exact (LeftLineBound.continuous_logDeriv_left_line.mul
      ((Gt_continuous (a := ((n + 2 : ℕ) : ℝ)) (continuous_gaussR _ b α)).comp
        (by fun_prop : Continuous fun t : ℝ => (-1/2 + t * I : ℂ)))).aestronglyMeasurable
  · exact LeftLineBound.integrable_log_div_one_add_sq.const_mul _
  · intro n
    refine Eventually.of_forall fun t => ?_
    have hn : (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
      push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [norm_mul]
    calc _ ≤ (B * Real.log (|t| + 2)) * (M / (1 + t ^ 2)) :=
          mul_le_mul (hB t) (hM _ hn t) (norm_nonneg _) ((norm_nonneg _).trans (hB t))
      _ = _ := by ring
  · refine Eventually.of_forall fun t => ?_
    apply Tendsto.const_mul
    exact (tendsto_gaussR_Gt hb α (-1/2 + t * I)).comp (tendsto_add_atTop_nat 2)

/-! ## The prime sum -/

/-- The prime-side majorant `Λ(n) e^{−b (log n)²}` (uniform in the cutoff). -/
def primeBound (b : ℝ) (n : ℕ) : ℝ := Λ n * Real.exp (-b * (Real.log n) ^ 2)

lemma primeBound_nonneg (b : ℝ) (n : ℕ) : 0 ≤ primeBound b n :=
  mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le

lemma norm_natCast_cpow_neg_half_le (n : ℕ) : ‖(n : ℂ) ^ (-(1 / 2) : ℂ)‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, Complex.zero_cpow (by norm_num)]
    simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [show ((n : ℕ) : ℂ) = ((n : ℝ) : ℂ) by norm_cast,
      Complex.norm_cpow_eq_rpow_re_of_pos hn']
    apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn)
    simp

lemma norm_primeTerm_le (b α R : ℝ) (n : ℕ) :
    ‖(Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2) : ℂ) * gaussR R b α (Real.log n)‖ ≤ primeBound b n := by
  have hΛ : (0 : ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, _root_.abs_of_nonneg hΛ]
  unfold primeBound
  calc Λ n * ‖(n : ℂ) ^ (-(1 / 2) : ℂ)‖ * ‖gaussR R b α (Real.log n)‖
      ≤ Λ n * 1 * Real.exp (-b * (Real.log n) ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (norm_natCast_cpow_neg_half_le n) hΛ)
          (norm_gaussR_le R b α _) (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The prime-side majorant is summable: for `log n ≥ 3/b`, `Λ(n) e^{−b log² n} ≤ n · n^{−3}`. -/
theorem summable_primeBound {b : ℝ} (hb : 0 < b) : Summable (primeBound b) := by
  refine Summable.of_norm_bounded_eventually_nat (g := fun n : ℕ => 1 / (n : ℝ) ^ 2)
    (Real.summable_one_div_nat_pow.mpr one_lt_two) ?_
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop (3 / b)), eventually_ge_atTop 1]
    with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hL0 : 0 ≤ Real.log n := Real.log_nonneg hn1'
  have hΛ : Λ n ≤ (n : ℝ) :=
    ArithmeticFunction.vonMangoldt_le_log.trans (by linarith [Real.log_le_sub_one_of_pos hn0])
  have hΛ0 : (0 : ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  have h3 : 3 * Real.log n ≤ b * (Real.log n) ^ 2 := by
    have : 3 / b ≤ Real.log n := hn
    rw [div_le_iff₀ hb] at this
    nlinarith
  have hexp3 : Real.exp ((3 : ℕ) * Real.log n) = (n : ℝ) ^ 3 := by
    rw [Real.exp_nat_mul, Real.exp_log hn0]
  push_cast at hexp3
  have hexp : Real.exp (-b * (Real.log n) ^ 2) ≤ 1 / (n : ℝ) ^ 3 := by
    calc Real.exp (-b * (Real.log n) ^ 2) ≤ Real.exp (-(3 * Real.log n)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = 1 / (n : ℝ) ^ 3 := by rw [Real.exp_neg, hexp3, one_div]
  rw [Real.norm_eq_abs, _root_.abs_of_nonneg (primeBound_nonneg b n)]
  unfold primeBound
  calc Λ n * Real.exp (-b * (Real.log n) ^ 2) ≤ (n : ℝ) * (1 / (n : ℝ) ^ 3) :=
        mul_le_mul hΛ hexp (Real.exp_pos _).le hn0.le
    _ = 1 / (n : ℝ) ^ 2 := by field_simp

/-- **The prime sum converges** (Tannery's theorem with the majorant `primeBound`). -/
theorem tendsto_primeSum {b : ℝ} (hb : 0 < b) (α : ℝ) :
    Tendsto (fun R : ℕ =>
        ∑' n : ℕ, (Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2) : ℂ) * gaussR R b α (Real.log n))
      atTop (𝓝 (∑' n : ℕ, (Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2) : ℂ) * gauss b α (Real.log n))) := by
  apply tendsto_tsum_of_dominated_convergence (summable_primeBound hb)
  · intro n
    apply Tendsto.const_mul
    apply tendsto_const_nhds.congr'
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_ge_atTop (2 * |Real.log n| + 2))] with R hR
    have h2 : (2 : ℝ) ≤ R := by linarith [abs_nonneg (Real.log n)]
    rw [gaussR_eq_of_small h2 b α _ (by linarith)]
  · exact Eventually.of_forall fun R n => norm_primeTerm_le b α R n

/-! ## (1) The right-hand side converges -/

/-- **`weilRHS R (gaussR R b α) → weilRHSInf (gauss b α)`** as `R → ∞` in `ℕ`. -/
theorem tendsto_weilRHS {b : ℝ} (hb : 0 < b) (α : ℝ) :
    Tendsto (fun R : ℕ => weilRHS R (gaussR R b α)) atTop (𝓝 (weilRHSInf (gauss b α))) := by
  unfold weilRHS weilRHSInf
  exact ((tendsto_gaussR_Gt hb α 1).sub (tendsto_primeSum hb α)).sub
    ((tendsto_leftLine hb α).const_mul _)

/-! ## (2) The spectral sums converge -/

/-- **Spectral sums of the truncated Gaussians converge to the Gaussian spectral sum.** For a
spectrum `t : ι → ℂ` with `|Im (t i)| ≤ ½`, finitely many `|Re (t i)| ≤ 1`, and
`∑ 1/(Re t i)² < ∞`: `∑ᵢ gaussHat b α (t i)` is summable and
`∑ᵢ hfun R (gaussR R b α) (t i) → ∑ᵢ gaussHat b α (t i)`. -/
theorem tendsto_hfun_sum {ι : Type*} (t : ι → ℂ) (him : ∀ i, |(t i).im| ≤ 1 / 2)
    (hfin : {i | |(t i).re| ≤ 1}.Finite) (hsum : Summable (fun i => 1 / ((t i).re) ^ 2))
    {b : ℝ} (hb : 0 < b) (α : ℝ) :
    Summable (fun i => gaussHat b α (t i)) ∧
    Tendsto (fun R : ℕ => ∑' i, hfun R (gaussR R b α) (t i)) atTop
      (𝓝 (∑' i, gaussHat b α (t i))) := by
  obtain ⟨K₀, hK₀⟩ := gaussR_sup_uniform hb α (1 / 2) (by norm_num)
  obtain ⟨K₂, hK₂⟩ := gaussR_weighted_uniform hb α (1 / 2) (by norm_num)
  set bound : ι → ℝ := fun i =>
    |K₀| * (if |(t i).re| ≤ 1 then 1 else 0) + |K₂| * (1 / (t i).re ^ 2) with hbound
  have hbound_sum : Summable bound := by
    apply Summable.add
    · apply Summable.mul_left
      apply summable_of_ne_finset_zero (s := hfin.toFinset)
      intro i hi
      rw [Set.Finite.mem_toFinset] at hi
      simp only [mem_setOf_eq] at hi
      simp [hi]
    · exact hsum.mul_left _
  have hpt : ∀ R : ℝ, 2 ≤ R → ∀ i, ‖hfun R (gaussR R b α) (t i)‖ ≤ bound i := by
    intro R hR i
    have hR0 : (0 : ℝ) ≤ R := by linarith
    have h1 : ‖hfun R (gaussR R b α) (t i)‖ ≤ |K₀| := by
      rw [← Gt_half_add_I_mul]
      refine (Gt_norm_le_weighted hR0 (continuous_gaussR R b α) _).trans ?_
      have hre : (1 / 2 + I * t i : ℂ).re - 1 / 2 = -(t i).im := by simp
      rw [hre, abs_neg]
      refine (weighted_integral_mono hR0 (continuous_gaussR R b α) (him i)).trans ?_
      exact (hK₀ R hR).trans (le_abs_self _)
    by_cases hi : |(t i).re| ≤ 1
    · simp only [hbound, hi, if_true, mul_one]
      have : 0 ≤ |K₂| * (1 / (t i).re ^ 2) := by positivity
      linarith
    · simp only [hbound, hi, if_false, mul_zero, zero_add]
      push_neg at hi
      have hre0 : (t i).re ≠ 0 := by
        intro h
        rw [h, abs_zero] at hi
        linarith
      have h2 := hfun_bound_weighted (gaussR_isTestFn hR b α) (t i) hre0
      refine h2.trans ?_
      rw [mul_one_div]
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      refine (weighted_integral_mono hR0 (continuous_deriv2_gaussR R b α) (him i)).trans ?_
      exact (hK₂ R hR).trans (le_abs_self _)
  have hlim : ∀ i, Tendsto (fun R : ℕ => hfun R (gaussR R b α) (t i)) atTop
      (𝓝 (gaussHat b α (t i))) :=
    fun i => tendsto_gaussR_hfun hb α (t i)
  have hev : ∀ᶠ R : ℕ in atTop, ∀ i, ‖hfun R (gaussR R b α) (t i)‖ ≤ bound i := by
    filter_upwards [eventually_ge_atTop 2] with R hR
    exact hpt R (by exact_mod_cast hR)
  refine ⟨?_, tendsto_tsum_of_dominated_convergence hbound_sum hlim hev⟩
  refine Summable.of_norm_bounded (g := bound) hbound_sum fun i => ?_
  exact le_of_tendsto (tendsto_norm.comp (hlim i)) (hev.mono fun R h => h i)

/-! ## (3), (4) The explicit formula for Gaussians -/

/-- **The Gaussian explicit formula for any spectrum realizing the interface.** -/
theorem gaussian_formula_of_realizes {ι : Type*} (t : ι → ℂ) (him : ∀ i, |(t i).im| ≤ 1 / 2)
    (hfin : {i | |(t i).re| ≤ 1}.Finite) (hsum : Summable (fun i => 1 / ((t i).re) ^ 2))
    (hreal : RealizesExplicitFormula t) {b : ℝ} (hb : 0 < b) (α : ℝ) :
    HasSum (fun i => gaussHat b α (t i)) (weilRHSInf (gauss b α)) := by
  obtain ⟨hsumm, hlim⟩ := tendsto_hfun_sum t him hfin hsum hb α
  have hlim' : Tendsto (fun R : ℕ => ∑' i, hfun R (gaussR R b α) (t i)) atTop
      (𝓝 (weilRHSInf (gauss b α))) := by
    refine (tendsto_weilRHS hb α).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with R hR
    have hR' : (2 : ℝ) ≤ R := by exact_mod_cast hR
    exact ((hreal R (gaussR R b α) (gaussR_isTestFn hR' b α)
      (gaussR_support hR' b α)).tsum_eq).symm
  have heq := tendsto_nhds_unique hlim hlim'
  rw [← heq]
  exact hsumm.hasSum

/-- **The explicit formula for `gauss b α` at the nontrivial zeros** (canonical enumeration
with multiplicity). Unconditional. -/
theorem gaussian_formula_zeros {b : ℝ} (hb : 0 < b) (α : ℝ) :
    HasSum (fun x : Index => gaussHat b α (ordinate (canonical x))) (weilRHSInf (gauss b α)) := by
  apply gaussian_formula_of_realizes _ _ _ _ canonical_realizes hb α
  · intro x
    have h := ZetaStrip.mem_strip_of_isNontrivialZero (multEnum_canonical.nontrivial x)
    rw [ordinate_im, abs_le]
    constructor <;> linarith [h.1, h.2]
  · have := multEnum_canonical.finite 1
    simp_rw [ordinate_re]
    exact this
  · have := summable_inv_sq_im multEnum_canonical
    simp_rw [ordinate_re]
    exact this

/-- **The explicit formula for `gauss b α` on a real spectrum** `γ : ι → ℝ` with
`∑ 1/(1 + γᵢ²) < ∞` that realizes the explicit formula. -/
theorem gaussian_formula_real {ι : Type*} (γ : ι → ℝ)
    (hsum : Summable (fun i => 1 / (1 + (γ i) ^ 2))) (hγ : RealSpectrumRealizes γ)
    {b : ℝ} (hb : 0 < b) (α : ℝ) :
    HasSum (fun i => gaussHat b α ((γ i : ℝ) : ℂ)) (weilRHSInf (gauss b α)) := by
  have hfin : {i | |γ i| ≤ 1}.Finite := by
    have h := hsum.tendsto_cofinite_zero
    have h2 : ∀ᶠ i in cofinite, 1 / (1 + (γ i) ^ 2) < 1 / 2 :=
      h.eventually (gt_mem_nhds (by norm_num))
    rw [eventually_cofinite] at h2
    refine h2.subset fun i hi => ?_
    simp only [mem_setOf_eq, not_lt] at hi ⊢
    have : (γ i) ^ 2 ≤ 1 := by nlinarith [abs_le.mp hi, _root_.sq_abs (γ i)]
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  have hsum' : Summable (fun i => 1 / (((γ i : ℝ) : ℂ)).re ^ 2) := by
    simp only [Complex.ofReal_re]
    refine Summable.of_norm_bounded_eventually (g := fun i => 2 * (1 / (1 + (γ i) ^ 2)))
      (hsum.mul_left 2) ?_
    rw [eventually_cofinite]
    refine hfin.subset fun i hi => ?_
    simp only [mem_setOf_eq] at hi ⊢
    by_contra hcon
    apply hi
    push_neg at hcon
    have hsq : 1 < (γ i) ^ 2 := by nlinarith [abs_nonneg (γ i), _root_.sq_abs (γ i)]
    have hpos : 0 < (γ i) ^ 2 := by linarith
    rw [Real.norm_eq_abs, _root_.abs_of_nonneg (by positivity), mul_one_div,
      div_le_div_iff₀ hpos (by positivity)]
    nlinarith
  have hfin' : {i | |(((γ i : ℝ) : ℂ)).re| ≤ 1}.Finite := by simpa using hfin
  exact gaussian_formula_of_realizes (fun i => ((γ i : ℝ) : ℂ)) (fun i => by simp) hfin' hsum'
    hγ hb α

/-! ## (5) The trace identity -/

/-- **Gaussian trace identity.** For a real spectrum realizing the explicit formula, the Gaussian
spectral sum equals the Gaussian sum over the zeros. -/
theorem gaussian_trace_eq {ι : Type*} (γ : ι → ℝ)
    (hsum : Summable (fun i => 1 / (1 + (γ i) ^ 2))) (hγ : RealSpectrumRealizes γ)
    {b : ℝ} (hb : 0 < b) (α : ℝ) :
    ∑' i, gaussHat b α ((γ i : ℝ) : ℂ) = ∑' x : Index, gaussHat b α (ordinate (canonical x)) := by
  rw [(gaussian_formula_real γ hsum hγ hb α).tsum_eq, (gaussian_formula_zeros hb α).tsum_eq]

end GaussianTraceFormula

end
