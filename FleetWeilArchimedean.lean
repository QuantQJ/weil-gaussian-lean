import FleetWeilConvolution
import FleetSeparatedExplicitFormula
import FleetGammaIdentification

/-!
# Weil criterion, part 2: Formal Conjectures' `weilArchimedean` is minus hp-proof's
standard archimedean term

For a real `C^∞` function `f` vanishing for `|u| > B` and any `a > B`,
`FleetStandardExplicitFormula.standardArchimedean a f = −weilArchimedean f`.
The proof expands `Re ψ(1/4 + it/2)` by the partial-fraction series
(`FleetGammaIdentification.digamma_eq_series`), integrates each Lorentzian against `hfun`
by Fubini and Fourier inversion (`∫ hfun(t) e^{itv} dt = 2π f(−v)`), and sums the resulting
Laplace integrals as a geometric series.
-/

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped Real ContDiff FourierTransform

namespace FleetWeilCriterion

/-! ## (A) The real digamma series on the line `Re = 1/4` -/

/-- The `k`-th term of the real digamma series at `1/4 + i t/2`. -/
def dk (k : ℕ) (t : ℝ) : ℝ :=
  ((k : ℝ) + 1 / 4) / (((k : ℝ) + 1 / 4) ^ 2 + t ^ 2 / 4) - 1 / ((k : ℝ) + 1)

lemma re_inv_term (k : ℕ) (t : ℝ) :
    ((1 / 4 + (t : ℂ) * I / 2 + (k : ℂ))⁻¹ - ((k : ℂ) + 1)⁻¹).re = dk k t := by
  have h1 : (((k : ℂ) + 1)⁻¹).re = 1 / ((k : ℝ) + 1) := by
    rw [show ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_inv,
      Complex.ofReal_re, one_div]
  rw [Complex.sub_re, h1, Complex.inv_re]
  unfold dk
  congr 1
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.div_re, Complex.div_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.natCast_re, Complex.natCast_im]
  norm_num
  ring

theorem digammaWeight_eq (t : ℝ) :
    FleetSeparatedExplicitFormula.digammaWeight t =
      -Real.eulerMascheroniConstant - ∑' k : ℕ, dk k t := by
  have hz : 0 < (1 / 4 + (t : ℂ) * I / 2).re := by norm_num
  unfold FleetSeparatedExplicitFormula.digammaWeight FleetGammaKernel.psi
  rw [FleetGammaIdentification.digamma_eq_series _ hz, Complex.sub_re, Complex.neg_re,
    Complex.ofReal_re, Complex.re_tsum (FleetDigammaSeries.summable_deriv_q hz)]
  simp_rw [re_inv_term]

lemma dk_eq (k : ℕ) (t : ℝ) :
    dk k t = (3 * ((k : ℝ) + 1 / 4) - t ^ 2) /
      (4 * ((((k : ℝ) + 1 / 4) ^ 2 + t ^ 2 / 4) * ((k : ℝ) + 1))) := by
  have h1 : 0 < ((k : ℝ) + 1 / 4) ^ 2 + t ^ 2 / 4 := by positivity
  have h2 : 0 < (k : ℝ) + 1 := by positivity
  unfold dk
  field_simp
  ring

lemma abs_dk_le (k : ℕ) (t : ℝ) : |dk k t| ≤ (12 + 4 * t ^ 2) / ((k : ℝ) + 1) ^ 2 := by
  set K : ℝ := (k : ℝ) + 1 with hK
  have hK1 : 1 ≤ K := by rw [hK]; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have hc : (k : ℝ) + 1 / 4 = K - 3 / 4 := by rw [hK]; ring
  rw [dk_eq, hc, ← hK]
  have hD : 0 < (K - 3 / 4) ^ 2 + t ^ 2 / 4 := by nlinarith
  have hDK : 0 < 4 * (((K - 3 / 4) ^ 2 + t ^ 2 / 4) * K) := by positivity
  rw [abs_div, abs_of_pos hDK, div_le_div_iff₀ hDK (by positivity)]
  have hnum : |3 * (K - 3 / 4) - t ^ 2| ≤ 3 * K + t ^ 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg t]
  have hc4 : K ^ 2 ≤ 16 * (K - 3 / 4) ^ 2 := by nlinarith
  calc |3 * (K - 3 / 4) - t ^ 2| * K ^ 2 ≤ (3 * K + t ^ 2) * K ^ 2 :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
    _ ≤ (12 + 4 * t ^ 2) * (4 * (((K - 3 / 4) ^ 2 + t ^ 2 / 4) * K)) := by
        nlinarith [sq_nonneg t, mul_nonneg (sq_nonneg t) (sub_nonneg.2 hK1),
          mul_nonneg (mul_nonneg (sq_nonneg t) (sq_nonneg t)) (by linarith : (0:ℝ) ≤ K),
          mul_nonneg (sq_nonneg t) (by linarith : (0:ℝ) ≤ K)]

lemma summable_dk (t : ℝ) : Summable (fun k : ℕ => dk k t) := by
  have hs : Summable (fun k : ℕ => (12 + 4 * t ^ 2) / ((k : ℝ) + 1) ^ 2) := by
    have := (Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective (add_left_injective 1)
    simpa [div_eq_mul_inv, Function.comp_def] using this.mul_left (12 + 4 * t ^ 2)
  exact hs.of_norm_bounded (fun k => by rw [Real.norm_eq_abs]; exact abs_dk_le k t)

lemma continuous_dk (k : ℕ) : Continuous (dk k) := by
  unfold dk
  apply Continuous.sub _ continuous_const
  apply Continuous.div continuous_const (by fun_prop)
  intro t; positivity


/-- The integrand `φ(v) = (f v + f(−v)) e^{−v/2} − 2 f(0) e^{−2v}` of the summed series. -/
def phiW (f : ℝ → ℝ) (v : ℝ) : ℝ :=
  (f v + f (-v)) * Real.exp (-v / 2) - 2 * f 0 * Real.exp (-2 * v)

/-! ## (B) Standing hypotheses and the decay of `hfun` -/

/-- Standing hypotheses: `f` real and smooth, vanishing for `|u| > B`, with `0 ≤ B < a`. -/
structure Admissible (f : ℝ → ℝ) (a B : ℝ) : Prop where
  smooth : ContDiff ℝ ∞ f
  B_nonneg : 0 ≤ B
  B_lt : B < a
  vanish : ∀ u, B < |u| → f u = 0

/-- The complex-valued version of a real function. -/
def cF (f : ℝ → ℝ) : ℝ → ℂ := fun u => (f u : ℂ)

namespace Admissible

variable {f : ℝ → ℝ} {a B : ℝ}

lemma vanishC (h : Admissible f a B) : ∀ u, B < |u| → cF f u = 0 := fun u hu => by
  simp [cF, h.vanish u hu]

lemma supp (h : Admissible f a B) : ∀ u, a < |u| → cF f u = 0 := fun u hu =>
  h.vanishC u (lt_trans h.B_lt hu)

lemma contDiffC (h : Admissible f a B) : ContDiff ℝ ∞ (cF f) :=
  Complex.ofRealCLM.contDiff.comp h.smooth

lemma isTestFn (h : Admissible f a B) : TestFunctions.IsTestFn a (cF f) :=
  isTestFn_of_vanish h.B_nonneg h.B_lt (h.contDiffC.of_le (by norm_cast)) h.vanishC

lemma continuous (h : Admissible f a B) : Continuous f := h.smooth.continuous

lemma deriv (h : Admissible f a B) : Admissible (_root_.deriv f) a B where
  smooth := by simpa using h.smooth.iterate_deriv 1
  B_nonneg := h.B_nonneg
  B_lt := h.B_lt
  vanish := deriv_vanish h.vanish

lemma deriv_cF (h : Admissible f a B) : _root_.deriv (cF f) = cF (_root_.deriv f) := by
  funext u
  have hd : HasDerivAt f (_root_.deriv f u) u :=
    ((h.smooth.differentiable (by simp)) u).hasDerivAt
  exact hd.ofReal_comp.deriv

lemma hfun_deriv2 (h : Admissible f a B) (t : ℂ) :
    TestFunctions.hfun a (cF (_root_.deriv (_root_.deriv f))) t =
      -t ^ 2 * TestFunctions.hfun a (cF f) t := by
  have hs := TestFunctions.sq_mul_Gt_eq h.isTestFn (1 / 2 + I * t)
  rw [TestFunctions.Gt_half_add_I_mul] at hs
  rw [h.deriv_cF, h.deriv.deriv_cF] at hs
  have hr : (∫ u in (-a)..a, cF (_root_.deriv (_root_.deriv f)) u *
      Complex.exp ((1 / 2 + I * t - 1 / 2) * u)) =
      TestFunctions.hfun a (cF (_root_.deriv (_root_.deriv f))) t := by
    rw [← TestFunctions.Gt_half_add_I_mul]; rfl
  rw [hr] at hs
  rw [← hs]
  ring_nf
  rw [Complex.I_sq]
  ring

lemma integrable_hfun (h : Admissible f a B) :
    Integrable (fun t : ℝ => TestFunctions.hfun a (cF f) (t : ℂ)) :=
  FleetFourierNormalization.integrable_hfun h.isTestFn

lemma continuous_hfun (h : Admissible f a B) :
    Continuous (fun t : ℝ => TestFunctions.hfun a (cF f) (t : ℂ)) := by
  have hc := TestFunctions.Gt_continuous (a := a) h.isTestFn.continuous
  have : (fun t : ℝ => TestFunctions.hfun a (cF f) (t : ℂ)) =
      fun t : ℝ => TestFunctions.Gt a (cF f) (1 / 2 + I * (t : ℂ)) := by
    funext t; rw [TestFunctions.Gt_half_add_I_mul]
  rw [this]
  exact hc.comp (by fun_prop)

/-- `∫ ‖hfun(t)‖ (12 + 4t²) dt < ∞`, from the decay of `hfun` of `f''`. -/
lemma integrable_weighted (h : Admissible f a B) :
    Integrable (fun t : ℝ => ‖TestFunctions.hfun a (cF f) (t : ℂ)‖ * (12 + 4 * t ^ 2)) := by
  have h1 := h.integrable_hfun.norm.mul_const 12
  have h2 := h.deriv.deriv.integrable_hfun.norm.mul_const 4
  refine (h1.add h2).congr (Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply]
  rw [h.hfun_deriv2, norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    sq_abs]
  ring

end Admissible

/-! ## (C) Interchanging the digamma series with the integral -/

theorem integral_hfun_mul_tsum {f : ℝ → ℝ} {a B : ℝ} (h : Admissible f a B) :
    ∫ t : ℝ, TestFunctions.hfun a (cF f) (t : ℂ) * ((∑' k : ℕ, dk k t : ℝ) : ℂ) =
      ∑' k : ℕ, ∫ t : ℝ, TestFunctions.hfun a (cF f) (t : ℂ) * (dk k t : ℂ) := by
  have hint : ∀ k : ℕ, Integrable (fun t : ℝ => TestFunctions.hfun a (cF f) (t : ℂ) * (dk k t : ℂ)) := by
    intro k
    refine (h.integrable_weighted.div_const (((k : ℝ) + 1) ^ 2)).mono'
      ((h.continuous_hfun.mul (Complex.continuous_ofReal.comp (continuous_dk k))).aestronglyMeasurable)
      (Eventually.of_forall fun t => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (abs_dk_le k t) (norm_nonneg _)
  have hsum : Summable (fun k : ℕ =>
      ∫ t : ℝ, ‖TestFunctions.hfun a (cF f) (t : ℂ) * (dk k t : ℂ)‖) := by
    set I0 := ∫ t : ℝ, ‖TestFunctions.hfun a (cF f) (t : ℂ)‖ * (12 + 4 * t ^ 2)
    have hs : Summable (fun k : ℕ => I0 / ((k : ℝ) + 1) ^ 2) := by
      have := (Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective (add_left_injective 1)
      simpa [div_eq_mul_inv, Function.comp_def] using this.mul_left I0
    refine hs.of_nonneg_of_le (fun k => integral_nonneg fun t => norm_nonneg _) (fun k => ?_)
    rw [← integral_div]
    refine integral_mono (hint k).norm (h.integrable_weighted.div_const _) (fun t => ?_)
    simp only
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (abs_dk_le k t) (norm_nonneg _)
  rw [integral_tsum_of_summable_integral_norm hint hsum]
  congr 1
  funext t
  rw [Complex.ofReal_tsum, tsum_mul_left]

/-! ## (D) Lorentzians: Fubini and Fourier inversion -/

lemma exp_neg_abs_le {b : ℝ} (hb : 0 < b) (v : ℝ) :
    Real.exp (-b * |v|) ≤ (1 + 2 / b ^ 2) * (1 + v ^ 2)⁻¹ := by
  have hq := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ b * |v|)
  have hE : 0 < Real.exp (b * |v|) := Real.exp_pos _
  have h1 : (1 + v ^ 2) ≤ (1 + 2 / b ^ 2) * (1 + b * |v| + (b * |v|) ^ 2 / 2) := by
    have hv : (b * |v|) ^ 2 = b ^ 2 * v ^ 2 := by rw [mul_pow, sq_abs]
    rw [hv]
    have hb2 : 0 < b ^ 2 := by positivity
    have : (2 / b ^ 2) * (b ^ 2 * v ^ 2 / 2) = v ^ 2 := by field_simp
    have hX : 0 ≤ b * |v| := mul_nonneg hb.le (abs_nonneg v)
    have hk : 0 ≤ 2 / b ^ 2 := by positivity
    have hY : b ^ 2 * v ^ 2 / 2 ≤ 1 + b * |v| + b ^ 2 * v ^ 2 / 2 := by linarith
    have := mul_le_mul_of_nonneg_left hY hk
    nlinarith [sq_nonneg v, sq_nonneg b, mul_nonneg hb2.le (sq_nonneg v)]
  have h2 : (1 + 2 / b ^ 2) * (1 + b * |v| + (b * |v|) ^ 2 / 2) ≤
      (1 + 2 / b ^ 2) * Real.exp (b * |v|) :=
    mul_le_mul_of_nonneg_left hq (by positivity)
  have h3 : 0 < 1 + v ^ 2 := by positivity
  rw [show -b * |v| = -(b * |v|) by ring, Real.exp_neg, ← one_div, ← div_eq_mul_inv,
    div_le_div_iff₀ hE h3]
  linarith

lemma integrable_exp_neg_abs {b : ℝ} (hb : 0 < b) :
    Integrable (fun v : ℝ => Real.exp (-b * |v|)) := by
  refine (integrable_inv_one_add_sq.const_mul (1 + 2 / b ^ 2)).mono'
    (by fun_prop) (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact exp_neg_abs_le hb v

/-- `∫ e^{−2c|v|} e^{itv} dv = c / (c² + t²/4)`. -/
theorem lorentz_integral {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ∫ v : ℝ, ((Real.exp (-(2 * c) * |v|) : ℝ) : ℂ) * Complex.exp (I * t * v) =
      ((c / (c ^ 2 + t ^ 2 / 4) : ℝ) : ℂ) := by
  have h2c : 0 < 2 * c := by linarith
  have hint : Integrable (fun v : ℝ => ((Real.exp (-(2 * c) * |v|) : ℝ) : ℂ) *
      Complex.exp (I * t * v)) := by
    refine (integrable_exp_neg_abs h2c).mono' (by fun_prop) (Eventually.of_forall fun v => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      Complex.norm_exp]
    simp
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0) hint.integrableOn hint.integrableOn]
  have hR : ∫ v in Ioi (0 : ℝ), ((Real.exp (-(2 * c) * |v|) : ℝ) : ℂ) * Complex.exp (I * t * v) =
      1 / (2 * c - I * t) := by
    have hre : ((-(2 * c : ℂ)) + I * t).re < 0 := by simp; linarith
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun v : ℝ =>
      Complex.exp ((-(2 * c : ℂ) + I * t) * v)) ?_]
    · rw [integral_exp_mul_complex_Ioi hre 0]
      have hne : (-(2 * c : ℂ)) + I * t ≠ 0 := by
        intro h0; have := congrArg Complex.re h0; simp at this; linarith
      have hne' : (2 * c : ℂ) - I * t ≠ 0 := by
        intro h0; apply hne; linear_combination -h0
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
      field_simp
      ring
    · intro v hv
      simp only
      rw [abs_of_pos (mem_Ioi.mp hv), Complex.ofReal_exp, ← Complex.exp_add]
      congr 1; push_cast; ring
  have hL : ∫ v in Iic (0 : ℝ), ((Real.exp (-(2 * c) * |v|) : ℝ) : ℂ) * Complex.exp (I * t * v) =
      1 / (2 * c + I * t) := by
    have hneg := integral_comp_neg_Iic (0 : ℝ) (fun w : ℝ =>
      ((Real.exp (-(2 * c) * |w|) : ℝ) : ℂ) * Complex.exp (I * (-t : ℝ) * w))
    simp only [neg_zero] at hneg
    have he : (fun v : ℝ => ((Real.exp (-(2 * c) * |v|) : ℝ) : ℂ) * Complex.exp (I * t * v)) =
        fun v : ℝ => ((Real.exp (-(2 * c) * |-v|) : ℝ) : ℂ) * Complex.exp (I * (-t : ℝ) * (-v : ℝ)) := by
      funext v; rw [abs_neg]; push_cast; ring_nf
    rw [he, hneg]
    have hre : ((-(2 * c : ℂ)) - I * t).re < 0 := by simp; linarith
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun v : ℝ =>
      Complex.exp ((-(2 * c : ℂ) - I * t) * v)) ?_]
    · rw [integral_exp_mul_complex_Ioi hre 0]
      have hne : (-(2 * c : ℂ)) - I * t ≠ 0 := by
        intro h0; have := congrArg Complex.re h0; simp at this; linarith
      have hne' : (2 * c : ℂ) + I * t ≠ 0 := by
        intro h0; apply hne; linear_combination -h0
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
      field_simp
      ring
    · intro v hv
      simp only
      rw [abs_of_pos (mem_Ioi.mp hv), Complex.ofReal_exp, ← Complex.exp_add]
      congr 1; push_cast; ring
  rw [hL, hR]
  have h1 : (2 * c : ℂ) + I * t ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this; linarith
  have h2 : (2 * c : ℂ) - I * t ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this; linarith
  have h3 : ((c ^ 2 + t ^ 2 / 4 : ℝ) : ℂ) ≠ 0 := by
    have : 0 < c ^ 2 + t ^ 2 / 4 := by positivity
    exact_mod_cast this.ne'
  have hprod : (2 * (c : ℂ) + I * t) * (2 * c - I * t) = 4 * (c ^ 2 + t ^ 2 / 4) := by
    ring_nf; rw [Complex.I_sq]; ring
  rw [div_add_div _ _ h1 h2, hprod]
  push_cast at h3 ⊢
  field_simp
  ring

namespace Admissible

variable {f : ℝ → ℝ} {a B : ℝ}

lemma integrable_cF (h : Admissible f a B) : Integrable (cF f) :=
  h.isTestFn.continuous.integrable_of_hasCompactSupport (hasCompactSupport_of_radius h.vanishC)

/-- **Fourier inversion** in the `hfun` convention: `∫ hfun(t) e^{itv} dt = 2π f(−v)`. -/
theorem integral_hfun_mul_exp (h : Admissible f a B) (v : ℝ) :
    ∫ t : ℝ, TestFunctions.hfun a (cF f) (t : ℂ) * Complex.exp (I * t * v) =
      2 * (Real.pi : ℂ) * cF f (-v) := by
  have hsupp := h.supp
  have hg := h.integrable_cF
  have hnonzero : (-(1 / (2 * Real.pi)) : ℝ) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero one_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  have hfg : Integrable (𝓕 (cF f)) := by
    apply (integrable_comp_mul_left_iff (𝓕 (cF f)) hnonzero).mp
    simpa only [← FleetFourierNormalization.hfun_eq_fourier h.isTestFn hsupp] using
      h.integrable_hfun
  have hinv := hg.fourierInv_fourier_eq hfg (h.isTestFn.continuous.continuousAt (x := -v))
  rw [Real.fourierInv_eq'] at hinv
  set G : ℝ → ℂ := fun ξ => Complex.exp (↑(2 * Real.pi * inner ℝ ξ (-v)) * I) • 𝓕 (cF f) ξ
  have hG : ∀ t : ℝ, TestFunctions.hfun a (cF f) (t : ℂ) * Complex.exp (I * t * v) =
      G (-(1 / (2 * Real.pi)) * t) := by
    intro t
    rw [FleetFourierNormalization.hfun_eq_fourier h.isTestFn hsupp]
    simp only [G, smul_eq_mul]
    rw [mul_comm]
    congr 2
    simp only [RCLike.inner_apply, conj_trivial]
    push_cast
    field_simp
  simp_rw [hG]
  rw [Measure.integral_comp_mul_left, hinv]
  have hscale : |(-(1 / (2 * Real.pi)) : ℝ)⁻¹| = 2 * Real.pi := by
    rw [abs_inv, abs_neg, abs_of_pos (by positivity), inv_div, div_one]
  rw [hscale, Complex.real_smul]
  push_cast
  ring

lemma bounded (h : Admissible f a B) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |f x| ≤ M := by
  obtain ⟨M, hM⟩ := h.continuous.bounded_above_of_compact_support
    (hasCompactSupport_of_radius h.vanish)
  exact ⟨max M 0, le_max_right _ _, fun x => (hM x).trans (le_max_left _ _)⟩

/-- `∫ e^{−2c|v|} f(−v) dv = ∫_{v>0} (f v + f(−v)) e^{−2cv} dv`. -/
lemma integral_exp_abs_mul_neg (h : Admissible f a B) {c : ℝ} (hc : 0 < c) :
    ∫ v : ℝ, Real.exp (-(2 * c) * |v|) * f (-v) =
      ∫ v in Ioi (0 : ℝ), (f v + f (-v)) * Real.exp (-(2 * c) * v) := by
  obtain ⟨M, hM0, hM⟩ := h.bounded
  have h2c : 0 < 2 * c := by linarith
  have hint : Integrable (fun v : ℝ => Real.exp (-(2 * c) * |v|) * f (-v)) := by
    refine ((integrable_exp_neg_abs h2c).mul_const M).mono'
      (by have := h.continuous; fun_prop) (Eventually.of_forall fun v => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hM _) (Real.exp_pos _).le
  have hIoi : ∀ g : ℝ → ℝ, (∀ x, |g x| ≤ M) → Continuous g →
      IntegrableOn (fun v : ℝ => g v * Real.exp (-(2 * c) * v)) (Ioi 0) := by
    intro g hg hgc
    refine ((exp_neg_integrableOn_Ioi 0 h2c).const_mul M).mono'
      (by fun_prop) ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v _ => ?_))
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (hg v) (Real.exp_pos _).le
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0) hint.integrableOn hint.integrableOn]
  have hL : ∫ v in Iic (0 : ℝ), Real.exp (-(2 * c) * |v|) * f (-v) =
      ∫ v in Ioi (0 : ℝ), f v * Real.exp (-(2 * c) * v) := by
    have hneg := integral_comp_neg_Iic (0 : ℝ) (fun w : ℝ => Real.exp (-(2 * c) * |w|) * f w)
    simp only [neg_zero, abs_neg] at hneg
    rw [hneg]
    refine setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
    rw [abs_of_pos (mem_Ioi.mp hv), mul_comm]
  have hR : ∫ v in Ioi (0 : ℝ), Real.exp (-(2 * c) * |v|) * f (-v) =
      ∫ v in Ioi (0 : ℝ), f (-v) * Real.exp (-(2 * c) * v) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
    rw [abs_of_pos (mem_Ioi.mp hv), mul_comm]
  rw [hL, hR, ← integral_add (hIoi f hM h.continuous)
    (hIoi (fun v => f (-v)) (fun v => hM _) (h.continuous.comp continuous_neg))]
  congr 1
  funext v
  ring

/-- **Lorentzian pairing.** `(1/2π) ∫ hfun(t) · c/(c² + t²/4) dt = ∫_{v>0} (f v + f(−v)) e^{−2cv} dv`. -/
theorem lorentz_pairing (h : Admissible f a B) {c : ℝ} (hc : 0 < c) :
    (1 / (2 * (Real.pi : ℂ))) *
      ∫ t : ℝ, TestFunctions.hfun a (cF f) (t : ℂ) * ((c / (c ^ 2 + t ^ 2 / 4) : ℝ) : ℂ) =
      ((∫ v in Ioi (0 : ℝ), (f v + f (-v)) * Real.exp (-(2 * c) * v) : ℝ) : ℂ) := by
  have h2c : 0 < 2 * c := by linarith
  simp_rw [← lorentz_integral hc]
  have hcφ : Continuous (fun v : ℝ => ((Real.exp (-(2 * c) * |v|) : ℝ) : ℂ)) := by fun_prop
  have hpull : ∀ t : ℝ, TestFunctions.hfun a (cF f) (t : ℂ) *
      (∫ v : ℝ, ((Real.exp (-(2 * c) * |v|) : ℝ) : ℂ) * Complex.exp (I * t * v)) =
      ∫ v : ℝ, TestFunctions.hfun a (cF f) (t : ℂ) * (((Real.exp (-(2 * c) * |v|) : ℝ) : ℂ) * Complex.exp (I * t * v)) := by
    intro t; rw [integral_const_mul]
  simp_rw [hpull]
  have hI : Integrable (Function.uncurry fun (t v : ℝ) =>
      TestFunctions.hfun a (cF f) (t : ℂ) * (((Real.exp (-(2 * c) * |v|) : ℝ) : ℂ) * Complex.exp (I * t * v)))
      (volume.prod volume) := by
    have hmaj := Integrable.mul_prod (μ := volume) (ν := volume) h.integrable_hfun.norm
      (integrable_exp_neg_abs h2c)
    refine hmaj.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hc1 := h.continuous_hfun
      exact (by
        apply Continuous.aestronglyMeasurable
        simp only [Function.uncurry_def]
        exact (hc1.comp continuous_fst).mul ((hcφ.comp continuous_snd).mul (by fun_prop)))
    · simp only [Function.uncurry_def]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        Complex.norm_exp]
      simp
  rw [integral_integral_swap hI]
  have hinner : ∀ v : ℝ, (∫ t : ℝ, TestFunctions.hfun a (cF f) (t : ℂ) *
      (((Real.exp (-(2 * c) * |v|) : ℝ) : ℂ) * Complex.exp (I * t * v))) = ((Real.exp (-(2 * c) * |v|) : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * cF f (-v)) := by
    intro v
    rw [← h.integral_hfun_mul_exp v, ← integral_const_mul]
    congr 1; funext t; ring
  simp_rw [hinner]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hre : (∫ v : ℝ, ((Real.exp (-(2 * c) * |v|) : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * cF f (-v))) =
      2 * (Real.pi : ℂ) * ((∫ v : ℝ, Real.exp (-(2 * c) * |v|) * f (-v) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal, ← integral_const_mul]
    congr 1; funext v; simp only [cF]; push_cast; ring
  rw [hre, h.integral_exp_abs_mul_neg hc, ← mul_assoc, one_div,
    inv_mul_cancel₀ (mul_ne_zero two_ne_zero hpi), one_mul]

lemma integrableOn_mul_exp {g : ℝ → ℝ} {M b : ℝ} (hb : 0 < b) (hg : ∀ x, |g x| ≤ M)
    (hgc : Continuous g) :
    IntegrableOn (fun v : ℝ => g v * Real.exp (-b * v)) (Ioi 0) := by
  refine ((exp_neg_integrableOn_Ioi 0 hb).const_mul M).mono'
    (by fun_prop) ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v _ => ?_))
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (hg v) (Real.exp_pos _).le

/-- The `k`-th digamma term against `hfun`, as a Laplace integral. -/
theorem term_k (h : Admissible f a B) (k : ℕ) :
    (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, TestFunctions.hfun a (cF f) (t : ℂ) * (dk k t : ℂ) =
      ((∫ v in Ioi (0 : ℝ), phiW f v * Real.exp (-2 * v) ^ k : ℝ) : ℂ) := by
  obtain ⟨M, hM0, hM⟩ := h.bounded
  set c : ℝ := (k : ℝ) + 1 / 4 with hcdef
  have hc : 0 < c := by positivity
  have hK : 0 < (k : ℝ) + 1 := by positivity
  have hsplit : ∀ t : ℝ, TestFunctions.hfun a (cF f) (t : ℂ) * (dk k t : ℂ) =
      TestFunctions.hfun a (cF f) (t : ℂ) * ((c / (c ^ 2 + t ^ 2 / 4) : ℝ) : ℂ) -
        TestFunctions.hfun a (cF f) (t : ℂ) * ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) := by
    intro t; rw [← mul_sub]; congr 1; rw [hcdef]; unfold dk; push_cast; ring
  have hL : Integrable (fun t : ℝ => TestFunctions.hfun a (cF f) (t : ℂ) *
      ((c / (c ^ 2 + t ^ 2 / 4) : ℝ) : ℂ)) := by
    refine (h.integrable_hfun.norm.mul_const (1 / c)).mono'
      (h.continuous_hfun.mul (Complex.continuous_ofReal.comp
        (continuous_const.div (by fun_prop) (fun t => by positivity)))).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) hc]
    nlinarith [sq_nonneg t]
  simp_rw [hsplit]
  rw [integral_sub hL (h.integrable_hfun.mul_const _), integral_mul_const,
    FleetFourierNormalization.integral_hfun h.isTestFn h.supp, mul_sub, lorentz_pairing h hc]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  -- the right side
  have hpt : ∀ v : ℝ, phiW f v * Real.exp (-2 * v) ^ k =
      (f v + f (-v)) * Real.exp (-(2 * c) * v) -
        2 * f 0 * Real.exp (-(2 * ((k : ℝ) + 1)) * v) := by
    intro v
    unfold phiW
    rw [← Real.exp_nat_mul, sub_mul, mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
    congr 2
    · congr 1; rw [hcdef]; ring
    · congr 1; ring
  have hI1 : IntegrableOn (fun v : ℝ => (f v + f (-v)) * Real.exp (-(2 * c) * v)) (Ioi 0) :=
    integrableOn_mul_exp (M := 2 * M) (by positivity)
      (fun x => (abs_add_le _ _).trans (by linarith [hM x, hM (-x)]))
      (h.continuous.add (h.continuous.comp continuous_neg))
  have hI2 : IntegrableOn (fun v : ℝ => 2 * f 0 * Real.exp (-(2 * ((k : ℝ) + 1)) * v)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (by positivity)).const_mul _
  have hexp : ∫ v in Ioi (0 : ℝ), 2 * f 0 * Real.exp (-(2 * ((k : ℝ) + 1)) * v) =
      f 0 / ((k : ℝ) + 1) := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 0]
    field_simp
    simp
  simp_rw [hpt]
  rw [integral_sub hI1 hI2, hexp]
  generalize (∫ v in Ioi (0 : ℝ), (f v + f (-v)) * Real.exp (-(2 * c) * v)) = J
  simp only [cF]
  push_cast
  field_simp

/-- `|f x − f 0| ≤ D |x|`. -/
lemma lipschitz_zero (h : Admissible f a B) : ∃ D : ℝ, 0 ≤ D ∧ ∀ x, |f x - f 0| ≤ D * |x| := by
  obtain ⟨D, hD0, hD⟩ := h.deriv.bounded
  refine ⟨D, hD0, fun x => ?_⟩
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := univ) (x := 0) (y := x) (C := D)
    (fun z _ => (h.smooth.differentiable (by simp)) z)
    (fun z _ => by rw [Real.norm_eq_abs]; exact hD z) convex_univ (mem_univ _) (mem_univ _)
  simpa [Real.norm_eq_abs] using this

lemma abs_phiW_le_lin (h : Admissible f a B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v : ℝ, 0 ≤ v → |phiW f v| ≤ K * v := by
  obtain ⟨D, hD0, hD⟩ := h.lipschitz_zero
  refine ⟨2 * D + 4 * |f 0|, by positivity, fun v hv => ?_⟩
  have e1 : Real.exp (-v / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have e0 : 0 < Real.exp (-v / 2) := Real.exp_pos _
  have e2 : Real.exp (-2 * v) ≤ Real.exp (-v / 2) := Real.exp_le_exp.mpr (by linarith)
  have e3 : 1 - Real.exp (-2 * v) ≤ 2 * v := by
    have := Real.add_one_le_exp (-2 * v); linarith
  have e4 : Real.exp (-v / 2) - Real.exp (-2 * v) ≤ 2 * v := by linarith
  have hsplit : phiW f v = (f v - f 0) * Real.exp (-v / 2) + (f (-v) - f 0) * Real.exp (-v / 2) +
      2 * f 0 * (Real.exp (-v / 2) - Real.exp (-2 * v)) := by unfold phiW; ring
  rw [hsplit]
  have h1 : |(f v - f 0) * Real.exp (-v / 2)| ≤ D * v := by
    rw [abs_mul, abs_of_pos e0]
    have := hD v; rw [abs_of_nonneg hv] at this
    nlinarith [abs_nonneg (f v - f 0)]
  have h2 : |(f (-v) - f 0) * Real.exp (-v / 2)| ≤ D * v := by
    rw [abs_mul, abs_of_pos e0]
    have := hD (-v); rw [abs_neg, abs_of_nonneg hv] at this
    nlinarith [abs_nonneg (f (-v) - f 0)]
  have h3 : |2 * f 0 * (Real.exp (-v / 2) - Real.exp (-2 * v))| ≤ 4 * |f 0| * v := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr e2)]
    simp only [abs_two]
    nlinarith [abs_nonneg (f 0)]
  calc _ ≤ |(f v - f 0) * Real.exp (-v / 2)| + |(f (-v) - f 0) * Real.exp (-v / 2)| +
        |2 * f 0 * (Real.exp (-v / 2) - Real.exp (-2 * v))| := abs_add_three _ _ _
    _ ≤ D * v + D * v + 4 * |f 0| * v := by linarith
    _ = (2 * D + 4 * |f 0|) * v := by ring

lemma abs_phiW_le_exp (h : Admissible f a B) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ v : ℝ, 0 ≤ v → |phiW f v| ≤ M * Real.exp (-(1 / 2) * v) := by
  obtain ⟨M, hM0, hM⟩ := h.bounded
  refine ⟨4 * M, by positivity, fun v hv => ?_⟩
  have e0 : 0 < Real.exp (-v / 2) := Real.exp_pos _
  have e2 : Real.exp (-2 * v) ≤ Real.exp (-v / 2) := Real.exp_le_exp.mpr (by linarith)
  have he : Real.exp (-(1 / 2) * v) = Real.exp (-v / 2) := by congr 1; ring
  rw [he]
  unfold phiW
  calc _ ≤ |(f v + f (-v)) * Real.exp (-v / 2)| + |2 * f 0 * Real.exp (-2 * v)| := abs_sub _ _
    _ ≤ 2 * M * Real.exp (-v / 2) + 2 * M * Real.exp (-v / 2) := by
        gcongr
        · rw [abs_mul, abs_of_pos e0]
          exact mul_le_mul_of_nonneg_right ((abs_add_le _ _).trans (by linarith [hM v, hM (-v)])) e0.le
        · rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
          simp only [abs_two]
          have := hM 0
          nlinarith [Real.exp_pos (-2 * v)]
    _ = 4 * M * Real.exp (-v / 2) := by ring

lemma one_sub_exp_neg_two_ge {v : ℝ} (hv : 0 ≤ v) :
    2 * v / (1 + 2 * v) ≤ 1 - Real.exp (-2 * v) := by
  have h := Real.add_one_le_exp (2 * v)
  have hp : 0 < Real.exp (2 * v) := Real.exp_pos _
  have he : Real.exp (-2 * v) = (Real.exp (2 * v))⁻¹ := by rw [← Real.exp_neg]; congr 1; ring
  rw [he, div_le_iff₀ (by positivity)]
  have : (Real.exp (2 * v))⁻¹ * (1 + 2 * v) ≤ 1 := by
    rw [inv_mul_le_iff₀ hp]; linarith
  nlinarith

/-- The majorant of the summed series. -/
def Qf (f : ℝ → ℝ) (v : ℝ) : ℝ := |phiW f v| * (1 - Real.exp (-2 * v))⁻¹

lemma continuousOn_Qf (h : Admissible f a B) : ContinuousOn (Qf f) (Ioi 0) := by
  have hc : Continuous (phiW f) := by
    unfold phiW; have := h.continuous; fun_prop
  apply ContinuousOn.mul hc.abs.continuousOn
  apply ContinuousOn.inv₀ (by fun_prop)
  intro v hv
  have : Real.exp (-2 * v) < 1 := Real.exp_lt_one_iff.mpr (by have := mem_Ioi.mp hv; linarith)
  linarith

lemma Qf_le (h : Admissible f a B) :
    ∃ C : ℝ, ∀ v : ℝ, 0 < v → Qf f v ≤ C * Real.exp (-(1 / 2) * v) := by
  obtain ⟨K, hK0, hK⟩ := h.abs_phiW_le_lin
  obtain ⟨M, hM0, hM⟩ := h.abs_phiW_le_exp
  refine ⟨3 * K / 2 * Real.exp (1 / 2) + 3 * M / 2, fun v hv => ?_⟩
  have hden := one_sub_exp_neg_two_ge hv.le
  have hpos : 0 < 1 - Real.exp (-2 * v) := lt_of_lt_of_le (by positivity) hden
  have hE : 0 < Real.exp (-(1 / 2) * v) := Real.exp_pos _
  unfold Qf
  rcases le_or_gt v 1 with hv1 | hv1
  · -- near zero: `|φ| ≤ K v`, `1 − e^{−2v} ≥ 2v/3`
    have hd : 2 * v / 3 ≤ 1 - Real.exp (-2 * v) := by
      refine le_trans ?_ hden
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
    have hinv : (1 - Real.exp (-2 * v))⁻¹ ≤ 3 / (2 * v) := by
      rw [inv_le_comm₀ hpos (by positivity)]
      rw [inv_div]; exact hd
    have hb : |phiW f v| * (1 - Real.exp (-2 * v))⁻¹ ≤ 3 * K / 2 := by
      calc _ ≤ (K * v) * (3 / (2 * v)) :=
            mul_le_mul (hK v hv.le) hinv (by positivity) (by positivity)
        _ = 3 * K / 2 := by field_simp
    have hexp : 1 ≤ Real.exp (1 / 2) * Real.exp (-(1 / 2) * v) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
    have : 3 * K / 2 ≤ 3 * K / 2 * Real.exp (1 / 2) * Real.exp (-(1 / 2) * v) := by
      rw [mul_assoc]; nlinarith
    nlinarith [mul_nonneg hM0 hE.le]
  · -- away from zero: `|φ| ≤ M e^{−v/2}`, `1 − e^{−2v} ≥ 2/3`
    have hd : 2 / 3 ≤ 1 - Real.exp (-2 * v) := by
      refine le_trans ?_ hden
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
    have hinv : (1 - Real.exp (-2 * v))⁻¹ ≤ 3 / 2 := by
      rw [inv_le_comm₀ hpos (by positivity), show ((3 : ℝ) / 2)⁻¹ = 2 / 3 by norm_num]; linarith
    have hb : |phiW f v| * (1 - Real.exp (-2 * v))⁻¹ ≤ 3 * M / 2 * Real.exp (-(1 / 2) * v) := by
      calc _ ≤ (M * Real.exp (-(1 / 2) * v)) * (3 / 2) :=
            mul_le_mul (hM v hv.le) hinv (by positivity) (by positivity)
        _ = _ := by ring
    have : 0 ≤ 3 * K / 2 * Real.exp (1 / 2) * Real.exp (-(1 / 2) * v) := by positivity
    nlinarith

lemma integrableOn_Qf (h : Admissible f a B) : IntegrableOn (Qf f) (Ioi 0) := by
  obtain ⟨C, hC⟩ := h.Qf_le
  refine ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul C).mono'
    ((h.continuousOn_Qf).aestronglyMeasurable measurableSet_Ioi)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v hv => ?_))
  have hpos : 0 ≤ Qf f v := by
    unfold Qf
    have : Real.exp (-2 * v) < 1 := Real.exp_lt_one_iff.mpr (by have := mem_Ioi.mp hv; linarith)
    have : 0 < 1 - Real.exp (-2 * v) := by linarith
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hpos]
  exact hC v hv

/-- **The geometric sum.** `Σ_k ∫_{v>0} φ(v) e^{−2kv} dv = ∫_{v>0} φ(v)/(1 − e^{−2v}) dv`. -/
theorem tsum_term (h : Admissible f a B) :
    ∑' k : ℕ, ∫ v in Ioi (0 : ℝ), phiW f v * Real.exp (-2 * v) ^ k =
      ∫ v in Ioi (0 : ℝ), phiW f v * (1 - Real.exp (-2 * v))⁻¹ := by
  have hcφ : Continuous (phiW f) := by
    unfold phiW; have := h.continuous; fun_prop
  have hr : ∀ v ∈ Ioi (0 : ℝ), 0 ≤ Real.exp (-2 * v) ∧ Real.exp (-2 * v) < 1 := fun v hv =>
    ⟨(Real.exp_pos _).le, Real.exp_lt_one_iff.mpr (by have := mem_Ioi.mp hv; linarith)⟩
  have hbound : ∀ k : ℕ, ∀ v ∈ Ioi (0 : ℝ),
      ‖phiW f v * Real.exp (-2 * v) ^ k‖ ≤ Qf f v := by
    intro k v hv
    obtain ⟨h0, h1⟩ := hr v hv
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg h0 k)]
    unfold Qf
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc Real.exp (-2 * v) ^ k ≤ 1 := pow_le_one₀ h0 h1.le
      _ ≤ (1 - Real.exp (-2 * v))⁻¹ := by
        rw [le_inv_comm₀ one_pos (by linarith), inv_one]; linarith
  have hint : ∀ k : ℕ, Integrable (fun v => phiW f v * Real.exp (-2 * v) ^ k)
      (volume.restrict (Ioi 0)) := by
    intro k
    exact h.integrableOn_Qf.mono' (by fun_prop)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (hbound k)))
  have hsum : Summable (fun k : ℕ => ∫ v in Ioi (0 : ℝ), ‖phiW f v * Real.exp (-2 * v) ^ k‖) := by
    refine summable_of_sum_range_le (c := ∫ v in Ioi (0 : ℝ), Qf f v)
      (fun k => integral_nonneg fun v => norm_nonneg _) (fun N => ?_)
    rw [← integral_finsetSum _ (fun k _ => (hint k).norm)]
    refine setIntegral_mono_on (integrable_finsetSum _ (fun k _ => (hint k).norm))
      h.integrableOn_Qf measurableSet_Ioi (fun v hv => ?_)
    obtain ⟨h0, h1⟩ := hr v hv
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg h0 _)]
    rw [← Finset.mul_sum]
    unfold Qf
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [← tsum_geometric_of_lt_one h0 h1]
    exact (summable_geometric_of_lt_one h0 h1).sum_le_tsum _ (fun i _ => pow_nonneg h0 i)
  rw [integral_tsum_of_summable_integral_norm hint hsum]
  refine setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
  obtain ⟨h0, h1⟩ := hr v hv
  rw [tsum_mul_left, tsum_geometric_of_lt_one h0 h1]

lemma integrableOn_phiW_div (h : Admissible f a B) :
    IntegrableOn (fun v => phiW f v * (1 - Real.exp (-2 * v))⁻¹) (Ioi 0) := by
  have hcφ : Continuous (phiW f) := by
    unfold phiW; have := h.continuous; fun_prop
  refine h.integrableOn_Qf.mono' ?_
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v hv => ?_))
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    apply ContinuousOn.mul hcφ.continuousOn
    apply ContinuousOn.inv₀ (by fun_prop)
    intro v hv
    have : Real.exp (-2 * v) < 1 := Real.exp_lt_one_iff.mpr (by have := mem_Ioi.mp hv; linarith)
    linarith
  · have : Real.exp (-2 * v) < 1 := Real.exp_lt_one_iff.mpr (by have := mem_Ioi.mp hv; linarith)
    have : 0 < 1 - Real.exp (-2 * v) := by linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr this)]
    rfl

end Admissible

/-! ## (E) Matching Formal Conjectures' integrand -/

/-- Formal Conjectures' archimedean integrand. -/
def weilIntegrand (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (f x + f (-x) - 2 * Real.exp (-x / 2) * f 0) * Real.exp (x / 2) / (Real.exp x - Real.exp (-x))

lemma weilArchimedean_eq (f : ℝ → ℝ) :
    weilArchimedean f = (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant) * f 0 +
      ∫ x in Ioi (0 : ℝ), weilIntegrand f x := rfl

lemma phiW_div_eq (f : ℝ → ℝ) {v : ℝ} (hv : 0 < v) :
    phiW f v * (1 - Real.exp (-2 * v))⁻¹ =
      weilIntegrand f v + 2 * f 0 * (Real.exp (-v) / (1 + Real.exp (-v))) := by
  obtain ⟨y, hy⟩ : ∃ y, y = Real.exp (v / 2) := ⟨_, rfl⟩
  have hy1 : 1 < y := by rw [hy]; exact Real.one_lt_exp_iff.mpr (by linarith)
  have e1 : Real.exp (-v / 2) = y⁻¹ := by rw [hy, ← Real.exp_neg]; congr 1; ring
  have e2 : Real.exp v = y ^ 2 := by
    rw [hy, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e3 : Real.exp (-v) = (y ^ 2)⁻¹ := by rw [Real.exp_neg, e2]
  have e4 : Real.exp (-2 * v) = (y ^ 4)⁻¹ := by
    rw [show -2 * v = -(((4 : ℕ) : ℝ) * (v / 2)) by push_cast; ring, Real.exp_neg,
      Real.exp_nat_mul, ← hy]
  have hy0 : 0 < y := by linarith
  have h4 : y ^ 4 - 1 ≠ 0 := by
    have : 1 < y ^ 4 := one_lt_pow₀ hy1 (by norm_num)
    linarith
  have h2 : y ^ 2 + 1 ≠ 0 := by positivity
  have h2' : y ^ 2 - 1 ≠ 0 := by
    have : 1 < y ^ 2 := one_lt_pow₀ hy1 (by norm_num)
    linarith
  unfold phiW weilIntegrand
  rw [e1, e2, e3, e4, ← hy]
  have hd1 : 1 - (y ^ 4)⁻¹ = (y ^ 4 - 1) / y ^ 4 := by field_simp
  have hd2 : y ^ 2 - (y ^ 2)⁻¹ = (y ^ 4 - 1) / y ^ 2 := by field_simp
  have hd3 : 1 + (y ^ 2)⁻¹ = (y ^ 2 + 1) / y ^ 2 := by field_simp
  rw [hd1, hd2, hd3]
  have hfac : y ^ 4 - 1 = (y ^ 2 - 1) * (y ^ 2 + 1) := by ring
  field_simp
  rw [hfac]
  ring

lemma integral_exp_div_one_add : ∫ v in Ioi (0 : ℝ), Real.exp (-v) / (1 + Real.exp (-v)) =
    Real.log 2 := by
  have hF : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun v => -Real.log (1 + Real.exp (-v)))
      (Real.exp (-x) / (1 + Real.exp (-x))) x := by
    intro x _
    have h1 : HasDerivAt (fun v => 1 + Real.exp (-v)) (-Real.exp (-x)) x := by
      have := ((hasDerivAt_neg x).exp).const_add 1
      simpa using this
    have h2 := (h1.log (by positivity)).neg
    convert h2 using 1
    field_simp
  have hqc : Continuous (fun v : ℝ => Real.exp (-v) / (1 + Real.exp (-v))) :=
    (Real.continuous_exp.comp continuous_neg).div
      (continuous_const.add (Real.continuous_exp.comp continuous_neg)) (fun v => by positivity)
  have hint : IntegrableOn (fun v => Real.exp (-v) / (1 + Real.exp (-v))) (Ioi 0) := by
    refine (exp_neg_integrableOn_Ioi 0 one_pos).mono'
      hqc.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v _ => ?_))
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_le_iff₀ (by positivity), neg_mul, one_mul]
    nlinarith [Real.exp_pos (-v)]
  have hlim : Tendsto (fun v => -Real.log (1 + Real.exp (-v))) atTop (𝓝 (-Real.log (1 + 0))) := by
    apply Tendsto.neg
    apply ((Real.continuousAt_log (by norm_num)).tendsto).comp
    exact tendsto_const_nhds.add Real.tendsto_exp_neg_atTop_nhds_zero
  have hFc : Continuous (fun v : ℝ => -Real.log (1 + Real.exp (-v))) :=
    ((continuous_const.add (Real.continuous_exp.comp continuous_neg)).log
      (fun v => (by positivity : (0 : ℝ) < 1 + Real.exp (-v)).ne')).neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hFc.continuousWithinAt hF hint hlim]
  simp
  norm_num

lemma integral_phiW_div {f : ℝ → ℝ} {a B : ℝ} (h : Admissible f a B) :
    ∫ v in Ioi (0 : ℝ), phiW f v * (1 - Real.exp (-2 * v))⁻¹ =
      (∫ v in Ioi (0 : ℝ), weilIntegrand f v) + 2 * f 0 * Real.log 2 := by
  have hq : IntegrableOn (fun v => 2 * f 0 * (Real.exp (-v) / (1 + Real.exp (-v)))) (Ioi 0) := by
    have hqc : Continuous (fun v : ℝ => 2 * f 0 * (Real.exp (-v) / (1 + Real.exp (-v)))) :=
      continuous_const.mul ((Real.continuous_exp.comp continuous_neg).div
        (continuous_const.add (Real.continuous_exp.comp continuous_neg)) (fun v => by positivity))
    refine ((exp_neg_integrableOn_Ioi 0 one_pos).const_mul (2 * |f 0|)).mono'
      hqc.aestronglyMeasurable ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v _ => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_mul, show |(2 : ℝ)| = 2 by norm_num,
      abs_of_pos (by positivity : 0 < Real.exp (-v) / (1 + Real.exp (-v)))]
    refine le_trans (mul_le_mul_of_nonneg_left (div_le_self (Real.exp_pos _).le ?_)
      (by positivity)) (le_of_eq ?_)
    · linarith [Real.exp_pos (-v)]
    · ring_nf
  have hW : IntegrableOn (weilIntegrand f) (Ioi 0) := by
    refine (h.integrableOn_phiW_div.sub hq).congr_fun (fun v hv => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]
    rw [phiW_div_eq f (mem_Ioi.mp hv)]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun v hv => phiW_div_eq f (mem_Ioi.mp hv)),
    integral_add hW hq, integral_const_mul, integral_exp_div_one_add]

/-! ## (F) The identity -/

/-- **Formal Conjectures' `weilArchimedean` is minus hp-proof's standard archimedean term**, for
every real smooth `f` vanishing for `|u| > B`, on any window `a > B ≥ 0`. -/
theorem standardArchimedean_eq_neg_weilArchimedean {f : ℝ → ℝ} {a B : ℝ}
    (h : Admissible f a B) :
    FleetStandardExplicitFormula.standardArchimedean a (cF f) =
      ((-weilArchimedean f : ℝ) : ℂ) := by
  rw [FleetSeparatedExplicitFormula.standardArchimedean_eq_separated h.isTestFn h.supp]
  have hdig : ∀ t : ℝ, TestFunctions.hfun a (cF f) (t : ℂ) *
      (FleetSeparatedExplicitFormula.digammaWeight t : ℂ) =
      TestFunctions.hfun a (cF f) (t : ℂ) * (-(Real.eulerMascheroniConstant : ℂ)) -
        TestFunctions.hfun a (cF f) (t : ℂ) * ((∑' k : ℕ, dk k t : ℝ) : ℂ) := by
    intro t; rw [digammaWeight_eq]; push_cast; ring
  have hint2 : Integrable (fun t : ℝ => TestFunctions.hfun a (cF f) (t : ℂ) *
      ((∑' k : ℕ, dk k t : ℝ) : ℂ)) := by
    refine ((h.integrable_hfun.mul_const (-(Real.eulerMascheroniConstant : ℂ))).sub
      (FleetSeparatedExplicitFormula.integrable_digamma h.isTestFn)).congr
      (Eventually.of_forall fun t => ?_)
    simp only [Pi.sub_apply]
    rw [hdig]; ring
  simp_rw [hdig]
  rw [integral_sub (h.integrable_hfun.mul_const _) hint2, integral_mul_const,
    FleetFourierNormalization.integral_hfun h.isTestFn h.supp, integral_hfun_mul_tsum h]
  have hJ : (1 / (2 * (Real.pi : ℂ))) * ∑' k : ℕ,
      ∫ t : ℝ, TestFunctions.hfun a (cF f) (t : ℂ) * (dk k t : ℂ) =
      (((∫ v in Ioi (0 : ℝ), weilIntegrand f v) + 2 * f 0 * Real.log 2 : ℝ) : ℂ) := by
    rw [← tsum_mul_left]
    simp_rw [Admissible.term_k h]
    rw [← Complex.ofReal_tsum, Admissible.tsum_term h, integral_phiW_div h]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [mul_sub, hJ, weilArchimedean_eq,
    Real.log_mul (by norm_num) Real.pi_ne_zero,
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  simp only [cF]
  push_cast
  field_simp
  ring


end FleetWeilCriterion
