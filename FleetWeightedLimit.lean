import FleetDualConverse
import Mathlib

/-!
# Weighted stage solutions have an entire limit (step 1–2 of `CONVERSE.md`, weighted atoms)

Suppose that for one budget `M` every stage `n` has a weighted solution (`FleetDualConverse.WeightedFeasible`)
with tolerance `ε n → 0`. The weighted atoms `a_n` are pushed to finite measures
`m_n = Σ a_n(x)(1+x²)⁻¹ δ_x` on the one-point compactification `OnePoint ℝ`, of mass `≤ M`.
Finite measures of bounded mass on a compact space form a compact set (Mathlib's Prokhorov
theorem), so the sequence has a cluster point `m`. For every rational `q`, the bounded continuous
test `x ↦ √π e^{-(x−q)²/4}(1+x²)` (zero at `∞`) has integral `→ R q` along the sequence, so its
integral against `m` is `R q`. Mass escaping to `∞` is invisible to every test.

`exists_entire_realization`: there is an entire `F` with `F q = R q` for every rational `q` and
`‖F(iy)‖ ≤ C e^{y²/4}` for every real `y`; namely `F z = ∫ √π e^{-(x−z)²/4}(1+x²) dm`.
No integer constraint on the atoms is used.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set MeasureTheory
open scoped OnePoint BoundedContinuousFunction

namespace FleetWeightedLimit

/-! ## Gaussian decay -/

/-- `(1+|x|)³ e^{A|x| − x²/4} → 0` at infinity. -/
lemma decay (A : ℝ) :
    Tendsto (fun x : ℝ => (1 + |x|) ^ 3 * Real.exp (A * |x| - x ^ 2 / 4)) (cocompact ℝ) (𝓝 0) := by
  have habs : Tendsto (fun x : ℝ => |x|) (cocompact ℝ) atTop := by
    exact (tendsto_norm_cocompact_atTop (E := ℝ)).congr (fun x => Real.norm_eq_abs x)
  have hg : Tendsto (fun u : ℝ => (1 + u) ^ 3 * Real.exp (A * u - u ^ 2 / 4)) atTop (𝓝 0) := by
    have h8 : Tendsto (fun u : ℝ => 8 * (u ^ 3 * Real.exp (-u))) atTop (𝓝 0) := by
      simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).const_mul 8
    refine squeeze_zero' ((eventually_ge_atTop 0).mono (fun u hu => by positivity)) ?_ h8
    filter_upwards [eventually_ge_atTop (max 1 (4 * (|A| + 1)))] with u hu
    have hu1 : 1 ≤ u := (le_max_left _ _).trans hu
    have hu2 : 4 * (|A| + 1) ≤ u := (le_max_right _ _).trans hu
    have hexp : Real.exp (A * u - u ^ 2 / 4) ≤ Real.exp (-u) := by
      apply Real.exp_le_exp.2
      have : A * u ≤ |A| * u := mul_le_mul_of_nonneg_right (le_abs_self A) (by linarith)
      nlinarith
    have hp : (1 + u) ^ 3 ≤ 8 * u ^ 3 := by
      have : 1 + u ≤ 2 * u := by linarith
      calc (1 + u) ^ 3 ≤ (2 * u) ^ 3 := pow_le_pow_left₀ (by linarith) this 3
        _ = 8 * u ^ 3 := by ring
    calc (1 + u) ^ 3 * Real.exp (A * u - u ^ 2 / 4) ≤ 8 * u ^ 3 * Real.exp (-u) :=
          mul_le_mul hp hexp (by positivity) (by positivity)
      _ = 8 * (u ^ 3 * Real.exp (-u)) := by ring
  have := hg.comp habs
  refine this.congr (fun x => ?_)
  simp only [Function.comp_apply, sq_abs]

/-- A continuous function vanishing at infinity is bounded. -/
lemma exists_bound_of_tendsto {f : ℝ → ℝ} (hf : Continuous f)
    (h0 : Tendsto f (cocompact ℝ) (𝓝 0)) : ∃ C : ℝ, ∀ x, |f x| ≤ C := by
  obtain ⟨K, hK, hout⟩ : ∃ K : Set ℝ, IsCompact K ∧ ∀ x ∉ K, |f x| ≤ 1 := by
    have hev : ∀ᶠ x in cocompact ℝ, |f x| ≤ 1 := by
      have := (h0.abs).eventually (ge_mem_nhds (by norm_num : |(0:ℝ)| < 1))
      simpa using this
    obtain ⟨K, hK, hKs⟩ := (Filter.mem_cocompact).1 hev
    exact ⟨K, hK, fun x hx => hKs hx⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 1, fun x => ?_⟩
  by_cases hx : x ∈ K
  · have := hC x hx; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  · exact (hout x hx).trans (le_max_right _ _)

/-- Norm of the shifted Gaussian at a complex centre `z`, `‖z‖ ≤ A`. -/
lemma norm_cexp_shift_le {A : ℝ} {z : ℂ} (hz : ‖z‖ ≤ A) (x : ℝ) :
    ‖cexp (-((x : ℂ) - z) ^ 2 / 4)‖ ≤ Real.exp (A ^ 2 / 4) * Real.exp ((A / 2) * |x| - x ^ 2 / 4) := by
  rw [Complex.norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have hre : (-((x : ℂ) - z) ^ 2 / 4).re = (-(x - z.re) ^ 2 + z.im ^ 2) / 4 := by
    simp [sq, Complex.mul_re, Complex.div_re]
    ring
  rw [hre]
  have ha : |z.re| ≤ A := (Complex.abs_re_le_norm z).trans hz
  have hb : z.im ^ 2 ≤ A ^ 2 := by
    have h1 := (Complex.abs_im_le_norm z).trans hz
    have h0 : 0 ≤ A := (norm_nonneg z).trans hz
    nlinarith [abs_nonneg z.im, sq_abs z.im]
  have hx : z.re * x ≤ A * |x| := by
    calc z.re * x ≤ |z.re * x| := le_abs_self _
      _ = |z.re| * |x| := abs_mul _ _
      _ ≤ A * |x| := mul_le_mul_of_nonneg_right ha (abs_nonneg x)
  nlinarith [sq_nonneg z.re]

/-- `1 + x² ≤ (1+|x|)³`. -/
lemma one_add_sq_le (x : ℝ) : 1 + x ^ 2 ≤ (1 + |x|) ^ 3 := by
  have h0 := abs_nonneg x
  have : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  nlinarith [mul_nonneg h0 (mul_nonneg h0 h0)]

/-! ## Extension by zero to the one-point compactification -/

/-- Extension by `0` at `∞`. -/
def ext {β : Type*} [Zero β] (f : ℝ → β) : OnePoint ℝ → β := fun e => e.elim 0 f

@[simp] lemma ext_coe {β : Type*} [Zero β] (f : ℝ → β) (x : ℝ) : ext f (x : OnePoint ℝ) = f x := rfl
@[simp] lemma ext_infty {β : Type*} [Zero β] (f : ℝ → β) : ext f ∞ = 0 := rfl

lemma continuous_ext {β : Type*} [TopologicalSpace β] [Zero β] {f : ℝ → β} (hf : Continuous f)
    (h0 : Tendsto f (cocompact ℝ) (𝓝 0)) : Continuous (ext f) := by
  rw [continuous_iff_continuousAt]
  intro e
  induction e using OnePoint.rec with
  | infty =>
    rw [OnePoint.continuousAt_infty', coclosedCompact_eq_cocompact]
    exact h0
  | coe x =>
    rw [OnePoint.continuousAt_coe]
    exact hf.continuousAt

/-- Borel structure on `OnePoint ℝ` (local to this file). -/
def oneMeas : MeasurableSpace (OnePoint ℝ) := borel _
attribute [local instance] oneMeas
lemma oneBorel : BorelSpace (OnePoint ℝ) := ⟨rfl⟩
attribute [local instance] oneBorel

/-! ## The test functions -/

/-- Real test: `√π e^{-(x−q)²/4} (1+x²)`. -/
def gq (q : ℝ) (x : ℝ) : ℝ := Real.sqrt Real.pi * Real.exp (-(x - q) ^ 2 / 4) * (1 + x ^ 2)

/-- Complex test: `√π e^{-(x−z)²/4} (1+x²)`. -/
def kf (z : ℂ) (x : ℝ) : ℂ := (Real.sqrt Real.pi : ℂ) * cexp (-((x : ℂ) - z) ^ 2 / 4) * (1 + (x : ℂ) ^ 2)

/-- Its `z`-derivative. -/
def kf' (z : ℂ) (x : ℝ) : ℂ := kf z x * (((x : ℂ) - z) / 2)

lemma kf_ofReal (q x : ℝ) : kf (q : ℂ) x = ((gq q x : ℝ) : ℂ) := by
  simp only [kf, gq]
  push_cast
  ring_nf

lemma continuous_kf (z : ℂ) : Continuous (kf z) := by unfold kf; fun_prop

lemma continuous_kf' (z : ℂ) : Continuous (kf' z) := by unfold kf' kf; fun_prop

/-- Uniform bound: for `‖z‖ ≤ A`, `‖kf z x‖ ≤ √π e^{A²/4} D_A(x)`. -/
lemma norm_kf_le {A : ℝ} {z : ℂ} (hz : ‖z‖ ≤ A) (x : ℝ) :
    ‖kf z x‖ ≤ Real.sqrt Real.pi * Real.exp (A ^ 2 / 4) *
      ((1 + |x|) ^ 3 * Real.exp ((A / 2) * |x| - x ^ 2 / 4)) := by
  have h1 := norm_cexp_shift_le hz x
  have h2 : ‖(1 + (x : ℂ) ^ 2)‖ = 1 + x ^ 2 := by
    rw [show (1 + (x : ℂ) ^ 2) = ((1 + x ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h3 := one_add_sq_le x
  simp only [kf, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), h2]
  have hpos : 0 ≤ Real.exp (A ^ 2 / 4) * Real.exp ((A / 2) * |x| - x ^ 2 / 4) := by positivity
  calc Real.sqrt Real.pi * ‖cexp (-((x : ℂ) - z) ^ 2 / 4)‖ * (1 + x ^ 2)
      ≤ Real.sqrt Real.pi * (Real.exp (A ^ 2 / 4) * Real.exp ((A / 2) * |x| - x ^ 2 / 4)) *
          (1 + |x|) ^ 3 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)) h3 (by positivity)
          (by positivity)
    _ = _ := by ring

lemma norm_kf'_le {A : ℝ} {z : ℂ} (hz : ‖z‖ ≤ A) (x : ℝ) :
    ‖kf' z x‖ ≤ Real.sqrt Real.pi * Real.exp (A ^ 2 / 4) * ((1 + A) / 2) *
      ((1 + |x|) ^ 4 * Real.exp ((A / 2) * |x| - x ^ 2 / 4)) := by
  have h1 := norm_kf_le hz x
  have hA : 0 ≤ A := (norm_nonneg z).trans hz
  have h2 : ‖((x : ℂ) - z) / 2‖ ≤ ((1 + A) / 2) * (1 + |x|) := by
    rw [norm_div, Complex.norm_two]
    have : ‖(x : ℂ) - z‖ ≤ |x| + A := by
      calc ‖(x : ℂ) - z‖ ≤ ‖(x : ℂ)‖ + ‖z‖ := norm_sub_le _ _
        _ ≤ |x| + A := by rw [Complex.norm_real, Real.norm_eq_abs]; linarith
    have h0 := abs_nonneg x
    have : |x| + A ≤ (1 + A) * (1 + |x|) := by nlinarith
    linarith
  simp only [kf', norm_mul]
  calc ‖kf z x‖ * ‖((x : ℂ) - z) / 2‖
      ≤ (Real.sqrt Real.pi * Real.exp (A ^ 2 / 4) *
          ((1 + |x|) ^ 3 * Real.exp ((A / 2) * |x| - x ^ 2 / 4))) * (((1 + A) / 2) * (1 + |x|)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma tendsto_D (A : ℝ) (n : ℕ) (hn : n ≤ 4) :
    Tendsto (fun x : ℝ => (1 + |x|) ^ n * Real.exp ((A / 2) * |x| - x ^ 2 / 4)) (cocompact ℝ) (𝓝 0) := by
  -- `(1+|x|)^n e^{…} ≤ (1+|x|)^3 e^{(A/2+1)|x| - x²/4}` since `1+|x| ≤ e^{|x|}`
  have hd := decay (A / 2 + 1)
  refine squeeze_zero' (Eventually.of_forall (fun x => by positivity)) ?_ hd
  refine Eventually.of_forall (fun x => ?_)
  have h0 := abs_nonneg x
  have h1 : 1 ≤ 1 + |x| := by linarith
  have hex : 1 + |x| ≤ Real.exp |x| := by linarith [Real.add_one_le_exp |x|]
  have hpow : (1 + |x|) ^ n ≤ (1 + |x|) ^ 4 := pow_le_pow_right₀ h1 hn
  have e1 : Real.exp ((A / 2 + 1) * |x| - x ^ 2 / 4) =
      Real.exp |x| * Real.exp ((A / 2) * |x| - x ^ 2 / 4) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e1]
  have : (1 + |x|) ^ 4 = (1 + |x|) ^ 3 * (1 + |x|) := by ring
  calc (1 + |x|) ^ n * Real.exp ((A / 2) * |x| - x ^ 2 / 4)
      ≤ (1 + |x|) ^ 4 * Real.exp ((A / 2) * |x| - x ^ 2 / 4) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
    _ ≤ (1 + |x|) ^ 3 * (Real.exp |x| * Real.exp ((A / 2) * |x| - x ^ 2 / 4)) := by
        rw [this, mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hex (by positivity))
          (by positivity)

lemma tendsto_kf (z : ℂ) : Tendsto (kf z) (cocompact ℝ) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := (tendsto_D ‖z‖ 3 (by norm_num)).const_mul (Real.sqrt Real.pi * Real.exp (‖z‖ ^ 2 / 4))
  rw [mul_zero] at h
  exact squeeze_zero (fun x => norm_nonneg _) (fun x => norm_kf_le le_rfl x) h

lemma tendsto_gq (q : ℝ) : Tendsto (gq q) (cocompact ℝ) (𝓝 0) := by
  have h := tendsto_kf (q : ℂ)
  have : (kf (q : ℂ)) = fun x => ((gq q x : ℝ) : ℂ) := funext (kf_ofReal q)
  rw [this] at h
  have h2 := (Complex.continuous_re.tendsto 0).comp h
  rw [Complex.zero_re] at h2
  exact h2.congr (fun x => by simp)

lemma continuous_gq (q : ℝ) : Continuous (gq q) := by unfold gq; fun_prop

lemma tendsto_kf' (z : ℂ) : Tendsto (kf' z) (cocompact ℝ) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := (tendsto_D ‖z‖ 4 le_rfl).const_mul
    (Real.sqrt Real.pi * Real.exp (‖z‖ ^ 2 / 4) * ((1 + ‖z‖) / 2))
  rw [mul_zero] at h
  exact squeeze_zero (fun x => norm_nonneg _) (fun x => norm_kf'_le le_rfl x) h

/-- The bounded continuous test on `OnePoint ℝ`. -/
def gB (q : ℝ) : OnePoint ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨ext (gq q), continuous_ext (continuous_gq q) (tendsto_gq q)⟩

lemma gB_apply (q : ℝ) (e : OnePoint ℝ) : gB q e = ext (gq q) e := rfl

/-! ## Weighted atoms as finite measures -/

/-- `Σ a(x)(1+x²)⁻¹ δ_x`. -/
def wmeas (a : ℝ →₀ ℝ) : Measure (OnePoint ℝ) :=
  ∑ x ∈ a.support, ENNReal.ofReal (a x * FleetDualConverse.w x) • Measure.dirac (x : OnePoint ℝ)

lemma wmeas_univ (a : ℝ →₀ ℝ) :
    wmeas a univ = ∑ x ∈ a.support, ENNReal.ofReal (a x * FleetDualConverse.w x) := by
  simp [wmeas]

instance (a : ℝ →₀ ℝ) : IsFiniteMeasure (wmeas a) :=
  ⟨by rw [wmeas_univ]; exact ENNReal.sum_lt_top.2 (fun x _ => ENNReal.ofReal_lt_top)⟩

lemma integral_wmeas (a : ℝ →₀ ℝ) (ha : ∀ x, 0 ≤ a x) (g : OnePoint ℝ →ᵇ ℝ) :
    ∫ e, g e ∂(wmeas a) = ∑ x ∈ a.support, a x * FleetDualConverse.w x * g (x : OnePoint ℝ) := by
  unfold wmeas
  rw [integral_finset_sum_measure (fun x _ => ?_)]
  · refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [integral_smul_measure, integral_dirac' _ _ g.continuous.stronglyMeasurable,
      ENNReal.toReal_ofReal (mul_nonneg (ha x) (FleetDualConverse.w_pos x).le), smul_eq_mul]
  · exact (g.integrable _).smul_measure ENNReal.ofReal_ne_top

lemma wmeas_real_univ (a : ℝ →₀ ℝ) (ha : ∀ x, 0 ≤ a x) :
    (wmeas a univ).toReal = FleetDualConverse.massMap a := by
  rw [wmeas_univ, FleetDualConverse.mass_eq, ENNReal.toReal_sum (fun x _ => ENNReal.ofReal_ne_top)]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [ENNReal.toReal_ofReal (mul_nonneg (ha x) (FleetDualConverse.w_pos x).le)]

/-- The finite measure of a weight. -/
def wfin (a : ℝ →₀ ℝ) : FiniteMeasure (OnePoint ℝ) := ⟨wmeas a, inferInstance⟩

lemma traceMap_eq (n : ℕ) (a : ℝ →₀ ℝ) (q : FleetDualConverse.S n) :
    FleetDualConverse.traceMap n a q = ∑ x ∈ a.support, a x * FleetDualConverse.G x q.1 := by
  simp only [FleetDualConverse.traceMap, Finsupp.linearCombination_apply, Finsupp.sum,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

lemma integral_wfin_gB (a : ℝ →₀ ℝ) (ha : ∀ x, 0 ≤ a x) (q : ℚ) :
    ∫ e, gB q e ∂(wfin a : Measure (OnePoint ℝ)) = ∑ x ∈ a.support, a x * FleetDualConverse.G x q := by
  change ∫ e, gB q e ∂(wmeas a) = _
  rw [integral_wmeas a ha]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [gB_apply, ext_coe]
  simp only [gq, FleetDualConverse.G, FleetDualConverse.w]
  have : (1 + x ^ 2) ≠ 0 := by positivity
  field_simp

/-! ## The limit measure -/

/-- **Step 1.** Weighted solutions at every stage with one budget and tolerance `→ 0` give a finite
measure on `OnePoint ℝ` realizing `R` at every rational centre through the tests `gB q`. -/
theorem exists_limit (R : ℚ → ℝ) {M : ℝ} {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hf : ∀ n, FleetDualConverse.WeightedFeasible R M (ε n) n) :
    ∃ m : FiniteMeasure (OnePoint ℝ), ∀ q : ℚ, ∫ e, gB q e ∂(m : Measure (OnePoint ℝ)) = R q := by
  choose a ha0 hmass hres using hf
  set ms : ℕ → FiniteMeasure (OnePoint ℝ) := fun n => wfin (a n) with hms
  have hK := isCompact_setOfPred_finiteMeasure_le_of_compactSpace (OnePoint ℝ) M.toNNReal
  have hmem : ∀ n, ms n ∈ {μ : FiniteMeasure (OnePoint ℝ) | μ.mass ≤ M.toNNReal} := by
    intro n
    simp only [mem_setOf_eq, hms]
    have h1 : ((wfin (a n)).mass : ℝ) = FleetDualConverse.massMap (a n) := by
      rw [← wmeas_real_univ (a n) (ha0 n)]
      have h := congrArg ENNReal.toReal (FiniteMeasure.ennreal_mass (μ := wfin (a n)))
      rw [ENNReal.coe_toReal] at h
      rw [h]; rfl
    rw [← NNReal.coe_le_coe, h1]
    exact (hmass n).trans (Real.le_coe_toNNReal M)
  obtain ⟨m, -, hm⟩ := hK.exists_mapClusterPt (f := atTop) (u := ms)
    (by rw [Filter.le_principal_iff]; exact Filter.mem_map.2 (Filter.Eventually.of_forall hmem))
  refine ⟨m, fun q => ?_⟩
  -- the test functional is continuous
  have hcont : Continuous (fun μ : FiniteMeasure (OnePoint ℝ) =>
      ∫ e, gB q e ∂(μ : Measure (OnePoint ℝ))) := by
    rw [continuous_iff_continuousAt]
    intro μ
    exact (FiniteMeasure.tendsto_iff_forall_integral_tendsto.1 tendsto_id) (gB q)
  -- along the sequence it converges to `R q`
  have hlim : Tendsto (fun n => ∫ e, gB q e ∂(ms n : Measure (OnePoint ℝ))) atTop (𝓝 (R q)) := by
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨N₁, hN₁⟩ := (Filter.eventually_atTop).1 (FleetRationalBanks.eventually_mem_bank q)
    obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 hε (η / 2) (by positivity)
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have hq := hN₁ n ((le_max_left _ _).trans hn)
    have he := hN₂ n ((le_max_right _ _).trans hn)
    rw [Real.dist_eq, sub_zero] at he
    have hr := hres n ⟨q, hq⟩
    rw [traceMap_eq] at hr
    simp only [hms]
    rw [integral_wfin_gB (a n) (ha0 n) q, Real.dist_eq]
    calc _ ≤ ε n := hr
      _ ≤ |ε n| := le_abs_self _
      _ < η := by linarith
  have hc := hm.continuousAt_comp hcont.continuousAt
  have hc' : ClusterPt (∫ e, gB q e ∂(m : Measure (OnePoint ℝ))) (𝓝 (R q)) :=
    ClusterPt.mono hc hlim
  exact eq_of_nhds_neBot hc'

/-! ## The entire function of the limit -/

/-- `F z = ∫ √π e^{-(x−z)²/4}(1+x²) dm`. -/
def Fm (m : FiniteMeasure (OnePoint ℝ)) (z : ℂ) : ℂ := ∫ e, ext (kf z) e ∂(m : Measure (OnePoint ℝ))

lemma continuous_ext_kf (z : ℂ) : Continuous (ext (kf z)) :=
  continuous_ext (continuous_kf z) (tendsto_kf z)

lemma continuous_ext_kf' (z : ℂ) : Continuous (ext (kf' z)) :=
  continuous_ext (continuous_kf' z) (tendsto_kf' z)

lemma hasDerivAt_kf (x : ℝ) (z : ℂ) : HasDerivAt (fun w => kf w x) (kf' z x) z := by
  have h1 : HasDerivAt (fun w : ℂ => -((x : ℂ) - w) ^ 2 / 4) (((x : ℂ) - z) / 2) z := by
    have := ((hasDerivAt_id z).const_sub (x : ℂ)).pow 2
    have := (this.neg).div_const 4
    convert this using 1
    · funext w; simp
    · simp; ring
  have h2 := (h1.cexp.const_mul (Real.sqrt Real.pi : ℂ)).mul_const (1 + (x : ℂ) ^ 2)
  convert h2 using 1
  · funext w; rfl
  show kf z x * (((x : ℂ) - z) / 2) = _
  unfold kf
  ring

theorem differentiable_Fm (m : FiniteMeasure (OnePoint ℝ)) : Differentiable ℂ (Fm m) := by
  intro z₁
  set A : ℝ := ‖z₁‖ + 1
  obtain ⟨C, hC⟩ := exists_bound_of_tendsto
    (f := fun x : ℝ => (1 + |x|) ^ 4 * Real.exp ((A / 2) * |x| - x ^ 2 / 4)) (by fun_prop)
    (tendsto_D A 4 le_rfl)
  set B : ℝ := Real.sqrt Real.pi * Real.exp (A ^ 2 / 4) * ((1 + A) / 2) * C
  have hball : ∀ z ∈ Metric.ball z₁ 1, ‖z‖ ≤ A := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    calc ‖z‖ = ‖(z - z₁) + z₁‖ := by ring_nf
      _ ≤ ‖z - z₁‖ + ‖z₁‖ := norm_add_le _ _
      _ ≤ A := by simp only [A]; linarith
  have hbound : ∀ e : OnePoint ℝ, ∀ z ∈ Metric.ball z₁ 1, ‖ext (kf' z) e‖ ≤ B := by
    intro e z hz
    have hBnn : 0 ≤ B := by
      have := (abs_nonneg _).trans (hC 0)
      positivity
    induction e using OnePoint.rec with
    | infty => simpa using hBnn
    | coe x =>
      rw [ext_coe]
      refine (norm_kf'_le (hball z hz) x).trans ?_
      have := hC x
      rw [abs_of_nonneg (by positivity)] at this
      exact mul_le_mul_of_nonneg_left this (by positivity)
  have hint : ∀ z, Integrable (ext (kf z)) (m : Measure (OnePoint ℝ)) := by
    intro z
    obtain ⟨C', hC'⟩ := (isCompact_univ (X := OnePoint ℝ)).exists_bound_of_continuousOn
      (continuous_ext_kf z).continuousOn
    exact Integrable.of_bound (continuous_ext_kf z).aestronglyMeasurable C'
      (Eventually.of_forall (fun e => hC' e (mem_univ _)))
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (m : Measure (OnePoint ℝ)))
    (F := fun z e => ext (kf z) e) (F' := fun z e => ext (kf' z) e) (x₀ := z₁)
    (Metric.ball_mem_nhds z₁ one_pos)
    (Eventually.of_forall (fun z => (continuous_ext_kf z).aestronglyMeasurable)) (hint z₁)
    (continuous_ext_kf' z₁).aestronglyMeasurable (bound := fun _ => B)
    (Eventually.of_forall (fun e z hz => hbound e z hz)) (integrable_const B)
    (Eventually.of_forall (fun e z _ => by
      induction e using OnePoint.rec with
      | infty => simpa using hasDerivAt_const z (0 : ℂ)
      | coe x => simpa using hasDerivAt_kf x z))
  exact hd.2.differentiableAt

lemma Fm_rat (m : FiniteMeasure (OnePoint ℝ)) (q : ℚ) :
    Fm m (q : ℂ) = ((∫ e, gB q e ∂(m : Measure (OnePoint ℝ)) : ℝ) : ℂ) := by
  unfold Fm
  rw [← integral_complex_ofReal]
  congr 1
  funext e
  induction e using OnePoint.rec with
  | infty => rw [gB_apply, ext_infty, ext_infty]; simp
  | coe x =>
    rw [ext_coe, gB_apply, ext_coe]
    have := kf_ofReal (q : ℝ) x
    push_cast at this ⊢
    exact this

lemma norm_kf_imag (y x : ℝ) :
    ‖kf ((y : ℂ) * I) x‖ ≤ 4 * Real.sqrt Real.pi * Real.exp (y ^ 2 / 4) := by
  have h1 : ‖cexp (-((x : ℂ) - (y : ℂ) * I) ^ 2 / 4)‖ = Real.exp (y ^ 2 / 4) * Real.exp (-x ^ 2 / 4) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    congr 1
    simp [sq, Complex.mul_re, Complex.div_re]
    ring
  have h2 : ‖(1 + (x : ℂ) ^ 2)‖ = 1 + x ^ 2 := by
    rw [show (1 + (x : ℂ) ^ 2) = ((1 + x ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h3 : Real.exp (-x ^ 2 / 4) * (1 + x ^ 2) ≤ 4 := by
    have he : 1 + x ^ 2 / 4 ≤ Real.exp (x ^ 2 / 4) := by linarith [Real.add_one_le_exp (x ^ 2 / 4)]
    have hm : Real.exp (-x ^ 2 / 4) * Real.exp (x ^ 2 / 4) = 1 := by
      rw [← Real.exp_add, show -x ^ 2 / 4 + x ^ 2 / 4 = 0 by ring, Real.exp_zero]
    have hpos := Real.exp_pos (-x ^ 2 / 4)
    nlinarith
  simp only [kf, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    h1, h2]
  have hs := Real.sqrt_nonneg Real.pi
  have he := Real.exp_pos (y ^ 2 / 4)
  calc Real.sqrt Real.pi * (Real.exp (y ^ 2 / 4) * Real.exp (-x ^ 2 / 4)) * (1 + x ^ 2)
      = Real.sqrt Real.pi * Real.exp (y ^ 2 / 4) * (Real.exp (-x ^ 2 / 4) * (1 + x ^ 2)) := by ring
    _ ≤ Real.sqrt Real.pi * Real.exp (y ^ 2 / 4) * 4 := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

lemma norm_Fm_imag (m : FiniteMeasure (OnePoint ℝ)) (y : ℝ) :
    ‖Fm m ((y : ℂ) * I)‖ ≤ 4 * Real.sqrt Real.pi * (m.mass : ℝ) * Real.exp (y ^ 2 / 4) := by
  unfold Fm
  have hb : ∀ e : OnePoint ℝ, ‖ext (kf ((y : ℂ) * I)) e‖ ≤ 4 * Real.sqrt Real.pi * Real.exp (y ^ 2 / 4) := by
    intro e
    induction e using OnePoint.rec with
    | infty => simp; positivity
    | coe x => rw [ext_coe]; exact norm_kf_imag y x
  have := norm_integral_le_of_norm_le_const (μ := (m : Measure (OnePoint ℝ)))
    (Eventually.of_forall hb)
  refine this.trans (le_of_eq ?_)
  have hmass : (m : Measure (OnePoint ℝ)).real univ = (m.mass : ℝ) := by
    have h := congrArg ENNReal.toReal (FiniteMeasure.ennreal_mass (μ := m))
    rw [ENNReal.coe_toReal] at h
    rw [h]; rfl
  rw [hmass]; ring

/-- **Weighted stages ⇒ an entire realization.** -/
theorem exists_entire_realization (R : ℚ → ℝ) {M : ℝ} {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hf : ∀ n, FleetDualConverse.WeightedFeasible R M (ε n) n) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ (∀ q : ℚ, F (q : ℂ) = (R q : ℂ)) ∧
      ∃ C : ℝ, ∀ y : ℝ, ‖F ((y : ℂ) * I)‖ ≤ C * Real.exp (y ^ 2 / 4) := by
  obtain ⟨m, hm⟩ := exists_limit R hε hf
  refine ⟨Fm m, differentiable_Fm m, fun q => ?_, 4 * Real.sqrt Real.pi * (m.mass : ℝ),
    norm_Fm_imag m⟩
  rw [Fm_rat, hm q]

end FleetWeightedLimit
