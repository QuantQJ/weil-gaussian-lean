import FleetPrimePoleBoundRH
import OffLineDetection
import RealSideBound

/-!
# Heat semigroup and monotonicity in `b` of the Gaussian zero trace

`R_b(α) = Σ_x ĝ_{b,α}(t_x)` (`= rhs (gauss b α)` by `FleetPrimePoleBoundRH.zero_trace_eq_rhs`).
Source: `research_notes/DUAL-INEQUALITY/POSITIVITY_ATTACK.md` item 3 ("Heat-equation maximum principle":
`R_{b+c} = G_c * R_b / 2π`, so `min_q R_b` is nondecreasing in `b`) and `HEAT_POSITIVITY.md`
("Gaussian semigroup (variances 2 and 2b add)").

* `integral_gaussHat_mul_heatW` : for complex `z`, `∫ ĝ_{b,u}(z) e^{−(u−α)²/(4c)} du = √(4πc) ĝ_{b+c,α}(z)`.
  With `G_c(x) = √(π/c) e^{−x²/(4c)}` this is the source's `G_c * R_b / 2π`, since `√(π/c)/(2π) = 1/√(4πc)`.
* `zeroTrace_heat_semigroup`, `rhs_heat_semigroup` : `R_{b+c}(α) = (4πc)^{−1/2} ∫ R_b(u) e^{−(u−α)²/(4c)} du`.
* `zeroTrace_lower_bound_mono`, `rhs_lower_bound_mono` : `m ≤ Re R_b` everywhere ⇒ `m ≤ Re R_{b'}` everywhere
  for every `b' ≥ b`.
* `heatPositiveWidths_upward_closed` : `{b > 0 | Re R_b ≥ 0 everywhere}` is upward closed.

The proof is the convolution identity plus a sum–integral interchange
(`integral_tsum_of_summable_integral_norm`), not the PDE maximum principle named in the source.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set MeasureTheory
open scoped Real
open OffLineDetection Reduction ZeroSumLimit GaussianTest

namespace FleetHeatMonotone

/-- The heat kernel weight `exp (−(u − α)² / (4c))`. -/
def heatW (c α u : ℝ) : ℝ := Real.exp (-(u - α) ^ 2 / (4 * c))

lemma heatW_pos (c α u : ℝ) : 0 < heatW c α u := Real.exp_pos _

lemma integrable_heatW {c : ℝ} (hc : 0 < c) (α : ℝ) : Integrable (heatW c α) := by
  have h := (integrable_exp_neg_mul_sq (b := 1 / (4 * c)) (by positivity)).comp_sub_right α
  refine h.congr (ae_of_all _ fun u => ?_)
  simp only [heatW]
  congr 1
  field_simp

lemma integral_heatW {c : ℝ} (hc : 0 < c) (α : ℝ) : ∫ u, heatW c α u = Real.sqrt (4 * π * c) := by
  have h1 : (fun u => heatW c α u) = fun u => Real.exp (-(1 / (4 * c)) * (u - α) ^ 2) := by
    funext u; simp only [heatW]; congr 1; field_simp
  rw [h1, integral_sub_right_eq_self (fun u => Real.exp (-(1 / (4 * c)) * u ^ 2)) α,
    integral_gaussian]
  congr 1
  field_simp

/-- Pointwise: `ĝ_{b,u}(z) · w_c(u)` is `√(π/b)` times the exponential of a quadratic in `u`. -/
lemma gaussHat_mul_heatW {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (α : ℝ) (z : ℂ) (u : ℝ) :
    gaussHat b u z * (heatW c α u : ℂ)
      = (Real.sqrt (π / b) : ℂ) * Complex.exp (-(1 / (4 * (b : ℂ)) + 1 / (4 * (c : ℂ))) * (u : ℂ) ^ 2
          + (z / (2 * b) + (α : ℂ) / (2 * c)) * u + (-z ^ 2 / (4 * b) - (α : ℂ) ^ 2 / (4 * c))) := by
  rw [gaussHat_eq hb, heatW, Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
  congr 2
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  push_cast
  field_simp
  ring

lemma integrable_gaussHat_mul_heatW {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (α : ℝ) (z : ℂ) :
    Integrable (fun u : ℝ => gaussHat b u z * (heatW c α u : ℂ)) := by
  simp_rw [gaussHat_mul_heatW hb hc α z]
  refine Integrable.const_mul (integrable_cexp_quadratic' ?_ _ _) _
  have : (-(1 / (4 * (b : ℂ)) + 1 / (4 * (c : ℂ)))) = ((-(1 / (4 * b) + 1 / (4 * c)) : ℝ) : ℂ) := by
    push_cast; ring
  rw [this, Complex.ofReal_re]
  have : 0 < 1 / (4 * b) + 1 / (4 * c) := by positivity
  linarith

/-- **One-term heat identity.** For complex `z`, `b, c > 0` and real `α`:
`∫ ĝ_{b,u}(z) e^{−(u−α)²/(4c)} du = √(4πc) · ĝ_{b+c,α}(z)`. -/
theorem integral_gaussHat_mul_heatW {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (α : ℝ) (z : ℂ) :
    ∫ u : ℝ, gaussHat b u z * (heatW c α u : ℂ)
      = (Real.sqrt (4 * π * c) : ℂ) * gaussHat (b + c) α z := by
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hbc' : (b : ℂ) + c ≠ 0 := by exact_mod_cast (by linarith : (0:ℝ) < b + c).ne'
  have hcb' : (c : ℂ) + b ≠ 0 := by rw [add_comm]; exact hbc'
  simp_rw [gaussHat_mul_heatW hb hc α z]
  have hA : (-(1 / (4 * (b : ℂ)) + 1 / (4 * (c : ℂ)))).re < 0 := by
    have : (-(1 / (4 * (b : ℂ)) + 1 / (4 * (c : ℂ)))) = ((-(1 / (4 * b) + 1 / (4 * c)) : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.ofReal_re]
    have : 0 < 1 / (4 * b) + 1 / (4 * c) := by positivity
    linarith
  rw [integral_const_mul, integral_cexp_quadratic hA, gaussHat_eq (by linarith : 0 < b + c)]
  have hpi : (π : ℂ) / -(-(1 / (4 * (b : ℂ)) + 1 / (4 * (c : ℂ))))
      = ((4 * π * b * c / (b + c) : ℝ) : ℂ) := by
    push_cast; field_simp; ring
  rw [hpi, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow]
  have hexp : (-z ^ 2 / (4 * (b : ℂ)) - (α : ℂ) ^ 2 / (4 * c))
      - (z / (2 * b) + (α : ℂ) / (2 * c)) ^ 2 / (4 * -(1 / (4 * (b : ℂ)) + 1 / (4 * (c : ℂ))))
      = -(z - ((α : ℝ) : ℂ)) ^ 2 / (4 * ((b + c : ℝ) : ℂ)) := by
    push_cast
    field_simp
    ring
  rw [hexp, ← mul_assoc, ← mul_assoc]
  congr 1
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.sqrt_mul (by positivity),
    ← Real.sqrt_mul (by positivity)]
  congr 2
  field_simp

/-- Real-argument form of the one-term identity. -/
lemma integral_real_heat {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (α r : ℝ) :
    ∫ u : ℝ, Real.sqrt (π / b) * Real.exp (-(r - u) ^ 2 / (4 * b)) * heatW c α u
      = Real.sqrt (4 * π * c) * RealSideBound.term (b + c) α r := by
  have h := integral_gaussHat_mul_heatW hb hc α (r : ℂ)
  have hl : (fun u : ℝ => gaussHat b u (r : ℂ) * (heatW c α u : ℂ))
      = fun u : ℝ => ((Real.sqrt (π / b) * Real.exp (-(r - u) ^ 2 / (4 * b)) * heatW c α u : ℝ) : ℂ) := by
    funext u; rw [gaussHat_real hb]; push_cast; ring
  rw [hl, integral_complex_ofReal, gaussHat_real (by linarith : 0 < b + c)] at h
  unfold RealSideBound.term
  exact_mod_cast h

/-- `‖ĝ_{b,u}(z) w_c(u)‖ = e^{(Im z)²/(4b)} · √(π/b) e^{−(Re z − u)²/(4b)} w_c(u)`. -/
lemma norm_gaussHat_mul_heatW {b c : ℝ} (hb : 0 < b) (α : ℝ) (z : ℂ) (u : ℝ) :
    ‖gaussHat b u z * (heatW c α u : ℂ)‖
      = Real.exp (z.im ^ 2 / (4 * b))
        * (Real.sqrt (π / b) * Real.exp (-(z.re - u) ^ 2 / (4 * b)) * heatW c α u) := by
  rw [norm_mul, norm_gaussHat hb, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (heatW_pos c α u)]
  have : Real.exp ((z.im ^ 2 - (z.re - u) ^ 2) / (4 * b))
      = Real.exp (z.im ^ 2 / (4 * b)) * Real.exp (-(z.re - u) ^ 2 / (4 * b)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this]; ring

lemma integral_norm_gaussHat_mul_heatW {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (α : ℝ) (z : ℂ) :
    ∫ u : ℝ, ‖gaussHat b u z * (heatW c α u : ℂ)‖
      = Real.exp (z.im ^ 2 / (4 * b)) * (Real.sqrt (4 * π * c) * RealSideBound.term (b + c) α z.re) := by
  simp_rw [norm_gaussHat_mul_heatW hb α z]
  rw [integral_const_mul, integral_real_heat hb hc]

/-- Integrability of a `tsum` of integrable functions with summable `L¹` norms. -/
lemma integrable_tsum_of_summable {ι : Type*} [Countable ι] {F : ι → ℝ → ℂ}
    (hF : ∀ i, Integrable (F i)) (hsum : Summable fun i => ∫ u, ‖F i u‖)
    (hmeas : AEStronglyMeasurable (fun u => ∑' i, F i u)) :
    Integrable (fun u => ∑' i, F i u) := by
  refine ⟨hmeas, ?_⟩
  unfold HasFiniteIntegral
  calc ∫⁻ u, ‖∑' i, F i u‖ₑ ≤ ∫⁻ u, ∑' i, ‖F i u‖ₑ := lintegral_mono fun u => enorm_tsum_le_tsum_enorm
    _ = ∑' i, ∫⁻ u, ‖F i u‖ₑ := lintegral_tsum fun i => (hF i).1.enorm
    _ = ∑' i, ENNReal.ofReal (∫ u, ‖F i u‖) := by
        congr 1; funext i; rw [ofReal_integral_norm_eq_lintegral_enorm (hF i)]
    _ = ENNReal.ofReal (∑' i, ∫ u, ‖F i u‖) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg fun u => norm_nonneg _) hsum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

lemma summable_integral_norm {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (α : ℝ) :
    Summable fun x : Index => ∫ u : ℝ, ‖gaussHat b u (t x) * (heatW c α u : ℂ)‖ := by
  simp_rw [integral_norm_gaussHat_mul_heatW hb hc α]
  have hs := RealSideBound.summable_term summable_inv_one_add_sq_re (b + c) (by linarith) α
  refine Summable.of_nonneg_of_le (fun x => ?_) (fun x => ?_)
    (hs.mul_left (Real.exp (1 / (16 * b)) * Real.sqrt (4 * π * c)))
  · have := RealSideBound.term_nonneg (b + c) α (t x).re
    positivity
  · have hT := RealSideBound.term_nonneg (b + c) α (t x).re
    have he : Real.exp ((t x).im ^ 2 / (4 * b)) ≤ Real.exp (1 / (16 * b)) := by
      apply Real.exp_le_exp.2
      have := t_im_sq_lt x
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have := mul_le_mul_of_nonneg_right he
      (mul_nonneg (Real.sqrt_nonneg (4 * π * c)) hT)
    linarith [this]

lemma aestronglyMeasurable_zeroTrace_mul {b c : ℝ} (hb : 0 < b) (α : ℝ) :
    AEStronglyMeasurable (fun u : ℝ => ∑' x : Index, gaussHat b u (t x) * (heatW c α u : ℂ)) := by
  refine aestronglyMeasurable_of_tendsto_ae (u := (atTop : Filter (Finset Index)))
    (f := fun s u => ∑ x ∈ s, gaussHat b u (t x) * (heatW c α u : ℂ)) (fun s => ?_)
    (ae_of_all _ fun u => ((GaussianTraceFormula.gaussian_formula_zeros hb u).summable.mul_right
      (heatW c α u : ℂ)).hasSum)
  refine (continuous_finsetSum _ fun x _ => ?_).aestronglyMeasurable
  have : (fun u : ℝ => gaussHat b u (t x) * (heatW c α u : ℂ))
      = fun u : ℝ => (Real.sqrt (π / b) : ℂ) * Complex.exp (-(t x - (u : ℂ)) ^ 2 / (4 * b))
          * Complex.exp (((-(u - α) ^ 2 / (4 * c) : ℝ) : ℂ)) := by
    funext u; rw [gaussHat_eq hb, heatW, Complex.ofReal_exp]
  rw [this]
  fun_prop

/-- The heat-smoothed zero trace is integrable against the heat kernel. -/
theorem integrable_zeroTrace_mul_heatW {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (α : ℝ) :
    Integrable (fun u : ℝ => (∑' x : Index, gaussHat b u (t x)) * (heatW c α u : ℂ)) := by
  have h := integrable_tsum_of_summable (fun x => integrable_gaussHat_mul_heatW hb hc α (t x))
    (summable_integral_norm hb hc α) (aestronglyMeasurable_zeroTrace_mul hb α)
  refine h.congr (ae_of_all _ fun u => ?_)
  exact tsum_mul_right

/-- **Heat semigroup for the zero trace.** For `b, c > 0` and real `α`,
`Σ_x ĝ_{b+c,α}(t_x) = (4πc)^{-1/2} ∫ (Σ_x ĝ_{b,u}(t_x)) e^{−(u−α)²/(4c)} du`. -/
theorem zeroTrace_heat_semigroup {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (α : ℝ) :
    ∑' x : Index, gaussHat (b + c) α (t x)
      = ((1 / Real.sqrt (4 * π * c) : ℝ) : ℂ)
        * ∫ u : ℝ, (∑' x : Index, gaussHat b u (t x)) * (Real.exp (-(u - α) ^ 2 / (4 * c)) : ℂ) := by
  have hint := integral_tsum_of_summable_integral_norm
    (fun x => integrable_gaussHat_mul_heatW hb hc α (t x)) (summable_integral_norm hb hc α)
  simp_rw [integral_gaussHat_mul_heatW hb hc α] at hint
  have h2 : (∫ u : ℝ, (∑' x : Index, gaussHat b u (t x)) * (Real.exp (-(u - α) ^ 2 / (4 * c)) : ℂ))
      = ∫ u : ℝ, ∑' x : Index, gaussHat b u (t x) * (heatW c α u : ℂ) := by
    congr 1; funext u; rw [tsum_mul_right]; rfl
  rw [h2, ← hint, tsum_mul_left, ← mul_assoc, ← Complex.ofReal_mul]
  have hs : 0 < Real.sqrt (4 * π * c) := Real.sqrt_pos.2 (by positivity)
  rw [one_div_mul_cancel hs.ne', Complex.ofReal_one, one_mul]

/-- **Heat semigroup for the arithmetic side** `R_b(α) = rhs (gauss b α)`. -/
theorem rhs_heat_semigroup {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (α : ℝ) :
    FleetFullLineArithmetic.rhs (gauss (b + c) α)
      = ((1 / Real.sqrt (4 * π * c) : ℝ) : ℂ)
        * ∫ u : ℝ, FleetFullLineArithmetic.rhs (gauss b u) * (Real.exp (-(u - α) ^ 2 / (4 * c)) : ℂ) := by
  rw [← FleetPrimePoleBoundRH.zero_trace_eq_rhs (by linarith) α]
  have : (fun u : ℝ => FleetFullLineArithmetic.rhs (gauss b u) * (Real.exp (-(u - α) ^ 2 / (4 * c)) : ℂ))
      = fun u : ℝ => (∑' x : Index, gaussHat b u (t x)) * (Real.exp (-(u - α) ^ 2 / (4 * c)) : ℂ) := by
    funext u; rw [← FleetPrimePoleBoundRH.zero_trace_eq_rhs hb u]; rfl
  rw [this]
  exact zeroTrace_heat_semigroup hb hc α

/-- **Monotonicity in `b`.** A lower bound `m ≤ Re R_b(u)` valid at every real centre persists for
every larger width `b' ≥ b` and every centre. -/
theorem zeroTrace_lower_bound_mono {b b' : ℝ} (hb : 0 < b) (hbb' : b ≤ b') {m : ℝ}
    (hm : ∀ u : ℝ, m ≤ (∑' x : Index, gaussHat b u (t x)).re) (α : ℝ) :
    m ≤ (∑' x : Index, gaussHat b' α (t x)).re := by
  rcases hbb'.eq_or_lt with h | h
  · rw [← h]; exact hm α
  set c := b' - b with hc_def
  have hc : 0 < c := by rw [hc_def]; linarith
  have hb' : b' = b + c := by rw [hc_def]; ring
  rw [hb', zeroTrace_heat_semigroup hb hc α, Complex.re_ofReal_mul]
  have hI := integrable_zeroTrace_mul_heatW hb hc α
  have hs : 0 < Real.sqrt (4 * π * c) := Real.sqrt_pos.2 (by positivity)
  change m ≤ 1 / Real.sqrt (4 * π * c)
    * (∫ u : ℝ, (∑' x : Index, gaussHat b u (t x)) * (heatW c α u : ℂ)).re
  have hre : (∫ u : ℝ, (∑' x : Index, gaussHat b u (t x)) * (heatW c α u : ℂ)).re
      = ∫ u : ℝ, ((∑' x : Index, gaussHat b u (t x)) * (heatW c α u : ℂ)).re :=
    (integral_re hI).symm
  rw [hre]
  have hle : ∫ u : ℝ, m * heatW c α u
      ≤ ∫ u : ℝ, ((∑' x : Index, gaussHat b u (t x)) * (heatW c α u : ℂ)).re := by
    refine integral_mono ((integrable_heatW hc α).const_mul m) hI.re fun u => ?_
    simp only
    rw [Complex.re_mul_ofReal]
    exact mul_le_mul_of_nonneg_right (hm u) (heatW_pos c α u).le
  rw [integral_const_mul, integral_heatW hc α] at hle
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hs]
  linarith

/-- **Monotonicity in `b`, arithmetic side.** -/
theorem rhs_lower_bound_mono {b b' : ℝ} (hb : 0 < b) (hbb' : b ≤ b') {m : ℝ}
    (hm : ∀ u : ℝ, m ≤ (FleetFullLineArithmetic.rhs (gauss b u)).re) (α : ℝ) :
    m ≤ (FleetFullLineArithmetic.rhs (gauss b' α)).re := by
  rw [← FleetPrimePoleBoundRH.zero_trace_eq_rhs (by linarith) α]
  refine zeroTrace_lower_bound_mono hb hbb' (fun u => ?_) α
  have := hm u
  rw [← FleetPrimePoleBoundRH.zero_trace_eq_rhs hb u] at this
  exact this

/-- The set of widths at which the arithmetic side is nonnegative at every centre. -/
def heatPositiveWidths : Set ℝ :=
  {b : ℝ | 0 < b ∧ ∀ α : ℝ, 0 ≤ (FleetFullLineArithmetic.rhs (gauss b α)).re}

/-- **Upward closure.** If `Re R_b ≥ 0` everywhere then `Re R_{b'} ≥ 0` everywhere for all `b' ≥ b`. -/
theorem heatPositiveWidths_upward_closed {b b' : ℝ} (hb : b ∈ heatPositiveWidths) (hbb' : b ≤ b') :
    b' ∈ heatPositiveWidths :=
  ⟨lt_of_lt_of_le hb.1 hbb', rhs_lower_bound_mono hb.1 hbb' hb.2⟩

end FleetHeatMonotone
