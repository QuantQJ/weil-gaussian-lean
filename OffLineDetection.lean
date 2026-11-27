import GaussianTest
import RealSideBound
import ExpSumLowerBound
import ZeroSumLimit
import Reduction
import ZetaStrip
import Mathlib

/-!
# Off-line detection: a Gaussian trace identity forces every zero onto the critical line

Let `γ : ι → ℝ` be a real *tempered* sequence (`∑ 1/(1 + γᵢ²) < ∞`) whose Gaussian trace agrees
with that of the nontrivial zeros for **every** width `b > 0` and centre `α`:

  `∑ᵢ gaussHat b α (γᵢ) = ∑ₓ gaussHat b α (ordinate (canonical x))`.

Then every zero ordinate is real, hence the Riemann Hypothesis holds.

**Mechanism.** With `s = 1/(4b)` and `t = ordinate ρ`,
`gaussHat b α t = √(π/b) · exp (v s) · exp (i θ s)` where `v = (Im t)² − (Re t − α)²` and
`θ = −2 (Re t − α) Im t` are real (`gaussHat_polar`).  The real side is `O(√(π/b))`
(`RealSideBound.tsum_term_le`), i.e. `O(b^{-1/2})`.  If some ordinate `t₀` had `Im t₀ ≠ 0`, put
`α = Re t₀`: the finitely many ordinates with `|Re t − α| < 1` have a maximal `v`-value
`M ≥ (Im t₀)² > 0`, attained on a nonempty finite set `S`; the remaining nearby terms are
`O(exp ((M − ε) s))`, and the far terms are `O(exp (−3s/4))` (`tail_bound`).  So
`exp (M s) · ‖∑_{x ∈ S} exp (i θₓ s)‖ ≤ C' + |Z| exp ((M − ε) s) + C exp (−3s/4)`,
which forces `‖∑_{x ∈ S} exp (i θₓ s)‖ → 0`, contradicting `ExpSumLowerBound.exists_large_of_nonempty`.

This module does **not** assume the explicit formula; the Gaussian identity is an explicit
hypothesis to be supplied by the glue.  Standard Mathlib foundations only (see `AxiomAudit.lean`).
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Topology Set
open scoped Real

namespace OffLineDetection

open Reduction ZeroSumLimit GaussianTest

/-! ## (a) The ordinates of the canonical enumeration -/

/-- The ordinate `t x = ordinate (canonical x)` of the `x`-th canonical zero. -/
def t (x : Index) : ℂ := ordinate (canonical x)

lemma t_re (x : Index) : (t x).re = (canonical x).im := ordinate_re _

lemma t_im (x : Index) : (t x).im = 1 / 2 - (canonical x).re := ordinate_im _

/-- `|Im (t x)| < 1/2`: the zero lies in the open critical strip. -/
lemma abs_t_im_lt (x : Index) : |(t x).im| < 1 / 2 := by
  have h := ZetaStrip.mem_strip_of_isNontrivialZero (multEnum_canonical.nontrivial x)
  rw [t_im, abs_lt]
  constructor <;> linarith [h.1, h.2]

/-- `(Im (t x))² < 1/4`. -/
lemma t_im_sq_lt (x : Index) : (t x).im ^ 2 < 1 / 4 := by
  have h := abs_t_im_lt x
  have h0 := abs_nonneg (t x).im
  rw [← _root_.sq_abs]
  nlinarith

/-- The near set `Z α = {x | |Re (t x) − α| < 1}`. -/
def Z (α : ℝ) : Set Index := {x | |(t x).re - α| < 1}

/-- The near set is finite. -/
lemma Z_finite (α : ℝ) : (Z α).Finite := by
  refine (multEnum_canonical.finite (|α| + 1)).subset ?_
  intro x hx
  simp only [Z, mem_setOf_eq] at hx ⊢
  rw [← t_re]
  have := abs_sub_abs_le_abs_sub (t x).re α
  linarith

/-- The near set as a `Finset`. -/
def Zfin (α : ℝ) : Finset Index := (Z_finite α).toFinset

lemma mem_Zfin {α : ℝ} {x : Index} : x ∈ Zfin α ↔ |(t x).re - α| < 1 := by
  simp [Zfin, Z, Set.Finite.mem_toFinset]

/-- **Temperedness of the ordinates**: `∑ₓ 1/(1 + (Re (t x))²) < ∞`. -/
theorem summable_inv_one_add_sq_re : Summable (fun x : Index => 1 / (1 + (t x).re ^ 2)) := by
  have h := summable_inv_sq_im multEnum_canonical
  refine Summable.of_norm_bounded_eventually h ?_
  rw [Filter.eventually_cofinite]
  refine (multEnum_canonical.finite 0).subset ?_
  intro x hx
  simp only [mem_setOf_eq] at hx ⊢
  by_contra hcon
  apply hx
  rw [Real.norm_eq_abs, _root_.abs_of_nonneg (by positivity), t_re]
  have hne : (canonical x).im ≠ 0 := by
    intro h0
    rw [abs_le] at hcon
    push_neg at hcon
    rw [h0] at hcon
    norm_num at hcon
  have hpos : 0 < (canonical x).im ^ 2 := by positivity
  rw [div_le_div_iff₀ (by positivity) hpos]
  nlinarith

/-! ## (b) Polar form of the Gaussian transform -/

/-- The real exponent `v = (Im z)² − (Re z − α)²`. -/
def vE (α : ℝ) (z : ℂ) : ℝ := z.im ^ 2 - (z.re - α) ^ 2

/-- The real phase frequency `θ = −2 (Re z − α) Im z`. -/
def thetaE (α : ℝ) (z : ℂ) : ℝ := -2 * (z.re - α) * z.im

/-- `−(z − α)² = v + i θ`. -/
lemma neg_sq_eq (α : ℝ) (z : ℂ) :
    -(z - (α : ℂ)) ^ 2 = ((vE α z : ℝ) : ℂ) + I * ((thetaE α z : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [vE, thetaE, sq, Complex.neg_re, Complex.mul_re, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.I_re, Complex.I_im]
    ring
  · simp only [vE, thetaE, sq, Complex.neg_im, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.add_im, Complex.I_re, Complex.I_im,
      Complex.mul_re]
    ring

/-- **Polar form.** For `s = 1/(4b)`:
`gaussHat b α z = √(π/b) · exp (v s) · exp (i θ s)` with `v = vE α z`, `θ = thetaE α z`. -/
theorem gaussHat_polar {b : ℝ} (hb : 0 < b) (α : ℝ) (z : ℂ) {s : ℝ} (hs : s = 1 / (4 * b)) :
    gaussHat b α z = (Real.sqrt (π / b) : ℂ) * ((Real.exp (vE α z * s) : ℝ) : ℂ)
      * Complex.exp (I * ((thetaE α z : ℝ) : ℂ) * (s : ℂ)) := by
  rw [gaussHat_eq hb, mul_assoc]
  congr 1
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  have hsC : (s : ℂ) = 1 / (4 * (b : ℂ)) := by rw [hs]; push_cast; ring
  rw [div_eq_mul_one_div, ← hsC, neg_sq_eq]
  push_cast
  ring

/-- Modulus in terms of `s = 1/(4b)`: `‖gaussHat b α z‖ = √(π/b) · exp (v s)`. -/
theorem norm_gaussHat_s {b : ℝ} (hb : 0 < b) (α : ℝ) (z : ℂ) {s : ℝ} (hs : s = 1 / (4 * b)) :
    ‖gaussHat b α z‖ = Real.sqrt (π / b) * Real.exp (vE α z * s) := by
  rw [norm_gaussHat hb, hs]
  unfold vE
  congr 2
  exact div_eq_mul_one_div _ _

/-! ## (c) Tail bound over the far zeros -/

/-- The far-zero weight `w α x = exp (−(Re (t x) − α)² / 4)`. -/
def w (α : ℝ) (x : Index) : ℝ := Real.exp (-((t x).re - α) ^ 2 / 4)

lemma w_nonneg (α : ℝ) (x : Index) : 0 ≤ w α x := by unfold w; positivity

/-- The far-zero weights are summable. -/
theorem summable_w (α : ℝ) : Summable (w α) := by
  obtain ⟨C, hC⟩ := RealSideBound.gaussian_le_inv_sq α
  refine Summable.of_nonneg_of_le (w_nonneg α) (fun x => ?_)
    (summable_inv_one_add_sq_re.mul_left C)
  unfold w
  calc Real.exp (-((t x).re - α) ^ 2 / 4) ≤ C / (1 + (t x).re ^ 2) := hC _
    _ = C * (1 / (1 + (t x).re ^ 2)) := by ring

/-- Exponent inequality for the far zeros: if `(Im z)² < 1/4`, `|Re z − α| ≥ 1` and `0 < b ≤ 1`,
then `((Im z)² − (Re z − α)²)/(4b) ≤ −3/(16b) + 1/4 − (Re z − α)²/4`. -/
lemma far_exponent_le {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) {α : ℝ} {z : ℂ}
    (him : z.im ^ 2 < 1 / 4) (hre : 1 ≤ |z.re - α|) :
    (z.im ^ 2 - (z.re - α) ^ 2) / (4 * b) ≤ -3 / (16 * b) + 1 / 4 - (z.re - α) ^ 2 / 4 := by
  have hX : 1 ≤ (z.re - α) ^ 2 := by
    rw [← _root_.sq_abs]
    nlinarith [abs_nonneg (z.re - α)]
  have heq : -3 / (16 * b) + 1 / 4 - (z.re - α) ^ 2 / 4
      = (-3 / 4 + b - b * (z.re - α) ^ 2) / (4 * b) := by
    field_simp
    ring
  rw [heq, div_le_div_iff_of_pos_right (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 hX) (sub_nonneg.2 hb1)]

/-- Pointwise far bound: for `x ∉ Z α` and `0 < b ≤ 1`,
`‖gaussHat b α (t x)‖ ≤ √(π/b) · exp (−3/(16b)) · (e^{1/4} · w α x)`. -/
lemma norm_gaussHat_far {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) {α : ℝ} {x : Index} (hx : x ∉ Z α) :
    ‖gaussHat b α (t x)‖
      ≤ Real.sqrt (π / b) * Real.exp (-3 / (16 * b)) * (Real.exp (1 / 4) * w α x) := by
  have hre : 1 ≤ |(t x).re - α| := by
    simp only [Z, mem_setOf_eq, not_lt] at hx
    exact hx
  rw [norm_gaussHat hb]
  have h := far_exponent_le hb hb1 (t_im_sq_lt x) hre
  calc Real.sqrt (π / b) * Real.exp (((t x).im ^ 2 - ((t x).re - α) ^ 2) / (4 * b))
      ≤ Real.sqrt (π / b) * Real.exp (-3 / (16 * b) + 1 / 4 - ((t x).re - α) ^ 2 / 4) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h) (Real.sqrt_nonneg _)
    _ = Real.sqrt (π / b) * Real.exp (-3 / (16 * b)) * (Real.exp (1 / 4) * w α x) := by
        unfold w
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, neg_div]
        ring_nf

/-- **Tail bound.** There is `C ≥ 0` with
`‖∑'ₓ (Z α)ᶜ.indicator (gaussHat b α ∘ t) x‖ ≤ √(π/b) · exp (−3/(16b)) · C` for all `0 < b ≤ 1`. -/
theorem tail_bound (α : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ b : ℝ, 0 < b → b ≤ 1 →
    ‖∑' x : Index, (Z α)ᶜ.indicator (fun x => gaussHat b α (t x)) x‖
      ≤ Real.sqrt (π / b) * Real.exp (-3 / (16 * b)) * C := by
  refine ⟨Real.exp (1 / 4) * ∑' x, w α x,
    mul_nonneg (Real.exp_pos _).le (tsum_nonneg (w_nonneg α)), fun b hb hb1 => ?_⟩
  have hg : HasSum (fun x => Real.sqrt (π / b) * Real.exp (-3 / (16 * b)) * (Real.exp (1 / 4) * w α x))
      (Real.sqrt (π / b) * Real.exp (-3 / (16 * b)) * (Real.exp (1 / 4) * ∑' x, w α x)) := by
    have hsw : Summable (fun x => Real.exp (1 / 4) * w α x) := (summable_w α).mul_left _
    have := (hsw.mul_left (Real.sqrt (π / b) * Real.exp (-3 / (16 * b)))).hasSum
    rw [tsum_mul_left, tsum_mul_left] at this
    exact this
  refine tsum_of_norm_bounded hg (fun x => ?_)
  by_cases hx : x ∈ (Z α)ᶜ
  · rw [Set.indicator_of_mem hx]
    exact norm_gaussHat_far hb hb1 hx
  · rw [Set.indicator_of_notMem hx, norm_zero]
    have := w_nonneg α x
    positivity

/-! ## (d) Real-side bound -/

/-- **Real-side bound.** For a tempered real sequence there is `C'` with
`‖∑ᵢ gaussHat b α (γᵢ)‖ ≤ √(π/b) · C'` for all `0 < b ≤ 1`. -/
theorem real_side_bound {ι : Type*} (γ : ι → ℝ)
    (hsum : Summable (fun i => 1 / (1 + (γ i) ^ 2))) (α : ℝ) :
    ∃ C' : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      ‖∑' i, gaussHat b α ((γ i : ℝ) : ℂ)‖ ≤ Real.sqrt (π / b) * C' := by
  obtain ⟨C', hC'⟩ := RealSideBound.tsum_term_le hsum α
  refine ⟨C', fun b hb hb1 => ?_⟩
  have heq : (fun i => gaussHat b α ((γ i : ℝ) : ℂ))
      = fun i => ((RealSideBound.term b α (γ i) : ℝ) : ℂ) := by
    funext i
    rw [gaussHat_real hb]
    rfl
  rw [heq, ← Complex.ofReal_tsum, Complex.norm_real, Real.norm_eq_abs,
    _root_.abs_of_nonneg (RealSideBound.tsum_term_nonneg b α)]
  exact hC' b hb hb1

/-! ## (e) The off-line contradiction -/

/-- A finite family of reals bounded by `M` has a gap below `M`: some `ε > 0` with
`v x ≤ M − ε` whenever `v x ≠ M`. -/
lemma exists_gap (Zf : Finset Index) (v : Index → ℝ) (M : ℝ) (hM : ∀ x ∈ Zf, v x ≤ M) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Zf, v x ≠ M → v x ≤ M - ε := by
  classical
  set R := Zf.filter (fun x => v x ≠ M) with hR
  by_cases hne : R.Nonempty
  · obtain ⟨xr, hxr, hmax⟩ := Finset.exists_max_image R v hne
    have hxr' := Finset.mem_filter.mp hxr
    have hlt : v xr < M := lt_of_le_of_ne (hM xr hxr'.1) hxr'.2
    refine ⟨M - v xr, by linarith, fun x hx hvx => ?_⟩
    have := hmax x (Finset.mem_filter.mpr ⟨hx, hvx⟩)
    linarith
  · refine ⟨1, one_pos, fun x hx hvx => ?_⟩
    exact absurd ⟨x, Finset.mem_filter.mpr ⟨hx, hvx⟩⟩ hne

/-- Splitting the zero side at the near set: `∑' f = ∑_{Zfin α} f + ∑' (Z α)ᶜ.indicator f`. -/
lemma tsum_split (α : ℝ) (f : Index → ℂ) (hf : Summable f) :
    ∑' x, f x = ∑ x ∈ Zfin α, f x + ∑' x, (Z α)ᶜ.indicator f x := by
  have h1 : Summable ((Z α).indicator f) := hf.indicator _
  have h2 : Summable ((Z α)ᶜ.indicator f) := hf.indicator _
  have hfin : ∑' x, (Z α).indicator f x = ∑ x ∈ Zfin α, f x := by
    rw [tsum_eq_sum (s := Zfin α)]
    · refine Finset.sum_congr rfl (fun x hx => ?_)
      exact Set.indicator_of_mem ((Set.Finite.mem_toFinset _).1 hx) f
    · intro x hx
      exact Set.indicator_of_notMem (fun h => hx ((Set.Finite.mem_toFinset _).2 h)) f
  calc ∑' x, f x = ∑' x, ((Z α).indicator f x + (Z α)ᶜ.indicator f x) := by
        simp only [Set.indicator_self_add_compl_apply]
    _ = ∑' x, (Z α).indicator f x + ∑' x, (Z α)ᶜ.indicator f x := h1.tsum_add h2
    _ = ∑ x ∈ Zfin α, f x + ∑' x, (Z α)ᶜ.indicator f x := by rw [hfin]

/-- **Off-line contradiction, quantitative form.** Fix `α`, a finite set `S ⊆ Zfin α` on which
`vE α (t x) = M`, with `vE α (t x) ≤ M − ε` on `Zfin α \ S`. Then for every `s ≥ 1/4`, with
`b = 1/(4s)`, the unimodular sum `E s = ∑_{x ∈ S} exp (i θₓ s)` satisfies
`exp (M s) ‖E s‖ ≤ C' + |Zfin α| exp ((M − ε) s) + C exp (−3s/4)`. -/
theorem key_estimate {ι : Type*} (γ : ι → ℝ)
    (hG : ∀ b : ℝ, 0 < b → ∀ α : ℝ,
      ∑' i, gaussHat b α ((γ i : ℝ) : ℂ) = ∑' x : Index, gaussHat b α (ordinate (canonical x)))
    (hS : ∀ b : ℝ, 0 < b → ∀ α : ℝ,
      Summable (fun x : Index => gaussHat b α (ordinate (canonical x))))
    (α : ℝ) (S : Finset Index) (hSsub : S ⊆ Zfin α) (M ε C C' : ℝ)
    (hSM : ∀ x ∈ S, vE α (t x) = M)
    (hgap : ∀ x ∈ Zfin α, x ∉ S → vE α (t x) ≤ M - ε)
    (hC : ∀ b : ℝ, 0 < b → b ≤ 1 →
      ‖∑' x : Index, (Z α)ᶜ.indicator (fun x => gaussHat b α (t x)) x‖
        ≤ Real.sqrt (π / b) * Real.exp (-3 / (16 * b)) * C)
    (hC' : ∀ b : ℝ, 0 < b → b ≤ 1 →
      ‖∑' i, gaussHat b α ((γ i : ℝ) : ℂ)‖ ≤ Real.sqrt (π / b) * C')
    (s : ℝ) (hs : 1 / 4 ≤ s) :
    Real.exp (M * s) * ‖∑ x ∈ S, Complex.exp (I * ((thetaE α (t x) : ℝ) : ℂ) * (s : ℂ))‖
      ≤ C' + (Zfin α).card * Real.exp ((M - ε) * s) + C * Real.exp (-(3 / 4) * s) := by
  classical
  set b : ℝ := 1 / (4 * s) with hb_def
  have hs0 : 0 < s := by linarith
  have hb : 0 < b := by positivity
  have hb1 : b ≤ 1 := by
    rw [hb_def, div_le_one (by positivity)]
    linarith
  have hsb : s = 1 / (4 * b) := by
    rw [hb_def]
    field_simp
  have h316 : -3 / (16 * b) = -(3 / 4) * s := by
    rw [hb_def]
    field_simp
    ring
  have hsqrt : 0 < Real.sqrt (π / b) := Real.sqrt_pos.2 (div_pos Real.pi_pos hb)
  set f : Index → ℂ := fun x => gaussHat b α (t x) with hf_def
  have hfS : Summable f := hS b hb α
  -- the zero side, split three ways
  have hsplit := tsum_split α f hfS
  rw [← Finset.sum_filter_add_sum_filter_not (Zfin α) (fun x => x ∈ S)] at hsplit
  have hfilt : (Zfin α).filter (fun x => x ∈ S) = S := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hSsub h, h⟩⟩
  rw [hfilt] at hsplit
  -- the `S`-part is `√(π/b) exp(M s) · E s`
  have hSpart : ∑ x ∈ S, f x
      = ((Real.sqrt (π / b) * Real.exp (M * s) : ℝ) : ℂ)
        * ∑ x ∈ S, Complex.exp (I * ((thetaE α (t x) : ℝ) : ℂ) * (s : ℂ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    simp only [hf_def]
    rw [gaussHat_polar hb α (t x) hsb, hSM x hx]
    push_cast
    ring
  -- the middle part
  have hmid : ‖∑ x ∈ (Zfin α).filter (fun x => x ∉ S), f x‖
      ≤ (Zfin α).card * (Real.sqrt (π / b) * Real.exp ((M - ε) * s)) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ (Real.sqrt (π / b) * Real.exp ((M - ε) * s))
      (fun x hx => ?_)).trans ?_
    · have hx' := Finset.mem_filter.mp hx
      simp only [hf_def]
      rw [norm_gaussHat_s hb α (t x) hsb]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.sqrt_nonneg _)
      exact mul_le_mul_of_nonneg_right (hgap x hx'.1 hx'.2) hs0.le
    · rw [nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact_mod_cast Finset.card_filter_le _ _
  -- the tail and the real side
  have htail := hC b hb hb1
  have hreal := hC' b hb hb1
  rw [hG b hb α] at hreal
  change ‖∑' x, f x‖ ≤ Real.sqrt (π / b) * C' at hreal
  -- assemble: `‖S-part‖ ≤ ‖total‖ + ‖mid‖ + ‖tail‖`
  have hkey : ‖∑ x ∈ S, f x‖ ≤ Real.sqrt (π / b) * C'
      + (Zfin α).card * (Real.sqrt (π / b) * Real.exp ((M - ε) * s))
      + Real.sqrt (π / b) * Real.exp (-3 / (16 * b)) * C := by
    have : ∑ x ∈ S, f x = ∑' x, f x - ∑ x ∈ (Zfin α).filter (fun x => x ∉ S), f x
        - ∑' x, (Z α)ᶜ.indicator f x := by
      rw [hsplit]; ring
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    refine add_le_add ((norm_sub_le _ _).trans (add_le_add hreal hmid)) htail
  rw [hSpart, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    _root_.abs_of_nonneg (by positivity), h316] at hkey
  -- divide by `√(π/b)`
  have hkey' : Real.sqrt (π / b) * (Real.exp (M * s)
      * ‖∑ x ∈ S, Complex.exp (I * ((thetaE α (t x) : ℝ) : ℂ) * (s : ℂ))‖)
      ≤ Real.sqrt (π / b) * (C' + (Zfin α).card * Real.exp ((M - ε) * s)
        + C * Real.exp (-(3 / 4) * s)) := by
    convert hkey using 1 <;> ring
  exact le_of_mul_le_mul_left hkey' hsqrt

/-- The bound function `C' e^{−Ms} + N e^{−εs} + C e^{−(M + 3/4)s}` tends to `0` when
`M, ε > 0`. -/
lemma tendsto_bound (C' N C M ε : ℝ) (hM : 0 < M) (hε : 0 < ε) :
    Tendsto (fun s : ℝ => C' * Real.exp (-(M * s)) + N * Real.exp (-(ε * s))
      + C * Real.exp (-((M + 3 / 4) * s))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun s : ℝ => Real.exp (-(M * s))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hM)
  have h2 : Tendsto (fun s : ℝ => Real.exp (-(ε * s))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hε)
  have h3 : Tendsto (fun s : ℝ => Real.exp (-((M + 3 / 4) * s))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop (by linarith))
  have := ((h1.const_mul C').add (h2.const_mul N)).add (h3.const_mul C)
  simpa using this

/-- **Main theorem (ordinates).** If a tempered real sequence has the same Gaussian trace as the
zeros for every width and centre, every zero ordinate is real. -/
theorem ordinates_real {ι : Type*} (γ : ι → ℝ)
    (hsum : Summable (fun i => 1 / (1 + (γ i) ^ 2)))
    (hG : ∀ b : ℝ, 0 < b → ∀ α : ℝ,
      ∑' i, gaussHat b α ((γ i : ℝ) : ℂ) = ∑' x : Index, gaussHat b α (ordinate (canonical x)))
    (hS : ∀ b : ℝ, 0 < b → ∀ α : ℝ,
      Summable (fun x : Index => gaussHat b α (ordinate (canonical x)))) :
    ∀ x : Index, (ordinate (canonical x)).im = 0 := by
  classical
  intro x₀
  by_contra hβ
  change (t x₀).im ≠ 0 at hβ
  set α : ℝ := (t x₀).re with hα
  -- `x₀` lies in the near set
  have hx₀ : x₀ ∈ Zfin α := by
    rw [mem_Zfin, hα, sub_self, abs_zero]
    exact one_pos
  have hne : (Zfin α).Nonempty := ⟨x₀, hx₀⟩
  -- the maximal value `M` of `v` on the near set
  obtain ⟨xm, hxm, hmax⟩ := Finset.exists_max_image (Zfin α) (fun x => vE α (t x)) hne
  set M : ℝ := vE α (t xm) with hM_def
  have hMpos : 0 < M := by
    have h0 : vE α (t x₀) = (t x₀).im ^ 2 := by
      simp only [vE, hα, sub_self]
      ring
    have h1 : 0 < (t x₀).im ^ 2 := by positivity
    have := hmax x₀ hx₀
    linarith
  -- the set `S` where the maximum is attained, and the gap `ε`
  set S : Finset Index := (Zfin α).filter (fun x => vE α (t x) = M) with hS_def
  have hSsub : S ⊆ Zfin α := Finset.filter_subset _ _
  have hSne : S.Nonempty := ⟨xm, Finset.mem_filter.mpr ⟨hxm, rfl⟩⟩
  have hSM : ∀ x ∈ S, vE α (t x) = M := fun x hx => (Finset.mem_filter.mp hx).2
  obtain ⟨ε, hε, hgap⟩ := exists_gap (Zfin α) (fun x => vE α (t x)) M (fun x hx => hmax x hx)
  have hgap' : ∀ x ∈ Zfin α, x ∉ S → vE α (t x) ≤ M - ε := by
    intro x hx hxS
    refine hgap x hx (fun h => hxS (Finset.mem_filter.mpr ⟨hx, h⟩))
  -- constants
  obtain ⟨C, -, hC⟩ := tail_bound α
  obtain ⟨C', hC'⟩ := real_side_bound γ hsum α
  -- the quantitative estimate, in the form `‖E s‖ ≤ B s`
  have hEst : ∀ s : ℝ, 1 / 4 ≤ s →
      ‖∑ x ∈ S, Complex.exp (I * ((thetaE α (t x) : ℝ) : ℂ) * (s : ℂ))‖
        ≤ C' * Real.exp (-(M * s)) + (Zfin α).card * Real.exp (-(ε * s))
          + C * Real.exp (-((M + 3 / 4) * s)) := by
    intro s hs
    have h := key_estimate γ hG hS α S hSsub M ε C C' hSM hgap' hC hC' s hs
    have hexp : 0 < Real.exp (M * s) := Real.exp_pos _
    refine le_of_mul_le_mul_right ?_ hexp
    have e1 : Real.exp (-(M * s)) * Real.exp (M * s) = 1 := by
      rw [← Real.exp_add]; simp
    have e2 : Real.exp (-(ε * s)) * Real.exp (M * s) = Real.exp ((M - ε) * s) := by
      rw [← Real.exp_add]; congr 1; ring
    have e3 : Real.exp (-((M + 3 / 4) * s)) * Real.exp (M * s) = Real.exp (-(3 / 4) * s) := by
      rw [← Real.exp_add]; congr 1; ring
    calc ‖∑ x ∈ S, Complex.exp (I * ((thetaE α (t x) : ℝ) : ℂ) * (s : ℂ))‖ * Real.exp (M * s)
        = Real.exp (M * s) * ‖∑ x ∈ S, Complex.exp (I * ((thetaE α (t x) : ℝ) : ℂ) * (s : ℂ))‖ := by
          ring
      _ ≤ C' + (Zfin α).card * Real.exp ((M - ε) * s) + C * Real.exp (-(3 / 4) * s) := h
      _ = (C' * Real.exp (-(M * s)) + (Zfin α).card * Real.exp (-(ε * s))
          + C * Real.exp (-((M + 3 / 4) * s))) * Real.exp (M * s) := by
          linear_combination (-C') * e1 - ((Zfin α).card : ℝ) * e2 - C * e3
  -- the bound tends to `0`, so it is `< 1/2` for large `s`
  have hB := tendsto_bound C' (Zfin α).card C M ε hMpos hε
  obtain ⟨S₁, hS₁⟩ := Filter.eventually_atTop.mp (hB.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2))
  -- but `‖E s‖ ≥ 1/2` at arbitrarily large `s`
  obtain ⟨s, hs, hlarge⟩ :=
    ExpSumLowerBound.exists_large_of_nonempty S hSne (fun x => thetaE α (t x)) (max S₁ (1 / 4))
  have hs1 : S₁ ≤ s := le_trans (le_max_left _ _) hs
  have hs2 : 1 / 4 ≤ s := le_trans (le_max_right _ _) hs
  have := hS₁ s hs1
  have := hEst s hs2
  linarith

/-- **Main theorem (RH).** If a tempered real sequence has the same Gaussian trace as the zeros
for every width and centre, the Riemann Hypothesis holds. -/
theorem RH_of_gaussian_trace {ι : Type*} (γ : ι → ℝ)
    (hsum : Summable (fun i => 1 / (1 + (γ i) ^ 2)))
    (hG : ∀ b : ℝ, 0 < b → ∀ α : ℝ,
      ∑' i, gaussHat b α ((γ i : ℝ) : ℂ) = ∑' x : Index, gaussHat b α (ordinate (canonical x)))
    (hS : ∀ b : ℝ, 0 < b → ∀ α : ℝ,
      Summable (fun x : Index => gaussHat b α (ordinate (canonical x)))) :
    RiemannHypothesis := by
  apply RH_of_nontrivial_zeros_on_critical_line
  intro ρ hρ
  obtain ⟨x, hx⟩ := multEnum_canonical.exists_index hρ
  have h := ordinates_real γ hsum hG hS x
  rw [hx, ordinate_im] at h
  linarith

end OffLineDetection

end
