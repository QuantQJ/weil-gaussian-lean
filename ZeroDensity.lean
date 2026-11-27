import Mathlib
import Jensen
import FiniteZeros
import ZetaStrip
import ZetaConj
import ZeroSymmetry
import ZetaGrowth
import Reduction
import ZerosCountable
import ZeroSumConvergence

/-!
# Zero-density bound for `ζ`: `N(T) = O(T log T)` from Jensen's formula

**Proven unconditionally (Lean's standard three axioms only):**

* `card_mul_log_le_of_jensen` — the honest general form of the counting argument: if `f` is
  holomorphic on `ball c R'`, its zero set in `ball c R'` is the finite set `Z ⊆ ball c R`
  (`R < R'`), `‖f‖ ≤ M` on the circle `‖z - c‖ = R` and `f c ≠ 0`, then for every `r < R`
  `#(Z ∩ closedBall c r) · log (R/r) ≤ log M − log ‖f c‖`. Read off
  `Jensen.jensen_formula_of_finite_zeros`.
* `ncard_mul_log_le_of_jensen` — the same with the radius `R ∈ [R₀, R')` chosen automatically
  so that no zero lies in the annulus `R ≤ ‖z − c‖ < R'` (only `‖f‖ ≤ M` on `ball c R'` is assumed).
* `isNontrivialZero_one_sub_conj` — the symmetry `ρ ↦ 1 − conj ρ` of the nontrivial zeros
  (same imaginary part, real part reflected in `1/2`); `finite_zeros_im_mem_Icc` etc.

**Proven from two explicit hypotheses** (the statements of the sibling modules
`ZetaGrowthNeg` / `ZetaLowerBound`, which do not exist yet), namely
`hgrowth : ∀ s, -1/2 ≤ Re s → Re s ≤ 2 → 2 ≤ |Im s| → ‖ζ s‖ ≤ C |Im s|^{3/2}` (with `0 ≤ C`) and
`hlow : ∀ t, 1/3 ≤ ‖ζ (3/2 + t i)‖`:

* `ncard_zeros_right_near_height_le` —
  `#{ρ : IsNontrivialZero ρ, 1/2 ≤ Re ρ, |Im ρ − T| ≤ 1} ≤ K C · log |T|` for `|T| ≥ 4`, with the
  explicit `K C = 5 (log (C + 3) + 6)`; disc `c = 3/2 + T i`, outer radius `2`, Jensen radius
  `≥ 19/10`, counting radius `3/2`.
* `ncard_zeros_near_height_le` — the full-strip count `≤ 2 K C log |T|` by the symmetry.
* `count_le_T_log_T` — `∃ C', ∀ T ≥ 2, #{ρ : IsNontrivialZero ρ, |Im ρ| ≤ T} ≤ C' T log T`.
* `zeroSumConvergence_hypotheses`, `summable_inv_sq_ordinates` — the hypotheses `hfin`, `hN` of
  `ZeroSumConvergence` hold for the ordinates of any injective enumeration of nontrivial zeros,
  hence `∑ 1/γ_n² < ∞` for an enumeration listed by non-decreasing `|γ_n| ≥ 2`.

**Not proven here:** `hgrowth` (growth of `ζ` on `-1/2 ≤ Re s ≤ 2`, which needs the functional
equation) and `hlow` (the lower bound `|ζ(3/2 + it)| ≥ ζ(3)/ζ(3/2) > 1/3`); nothing else is
assumed. Nothing is left unproven beyond those two hypotheses; no custom axioms.
-/

noncomputable section

open Metric Set Reduction
open scoped Real ComplexConjugate

namespace ZeroDensity

/-! ## The counting argument from Jensen's formula -/

open scoped Classical in
/-- **Zero counting from Jensen's formula (general form).** Let `f` be holomorphic on `ball c R'`,
`0 < r < R < R'`, let the finite set `Z ⊆ ball c R` be exactly the zero set of `f` in `ball c R'`,
let `‖f‖ ≤ M` on the circle `‖z - c‖ = R`, and `f c ≠ 0`. Then
`#(Z ∩ closedBall c r) · log (R / r) ≤ log M − log ‖f c‖`.
Proof: in Jensen's formula every zero contributes `m b · log (R / ‖b - c‖) ≥ 0`, and those in
`closedBall c r` contribute at least `log (R / r)`; the circle average is at most `log M`. -/
theorem card_mul_log_le_of_jensen {c : ℂ} {R R' r M : ℝ} (hr : 0 < r) (hrR : r < R)
    (hRR' : R < R') {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball c R')) (Z : Finset ℂ)
    (hZR : ∀ b ∈ Z, b ∈ ball c R) (hZ : ∀ z ∈ ball c R', f z = 0 ↔ z ∈ Z)
    (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (hfc : f c ≠ 0) :
    ((Z.filter fun b => b ∈ closedBall c r).card : ℝ) * Real.log (R / r)
      ≤ Real.log M - Real.log ‖f c‖ := by
  have hR : 0 < R := hr.trans hrR
  obtain ⟨m, hm, hJ⟩ := Jensen.jensen_formula_of_finite_zeros hR hRR' hf Z hZR hZ hfc
  have hsub : closedBall c R ⊆ ball c R' := closedBall_subset_ball hRR'
  -- `f` does not vanish on the circle
  have hfpos : ∀ θ : ℝ, 0 < ‖f (circleMap c R θ)‖ := by
    intro θ
    have hmem := circleMap_mem_closedBall c hR.le θ
    apply norm_pos_iff.mpr
    intro h0
    have hb := mem_ball_iff_norm.mp (hZR _ ((hZ _ (hsub hmem)).mp h0))
    rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hR] at hb
    exact lt_irrefl _ hb
  have hcont : Continuous (fun θ : ℝ => Real.log ‖f (circleMap c R θ)‖) := by
    have hfc' : Continuous (fun θ : ℝ => f (circleMap c R θ)) :=
      (hf.mono hsub).continuousOn.comp_continuous (continuous_circleMap c R)
        (fun θ => circleMap_mem_closedBall c hR.le θ)
    exact (continuous_norm.comp hfc').log (fun θ => (hfpos θ).ne')
  -- the circle average is at most `log M`
  have havg : (2 * π)⁻¹ *
      (∫ θ in (0 : ℝ)..(2 * π), Real.log ‖f (c + R * Complex.exp (θ * Complex.I))‖)
      ≤ Real.log M := by
    have hle : (∫ θ in (0 : ℝ)..(2 * π), Real.log ‖f (circleMap c R θ)‖)
        ≤ ∫ _ in (0 : ℝ)..(2 * π), Real.log M := by
      apply intervalIntegral.integral_mono_on Real.two_pi_pos.le
        (hcont.intervalIntegrable 0 (2 * π)) intervalIntegrable_const
      intro θ _
      exact Real.log_le_log (hfpos θ) (hM _ (circleMap_mem_sphere c hR.le θ))
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hle
    have h2π : 0 < (2 * π)⁻¹ := by positivity
    calc (2 * π)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * π), Real.log ‖f (c + R * Complex.exp (θ * Complex.I))‖)
        ≤ (2 * π)⁻¹ * (2 * π * Real.log M) := by
          apply mul_le_mul_of_nonneg_left _ h2π.le
          exact hle
      _ = Real.log M := by field_simp
  -- the points of `Z` are not `c`
  have hcZ : ∀ b ∈ Z, b ≠ c := by
    intro b hb h
    exact hfc ((hZ c (mem_ball_self (hR.trans hRR'))).mpr (h ▸ hb))
  have hterm_nonneg : ∀ b ∈ Z, 0 ≤ (m b : ℝ) * Real.log (R / ‖b - c‖) := by
    intro b hb
    apply mul_nonneg (Nat.cast_nonneg _)
    apply Real.log_nonneg
    rw [one_le_div (norm_pos_iff.mpr (sub_ne_zero.mpr (hcZ b hb)))]
    exact (mem_ball_iff_norm.mp (hZR b hb)).le
  have hterm_r : ∀ b ∈ Z.filter (fun b => b ∈ closedBall c r),
      Real.log (R / r) ≤ (m b : ℝ) * Real.log (R / ‖b - c‖) := by
    intro b hb
    obtain ⟨hbZ, hbr⟩ := Finset.mem_filter.mp hb
    have hbc : 0 < ‖b - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hcZ b hbZ))
    have hbr' : ‖b - c‖ ≤ r := mem_closedBall_iff_norm.mp hbr
    have h1 : Real.log (R / r) ≤ Real.log (R / ‖b - c‖) := by
      apply Real.log_le_log (div_pos hR hr)
      exact div_le_div_of_nonneg_left hR.le hbc hbr'
    have h2 : 0 ≤ Real.log (R / r) := Real.log_nonneg (by rw [one_le_div hr]; exact hrR.le)
    have hm1 : (1 : ℝ) ≤ m b := by exact_mod_cast hm b hbZ
    calc Real.log (R / r) ≤ Real.log (R / ‖b - c‖) := h1
      _ = 1 * Real.log (R / ‖b - c‖) := (one_mul _).symm
      _ ≤ (m b : ℝ) * Real.log (R / ‖b - c‖) :=
          mul_le_mul_of_nonneg_right hm1 (h2.trans h1)
  have hsum : ((Z.filter fun b => b ∈ closedBall c r).card : ℝ) * Real.log (R / r)
      ≤ ∑ b ∈ Z, (m b : ℝ) * Real.log (R / ‖b - c‖) := by
    calc ((Z.filter fun b => b ∈ closedBall c r).card : ℝ) * Real.log (R / r)
        = ∑ b ∈ Z.filter (fun b => b ∈ closedBall c r), Real.log (R / r) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ b ∈ Z.filter (fun b => b ∈ closedBall c r), (m b : ℝ) * Real.log (R / ‖b - c‖) :=
          Finset.sum_le_sum hterm_r
      _ ≤ ∑ b ∈ Z, (m b : ℝ) * Real.log (R / ‖b - c‖) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun b hb _ => hterm_nonneg b hb)
  linarith [hJ, havg, hsum]

open scoped Classical in
/-- **Zero counting from Jensen's formula, radius chosen automatically.** Let `f` be holomorphic
on `ball c R'` with finitely many zeros there, `0 < r < R₀ < R'`, `‖f‖ ≤ M` on `ball c R'` and
`f c ≠ 0`. Then `#{zeros of f in closedBall c r} · log (R₀ / r) ≤ log M − log ‖f c‖`.
A Jensen radius `R ∈ [R₀, R')` with no zeros in the annulus `R ≤ ‖z - c‖ < R'` exists because
the zero set is finite. -/
theorem ncard_mul_log_le_of_jensen {c : ℂ} {R₀ R' r M : ℝ} (hr : 0 < r) (hrR : r < R₀)
    (hRR' : R₀ < R') {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball c R'))
    (hfin : {z ∈ ball c R' | f z = 0}.Finite)
    (hM : ∀ z ∈ ball c R', ‖f z‖ ≤ M) (hfc : f c ≠ 0) :
    ({z ∈ closedBall c r | f z = 0}.ncard : ℝ) * Real.log (R₀ / r)
      ≤ Real.log M - Real.log ‖f c‖ := by
  set Z : Finset ℂ := hfin.toFinset with hZdef
  have hZmem : ∀ b ∈ Z, b ∈ ball c R' ∧ f b = 0 := fun b hb => hfin.mem_toFinset.mp hb
  have hZ : ∀ z ∈ ball c R', f z = 0 ↔ z ∈ Z := by
    intro z hz
    rw [hZdef, Set.Finite.mem_toFinset]
    exact ⟨fun h => ⟨hz, h⟩, fun h => h.2⟩
  -- choose the Jensen radius
  obtain ⟨R, hR₀R, hRR'', hZR⟩ : ∃ R : ℝ, R₀ ≤ R ∧ R < R' ∧ ∀ b ∈ Z, b ∈ ball c R := by
    rcases Z.eq_empty_or_nonempty with hZe | hZne
    · refine ⟨R₀, le_rfl, hRR', fun b hb => ?_⟩
      rw [hZe] at hb
      exact absurd hb (Finset.notMem_empty b)
    · obtain ⟨x, hxZ, hxmax⟩ := Z.exists_max_image (fun b => ‖b - c‖) hZne
      have hx : ‖x - c‖ < R' := mem_ball_iff_norm.mp (hZmem x hxZ).1
      refine ⟨max R₀ ((‖x - c‖ + R') / 2), le_max_left _ _, max_lt hRR' (by linarith), ?_⟩
      intro b hb
      rw [mem_ball_iff_norm]
      calc ‖b - c‖ ≤ ‖x - c‖ := hxmax b hb
        _ < (‖x - c‖ + R') / 2 := by linarith
        _ ≤ max R₀ ((‖x - c‖ + R') / 2) := le_max_right _ _
  have hM' : ∀ z ∈ sphere c R, ‖f z‖ ≤ M := fun z hz =>
    hM z (closedBall_subset_ball hRR'' (sphere_subset_closedBall hz))
  have hcore := card_mul_log_le_of_jensen hr (hrR.trans_le hR₀R) hRR'' hf Z hZR hZ hM' hfc
  have hrR' : closedBall c r ⊆ ball c R' := closedBall_subset_ball (hrR.trans hRR')
  have hset : {z ∈ closedBall c r | f z = 0} = ↑(Z.filter fun b => b ∈ closedBall c r) := by
    ext z
    simp only [Set.mem_ofPred_eq, Finset.coe_filter]
    constructor
    · rintro ⟨hz, hfz⟩
      exact ⟨(hZ z (hrR' hz)).mp hfz, hz⟩
    · rintro ⟨hzZ, hz⟩
      exact ⟨hz, (hZ z (hrR' hz)).mpr hzZ⟩
  rw [hset, Set.ncard_coe_finset]
  have hlog : Real.log (R₀ / r) ≤ Real.log (R / r) :=
    Real.log_le_log (div_pos (hr.trans hrR) hr) (div_le_div_of_nonneg_right hR₀R hr.le)
  calc ((Z.filter fun b => b ∈ closedBall c r).card : ℝ) * Real.log (R₀ / r)
      ≤ ((Z.filter fun b => b ∈ closedBall c r).card : ℝ) * Real.log (R / r) :=
        mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
    _ ≤ Real.log M - Real.log ‖f c‖ := hcore

/-! ## Elementary geometry and finiteness -/

/-- Euclidean bound on `‖z‖` from bounds on the real and imaginary parts. -/
theorem norm_le_of_re_im {z : ℂ} {a : ℝ} (ha : 0 ≤ a) (h : z.re ^ 2 + z.im ^ 2 ≤ a ^ 2) :
    ‖z‖ ≤ a := by
  rw [Complex.norm_def, Complex.normSq_apply, Real.sqrt_le_left ha]
  linarith [h]

/-- The nontrivial zeros with imaginary part in `[a, b]` form a finite set
(they lie in the compact rectangle `[0, 1] × [a, b]`). -/
theorem finite_zeros_im_mem_Icc (a b : ℝ) :
    {ρ : ℂ | IsNontrivialZero ρ ∧ a ≤ ρ.im ∧ ρ.im ≤ b}.Finite := by
  have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc a b) := isCompact_Icc.reProdIm isCompact_Icc
  refine (FiniteZeros.finite_nontrivialZeros_of_isCompact hK).subset ?_
  rintro ρ ⟨hρ, ha, hb⟩
  refine ⟨?_, hρ⟩
  rw [Complex.mem_reProdIm]
  obtain ⟨h0, h1⟩ := ZetaStrip.mem_strip_of_isNontrivialZero hρ
  exact ⟨⟨h0.le, h1.le⟩, ⟨ha, hb⟩⟩

/-- The nontrivial zeros of height at most `T` form a finite set. -/
theorem finite_zeros_abs_im_le (T : ℝ) :
    {ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im| ≤ T}.Finite :=
  (finite_zeros_im_mem_Icc (-T) T).subset
    (fun _ ⟨hρ, h⟩ => ⟨hρ, (abs_le.mp h).1, (abs_le.mp h).2⟩)

/-- The nontrivial zeros within height `1` of `T` form a finite set. -/
theorem finite_zeros_near_height (T : ℝ) :
    {ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im - T| ≤ 1}.Finite :=
  (finite_zeros_im_mem_Icc (T - 1) (T + 1)).subset
    (fun _ ⟨hρ, h⟩ => ⟨hρ, by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩)

/-! ## The symmetry `ρ ↦ 1 - conj ρ` -/

/-- **Reflection in the critical line.** If `ρ` is a nontrivial zero, so is `1 - conj ρ`
(`ZetaConj.isNontrivialZero_conj` followed by `ZeroSymmetry.isNontrivialZero_one_sub`). -/
theorem isNontrivialZero_one_sub_conj {ρ : ℂ} (h : IsNontrivialZero ρ) :
    IsNontrivialZero (1 - conj ρ) :=
  ZeroSymmetry.isNontrivialZero_one_sub (ZetaConj.isNontrivialZero_conj h)

/-- `Re (1 - conj ρ) = 1 - Re ρ`. -/
theorem one_sub_conj_re (ρ : ℂ) : (1 - conj ρ).re = 1 - ρ.re := by simp

/-- `Im (1 - conj ρ) = Im ρ`: the reflection preserves the height. -/
theorem one_sub_conj_im (ρ : ℂ) : (1 - conj ρ).im = ρ.im := by simp

/-! ## The local count near height `T` -/

/-- The explicit constant of the local zero count: `K C = 5 (log (C + 3) + 6)`. -/
def K (C : ℝ) : ℝ := 5 * (Real.log (C + 3) + 6)

/-- `K C ≥ 0` for `C ≥ 0`. -/
theorem K_nonneg {C : ℝ} (hC : 0 ≤ C) : 0 ≤ K C := by
  unfold K
  have : 0 ≤ Real.log (C + 3) := Real.log_nonneg (by linarith)
  linarith

/-- `‖ζ 2‖ = π²/6 ≤ 3`. -/
theorem norm_riemannZeta_two_le : ‖riemannZeta 2‖ ≤ 3 := by
  rw [riemannZeta_two]
  have : ((π : ℂ) ^ 2 / 6) = ((π ^ 2 / 6 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  nlinarith [Real.pi_le_four, Real.pi_pos]

/-- **Local zero count, right half of the strip (hypothesis-dependent).** Under the growth
hypothesis `hgrowth` (`‖ζ s‖ ≤ C |Im s|^{3/2}` on `-1/2 ≤ Re s ≤ 2`, `|Im s| ≥ 2`) and the
lower bound `hlow` (`‖ζ (3/2 + it)‖ ≥ 1/3`), for `|T| ≥ 4` the number of nontrivial zeros `ρ`
with `1/2 ≤ Re ρ` and `|Im ρ − T| ≤ 1` is at most `K C · log |T|`, `K C = 5 (log (C + 3) + 6)`.
Jensen's formula is applied to `ζ` on the disc of centre `c = 3/2 + T i` and radius `2`
(which avoids the pole and stays in `Re s > -1/2`), with counting radius `3/2` and Jensen radius
`≥ 19/10`; the zeros in question lie in `closedBall c (3/2)` since `Re ρ < 1`. -/
theorem ncard_zeros_right_near_height_le (C : ℝ) (hC : 0 ≤ C)
    (hgrowth : ∀ s : ℂ, -1/2 ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * |s.im| ^ (3/2 : ℝ))
    (hlow : ∀ t : ℝ, 1/3 ≤ ‖riemannZeta (3/2 + t * Complex.I)‖)
    (T : ℝ) (hT : 4 ≤ |T|) :
    ({ρ : ℂ | IsNontrivialZero ρ ∧ 1/2 ≤ ρ.re ∧ |ρ.im - T| ≤ 1}.ncard : ℝ)
      ≤ K C * Real.log |T| := by
  set c : ℂ := 3/2 + T * Complex.I with hc
  have hcre : c.re = 3/2 := by simp [hc]
  have hcim : c.im = T := by simp [hc]
  have hTpos : 0 < |T| := by linarith
  -- geometry of the disc `ball c 2`
  have hmem : ∀ z ∈ ball c 2, |z.re - 3/2| < 2 ∧ |z.im - T| < 2 := by
    intro z hz
    have hz' : ‖z - c‖ < 2 := mem_ball_iff_norm.mp hz
    constructor
    · calc |z.re - 3/2| = |(z - c).re| := by rw [Complex.sub_re, hcre]
        _ ≤ ‖z - c‖ := by skip; exact Complex.abs_re_le_norm _
        _ < 2 := hz'
    · calc |z.im - T| = |(z - c).im| := by rw [Complex.sub_im, hcim]
        _ ≤ ‖z - c‖ := by skip; exact Complex.abs_im_le_norm _
        _ < 2 := hz'
  have hne1 : ∀ z ∈ ball c 2, z ≠ 1 := by
    intro z hz h1
    have := (hmem z hz).2
    rw [h1, Complex.one_im, zero_sub, abs_neg] at this
    linarith
  have hf : DifferentiableOn ℂ riemannZeta (ball c 2) := fun z hz =>
    (differentiableAt_riemannZeta (hne1 z hz)).differentiableWithinAt
  -- the zero set in the disc is finite
  have h1K : (1 : ℂ) ∉ closedBall c 2 := by
    intro h
    have h' : ‖(1 : ℂ) - c‖ ≤ 2 := mem_closedBall_iff_norm.mp h
    have : |T| ≤ 2 := by
      calc |T| = |((1 : ℂ) - c).im| := by
            rw [Complex.sub_im, Complex.one_im, hcim, zero_sub, abs_neg]
        _ ≤ ‖(1 : ℂ) - c‖ := by skip; exact Complex.abs_im_le_norm _
        _ ≤ 2 := h'
    linarith
  have hfin : {z ∈ ball c 2 | riemannZeta z = 0}.Finite :=
    (FiniteZeros.finite_zeros_of_isCompact (isCompact_closedBall c 2) h1K).subset
      (fun z hz => ⟨ball_subset_closedBall hz.1, hz.2⟩)
  -- the bound `M` on the disc
  set M : ℝ := (C + 3) * (|T| + 2) ^ (3/2 : ℝ) with hMdef
  have hpow0 : 0 < (|T| + 2) ^ (3/2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hpow1 : 1 ≤ (|T| + 2) ^ (3/2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hM : ∀ z ∈ ball c 2, ‖riemannZeta z‖ ≤ M := by
    intro z hz
    obtain ⟨hzre, hzim⟩ := hmem z hz
    have hzre' := abs_lt.mp hzre
    have hzim2 : 2 ≤ |z.im| := by
      have h1 := abs_sub_abs_le_abs_sub T z.im
      rw [abs_sub_comm] at h1
      linarith
    have hzimT : |z.im| ≤ |T| + 2 := by
      have h1 := abs_sub_abs_le_abs_sub z.im T
      linarith
    by_cases hre2 : z.re ≤ 2
    · calc ‖riemannZeta z‖ ≤ C * |z.im| ^ (3/2 : ℝ) := hgrowth z (by linarith) hre2 hzim2
        _ ≤ C * (|T| + 2) ^ (3/2 : ℝ) := by
            apply mul_le_mul_of_nonneg_left _ hC
            exact Real.rpow_le_rpow (abs_nonneg _) hzimT (by norm_num)
        _ ≤ M := by
            rw [hMdef]
            have : 0 ≤ 3 * (|T| + 2) ^ (3/2 : ℝ) := by positivity
            linarith
    · push_neg at hre2
      calc ‖riemannZeta z‖ ≤ ‖riemannZeta ((1 + 1 : ℝ) : ℂ)‖ :=
            ZetaGrowth.norm_zeta_le_of_re_ge one_pos (by linarith)
        _ = ‖riemannZeta 2‖ := by norm_num
        _ ≤ 3 := norm_riemannZeta_two_le
        _ ≤ M := by
            rw [hMdef]
            have := mul_le_mul_of_nonneg_left hpow1 (by linarith : (0 : ℝ) ≤ C + 3)
            linarith
  -- `ζ c ≠ 0`, with `log ‖ζ c‖ ≥ -log 3`
  have hζc : 1/3 ≤ ‖riemannZeta c‖ := hlow T
  have hfc : riemannZeta c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hζc
    norm_num at hζc
  have hlogc : -Real.log 3 ≤ Real.log ‖riemannZeta c‖ := by
    have := Real.log_le_log (by norm_num) hζc
    rwa [one_div, Real.log_inv] at this
  -- Jensen
  have hJ := ncard_mul_log_le_of_jensen (c := c) (R₀ := 19/10) (R' := 2) (r := 3/2) (M := M)
    (by norm_num) (by norm_num) (by norm_num) hf hfin hM hfc
  -- the zeros in question lie in `closedBall c (3/2)`
  have hsub : {ρ : ℂ | IsNontrivialZero ρ ∧ 1/2 ≤ ρ.re ∧ |ρ.im - T| ≤ 1}
      ⊆ {z ∈ closedBall c (3/2) | riemannZeta z = 0} := by
    rintro ρ ⟨hρ, hre, him⟩
    refine ⟨?_, hρ.1⟩
    rw [mem_closedBall_iff_norm]
    apply norm_le_of_re_im (by norm_num)
    rw [Complex.sub_re, Complex.sub_im, hcre, hcim]
    have hre1 := ZetaStrip.re_lt_one_of_isNontrivialZero hρ
    have h1 : (ρ.re - 3/2) ^ 2 ≤ 1 :=
      (sq_le_one_iff_abs_le_one _).mpr (abs_le.mpr ⟨by linarith, by linarith⟩)
    have h2 : (ρ.im - T) ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr him
    linarith
  have hfin' : {z ∈ closedBall c (3/2) | riemannZeta z = 0}.Finite :=
    hfin.subset (fun z hz => ⟨closedBall_subset_ball (by norm_num) hz.1, hz.2⟩)
  have hcard : ({ρ : ℂ | IsNontrivialZero ρ ∧ 1/2 ≤ ρ.re ∧ |ρ.im - T| ≤ 1}.ncard : ℝ)
      ≤ ({z ∈ closedBall c (3/2) | riemannZeta z = 0}.ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hsub hfin'
  -- numerics
  have hlogM : Real.log M ≤ Real.log (C + 3) + 3/2 * (Real.log 2 + Real.log |T|) := by
    rw [hMdef, Real.log_mul (by linarith : (0 : ℝ) < C + 3).ne' hpow0.ne',
      Real.log_rpow (by linarith)]
    have h1 : Real.log (|T| + 2) ≤ Real.log (2 * |T|) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) hTpos.ne'] at h1
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog3 : Real.log 3 ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hlogT : 1 ≤ Real.log |T| := by
    rw [Real.le_log_iff_exp_le hTpos]
    linarith [Real.exp_one_lt_d9]
  have hlogC : 0 ≤ Real.log (C + 3) := Real.log_nonneg (by linarith)
  have hprod : Real.log (C + 3) ≤ Real.log (C + 3) * Real.log |T| :=
    le_mul_of_one_le_right hlogC hlogT
  have hlog1915 : (1 : ℝ) / 5 ≤ Real.log (19/10 / (3/2)) := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 19/10 / (3/2))
    norm_num at this ⊢
    linarith
  set N : ℝ := ({ρ : ℂ | IsNontrivialZero ρ ∧ 1/2 ≤ ρ.re ∧ |ρ.im - T| ≤ 1}.ncard : ℝ) with hN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hN1 : N * (1/5) ≤ N * Real.log (19/10 / (3/2)) :=
    mul_le_mul_of_nonneg_left hlog1915 hN0
  have hN2 : N * Real.log (19/10 / (3/2)) ≤ Real.log M - Real.log ‖riemannZeta c‖ :=
    calc N * Real.log (19/10 / (3/2))
        ≤ ({z ∈ closedBall c (3/2) | riemannZeta z = 0}.ncard : ℝ) * Real.log (19/10 / (3/2)) :=
          mul_le_mul_of_nonneg_right hcard (by linarith)
      _ ≤ Real.log M - Real.log ‖riemannZeta c‖ := hJ
  have key : N * (1/5) ≤ (Real.log (C + 3) + 6) * Real.log |T| := by
    linarith
  unfold K
  linarith

/-- **Local zero count, full strip (hypothesis-dependent).** Under `hgrowth`, `hlow`, for
`|T| ≥ 4` the number of nontrivial zeros with `|Im ρ − T| ≤ 1` is at most `2 K C · log |T|`:
the zeros with `Re ρ < 1/2` inject into those with `Re ρ ≥ 1/2` via `ρ ↦ 1 − conj ρ`. -/
theorem ncard_zeros_near_height_le (C : ℝ) (hC : 0 ≤ C)
    (hgrowth : ∀ s : ℂ, -1/2 ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * |s.im| ^ (3/2 : ℝ))
    (hlow : ∀ t : ℝ, 1/3 ≤ ‖riemannZeta (3/2 + t * Complex.I)‖)
    (T : ℝ) (hT : 4 ≤ |T|) :
    ({ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im - T| ≤ 1}.ncard : ℝ) ≤ 2 * K C * Real.log |T| := by
  have hfinP : {ρ : ℂ | IsNontrivialZero ρ ∧ 1/2 ≤ ρ.re ∧ |ρ.im - T| ≤ 1}.Finite :=
    (finite_zeros_near_height T).subset (fun _ ⟨hρ, _, him⟩ => ⟨hρ, him⟩)
  have hfinM : {ρ : ℂ | IsNontrivialZero ρ ∧ ρ.re < 1/2 ∧ |ρ.im - T| ≤ 1}.Finite :=
    (finite_zeros_near_height T).subset (fun _ ⟨hρ, _, him⟩ => ⟨hρ, him⟩)
  have hunion : {ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im - T| ≤ 1}
      ⊆ {ρ : ℂ | IsNontrivialZero ρ ∧ 1/2 ≤ ρ.re ∧ |ρ.im - T| ≤ 1}
        ∪ {ρ : ℂ | IsNontrivialZero ρ ∧ ρ.re < 1/2 ∧ |ρ.im - T| ≤ 1} := by
    rintro ρ ⟨hρ, him⟩
    by_cases h : 1/2 ≤ ρ.re
    · exact Or.inl ⟨hρ, h, him⟩
    · exact Or.inr ⟨hρ, lt_of_not_ge h, him⟩
  have hP := ncard_zeros_right_near_height_le C hC hgrowth hlow T hT
  have hM : {ρ : ℂ | IsNontrivialZero ρ ∧ ρ.re < 1/2 ∧ |ρ.im - T| ≤ 1}.ncard
      ≤ {ρ : ℂ | IsNontrivialZero ρ ∧ 1/2 ≤ ρ.re ∧ |ρ.im - T| ≤ 1}.ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun ρ => 1 - conj ρ) ?_ ?_ hfinP
    · rintro ρ ⟨hρ, hre, him⟩
      refine ⟨isNontrivialZero_one_sub_conj hρ, ?_, ?_⟩
      · rw [one_sub_conj_re]; linarith
      · rw [one_sub_conj_im]; exact him
    · intro ρ _ ρ' _ h
      exact (starRingEnd ℂ).injective (sub_right_inj.mp h)
  have htot : {ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im - T| ≤ 1}.ncard
      ≤ {ρ : ℂ | IsNontrivialZero ρ ∧ 1/2 ≤ ρ.re ∧ |ρ.im - T| ≤ 1}.ncard
        + {ρ : ℂ | IsNontrivialZero ρ ∧ ρ.re < 1/2 ∧ |ρ.im - T| ≤ 1}.ncard :=
    (Set.ncard_le_ncard hunion (hfinP.union hfinM)).trans (Set.ncard_union_le _ _)
  have h1 : ({ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im - T| ≤ 1}.ncard : ℝ)
      ≤ ({ρ : ℂ | IsNontrivialZero ρ ∧ 1/2 ≤ ρ.re ∧ |ρ.im - T| ≤ 1}.ncard : ℝ)
        + ({ρ : ℂ | IsNontrivialZero ρ ∧ ρ.re < 1/2 ∧ |ρ.im - T| ≤ 1}.ncard : ℝ) := by
    exact_mod_cast htot
  have h2 : ({ρ : ℂ | IsNontrivialZero ρ ∧ ρ.re < 1/2 ∧ |ρ.im - T| ≤ 1}.ncard : ℝ)
      ≤ ({ρ : ℂ | IsNontrivialZero ρ ∧ 1/2 ≤ ρ.re ∧ |ρ.im - T| ≤ 1}.ncard : ℝ) := by
    exact_mod_cast hM
  linarith

/-! ## The global count `N(T) = O(T log T)` -/

/-- **One unit step in height.** Under `hgrowth`, `hlow`, for `t ≥ 4`,
`#{|Im ρ| ≤ t + 1} ≤ #{|Im ρ| ≤ t} + 4 K C log (t + 1)`: the new zeros lie within height `1`
of `t + 1` or of `−(t + 1)`. -/
theorem ncard_zeros_step (C : ℝ) (hC : 0 ≤ C)
    (hgrowth : ∀ s : ℂ, -1/2 ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * |s.im| ^ (3/2 : ℝ))
    (hlow : ∀ t : ℝ, 1/3 ≤ ‖riemannZeta (3/2 + t * Complex.I)‖)
    (t : ℝ) (ht : 4 ≤ t) :
    ({ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im| ≤ t + 1}.ncard : ℝ)
      ≤ ({ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im| ≤ t}.ncard : ℝ) + 4 * K C * Real.log (t + 1) := by
  have hsub : {ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im| ≤ t + 1}
      ⊆ {ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im| ≤ t}
        ∪ ({ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im - (t + 1)| ≤ 1}
          ∪ {ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im - (-(t + 1))| ≤ 1}) := by
    rintro ρ ⟨hρ, him⟩
    by_cases h : |ρ.im| ≤ t
    · exact Or.inl ⟨hρ, h⟩
    · push_neg at h
      refine Or.inr ?_
      rcases le_or_gt 0 ρ.im with hpos | hneg
      · refine Or.inl ⟨hρ, ?_⟩
        rw [abs_of_nonneg hpos] at h him
        rw [abs_le]; constructor <;> linarith
      · refine Or.inr ⟨hρ, ?_⟩
        rw [abs_of_neg hneg] at h him
        rw [abs_le]; constructor <;> linarith
  have hfin1 := finite_zeros_abs_im_le t
  have hfin2 := finite_zeros_near_height (t + 1)
  have hfin3 := finite_zeros_near_height (-(t + 1))
  have hc1 := Set.ncard_le_ncard hsub (hfin1.union (hfin2.union hfin3))
  have hc2 := Set.ncard_union_le {ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im| ≤ t}
    ({ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im - (t + 1)| ≤ 1}
      ∪ {ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im - (-(t + 1))| ≤ 1})
  have hc3 := Set.ncard_union_le {ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im - (t + 1)| ≤ 1}
    {ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im - (-(t + 1))| ≤ 1}
  have hb2 := ncard_zeros_near_height_le C hC hgrowth hlow (t + 1)
    (by rw [abs_of_nonneg (by linarith)]; linarith)
  have hb3 := ncard_zeros_near_height_le C hC hgrowth hlow (-(t + 1))
    (by rw [abs_neg, abs_of_nonneg (by linarith)]; linarith)
  rw [abs_of_nonneg (by linarith)] at hb2
  rw [abs_neg, abs_of_nonneg (by linarith)] at hb3
  have hcast : ({ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im| ≤ t + 1}.ncard : ℝ)
      ≤ ({ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im| ≤ t}.ncard : ℝ)
        + (({ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im - (t + 1)| ≤ 1}.ncard : ℝ)
          + ({ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im - (-(t + 1))| ≤ 1}.ncard : ℝ)) := by
    exact_mod_cast hc1.trans (hc2.trans (Nat.add_le_add_left hc3 _))
  linarith

/-- **Height `4 + n` (hypothesis-dependent).** Under `hgrowth`, `hlow`, for every `n : ℕ`,
`#{|Im ρ| ≤ 4 + n} ≤ #{|Im ρ| ≤ 4} + n · 4 K C log (4 + n)`. Induction on `n` with
`ncard_zeros_step`. -/
theorem ncard_zeros_le_of_nat (C : ℝ) (hC : 0 ≤ C)
    (hgrowth : ∀ s : ℂ, -1/2 ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * |s.im| ^ (3/2 : ℝ))
    (hlow : ∀ t : ℝ, 1/3 ≤ ‖riemannZeta (3/2 + t * Complex.I)‖) (n : ℕ) :
    ({ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im| ≤ 4 + n}.ncard : ℝ)
      ≤ ({ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im| ≤ 4}.ncard : ℝ)
        + n * (4 * K C * Real.log (4 + n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (4 : ℝ) + ((n + 1 : ℕ) : ℝ) = (4 + n) + 1 := by push_cast; ring
    rw [e]
    have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    have hstep := ncard_zeros_step C hC hgrowth hlow (4 + n) (by linarith)
    have hlog : Real.log (4 + n) ≤ Real.log (4 + n + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    have hK := K_nonneg hC
    have hprod := mul_nonneg (mul_nonneg hn0 hK) (sub_nonneg.mpr hlog)
    push_cast
    linarith

/-- **`N(T) = O(T log T)` (hypothesis-dependent).** Under `hgrowth`, `hlow`, there is a constant
`C'` (namely `#{|Im ρ| ≤ 4} + 24 K C`) with `#{ρ : IsNontrivialZero ρ, |Im ρ| ≤ T} ≤ C' T log T`
for every `T ≥ 2`. -/
theorem count_le_T_log_T (C : ℝ) (hC : 0 ≤ C)
    (hgrowth : ∀ s : ℂ, -1/2 ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * |s.im| ^ (3/2 : ℝ))
    (hlow : ∀ t : ℝ, 1/3 ≤ ‖riemannZeta (3/2 + t * Complex.I)‖) :
    ∃ C' : ℝ, ∀ T : ℝ, 2 ≤ T →
      ({ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im| ≤ T}.ncard : ℝ) ≤ C' * T * Real.log T := by
  refine ⟨({ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im| ≤ 4}.ncard : ℝ) + 24 * K C, ?_⟩
  intro T hT
  set A : ℝ := ({ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im| ≤ 4}.ncard : ℝ) with hA
  have hA0 : 0 ≤ A := Nat.cast_nonneg _
  have hK := K_nonneg hC
  set n : ℕ := ⌈T⌉₊ with hn
  have hTn : T ≤ n := Nat.le_ceil T
  have hnT : (n : ℝ) < T + 1 := Nat.ceil_lt_add_one (by linarith)
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  have hsub : {ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im| ≤ T}
      ⊆ {ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im| ≤ 4 + n} :=
    fun _ ⟨hρ, h⟩ => ⟨hρ, by linarith⟩
  have h1 : ({ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im| ≤ T}.ncard : ℝ)
      ≤ ({ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im| ≤ 4 + n}.ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hsub (finite_zeros_abs_im_le _)
  have h2 : ({ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im| ≤ 4 + n}.ncard : ℝ)
      ≤ A + n * (4 * K C * Real.log (4 + n)) :=
    ncard_zeros_le_of_nat C hC hgrowth hlow n
  -- numerics
  have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hlog2 : 1/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogT0 : 1/2 ≤ Real.log T := hlog2.trans hlogT
  have hlogn : Real.log (4 + n) ≤ 3 * Real.log T := by
    have hcube : 0 ≤ T * ((T - 2) * (T + 2)) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
    have h4n : (4 : ℝ) + n ≤ T ^ 3 := by linarith
    calc Real.log (4 + n) ≤ Real.log (T ^ 3) := Real.log_le_log (by positivity) h4n
      _ = 3 * Real.log T := by rw [Real.log_pow]; push_cast; ring
  have hn2T : (n : ℝ) ≤ 2 * T := by linarith
  have hTlog : 1 ≤ T * Real.log T := by
    have := mul_nonneg (sub_nonneg.mpr hT) (sub_nonneg.mpr hlogT0)
    linarith
  have hprod : (n : ℝ) * (4 * K C * Real.log (4 + n))
      ≤ (2 * T) * (4 * K C * (3 * Real.log T)) := by
    apply mul_le_mul hn2T _ _ (by linarith)
    · exact mul_le_mul_of_nonneg_left hlogn (by linarith)
    · exact mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
  have hA1 : A ≤ A * (T * Real.log T) := le_mul_of_one_le_right hA0 hTlog
  calc ({ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im| ≤ T}.ncard : ℝ)
      ≤ A + n * (4 * K C * Real.log (4 + n)) := h1.trans h2
    _ ≤ A * (T * Real.log T) + (2 * T) * (4 * K C * (3 * Real.log T)) := by linarith
    _ = (A + 24 * K C) * T * Real.log T := by ring

/-! ## Connection to `ZeroSumConvergence` -/

/-- For an injective enumeration `zeros : ℕ → ℂ` of nontrivial zeros, only finitely many
indices have height at most `T` (the hypothesis `hfin` of `ZeroSumConvergence`). -/
theorem finite_index_of_height (zeros : ℕ → ℂ) (hinj : Function.Injective zeros)
    (hz : ∀ n, IsNontrivialZero (zeros n)) (T : ℝ) :
    {n : ℕ | |(zeros n).im| ≤ T}.Finite := by
  have h : {n : ℕ | |(zeros n).im| ≤ T}
      = zeros ⁻¹' {ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im| ≤ T} := by
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    exact ⟨fun h => ⟨hz n, h⟩, fun h => h.2⟩
  rw [h]
  exact (finite_zeros_abs_im_le T).preimage hinj.injOn

/-- The counting function of the ordinates of an injective enumeration of nontrivial zeros is
bounded by the number of nontrivial zeros of height at most `T`. -/
theorem count_le_ncard (zeros : ℕ → ℂ) (hinj : Function.Injective zeros)
    (hz : ∀ n, IsNontrivialZero (zeros n)) (T : ℝ) :
    ZeroSumConvergence.count (fun n => (zeros n).im) T
      ≤ {ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im| ≤ T}.ncard := by
  unfold ZeroSumConvergence.count
  exact Set.ncard_le_ncard_of_injOn zeros (fun n hn => ⟨hz n, hn⟩) hinj.injOn
    (finite_zeros_abs_im_le T)

/-- **The hypotheses of `ZeroSumConvergence` (hypothesis-dependent).** Under `hgrowth`, `hlow`,
for every injective enumeration `zeros : ℕ → ℂ` of nontrivial zeros, the ordinates
`γ n = Im (zeros n)` satisfy `hfin` (finitely many below any height) and `hN`
(`count γ T ≤ C' T log T` for `T ≥ 2`). -/
theorem zeroSumConvergence_hypotheses (C : ℝ) (hC : 0 ≤ C)
    (hgrowth : ∀ s : ℂ, -1/2 ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * |s.im| ^ (3/2 : ℝ))
    (hlow : ∀ t : ℝ, 1/3 ≤ ‖riemannZeta (3/2 + t * Complex.I)‖)
    (zeros : ℕ → ℂ) (hinj : Function.Injective zeros) (hz : ∀ n, IsNontrivialZero (zeros n)) :
    (∀ T, {n : ℕ | |(zeros n).im| ≤ T}.Finite) ∧
    ∃ C' : ℝ, ∀ T ≥ (2 : ℝ),
      (ZeroSumConvergence.count (fun n => (zeros n).im) T : ℝ) ≤ C' * T * Real.log T := by
  refine ⟨finite_index_of_height zeros hinj hz, ?_⟩
  obtain ⟨C', hC'⟩ := count_le_T_log_T C hC hgrowth hlow
  refine ⟨C', fun T hT => ?_⟩
  calc (ZeroSumConvergence.count (fun n => (zeros n).im) T : ℝ)
      ≤ ({ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im| ≤ T}.ncard : ℝ) := by
        exact_mod_cast count_le_ncard zeros hinj hz T
    _ ≤ C' * T * Real.log T := hC' T hT

/-- **`∑ 1/γ_n² < ∞` (hypothesis-dependent).** Under `hgrowth`, `hlow`, for an injective
enumeration of nontrivial zeros listed by non-decreasing height, all of height `≥ 2`, the series
`∑ 1 / (Im (zeros n))²` converges (`ZeroSumConvergence.summable_inv_sq_of_count_bound`). -/
theorem summable_inv_sq_ordinates (C : ℝ) (hC : 0 ≤ C)
    (hgrowth : ∀ s : ℂ, -1/2 ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C * |s.im| ^ (3/2 : ℝ))
    (hlow : ∀ t : ℝ, 1/3 ≤ ‖riemannZeta (3/2 + t * Complex.I)‖)
    (zeros : ℕ → ℂ) (hinj : Function.Injective zeros) (hz : ∀ n, IsNontrivialZero (zeros n))
    (hγ : ∀ n, 2 ≤ |(zeros n).im|) (hmono : Monotone (fun n => |(zeros n).im|)) :
    Summable (fun n => 1 / ((zeros n).im) ^ 2) := by
  obtain ⟨hfin, C', hN⟩ := zeroSumConvergence_hypotheses C hC hgrowth hlow zeros hinj hz
  exact ZeroSumConvergence.summable_inv_sq_of_count_bound (fun n => (zeros n).im) C' hγ hmono
    hfin hN

end ZeroDensity

end
