import PrincipalPartDischarge
import ZeroDensityUnconditional
import ZeroDensity
import ZeroSumConvergence
import ZerosCountable
import FiniteZeros
import ZetaStrip
import TestFunctions
import Reduction
import Mathlib

/-!
# The zero side as a convergent sum with multiplicities, and its truncations

The contour-shift identity (`PrincipalPartDischarge.contour_shift_rectangle_of_G`) produces, at
height `T`, the finite sum `∑ ρ ∈ zeroFinset (3/2) T, zetaOrder ρ · Gt a g ρ` over the zeros of
`ζ` in the rectangle, weighted by their orders. This file turns the zero side into a convergent
series and proves that the truncations converge to it as `T → ∞`.

**Proven (no custom axioms):**

* `MultEnum zeros` — the notion of an *enumeration with multiplicity* `zeros : ι → ℂ` of the
  nontrivial zeros: every term is a nontrivial zero, every nontrivial zero `ρ` occurs exactly
  `zetaOrder ρ` times, and finitely many indices lie below any height.
* `sum_order_mul_log_le_of_jensen` — Jensen's zero count **with multiplicities** (the
  multiplicities of `Jensen.exists_factorization_of_finite_zeros` are the local orders, by the
  uniqueness of the order, `order_unique`).
* `sum_zetaOrder_near_height_le` — `∑ zetaOrder ρ ≤ 300 log |T|` over the zeros with
  `|Im ρ − T| ≤ 1`, `|T| ≥ 4` (whole strip in one disc: no reflection symmetry needed).
* `exists_bound_sum_zetaOrder_div_sq` — `∑ zetaOrder ρ / (Im ρ)²` is uniformly bounded over
  finite sets of nontrivial zeros (band decomposition against `∑ log k / k²`).
* `summable_inv_sq_im`, `summable_norm_Gt`, `summable_Gt` — for any enumeration with
  multiplicity and any test function, `∑ Gt a g (zeros i)` converges absolutely.
* `sum_zeroFinset_eq` — the truncation identity: the weighted finset sum at height `T ≥ 0` is the
  sum over the indices of height `≤ T`.
* `tendsto_sum_zeroFinset` — the truncations along any heights `T k → ∞` converge to
  `∑' i, Gt a g (zeros i)` (Tannery's theorem).
* `multEnum_canonical` — an enumeration with multiplicity exists (index type `Index`),
  unconditionally; `zero_side_canonical` packages the results for it.

**Hypothesis-dependent:** `exists_multEnum_nat` / `zero_side_nat` — an enumeration indexed by
`ℕ` needs infinitely many nontrivial zeros (`hinf`), which is not proven in this project.

**Not proven:** nothing about the value of the limit (the explicit formula itself).
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Topology Set Metric Reduction PrincipalPartDischarge TestFunctions
open scoped Real Interval

namespace ZeroSumLimit

/-! ## Enumerations with multiplicity -/

/-- An *enumeration with multiplicity* of the nontrivial zeros of `ζ`, indexed by `ι`: every term
is a nontrivial zero, every nontrivial zero `ρ` occurs exactly `zetaOrder ρ` times, and only
finitely many indices lie below any given height. -/
structure MultEnum {ι : Type*} (zeros : ι → ℂ) : Prop where
  nontrivial : ∀ i, IsNontrivialZero (zeros i)
  mult : ∀ ρ, IsNontrivialZero ρ → {i | zeros i = ρ}.ncard = zetaOrder ρ
  finite : ∀ T : ℝ, {i | |(zeros i).im| ≤ T}.Finite

namespace MultEnum

/-- The fibre over any point is finite. -/
theorem fiber_finite {ι : Type*} {zeros : ι → ℂ} (h : MultEnum zeros) (ρ : ℂ) :
    {i | zeros i = ρ}.Finite :=
  (h.finite |ρ.im|).subset fun i hi => by
    simp only [mem_setOf_eq] at hi ⊢
    rw [hi]

/-- Every nontrivial zero occurs. -/
theorem exists_index {ι : Type*} {zeros : ι → ℂ} (h : MultEnum zeros) {ρ : ℂ}
    (hρ : IsNontrivialZero ρ) : ∃ i, zeros i = ρ := by
  have hpos : 0 < {i | zeros i = ρ}.ncard := by
    rw [h.mult ρ hρ]
    exact zetaOrder_pos hρ.2.2 hρ.1
  exact (Set.ncard_pos (h.fiber_finite ρ)).mp hpos

/-- In any finite index set, `ρ` occurs at most `zetaOrder ρ` times. -/
theorem card_filter_le {ι : Type*} {zeros : ι → ℂ} (h : MultEnum zeros) (s : Finset ι) {ρ : ℂ}
    (hρ : IsNontrivialZero ρ) :
    (s.filter fun i => zeros i = ρ).card ≤ zetaOrder ρ := by
  rw [← h.mult ρ hρ, ← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard ?_ (h.fiber_finite ρ)
  intro i hi
  rw [Finset.mem_coe, Finset.mem_filter] at hi
  exact hi.2

/-- Among the indices of height `≤ T`, a nontrivial zero `ρ` with `|Im ρ| ≤ T` occurs exactly
`zetaOrder ρ` times. -/
theorem card_filter_eq {ι : Type*} {zeros : ι → ℂ} (h : MultEnum zeros) {T : ℝ} {ρ : ℂ}
    (hρ : IsNontrivialZero ρ) (hT : |ρ.im| ≤ T) :
    ((h.finite T).toFinset.filter fun i => zeros i = ρ).card = zetaOrder ρ := by
  rw [← h.mult ρ hρ, ← Set.ncard_coe_finset]
  congr 1
  ext i
  simp only [Finset.coe_filter, Set.Finite.mem_toFinset, mem_setOf_eq]
  constructor
  · exact fun hi => hi.2
  · intro hi
    refine ⟨?_, hi⟩
    rw [hi]
    exact hT

/-- Transport along a bijection of index types. -/
theorem comp_equiv {ι κ : Type*} {zeros : ι → ℂ} (h : MultEnum zeros) (e : κ ≃ ι) :
    MultEnum (zeros ∘ e) where
  nontrivial i := h.nontrivial (e i)
  mult ρ hρ := by
    have hset : {k | (zeros ∘ e) k = ρ} = e ⁻¹' {i | zeros i = ρ} := rfl
    rw [hset, Set.ncard_preimage_of_injective_subset_range e.injective
      (fun i _ => e.surjective i)]
    exact h.mult ρ hρ
  finite T := by
    have hset : {k | |((zeros ∘ e) k).im| ≤ T} = e ⁻¹' {i | |(zeros i).im| ≤ T} := rfl
    rw [hset]
    exact (h.finite T).preimage e.injective.injOn

end MultEnum

/-! ## Jensen's formula with multiplicities -/

/-- **Uniqueness of the local order.** Two local factorisations `f = (· − b)^n · G`,
`f = (· − b)^{n'} · G'` with `G b ≠ 0 ≠ G' b` have `n = n'`. -/
theorem order_unique {f G G' : ℂ → ℂ} {b : ℂ} {n n' : ℕ} (hf : AnalyticAt ℂ f b)
    (hG : AnalyticAt ℂ G b) (hG0 : G b ≠ 0) (hfG : ∀ᶠ z in 𝓝 b, f z = (z - b) ^ n * G z)
    (hG' : AnalyticAt ℂ G' b) (hG0' : G' b ≠ 0)
    (hfG' : ∀ᶠ z in 𝓝 b, f z = (z - b) ^ n' * G' z) : n = n' := by
  have h1 : analyticOrderAt f b = n :=
    hf.analyticOrderAt_eq_natCast.mpr ⟨G, hG, hG0, by simpa only [smul_eq_mul] using hfG⟩
  have h2 : analyticOrderAt f b = n' :=
    hf.analyticOrderAt_eq_natCast.mpr ⟨G', hG', hG0', by simpa only [smul_eq_mul] using hfG'⟩
  exact ENat.natCast_inj.mp (h1.symm.trans h2)

open scoped Classical in
/-- **Jensen zero count with multiplicities (explicit circle radius).** Let `f` be holomorphic on
`ball c R'`, `0 < r < R < R'`, let the finite set `Z ⊆ ball c R` be exactly the zero set of `f` in
`ball c R'`, `‖f‖ ≤ M` on the circle `‖z − c‖ = R`, `f c ≠ 0`, and let `ord b` be the local order
of `f` at each `b ∈ Z` (given through a local factorisation). Then
`(∑_{b ∈ Z ∩ closedBall c r} ord b) · log (R / r) ≤ log M − log ‖f c‖`. -/
theorem sum_order_mul_log_le_of_jensen {c : ℂ} {R R' r M : ℝ} (hr : 0 < r) (hrR : r < R)
    (hRR' : R < R') {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball c R')) (Z : Finset ℂ)
    (hZR : ∀ b ∈ Z, b ∈ ball c R) (hZ : ∀ z ∈ ball c R', f z = 0 ↔ z ∈ Z)
    (hM : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (hfc : f c ≠ 0) (ord : ℂ → ℕ)
    (hord : ∀ b ∈ Z, ∃ G : ℂ → ℂ, AnalyticAt ℂ G b ∧ G b ≠ 0 ∧
      ∀ᶠ z in 𝓝 b, f z = (z - b) ^ ord b * G z) :
    (∑ b ∈ Z.filter (fun b => b ∈ closedBall c r), (ord b : ℝ)) * Real.log (R / r)
      ≤ Real.log M - Real.log ‖f c‖ := by
  have hR : 0 < R := hr.trans hrR
  obtain ⟨m, g, hg, hg0, hfg, -⟩ :=
    Jensen.exists_factorization_of_finite_zeros hR hRR' hf Z hZR hZ
  have hsub : closedBall c R ⊆ ball c R' := closedBall_subset_ball hRR'
  have hcZ : ∀ b ∈ Z, b ≠ c := by
    intro b hb h
    exact hfc ((hZ c (mem_ball_self (hR.trans hRR'))).mpr (h ▸ hb))
  -- the multiplicities of the factorisation are the local orders
  have hmord : ∀ b ∈ Z, m b = ord b := by
    intro b hb
    have hbR' : b ∈ ball c R' := ball_subset_ball hRR'.le (hZR b hb)
    have hnhds : ball c R' ∈ 𝓝 b := isOpen_ball.mem_nhds hbR'
    have hfb : AnalyticAt ℂ f b := hf.analyticAt hnhds
    obtain ⟨G, hG, hG0, hfG⟩ := hord b hb
    have hQd : Differentiable ℂ (fun z => ∏ b' ∈ Z.erase b, (z - b') ^ m b') :=
      Differentiable.fun_finsetProd (u := Z.erase b) (f := fun b' z => (z - b') ^ m b')
        fun b' _ => (differentiable_id.sub_const b').pow (m b')
    have hQ : AnalyticAt ℂ (fun z => ∏ b' ∈ Z.erase b, (z - b') ^ m b') b := hQd.analyticAt b
    have hQ0 : ∏ b' ∈ Z.erase b, (b - b') ^ m b' ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro b' hb'
      exact pow_ne_zero _ (sub_ne_zero.mpr (Finset.ne_of_mem_erase hb').symm)
    have hgb : AnalyticAt ℂ g b := hg.analyticAt hnhds
    have hfQ : ∀ᶠ z in 𝓝 b, f z = (z - b) ^ m b * ((∏ b' ∈ Z.erase b, (z - b') ^ m b') * g z) := by
      filter_upwards [hnhds] with z hz
      rw [hfg z hz, ← Finset.mul_prod_erase Z (fun b' => (z - b') ^ m b') hb, mul_assoc]
    exact order_unique hfb (hQ.mul hgb) (mul_ne_zero hQ0 (hg0 b hbR')) hfQ hG hG0 hfG
  -- Jensen's formula
  have hJ : Real.log ‖f c‖ =
      (2 * π)⁻¹ * (∫ θ in (0 : ℝ)..(2 * π), Real.log ‖f (c + R * Complex.exp (θ * I))‖)
        - ∑ b ∈ Z, (m b : ℝ) * Real.log (R / ‖b - c‖) :=
    Jensen.jensen_formula_multiplicity hR hRR' (s := Z) (a := id) (m := m) hZR hcZ hg hg0
      (fun z hz => hfg z (hsub hz))
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
      (∫ θ in (0 : ℝ)..(2 * π), Real.log ‖f (c + R * Complex.exp (θ * I))‖)
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
          (∫ θ in (0 : ℝ)..(2 * π), Real.log ‖f (c + R * Complex.exp (θ * I))‖)
        ≤ (2 * π)⁻¹ * (2 * π * Real.log M) := by
          apply mul_le_mul_of_nonneg_left _ h2π.le
          exact hle
      _ = Real.log M := by field_simp
  -- termwise estimates
  have hterm_nonneg : ∀ b ∈ Z, 0 ≤ (m b : ℝ) * Real.log (R / ‖b - c‖) := by
    intro b hb
    apply mul_nonneg (Nat.cast_nonneg _)
    apply Real.log_nonneg
    rw [one_le_div (norm_pos_iff.mpr (sub_ne_zero.mpr (hcZ b hb)))]
    exact (mem_ball_iff_norm.mp (hZR b hb)).le
  have hterm_r : ∀ b ∈ Z.filter (fun b => b ∈ closedBall c r),
      (ord b : ℝ) * Real.log (R / r) ≤ (m b : ℝ) * Real.log (R / ‖b - c‖) := by
    intro b hb
    obtain ⟨hbZ, hbr⟩ := Finset.mem_filter.mp hb
    have hbc : 0 < ‖b - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hcZ b hbZ))
    have hbr' : ‖b - c‖ ≤ r := mem_closedBall_iff_norm.mp hbr
    have h1 : Real.log (R / r) ≤ Real.log (R / ‖b - c‖) := by
      apply Real.log_le_log (div_pos hR hr)
      exact div_le_div_of_nonneg_left hR.le hbc hbr'
    rw [hmord b hbZ]
    exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
  have hsum : (∑ b ∈ Z.filter (fun b => b ∈ closedBall c r), (ord b : ℝ)) * Real.log (R / r)
      ≤ ∑ b ∈ Z, (m b : ℝ) * Real.log (R / ‖b - c‖) := by
    rw [Finset.sum_mul]
    calc ∑ b ∈ Z.filter (fun b => b ∈ closedBall c r), (ord b : ℝ) * Real.log (R / r)
        ≤ ∑ b ∈ Z.filter (fun b => b ∈ closedBall c r), (m b : ℝ) * Real.log (R / ‖b - c‖) :=
          Finset.sum_le_sum hterm_r
      _ ≤ ∑ b ∈ Z, (m b : ℝ) * Real.log (R / ‖b - c‖) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun b hb _ => hterm_nonneg b hb)
  linarith [hJ, havg, hsum]

open scoped Classical in
/-- **Jensen zero count with multiplicities (radius chosen automatically).** Let `f` be
holomorphic on `ball c R'` with finitely many zeros there, `0 < r < R₀ < R'`, `‖f‖ ≤ M` on
`ball c R'`, `f c ≠ 0`, and `ord b` the local order at every zero `b`. Then
`(∑_{zeros b of f in closedBall c r} ord b) · log (R₀ / r) ≤ log M − log ‖f c‖`. -/
theorem sum_order_mul_log_le_of_jensen' {c : ℂ} {R₀ R' r M : ℝ} (hr : 0 < r) (hrR : r < R₀)
    (hRR' : R₀ < R') {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball c R'))
    (hfin : {z ∈ ball c R' | f z = 0}.Finite)
    (hM : ∀ z ∈ ball c R', ‖f z‖ ≤ M) (hfc : f c ≠ 0) (ord : ℂ → ℕ)
    (hord : ∀ b ∈ ball c R', f b = 0 → ∃ G : ℂ → ℂ, AnalyticAt ℂ G b ∧ G b ≠ 0 ∧
      ∀ᶠ z in 𝓝 b, f z = (z - b) ^ ord b * G z) :
    (∑ b ∈ hfin.toFinset.filter (fun b => b ∈ closedBall c r), (ord b : ℝ)) * Real.log (R₀ / r)
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
  have hord' : ∀ b ∈ Z, ∃ G : ℂ → ℂ, AnalyticAt ℂ G b ∧ G b ≠ 0 ∧
      ∀ᶠ z in 𝓝 b, f z = (z - b) ^ ord b * G z :=
    fun b hb => hord b (hZmem b hb).1 (hZmem b hb).2
  have hcore := sum_order_mul_log_le_of_jensen hr (hrR.trans_le hR₀R) hRR'' hf Z hZR hZ hM' hfc
    ord hord'
  have hlog : Real.log (R₀ / r) ≤ Real.log (R / r) :=
    Real.log_le_log (div_pos (hr.trans hrR) hr) (div_le_div_of_nonneg_right hR₀R hr.le)
  calc (∑ b ∈ Z.filter (fun b => b ∈ closedBall c r), (ord b : ℝ)) * Real.log (R₀ / r)
      ≤ (∑ b ∈ Z.filter (fun b => b ∈ closedBall c r), (ord b : ℝ)) * Real.log (R / r) :=
        mul_le_mul_of_nonneg_left hlog (Finset.sum_nonneg fun b _ => Nat.cast_nonneg _)
    _ ≤ Real.log M - Real.log ‖f c‖ := hcore

/-! ## The multiplicity-weighted local zero count for `ζ` -/

open scoped Classical in
/-- **Multiplicity-weighted local zero count.** For `|T| ≥ 4` and any finite set `Z` of nontrivial
zeros with `|Im ρ − T| ≤ 1`, `∑ ρ ∈ Z, zetaOrder ρ ≤ 300 log |T|`. Jensen's formula on the disc
of centre `3/2 + T i` and radius `2` (growth bound `‖ζ s‖ ≤ 7 |Im s|^{3/2}` from
`ZetaGrowthNeg`, lower bound `‖ζ(3/2 + iT)‖ ≥ 1/3` from `ZetaLowerBound`), counting radius
`37/20` (which contains the whole strip `0 < Re ρ < 1`, `|Im ρ − T| ≤ 1`), Jensen radius
`≥ 39/20`. -/
theorem sum_zetaOrder_near_height_le (T : ℝ) (hT : 4 ≤ |T|) (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, IsNontrivialZero ρ ∧ |ρ.im - T| ≤ 1) :
    ∑ ρ ∈ Z, (zetaOrder ρ : ℝ) ≤ 300 * Real.log |T| := by
  set c : ℂ := 3/2 + T * I with hc
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
  set M : ℝ := 10 * (|T| + 2) ^ (3/2 : ℝ) with hMdef
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
    · calc ‖riemannZeta z‖ ≤ 7 * |z.im| ^ (3/2 : ℝ) :=
            ZeroDensityUnconditional.hgrowth z (by linarith) hre2 hzim2
        _ ≤ 7 * (|T| + 2) ^ (3/2 : ℝ) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact Real.rpow_le_rpow (abs_nonneg _) hzimT (by norm_num)
        _ ≤ M := by
            rw [hMdef]
            linarith
    · push_neg at hre2
      calc ‖riemannZeta z‖ ≤ ‖riemannZeta ((1 + 1 : ℝ) : ℂ)‖ :=
            ZetaGrowth.norm_zeta_le_of_re_ge one_pos (by linarith)
        _ = ‖riemannZeta 2‖ := by norm_num
        _ ≤ 3 := ZeroDensity.norm_riemannZeta_two_le
        _ ≤ M := by
            rw [hMdef]
            linarith
  -- `ζ c ≠ 0`, with `log ‖ζ c‖ ≥ -log 3`
  have hζc : 1/3 ≤ ‖riemannZeta c‖ := ZeroDensityUnconditional.hlow T
  have hfc : riemannZeta c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hζc
    norm_num at hζc
  have hlogc : -Real.log 3 ≤ Real.log ‖riemannZeta c‖ := by
    have := Real.log_le_log (by norm_num) hζc
    rwa [one_div, Real.log_inv] at this
  -- the local orders
  have hord : ∀ b ∈ ball c 2, riemannZeta b = 0 → ∃ G : ℂ → ℂ, AnalyticAt ℂ G b ∧ G b ≠ 0 ∧
      ∀ᶠ z in 𝓝 b, riemannZeta z = (z - b) ^ zetaOrder b * G z :=
    fun b hb _ => exists_factorization (hne1 b hb)
  -- Jensen
  have hJ := sum_order_mul_log_le_of_jensen' (c := c) (R₀ := 39/20) (R' := 2) (r := 37/20)
    (M := M) (by norm_num) (by norm_num) (by norm_num) hf hfin hM hfc zetaOrder hord
  -- `Z` lies in the counted set
  have hsub : Z ⊆ hfin.toFinset.filter (fun b => b ∈ closedBall c (37/20)) := by
    intro ρ hρ
    obtain ⟨hρz, him⟩ := hZ ρ hρ
    obtain ⟨hre0, hre1⟩ := ZetaStrip.mem_strip_of_isNontrivialZero hρz
    have hnorm : ‖ρ - c‖ ≤ 37/20 := by
      apply ZeroDensity.norm_le_of_re_im (by norm_num)
      rw [Complex.sub_re, Complex.sub_im, hcre, hcim]
      have h1 : (ρ.re - 3/2) ^ 2 ≤ 9/4 := by
        nlinarith [mul_pos hre0 (by linarith : (0 : ℝ) < 3 - ρ.re)]
      have h2 : (ρ.im - T) ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr him
      nlinarith [h1, h2]
    rw [Finset.mem_filter, Set.Finite.mem_toFinset]
    refine ⟨⟨?_, hρz.1⟩, ?_⟩
    · rw [mem_ball_iff_norm]
      linarith
    · exact mem_closedBall_iff_norm.mpr hnorm
  have hsum_le : ∑ ρ ∈ Z, (zetaOrder ρ : ℝ)
      ≤ ∑ ρ ∈ hfin.toFinset.filter (fun b => b ∈ closedBall c (37/20)), (zetaOrder ρ : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
  -- numerics
  have hlogM : Real.log M ≤ Real.log 10 + 3/2 * (Real.log 2 + Real.log |T|) := by
    rw [hMdef, Real.log_mul (by norm_num : (10 : ℝ) ≠ 0) hpow0.ne',
      Real.log_rpow (by linarith : (0 : ℝ) < |T| + 2)]
    have h1 : Real.log (|T| + 2) ≤ Real.log (2 * |T|) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) hTpos.ne'] at h1
    linarith
  have hlog10 : Real.log 10 ≤ 9 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)]
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog3 : Real.log 3 ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hlogT : 1 ≤ Real.log |T| := by
    rw [Real.le_log_iff_exp_le hTpos]
    linarith [Real.exp_one_lt_d9]
  have hlogr : (2 : ℝ) / 39 ≤ Real.log (39/20 / (37/20)) := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 39/20 / (37/20))
    norm_num at this ⊢
    linarith
  set S : ℝ := ∑ ρ ∈ hfin.toFinset.filter (fun b => b ∈ closedBall c (37/20)), (zetaOrder ρ : ℝ)
    with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hS1 : S * (2/39) ≤ S * Real.log (39/20 / (37/20)) :=
    mul_le_mul_of_nonneg_left hlogr hS0
  have key : S * (2/39) ≤ 14 * Real.log |T| := by linarith
  linarith

/-- **Two-sided band count.** For `k ≥ 4` and any finite set `Z` of nontrivial zeros with
`k ≤ |Im ρ| < k + 1`, `∑ ρ ∈ Z, zetaOrder ρ ≤ 600 log k`. -/
theorem sum_zetaOrder_band_le (k : ℕ) (hk : 4 ≤ k) (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, IsNontrivialZero ρ ∧ (k : ℝ) ≤ |ρ.im| ∧ |ρ.im| < k + 1) :
    ∑ ρ ∈ Z, (zetaOrder ρ : ℝ) ≤ 600 * Real.log k := by
  have hk' : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hkabs : |(k : ℝ)| = k := abs_of_nonneg (by linarith)
  have hkabs' : |(-(k : ℝ))| = k := by rw [_root_.abs_neg, hkabs]
  have h1 := sum_zetaOrder_near_height_le (k : ℝ) (by rw [hkabs]; exact hk')
    (Z.filter fun ρ => 0 ≤ ρ.im) (by
      intro ρ hρ
      obtain ⟨hρZ, hρpos⟩ := Finset.mem_filter.mp hρ
      obtain ⟨hnt, hlo, hhi⟩ := hZ ρ hρZ
      rw [_root_.abs_of_nonneg hρpos] at hlo hhi
      exact ⟨hnt, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  have h2 := sum_zetaOrder_near_height_le (-(k : ℝ)) (by rw [hkabs']; exact hk')
    (Z.filter fun ρ => ¬ 0 ≤ ρ.im) (by
      intro ρ hρ
      obtain ⟨hρZ, hρneg⟩ := Finset.mem_filter.mp hρ
      push_neg at hρneg
      obtain ⟨hnt, hlo, hhi⟩ := hZ ρ hρZ
      rw [_root_.abs_of_neg hρneg] at hlo hhi
      exact ⟨hnt, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  rw [hkabs] at h1
  rw [hkabs'] at h2
  rw [← Finset.sum_filter_add_sum_filter_not Z (fun ρ => 0 ≤ ρ.im)]
  refine le_trans (add_le_add h1 h2) ?_
  linarith

/-! ## The uniform bound on `∑ zetaOrder ρ / (Im ρ)²` -/

/-- The dominating sequence `1200 / k^{3/2}`. -/
def dom (k : ℕ) : ℝ := 1200 * ((k : ℝ) ^ ((3 : ℝ) / 2))⁻¹

theorem dom_nonneg (k : ℕ) : 0 ≤ dom k := by
  unfold dom
  have : 0 ≤ (k : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg k) _
  positivity

theorem summable_dom : Summable dom := by
  unfold dom
  exact (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 1200

/-- `600 log k / k² ≤ dom k` for `k ≥ 1` (from `log k ≤ 2 √k`). -/
theorem log_div_sq_le_dom (k : ℕ) (hk : 1 ≤ k) :
    600 * Real.log k / (k : ℝ) ^ 2 ≤ dom k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hlog : Real.log k ≤ 2 * (k : ℝ) ^ ((1 : ℝ) / 2) := by
    have := Real.log_le_rpow_div (x := (k : ℝ)) (ε := 1 / 2) hk0.le (by norm_num)
    calc Real.log k ≤ (k : ℝ) ^ ((1 : ℝ) / 2) / (1 / 2) := this
      _ = 2 * (k : ℝ) ^ ((1 : ℝ) / 2) := by ring
  have hsplit : (k : ℝ) ^ 2 = (k : ℝ) ^ ((3 : ℝ) / 2) * (k : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_add hk0, ← Real.rpow_two]
    norm_num
  have h32 : 0 < (k : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hk0 _
  have h12 : 0 < (k : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hk0 _
  unfold dom
  rw [div_le_iff₀ (by positivity), hsplit]
  calc 600 * Real.log k ≤ 600 * (2 * (k : ℝ) ^ ((1 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hlog (by norm_num)
    _ = 1200 * ((k : ℝ) ^ ((3 : ℝ) / 2))⁻¹ *
          ((k : ℝ) ^ ((3 : ℝ) / 2) * (k : ℝ) ^ ((1 : ℝ) / 2)) := by
        field_simp
        ring

/-- **Uniform bound.** There is `B` with `∑ ρ ∈ Z, zetaOrder ρ / (Im ρ)² ≤ B` for every finite
set `Z` of nontrivial zeros: the finitely many zeros of height `≤ 4` contribute a fixed amount,
and the band `k ≤ |Im ρ| < k + 1` (`k ≥ 4`) contributes at most `600 log k / k² ≤ dom k`. -/
theorem exists_bound_sum_zetaOrder_div_sq :
    ∃ B : ℝ, ∀ Z : Finset ℂ, (∀ ρ ∈ Z, IsNontrivialZero ρ) →
      ∑ ρ ∈ Z, (zetaOrder ρ : ℝ) / ρ.im ^ 2 ≤ B := by
  set A₀ : ℝ := ∑ ρ ∈ (ZeroDensity.finite_zeros_abs_im_le 4).toFinset,
    (zetaOrder ρ : ℝ) / ρ.im ^ 2 with hA₀
  refine ⟨A₀ + ∑' k, dom k, fun Z hZ => ?_⟩
  have hnn : ∀ ρ, 0 ≤ (zetaOrder ρ : ℝ) / ρ.im ^ 2 := fun ρ => by positivity
  -- low part
  have hlow : ∑ ρ ∈ Z.filter (fun ρ => |ρ.im| ≤ 4), (zetaOrder ρ : ℝ) / ρ.im ^ 2 ≤ A₀ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ρ hρ
      obtain ⟨hρZ, hρ4⟩ := Finset.mem_filter.mp hρ
      rw [Set.Finite.mem_toFinset]
      exact ⟨hZ ρ hρZ, hρ4⟩
    · intro ρ _ _
      exact hnn ρ
  -- high part: fibrewise over the integer band `⌊|Im ρ|⌋₊`
  have hhigh : ∑ ρ ∈ Z.filter (fun ρ => ¬ |ρ.im| ≤ 4), (zetaOrder ρ : ℝ) / ρ.im ^ 2
      ≤ ∑' k, dom k := by
    set Z₂ := Z.filter (fun ρ => ¬ |ρ.im| ≤ 4) with hZ₂
    have hZ₂mem : ∀ ρ ∈ Z₂, IsNontrivialZero ρ ∧ 4 < |ρ.im| := by
      intro ρ hρ
      obtain ⟨hρZ, hρ4⟩ := Finset.mem_filter.mp hρ
      exact ⟨hZ ρ hρZ, lt_of_not_ge hρ4⟩
    rw [← Finset.sum_fiberwise_of_maps_to (s := Z₂) (t := Z₂.image fun ρ => ⌊|ρ.im|⌋₊)
      (g := fun ρ => ⌊|ρ.im|⌋₊) (fun ρ hρ => Finset.mem_image_of_mem _ hρ)]
    calc ∑ k ∈ Z₂.image (fun ρ => ⌊|ρ.im|⌋₊), ∑ ρ ∈ Z₂.filter (fun ρ => ⌊|ρ.im|⌋₊ = k),
            (zetaOrder ρ : ℝ) / ρ.im ^ 2
        ≤ ∑ k ∈ Z₂.image (fun ρ => ⌊|ρ.im|⌋₊), dom k := by
          apply Finset.sum_le_sum
          intro k hk
          obtain ⟨ρ₀, hρ₀, hk₀⟩ := Finset.mem_image.mp hk
          have hk4 : 4 ≤ k := by
            rw [← hk₀]
            exact Nat.le_floor (by exact_mod_cast (hZ₂mem ρ₀ hρ₀).2.le)
          have hk1 : 1 ≤ k := by omega
          have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
          have hsq : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
          have hterm : ∀ ρ ∈ Z₂.filter (fun ρ => ⌊|ρ.im|⌋₊ = k),
              (zetaOrder ρ : ℝ) / ρ.im ^ 2 ≤ (zetaOrder ρ : ℝ) / (k : ℝ) ^ 2 := by
            intro ρ hρ
            obtain ⟨-, hρk⟩ := Finset.mem_filter.mp hρ
            have hkle : (k : ℝ) ≤ |ρ.im| := by
              rw [← hρk]
              exact Nat.floor_le (abs_nonneg _)
            apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) hsq
            rw [← _root_.sq_abs ρ.im]
            exact pow_le_pow_left₀ hkpos.le hkle 2
          have hband := sum_zetaOrder_band_le k hk4 (Z₂.filter (fun ρ => ⌊|ρ.im|⌋₊ = k)) (by
            intro ρ hρ
            obtain ⟨hρZ₂, hρk⟩ := Finset.mem_filter.mp hρ
            refine ⟨(hZ₂mem ρ hρZ₂).1, ?_, ?_⟩
            · rw [← hρk]
              exact Nat.floor_le (abs_nonneg _)
            · rw [← hρk]
              exact Nat.lt_floor_add_one _)
          calc ∑ ρ ∈ Z₂.filter (fun ρ => ⌊|ρ.im|⌋₊ = k), (zetaOrder ρ : ℝ) / ρ.im ^ 2
              ≤ ∑ ρ ∈ Z₂.filter (fun ρ => ⌊|ρ.im|⌋₊ = k), (zetaOrder ρ : ℝ) / (k : ℝ) ^ 2 :=
                Finset.sum_le_sum hterm
            _ = (∑ ρ ∈ Z₂.filter (fun ρ => ⌊|ρ.im|⌋₊ = k), (zetaOrder ρ : ℝ)) / (k : ℝ) ^ 2 :=
                (Finset.sum_div _ _ _).symm
            _ ≤ 600 * Real.log k / (k : ℝ) ^ 2 := div_le_div_of_nonneg_right hband hsq.le
            _ ≤ dom k := log_div_sq_le_dom k hk1
      _ ≤ ∑' k, dom k := Summable.sum_le_tsum _ (fun k _ => dom_nonneg k) summable_dom
  rw [← Finset.sum_filter_add_sum_filter_not Z (fun ρ => |ρ.im| ≤ 4)]
  exact add_le_add hlow hhigh

/-! ## Summability of the zero side -/

/-- **`∑ 1/(Im ρ)² < ∞` with multiplicities**, along any enumeration with multiplicity. -/
theorem summable_inv_sq_im {ι : Type*} {zeros : ι → ℂ} (h : MultEnum zeros) :
    Summable (fun i => 1 / ((zeros i).im) ^ 2) := by
  obtain ⟨B, hB⟩ := exists_bound_sum_zetaOrder_div_sq
  refine summable_of_sum_le (c := B) (fun i => ?_) (fun u => ?_)
  · show (0 : ℝ) ≤ 1 / ((zeros i).im) ^ 2
    positivity
  rw [Finset.sum_comp (fun ρ : ℂ => 1 / ρ.im ^ 2) zeros]
  calc ∑ ρ ∈ u.image zeros, (u.filter fun i => zeros i = ρ).card • (1 / ρ.im ^ 2)
      ≤ ∑ ρ ∈ u.image zeros, (zetaOrder ρ : ℝ) / ρ.im ^ 2 := by
        apply Finset.sum_le_sum
        intro ρ hρ
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hρ
        rw [nsmul_eq_mul, mul_one_div]
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        exact_mod_cast h.card_filter_le u (h.nontrivial i)
    _ ≤ B := hB _ (fun ρ hρ => by
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hρ
        exact h.nontrivial i)

/-- **Absolute summability of the zero side.** For an enumeration with multiplicity and a test
function `g` on `[-a, a]`, `∑ ‖Gt a g (zeros i)‖ < ∞`: by `Gt_decay`,
`‖Gt a g ρ‖ ≤ C₂ e^{a/2} / (Im ρ)²` for every nontrivial zero with `Im ρ ≠ 0` (as
`|Re ρ − ½| < ½`), and the indices with `Im (zeros i) = 0` are finitely many. -/
theorem summable_norm_Gt {ι : Type*} {zeros : ι → ℂ} (h : MultEnum zeros) {a : ℝ} {g : ℝ → ℂ}
    (hg : IsTestFn a g) : Summable (fun i => ‖Gt a g (zeros i)‖) := by
  have hsum := (summable_inv_sq_im h).mul_left (C₂ a g * Real.exp (a / 2))
  have hbound : ∀ i, (zeros i).im ≠ 0 →
      ‖Gt a g (zeros i)‖ ≤ C₂ a g * Real.exp (a / 2) * (1 / ((zeros i).im) ^ 2) := by
    intro i hi
    obtain ⟨hre0, hre1⟩ := ZetaStrip.mem_strip_of_isNontrivialZero (h.nontrivial i)
    have habs : |(zeros i).re - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hexp : Real.exp (a * |(zeros i).re - 1 / 2|) ≤ Real.exp (a / 2) := by
      rw [Real.exp_le_exp]
      have := mul_le_mul_of_nonneg_left habs hg.nonneg
      linarith
    calc ‖Gt a g (zeros i)‖
        ≤ C₂ a g * Real.exp (a * |(zeros i).re - 1 / 2|) / (zeros i).im ^ 2 := Gt_decay hg hi
      _ ≤ C₂ a g * Real.exp (a / 2) / (zeros i).im ^ 2 := by
          apply div_le_div_of_nonneg_right _ (sq_nonneg _)
          exact mul_le_mul_of_nonneg_left hexp (C₂_nonneg hg)
      _ = C₂ a g * Real.exp (a / 2) * (1 / (zeros i).im ^ 2) := by ring
  refine Summable.of_norm_bounded_eventually hsum ?_
  rw [Filter.eventually_cofinite]
  refine (h.finite 0).subset ?_
  intro i hi
  simp only [mem_setOf_eq] at hi ⊢
  by_contra h0
  apply hi
  rw [norm_norm]
  apply hbound
  intro hzero
  apply h0
  simp [hzero]

/-- **Summability of the zero side.** -/
theorem summable_Gt {ι : Type*} {zeros : ι → ℂ} (h : MultEnum zeros) {a : ℝ} {g : ℝ → ℂ}
    (hg : IsTestFn a g) : Summable (fun i => Gt a g (zeros i)) :=
  (summable_norm_Gt h hg).of_norm

/-! ## The truncation identity and the limit -/

/-- For `T ≥ 0`, `zeroFinset (3/2) T` is exactly the set of nontrivial zeros of height `≤ T`
(every nontrivial zero has `0 < Re ρ < 1 ⊆ [-1/2, 3/2]`, and no trivial zero has
`Re ≥ -1/2`). -/
theorem mem_zeroFinset_three_halves {T : ℝ} (hT : 0 ≤ T) {ρ : ℂ} :
    ρ ∈ zeroFinset (3/2) T ↔ IsNontrivialZero ρ ∧ |ρ.im| ≤ T := by
  rw [mem_zeroFinset, Complex.mem_reProdIm, Set.uIcc_of_le (by linarith : -T ≤ T), Set.mem_Icc,
    ← _root_.abs_le]
  constructor
  · rintro ⟨⟨hre, him⟩, h1, h0⟩
    refine ⟨⟨h0, ?_, h1⟩, him⟩
    rintro ⟨n, hn⟩
    have hre' := congrArg Complex.re hn
    simp at hre'
    have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    rcases Set.mem_uIcc.mp hre with ⟨h, _⟩ | ⟨_, h⟩ <;> linarith
  · rintro ⟨hnt, him⟩
    obtain ⟨h0, h1⟩ := ZetaStrip.mem_strip_of_isNontrivialZero hnt
    exact ⟨⟨Set.mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩), him⟩, hnt.2.2, hnt.1⟩

/-- **Truncation identity.** For `T ≥ 0`, the multiplicity-weighted sum over
`zeroFinset (3/2) T` is the sum over the indices of height `≤ T`. -/
theorem sum_zeroFinset_eq {ι : Type*} {zeros : ι → ℂ} (h : MultEnum zeros) (F : ℂ → ℂ) {T : ℝ}
    (hT : 0 ≤ T) :
    ∑ ρ ∈ zeroFinset (3/2) T, (zetaOrder ρ : ℂ) * F ρ
      = ∑ i ∈ (h.finite T).toFinset, F (zeros i) := by
  rw [Finset.sum_comp F zeros]
  have himage : (h.finite T).toFinset.image zeros = zeroFinset (3/2) T := by
    ext ρ
    rw [Finset.mem_image, mem_zeroFinset_three_halves hT]
    constructor
    · rintro ⟨i, hi, rfl⟩
      rw [Set.Finite.mem_toFinset] at hi
      exact ⟨h.nontrivial i, hi⟩
    · rintro ⟨hnt, him⟩
      obtain ⟨i, rfl⟩ := h.exists_index hnt
      exact ⟨i, (h.finite T).mem_toFinset.mpr him, rfl⟩
  rw [himage]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  obtain ⟨hnt, him⟩ := (mem_zeroFinset_three_halves hT).mp hρ
  rw [h.card_filter_eq hnt him, nsmul_eq_mul]

/-- **The truncated zero sums converge to the full zero sum.** For any heights `T k → ∞`,
`∑ ρ ∈ zeroFinset (3/2) (T k), zetaOrder ρ · Gt a g ρ → ∑' i, Gt a g (zeros i)`
(Tannery's theorem with the summable majorant `‖Gt a g (zeros i)‖`). -/
theorem tendsto_sum_zeroFinset {ι : Type*} {zeros : ι → ℂ} (h : MultEnum zeros) {a : ℝ}
    {g : ℝ → ℂ} (hg : IsTestFn a g) (T : ℕ → ℝ) (hT : Tendsto T atTop atTop) :
    Tendsto (fun k => ∑ ρ ∈ zeroFinset (3/2) (T k), (zetaOrder ρ : ℂ) * Gt a g ρ) atTop
      (𝓝 (∑' i, Gt a g (zeros i))) := by
  have hbound := summable_norm_Gt h hg
  have htan : Tendsto (fun k => ∑' i, if |(zeros i).im| ≤ T k then Gt a g (zeros i) else 0)
      atTop (𝓝 (∑' i, Gt a g (zeros i))) := by
    refine tendsto_tsum_of_dominated_convergence
      (f := fun (k : ℕ) (i : ι) => if |(zeros i).im| ≤ T k then Gt a g (zeros i) else 0)
      (g := fun i => Gt a g (zeros i)) (bound := fun i => ‖Gt a g (zeros i)‖) hbound
      (fun i => ?_) ?_
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hT.eventually_ge_atTop |(zeros i).im|] with k hk
      simp [hk]
    · refine Eventually.of_forall fun k i => ?_
      split_ifs <;> simp
  refine htan.congr' ?_
  filter_upwards [hT.eventually_ge_atTop 0] with k hk
  rw [tsum_eq_sum (s := (h.finite (T k)).toFinset) (fun i hi => ?_), sum_zeroFinset_eq h _ hk]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [Set.Finite.mem_toFinset] at hi
    exact if_pos hi
  · rw [Set.Finite.mem_toFinset] at hi
    exact if_neg hi

/-- The zero side as a series along an enumeration with multiplicity: the `HasSum` form. -/
theorem hasSum_Gt {ι : Type*} {zeros : ι → ℂ} (h : MultEnum zeros) {a : ℝ} {g : ℝ → ℂ}
    (hg : IsTestFn a g) : HasSum (fun i => Gt a g (zeros i)) (∑' i, Gt a g (zeros i)) :=
  (summable_Gt h hg).hasSum

/-! ## Existence of an enumeration with multiplicity -/

/-- The canonical index type: pairs `(ρ, j)` with `ρ` a nontrivial zero and `j < zetaOrder ρ`. -/
abbrev Index : Type := Σ ρ : {ρ : ℂ // IsNontrivialZero ρ}, Fin (zetaOrder ρ.1)

/-- The canonical enumeration with multiplicity: `(ρ, j) ↦ ρ`. -/
def canonical : Index → ℂ := fun x => x.1.1

/-- The fibre of `canonical` over a nontrivial zero `ρ` is the range of `j ↦ (ρ, j)`. -/
theorem fiber_canonical_eq {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    {x : Index | canonical x = ρ}
      = Set.range (fun j : Fin (zetaOrder ρ) => (⟨⟨ρ, hρ⟩, j⟩ : Index)) := by
  ext x
  simp only [mem_setOf_eq, Set.mem_range]
  constructor
  · intro hx
    obtain ⟨⟨ρ', hρ'⟩, j⟩ := x
    have hρρ' : ρ' = ρ := hx
    subst hρρ'
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    rfl

/-- **Existence (unconditional).** The canonical enumeration is an enumeration with
multiplicity. -/
theorem multEnum_canonical : MultEnum canonical where
  nontrivial x := x.1.2
  mult ρ hρ := by
    rw [fiber_canonical_eq hρ, ← Set.image_univ, Set.ncard_image_of_injective _ ?_,
      Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    intro j j' hjj'
    exact eq_of_heq (Sigma.mk.inj_iff.mp hjj').2
  finite T := by
    have hfin : {ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im| ≤ T}.Finite :=
      ZeroDensity.finite_zeros_abs_im_le T
    have hsub : {x : Index | |(canonical x).im| ≤ T} ⊆
        ⋃ ρ ∈ {ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im| ≤ T}, {x : Index | canonical x = ρ} := by
      intro x hx
      exact Set.mem_biUnion (x := canonical x) ⟨x.1.2, hx⟩ rfl
    refine (hfin.biUnion fun ρ hρ => ?_).subset hsub
    rw [fiber_canonical_eq hρ.1]
    exact Set.finite_range _

/-- The zero side, packaged for the canonical enumeration: absolute convergence and the
truncation limit, unconditionally. -/
theorem zero_side_canonical {a : ℝ} {g : ℝ → ℂ} (hg : IsTestFn a g) :
    Summable (fun x => ‖Gt a g (canonical x)‖) ∧
    ∀ T : ℕ → ℝ, Tendsto T atTop atTop →
      Tendsto (fun k => ∑ ρ ∈ zeroFinset (3/2) (T k), (zetaOrder ρ : ℂ) * Gt a g ρ) atTop
        (𝓝 (∑' x, Gt a g (canonical x))) :=
  ⟨summable_norm_Gt multEnum_canonical hg,
    fun T hT => tendsto_sum_zeroFinset multEnum_canonical hg T hT⟩

/-- `Index` is countable: the nontrivial zeros form a countable set (`ZerosCountable`). -/
instance : Countable Index := by
  haveI : Countable {ρ : ℂ // IsNontrivialZero ρ} :=
    ZerosCountable.countable_nontrivialZeros.to_subtype
  infer_instance

/-- **Existence of an `ℕ`-indexed enumeration (hypothesis-dependent).** If there are infinitely
many nontrivial zeros (`hinf`, not proven in this project), there is an enumeration with
multiplicity `zeros : ℕ → ℂ`. -/
theorem exists_multEnum_nat (hinf : {ρ : ℂ | IsNontrivialZero ρ}.Infinite) :
    ∃ zeros : ℕ → ℂ, MultEnum zeros := by
  haveI : Infinite {ρ : ℂ // IsNontrivialZero ρ} := Set.infinite_coe_iff.mpr hinf
  haveI : Infinite Index := by
    refine Infinite.of_injective (fun ρ : {ρ : ℂ // IsNontrivialZero ρ} =>
      (⟨ρ, ⟨0, zetaOrder_pos ρ.2.2.2 ρ.2.1⟩⟩ : Index)) ?_
    intro ρ ρ' hρρ'
    exact (Sigma.mk.inj_iff.mp hρρ').1
  obtain ⟨d⟩ := nonempty_denumerable Index
  let e : Index ≃ ℕ := @Denumerable.eqv Index d
  exact ⟨canonical ∘ e.symm, multEnum_canonical.comp_equiv e.symm⟩

/-- The zero side along an `ℕ`-indexed enumeration (hypothesis-dependent on `hinf`): an
enumeration `zeros : ℕ → ℂ` with multiplicity such that, for every test function, the zero
side converges absolutely and the truncations along any heights `T k → ∞` converge to it. -/
theorem zero_side_nat (hinf : {ρ : ℂ | IsNontrivialZero ρ}.Infinite) :
    ∃ zeros : ℕ → ℂ, MultEnum zeros ∧ ∀ (a : ℝ) (g : ℝ → ℂ), IsTestFn a g →
      Summable (fun n => ‖Gt a g (zeros n)‖) ∧
      ∀ T : ℕ → ℝ, Tendsto T atTop atTop →
        Tendsto (fun k => ∑ ρ ∈ zeroFinset (3/2) (T k), (zetaOrder ρ : ℂ) * Gt a g ρ) atTop
          (𝓝 (∑' n, Gt a g (zeros n))) := by
  obtain ⟨zeros, h⟩ := exists_multEnum_nat hinf
  exact ⟨zeros, h, fun a g hg => ⟨summable_norm_Gt h hg,
    fun T hT => tendsto_sum_zeroFinset h hg T hT⟩⟩

end ZeroSumLimit

end
