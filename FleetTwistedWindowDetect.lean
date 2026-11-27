import FleetTwistedWindowShift
import ContourShift
import PrincipalPartDischarge
import ExpSumLowerBound

/-!
# Local zero detection from a Gaussian prime-line bound (any entire `L`)

The ζ strip theorem (`FleetHeadContourStrip`) reaches the zeros through the **global** explicit
formula (`FleetExponentLadder` → `GaussianTraceFormula` → zero counting, functional equation and the
archimedean term of `ζ`). This file replaces that step, for an arbitrary entire function `L`, by a
**finite rectangle**: only finitely many zeros lie in a compact rectangle, so no zero counting, no
functional equation and no archimedean term is needed.

Setting: `L` entire, `L ≠ 0` on `Re ≥ 1`, `‖L'/L‖ ≤ B` on `Re = 3/2`. The prime line is
`primeLine L b α = ∫ LGw b α (3/2+it) · (L'/L)(3/2+it) dt`.

* `finite_zeros`         : zeros of `L` in a compact set form a finite set.
* `rect_logDeriv_residue`: for a rectangle with no zero on its boundary and an entire `G`,
                           `∮ G · L'/L = 2πi Σ_{ρ inside} m_ρ G(ρ)` (`m_ρ` = order of the zero).
* `exp_detect`           : a finite exponential sum `Σ e^{w_i s}` cannot be `O(e^{a s})` if some
                           `Re w_i > a ≥ 0` (via `ExpSumLowerBound`).
* `zero_detect`          : **if `‖primeLine L b α‖ ≤ √(π/b) C e^{c/b}` for every `α` and `0 < b ≤ 1`,
                           then every zero `ρ` of `L` with `Re ρ > 1/2` has `(Re ρ − 1/2)² ≤ 4c`.**

Route of `zero_detect`: fix a zero `ρ₀ = 1/2 + δ₀ + iγ₀` with `δ₀² > 4c`, take `α = −γ₀`, and the
rectangle `[1/2 + η, 3/2] × [−Y, Y]` (`0 < η < δ₀`, `Y > |γ₀| + 3`, both chosen off the finitely many
zeros). The residue sum is `√(π/b) Σ_ρ m_ρ (e^{(ρ−1/2+iα)²/4b} + e^{(ρ−1/2−iα)²/4b})`; the left edge
costs `e^{η²/4b}`, the horizontal edges and the tails of the right line cost `O(1)` (Gaussian decay at
distance `≥ 2` from `±α`), and the right line is the prime line. The term of `ρ₀` has exponent
`δ₀²/4b > max(4c, η²)/4b`, which `exp_detect` forbids.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Complex Filter Topology Set MeasureTheory
open scoped Real Interval

namespace FleetTwistedWindow

open FleetHeadContour Residue

/-! ## Isolated zeros -/

lemma eventually_ne_zero_punctured_of_entire {L : ℂ → ℂ} (hL : Differentiable ℂ L) {z₁ : ℂ}
    (hz₁ : L z₁ ≠ 0) (z : ℂ) : ∀ᶠ w in 𝓝[≠] z, L w ≠ 0 := by
  rcases (hL.analyticAt z).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have han : AnalyticOnNhd ℂ L univ := fun w _ => hL.analyticAt w
    have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ z) h
    exact hz₁ (this (mem_univ z₁))
  · exact h

/-- Zeros of a not-identically-zero entire function in a compact set form a finite set. -/
theorem finite_zeros {L : ℂ → ℂ} (hL : Differentiable ℂ L) {z₁ : ℂ} (hz₁ : L z₁ ≠ 0)
    {K : Set ℂ} (hK : IsCompact K) : {s : ℂ | s ∈ K ∧ L s = 0}.Finite := by
  have hU : ∀ x ∈ K, {w : ℂ | w ≠ x → L w ≠ 0} ∈ 𝓝 x := by
    intro x _
    have h : ∀ᶠ w in 𝓝 x, w ≠ x → L w ≠ 0 :=
      eventually_nhdsWithin_iff.mp (eventually_ne_zero_punctured_of_entire hL hz₁ x)
    exact h
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover _ hU
  refine t.finite_toSet.subset ?_
  rintro s ⟨hsK, hs0⟩
  obtain ⟨x, hxt, hsx⟩ := Set.mem_iUnion₂.mp (ht hsK)
  rcases eq_or_ne s x with rfl | hne
  · exact hxt
  · exact absurd hs0 (hsx hne)

/-- Local factorisation of an entire, not identically zero `L` at `ρ`. -/
lemma exists_factorization_entire {L : ℂ → ℂ} (hL : Differentiable ℂ L) {z₁ : ℂ} (hz₁ : L z₁ ≠ 0)
    (ρ : ℂ) : ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
      ∀ᶠ z in 𝓝 ρ, L z = (z - ρ) ^ analyticOrderNatAt L ρ * g z := by
  have han : AnalyticAt ℂ L ρ := hL.analyticAt ρ
  have hne : analyticOrderAt L ρ ≠ ⊤ := by
    intro h
    obtain ⟨z, hz0, hz1⟩ := ((eventually_nhdsWithin_of_eventually_nhds (analyticOrderAt_eq_top.mp h)).and
      (eventually_ne_zero_punctured_of_entire hL hz₁ ρ)).exists
    exact hz1 hz0
  obtain ⟨g, hg, hg0, hfg⟩ := han.analyticOrderAt_ne_top.mp hne
  refine ⟨g, hg, hg0, ?_⟩
  filter_upwards [hfg] with z hz
  simpa only [smul_eq_mul] using hz

lemma one_le_order_of_zero {L : ℂ → ℂ} (hL : Differentiable ℂ L) {z₁ : ℂ} (hz₁ : L z₁ ≠ 0)
    {ρ : ℂ} (hρ : L ρ = 0) : 1 ≤ analyticOrderNatAt L ρ := by
  obtain ⟨g, -, hg0, hfg⟩ := exists_factorization_entire hL hz₁ ρ
  rcases Nat.eq_zero_or_pos (analyticOrderNatAt L ρ) with h0 | hpos
  · exfalso
    have h := hfg.self_of_nhds
    rw [hρ, h0, sub_self, pow_zero, one_mul] at h
    exact hg0 h.symm
  · exact hpos

/-! ## The residue identity on a rectangle -/

/-- The closed rectangle `[[x₁, x₂]] ×ℂ [[y₁, y₂]]`. -/
abbrev rect (x₁ x₂ y₁ y₂ : ℝ) : Set ℂ := [[x₁, x₂]] ×ℂ [[y₁, y₂]]

lemma rect_mem_nhds {x₁ x₂ y₁ y₂ : ℝ} {ρ : ℂ}
    (hρ : x₁ < ρ.re ∧ ρ.re < x₂ ∧ y₁ < ρ.im ∧ ρ.im < y₂) : rect x₁ x₂ y₁ y₂ ∈ 𝓝 ρ := by
  rw [mem_nhds_iff]
  refine ⟨Ioo x₁ x₂ ×ℂ Ioo y₁ y₂, ?_, IsOpen.reProdIm isOpen_Ioo isOpen_Ioo, ?_⟩
  · intro s hs
    rw [mem_reProdIm] at hs ⊢
    exact ⟨Icc_subset_uIcc (Ioo_subset_Icc_self hs.1), Icc_subset_uIcc (Ioo_subset_Icc_self hs.2)⟩
  · rw [mem_reProdIm]
    exact ⟨⟨hρ.1, hρ.2.1⟩, ⟨hρ.2.2.1, hρ.2.2.2⟩⟩

lemma differentiable_deriv_of_entire {L : ℂ → ℂ} (hL : Differentiable ℂ L) :
    Differentiable ℂ (deriv L) := by
  have h := (contDiff_succ_iff_deriv (n := 1)).mp (hL.contDiff (n := 1 + 1))
  exact h.2.2.differentiable (by norm_num)

lemma continuousAt_logDeriv_mul {L G : ℂ → ℂ} (hL : Differentiable ℂ L) (hG : Continuous G) {s : ℂ}
    (hs : L s ≠ 0) : ContinuousAt (fun w => G w * (deriv L w / L w)) s :=
  hG.continuousAt.mul (((differentiable_deriv_of_entire hL).continuous.continuousAt).div
    hL.continuous.continuousAt hs)

/-- **Residue identity for `G · L'/L` on a rectangle.** If no zero of `L` lies on the boundary of the
closed rectangle and `Z` is the (finite) set of zeros of `L` in the rectangle, then
`∮ G · L'/L = 2πi Σ_{ρ ∈ Z} m_ρ G(ρ)`, `m_ρ = analyticOrderNatAt L ρ`. -/
theorem rect_logDeriv_residue {L : ℂ → ℂ} (hL : Differentiable ℂ L) {z₁ : ℂ} (hz₁ : L z₁ ≠ 0)
    {G : ℂ → ℂ} (hG : Differentiable ℂ G) {x₁ x₂ y₁ y₂ : ℝ} (hx : x₁ < x₂) (hy : y₁ < y₂)
    (hbd : ∀ s ∈ rect x₁ x₂ y₁ y₂, L s = 0 → x₁ < s.re ∧ s.re < x₂ ∧ y₁ < s.im ∧ s.im < y₂)
    (Z : Finset ℂ) (hZ1 : ∀ s ∈ rect x₁ x₂ y₁ y₂, L s = 0 → s ∈ Z)
    (hZ2 : ∀ ρ ∈ Z, ρ ∈ rect x₁ x₂ y₁ y₂ ∧ L ρ = 0) :
    rectBoundaryIntegral (fun s => G s * (deriv L s / L s)) ((x₁ : ℂ) + y₁ * I) ((x₂ : ℂ) + y₂ * I)
      = 2 * π * I * ∑ ρ ∈ Z, (analyticOrderNatAt L ρ : ℂ) * G ρ := by
  classical
  set R := rect x₁ x₂ y₁ y₂ with hR
  have memZ : ∀ s, s ∈ Z ↔ s ∈ R ∧ L s = 0 := fun s => ⟨fun h => hZ2 s h, fun h => hZ1 s h.1 h.2⟩
  set m : ℂ → ℕ := fun ρ => analyticOrderNatAt L ρ with hm
  -- the remainder `H`
  set H₀ : ℂ → ℂ := fun s => deriv L s / L s - ∑ q ∈ Z, (m q : ℂ) / (s - q) with hH₀
  have hdL := differentiable_deriv_of_entire hL
  have hH₀d : ∀ s, L s ≠ 0 → s ∉ Z → DifferentiableAt ℂ H₀ s := by
    intro s hs hsZ
    refine ((hdL s).div (hL s) hs).sub ?_
    apply DifferentiableAt.fun_sum
    intro q hq
    have hsq : s - q ≠ 0 := sub_ne_zero.mpr (fun h => hsZ (h ▸ hq))
    exact (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _)) hsq
  obtain ⟨H, hHd, hHeq⟩ := PrincipalPartDischarge.exists_differentiableAt_of_tendsto_punctures R Z H₀
    (fun s hsR hsZ => hH₀d s (fun h0 => hsZ ((memZ s).mpr ⟨hsR, h0⟩)) hsZ)
    (fun p _ => by
      filter_upwards [eventually_ne_zero_punctured_of_entire hL hz₁ p,
        PrincipalPartDischarge.eventually_not_mem_punctured Z p] with t ht htZ
      exact hH₀d t ht htZ)
    (fun p hp => by
      obtain ⟨g, hg, hg0, hfg⟩ := exists_factorization_entire hL hz₁ p
      exact ⟨_, PrincipalPartDischarge.tendsto_sub_principalPart hg hg0 Z (fun q => (m q : ℂ)) hp
        (PrincipalPartDischarge.logDeriv_eventually_eq_of_eventually_eq_pow_mul hg hg0 _ hfg)⟩)
  -- poles and the regular part
  set P : Finset SimplePole := Z.image fun ρ => ⟨ρ, (m ρ : ℂ) * G ρ⟩ with hP
  have hinj : ∀ x ∈ Z, ∀ y ∈ Z, (fun ρ : ℂ => (⟨ρ, (m ρ : ℂ) * G ρ⟩ : SimplePole)) x =
      (fun ρ : ℂ => (⟨ρ, (m ρ : ℂ) * G ρ⟩ : SimplePole)) y → x = y := by
    intro x _ y _ h
    simpa using congrArg SimplePole.pole h
  have hPP : ∀ s, principalPart P s = ∑ ρ ∈ Z, ((m ρ : ℂ) * G ρ) / (s - ρ) := by
    intro s
    unfold principalPart
    rw [hP, Finset.sum_image hinj]
  set K : ℂ → ℂ := fun s => H s * G s + ∑ ρ ∈ Z, (m ρ : ℂ) * dslope G ρ s with hK
  have hKd : DifferentiableOn ℂ K R := by
    intro s hs
    refine (((hHd s hs).mul (hG s)).add ?_).differentiableWithinAt
    apply DifferentiableAt.fun_sum
    intro ρ _
    have hds : Differentiable ℂ (dslope G ρ) := by
      rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]
      exact hG.differentiableOn
    exact (differentiableAt_const _).mul (hds s)
  -- the corners
  set z : ℂ := (x₁ : ℂ) + y₁ * I with hz
  set w : ℂ := (x₂ : ℂ) + y₂ * I with hw
  have hzre : z.re = x₁ := by simp [hz]
  have hzim : z.im = y₁ := by simp [hz]
  have hwre : w.re = x₂ := by simp [hw]
  have hwim : w.im = y₂ := by simp [hw]
  have hrect : [[z.re, w.re]] ×ℂ [[z.im, w.im]] = R := by rw [hzre, hzim, hwre, hwim]
  -- apply the residue theorem
  have hmain := ContourShift.rectBoundaryIntegral_eq_of_extension
    (fun s => G s * (deriv L s / L s)) K z w (by rw [hzre, hwre]; exact hx) (by rw [hzim, hwim]; exact hy) P
    (by
      intro p hp
      rw [hP, Finset.mem_image] at hp
      obtain ⟨ρ, hρ, rfl⟩ := hp
      obtain ⟨hρR, hρ0⟩ := (memZ ρ).mp hρ
      rw [hzre, hzim, hwre, hwim]
      exact hbd ρ hρR hρ0)
    (by rw [hrect]; exact hKd)
    (by
      intro s hs hsP
      rw [hrect] at hs
      have hsZ : ∀ ρ ∈ Z, s ≠ ρ := fun ρ hρ =>
        hsP ⟨ρ, (m ρ : ℂ) * G ρ⟩ (Finset.mem_image_of_mem _ hρ)
      have hsZ' : s ∉ Z := fun h => hsZ s h rfl
      have hL0 : L s ≠ 0 := fun h0 => hsZ' ((memZ s).mpr ⟨hs, h0⟩)
      have hH := hHeq s hsZ'
      have hid : deriv L s / L s = H s + ∑ q ∈ Z, (m q : ℂ) / (s - q) := by
        rw [hH, hH₀]; ring
      rw [hid, hPP, hK]
      beta_reduce
      have hsum : ∀ ρ ∈ Z, (m ρ : ℂ) * dslope G ρ s = (m ρ : ℂ) * ((G s - G ρ) / (s - ρ)) := by
        intro ρ hρ
        rw [dslope_of_ne G (hsZ ρ hρ), slope_def_field]
      rw [Finset.sum_congr rfl hsum, mul_add, Finset.mul_sum]
      have hsum2 : ∑ ρ ∈ Z, G s * ((m ρ : ℂ) / (s - ρ))
          = ∑ ρ ∈ Z, ((m ρ : ℂ) * ((G s - G ρ) / (s - ρ)) + (m ρ : ℂ) * G ρ / (s - ρ)) := by
        refine Finset.sum_congr rfl (fun ρ hρ => ?_)
        have hne : s - ρ ≠ 0 := sub_ne_zero.mpr (hsZ ρ hρ)
        field_simp
        ring
      rw [hsum2, Finset.sum_add_distrib]
      ring)
    (by
      have hcont : ∀ s ∈ R, (s.re = x₁ ∨ s.re = x₂ ∨ s.im = y₁ ∨ s.im = y₂) →
          ContinuousAt (fun s => G s * (deriv L s / L s)) s := by
        intro s hs hbd'
        refine continuousAt_logDeriv_mul hL hG.continuous (fun h0 => ?_)
        have := hbd s hs h0
        rcases hbd' with h | h | h | h <;> linarith [this.1, this.2.1, this.2.2.1, this.2.2.2]
      refine ⟨?_, ?_, ?_, ?_⟩
      · refine ContinuousOn.intervalIntegrable fun x hxI => ?_
        have hs : (x : ℂ) + z.im * I ∈ R := by
          rw [← hrect, mem_reProdIm]; simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
            mul_zero, mul_one, sub_zero, add_zero, add_im, mul_im, zero_add]
          exact ⟨hxI, left_mem_uIcc⟩
        exact (ContinuousAt.comp (g := fun s => G s * (deriv L s / L s)) (f := fun x : ℝ => (x : ℂ) + z.im * I)
          (hcont _ hs (Or.inr (Or.inr (Or.inl (by simp [hzim]))))) (by fun_prop)).continuousWithinAt
      · refine ContinuousOn.intervalIntegrable fun x hxI => ?_
        have hs : (x : ℂ) + w.im * I ∈ R := by
          rw [← hrect, mem_reProdIm]; simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
            mul_zero, mul_one, sub_zero, add_zero, add_im, mul_im, zero_add]
          exact ⟨hxI, right_mem_uIcc⟩
        exact (ContinuousAt.comp (g := fun s => G s * (deriv L s / L s)) (f := fun x : ℝ => (x : ℂ) + w.im * I)
          (hcont _ hs (Or.inr (Or.inr (Or.inr (by simp [hwim]))))) (by fun_prop)).continuousWithinAt
      · refine ContinuousOn.intervalIntegrable fun y hyI => ?_
        have hs : (w.re : ℂ) + y * I ∈ R := by
          rw [← hrect, mem_reProdIm]; simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
            mul_zero, mul_one, sub_zero, add_zero, add_im, mul_im, zero_add]
          exact ⟨right_mem_uIcc, hyI⟩
        exact (ContinuousAt.comp (g := fun s => G s * (deriv L s / L s)) (f := fun y : ℝ => (w.re : ℂ) + y * I)
          (hcont _ hs (Or.inr (Or.inl (by simp [hwre])))) (by fun_prop)).continuousWithinAt
      · refine ContinuousOn.intervalIntegrable fun y hyI => ?_
        have hs : (z.re : ℂ) + y * I ∈ R := by
          rw [← hrect, mem_reProdIm]; simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
            mul_zero, mul_one, sub_zero, add_zero, add_im, mul_im, zero_add]
          exact ⟨left_mem_uIcc, hyI⟩
        exact (ContinuousAt.comp (g := fun s => G s * (deriv L s / L s)) (f := fun y : ℝ => (z.re : ℂ) + y * I)
          (hcont _ hs (Or.inl (by simp [hzre]))) (by fun_prop)).continuousWithinAt)
  rw [hmain, hP, Finset.sum_image hinj]

/-! ## Finite exponential sums -/

/-- **A finite exponential sum cannot be `O(e^{as})` below its top exponent.** If
`‖Σ_{i ∈ T} e^{w_i s}‖ ≤ A e^{a s}` for all `s ≥ 1/4`, then `Re w_i ≤ a` for every `i ∈ T` (`a ≥ 0`). -/
theorem exp_detect {ι : Type*} [DecidableEq ι] (T : Finset ι) (w : ι → ℂ) {i₀ : ι} (hi₀ : i₀ ∈ T)
    {a A : ℝ} (ha0 : 0 ≤ a) (ha : a < (w i₀).re)
    (h : ∀ s : ℝ, 1 / 4 ≤ s → ‖∑ i ∈ T, cexp (w i * s)‖ ≤ A * Real.exp (a * s)) : False := by
  obtain ⟨im, him, hmax⟩ := T.exists_max_image (fun i => (w i).re) ⟨i₀, hi₀⟩
  set M := (w im).re with hM
  have hMa : a < M := lt_of_lt_of_le ha (hmax i₀ hi₀)
  set S := T.filter (fun i => (w i).re = M) with hS
  have hSne : S.Nonempty := ⟨im, Finset.mem_filter.mpr ⟨him, rfl⟩⟩
  set U := T.filter (fun i => ¬ (w i).re = M) with hU
  obtain ⟨ε, hε, hgap⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ U, (w i).re ≤ M - ε := by
    by_cases hUn : U.Nonempty
    · obtain ⟨j, hj, hjmax⟩ := U.exists_max_image (fun i => (w i).re) hUn
      have hj' := Finset.mem_filter.mp hj
      refine ⟨M - (w j).re, sub_pos.mpr (lt_of_le_of_ne (hmax j hj'.1) hj'.2), fun i hi => ?_⟩
      have := hjmax i hi
      linarith
    · refine ⟨1, one_pos, fun i hi => absurd ⟨i, hi⟩ hUn⟩
  have hEst : ∀ s : ℝ, 1 / 4 ≤ s →
      ‖∑ i ∈ S, cexp (I * ((w i).im : ℂ) * (s : ℂ))‖
        ≤ A * Real.exp (-((M - a) * s)) + T.card * Real.exp (-(ε * s)) := by
    intro s hs
    have hs0 : 0 ≤ s := by linarith
    have hsplit : ∑ i ∈ T, cexp (w i * s) = ∑ i ∈ S, cexp (w i * s) + ∑ i ∈ U, cexp (w i * s) :=
      (Finset.sum_filter_add_sum_filter_not T _ _).symm
    have hSpart : ∑ i ∈ S, cexp (w i * s)
        = ((Real.exp (M * s) : ℝ) : ℂ) * ∑ i ∈ S, cexp (I * ((w i).im : ℂ) * (s : ℂ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hre : (w i).re = M := (Finset.mem_filter.mp hi).2
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      conv_lhs => rw [← Complex.re_add_im (w i)]
      rw [hre]; push_cast; ring
    have hrest : ‖∑ i ∈ U, cexp (w i * s)‖ ≤ T.card * Real.exp ((M - ε) * s) := by
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ (Real.exp ((M - ε) * s)) fun i hi => ?_).trans ?_
      · rw [Complex.norm_exp]
        have e : (w i * (s : ℂ)).re = (w i).re * s := by simp
        rw [e]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hgap i hi) hs0)
      · rw [nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_filter_le _ _) (Real.exp_pos _).le
    have h1 := h s hs
    rw [hsplit] at h1
    have h2 : ‖∑ i ∈ S, cexp (w i * s)‖ ≤ A * Real.exp (a * s) + T.card * Real.exp ((M - ε) * s) := by
      have := norm_sub_le (∑ i ∈ S, cexp (w i * s) + ∑ i ∈ U, cexp (w i * s)) (∑ i ∈ U, cexp (w i * s))
      rw [add_sub_cancel_right] at this
      linarith
    rw [hSpart, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h2
    have hE := Real.exp_pos (M * s)
    refine le_of_mul_le_mul_left ?_ hE
    have e1 : Real.exp (M * s) * Real.exp (-((M - a) * s)) = Real.exp (a * s) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (M * s) * Real.exp (-(ε * s)) = Real.exp ((M - ε) * s) := by
      rw [← Real.exp_add]; congr 1; ring
    calc Real.exp (M * s) * ‖∑ i ∈ S, cexp (I * ((w i).im : ℂ) * (s : ℂ))‖
        ≤ A * Real.exp (a * s) + T.card * Real.exp ((M - ε) * s) := h2
      _ = Real.exp (M * s) * (A * Real.exp (-((M - a) * s)) + T.card * Real.exp (-(ε * s))) := by
          rw [mul_add, ← mul_assoc, mul_comm (Real.exp (M * s)) A, mul_assoc, e1,
            ← mul_assoc, mul_comm (Real.exp (M * s)) (T.card : ℝ), mul_assoc, e2]
  have hlin : ∀ k : ℝ, 0 < k → Tendsto (fun s : ℝ => Real.exp (-(k * s))) atTop (𝓝 0) := by
    intro k hk
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hk)
  have hB : Tendsto (fun s : ℝ => A * Real.exp (-((M - a) * s)) + T.card * Real.exp (-(ε * s)))
      atTop (𝓝 0) := by
    have := ((hlin _ (sub_pos.mpr hMa)).const_mul A).add ((hlin _ hε).const_mul (T.card : ℝ))
    simpa using this
  obtain ⟨S₁, hS₁⟩ := Filter.eventually_atTop.mp (hB.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨s, hs, hlarge⟩ :=
    ExpSumLowerBound.exists_large_of_nonempty S hSne (fun i => (w i).im) (max S₁ (1 / 4))
  have h1 := hS₁ s (le_trans (le_max_left _ _) hs)
  have h2 := hEst s (le_trans (le_max_right _ _) hs)
  linarith

/-! ## Gaussian bounds on the edges -/

lemma norm_LGw_le_two {b : ℝ} (hb : 0 < b) (α x y : ℝ) (hx : (x - 1 / 2) ^ 2 ≤ (y + α) ^ 2)
    (hx' : (x - 1 / 2) ^ 2 ≤ (y - α) ^ 2) :
    ‖LGw b α ((x : ℂ) + y * I)‖ ≤ 2 * Real.sqrt (π / b) := by
  refine (norm_LGw_le b α x y).trans ?_
  have h1 : Real.exp ((x - 1 / 2) ^ 2 / (4 * b)) * Real.exp (-(y + α) ^ 2 / (4 * b)) ≤ 1 := by
    rw [← Real.exp_add, Real.exp_le_one_iff, ← add_div]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have h2 : Real.exp ((x - 1 / 2) ^ 2 / (4 * b)) * Real.exp (-(y - α) ^ 2 / (4 * b)) ≤ 1 := by
    rw [← Real.exp_add, Real.exp_le_one_iff, ← add_div]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have hs := Real.sqrt_nonneg (π / b)
  nlinarith

lemma norm_LGw_le_left {b : ℝ} (hb : 0 < b) (α x y : ℝ) :
    ‖LGw b α ((x : ℂ) + y * I)‖ ≤ 2 * Real.sqrt (π / b) * Real.exp ((x - 1 / 2) ^ 2 / (4 * b)) := by
  refine (norm_LGw_le b α x y).trans ?_
  have h1 : Real.exp (-(y + α) ^ 2 / (4 * b)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (y + α)]) (by positivity))
  have h2 : Real.exp (-(y - α) ^ 2 / (4 * b)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (y - α)]) (by positivity))
  have hs := Real.sqrt_nonneg (π / b)
  have hE := (Real.exp_pos ((x - 1 / 2) ^ 2 / (4 * b))).le
  nlinarith [mul_nonneg hs hE]

lemma exp_tail_le {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) {u : ℝ} (hu : 2 ≤ u ^ 2) :
    Real.exp (1 / (4 * b)) * Real.exp (-u ^ 2 / (4 * b)) ≤ Real.exp (-u ^ 2 / 8) := by
  rw [← Real.exp_add, Real.exp_le_exp, ← add_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

lemma norm_LGw_le_tail {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (α y : ℝ) (h1 : 2 ≤ (y + α) ^ 2)
    (h2 : 2 ≤ (y - α) ^ 2) :
    ‖LGw b α (((3 / 2 : ℝ) : ℂ) + y * I)‖
      ≤ Real.sqrt (π / b) * (Real.exp (-(y + α) ^ 2 / 8) + Real.exp (-(y - α) ^ 2 / 8)) := by
  refine (norm_LGw_le b α (3 / 2) y).trans ?_
  have e : ((3 / 2 : ℝ) - 1 / 2) ^ 2 / (4 * b) = 1 / (4 * b) := by norm_num
  rw [e, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  rw [mul_add]
  exact add_le_add (exp_tail_le hb hb1 h1) (exp_tail_le hb hb1 h2)

/-- A continuous path on a compact interval avoiding the zeros of `L` keeps `L'/L` bounded. -/
lemma exists_bound_logDeriv_path {L : ℂ → ℂ} (hL : Differentiable ℂ L) {p : ℝ → ℂ} (hp : Continuous p)
    (a₁ a₂ : ℝ) (hne : ∀ x ∈ Set.uIcc a₁ a₂, L (p x) ≠ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Set.uIcc a₁ a₂, ‖deriv L (p x) / L (p x)‖ ≤ K := by
  have hc : ContinuousOn (fun x => deriv L (p x) / L (p x)) (Set.uIcc a₁ a₂) := by
    intro x hx
    exact ((((differentiable_deriv_of_entire hL).continuous.comp hp).continuousAt).div
      ((hL.continuous.comp hp).continuousAt) (hne x hx)).continuousWithinAt
  obtain ⟨K, hK⟩ := isCompact_uIcc.exists_bound_of_continuousOn hc
  exact ⟨max K 0, le_max_right _ _, fun x hx => (hK x hx).trans (le_max_left _ _)⟩

/-! ## The detection theorem -/

/-- **The Gaussian prime line** `∫ LGw b α (3/2+it) · (L'/L)(3/2+it) dt`. -/
def primeLine (L : ℂ → ℂ) (b α : ℝ) : ℂ :=
  ∫ t : ℝ, LGw b α (((3 / 2 : ℝ) : ℂ) + t * I)
    * (deriv L (((3 / 2 : ℝ) : ℂ) + t * I) / L (((3 / 2 : ℝ) : ℂ) + t * I))

/-- The right edge of the rectangle against the full prime line: the two tails cost `O(√(π/b))`. -/
lemma norm_right_edge_le {L : ℂ → ℂ} (hL : Differentiable ℂ L) (hL1 : ∀ w : ℂ, 1 ≤ w.re → L w ≠ 0)
    {B : ℝ} (hB : ∀ t : ℝ, ‖deriv L (((3 / 2 : ℝ) : ℂ) + t * I) / L (((3 / 2 : ℝ) : ℂ) + t * I)‖ ≤ B)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (α Y : ℝ) (hY : 0 ≤ Y) (hYα : |α| + 2 ≤ Y) :
    ‖∫ y in (-Y)..Y, LGw b α (((3 / 2 : ℝ) : ℂ) + y * I)
      * (deriv L (((3 / 2 : ℝ) : ℂ) + y * I) / L (((3 / 2 : ℝ) : ℂ) + y * I))‖
      ≤ ‖primeLine L b α‖ + B * Real.sqrt (π / b) * (2 * Real.sqrt (8 * π)) := by
  set g : ℝ → ℂ := fun y => LGw b α (((3 / 2 : ℝ) : ℂ) + y * I)
      * (deriv L (((3 / 2 : ℝ) : ℂ) + y * I) / L (((3 / 2 : ℝ) : ℂ) + y * I)) with hg
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hne : ∀ y : ℝ, L (((3 / 2 : ℝ) : ℂ) + y * I) ≠ 0 := fun y => hL1 _ (by simp; norm_num)
  have hgc : Continuous g := by
    refine ((differentiable_LGw b α).continuous.comp (continuous_line _)).mul ?_
    refine continuous_iff_continuousAt.mpr fun y => ?_
    exact (((differentiable_deriv_of_entire hL).continuous.comp (continuous_line _)).continuousAt).div
      ((hL.continuous.comp (continuous_line _)).continuousAt) (hne y)
  have hgi : Integrable g := by
    refine Integrable.mono' ((integrable_LGw_line hb α (3 / 2)).norm.mul_const B) hgc.aestronglyMeasurable
      (ae_of_all _ fun y => ?_)
    simp only [hg, norm_mul]
    exact mul_le_mul_of_nonneg_left (hB y) (norm_nonneg _)
  set h : ℝ → ℝ := fun y => B * Real.sqrt (π / b) * (Real.exp (-(y + α) ^ 2 / 8) + Real.exp (-(y - α) ^ 2 / 8))
    with hh
  have hhi : Integrable h := by
    have e : ∀ β : ℝ, (fun y : ℝ => Real.exp (-(y + β) ^ 2 / 8)) = fun y => Real.exp (-(y - (-β)) ^ 2 / 8) := by
      intro β; funext y; congr 2; ring
    have i1 : Integrable (fun y : ℝ => Real.exp (-(y + α) ^ 2 / 8)) := by
      rw [e]; exact integrable_gauss_scale (by norm_num) _
    exact (i1.add (integrable_gauss_scale (by norm_num) α)).const_mul _
  have hint_h : ∫ y, h y = B * Real.sqrt (π / b) * (2 * Real.sqrt (8 * π)) := by
    simp only [hh]
    have e : (fun y : ℝ => Real.exp (-(y + α) ^ 2 / 8)) = fun y => Real.exp (-(y - (-α)) ^ 2 / 8) := by
      funext y; congr 2; ring
    have i1 : Integrable (fun y : ℝ => Real.exp (-(y + α) ^ 2 / 8)) := by
      rw [e]; exact integrable_gauss_scale (by norm_num) _
    rw [MeasureTheory.integral_const_mul, integral_add i1 (integrable_gauss_scale (by norm_num) α), e,
      integral_gauss_scale (by norm_num), integral_gauss_scale (by norm_num)]
    rw [show π * 8 = 8 * π by ring]; ring
  have hh0 : ∀ y, 0 ≤ h y := fun y => by simp only [hh]; positivity
  set s : Set ℝ := Set.Ioc (-Y) Y with hs
  have hsplit := integral_add_compl (μ := volume) measurableSet_Ioc hgi (s := s)
  have hII : ∫ y in (-Y)..Y, g y = ∫ y in s, g y := intervalIntegral.integral_of_le (by linarith)
  have htail : ‖∫ y in sᶜ, g y‖ ≤ ∫ y, h y := by
    refine (norm_integral_le_of_norm_le hhi.integrableOn (ae_restrict_of_forall_mem
      measurableSet_Ioc.compl fun y hy => ?_)).trans
      (setIntegral_le_integral hhi (Eventually.of_forall hh0))
    have hyY : Y ≤ |y| := by
      simp only [hs, Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at hy
      rcases hy with h1 | h1
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have hα := neg_abs_le α
    have hα' := le_abs_self α
    have h1 : 2 ≤ (y + α) ^ 2 := by
      have : 2 ≤ |y + α| := by
        rcases le_or_gt 0 y with hy0 | hy0
        · rw [abs_of_nonneg hy0] at hyY; rw [abs_of_nonneg (by linarith)]; linarith
        · rw [abs_of_neg hy0] at hyY; rw [abs_of_nonpos (by linarith)]; linarith
      nlinarith [_root_.sq_abs (y + α)]
    have h2 : 2 ≤ (y - α) ^ 2 := by
      have : 2 ≤ |y - α| := by
        rcases le_or_gt 0 y with hy0 | hy0
        · rw [abs_of_nonneg hy0] at hyY; rw [abs_of_nonneg (by linarith)]; linarith
        · rw [abs_of_neg hy0] at hyY; rw [abs_of_nonpos (by linarith)]; linarith
      nlinarith [_root_.sq_abs (y - α)]
    simp only [hg, hh, norm_mul]
    calc ‖LGw b α (((3 / 2 : ℝ) : ℂ) + y * I)‖
          * ‖deriv L (((3 / 2 : ℝ) : ℂ) + y * I) / L (((3 / 2 : ℝ) : ℂ) + y * I)‖
        ≤ (Real.sqrt (π / b) * (Real.exp (-(y + α) ^ 2 / 8) + Real.exp (-(y - α) ^ 2 / 8))) * B :=
          mul_le_mul (norm_LGw_le_tail hb hb1 α y h1 h2) (hB y) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hpl : primeLine L b α = ∫ y, g y := rfl
  rw [hII, ← hint_h]
  have : ∫ y in s, g y = primeLine L b α - ∫ y in sᶜ, g y := by rw [hpl, ← hsplit]; ring
  rw [this]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl htail)

lemma mem_rect_iff {x₁ x₂ y₁ y₂ : ℝ} (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) {s : ℂ} :
    s ∈ rect x₁ x₂ y₁ y₂ ↔ x₁ ≤ s.re ∧ s.re ≤ x₂ ∧ y₁ ≤ s.im ∧ s.im ≤ y₂ := by
  rw [rect, mem_reProdIm, Set.uIcc_of_le hx, Set.uIcc_of_le hy, Set.mem_Icc, Set.mem_Icc, and_assoc]

lemma div_four_mul_inv (z : ℂ) {s : ℝ} (hs : 0 < s) :
    z / (4 * ((1 / (4 * s) : ℝ) : ℂ)) = z * s := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  push_cast
  field_simp

lemma one_le_sq_of_one_le {u : ℝ} (h : 1 ≤ u) : 1 ≤ u ^ 2 := by nlinarith

lemma one_le_sq_of_le_neg_one {u : ℝ} (h : u ≤ -1) : 1 ≤ u ^ 2 := by nlinarith

/-- A horizontal edge `[x₁, 3/2] × {y}` with `(y ± α)² ≥ 1` costs at most `2 √(π/b) K`. -/
lemma horiz_edge_le {L : ℂ → ℂ} {b : ℝ} (hb : 0 < b) (α x₁ y K : ℝ) (hx₁ : 1 / 2 ≤ x₁)
    (hx₁' : x₁ ≤ 3 / 2) (hy1 : 1 ≤ (y + α) ^ 2) (hy2 : 1 ≤ (y - α) ^ 2) (hK0 : 0 ≤ K)
    (hK : ∀ x ∈ Set.uIcc x₁ (3 / 2), ‖deriv L ((x : ℂ) + (y : ℂ) * I) / L ((x : ℂ) + (y : ℂ) * I)‖ ≤ K) :
    ‖∫ x in x₁..(3 / 2 : ℝ), LGw b α ((x : ℂ) + (y : ℂ) * I)
      * (deriv L ((x : ℂ) + (y : ℂ) * I) / L ((x : ℂ) + (y : ℂ) * I))‖ ≤ 2 * Real.sqrt (π / b) * K := by
  have hC0 : 0 ≤ 2 * Real.sqrt (π / b) * K := by positivity
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 2 * Real.sqrt (π / b) * K)
    fun x hx => ?_).trans ?_
  · have hxI : x ∈ Set.uIcc x₁ (3 / 2) := Set.uIoc_subset_uIcc hx
    have hx' := hxI
    rw [Set.uIcc_of_le hx₁'] at hx'
    have hxx : (x - 1 / 2) ^ 2 ≤ 1 := by nlinarith [hx'.1, hx'.2]
    rw [norm_mul]
    exact mul_le_mul (norm_LGw_le_two hb α x y (hxx.trans hy1) (hxx.trans hy2))
      (hK x hxI) (norm_nonneg _) (by positivity)
  · have h1 : |(3 / 2 : ℝ) - x₁| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
    calc 2 * Real.sqrt (π / b) * K * |(3 / 2 : ℝ) - x₁| ≤ 2 * Real.sqrt (π / b) * K * 1 :=
          mul_le_mul_of_nonneg_left h1 hC0
      _ = _ := mul_one _

/-- The left edge `{x₁} × [−Y, Y]` costs at most `2 √(π/b) e^{(x₁−1/2)²/4b} K · 2Y`. -/
lemma vert_edge_le {L : ℂ → ℂ} {b : ℝ} (hb : 0 < b) (α x₁ Y K : ℝ) (hY : 0 ≤ Y) (hK0 : 0 ≤ K)
    (hK : ∀ y ∈ Set.uIcc (-Y) Y, ‖deriv L ((x₁ : ℂ) + (y : ℂ) * I) / L ((x₁ : ℂ) + (y : ℂ) * I)‖ ≤ K) :
    ‖∫ y in (-Y)..Y, LGw b α ((x₁ : ℂ) + (y : ℂ) * I)
      * (deriv L ((x₁ : ℂ) + (y : ℂ) * I) / L ((x₁ : ℂ) + (y : ℂ) * I))‖
      ≤ 2 * Real.sqrt (π / b) * Real.exp ((x₁ - 1 / 2) ^ 2 / (4 * b)) * K * (2 * Y) := by
  refine (intervalIntegral.norm_integral_le_of_norm_le_const
    (C := 2 * Real.sqrt (π / b) * Real.exp ((x₁ - 1 / 2) ^ 2 / (4 * b)) * K) fun y hy => ?_).trans ?_
  · have hyI : y ∈ Set.uIcc (-Y) Y := Set.uIoc_subset_uIcc hy
    rw [norm_mul]
    exact mul_le_mul (norm_LGw_le_left hb α x₁ y) (hK y hyI) (norm_nonneg _) (by positivity)
  · rw [show Y - -Y = 2 * Y by ring, abs_of_nonneg (by linarith)]

/-- The closing arithmetic of `zero_detect`. -/
lemma detect_arith {S q KF C B Y k E1 E2 Ea : ℝ} (hq : 0 < q) (hS : 0 ≤ S) (hKF : 0 ≤ KF)
    (hB : 0 ≤ B) (hY : 0 ≤ Y) (hk : 0 ≤ k) (hE1 : C * E1 ≤ |C| * Ea) (hE2 : E2 ≤ Ea) (hE3 : 1 ≤ Ea)
    (h : 2 * π * q * S ≤ 2 * q * KF + 2 * q * KF + (q * (C * E1) + B * q * (2 * k))
      + 2 * q * E2 * KF * (2 * Y)) :
    S ≤ (1 / (2 * π)) * (4 * KF + |C| + 2 * k * B + 4 * Y * KF) * Ea := by
  have hpi : 0 < 2 * π := by positivity
  have h1 : 2 * π * S ≤ 4 * KF + C * E1 + 2 * k * B + 4 * Y * KF * E2 := by
    have h' : q * (2 * π * S) ≤ q * (4 * KF + C * E1 + 2 * k * B + 4 * Y * KF * E2) := by
      linarith
    exact le_of_mul_le_mul_left h' hq
  have h2 : 4 * KF + C * E1 + 2 * k * B + 4 * Y * KF * E2
      ≤ (4 * KF + |C| + 2 * k * B + 4 * Y * KF) * Ea := by
    have a1 : 4 * KF ≤ 4 * KF * Ea := le_mul_of_one_le_right (by positivity) hE3
    have a2 : 2 * k * B ≤ 2 * k * B * Ea := le_mul_of_one_le_right (by positivity) hE3
    have a3 : 4 * Y * KF * E2 ≤ 4 * Y * KF * Ea := mul_le_mul_of_nonneg_left hE2 (by positivity)
    nlinarith
  rw [mul_assoc, div_mul_eq_mul_div, one_mul, le_div_iff₀ hpi]
  linarith

/-- **Local zero detection.** Let `L` be entire, nonvanishing on `Re ≥ 1`, with `‖L'/L‖ ≤ B` on
`Re = 3/2`. If for every `α` there is `C` with `‖primeLine L b α‖ ≤ √(π/b) C e^{c/b}` (`0 < b ≤ 1`),
then every zero `ρ` of `L` with `Re ρ > 1/2` satisfies `(Re ρ − 1/2)² ≤ 4c`. -/
theorem zero_detect {L : ℂ → ℂ} (hL : Differentiable ℂ L) (hL1 : ∀ w : ℂ, 1 ≤ w.re → L w ≠ 0)
    {B : ℝ} (hB : ∀ t : ℝ, ‖deriv L (((3 / 2 : ℝ) : ℂ) + t * I) / L (((3 / 2 : ℝ) : ℂ) + t * I)‖ ≤ B)
    {c : ℝ} (hc : 0 ≤ c)
    (hP : ∀ α : ℝ, ∃ C : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      ‖primeLine L b α‖ ≤ Real.sqrt (π / b) * (C * Real.exp (c / b)))
    {ρ₀ : ℂ} (hρ₀ : L ρ₀ = 0) (hre : 1 / 2 < ρ₀.re) : (ρ₀.re - 1 / 2) ^ 2 ≤ 4 * c := by
  classical
  by_contra hcon
  push Not at hcon
  set δ := ρ₀.re - 1 / 2 with hδdef
  have hδ : 0 < δ := by linarith
  have hz₁ : L 2 ≠ 0 := hL1 2 (by norm_num)
  have hρ1 : ρ₀.re < 1 := by
    by_contra h
    push Not at h
    exact hL1 ρ₀ h hρ₀
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  set α : ℝ := -ρ₀.im with hα
  set Y₀ : ℝ := |ρ₀.im| + 3 with hY₀
  have hY₀3 : 3 ≤ Y₀ := by have := abs_nonneg ρ₀.im; linarith
  have hK₀c : IsCompact (rect 0 2 (-(Y₀ + 1)) (Y₀ + 1)) := isCompact_uIcc.reProdIm isCompact_uIcc
  set Zf := (finite_zeros hL hz₁ hK₀c).toFinset with hZf
  have memZf : ∀ s, s ∈ Zf ↔ s ∈ rect 0 2 (-(Y₀ + 1)) (Y₀ + 1) ∧ L s = 0 := fun s => by simp [hZf]
  obtain ⟨η, ⟨hη0, hηδ⟩, hηZ⟩ :=
    (Set.Ioo_infinite hδ).exists_notMem_finset (Zf.image fun z => z.re - 1 / 2)
  obtain ⟨Y, ⟨hY0, hY1⟩, hYZ⟩ := (Set.Ioo_infinite (show Y₀ < Y₀ + 1 by linarith)).exists_notMem_finset
    (Zf.image fun z => |z.im|)
  set x₁ : ℝ := 1 / 2 + η with hx₁
  have hx₁32 : x₁ < 3 / 2 := by linarith
  have hYpos : 0 < Y := by linarith
  have habsα : |α| = |ρ₀.im| := by rw [hα, abs_neg]
  -- the rectangle sits in `K₀`, and its zeros are interior
  have hsub : ∀ s ∈ rect x₁ (3 / 2) (-Y) Y, s ∈ rect 0 2 (-(Y₀ + 1)) (Y₀ + 1) := by
    intro s hs
    rw [mem_rect_iff hx₁32.le (by linarith)] at hs
    rw [mem_rect_iff (by norm_num) (by linarith)]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hbd : ∀ s ∈ rect x₁ (3 / 2) (-Y) Y, L s = 0 →
      x₁ < s.re ∧ s.re < 3 / 2 ∧ -Y < s.im ∧ s.im < Y := by
    intro s hs h0
    have hsZ : s ∈ Zf := (memZf s).mpr ⟨hsub s hs, h0⟩
    have hs' := (mem_rect_iff hx₁32.le (by linarith)).mp hs
    have hre1 : s.re < 1 := by
      by_contra h
      push Not at h
      exact hL1 s h h0
    have hne1 : s.re ≠ x₁ := by
      intro h
      apply hηZ
      rw [Finset.mem_image]
      exact ⟨s, hsZ, by rw [h, hx₁]; ring⟩
    have hne2 : |s.im| ≠ Y := by
      intro h
      apply hYZ
      rw [Finset.mem_image]
      exact ⟨s, hsZ, h⟩
    refine ⟨lt_of_le_of_ne hs'.1 (Ne.symm hne1), by linarith, ?_, ?_⟩
    · refine lt_of_le_of_ne hs'.2.2.1 fun h => hne2 ?_
      rw [← h, abs_neg, abs_of_pos hYpos]
    · refine lt_of_le_of_ne hs'.2.2.2 fun h => hne2 ?_
      rw [h, abs_of_pos hYpos]
  have hRc : IsCompact (rect x₁ (3 / 2) (-Y) Y) := isCompact_uIcc.reProdIm isCompact_uIcc
  set Z := (finite_zeros hL hz₁ hRc).toFinset with hZ
  have hZ1 : ∀ s ∈ rect x₁ (3 / 2) (-Y) Y, L s = 0 → s ∈ Z := fun s hs h0 => by simp [hZ, hs, h0]
  have hZ2 : ∀ ρ ∈ Z, ρ ∈ rect x₁ (3 / 2) (-Y) Y ∧ L ρ = 0 := fun ρ hρ => by simpa [hZ] using hρ
  have hρ₀Z : ρ₀ ∈ Z := by
    refine hZ1 ρ₀ ?_ hρ₀
    rw [mem_rect_iff hx₁32.le (by linarith)]
    have h1 := neg_abs_le ρ₀.im
    have h2 := le_abs_self ρ₀.im
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  -- the edge bound for `L'/L`
  have hedge : ∀ s ∈ rect x₁ (3 / 2) (-Y) Y,
      (s.re = x₁ ∨ s.re = 3 / 2 ∨ s.im = -Y ∨ s.im = Y) → L s ≠ 0 := by
    intro s hs hb h0
    have := hbd s hs h0
    rcases hb with h | h | h | h <;> linarith [this.1, this.2.1, this.2.2.1, this.2.2.2]
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_bound_logDeriv_path hL (p := fun x : ℝ => (x : ℂ) + ((-Y : ℝ) : ℂ) * I)
    (by fun_prop) x₁ (3 / 2) (fun x hx => hedge _ (by
      rw [Set.uIcc_of_le hx₁32.le] at hx
      rw [mem_rect_iff hx₁32.le (by linarith)]; simp; exact ⟨hx.1, hx.2, by linarith⟩)
      (Or.inr (Or.inr (Or.inl (by simp)))))
  obtain ⟨K₂, hK₂0, hK₂⟩ := exists_bound_logDeriv_path hL (p := fun x : ℝ => (x : ℂ) + (Y : ℂ) * I)
    (by fun_prop) x₁ (3 / 2) (fun x hx => hedge _ (by
      rw [Set.uIcc_of_le hx₁32.le] at hx
      rw [mem_rect_iff hx₁32.le (by linarith)]; simp; exact ⟨hx.1, hx.2, by linarith⟩)
      (Or.inr (Or.inr (Or.inr (by simp)))))
  obtain ⟨K₃, hK₃0, hK₃⟩ := exists_bound_logDeriv_path hL (p := fun y : ℝ => (x₁ : ℂ) + (y : ℂ) * I)
    (by fun_prop) (-Y) Y (fun y hy => hedge _ (by
      rw [Set.uIcc_of_le (by linarith)] at hy
      rw [mem_rect_iff hx₁32.le (by linarith)]; simp; exact ⟨by linarith, hy.1, hy.2⟩)
      (Or.inl (by simp)))
  set KF := K₁ + K₂ + K₃ with hKF
  have hKF0 : 0 ≤ KF := by positivity
  obtain ⟨C, hC⟩ := hP α
  -- the index set and exponents
  set m : ℂ → ℕ := fun ρ => analyticOrderNatAt L ρ with hm
  set T : Finset (Σ ρ : ℂ, Fin (m ρ) × Bool) := Z.sigma fun _ => Finset.univ with hT
  set wv : (Σ ρ : ℂ, Fin (m ρ) × Bool) → ℂ := fun x =>
    if x.2.2 then (x.1 - 1 / 2 + I * α) ^ 2 else (x.1 - 1 / 2 - I * α) ^ 2 with hwv
  have hsumT : ∀ s : ℝ, ∑ x ∈ T, cexp (wv x * s) = ∑ ρ ∈ Z, (m ρ : ℂ) *
      (cexp ((ρ - 1 / 2 + I * α) ^ 2 * s) + cexp ((ρ - 1 / 2 - I * α) ^ 2 * s)) := by
    intro s
    rw [hT, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [← Finset.univ_product_univ, Finset.sum_product]
    simp [hwv, Fintype.sum_bool, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] <;> ring
  -- the main estimate
  set a : ℝ := max (4 * c) (η ^ 2) with ha
  have ha0 : 0 ≤ a := le_trans (by positivity : (0 : ℝ) ≤ 4 * c) (le_max_left _ _)
  set A : ℝ := (1 / (2 * π)) * (4 * KF + |C| + 2 * Real.sqrt (8 * π) * B + 4 * Y * KF) with hA
  have key : ∀ s : ℝ, 1 / 4 ≤ s → ‖∑ x ∈ T, cexp (wv x * s)‖ ≤ A * Real.exp (a * s) := by
    intro s hs
    have hs0 : 0 < s := by linarith
    set b : ℝ := 1 / (4 * s) with hbdef
    have hb : 0 < b := by positivity
    have hb1 : b ≤ 1 := by rw [hbdef, div_le_one (by positivity)]; linarith
    have hsb : 1 / (4 * b) = s := by rw [hbdef]; field_simp
    have hsq : 0 < Real.sqrt (π / b) := Real.sqrt_pos.mpr (by positivity)
    -- the residue sum in terms of `LGw`
    have hLG : ∀ ρ : ℂ, LGw b α ρ = (Real.sqrt (π / b) : ℂ) *
        (cexp ((ρ - 1 / 2 + I * α) ^ 2 * s) + cexp ((ρ - 1 / 2 - I * α) ^ 2 * s)) := by
      intro ρ
      unfold LGw
      rw [hbdef, div_four_mul_inv _ hs0, div_four_mul_inv _ hs0]
    have hres := rect_logDeriv_residue hL hz₁ (G := LGw b α) (differentiable_LGw b α) hx₁32
      (show -Y < Y by linarith) hbd Z hZ1 hZ2
    rw [RectangleResidue.rectBoundaryIntegral_eq_rectInt] at hres
    unfold RectangleWinding.rectInt at hres
    have hSig : ∑ ρ ∈ Z, (analyticOrderNatAt L ρ : ℂ) * LGw b α ρ
        = (Real.sqrt (π / b) : ℂ) * ∑ x ∈ T, cexp (wv x * s) := by
      rw [hsumT, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [hLG]; ring
    rw [hSig] at hres
    -- edge bounds
    have hYα1 : 3 < Y - α := by have := le_abs_self α; linarith
    have hYα2 : 3 < Y + α := by have := neg_abs_le α; linarith
    have hK1F : K₁ ≤ KF := by linarith
    have hK2F : K₂ ≤ KF := by linarith
    have hK3F : K₃ ≤ KF := by linarith
    have hsq0 := hsq.le
    have hbot := horiz_edge_le (L := L) hb α x₁ (-Y) KF (by linarith) hx₁32.le
      (one_le_sq_of_le_neg_one (by linarith)) (one_le_sq_of_le_neg_one (by linarith)) hKF0
      (fun x hx => (hK₁ x hx).trans hK1F)
    have htop := horiz_edge_le (L := L) hb α x₁ Y KF (by linarith) hx₁32.le
      (one_le_sq_of_one_le (by linarith)) (one_le_sq_of_one_le (by linarith)) hKF0
      (fun x hx => (hK₂ x hx).trans hK2F)
    have hleft := vert_edge_le (L := L) hb α x₁ Y KF hYpos.le hKF0 (fun y hy => (hK₃ y hy).trans hK3F)
    have e : (x₁ - 1 / 2) ^ 2 / (4 * b) = η ^ 2 * s := by rw [hx₁, ← hsb]; ring
    rw [e] at hleft
    have hright := norm_right_edge_le hL hL1 hB hb hb1 α Y hYpos.le (by linarith)
    have hPl := hC b hb hb1
    have hcb : c / b = 4 * c * s := by rw [hbdef]; field_simp
    rw [hcb] at hPl
    -- assemble
    have hnorm : 2 * π * Real.sqrt (π / b) * ‖∑ x ∈ T, cexp (wv x * s)‖
        ≤ 2 * Real.sqrt (π / b) * KF + 2 * Real.sqrt (π / b) * KF
          + (Real.sqrt (π / b) * (C * Real.exp (4 * c * s)) + B * Real.sqrt (π / b) * (2 * Real.sqrt (8 * π)))
          + 2 * Real.sqrt (π / b) * Real.exp (η ^ 2 * s) * KF * (2 * Y) := by
      have h := congrArg norm hres
      rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_pos hsq,
        show ‖(2 : ℂ)‖ = 2 by norm_num, mul_one] at h
      rw [mul_assoc (2 * π), ← h]
      refine (norm_sub_le _ _).trans ?_
      refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
      refine (add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]
      exact add_le_add (add_le_add (add_le_add hbot htop) (hright.trans (add_le_add hPl le_rfl))) hleft
    have hE1 : Real.exp (4 * c * s) ≤ Real.exp (a * s) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) hs0.le)
    have hE2 : Real.exp (η ^ 2 * s) ≤ Real.exp (a * s) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) hs0.le)
    have hE3 : 1 ≤ Real.exp (a * s) := Real.one_le_exp (by positivity)
    have hCa : C * Real.exp (4 * c * s) ≤ |C| * Real.exp (a * s) :=
      (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le).trans
        (mul_le_mul_of_nonneg_left hE1 (abs_nonneg C))
    exact detect_arith hsq (norm_nonneg _) hKF0 hB0 hYpos.le (Real.sqrt_nonneg _) hCa hE2 hE3 hnorm
  -- the zero `ρ₀` gives an exponent above `a`
  have hm0 : 0 < m ρ₀ := one_le_order_of_zero hL hz₁ hρ₀
  have hi₀ : (⟨ρ₀, (⟨0, hm0⟩, true)⟩ : (Σ ρ : ℂ, Fin (m ρ) × Bool)) ∈ T := by
    rw [hT, Finset.mem_sigma]; exact ⟨hρ₀Z, Finset.mem_univ _⟩
  have hw₀ : wv ⟨ρ₀, (⟨0, hm0⟩, true)⟩ = ((δ ^ 2 : ℝ) : ℂ) := by
    simp only [hwv, if_true]
    have e : ρ₀ - 1 / 2 + I * (α : ℂ) = (δ : ℂ) := by
      apply Complex.ext <;> simp [hα, hδdef]
    rw [e]; push_cast; ring
  have ha_lt : a < (wv ⟨ρ₀, (⟨0, hm0⟩, true)⟩).re := by
    rw [hw₀, Complex.ofReal_re]
    exact max_lt hcon (by nlinarith)
  exact exp_detect T wv hi₀ ha0 ha_lt key
end FleetTwistedWindow
