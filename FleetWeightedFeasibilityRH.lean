import FleetLaplacePole
import FleetWeightedLimit
import FleetDualInequality
import FleetPrimeSideConsequences

/-!
# Weighted feasibility ⇒ RH (integrality is not needed)

`research_notes/DUAL-INEQUALITY/CONVERSE.md`, "Paper-level result: integrality is not needed": if for
one budget `M` every stage has a *weighted* solution with tolerance `→ 0`, then RH holds. Hence

  `RH ⇔ ∃ M, ∀ n, WeightedFeasible R M (1/(n+1)) n ⇔ ∃ M > 0, ∀ n, DualIneq R M (1/(n+1)) n`.

Proof, following the note's steps 1–4.
1. `FleetWeightedLimit.exists_entire_realization`: an entire `F` with `F q = R q` on `ℚ` and
   `‖F(iy)‖ ≤ C e^{y²/4}` (limit of the weighted atoms as a finite measure on `OnePoint ℝ`).
2. The zero side `Z̃ z = ½ Σ_ρ [g(t_ρ − z) + g(conj t_ρ − z)]`, `g w = √π e^{-w²/4}`, is entire and
   equals `Re rhs(gauss 1 q) = R q` on real `q` (explicit formula, `zero_trace_eq_rhs`). So `F = Z̃`.
   (Symmetrizing with `conj t_ρ` replaces the note's use of the reality of the zero sum.)
3. `Z̃(iy) = √π e^{y²/4} Σ cₖ e^{λₖ y}` with `λ = i u/2`, `cₖ = ½ e^{λₖ²}` over `u ∈ {t_ρ, conj t_ρ}`;
   so the exponential series is bounded on the real line.
4. `FleetLaplacePole.re_nonpos_of_bounded`: every `Re λₖ = −Im uₖ/2 ≤ 0`; applied to `t_ρ` and to
   `conj t_ρ` this gives `Im t_ρ = 0` for every zero.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Set MeasureTheory
open scoped ComplexConjugate
open OffLineDetection ZeroSumLimit Reduction GaussianTest

namespace FleetWeightedFeasibilityRH

/-- The width-one Gaussian `g w = √π e^{-w²/4}`. -/
def gk (w : ℂ) : ℂ := (Real.sqrt Real.pi : ℂ) * cexp (-w ^ 2 / 4)

/-- Ordinates and their conjugates. -/
def u : Index ⊕ Index → ℂ := Sum.elim t (fun x => conj (t x))

/-- The underlying zero. -/
def base : Index ⊕ Index → Index := Sum.elim id id

lemma u_re (k : Index ⊕ Index) : (u k).re = (t (base k)).re := by
  cases k <;> simp [u, base]

lemma abs_u_im (k : Index ⊕ Index) : |(u k).im| < 1 / 2 := by
  cases k with
  | inl x => simpa [u] using abs_t_im_lt x
  | inr x => simpa [u, abs_neg] using abs_t_im_lt x

lemma exp_neg_sq_div_eight_le (a : ℝ) : Real.exp (-a ^ 2 / 8) ≤ 8 / (1 + a ^ 2) := by
  have he : 1 + a ^ 2 / 8 ≤ Real.exp (a ^ 2 / 8) := by linarith [Real.add_one_le_exp (a ^ 2 / 8)]
  have hm : Real.exp (-a ^ 2 / 8) * Real.exp (a ^ 2 / 8) = 1 := by
    rw [← Real.exp_add, show -a ^ 2 / 8 + a ^ 2 / 8 = 0 by ring, Real.exp_zero]
  rw [le_div_iff₀ (by positivity)]
  have hp := Real.exp_pos (-a ^ 2 / 8)
  nlinarith

/-- Uniform Gaussian bound on the strip: `‖z‖ ≤ r`, `|Im v| < 1/2`. -/
lemma norm_cexp_le {r : ℝ} {z v : ℂ} (hz : ‖z‖ ≤ r) (hv : |v.im| < 1 / 2) :
    ‖cexp (-(v - z) ^ 2 / 4)‖ ≤ Real.exp ((r ^ 2 + (1 / 2 + r) ^ 2) / 4) * (8 / (1 + v.re ^ 2)) := by
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (exp_neg_sq_div_eight_le v.re) (by positivity))
  rw [Complex.norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have hre : (-(v - z) ^ 2 / 4).re = (-(v.re - z.re) ^ 2 + (v.im - z.im) ^ 2) / 4 := by
    simp [sq, Complex.mul_re]; ring
  rw [hre]
  have h1 : |z.re| ≤ r := (Complex.abs_re_le_norm z).trans hz
  have h2 : |z.im| ≤ r := (Complex.abs_im_le_norm z).trans hz
  have h3 : (v.im - z.im) ^ 2 ≤ (1 / 2 + r) ^ 2 := by
    have : |v.im - z.im| ≤ 1 / 2 + r := (abs_sub _ _).trans (by linarith)
    have h0 : 0 ≤ |v.im - z.im| := abs_nonneg _
    nlinarith [sq_abs (v.im - z.im)]
  have h4 : z.re ^ 2 ≤ r ^ 2 := by
    have h0 : 0 ≤ |z.re| := abs_nonneg _
    nlinarith [sq_abs z.re]
  nlinarith [sq_nonneg (v.re - 2 * z.re)]

lemma summable_inv_u : Summable (fun k : Index ⊕ Index => 8 / (1 + (u k).re ^ 2)) := by
  have hs : Summable (fun x : Index => 8 / (1 + (t x).re ^ 2)) := by
    have := summable_inv_one_add_sq_re.mul_left 8
    refine this.congr (fun x => ?_); ring
  refine Summable.sum _ ?_ ?_ <;> refine hs.congr (fun x => ?_) <;> simp [u]

/-- The symmetrized zero side. -/
def Ztil (z : ℂ) : ℂ := ∑' k : Index ⊕ Index, gk (u k - z) / 2

lemma norm_term_le {r : ℝ} {z : ℂ} (hz : ‖z‖ ≤ r) (k : Index ⊕ Index) :
    ‖gk (u k - z) / 2‖ ≤ Real.sqrt Real.pi / 2 * Real.exp ((r ^ 2 + (1 / 2 + r) ^ 2) / 4) *
      (8 / (1 + (u k).re ^ 2)) := by
  simp only [gk, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_two]
  have := norm_cexp_le hz (abs_u_im k)
  have hs := Real.sqrt_nonneg Real.pi
  calc Real.sqrt Real.pi * ‖cexp (-(u k - z) ^ 2 / 4)‖ / 2
      ≤ Real.sqrt Real.pi * (Real.exp ((r ^ 2 + (1 / 2 + r) ^ 2) / 4) * (8 / (1 + (u k).re ^ 2))) / 2 := by
        gcongr
    _ = _ := by ring

theorem differentiable_Ztil : Differentiable ℂ Ztil := by
  intro z₀
  set r : ℝ := ‖z₀‖ + 1
  have hd : DifferentiableOn ℂ Ztil (Metric.ball z₀ 1) := by
    refine differentiableOn_tsum_of_summable_norm
      (u := fun k => Real.sqrt Real.pi / 2 * Real.exp ((r ^ 2 + (1 / 2 + r) ^ 2) / 4) *
        (8 / (1 + (u k).re ^ 2)))
      (summable_inv_u.mul_left _) (fun k => ?_) Metric.isOpen_ball (fun k w hw => ?_)
    · unfold gk; fun_prop
    · apply norm_term_le
      rw [Metric.mem_ball, dist_eq_norm] at hw
      calc ‖w‖ = ‖(w - z₀) + z₀‖ := by ring_nf
        _ ≤ ‖w - z₀‖ + ‖z₀‖ := norm_add_le _ _
        _ ≤ r := by simp only [r]; linarith
  exact hd.differentiableAt (Metric.ball_mem_nhds z₀ one_pos)

lemma summable_term (z : ℂ) : Summable (fun k : Index ⊕ Index => gk (u k - z) / 2) :=
  Summable.of_norm_bounded (summable_inv_u.mul_left _) (norm_term_le (r := ‖z‖) le_rfl)

lemma gk_conj (v : ℂ) (q : ℝ) : gk (conj v - q) = conj (gk (v - q)) := by
  rw [gk, gk, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp [map_div₀, map_neg, map_pow, map_sub, map_ofNat]

lemma gaussHat_one (q : ℝ) (v : ℂ) : gaussHat 1 q v = gk (v - q) := by
  rw [gaussHat_eq one_pos, gk]
  norm_num

/-- On real centres the symmetrized zero side is the real arithmetic target. -/
theorem Ztil_real (q : ℚ) : Ztil (q : ℂ) = (FleetDualInequality.R q : ℂ) := by
  have hs := summable_term (q : ℂ)
  have hq : ((q : ℝ) : ℂ) = (q : ℂ) := Complex.ofReal_ratCast q
  set Z : ℂ := FleetFullLineArithmetic.rhs (gauss 1 (q : ℝ)) with hZdef
  have hZ : HasSum (fun x : Index => gk (t x - (q : ℂ))) Z := by
    have h := GaussianTraceFormula.gaussian_formula_zeros one_pos (q : ℝ)
    rw [← FleetPrimePoleBoundRH.rhs_gauss_eq one_pos] at h
    refine h.congr_fun (fun x => ?_)
    rw [gaussHat_one, hq]; rfl
  have hA : HasSum (fun x : Index => gk (u (Sum.inl x) - (q : ℂ)) / 2) (Z / 2) :=
    hZ.div_const 2
  have hB : HasSum (fun x : Index => gk (u (Sum.inr x) - (q : ℂ)) / 2) (conj Z / 2) := by
    have h := (hZ.mapL (Complex.conjCLE.toContinuousLinearMap)).div_const 2
    refine h.congr_fun (fun x => ?_)
    have := gk_conj (t x) (q : ℝ)
    rw [hq] at this
    simp only [u, Sum.elim_inr, Function.comp_apply]
    rw [this]; rfl
  have hsum : HasSum (fun k : Index ⊕ Index => gk (u k - (q : ℂ)) / 2) (Z / 2 + conj Z / 2) :=
    HasSum.sum (f := fun k : Index ⊕ Index => gk (u k - (q : ℂ)) / 2) hA hB
  unfold Ztil
  rw [hsum.tsum_eq, ← add_div, Complex.add_conj]
  simp [FleetDualInequality.R, hZdef]

/-- Exponents and coefficients of the exponential series. -/
def lam (k : Index ⊕ Index) : ℂ := I * u k / 2
def cf (k : Index ⊕ Index) : ℂ := cexp (lam k ^ 2) / 2

lemma Ztil_imag (y : ℝ) :
    Ztil ((y : ℂ) * I) = (Real.sqrt Real.pi : ℂ) * cexp ((y : ℂ) ^ 2 / 4) *
      ∑' k, cf k * cexp (lam k * y) := by
  unfold Ztil
  rw [← tsum_mul_left]
  refine tsum_congr (fun k => ?_)
  simp only [gk, cf, lam]
  have : cexp (-(u k - (y : ℂ) * I) ^ 2 / 4) =
      cexp ((y : ℂ) ^ 2 / 4) * cexp ((I * u k / 2) ^ 2) * cexp (I * u k / 2 * y) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    linear_combination (-((u k) ^ 2 + (y : ℂ) ^ 2) / 4) * Complex.I_sq
  rw [this]; ring

lemma finite_window (α ρ : ℝ) : {x : Index | |(t x).re - α| < ρ}.Finite := by
  have hs := (summable_w α).tendsto_cofinite_zero
  have hev := (tendsto_order.1 hs).2 (Real.exp (-ρ ^ 2 / 4)) (Real.exp_pos _)
  refine (Filter.eventually_cofinite.1 hev).subset (fun x hx => ?_)
  simp only [mem_setOf_eq, not_lt] at hx ⊢
  unfold w
  apply Real.exp_le_exp.2
  have h0 := abs_nonneg ((t x).re - α)
  have : ((t x).re - α) ^ 2 ≤ ρ ^ 2 := by nlinarith [sq_abs ((t x).re - α)]
  linarith

/-- **Every ordinate is real**, given an entire realization of the arithmetic target with the
`e^{y²/4}` growth bound on the imaginary axis. -/
theorem ordinates_real_of_entire_realization {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hFq : ∀ q : ℚ, F (q : ℂ) = (FleetDualInequality.R q : ℂ)) {C : ℝ}
    (hFb : ∀ y : ℝ, ‖F ((y : ℂ) * I)‖ ≤ C * Real.exp (y ^ 2 / 4)) :
    ∀ x : Index, (t x).im = 0 := by
  -- step 2: `F = Z̃`
  have heq : EqOn F Ztil univ := by
    refine (analyticOnNhd_univ_iff_differentiable.2 hF).eqOn_of_preconnected_of_frequently_eq
      (analyticOnNhd_univ_iff_differentiable.2 differentiable_Ztil) isPreconnected_univ (mem_univ (0 : ℂ)) ?_
    have hseq : Tendsto (fun n : ℕ => (((1 / ((n : ℚ) + 1) : ℚ) : ℂ))) atTop (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      constructor
      · have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
        refine this.congr (fun n => ?_)
        push_cast; rfl
      · refine Eventually.of_forall (fun n => ?_)
        simp only [mem_compl_iff, mem_singleton_iff]
        push_cast
        exact one_div_ne_zero (by exact_mod_cast Nat.succ_ne_zero n)
    refine hseq.frequently (Frequently.of_forall (fun n => ?_))
    rw [hFq, Ztil_real]
  -- step 3: the bounded exponential series
  set h : ℝ → ℂ := fun y => ∑' k, cf k * cexp (lam k * y) with h_def
  have hden : ∀ y : ℝ, (Real.sqrt Real.pi : ℂ) * cexp ((y : ℂ) ^ 2 / 4) ≠ 0 := by
    intro y
    refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
    exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hh : ∀ y : ℝ, h y = F ((y : ℂ) * I) / ((Real.sqrt Real.pi : ℂ) * cexp ((y : ℂ) ^ 2 / 4)) := by
    intro y
    rw [heq (mem_univ _), Ztil_imag, mul_div_cancel_left₀ _ (hden y)]
  have hnormden : ∀ y : ℝ, ‖(Real.sqrt Real.pi : ℂ) * cexp ((y : ℂ) ^ 2 / 4)‖ =
      Real.sqrt Real.pi * Real.exp (y ^ 2 / 4) := by
    intro y
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Complex.norm_exp]
    congr 2
    simp [sq]
  have hbd : ∀ y : ℝ, 0 ≤ y → ‖h y‖ ≤ C / Real.sqrt Real.pi := by
    intro y _
    rw [hh, norm_div, hnormden, div_le_div_iff₀ (by positivity) (Real.sqrt_pos.2 Real.pi_pos)]
    have := hFb y
    have hs := Real.sqrt_nonneg Real.pi
    nlinarith
  have hcont : Continuous h := by
    have : h = fun y : ℝ => F ((y : ℂ) * I) / ((Real.sqrt Real.pi : ℂ) * cexp ((y : ℂ) ^ 2 / 4)) :=
      funext hh
    rw [this]
    exact Continuous.div (hF.continuous.comp (by fun_prop)) (by fun_prop) hden
  -- step 4: the Laplace-pole lemma
  have hsum : Summable (fun k => ‖cf k‖) := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      ((summable_inv_u).mul_left (Real.exp ((0 ^ 2 + (1 / 2 + 0) ^ 2) / 4) / 2))
    have h1 := norm_cexp_le (r := 0) (z := 0) (by simp) (abs_u_im k)
    have e : lam k ^ 2 = -(u k - 0) ^ 2 / 4 := by
      simp only [lam, sub_zero]
      linear_combination ((u k) ^ 2 / 4) * Complex.I_sq
    simp only [cf, norm_div, Complex.norm_two, e]
    linarith
  have hσ : ∀ k, (lam k).re ≤ 1 / 4 := by
    intro k
    have : (lam k).re = -(u k).im / 2 := by simp [lam, Complex.mul_re, Complex.div_re]
    rw [this]
    have := abs_u_im k
    linarith [neg_abs_le (u k).im]
  have hfin : ∀ (z : ℂ) (r : ℝ), {k | ‖lam k - z‖ < r}.Finite := by
    intro z r
    have hS := finite_window (2 * z.im) (2 * r)
    refine ((hS.image Sum.inl).union (hS.image Sum.inr)).subset (fun k hk => ?_)
    simp only [mem_setOf_eq] at hk
    have h1 := Complex.abs_im_le_norm (lam k - z)
    have h2 : (lam k - z).im = (t (base k)).re / 2 - z.im := by
      rw [Complex.sub_im, ← u_re]
      simp [lam, Complex.mul_im, Complex.div_im]
    rw [h2] at h1
    have h3 : |(t (base k)).re - 2 * z.im| < 2 * r := by
      have : |(t (base k)).re - 2 * z.im| = 2 * |(t (base k)).re / 2 - z.im| := by
        rw [← abs_two, ← abs_mul, abs_two]; congr 1; ring
      rw [this]; linarith
    cases k with
    | inl x => exact Or.inl ⟨x, h3, rfl⟩
    | inr x => exact Or.inr ⟨x, h3, rfl⟩
  have hc : ∀ k, cf k = (fun z => cexp (z ^ 2) / 2) (lam k) := fun k => rfl
  have hre := FleetLaplacePole.re_nonpos_of_bounded cf lam (fun z => cexp (z ^ 2) / 2)
    (fun z => div_ne_zero (Complex.exp_ne_zero _) two_ne_zero) hc hsum hσ hfin hcont hbd
  intro x
  have h1 := hre (Sum.inl x)
  have h2 := hre (Sum.inr x)
  simp [lam, u, Complex.mul_re, Complex.div_re] at h1 h2
  linarith

/-- **Weighted feasibility ⇒ RH.** One budget `M`, weighted (not unit) atoms, tolerance `ε n → 0`. -/
theorem RH_of_weightedFeasible {M : ℝ} {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hf : ∀ n, FleetDualConverse.WeightedFeasible FleetDualInequality.R M (ε n) n) :
    RiemannHypothesis := by
  obtain ⟨F, hF, hFq, C, hFb⟩ :=
    FleetWeightedLimit.exists_entire_realization FleetDualInequality.R hε hf
  have hreal := ordinates_real_of_entire_realization hF hFq hFb
  apply RH_of_nontrivial_zeros_on_critical_line
  intro ρ hρ
  obtain ⟨x, hx⟩ := multEnum_canonical.exists_index hρ
  have h := hreal x
  rw [t_im, hx] at h
  linarith

/-- Unit atoms are weighted atoms. -/
theorem weightedFeasible_of_feasible {M : ℝ} {n : ℕ}
    (hf : FleetRationalBankCriterion.Feasible 1 M n) :
    FleetDualConverse.WeightedFeasible FleetDualInequality.R M (1 / ((n : ℝ) + 1)) n := by
  classical
  obtain ⟨N, x, hmass, hres⟩ := hf
  refine ⟨∑ i : Fin N, Finsupp.single (x i) 1, fun y => ?_, ?_, fun q => ?_⟩
  · rw [Finsupp.finset_sum_apply]
    exact Finset.sum_nonneg (fun i _ => by
      rw [Finsupp.single_apply]; split_ifs <;> norm_num)
  · rw [map_sum]
    simp only [FleetDualConverse.massMap, Finsupp.linearCombination_single, one_smul]
    simpa [FleetDualConverse.w] using hmass
  · rw [map_sum]
    simp only [FleetDualConverse.traceMap, Finsupp.linearCombination_single, one_smul,
      Finset.sum_apply]
    have h := hres q.1 q.2
    have htr : (∑ i : Fin N, FleetFullLineFourier.h (gauss 1 (q.1 : ℝ)) (x i)) =
        ((∑ i : Fin N, FleetDualConverse.G (x i) q.1 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl (fun i _ => FleetThreeCentreInequality.probe_real _ _)
    rw [htr] at h
    have h2 := Complex.abs_re_le_norm
      (((∑ i : Fin N, FleetDualConverse.G (x i) q.1 : ℝ) : ℂ) -
        FleetFullLineArithmetic.rhs (gauss 1 (q.1 : ℝ)))
    rw [Complex.sub_re, Complex.ofReal_re] at h2
    exact h2.trans h

/-- **RH ⇔ weighted feasibility** at every stage with one budget, tolerance `1/(n+1)`. -/
theorem RH_iff_weightedFeasible :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ n : ℕ,
      FleetDualConverse.WeightedFeasible FleetDualInequality.R M (1 / ((n : ℝ) + 1)) n := by
  constructor
  · intro hRH
    obtain ⟨M, hM⟩ := FleetPrimeSideConsequences.uniformFeasibility_of_RH hRH one_pos
    exact ⟨M, fun n => weightedFeasible_of_feasible (hM n)⟩
  · rintro ⟨M, hM⟩
    exact RH_of_weightedFeasible (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) hM

/-- **RH ⇔ the prime-side inequality at every stage** (`FleetDualConverse.DualIneq`) with one positive
budget and tolerance `1/(n+1)`: a statement about the arithmetic target alone, no integer constraint. -/
theorem RH_iff_dualIneq :
    RiemannHypothesis ↔ ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ,
      FleetDualConverse.DualIneq FleetDualInequality.R M (1 / ((n : ℝ) + 1)) n := by
  constructor
  · intro hRH
    obtain ⟨M, hM⟩ := RH_iff_weightedFeasible.1 hRH
    refine ⟨max M 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun n => ?_⟩
    obtain ⟨a, ha0, hm, hr⟩ := hM n
    exact FleetDualConverse.dualIneq_of_weightedFeasible ⟨a, ha0, hm.trans (le_max_left _ _), hr⟩
  · rintro ⟨M, hM, hd⟩
    have hf : ∀ n : ℕ, FleetDualConverse.WeightedFeasible FleetDualInequality.R M
        (1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1)) n := fun n =>
      FleetDualConverse.weightedFeasible_of_dualIneq hM (by positivity) (hd n) (by positivity)
    have hε : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      rw [add_zero] at this
      exact this
    exact RH_of_weightedFeasible hε hf

end FleetWeightedFeasibilityRH
