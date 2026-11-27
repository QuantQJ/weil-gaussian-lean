import FleetPrimeTarget
import FleetMoebiusSmoothDecomposition
import FleetMollifierTail

/-!
# `Ismooth` = the window-tail inner sum, and RH ⇔ a bound on a finite Möbius head

`FleetMoebiusSmoothDecomposition` writes `S_b(α) = Σ_m μ(m) m^{-1/2} Ismooth b α (log m)` (complex);
`FleetMollifierTail` bounds the real sums `inner b α m = Σ_{n ≥ 2} log n · kernel b α (m n)`.

* `ismooth_eq_inner`: `m^{-1/2} · Ismooth b α (log m) = inner b α m` for `m ≥ 1`.
* `primeSumSym_eq_inner`: `S_b(α) = Σ'_m μ(m) · inner b α m` (a real number).
* `primeSumSym_sub_head`: with `M = ⌊e^{1.1/b}⌋`, `0 < b ≤ 1`, every real `α`,
  `‖S_b(α) − Σ_{m ≤ M} μ(m) inner b α m‖ ≤ 8 e^{−0.6375/b}`  (unconditional).
* `RH_iff_head_bound`: **RH ⇔ for every `|α| ≥ 1/2` there is `C` with
  `|Σ_{m ≤ ⌊e^{1.1/b}⌋} μ(m) inner b α m| ≤ C √(π/b)` for all `0 < b ≤ 1`.**
  The target is now a finite Möbius sum; the discarded tail is unconditionally negligible.
-/

set_option autoImplicit false
noncomputable section
open Complex Filter Topology Finset
open scoped Real
open GaussianTest FleetMollifierTail

namespace FleetFiniteHeadRH

lemma natCast_cpow_neg_half {n : ℕ} (hn : 0 < n) :
    (n : ℂ) ^ (-(1 / 2) : ℂ) = ((Real.exp (-Real.log n / 2) : ℝ) : ℂ) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Complex.cpow_def_of_ne_zero hn', Complex.ofReal_exp]
  congr 1
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_log (by positivity : (0 : ℝ) ≤ n)]
  push_cast; ring

lemma term_eq (b α : ℝ) {m k : ℕ} (hm : 0 < m) (hk : 0 < k) :
    (m : ℂ) ^ (-(1 / 2) : ℂ) * ((Real.log k : ℂ) * (k : ℂ) ^ (-(1 / 2) : ℂ)
      * (gauss b α (Real.log k + Real.log m) + gauss b α (-(Real.log k + Real.log m))))
    = ((Real.log k * kernel b α ((m : ℝ) * k) : ℝ) : ℂ) := by
  rw [FleetPrimeTarget.gauss_add_neg, natCast_cpow_neg_half hm, natCast_cpow_neg_half hk]
  simp only [← Complex.ofReal_mul]
  congr 1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  unfold kernel
  rw [Real.log_mul hmR.ne' hkR.ne']
  rw [show -(Real.log m + Real.log k) / 2 - b * (Real.log m + Real.log k) ^ 2
      = -Real.log m / 2 + (-Real.log k / 2 + -b * (Real.log k + Real.log m) ^ 2) by ring,
    Real.exp_add, Real.exp_add, show Real.log m + Real.log k = Real.log k + Real.log m by ring]
  ring

/-- **`m^{-1/2} · Ismooth b α (log m) = FleetMollifierTail.inner b α m`.** -/
theorem ismooth_eq_inner {b : ℝ} (hb : 0 < b) (α : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    (m : ℂ) ^ (-(1 / 2) : ℂ) * FleetMoebiusSmoothDecomposition.Ismooth b α (Real.log m)
      = (FleetMollifierTail.inner b α m : ℂ) := by
  have hm0 : 0 < m := by omega
  set f : ℕ → ℝ := fun k => Real.log k * kernel b α ((m : ℝ) * k) with hf
  unfold FleetMoebiusSmoothDecomposition.Ismooth
  rw [← tsum_mul_left]
  have hterm : ∀ k : ℕ, (m : ℂ) ^ (-(1 / 2) : ℂ) * ((Real.log k : ℂ) * (k : ℂ) ^ (-(1 / 2) : ℂ)
      * (gauss b α (Real.log k + Real.log m) + gauss b α (-(Real.log k + Real.log m))))
      = ((f k : ℝ) : ℂ) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hf]
    · exact term_eq b α hm0 hk
  rw [tsum_congr hterm, ← Complex.ofReal_tsum]
  congr 1
  have hs := (inner_summable_and_bound b α m hb hm).1
  have h2 : (fun n : ℕ => f (n + 2))
      = (fun n : ℕ => Real.log (n + 2) * kernel b α ((m : ℝ) * (n + 2))) := by
    funext n; simp only [hf]; push_cast; ring_nf
  have hsf : Summable f := (summable_nat_add_iff 2).mp (h2 ▸ hs)
  rw [hsf.tsum_eq_zero_add, ((summable_nat_add_iff 1).mpr hsf).tsum_eq_zero_add]
  have e0 : f 0 = 0 := by simp [hf]
  have e1 : f (0 + 1) = 0 := by simp [hf]
  rw [e0, e1, zero_add, zero_add]
  unfold FleetMollifierTail.inner
  congr 1

/-- **`S_b(α) = Σ'_m μ(m) · FleetMollifierTail.inner b α m`.** -/
theorem primeSumSym_eq_inner {b : ℝ} (hb : 0 < b) (α : ℝ) :
    FleetPrimeSideConsequences.primeSumSym b α
      = ((∑' m : ℕ, (ArithmeticFunction.moebius m : ℝ) * FleetMollifierTail.inner b α m : ℝ) : ℂ) := by
  rw [FleetMoebiusSmoothDecomposition.primeSumSym_eq_moebius_smooth hb, Complex.ofReal_tsum]
  congr 1; funext m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  rw [mul_assoc, ismooth_eq_inner hb α hm]
  push_cast; ring

lemma summable_moebius_inner {b : ℝ} (hb : 0 < b) (α : ℝ) :
    Summable (fun m : ℕ => (ArithmeticFunction.moebius m : ℝ) * FleetMollifierTail.inner b α m) := by
  refine Summable.of_norm_bounded (g := fun m : ℕ => envelope b * (1 / (m : ℝ) ^ 3))
    ((Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)).mul_left _) ?_
  intro m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  rw [Real.norm_eq_abs, abs_mul]
  have h1 := moebius_abs_le m
  have h2 := (inner_summable_and_bound b α m hb hm).2
  calc |(ArithmeticFunction.moebius m : ℝ)| * |FleetMollifierTail.inner b α m| ≤ 1 * (envelope b / (m : ℝ) ^ 3) :=
        mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    _ = envelope b * (1 / (m : ℝ) ^ 3) := by ring

/-- The cutoff `M = ⌊e^{1.1/b}⌋`. -/
def cut (b : ℝ) : ℕ := ⌊Real.exp (11 / (10 * b))⌋₊

/-- The finite Möbius head `Σ_{m ≤ M} μ(m) FleetMollifierTail.inner b α m` (the `m = 0` term is `0`). -/
def head (b α : ℝ) (M : ℕ) : ℝ :=
  ∑ m ∈ range (M + 1), (ArithmeticFunction.moebius m : ℝ) * FleetMollifierTail.inner b α m

/-- **The prime sum is the finite head up to `8 e^{−0.6375/b}`**, unconditionally, every real `α`. -/
theorem primeSumSym_sub_head {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (α : ℝ) :
    ‖FleetPrimeSideConsequences.primeSumSym b α - (head b α (cut b) : ℂ)‖
      ≤ 8 * Real.exp (-51 / (80 * b)) := by
  set M := cut b with hMdef
  have hc := cutoff_floor_bounds b hb hb1
  have hs := summable_moebius_inner hb α
  rw [primeSumSym_eq_inner hb, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    ← hs.sum_add_tsum_nat_add (M + 1)]
  simp only [head, add_sub_cancel_left]
  have hsT := (summable_nat_add_iff (M + 1)).mpr hs
  have hbound : ∀ L : ℕ, |∑ i ∈ range L, (ArithmeticFunction.moebius (i + (M + 1)) : ℝ)
      * FleetMollifierTail.inner b α (i + (M + 1))| ≤ 8 * Real.exp (-51 / (80 * b)) := by
    intro L
    have h := moebius_finite_tail_bound b α M L hb hc.1
    have e : ∑ i ∈ range L, (ArithmeticFunction.moebius (i + (M + 1)) : ℝ) * FleetMollifierTail.inner b α (i + (M + 1))
        = ∑ k ∈ range L, (ArithmeticFunction.moebius (M + k + 1) : ℝ) * FleetMollifierTail.inner b α (M + k + 1) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [show i + (M + 1) = M + i + 1 by omega]
    rw [e]
    exact h.trans (envelope_at_half_cutoff b _ hb hc.2)
  have ht := hsT.hasSum.tendsto_sum_nat
  have ht' := (_root_.continuous_abs.tendsto _).comp ht
  exact le_of_tendsto' ht' hbound

lemma one_le_sqrt_pi_div {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) : 1 ≤ Real.sqrt (π / b) := by
  apply Real.one_le_sqrt.mpr
  apply (le_div_iff₀ hb).2
  linarith [Real.two_le_pi]

lemma exp_tail_le {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    8 * Real.exp (-51 / (80 * b)) ≤ Real.sqrt (π / b) * 8 := by
  have he : Real.exp (-51 / (80 * b)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity))
  nlinarith [one_le_sqrt_pi_div hb hb1]

/-- **RH ⇔ the finite Möbius head is `O(√(π/b))`** at every height `|α| ≥ 1/2`. -/
theorem RH_iff_head_bound :
    RiemannHypothesis ↔ ∀ α : ℝ, 1 / 2 ≤ |α| → ∃ C : ℝ, ∀ b : ℝ, 0 < b → b ≤ 1 →
      |head b α (cut b)| ≤ Real.sqrt (π / b) * C := by
  rw [FleetLowZeroFree.RH_iff_primeSumSym_bound]
  constructor
  · intro h α hα
    obtain ⟨C, hC⟩ := h α hα
    refine ⟨C + 8, fun b hb hb1 => ?_⟩
    have h1 := hC b hb hb1
    have h2 := primeSumSym_sub_head hb hb1 α
    have hh : ‖(head b α (cut b) : ℂ)‖ = |head b α (cut b)| := by rw [Complex.norm_real, Real.norm_eq_abs]
    have h3 := norm_sub_norm_le (head b α (cut b) : ℂ) (FleetPrimeSideConsequences.primeSumSym b α)
    rw [norm_sub_rev, hh] at h3
    nlinarith [exp_tail_le hb hb1]
  · intro h α hα
    obtain ⟨C, hC⟩ := h α hα
    refine ⟨C + 8, fun b hb hb1 => ?_⟩
    have h1 := hC b hb hb1
    have h2 := primeSumSym_sub_head hb hb1 α
    have hh : ‖(head b α (cut b) : ℂ)‖ = |head b α (cut b)| := by rw [Complex.norm_real, Real.norm_eq_abs]
    have h3 := norm_sub_norm_le (FleetPrimeSideConsequences.primeSumSym b α) (head b α (cut b) : ℂ)
    rw [hh] at h3
    nlinarith [exp_tail_le hb hb1]

end FleetFiniteHeadRH
