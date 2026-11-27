import FleetThreeCentreInequality

/-!
# The prime-side inequality forced by a feasible stage, for every finite weighting

Let `φ_c t = Σ_{q ∈ s} c q · √π · exp (-(t-q)²/4)` be any finite real combination of
width-one Gaussians centred at bank points. Suppose its negative part is controlled by the
mass weight: `-φ_c t ≤ K · (1+t²)⁻¹` for every real `t`, with `K ≥ 0`.

If stage `n` is feasible with mass budget `M`, then the arithmetic target alone satisfies

  `-(K·M) - (Σ |c q|)/(n+1) ≤ Σ_{q ∈ s} c q · Re rhs(q)`.

`FleetThreeCentreInequality.three_centre_of_feasible` is the case `s = {c-r, c, c+r}`,
weights `(-1, 2e^{-r²/4}, -1)` with sign reversed, where `K = 0`.

Under uniform feasibility (one `M` for all stages) the tolerance term disappears in the limit:
`uniform_dual_inequality` gives `-(K·M) ≤ Σ c q · Re rhs(q)` for every finite rational
weighting. This file proves these implications (feasible ⇒ inequality). It does not prove
the converse, and it does not assert the inequality for the actual arithmetic target.
-/

noncomputable section
open GaussianTest Complex Filter

namespace FleetDualInequality

/-- The width-one Gaussian combination with weights `c` on the finite set `s`. -/
def phi (s : Finset ℚ) (c : ℚ → ℝ) (t : ℝ) : ℝ :=
  ∑ q ∈ s, c q * (Real.sqrt Real.pi * Real.exp (-(t - (q : ℝ))^2/4))

/-- Real part of the arithmetic target at a centre. -/
def R (q : ℚ) : ℝ := (FleetFullLineArithmetic.rhs (gauss 1 (q : ℝ))).re

/-- Feasibility at stage `n` with budget `M` forces the weighted prime-side inequality. -/
theorem dual_of_feasible {M : ℝ} {n : ℕ}
    (hf : FleetRationalBankCriterion.Feasible 1 M n)
    (s : Finset ℚ) (hs : s ⊆ FleetRationalBanks.bank n) (c : ℚ → ℝ)
    {K : ℝ} (hK : 0 ≤ K) (hneg : ∀ t : ℝ, -phi s c t ≤ K * (1 + t^2)⁻¹) :
    -(K * M) - (∑ q ∈ s, |c q|) / ((n : ℝ) + 1) ≤ ∑ q ∈ s, c q * R q := by
  obtain ⟨N, x, hmass, hres⟩ := hf
  let S : ℝ → ℝ := fun q => ∑ i : Fin N, Real.sqrt Real.pi * Real.exp (-(x i - q)^2/4)
  have htrace : ∀ q : ℝ,
      (∑ i : Fin N, FleetFullLineFourier.h (gauss 1 q) (x i)) = ((S q : ℝ) : ℂ) := by
    intro q
    simp only [S]
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun i _ => FleetThreeCentreInequality.probe_real q (x i))
  have hclose : ∀ q ∈ s, |S (q : ℝ) - R q| ≤ 1/((n : ℝ)+1) := by
    intro q hq
    have h := hres q (hs hq)
    rw [htrace] at h
    have h2 := Complex.abs_re_le_norm
      (((S (q : ℝ) : ℝ) : ℂ) - FleetFullLineArithmetic.rhs (gauss 1 (q : ℝ)))
    rw [Complex.sub_re, Complex.ofReal_re] at h2
    exact h2.trans h
  -- Σ_q c_q S(q) = Σ_i φ(x_i)
  have hswap : ∑ q ∈ s, c q * S (q : ℝ) = ∑ i : Fin N, phi s c (x i) := by
    simp only [S, phi, Finset.mul_sum]
    rw [Finset.sum_comm]
  -- each atom pays at most K times its mass weight
  have hatoms : -(K * M) ≤ ∑ i : Fin N, phi s c (x i) := by
    have h1 : ∑ i : Fin N, -phi s c (x i) ≤ ∑ i : Fin N, K * (1 + (x i)^2)⁻¹ :=
      Finset.sum_le_sum (fun i _ => hneg (x i))
    rw [← Finset.mul_sum, Finset.sum_neg_distrib] at h1
    have h2 : K * (∑ i : Fin N, (1 + (x i)^2)⁻¹) ≤ K * M := mul_le_mul_of_nonneg_left hmass hK
    linarith
  -- replacing S by R costs at most |c q|/(n+1) per centre
  have hrep : ∑ q ∈ s, c q * S (q : ℝ) - (∑ q ∈ s, |c q|) / ((n : ℝ) + 1)
      ≤ ∑ q ∈ s, c q * R q := by
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro q hq
    have hb := hclose q hq
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have e : |c q| / ((n : ℝ) + 1) = |c q| * (1 / ((n : ℝ) + 1)) := by ring
    rw [e]
    have key : |c q * (S (q : ℝ) - R q)| ≤ |c q| * (1 / ((n : ℝ) + 1)) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    have := (abs_le.mp key).2
    nlinarith [this]
  linarith [hswap, hatoms, hrep]

/-- Contrapositive: a violation by the arithmetic target certifies that stage `n` is
infeasible with budget `M`. -/
theorem infeasible_of_dual_violation {M K : ℝ} {n : ℕ}
    (s : Finset ℚ) (hs : s ⊆ FleetRationalBanks.bank n) (c : ℚ → ℝ)
    (hK : 0 ≤ K) (hneg : ∀ t : ℝ, -phi s c t ≤ K * (1 + t^2)⁻¹)
    (hv : ∑ q ∈ s, c q * R q < -(K * M) - (∑ q ∈ s, |c q|) / ((n : ℝ) + 1)) :
    ¬ FleetRationalBankCriterion.Feasible 1 M n :=
  fun hf => (not_lt_of_ge (dual_of_feasible hf s hs c hK hneg)) hv

/-- Every finite set of rationals lies in all sufficiently late banks. -/
lemma eventually_subset_bank (s : Finset ℚ) :
    ∀ᶠ n in atTop, s ⊆ FleetRationalBanks.bank n := by
  induction s using Finset.induction_on with
  | empty => exact Eventually.of_forall (fun n => Finset.empty_subset _)
  | insert a s' _ ih =>
    filter_upwards [ih, FleetRationalBanks.eventually_mem_bank a] with n h1 h2
    exact Finset.insert_subset h2 h1

/-- Under uniform feasibility the tolerance term vanishes: the limiting prime-side inequality
`-(K·M) ≤ Σ c q · Re rhs(q)` holds for every finite rational weighting whose Gaussian
combination has negative part at most `K` times the mass weight. -/
theorem uniform_dual_inequality {M : ℝ}
    (hf : ∀ n : ℕ, FleetRationalBankCriterion.Feasible 1 M n)
    (s : Finset ℚ) (c : ℚ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hneg : ∀ t : ℝ, -phi s c t ≤ K * (1 + t^2)⁻¹) :
    -(K * M) ≤ ∑ q ∈ s, c q * R q := by
  have hev : ∀ᶠ n : ℕ in atTop,
      -(K * M) - (∑ q ∈ s, |c q|) * (1 / ((n : ℝ) + 1)) ≤ ∑ q ∈ s, c q * R q := by
    filter_upwards [eventually_subset_bank s] with n hn
    have h := dual_of_feasible (hf n) s hn c hK hneg
    have e : (∑ q ∈ s, |c q|) * (1 / ((n : ℝ) + 1)) = (∑ q ∈ s, |c q|) / ((n : ℝ) + 1) := by ring
    rw [e]; exact h
  have hlim : Tendsto (fun n : ℕ => -(K * M) - (∑ q ∈ s, |c q|) * (1 / ((n : ℝ) + 1)))
      atTop (nhds (-(K * M) - (∑ q ∈ s, |c q|) * 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat)
  rw [mul_zero, sub_zero] at hlim
  exact le_of_tendsto hlim hev

/-- Positivity form: if the Gaussian combination is nonnegative on the real line, uniform
feasibility forces the prime-side functional to be nonnegative. No mass term enters. -/
theorem uniform_positivity {M : ℝ}
    (hf : ∀ n : ℕ, FleetRationalBankCriterion.Feasible 1 M n)
    (s : Finset ℚ) (c : ℚ → ℝ) (hpos : ∀ t : ℝ, 0 ≤ phi s c t) :
    0 ≤ ∑ q ∈ s, c q * R q := by
  have h := uniform_dual_inequality hf s c (le_refl 0) (fun t => by
    have := hpos t; simp only [zero_mul]; linarith)
  simpa using h

end FleetDualInequality
