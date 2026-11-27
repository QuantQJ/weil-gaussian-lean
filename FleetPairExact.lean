/-
Copyright 2026 James C. Kerr (QuantQJ). Apache-2.0.
-/
import Mathlib

/-!
# The off-line pair identity, exactly

`research_notes/DUAL-INEQUALITY/ATTEMPT.md` lists as sub-target 2 of "What would finish it":
"Formalize the off-line pair identity for the Gaussian dictionary (exact, not O(e^4))."
This file does that for the width-one probe `g w = sqrt(pi) exp(-w^2/4)`.

* `gp_pair`: `g(u+ie) + g(u-ie) = 2 sqrt(pi) e^{e^2/4} e^{-u^2/4} cos(e u / 2)`, exact.
* `pairR_sum`: summed over a bank with weights `c`, the entire `e`-dependence outside the
  cosine is the single scalar `e^{e^2/4}`.
* `pairR_sum_of_vanishing`: if the weighting vanishes at the height
  (`sum c_i Gp (gamma - q_i) = 0`, the condition the note attributes to the extremal `phi_c`
  of the dual LP), the pair contribution is *exactly* the cosine defect `cos(.) - 1`: no
  first-order term, no remainder.
* `defect_nonpos`: for nonnegative weights that defect is `<= 0` termwise.

**What this does not do.** It does not prove that the extremal `phi_c` of the dual LP vanish
on the zeros. That claim rests on `tools/dual_lp.py` and stays numerical (Tier F): it is a
statement about where a finite linear program attains its optimum, not about this identity.
What is formalized here is the mechanism the note invokes once such a `phi_c` is given.
-/

noncomputable section
open Complex

/-- Width-one Gaussian probe, complex argument: `g w = √π exp(-w²/4)`. -/
def gp (w : ℂ) : ℂ := (Real.sqrt Real.pi : ℂ) * Complex.exp (-w ^ 2 / 4)

/-- **Exact pair identity.**  An off-line pair at height `u` with offset `e` contributes
`2 √π e^{e²/4} e^{-u²/4} cos(e u / 2)` — no `O(e⁴)`. -/
theorem gp_pair (u e : ℝ) :
    gp ((u : ℂ) + (e : ℂ) * I) + gp ((u : ℂ) - (e : ℂ) * I)
      = 2 * (Real.sqrt Real.pi : ℂ) * Complex.exp ((e ^ 2 - u ^ 2) / 4)
          * Complex.cos ((u : ℂ) * (e : ℂ) / 2) := by
  have hI : (I : ℂ) ^ 2 = -1 := Complex.I_sq
  have e1 : -((u : ℂ) + (e : ℂ) * I) ^ 2 / 4
      = ((e : ℂ) ^ 2 - (u : ℂ) ^ 2) / 4 + (-((u : ℂ) * (e : ℂ) / 2)) * I := by
    ring_nf
    rw [hI]
    ring
  have e2 : -((u : ℂ) - (e : ℂ) * I) ^ 2 / 4
      = ((e : ℂ) ^ 2 - (u : ℂ) ^ 2) / 4 + ((u : ℂ) * (e : ℂ) / 2) * I := by
    ring_nf
    rw [hI]
    ring
  rw [gp, gp, e1, e2, Complex.exp_add, Complex.exp_add, Complex.cos]
  ring

/-- The real form: the pair contribution is a real multiple of `cos (e u / 2)`. -/
theorem gp_pair_real (u e : ℝ) :
    gp ((u : ℂ) + (e : ℂ) * I) + gp ((u : ℂ) - (e : ℂ) * I)
      = ((2 * Real.sqrt Real.pi * Real.exp ((e ^ 2 - u ^ 2) / 4) * Real.cos (u * e / 2) : ℝ) : ℂ) := by
  rw [gp_pair]
  push_cast [Complex.ofReal_cos, Complex.ofReal_exp]
  ring

/-- At `e = 0` the pair identity degenerates to twice the on-line probe. -/
theorem gp_pair_zero (u : ℝ) :
    gp ((u : ℂ) + (0 : ℝ) * I) + gp ((u : ℂ) - (0 : ℝ) * I)
      = 2 * (Real.sqrt Real.pi : ℂ) * Complex.exp (-(u : ℂ) ^ 2 / 4) := by
  rw [gp_pair]
  norm_num

/-! ## Summed over a bank, and the excess at a vanishing point -/

/-- Real width-one probe. -/
def Gp (u : ℝ) : ℝ := Real.sqrt Real.pi * Real.exp (-u ^ 2 / 4)

/-- The real pair contribution at offset `e`, height `γ`, centre `q`. -/
def pairR (γ q e : ℝ) : ℝ :=
  2 * Real.sqrt Real.pi * Real.exp ((e ^ 2 - (γ - q) ^ 2) / 4) * Real.cos ((γ - q) * e / 2)

theorem pairR_eq (γ q e : ℝ) :
    pairR γ q e = 2 * Real.exp (e ^ 2 / 4) * (Gp (γ - q) * Real.cos ((γ - q) * e / 2)) := by
  unfold pairR Gp
  rw [show (e ^ 2 - (γ - q) ^ 2) / 4 = e ^ 2 / 4 + -(γ - q) ^ 2 / 4 by ring, Real.exp_add]
  ring

/-- **The pair sum over a bank.**  The whole `e`-dependence outside the cosine is one scalar
`e^{e²/4}`; the bank-dependent factor is the cosine-twisted combination. -/
theorem pairR_sum {ι : Type*} (s : Finset ι) (c q : ι → ℝ) (γ e : ℝ) :
    ∑ i ∈ s, c i * pairR γ (q i) e
      = 2 * Real.exp (e ^ 2 / 4)
          * ∑ i ∈ s, c i * Gp (γ - q i) * Real.cos ((γ - q i) * e / 2) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [pairR_eq]
  ring

/-- **No slack, exact form.**  If the weighting vanishes at the height `γ`
(`∑ c_i Gp(γ - q_i) = 0`, the condition satisfied by an extremal `φ_c` of the dual LP), the
entire pair contribution is the cosine *defect* `cos(·) - 1`, which is `≤ 0` termwise for
nonnegative weights and is `O(e²)` as `e → 0`.  No first-order term survives. -/
theorem pairR_sum_of_vanishing {ι : Type*} (s : Finset ι) (c q : ι → ℝ) (γ e : ℝ)
    (h0 : ∑ i ∈ s, c i * Gp (γ - q i) = 0) :
    ∑ i ∈ s, c i * pairR γ (q i) e
      = 2 * Real.exp (e ^ 2 / 4)
          * ∑ i ∈ s, c i * Gp (γ - q i) * (Real.cos ((γ - q i) * e / 2) - 1) := by
  rw [pairR_sum]
  have : ∑ i ∈ s, c i * Gp (γ - q i) * (Real.cos ((γ - q i) * e / 2) - 1)
      = (∑ i ∈ s, c i * Gp (γ - q i) * Real.cos ((γ - q i) * e / 2))
        - ∑ i ∈ s, c i * Gp (γ - q i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [this, h0, sub_zero]

/-- Termwise sign for nonnegative weights: the defect is `≤ 0`. -/
theorem defect_nonpos {ι : Type*} (s : Finset ι) (c q : ι → ℝ) (γ e : ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) :
    ∑ i ∈ s, c i * Gp (γ - q i) * (Real.cos ((γ - q i) * e / 2) - 1) ≤ 0 := by
  refine Finset.sum_nonpos (fun i hi => ?_)
  have hG : 0 ≤ Gp (γ - q i) := by
    unfold Gp
    positivity
  have hcos : Real.cos ((γ - q i) * e / 2) - 1 ≤ 0 := by
    linarith [Real.cos_le_one ((γ - q i) * e / 2)]
  have := mul_nonneg (hc i hi) hG
  nlinarith
