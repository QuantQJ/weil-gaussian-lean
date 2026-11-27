/-
Copyright 2026 James C. Kerr (QuantQJ). Apache-2.0.
-/
import FleetPairExact

/-!
# Extremality in the Gaussian dual problem

`research_notes/DUAL-INEQUALITY/ATTEMPT.md` asserts, from `tools/dual_lp.py`: "the extremal
phi_c are exactly those vanishing on the zeros ... There is no slack."  This file formalizes the
structural content of that claim for the width-one Gaussian dictionary.

* `weights_eq_zero_of_phiB_eq_zero` : a **nonnegatively weighted** probe combination cannot
  vanish at any point unless every weight is zero.  So a certificate that vanishes at a height
  must use cancellation; sign-unrestricted weights are forced, and with them the `K * M` term
  of `FleetDualConverse.DualIneq`.
* `cos_sub_one`, `defect_eq_sin` : the pair defect of `FleetPairExact.pairR_sum_of_vanishing`
  in exact `sin^2` form, `-2 * sum c_i Gp(gamma - q_i) sin((gamma - q_i) e / 4)^2`.
* `defect_eq_zero_iff` : for nonnegative weights the defect vanishes **iff** every centre either
  carries no weight or sits exactly on a zero of the twisting sine.  That is the equality case:
  the inequality is tight only on that degenerate set.
* `defect_neg` : one centre with positive weight off the sine's zero set makes the defect
  strictly negative.  No slack.

What is still **not** formalized: that the dual LP's optimum is *attained* at such a
configuration at every height.  That is a statement about where a finite linear program attains
its maximum, measured in `tools/dual_lp.py`, and remains Tier F.  What is proved here is the
equality case and the strictness, which is what the note uses the LP picture to assert.
-/

noncomputable section
open Finset

theorem Gp_pos (u : ℝ) : 0 < Gp u := by
  unfold Gp
  have : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  positivity

/-- Gaussian combination with weights `c` at centres `q`. -/
def phiB {ι : Type*} (s : Finset ι) (c q : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ s, c i * Gp (t - q i)

/-- **A nonnegatively weighted probe combination never vanishes unless it is trivial.**
So an extremal certificate — one that vanishes at a height — must use cancellation;
sign-unrestricted weights are forced, and with them the `K · M` term of the dual inequality. -/
theorem weights_eq_zero_of_phiB_eq_zero {ι : Type*} (s : Finset ι) (c q : ι → ℝ) (t : ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (h : phiB s c q t = 0) : ∀ i ∈ s, c i = 0 := by
  have hterm : ∀ i ∈ s, c i * Gp (t - q i) = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp h
    intro i hi
    exact mul_nonneg (hc i hi) (Gp_pos _).le
  intro i hi
  have := hterm i hi
  rcases mul_eq_zero.mp this with h1 | h2
  · exact h1
  · exact absurd h2 (ne_of_gt (Gp_pos _))

/-- `cos x - 1 = -2 sin(x/2)²`. -/
theorem cos_sub_one (x : ℝ) : Real.cos x - 1 = -2 * Real.sin (x / 2) ^ 2 := by
  have h : Real.cos (2 * (x / 2)) = 1 - 2 * Real.sin (x / 2) ^ 2 := by
    rw [Real.cos_two_mul', Real.cos_sq']
    ring_nf
  rw [show 2 * (x / 2) = x by ring] at h
  rw [h]; ring

/-- **The pair defect in exact `sin²` form.**  No expansion, no remainder. -/
theorem defect_eq_sin {ι : Type*} (s : Finset ι) (c q : ι → ℝ) (γ e : ℝ) :
    ∑ i ∈ s, c i * Gp (γ - q i) * (Real.cos ((γ - q i) * e / 2) - 1)
      = -2 * ∑ i ∈ s, c i * Gp (γ - q i) * Real.sin ((γ - q i) * e / 4) ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [cos_sub_one]
  rw [show (γ - q i) * e / 2 / 2 = (γ - q i) * e / 4 by ring]
  ring

/-- **Extremality, nonnegative-weight case.**  The defect vanishes exactly when every centre
either carries no weight or sits at a zero of the twisting sine. -/
theorem defect_eq_zero_iff {ι : Type*} (s : Finset ι) (c q : ι → ℝ) (γ e : ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) :
    (∑ i ∈ s, c i * Gp (γ - q i) * (Real.cos ((γ - q i) * e / 2) - 1) = 0)
      ↔ ∀ i ∈ s, c i = 0 ∨ Real.sin ((γ - q i) * e / 4) = 0 := by
  rw [defect_eq_sin]
  have hnn : ∀ i ∈ s, 0 ≤ c i * Gp (γ - q i) * Real.sin ((γ - q i) * e / 4) ^ 2 := by
    intro i hi
    have := mul_nonneg (hc i hi) (Gp_pos (γ - q i)).le
    positivity
  constructor
  · intro h
    have hz : ∑ i ∈ s, c i * Gp (γ - q i) * Real.sin ((γ - q i) * e / 4) ^ 2 = 0 := by linarith
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz
    intro i hi
    have hi' := this i hi
    rcases mul_eq_zero.mp hi' with h1 | h2
    · rcases mul_eq_zero.mp h1 with h3 | h4
      · exact Or.inl h3
      · exact absurd h4 (ne_of_gt (Gp_pos _))
    · exact Or.inr (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2)
  · intro h
    have : ∑ i ∈ s, c i * Gp (γ - q i) * Real.sin ((γ - q i) * e / 4) ^ 2 = 0 := by
      refine Finset.sum_eq_zero (fun i hi => ?_)
      rcases h i hi with h1 | h2
      · rw [h1]; ring
      · rw [h2]; ring
    rw [this]; ring

/-- **Strict defect.**  One centre with positive weight and a nonvanishing twist forces the
defect strictly negative: there is no slack to be had from such a configuration. -/
theorem defect_neg {ι : Type*} (s : Finset ι) (c q : ι → ℝ) (γ e : ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) {j : ι} (hj : j ∈ s) (hcj : 0 < c j)
    (hsj : Real.sin ((γ - q j) * e / 4) ≠ 0) :
    ∑ i ∈ s, c i * Gp (γ - q i) * (Real.cos ((γ - q i) * e / 2) - 1) < 0 := by
  have hne : ¬ (∀ i ∈ s, c i = 0 ∨ Real.sin ((γ - q i) * e / 4) = 0) := by
    intro h
    rcases h j hj with h1 | h2
    · exact absurd h1 (ne_of_gt hcj)
    · exact hsj h2
  have hle : ∑ i ∈ s, c i * Gp (γ - q i) * (Real.cos ((γ - q i) * e / 2) - 1) ≤ 0 := by
    refine Finset.sum_nonpos (fun i hi => ?_)
    have h1 : 0 ≤ c i * Gp (γ - q i) := mul_nonneg (hc i hi) (Gp_pos _).le
    have h2 : Real.cos ((γ - q i) * e / 2) - 1 ≤ 0 := by
      linarith [Real.cos_le_one ((γ - q i) * e / 2)]
    exact mul_nonpos_of_nonneg_of_nonpos h1 h2
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exact absurd ((defect_eq_zero_iff s c q γ e hc).mp h) hne
