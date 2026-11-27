/-
Copyright 2026 James C. Kerr (QuantQJ). Apache-2.0.
-/
import FleetPairExact
import GaussianTest

/-!
# The pair defect is governed by one scalar: offset × bandwidth

`FleetPairExact.pairR_sum_of_vanishing` shows that the off-line pair contribution of the
*width-one* Gaussian dictionary is the cosine defect `cos(·) - 1`, which is `O(e²)`, and
`FleetDualExtremal` draws the no-slack conclusion from it.  Reading that as a fact about
off-line pairs, or about admissible envelopes, is wrong.  This file isolates what it is a
fact about.

Write a probe as a superposition of spectral modes, `F u = ∑ w j * cos (u * t j)`; the
spectral variable `t` is the prime-side variable `u = log n`, so the band edge
`a = max |t j|` is the logarithm of the prime cutoff.  Then:

* `cos_pair` — one mode's pair is exactly `2 cos (u t) cosh (e t)`.  The offset enters only
  through `cosh (e t)`, hence only through the product `e * t`.
* `probePair_sub_two_mul` — the defect is `∑ w j * cos (u t j) * 2 (cosh (e t j) - 1)`,
  exactly.  That is the universal form, and the Gaussian's `cos(·) - 1` is one evaluation of
  it, so the `O(e²)` suppression is *Taylor's theorem in `e t`*, not a Gaussian artifact: no
  envelope escapes it at fixed bandwidth.
* `defect_le_coshFactor_mul` — with nonnegative weights inside the band `|t| ≤ a`, the defect
  at the height is at most `2 (cosh (e a) - 1)` times the probe's own mass, and
  `defect_eq_coshFactor_mul_of_edge` shows that bound is attained by mass at the band edge.
* `one_lt_coshFactor_of_one_le_mul` — `e * a ≥ 1` already puts the extremal defect above the
  probe's own mass.  So the suppression is exactly the statement `e * a ≪ 1`, and
  `tendsto_coshFactor_atTop` says nothing caps it from above: it is not a barrier of the
  problem.

The second half identifies the bandwidth inside the dictionary the criterion actually uses.
By the repo's own `GaussianTest.gaussHat_eq` the width-`b` probe is
`√(π/b) · exp(-(t-α)²/(4b))`, whose effective band edge is `1/√b`:

* `gauss_defect_eq_width` — its defect ratio at the height is exactly
  `gaussRatioB b e = 2 (exp (e²/(4b)) - 1)`.
* `gaussRatioB_eq_gaussRatio` — **`b` enters only through `e / √b`.**  The width-`b` family is
  the width-one family reparametrised by that one scalar, which is `e` times the effective
  bandwidth.
* `gaussRatioB_one`, `one_lt_gaussRatioB_of_sq_le` — at `b = 1` the scalar is pinned at `e`,
  which is what forces the suppression; at `4b ≤ e²` it is gone.

So `FleetPairExact` and `FleetDualExtremal` hard-code `b = 1`, and their extremality and
no-slack conclusions are conclusions about that normalisation, not about the problem.  The
scalar that has to be moved is `e / √b`, and `FleetRationalBankCriterion.UniformFeasibility`
quantifies `∃ M, ∀ n` *after* fixing `b`, so it cannot move it.
-/
noncomputable section
open Finset

namespace FleetPairCosh

/-! ## One mode -/

/-- **The pair of a single spectral mode, exactly.**  An off-line pair at height `u` with
offset `e` sees the mode `cos (· * t)` as `2 cos (u t) cosh (e t)`: the offset enters only
through `cosh (e t)`, so only through the product `e * t`. -/
theorem cos_pair (u t e : ℝ) :
    Complex.cos (((u : ℂ) + (e : ℂ) * Complex.I) * (t : ℂ))
      + Complex.cos (((u : ℂ) - (e : ℂ) * Complex.I) * (t : ℂ))
      = 2 * (Real.cos (u * t) : ℂ) * (Real.cosh (e * t) : ℂ) := by
  rw [Complex.cos_add_cos]
  have h1 : (((u : ℂ) + (e : ℂ) * Complex.I) * (t : ℂ)
      + ((u : ℂ) - (e : ℂ) * Complex.I) * (t : ℂ)) / 2 = ((u * t : ℝ) : ℂ) := by
    push_cast; ring
  have h2 : (((u : ℂ) + (e : ℂ) * Complex.I) * (t : ℂ)
      - ((u : ℂ) - (e : ℂ) * Complex.I) * (t : ℂ)) / 2 = ((e * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h1, h2, Complex.cos_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_cosh]

/-! ## Finitely many modes with nonnegative spectral mass -/

variable {ι : Type*}

/-- A probe with finite spectral mass `w` at frequencies `t`: `F u = ∑ w j cos (u t j)`. -/
def probe (s : Finset ι) (w t : ι → ℝ) (u : ℝ) : ℝ := ∑ j ∈ s, w j * Real.cos (u * t j)

/-- Its off-line pair at offset `e`, mode by mode via `cos_pair`. -/
def probePair (s : Finset ι) (w t : ι → ℝ) (u e : ℝ) : ℝ :=
  ∑ j ∈ s, w j * (2 * Real.cos (u * t j) * Real.cosh (e * t j))

/-- `2 (cosh x - 1)`: the entire offset dependence of the defect, as a function of `e * t`. -/
def coshFactor (x : ℝ) : ℝ := 2 * (Real.cosh x - 1)

@[simp] theorem coshFactor_zero : coshFactor 0 = 0 := by simp [coshFactor]

theorem coshFactor_nonneg (x : ℝ) : 0 ≤ coshFactor x := by
  have := Real.one_le_cosh x
  unfold coshFactor; linarith

/-- **The universal defect identity.**  No expansion, no remainder: the pair excess is the
spectral mass weighted by `coshFactor (e * t j)`. -/
theorem probePair_sub_two_mul (s : Finset ι) (w t : ι → ℝ) (u e : ℝ) :
    probePair s w t u e - 2 * probe s w t u
      = ∑ j ∈ s, w j * Real.cos (u * t j) * coshFactor (e * t j) := by
  unfold probePair probe coshFactor
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- At the height itself the cosines are `1`, so the defect is the plain spectral average of
`coshFactor (e * t j)` and the probe's mass is `∑ w j`. -/
theorem probe_zero (s : Finset ι) (w t : ι → ℝ) : probe s w t 0 = ∑ j ∈ s, w j := by
  unfold probe; exact Finset.sum_congr rfl (fun j _ => by simp)

theorem defect_at_zero (s : Finset ι) (w t : ι → ℝ) (e : ℝ) :
    probePair s w t 0 e - 2 * probe s w t 0 = ∑ j ∈ s, w j * coshFactor (e * t j) := by
  rw [probePair_sub_two_mul]
  exact Finset.sum_congr rfl (fun j _ => by simp)

/-- **The bandwidth bound.**  Nonnegative spectral mass inside the band `|t| ≤ a` cannot
produce a defect larger than `coshFactor (e * a)` times the probe's own mass.  The bound
depends on `e` and `a` only through their product. -/
theorem defect_le_coshFactor_mul {s : Finset ι} {w t : ι → ℝ} {a e : ℝ}
    (hw : ∀ j ∈ s, 0 ≤ w j) (ht : ∀ j ∈ s, |t j| ≤ a) (he : 0 ≤ e) :
    probePair s w t 0 e - 2 * probe s w t 0 ≤ coshFactor (e * a) * probe s w t 0 := by
  rw [defect_at_zero, probe_zero, Finset.mul_sum]
  refine Finset.sum_le_sum (fun j hj => ?_)
  have ha : 0 ≤ a := le_trans (abs_nonneg _) (ht j hj)
  have hle : Real.cosh (e * t j) ≤ Real.cosh (e * a) := by
    refine (Real.cosh_le_cosh).mpr ?_
    rw [abs_mul, abs_mul, abs_of_nonneg he, abs_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left (ht j hj) he
  have : coshFactor (e * t j) ≤ coshFactor (e * a) := by unfold coshFactor; linarith
  calc w j * coshFactor (e * t j) ≤ w j * coshFactor (e * a) :=
        mul_le_mul_of_nonneg_left this (hw j hj)
    _ = coshFactor (e * a) * w j := by ring

/-- **The bound is attained.**  Mass placed at the band edge realises `coshFactor (e * a)`
exactly, so nothing is lost in `defect_le_coshFactor_mul`. -/
theorem defect_eq_coshFactor_mul_of_edge {s : Finset ι} {w t : ι → ℝ} {a e : ℝ}
    (ha : 0 ≤ a) (ht : ∀ j ∈ s, |t j| = a) :
    probePair s w t 0 e - 2 * probe s w t 0 = coshFactor (e * a) * probe s w t 0 := by
  rw [defect_at_zero, probe_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hcosh : Real.cosh (e * t j) = Real.cosh (e * a) := by
    rcases (abs_eq ha).mp (ht j hj) with h | h
    · rw [h]
    · rw [show e * t j = -(e * a) by rw [h]; ring, Real.cosh_neg]
  rw [coshFactor, coshFactor, hcosh]; ring

/-! ## Where the suppression lives -/

/-- `cosh 1 > 3/2`, from the two-sided decimal bounds on `e`. -/
theorem three_halves_lt_cosh_one : (3 : ℝ) / 2 < Real.cosh 1 := by
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hp : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hinv : (0.367879441 : ℝ) < Real.exp (-1) := by
    rw [Real.exp_neg]
    rw [lt_inv_comm₀ (by norm_num) hp]
    calc Real.exp 1 < 2.7182818286 := h2
      _ < (0.367879441 : ℝ)⁻¹ := by norm_num
  rw [Real.cosh_eq]
  linarith

/-- **`e * a ≥ 1` removes the suppression.**  Once the offset times the bandwidth reaches one,
the extremal defect already exceeds the probe's own mass: there is nothing left to suppress. -/
theorem one_lt_coshFactor_of_one_le_mul {a e : ℝ} (h : 1 ≤ e * a) : 1 < coshFactor (e * a) := by
  have hle : Real.cosh 1 ≤ Real.cosh (e * a) := by
    refine (Real.cosh_le_cosh).mpr ?_
    rw [abs_one, abs_of_nonneg (by linarith : (0:ℝ) ≤ e * a)]
    exact h
  have := three_halves_lt_cosh_one
  unfold coshFactor; linarith

/-! ## The Gaussian dictionary does not use its bandwidth -/

/-- The width-one Gaussian dictionary's own defect ratio at the height. -/
def gaussRatio (e : ℝ) : ℝ := 2 * (Real.exp (e ^ 2 / 4) - 1)

/-- `gaussRatio` is exactly the repo's Gaussian pair excess, normalised by the probe's mass.
Note what is absent from the statement: any bandwidth.  `FleetPairExact.pairR` has no `a`. -/
theorem gauss_defect_eq (e : ℝ) : pairR 0 0 e - 2 * Gp 0 = gaussRatio e * Gp 0 := by
  have hG : Gp 0 = Real.sqrt Real.pi := by unfold Gp; norm_num
  have hP : pairR 0 0 e = 2 * Real.sqrt Real.pi * Real.exp (e ^ 2 / 4) := by
    unfold pairR; norm_num
  rw [hG, hP, gaussRatio]; ring

/-- **Nothing caps the extremal defect.**  At any fixed offset `e > 0` the band-limited
extremum `coshFactor (e * a)` tends to infinity with the bandwidth.  The `O(e²)` suppression
is therefore a statement about where the dictionary's spectral mass sits, not an upper bound
imposed by the problem. -/
theorem tendsto_coshFactor_atTop {e : ℝ} (he : 0 < e) :
    Filter.Tendsto (fun a : ℝ => coshFactor (e * a)) Filter.atTop Filter.atTop := by
  have hlin : Filter.Tendsto (fun a : ℝ => e * a) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop he Filter.tendsto_id
  have hbase : Filter.Tendsto (fun a : ℝ => Real.exp (e * a)) Filter.atTop Filter.atTop := by
    simpa [Function.comp_def] using Real.tendsto_exp_atTop.comp hlin
  have hexp : Filter.Tendsto (fun a : ℝ => Real.exp (e * a) + (-2))
      Filter.atTop Filter.atTop := Filter.tendsto_atTop_add_const_right _ (-2) hbase
  refine Filter.tendsto_atTop_mono (fun a => ?_) hexp
  have hpos : 0 < Real.exp (-(e * a)) := Real.exp_pos _
  rw [coshFactor, Real.cosh_eq]
  linarith

/-! ## The bandwidth inside the dictionary the criterion uses -/

/-- The width-`b` defect ratio at the height. -/
def gaussRatioB (b e : ℝ) : ℝ := 2 * (Real.exp (e ^ 2 / (4 * b)) - 1)

@[simp] theorem gaussRatioB_one (e : ℝ) : gaussRatioB 1 e = gaussRatio e := by
  unfold gaussRatioB gaussRatio; norm_num

/-- **The width-`b` pair defect, from the repo's own transform.**  `GaussianTest.gaussHat_eq`
gives the probe as `√(π/b) exp(-(t-α)²/(4b))`; its pair excess at the centre is exactly
`gaussRatioB b e` times the probe's value there. -/
theorem gauss_defect_eq_width {b : ℝ} (hb : 0 < b) (α e : ℝ) :
    GaussianTest.gaussHat b α ((α : ℂ) + (e : ℂ) * Complex.I)
      + GaussianTest.gaussHat b α ((α : ℂ) - (e : ℂ) * Complex.I)
      - 2 * GaussianTest.gaussHat b α (α : ℂ)
      = (gaussRatioB b e : ℂ) * (Real.sqrt (Real.pi / b) : ℂ) := by
  rw [GaussianTest.gaussHat_eq hb, GaussianTest.gaussHat_eq hb, GaussianTest.gaussHat_eq hb]
  have h1 : -(((α : ℂ) + (e : ℂ) * Complex.I) - (α : ℂ)) ^ 2 / (4 * (b : ℂ))
      = ((e ^ 2 / (4 * b) : ℝ) : ℂ) := by
    have : (((α : ℂ) + (e : ℂ) * Complex.I) - (α : ℂ)) ^ 2 = -(e : ℂ) ^ 2 := by
      rw [show ((α : ℂ) + (e : ℂ) * Complex.I) - (α : ℂ) = (e : ℂ) * Complex.I by ring]
      rw [mul_pow, Complex.I_sq]; ring
    rw [this]; push_cast; ring
  have h2 : -(((α : ℂ) - (e : ℂ) * Complex.I) - (α : ℂ)) ^ 2 / (4 * (b : ℂ))
      = ((e ^ 2 / (4 * b) : ℝ) : ℂ) := by
    have : (((α : ℂ) - (e : ℂ) * Complex.I) - (α : ℂ)) ^ 2 = -(e : ℂ) ^ 2 := by
      rw [show ((α : ℂ) - (e : ℂ) * Complex.I) - (α : ℂ) = -((e : ℂ) * Complex.I) by ring]
      rw [neg_pow, mul_pow, Complex.I_sq]; ring
    rw [this]; push_cast; ring
  have h3 : -((α : ℂ) - (α : ℂ)) ^ 2 / (4 * (b : ℂ)) = 0 := by rw [sub_self]; ring
  rw [h1, h2, h3, Complex.exp_zero, ← Complex.ofReal_exp, gaussRatioB]
  push_cast; ring

/-- **`b` enters only through `e / √b`.**  The width-`b` family is the width-one family
reparametrised by that single scalar, which is `e` times the probe's effective bandwidth
`1/√b`.  Fixing `b = 1`, as `FleetPairExact` and `FleetDualExtremal` do, pins the scalar at
`e` and so makes the `O(e²)` suppression unavoidable by construction. -/
theorem gaussRatioB_eq_gaussRatio {b : ℝ} (hb : 0 < b) (e : ℝ) :
    gaussRatioB b e = gaussRatio (e / Real.sqrt b) := by
  unfold gaussRatioB gaussRatio
  rw [div_pow, Real.sq_sqrt hb.le]
  ring_nf

/-- **The suppression is gone once `4b ≤ e²`,** i.e. once the effective bandwidth `1/√b`
reaches `2/e`: the width-`b` defect then exceeds the probe's own mass. -/
theorem one_lt_gaussRatioB_of_sq_le {b e : ℝ} (hb : 0 < b) (h : 4 * b ≤ e ^ 2) :
    1 < gaussRatioB b e := by
  have hx : (1 : ℝ) ≤ e ^ 2 / (4 * b) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have : Real.exp 1 ≤ Real.exp (e ^ 2 / (4 * b)) := Real.exp_le_exp.mpr hx
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  unfold gaussRatioB; linarith

end FleetPairCosh
