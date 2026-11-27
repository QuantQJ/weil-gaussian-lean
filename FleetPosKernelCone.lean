/-
Copyright 2026 James C. Kerr (QuantQJ). Apache-2.0.
-/
import Mathlib

/-!
# Nonnegative combinations of a strictly positive kernel

`FleetDualExtremal.weights_eq_zero_of_phiB_eq_zero` says a nonnegatively weighted width-one
Gaussian combination cannot vanish anywhere unless every weight vanishes.  The proof used
exactly one property of the probe: `0 < Gp u`.  This file states the result at that level of
generality, for an arbitrary strictly positive kernel `k : X → ι → ℝ` on arbitrary index and
point types -- no continuity, no total positivity, no structure on `X` at all.

* `weights_eq_zero_of_comb_eq_zero` : vanishing at one point forces the trivial weighting.
* `comb_pos` : hence a nonzero nonnegative weighting is strictly positive *everywhere* -- the
  cone of nonnegative combinations has no element that touches zero without being zero.
* `exists_neg_of_comb_eq_zero` : the polar statement.  Every vanishing nontrivial certificate
  has a strictly negative weight: **certificates must change sign.**  So every dual extremal
  problem over such a kernel pays a negative-part price (the `K * M` term of
  `FleetDualConverse.DualIneq`), for structural reasons that have nothing to do with Gaussians.

Instances: `strictlyPos_exp`, `strictlyPos_gauss` (recovering the original), `strictlyPos_cauchy`
(Poisson kernel), `strictlyPos_laplace`, `strictlyPos_heat` (the whole `b`-family at once, with
`X = ℝ × ℝ` carrying both the width and the point).
-/

noncomputable section
open Finset

variable {ι : Type*}

/-- **The engine.**  A nonnegative combination of strictly positive values vanishes only if
every weight vanishes.  All that is used is `0 < K i`. -/
theorem weights_eq_zero_of_sum_eq_zero (s : Finset ι) (c K : ι → ℝ)
    (hK : ∀ i ∈ s, 0 < K i) (hc : ∀ i ∈ s, 0 ≤ c i)
    (h : ∑ i ∈ s, c i * K i = 0) : ∀ i ∈ s, c i = 0 := by
  have hterm : ∀ i ∈ s, c i * K i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => mul_nonneg (hc i hi) (hK i hi).le)).mp h
  intro i hi
  rcases mul_eq_zero.mp (hterm i hi) with h1 | h2
  · exact h1
  · exact absurd h2 (ne_of_gt (hK i hi))

/-- Contrapositive: a nonzero nonnegative weighting gives a strictly positive value. -/
theorem sum_pos_of_exists_pos (s : Finset ι) (c K : ι → ℝ)
    (hK : ∀ i ∈ s, 0 < K i) (hc : ∀ i ∈ s, 0 ≤ c i)
    {j : ι} (hj : j ∈ s) (hcj : 0 < c j) : 0 < ∑ i ∈ s, c i * K i := by
  have hnn : ∀ i ∈ s, 0 ≤ c i * K i := fun i hi => mul_nonneg (hc i hi) (hK i hi).le
  have hle : 0 ≤ ∑ i ∈ s, c i * K i := Finset.sum_nonneg hnn
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exact absurd (weights_eq_zero_of_sum_eq_zero s c K hK hc h.symm j hj) (ne_of_gt hcj)

/-- **The polar statement: certificates must change sign.**  If a combination of a strictly
positive kernel vanishes but is not the zero weighting, some weight is strictly negative. -/
theorem exists_neg_weight_of_vanishing (s : Finset ι) (c K : ι → ℝ)
    (hK : ∀ i ∈ s, 0 < K i) (h : ∑ i ∈ s, c i * K i = 0)
    {j : ι} (hj : j ∈ s) (hcj : c j ≠ 0) : ∃ i ∈ s, c i < 0 := by
  by_contra hno
  push Not at hno
  exact hcj (weights_eq_zero_of_sum_eq_zero s c K hK (fun i hi => hno i hi) h j hj)

/-! ### Kernel form: a strictly positive kernel on any index and point type -/

/-- A kernel is *strictly positive* if every value is. -/
def StrictlyPos {X : Type*} (k : X → ι → ℝ) : Prop := ∀ x i, 0 < k x i

/-- Combination of a kernel's columns with weights `c`. -/
def comb {X : Type*} (s : Finset ι) (c : ι → ℝ) (k : X → ι → ℝ) (x : X) : ℝ :=
  ∑ i ∈ s, c i * k x i

/-- **Vanishing at one point forces the trivial weighting**, for *any* strictly positive kernel
on *any* point type: no continuity, no total positivity, no structure on `X`. -/
theorem weights_eq_zero_of_comb_eq_zero {X : Type*} (s : Finset ι) (c : ι → ℝ)
    (k : X → ι → ℝ) (hk : StrictlyPos k) (hc : ∀ i ∈ s, 0 ≤ c i) {x : X}
    (h : comb s c k x = 0) : ∀ i ∈ s, c i = 0 :=
  weights_eq_zero_of_sum_eq_zero s c (k x) (fun i _ => hk x i) hc h

/-- Hence a nonzero nonnegative weighting is strictly positive **everywhere**: the cone of
nonnegative combinations has no element that touches zero without being zero. -/
theorem comb_pos {X : Type*} (s : Finset ι) (c : ι → ℝ) (k : X → ι → ℝ)
    (hk : StrictlyPos k) (hc : ∀ i ∈ s, 0 ≤ c i) {j : ι} (hj : j ∈ s) (hcj : 0 < c j) :
    ∀ x : X, 0 < comb s c k x :=
  fun x => sum_pos_of_exists_pos s c (k x) (fun i _ => hk x i) hc hj hcj

/-- Every vanishing nontrivial certificate changes sign, for any strictly positive kernel. -/
theorem exists_neg_of_comb_eq_zero {X : Type*} (s : Finset ι) (c : ι → ℝ)
    (k : X → ι → ℝ) (hk : StrictlyPos k) {x : X} (h : comb s c k x = 0)
    {j : ι} (hj : j ∈ s) (hcj : c j ≠ 0) : ∃ i ∈ s, c i < 0 :=
  exists_neg_weight_of_vanishing s c (k x) (fun i _ => hk x i) h hj hcj

/-! ### Instances -/

/-- Any kernel of the form `exp ∘ f` is strictly positive. -/
theorem strictlyPos_exp {X : Type*} (f : X → ι → ℝ) :
    StrictlyPos (fun x i => Real.exp (f x i)) := fun _ _ => Real.exp_pos _

/-- The width-one Gaussian dictionary: the original statement, now an instance. -/
theorem strictlyPos_gauss (q : ι → ℝ) (A : ℝ) (hA : 0 < A) :
    StrictlyPos (fun (t : ℝ) (i : ι) => A * Real.exp (-(t - q i) ^ 2 / 4)) := by
  intro t i
  have := Real.exp_pos (-(t - q i) ^ 2 / 4)
  positivity

/-- Poisson / Cauchy dictionary. -/
theorem strictlyPos_cauchy (q : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    StrictlyPos (fun (t : ℝ) (i : ι) => δ / (δ ^ 2 + (t - q i) ^ 2)) := by
  intro t i
  have h : 0 < δ ^ 2 + (t - q i) ^ 2 := by positivity
  exact div_pos hδ h

/-- Laplace / two-sided exponential dictionary. -/
theorem strictlyPos_laplace (q : ι → ℝ) (δ : ℝ) :
    StrictlyPos (fun (t : ℝ) (i : ι) => Real.exp (-δ * |t - q i|)) :=
  fun _ _ => Real.exp_pos _

/-- Heat kernel at any positive time; the `b`-family of the dual problem, all `b` at once. -/
theorem strictlyPos_heat (q : ι → ℝ) :
    StrictlyPos (fun (p : ℝ × ℝ) (i : ι) => Real.exp (-(p.1) * (p.2 - q i) ^ 2)) :=
  fun _ _ => Real.exp_pos _
