/-
Copyright 2026 James C. Kerr (QuantQJ). Apache-2.0.
-/
import Mathlib

/-!
# The Haar/Chebyshev bound for a kernel with positive collocation determinants

Companion to `FleetPosKernelCone`, which bounds the zeros of *nonnegatively* weighted
combinations (there are none, unless the weighting is trivial).  This file bounds the zeros of an
*arbitrary* weighting, from a determinant hypothesis instead of a positivity hypothesis.

* `StrictlyTotallyPositive k r` : every `r x r` collocation minor at increasing points and
  increasing indices has positive determinant.
* `weights_eq_zero_of_collocation` : one nonsingular collocation matrix suffices -- a weighting
  killing the combination at those `m` points is the zero weighting.
* `weights_eq_zero_of_stp` : hence an STP kernel of order `m` admits **at most `m - 1` zeros**
  for a nontrivial combination of `m` columns.

Together with `FleetPosKernelCone.comb_pos` this gives the pair: for a strictly positive STP
kernel, a nontrivial nonnegative weighting has no zeros at all, and a nontrivial arbitrary
weighting has at most `m - 1`.

**Variation diminishing is stated, not proved.**  `VariationDiminishing k` says the number of
distinct zeros of a combination is at most the number of sign changes of its weights (Karlin).
It is a `Prop` carried in signatures, never an `axiom` and never a `sorry` in a built module.
Nonsingularity of a single minor does **not** prove it: the classical proof needs Karlin's basic
composition formula for the compound kernels, which Mathlib does not have.  The target statement
with its `sorry` is quarantined in `research_notes/VARIATION-DIMINISHING/Target.lean`, which is
not a lakefile root, in the same way as the `audit-20261106` calibration files.

Typeclass notes, since this is easy to get wrong:
* `LinearOrder X` is needed only to say the evaluation points increase.
* `LinearOrder ι` is needed to say the indices increase -- and it also supplies the
  `DecidableEq ι` that `Matrix.det` and `Finset.sort` require, so `DecidableEq` need not be
  assumed separately once `ι` is linearly ordered.  In a version where `ι` is only a `Fintype`
  (as in the first draft of this file) both are missing and nothing typechecks.
* `Fintype ι` is needed only where one sums or counts over *all* of `ι`: in `signChanges` and in
  `VariationDiminishing`.  The strict-total-positivity definition quantifies over `Fin r → ι`
  and needs no finiteness at all.
-/

set_option autoImplicit false
noncomputable section
open Finset Matrix

variable {X : Type*}

/-- Strict total positivity of order `r`: every `r × r` collocation minor at increasing
points and increasing indices has positive determinant. -/
def StrictlyTotallyPositive [LinearOrder X] {ι : Type*} [LinearOrder ι]
    (k : X → ι → ℝ) (r : ℕ) : Prop :=
  ∀ (xs : Fin r → X) (is : Fin r → ι),
    StrictMono xs → StrictMono is → 0 < (Matrix.of fun i j => k (xs i) (is j)).det

/-- **Haar / Chebyshev property.**  If one collocation matrix is nonsingular, a weighting that
kills the combination at those `m` points is the zero weighting. -/
theorem weights_eq_zero_of_collocation {m : ℕ} (k : X → Fin m → ℝ) (c : Fin m → ℝ)
    (xs : Fin m → X) (hdet : (Matrix.of fun i j => k (xs i) j).det ≠ 0)
    (hz : ∀ i, ∑ j, c j * k (xs i) j = 0) : c = 0 := by
  set A : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i j => k (xs i) j with hA
  have hmul : A.mulVec c = 0 := by
    funext i
    have h : ∑ j, k (xs i) j * c j = 0 := by
      rw [show ∑ j, k (xs i) j * c j = ∑ j, c j * k (xs i) j from
        Finset.sum_congr rfl (fun j _ => mul_comm _ _)]
      exact hz i
    simpa [Matrix.mulVec, hA, dotProduct] using h
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  calc c = (A⁻¹ * A).mulVec c := by rw [Matrix.nonsing_inv_mul A hu, Matrix.one_mulVec]
    _ = A⁻¹.mulVec (A.mulVec c) := by rw [Matrix.mulVec_mulVec]
    _ = 0 := by rw [hmul, Matrix.mulVec_zero]

/-- **An STP kernel of order `m` has at most `m - 1` zeros**: `m` distinct increasing zeros of a
combination of `m` columns force every weight to vanish. -/
theorem weights_eq_zero_of_stp [LinearOrder X] {m : ℕ}
    (k : X → Fin m → ℝ) (hk : StrictlyTotallyPositive k m)
    (c : Fin m → ℝ) (xs : Fin m → X) (hxs : StrictMono xs)
    (hz : ∀ i, ∑ j, c j * k (xs i) j = 0) : c = 0 :=
  weights_eq_zero_of_collocation k c xs
    (ne_of_gt (hk xs id hxs strictMono_id)) hz

/-- The Gaussian dictionary is STP of every order (Schoenberg); stated for order `m` as the
collocation hypothesis actually used, so the instance is checkable per application. -/
def GaussCol {m : ℕ} (q : Fin m → ℝ) : ℝ → Fin m → ℝ :=
  fun t j => Real.sqrt Real.pi * Real.exp (-(t - q j) ^ 2 / 4)

theorem gaussCol_pos {m : ℕ} (q : Fin m → ℝ) (t : ℝ) (j : Fin m) : 0 < GaussCol q t j := by
  unfold GaussCol
  have h1 : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have h2 := Real.exp_pos (-(t - q j) ^ 2 / 4)
  positivity

/-! ### Sign changes and the variation-diminishing target -/


/-- Sign changes of a list of nonzero reals: count adjacent pairs with opposite signs. -/
def signChangesList : List ℝ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: t => (if a * b < 0 then 1 else 0) + signChangesList (b :: t)

/-- Number of strict sign changes of a weight vector, zeros ignored.  Needs `LinearOrder ι`
to order the indices, `Fintype ι` to enumerate them, `DecidableEq ι` for `Finset.sort`. -/
def signChanges {ι : Type*} [Fintype ι] [LinearOrder ι] (c : ι → ℝ) : ℕ :=
  signChangesList (((Finset.univ.sort (· ≤ ·)).map c).filter (fun x => x ≠ 0))

example : signChangesList [1, -1, 1] = 2 := by norm_num [signChangesList]
example : signChangesList [1, 2, 3] = 0 := by norm_num [signChangesList]

/-- **Variation-diminishing property** (Karlin).  Stated as a `Prop`, never assumed: the number
of distinct zeros of a combination is at most the number of sign changes of its weights. -/
def VariationDiminishing {X ι : Type*} [LinearOrder X] [Fintype ι] [LinearOrder ι]
    (k : X → ι → ℝ) : Prop :=
  ∀ (c : ι → ℝ) (r : ℕ) (xs : Fin r → X), StrictMono xs →
    (∀ i : Fin r, ∑ j, c j * k (xs i) j = 0) → (∃ j, c j ≠ 0) → r ≤ signChanges c

/-- Interface: consuming the property. -/
theorem card_zeros_le_signChanges {X ι : Type*} [LinearOrder X] [Fintype ι] [LinearOrder ι]
    {k : X → ι → ℝ} (hVD : VariationDiminishing k) (c : ι → ℝ) {r : ℕ} (xs : Fin r → X)
    (hxs : StrictMono xs) (hz : ∀ i : Fin r, ∑ j, c j * k (xs i) j = 0)
    (hc : ∃ j, c j ≠ 0) : r ≤ signChanges c :=
  hVD c r xs hxs hz hc
