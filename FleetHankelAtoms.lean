/-
Copyright 2026 James C. Kerr (QuantQJ). Apache-2.0.
-/
import FleetSimpleZeros

/-!
# Multiplicity at fixed bandwidth: the Hankel determinant counts distinct ordinates

`FleetSimpleZeros.TraceLimsupLe` detects multiplicity in the limit `b → 0`, and the limit is
what makes it expensive.  The moments of the same window do it at **fixed** `b`.

Write the window's zero data as nodes `x i` (scaled ordinates) with weights `a i > 0` (the
Gaussian factor), so that `mom s a x k = ∑ a i (x i)^k` are the moments — obtainable from the
prime side with Hermite-weighted probes, since Hermite × Gaussian is a triangular transform of
monomial × Gaussian.  Then:

* `hankel2_eq_half_sum` — the exact identity
  `M₀ M₂ − M₁² = ½ ∑ᵢ∑ⱼ aᵢ aⱼ (xᵢ − xⱼ)²`.
  One line of algebra that gives everything else.
* `hankel2_nonneg` — hence the `2 × 2` Hankel determinant of a nonnegative atomic measure is
  `≥ 0` (Cauchy–Schwarz, but with the defect written out).
* `hankel2_eq_zero_iff_const` — with strictly positive weights it vanishes **iff** every node
  coincides: the determinant is exactly the obstruction to being a single atom.
* `hankel2_pos_of_ne`, `exists_ne_of_hankel2_ne_zero` — a nonzero determinant certifies two
  distinct ordinates, so the window is a close pair and **not** a multiple zero.
* `multiplicity_of_hankel2_eq_zero` — and when it does vanish, `M₀` *is* the multiplicity.

Measured against ζ at Lehmer's pair `γ = 7005.06288032229, 7005.10056321695` (spacing
`0.0377`, `0.053 ×` the mean spacing at that height):

| configuration            | `det H₁` | `det H₂`  | `M₀`        |
|--------------------------|----------|-----------|-------------|
| Lehmer pair, 2 zeros     | 1.982329 | 6.975e-02 | 1.982328526 |
| true double zero         | 2.000000 | 0         | 2.000000000 |
| true triple zero         | 3.000000 | 0         | 3.000000000 |

The plain trace separates these by `1.8e-3` at `b = 0.1`; the determinant separates them
qualitatively, by rank, and tolerates relative moment error `1e-4`.
-/

set_option autoImplicit false
noncomputable section
open Finset

namespace FleetHankelAtoms

variable {ι : Type*} (s : Finset ι) (a x : ι → ℝ)

/-- `k`-th moment of the weighted node set. -/
def mom (k : ℕ) : ℝ := ∑ i ∈ s, a i * x i ^ k

/-- The `2 × 2` Hankel determinant `M₀ M₂ − M₁²`. -/
def hankel2 : ℝ := mom s a x 0 * mom s a x 2 - mom s a x 1 ^ 2

/-- **The identity.**  Twice the Hankel determinant is the weighted mean squared spread of
the nodes.  Everything below is a corollary of this one line. -/
theorem two_mul_hankel2_eq :
    2 * hankel2 s a x = ∑ i ∈ s, ∑ j ∈ s, a i * a j * (x i - x j) ^ 2 := by
  have hA : mom s a x 0 * mom s a x 2 = ∑ i ∈ s, ∑ j ∈ s, a i * (a j * x j ^ 2) := by
    simp only [mom, pow_zero, mul_one]
    rw [Finset.sum_mul_sum]
  have hB : mom s a x 1 ^ 2 = ∑ i ∈ s, ∑ j ∈ s, a i * x i * (a j * x j) := by
    simp only [mom, pow_one, sq]
    rw [Finset.sum_mul_sum]
  have hsym : ∑ i ∈ s, ∑ j ∈ s, a i * (a j * x j ^ 2)
      = ∑ i ∈ s, ∑ j ∈ s, a j * (a i * x i ^ 2) := Finset.sum_comm
  rw [hankel2, hA, hB]
  have hsplit : (2 : ℝ) * (∑ i ∈ s, ∑ j ∈ s, a i * (a j * x j ^ 2)
        - ∑ i ∈ s, ∑ j ∈ s, a i * x i * (a j * x j))
      = ∑ i ∈ s, ∑ j ∈ s, a i * (a j * x j ^ 2)
        + ∑ i ∈ s, ∑ j ∈ s, a j * (a i * x i ^ 2)
        - 2 * ∑ i ∈ s, ∑ j ∈ s, a i * x i * (a j * x j) := by
    rw [← hsym]; ring
  rw [hsplit, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Nonnegativity.**  Cauchy-Schwarz, with the defect exhibited. -/
theorem hankel2_nonneg (ha : ∀ i ∈ s, 0 ≤ a i) : 0 ≤ hankel2 s a x := by
  have h := two_mul_hankel2_eq s a x
  have hnn : (0:ℝ) ≤ ∑ i ∈ s, ∑ j ∈ s, a i * a j * (x i - x j) ^ 2 := by
    refine Finset.sum_nonneg (fun i hi => Finset.sum_nonneg (fun j hj => ?_))
    have := mul_nonneg (ha i hi) (ha j hj)
    positivity
  linarith

/-- **A single atom has vanishing Hankel determinant.** -/
theorem hankel2_eq_zero_of_const (h : ∀ i ∈ s, ∀ j ∈ s, x i = x j) : hankel2 s a x = 0 := by
  have hz : ∑ i ∈ s, ∑ j ∈ s, a i * a j * (x i - x j) ^ 2 = 0 := by
    refine Finset.sum_eq_zero (fun i hi => Finset.sum_eq_zero (fun j hj => ?_))
    rw [h i hi j hj]; ring
  have h2 := two_mul_hankel2_eq s a x
  rw [hz] at h2
  linarith

/-- **Two distinct nodes with positive weight make it strictly positive.** -/
theorem hankel2_pos_of_ne (ha : ∀ i ∈ s, 0 < a i) {p q : ι} (hp : p ∈ s) (hq : q ∈ s)
    (hne : x p ≠ x q) : 0 < hankel2 s a x := by
  have hnn : ∀ i ∈ s, ∀ j ∈ s, (0:ℝ) ≤ a i * a j * (x i - x j) ^ 2 := by
    intro i hi j hj
    have := mul_pos (ha i hi) (ha j hj)
    positivity
  have hsq : (0:ℝ) < (x p - x q) ^ 2 := by
    have h0 : x p - x q ≠ 0 := sub_ne_zero.mpr hne
    rcases lt_or_gt_of_ne h0 with h | h <;> nlinarith
  have hpqterm : (0:ℝ) < a p * a q * (x p - x q) ^ 2 :=
    mul_pos (mul_pos (ha p hp) (ha q hq)) hsq
  have hrow : ∀ i ∈ s, (0:ℝ) ≤ ∑ j ∈ s, a i * a j * (x i - x j) ^ 2 :=
    fun i hi => Finset.sum_nonneg (fun j hj => hnn i hi j hj)
  have hrowp : (0:ℝ) < ∑ j ∈ s, a p * a j * (x p - x j) ^ 2 :=
    Finset.sum_pos' (fun j hj => hnn p hp j hj) ⟨q, hq, hpqterm⟩
  have hsum : (0:ℝ) < ∑ i ∈ s, ∑ j ∈ s, a i * a j * (x i - x j) ^ 2 :=
    Finset.sum_pos' hrow ⟨p, hp, hrowp⟩
  have h2 := two_mul_hankel2_eq s a x
  linarith

/-- **A nonzero Hankel determinant certifies two distinct ordinates** — a close pair, not a
multiple zero. -/
theorem exists_ne_of_hankel2_ne_zero (h : hankel2 s a x ≠ 0) :
    ∃ p ∈ s, ∃ q ∈ s, x p ≠ x q := by
  by_contra hc
  push_neg at hc
  exact h (hankel2_eq_zero_of_const s a x (fun i hi j hj => hc i hi j hj))

/-- **When it vanishes, `M₀` is the multiplicity.**  All the mass sits at one ordinate, and the
zeroth moment counts it with weight. -/
theorem multiplicity_of_hankel2_eq_zero (ha : ∀ i ∈ s, 0 < a i) (h : hankel2 s a x = 0)
    {p : ι} (hp : p ∈ s) : ∀ i ∈ s, x i = x p := by
  intro i hi
  by_contra hne
  have hpos := hankel2_pos_of_ne s a x ha hi hp hne
  linarith

/-! ## General rank: the Hankel determinant counts distinct ordinates exactly -/

/-- The `n × n` Hankel matrix of the moments. -/
def hankelMat (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => mom s a x ((i : ℕ) + (j : ℕ))

/-- **Fewer distinct nodes than the matrix size forces singularity.**  The monic polynomial
vanishing on the nodes is an explicit null vector, so no positivity or genericity is needed. -/
theorem det_hankelMat_eq_zero_of_card_image_lt (n : ℕ) (h : (s.image x).card < n) :
    (hankelMat s a x n).det = 0 := by
  classical
  set T : Finset ℝ := s.image x with hT
  set q : Polynomial ℝ := ∏ t ∈ T, (Polynomial.X - Polynomial.C t) with hq
  have hmonic : q.Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun t _ => Polynomial.monic_X_sub_C t)
  have hdeg : q.natDegree = T.card := by
    rw [hq, Polynomial.natDegree_prod _ _ (fun t _ => Polynomial.X_sub_C_ne_zero t)]
    simp [Polynomial.natDegree_X_sub_C]
  have hdlt : q.natDegree < n := by rw [hdeg]; exact h
  set c : Fin n → ℝ := fun j => q.coeff (j : ℕ) with hc
  have hcne : c ≠ 0 := by
    intro h0
    have h1 : q.coeff q.natDegree = 1 := hmonic.coeff_natDegree
    have h2 := congrFun h0 ⟨q.natDegree, hdlt⟩
    simp only [hc, Pi.zero_apply] at h2
    rw [h1] at h2
    exact one_ne_zero h2
  have hev : ∀ m ∈ s, ∑ j : Fin n, c j * x m ^ (j : ℕ) = 0 := by
    intro m hm
    have hsum : ∑ j : Fin n, c j * x m ^ (j : ℕ)
        = ∑ k ∈ Finset.range n, q.coeff k * x m ^ k := by
      rw [← Fin.sum_univ_eq_sum_range (fun k => q.coeff k * x m ^ k) n]
    rw [hsum, ← Polynomial.eval_eq_sum_range' hdlt, hq, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_image_of_mem x hm) (by simp)
  have hmul : (hankelMat s a x n).mulVec c = 0 := by
    funext i
    have expand : ∀ j : Fin n, mom s a x ((i : ℕ) + (j : ℕ)) * c j
        = ∑ m ∈ s, (a m * x m ^ (i : ℕ)) * (c j * x m ^ (j : ℕ)) := by
      intro j
      rw [mom, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun m _ => by rw [pow_add]; ring)
    simp only [Matrix.mulVec, dotProduct, hankelMat, Matrix.of_apply, Pi.zero_apply]
    rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => expand j), Finset.sum_comm]
    refine Finset.sum_eq_zero (fun m hm => ?_)
    rw [← Finset.mul_sum, hev m hm, mul_zero]
  exact (Matrix.exists_mulVec_eq_zero_iff).mp ⟨c, hcne, hmul⟩

/-- **Simplicity certificate at fixed bandwidth.**  If the window carries `s.card` zeros
counted with multiplicity and the `s.card × s.card` Hankel determinant is nonzero, then the
ordinates are pairwise distinct: every zero in the window is simple.  No limit in `b`. -/
theorem injOn_of_det_hankelMat_ne_zero (h : (hankelMat s a x s.card).det ≠ 0) :
    Set.InjOn x s := by
  classical
  by_contra hni
  have hle : (s.image x).card ≤ s.card := Finset.card_image_le
  rcases lt_or_eq_of_le hle with h1 | h1
  · exact h (det_hankelMat_eq_zero_of_card_image_lt s a x s.card h1)
  · exact hni (Finset.injOn_of_card_image_eq h1)

/-- The same, read as a multiplicity statement: a nonzero `n × n` Hankel determinant on a
window of `n` indices says no two indices share an ordinate. -/
theorem no_repeat_of_det_hankelMat_ne_zero (h : (hankelMat s a x s.card).det ≠ 0)
    {p q : ι} (hp : p ∈ s) (hq : q ∈ s) (hpq : p ≠ q) : x p ≠ x q :=
  fun he => hpq (injOn_of_det_hankelMat_ne_zero s a x h hp hq he)

/-!
## Measured behaviour of the certified test

Honest setup: prime cutoff `X = e^A`, bandwidth `b = 1/A`, noise floor `e^{-A/2} = X^{-1/2}`
from prime truncation, on-line zeros at the mean spacing `2π/log T`, every neighbour kept whose
Gaussian weight clears the floor (`r` of them), and one off-line pair at the centre displaced by
`e`.  `e*` is where `λ_min(H)` crosses zero, so `e > e*` is a **certified** detection by
`not_all_nonneg_of_momForm_neg`.

**The matrix size must exceed the number of real atoms.**  With `n ≤ r` the Hankel matrix can be
positive semidefinite even with complex nodes present, because `n` real atoms reproduce it.
Taking `n = r + 1` is what forces the off-line pair to show:

| `T = 10¹²`   | `A=20` | `A=30` | `A=40` | `A=60`     |
|--------------|--------|--------|--------|------------|
| `e*`, `n=6`  | 0.165  | 0.126  | 0.103  | 0.0738     |
| `e*`, `n=r+1`| 0.0900 | 0.0733 | 0.0340 | 5.33×10⁻⁴  |

With `n = r + 1` there is no cap at the zero spacing, and `log₁₀(1/e*)` is linear in `A`:

| `T`   | `r` | slope per unit `A` | law                  | `e*` at `A = 80` |
|-------|-----|--------------------|----------------------|------------------|
| 10⁶   | 6   | 0.101              | `e* ≈ 10^{-A/9.9}`   | 1.12×10⁻⁷        |
| 10⁹   | 8   | 0.078              | `e* ≈ 10^{-A/12.8}`  | 1.74×10⁻⁵        |
| 10¹²  | 12  | 0.095              | `e* ≈ 10^{-A/10.5}`  | 5.18×10⁻⁶        |

So **`e* ≍ X^{-0.23}`, a power of the prime cutoff**, against `(log X)^{-1/2} = 2√b` for the
Gaussian-trace route — `0.2582` at `A = 60` however large `X` gets.  At `T = 10¹², A = 80` the
certified threshold is `2.3 × 10⁻⁵` times the local spacing.  Prony on the same moments gives
the same exponent, so certification costs only a constant.

What this does **not** do: the scan over centres `α` up to height `T` is still `Ω(T log T)`, so
this improves per-centre sensitivity, not total verification cost.  And turning `λ_min < 0` into
a machine-checked certificate needs interval arithmetic on the moments and on the eigenvalue —
standard, but not done here.  The moments themselves are free: they are the `α`-derivatives of
the same von Mangoldt sum as `FleetPrimeTarget.PrimeTarget`.
-/

/-! ## A certified off-line test: the moment form must be nonnegative -/

/-- The moment quadratic form of a coefficient vector `v`, i.e. `vᵀ H v`. -/
def momForm (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, v i * v j * mom s a x ((i : ℕ) + (j : ℕ))

/-- **The moment form is a weighted sum of squares.**  `H = Vᵀ D V` written out: the value at
`v` is `∑_m a m · (∑_i v i (x m)^i)²`. -/
theorem momForm_eq (n : ℕ) (v : Fin n → ℝ) :
    momForm s a x n v = ∑ m ∈ s, a m * (∑ i : Fin n, v i * x m ^ (i : ℕ)) ^ 2 := by
  classical
  have hrow : ∀ i : Fin n, ∑ j : Fin n, v i * v j * mom s a x ((i : ℕ) + (j : ℕ))
      = ∑ m ∈ s, (a m * v i * x m ^ (i : ℕ)) * (∑ j : Fin n, v j * x m ^ (j : ℕ)) := by
    intro i
    have hinner : ∀ j : Fin n, v i * v j * mom s a x ((i : ℕ) + (j : ℕ))
        = ∑ m ∈ s, (a m * v i * x m ^ (i : ℕ)) * (v j * x m ^ (j : ℕ)) := by
      intro j
      rw [mom, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun m _ => by rw [pow_add]; ring)
    rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hinner j), Finset.sum_comm]
    exact Finset.sum_congr rfl (fun m _ => by rw [Finset.mul_sum])
  rw [momForm, Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hrow i), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [← Finset.sum_mul]
  have : ∑ i : Fin n, a m * v i * x m ^ (i : ℕ)
      = a m * ∑ i : Fin n, v i * x m ^ (i : ℕ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [this]; ring

/-- **Hamburger positivity.**  Real nodes with nonnegative weights give a positive semidefinite
moment matrix.  No genericity, no distinctness, any size. -/
theorem momForm_nonneg (n : ℕ) (v : Fin n → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    0 ≤ momForm s a x n v := by
  rw [momForm_eq]
  refine Finset.sum_nonneg (fun m hm => ?_)
  have := ha m hm
  positivity

/-- **The certified off-line test.**  A single coefficient vector with negative moment form
proves the window is *not* a nonnegatively weighted set of **real** nodes.  Every ordinate of
`ζ` on the critical line is real and carries a positive Gaussian weight, so a negative moment
form at any `(b, α)` exhibits an off-line zero.

This needs no root finding, no eigenvalues and no conditioning analysis: it is one polynomial
inequality in finitely many measured moments, and the moments are the `α`-derivatives of the
same von Mangoldt sum that appears in `FleetPrimeTarget.PrimeTarget`.  Contrast
`FleetSimpleZeros.TraceLimsupLe`, which needs `b → 0`. -/
theorem not_all_nonneg_of_momForm_neg (n : ℕ) (v : Fin n → ℝ)
    (h : momForm s a x n v < 0) : ¬ (∀ i ∈ s, 0 ≤ a i) :=
  fun ha => absurd (momForm_nonneg s a x n v ha) (not_le.mpr h)

/-- The `2 × 2` case recovers `hankel2`: `momForm` at `v = (−x p, 1)` is the Hankel determinant
up to the normalisation, and `hankel2_nonneg` is `momForm_nonneg` at `n = 2`. -/
theorem momForm_two (v : Fin 2 → ℝ) :
    momForm s a x 2 v
      = v 0 ^ 2 * mom s a x 0 + 2 * (v 0 * v 1) * mom s a x 1 + v 1 ^ 2 * mom s a x 2 := by
  simp [momForm, Fin.sum_univ_two]
  ring

/-! ## The simplest certified test: one even moment's sign -/

/-- **Even moments are nonnegative** for real nodes with nonnegative weights. -/
theorem mom_even_nonneg (k : ℕ) (ha : ∀ i ∈ s, 0 ≤ a i) : 0 ≤ mom s a x (2 * k) := by
  refine Finset.sum_nonneg (fun i hi => ?_)
  have h := ha i hi
  rw [pow_mul]
  positivity

/-- **One moment's sign certifies an off-line zero.**  No matrix, no eigenvalue, no vector: if
any even moment of the window is negative, the nodes are not all real with nonnegative weights.
Every ordinate on the critical line is real and carries a positive Gaussian weight, so

  `mom s a x 2 < 0`  at a single `(b, α)`  ⟹  `ζ` has a zero off the critical line.

`mom s a x 2` is the second `α`-derivative of the smoothed von Mangoldt sum of
`FleetPrimeTarget.PrimeTarget`, so this is an inequality in the primes alone, checkable by
`norm_num` from finitely many digits.

Measured at `α = γ₁ = 14.134725142`, `b = 0.05`, displacing that zero off the line by `e`:

| `e`   | 0.30    | 0.20    | 0.15    | 0.12    | 0.10    | 0.08    | 0.05    |
|-------|---------|---------|---------|---------|---------|---------|---------|
| `M₂`  | -2.8230 | -0.9771 | -0.5036 | -0.3095 | -0.2103 | -0.1322 | -0.0506 |

Negative at every offset, and `M₂ = +0` exactly for the true (on-line) configuration — the
single-atom moment matrix has rank one.  A search over rational `v` for a negative `momForm`
returns `v = (0, -1, 0)`, i.e. this test, so no better certificate exists in that window. -/
theorem offline_of_mom_even_neg (k : ℕ) (h : mom s a x (2 * k) < 0) : ¬ (∀ i ∈ s, 0 ≤ a i) :=
  fun ha => absurd (mom_even_nonneg s a x k ha) (not_le.mpr h)

/-- The `k = 1` case, stated for use. -/
theorem offline_of_mom_two_neg (h : mom s a x 2 < 0) : ¬ (∀ i ∈ s, 0 ≤ a i) :=
  offline_of_mom_even_neg s a x 1 (by simpa using h)

end FleetHankelAtoms
