import DiscreteSpectrum
import Mathlib

/-!
# Orthogonality and completeness of the discrete sine eigenbasis

`DiscreteSpectrum.lean` proves that `φ^{(m)}_i = sin(i θ_m)`, `θ_m = mπ/(N+1)`,
solves the discrete Dirichlet Laplacian eigenvalue equation with eigenvalue
`μ_m = (4/h²)sin²(θ_m/2)`, that the eigenvalues are positive and strictly
increasing.

That leaves the piece the project has been missing: those eigenvectors are
**mutually orthogonal with known norm**, hence (being `N` independent vectors
in an `N`-dimensional space) a complete orthogonal basis. That is what makes
the spectral decomposition of `H_N = T + D_V` rigorous rather than asserted —
without it one has eigenpairs but no spectral theorem.

Main results:

* `sum_cos_eq` — the Dirichlet-kernel sum `∑_{i<M} cos(i·qπ/M) = (1−(−1)^q)/2`
  for `0 < q < 2M`, proven by a telescoping identity (no complex exponentials).
* `sineVec_orthogonal` — `∑_i φ^{(m)}_i φ^{(n)}_i = 0` for `m ≠ n`.
* `sineVec_norm_sq` — `∑_i (φ^{(m)}_i)² = (N+1)/2`.
* `sineVec_orthonormal_basis` — the two combined: the DST-I orthogonality
  relation `∑_i φ^{(m)}_i φ^{(n)}_i = ((N+1)/2)·δ_{mn}`.

No `sorry`, no custom axioms.
-/

noncomputable section
open Real Finset

namespace DiscreteSpectrum

/-! ## The Dirichlet-kernel sum, by telescoping -/

/-- `cos(qπ) = (−1)^q`. -/
lemma cos_nat_mul_pi (q : ℕ) : Real.cos (q * π) = (-1 : ℝ) ^ q := by
  induction q with
  | zero => simp
  | succ k ih =>
      have h : ((k : ℝ) + 1) * π = k * π + π := by ring
      push_cast
      rw [h, Real.cos_add_pi, ih]
      ring

/-- **Telescoping kernel identity.** `2 sin β · ∑_{i<M} cos(2iβ)
= sin((2M−1)β) + sin β`. -/
theorem two_sin_mul_sum_cos_two_mul (β : ℝ) (M : ℕ) :
    2 * Real.sin β * (∑ i ∈ range M, Real.cos (2 * i * β))
      = Real.sin ((2 * M - 1) * β) + Real.sin β := by
  have step : ∀ i : ℕ,
      2 * Real.sin β * Real.cos (2 * i * β)
        = Real.sin ((2 * (i + 1) - 1) * β) - Real.sin ((2 * i - 1) * β) := by
    intro i
    have e1 : ((2 * ((i : ℝ) + 1) - 1) * β) = 2 * i * β + β := by ring
    have e2 : ((2 * (i : ℝ) - 1) * β) = 2 * i * β - β := by ring
    rw [e1, e2, Real.sin_add, Real.sin_sub]
    ring
  rw [Finset.mul_sum]
  have hcong : ∀ i ∈ range M,
      2 * Real.sin β * Real.cos (2 * i * β)
        = (fun k : ℕ => Real.sin ((2 * (k : ℝ) - 1) * β)) (i + 1)
          - (fun k : ℕ => Real.sin ((2 * (k : ℝ) - 1) * β)) i := by
    intro i _
    simp only []
    rw [step i]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl hcong,
      Finset.sum_range_sub (fun k : ℕ => Real.sin ((2 * (k : ℝ) - 1) * β))]
  have h0 : ((2 * ((0 : ℕ) : ℝ) - 1) * β) = -β := by push_cast; ring
  rw [h0, Real.sin_neg]
  ring

/-- The half-phase `β = qπ/(2M)` lies strictly inside `(0, π)` when
`0 < q < 2M`, so `sin β ≠ 0`. -/
lemma sin_half_phase_ne_zero {M q : ℕ} (hM : 0 < M) (hq : 0 < q) (hq2 : q < 2 * M) :
    Real.sin (q * π / (2 * M)) ≠ 0 := by
  have hMR : (0 : ℝ) < 2 * M := by positivity
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpos : 0 < (q : ℝ) * π / (2 * M) := by positivity
  have hlt : (q : ℝ) * π / (2 * M) < π := by
    rw [div_lt_iff₀ hMR]
    have : (q : ℝ) < 2 * M := by exact_mod_cast hq2
    nlinarith [pi_pos]
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hpos hlt)

/-- **Dirichlet-kernel sum.** For `0 < q < 2M`,
`∑_{i<M} cos(i·qπ/M) = (1 − (−1)^q)/2` — that is, `0` for even `q` and `1`
for odd `q`. This is the arithmetic engine behind DST orthogonality. -/
theorem sum_cos_eq {M q : ℕ} (hM : 0 < M) (hq : 0 < q) (hq2 : q < 2 * M) :
    ∑ i ∈ range M, Real.cos ((i : ℝ) * ((q : ℝ) * π / M))
      = (1 - (-1 : ℝ) ^ q) / 2 := by
  set β : ℝ := (q : ℝ) * π / (2 * M) with hβ
  have hMR : (M : ℝ) ≠ 0 := by
    have : (0 : ℝ) < M := by exact_mod_cast hM
    exact ne_of_gt this
  have hsin : Real.sin β ≠ 0 := sin_half_phase_ne_zero hM hq hq2
  -- rewrite the summand as cos(2iβ)
  have hrw : ∀ i : ℕ, (i : ℝ) * ((q : ℝ) * π / M) = 2 * (i : ℝ) * β := by
    intro i; rw [hβ]; field_simp
  rw [Finset.sum_congr rfl (fun i _ => by rw [hrw i])]
  have hkey := two_sin_mul_sum_cos_two_mul β M
  -- (2M − 1)β = qπ − β
  have hphase : (2 * (M : ℝ) - 1) * β = (q : ℝ) * π - β := by
    rw [hβ]; field_simp
  rw [hphase, Real.sin_sub, Real.sin_nat_mul_pi, cos_nat_mul_pi] at hkey
  -- hkey : 2 sin β * S = (0 * cos β - (-1)^q * sin β) + sin β
  have hkey' : 2 * Real.sin β * (∑ i ∈ range M, Real.cos (2 * (i : ℝ) * β))
      = Real.sin β * (1 - (-1 : ℝ) ^ q) := by
    rw [hkey]; ring
  -- cancel sin β
  have hcancel : Real.sin β * (2 * (∑ i ∈ range M, Real.cos (2 * (i : ℝ) * β)))
      = Real.sin β * (1 - (-1 : ℝ) ^ q) := by linarith [hkey']
  have h3 := mul_left_cancel₀ hsin hcancel
  linarith [h3]

/-! ## Orthogonality of the eigenvectors -/

/-- Product-to-sum for the eigenvector entries. -/
lemma sineVec_mul (θ₁ θ₂ : ℝ) (i : ℕ) :
    sineVec θ₁ i * sineVec θ₂ i
      = (Real.cos ((i : ℝ) * (θ₁ - θ₂)) - Real.cos ((i : ℝ) * (θ₁ + θ₂))) / 2 := by
  unfold sineVec
  have e1 : (i : ℝ) * (θ₁ - θ₂) = (i : ℝ) * θ₁ - (i : ℝ) * θ₂ := by ring
  have e2 : (i : ℝ) * (θ₁ + θ₂) = (i : ℝ) * θ₁ + (i : ℝ) * θ₂ := by ring
  rw [e1, e2, Real.cos_sub, Real.cos_add]
  ring

/-- Orthogonality in the ordered case `n < m`. -/
lemma sineVec_orthogonal_of_lt {N m n : ℕ} (hm : m ≤ N) (hn : 1 ≤ n) (hnm : n < m) :
    ∑ i ∈ range (N + 1),
      sineVec ((m : ℝ) * π / ((N : ℝ) + 1)) i
        * sineVec ((n : ℝ) * π / ((N : ℝ) + 1)) i = 0 := by
  set M : ℕ := N + 1 with hM
  have hMpos : 0 < M := Nat.succ_pos N
  have hMR : ((N : ℝ) + 1) = (M : ℝ) := by rw [hM]; push_cast; ring
  set θm : ℝ := (m : ℝ) * π / ((N : ℝ) + 1) with hθm
  set θn : ℝ := (n : ℝ) * π / ((N : ℝ) + 1) with hθn
  -- difference and sum phases, as natural-indexed kernels
  have hdiff : θm - θn = ((m - n : ℕ) : ℝ) * π / (M : ℝ) := by
    rw [hθm, hθn, hMR, Nat.cast_sub (le_of_lt hnm)]
    field_simp
  have hsum : θm + θn = ((m + n : ℕ) : ℝ) * π / (M : ℝ) := by
    rw [hθm, hθn, hMR]
    push_cast; field_simp
  rw [Finset.sum_congr rfl (fun i _ => sineVec_mul θm θn i)]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, hdiff, hsum]
  rw [sum_cos_eq (M := M) (q := m - n) hMpos (by omega) (by omega),
      sum_cos_eq (M := M) (q := m + n) hMpos (by omega) (by omega)]
  -- m−n and m+n have the same parity, so the two kernel values coincide
  have hpar : (-1 : ℝ) ^ (m - n) = (-1 : ℝ) ^ (m + n) := by
    have hmn : m + n = (m - n) + 2 * n := by omega
    rw [hmn, pow_add, pow_mul]
    norm_num
  rw [hpar]
  ring

/-- **Orthogonality of the discrete Dirichlet eigenvectors.**
For distinct modes `1 ≤ m, n ≤ N`, `∑_i φ^{(m)}_i φ^{(n)}_i = 0`. -/
theorem sineVec_orthogonal {N m n : ℕ}
    (hm : 1 ≤ m) (hmN : m ≤ N) (hn : 1 ≤ n) (hnN : n ≤ N) (hmn : m ≠ n) :
    ∑ i ∈ range (N + 1),
      sineVec ((m : ℝ) * π / ((N : ℝ) + 1)) i
        * sineVec ((n : ℝ) * π / ((N : ℝ) + 1)) i = 0 := by
  rcases lt_or_gt_of_ne hmn with h | h
  · have := sineVec_orthogonal_of_lt (N := N) hnN hm h
    rw [← this]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  · exact sineVec_orthogonal_of_lt hmN hn h

/-- **Norm of an eigenvector**: `∑_i (φ^{(m)}_i)² = (N+1)/2`.
This is the normalization constant `√(2/(N+1))` in the DST. -/
theorem sineVec_norm_sq {N m : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) :
    ∑ i ∈ range (N + 1), (sineVec ((m : ℝ) * π / ((N : ℝ) + 1)) i) ^ 2
      = ((N : ℝ) + 1) / 2 := by
  set M : ℕ := N + 1 with hM
  have hMpos : 0 < M := Nat.succ_pos N
  have hMR : ((N : ℝ) + 1) = (M : ℝ) := by rw [hM]; push_cast; ring
  set θm : ℝ := (m : ℝ) * π / ((N : ℝ) + 1) with hθm
  have hsq : ∀ i : ℕ, (sineVec θm i) ^ 2
      = (Real.cos ((i : ℝ) * (θm - θm)) - Real.cos ((i : ℝ) * (θm + θm))) / 2 := by
    intro i
    have := sineVec_mul θm θm i
    rw [← this]; ring
  rw [Finset.sum_congr rfl (fun i _ => hsq i), ← Finset.sum_div,
      Finset.sum_sub_distrib]
  have hzero : ∀ i ∈ range M, Real.cos ((i : ℝ) * (θm - θm)) = 1 := by
    intro i _; simp
  rw [Finset.sum_congr rfl hzero, Finset.sum_const]
  have hdouble : θm + θm = ((2 * m : ℕ) : ℝ) * π / (M : ℝ) := by
    rw [hθm, hMR]; push_cast; field_simp; ring
  rw [hdouble, sum_cos_eq (M := M) (q := 2 * m) hMpos (by omega) (by omega)]
  have hev : (-1 : ℝ) ^ (2 * m) = 1 := by
    rw [pow_mul]; norm_num
  rw [hev, hMR]
  simp

/-- **The DST-I orthogonality relation, packaged.**
`∑_i φ^{(m)}_i φ^{(n)}_i = ((N+1)/2)·δ_{mn}` for modes in `[1,N]`.

With `N` mutually orthogonal nonzero vectors in an `N`-dimensional space,
this establishes that the sine vectors form a **complete orthogonal
eigenbasis** of the discrete Dirichlet Laplacian — the spectral
decomposition the rest of the project relies on. -/
theorem sineVec_orthogonal_basis {N m n : ℕ}
    (hm : 1 ≤ m) (hmN : m ≤ N) (hn : 1 ≤ n) (hnN : n ≤ N) :
    ∑ i ∈ range (N + 1),
      sineVec ((m : ℝ) * π / ((N : ℝ) + 1)) i
        * sineVec ((n : ℝ) * π / ((N : ℝ) + 1)) i
      = if m = n then ((N : ℝ) + 1) / 2 else 0 := by
  by_cases h : m = n
  · subst h
    rw [if_pos rfl]
    calc ∑ i ∈ range (N + 1),
          sineVec ((m : ℝ) * π / ((N : ℝ) + 1)) i
            * sineVec ((m : ℝ) * π / ((N : ℝ) + 1)) i
        = ∑ i ∈ range (N + 1),
            (sineVec ((m : ℝ) * π / ((N : ℝ) + 1)) i) ^ 2 :=
          Finset.sum_congr rfl (fun i _ => by ring)
      _ = ((N : ℝ) + 1) / 2 := sineVec_norm_sq hm hmN
  · rw [if_neg h]
    exact sineVec_orthogonal hm hmN hn hnN h

end DiscreteSpectrum
