/-
Copyright (c) 2026 James C. Kerr. All rights reserved.
-/
import Mathlib

/-!
# DCT-II orthogonality (self-contained)

Formal support for US provisional 63/945,277.

The statement proved here is the orthogonality of the un-normalized DCT-II
kernel, with the half-shift on the **sample** index `m` (NOT on the frequency
indices `j`, `k`):

  `∑_{m=0}^{N-1} cos(π (m + 1/2) j / N) * cos(π (m + 1/2) k / N)`
      `= N`      if `j = k = 0`
      `= N / 2`  if `j = k`, `0 < j < N`
      `= 0`      if `j ≠ k`, `j, k < N`

Note `π (m + 1/2) j / N = π (2m+1) j / (2N)`, so this is the same convention
as `SpectralCompression.dct` (`SpectralCompression.lean:164`), with the
frequency index written first.

The variant with the half-shift on `j` and `k` instead,
`∑_m cos(π (j+1/2) m / N) cos(π (k+1/2) m / N)`, is FALSE off-diagonal and is
deliberately not stated here.

This file depends on Mathlib only; it does not import any other module of this
repository, so the `#print axioms` receipt at the bottom is self-contained.
-/

noncomputable section
open Finset Real

namespace DCTOrthogonality

/-- Un-normalized DCT-II kernel, frequency index `j`, sample index `m`,
block length `N`: `cos(π (m + 1/2) j / N)`. -/
def dctK (N j m : ℕ) : ℝ := Real.cos (π * ((m : ℝ) + 1 / 2) * j / N)

/-- The half-integer form equals the usual `(2m+1)/(2N)` form. -/
lemma dctK_eq (N j m : ℕ) :
    dctK N j m = Real.cos (π * (2 * (m : ℝ) + 1) * j / (2 * N)) := by
  unfold dctK
  congr 1
  ring

/-! ## The telescoping identity -/

/-- **Telescoping Dirichlet sum**: `2 sin θ · Σ_{m<N} cos((2m+1)θ) = sin(2Nθ)`. -/
theorem two_sin_mul_sum_cos_odd (θ : ℝ) (N : ℕ) :
    2 * Real.sin θ * (∑ m ∈ range N, Real.cos ((2 * (m : ℝ) + 1) * θ))
      = Real.sin (2 * N * θ) := by
  have step : ∀ m : ℕ,
      2 * Real.sin θ * Real.cos ((2 * (m : ℝ) + 1) * θ)
        = Real.sin (2 * ((m : ℝ) + 1) * θ) - Real.sin (2 * (m : ℝ) * θ) := by
    intro m
    have h1 : Real.sin (2 * ((m : ℝ) + 1) * θ)
        = Real.sin ((2 * (m : ℝ) + 1) * θ + θ) := by ring_nf
    have h2 : Real.sin (2 * (m : ℝ) * θ)
        = Real.sin ((2 * (m : ℝ) + 1) * θ - θ) := by ring_nf
    rw [h1, h2, Real.sin_add, Real.sin_sub]
    ring
  rw [Finset.mul_sum]
  have hcong : ∀ m ∈ range N,
      2 * Real.sin θ * Real.cos ((2 * (m : ℝ) + 1) * θ)
        = (fun i : ℕ => Real.sin (2 * (i : ℝ) * θ)) (m + 1)
          - (fun i : ℕ => Real.sin (2 * (i : ℝ) * θ)) m := by
    intro m _
    simp only []
    rw [step m]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl hcong,
    Finset.sum_range_sub (fun i : ℕ => Real.sin (2 * (i : ℝ) * θ))]
  simp

/-! ## The vanishing row sum -/

/-- For `0 < k < 2N` the phase `πk/(2N)` lies strictly inside `(0, π)`. -/
lemma sin_phase_ne_zero {N k : ℕ} (hk : 0 < k) (hk2 : k < 2 * N) :
    Real.sin (π * k / (2 * N)) ≠ 0 := by
  have hN : 0 < N := by omega
  have hNR : (0 : ℝ) < 2 * N := by
    have : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
    linarith
  have hkR0 : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hpos : 0 < π * k / (2 * N) := by
    apply div_pos _ hNR
    have := pi_pos
    positivity
  have hlt : π * k / (2 * N) < π := by
    rw [div_lt_iff₀ hNR]
    have hkR : (k : ℝ) < 2 * N := by exact_mod_cast hk2
    nlinarith [pi_pos, hkR]
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hpos hlt)

/-- **Vanishing row sum**: for `0 < k < 2N`,
`Σ_{m<N} cos(π(2m+1)k/(2N)) = 0`. -/
theorem sum_cos_odd_eq_zero {N k : ℕ} (hk : 0 < k) (hk2 : k < 2 * N) :
    ∑ m ∈ range N, Real.cos (π * (2 * (m : ℝ) + 1) * k / (2 * N)) = 0 := by
  have hN : 0 < N := by omega
  have hNR : (0 : ℝ) < 2 * N := by
    have : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
    linarith
  set θ : ℝ := π * k / (2 * N) with hθ
  have hsin : Real.sin θ ≠ 0 := sin_phase_ne_zero hk hk2
  have hrw : ∀ m : ℕ, Real.cos (π * (2 * (m : ℝ) + 1) * k / (2 * N))
      = Real.cos ((2 * (m : ℝ) + 1) * θ) := by
    intro m; rw [hθ]; ring_nf
  rw [Finset.sum_congr rfl (fun m _ => hrw m)]
  have hkey := two_sin_mul_sum_cos_odd θ N
  have hNθ : 2 * (N : ℝ) * θ = π * k := by
    rw [hθ]
    field_simp
  rw [hNθ] at hkey
  have hzero : Real.sin (π * k) = 0 := by
    rw [mul_comm]; exact Real.sin_nat_mul_pi k
  rw [hzero] at hkey
  have h2 : 2 * Real.sin θ ≠ 0 := by simpa using hsin
  exact (mul_eq_zero.mp hkey).resolve_left h2

/-! ## Diagonal entries -/

/-- Row `j = 0`: the square-sum is `N`. -/
theorem dctK_diag_zero (N : ℕ) :
    ∑ m ∈ range N, dctK N 0 m * dctK N 0 m = (N : ℝ) := by
  unfold dctK
  simp

/-- Row `0 < j < N`: the square-sum is `N/2`. -/
theorem dctK_diag_pos {N j : ℕ} (hj : 0 < j) (hjN : j < N) :
    ∑ m ∈ range N, dctK N j m * dctK N j m = (N : ℝ) / 2 := by
  have hdouble : ∀ m : ℕ, dctK N j m * dctK N j m
      = 1 / 2 + (1 / 2) * Real.cos (π * (2 * (m : ℝ) + 1) * ((2 * j : ℕ) : ℝ) / (2 * N)) := by
    intro m
    have h := Real.cos_sq (π * (2 * (m : ℝ) + 1) * j / (2 * N))
    rw [dctK_eq, ← sq, h]
    have harg : 2 * (π * (2 * (m : ℝ) + 1) * j / (2 * N))
        = π * (2 * (m : ℝ) + 1) * ((2 * j : ℕ) : ℝ) / (2 * N) := by
      push_cast
      ring
    rw [harg]
    ring
  have hzero := sum_cos_odd_eq_zero (N := N) (k := 2 * j) (by omega) (by omega)
  rw [Finset.sum_congr rfl (fun m _ => hdouble m), Finset.sum_add_distrib,
      Finset.sum_const, ← Finset.mul_sum, hzero]
  simp
  ring

/-! ## Off-diagonal entries -/

/-- Orthogonality for the ordered case `k < j < N`. -/
lemma dctK_offdiag_of_lt {N j k : ℕ} (hj : j < N) (hkj : k < j) :
    ∑ m ∈ range N, dctK N j m * dctK N k m = 0 := by
  have hprod : ∀ m : ℕ, dctK N j m * dctK N k m
      = (1 / 2) * Real.cos (π * (2 * (m : ℝ) + 1) * ((j - k : ℕ) : ℝ) / (2 * N))
        + (1 / 2) * Real.cos (π * (2 * (m : ℝ) + 1) * ((j + k : ℕ) : ℝ) / (2 * N)) := by
    intro m
    set A : ℝ := π * (2 * (m : ℝ) + 1) * j / (2 * N) with hA
    set B : ℝ := π * (2 * (m : ℝ) + 1) * k / (2 * N) with hB
    have hcast : ((j - k : ℕ) : ℝ) = (j : ℝ) - (k : ℝ) := by
      have hle : k ≤ j := le_of_lt hkj
      push_cast [Nat.cast_sub hle]
      ring
    have e1 : π * (2 * (m : ℝ) + 1) * ((j - k : ℕ) : ℝ) / (2 * N) = A - B := by
      rw [hcast, hA, hB]; ring
    have e2 : π * (2 * (m : ℝ) + 1) * ((j + k : ℕ) : ℝ) / (2 * N) = A + B := by
      push_cast; rw [hA, hB]; ring
    rw [e1, e2, Real.cos_sub, Real.cos_add]
    simp only [dctK_eq, ← hA, ← hB]
    ring
  rw [Finset.sum_congr rfl (fun m _ => hprod m), Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum,
      sum_cos_odd_eq_zero (N := N) (k := j - k) (by omega) (by omega),
      sum_cos_odd_eq_zero (N := N) (k := j + k) (by omega) (by omega)]
  ring

/-- **Distinct DCT-II rows are orthogonal**: for `j ≠ k`, both `< N`. -/
theorem dctK_rows_orthogonal {N j k : ℕ} (hj : j < N) (hk : k < N) (hjk : j ≠ k) :
    ∑ m ∈ range N, dctK N j m * dctK N k m = 0 := by
  rcases lt_or_gt_of_ne hjk with h | h
  · have hsym := dctK_offdiag_of_lt (N := N) (j := k) (k := j) hk h
    rw [← hsym]
    exact Finset.sum_congr rfl (fun m _ => mul_comm _ _)
  · exact dctK_offdiag_of_lt hj h

/-! ## The combined statement -/

/-- **DCT-II orthogonality, all cases.** For `j, k < N`:
`Σ_{m<N} cos(π(m+1/2)j/N) cos(π(m+1/2)k/N)` is `N` when `j = k = 0`,
`N/2` when `j = k ≠ 0`, and `0` when `j ≠ k`. -/
theorem dctII_orthogonality {N j k : ℕ} (hj : j < N) (hk : k < N) :
    ∑ m ∈ range N, dctK N j m * dctK N k m
      = if j = k then (if j = 0 then (N : ℝ) else (N : ℝ) / 2) else 0 := by
  by_cases hjk : j = k
  · subst hjk
    by_cases hj0 : j = 0
    · subst hj0
      simp [dctK_diag_zero]
    · simp only [if_pos rfl, if_neg hj0]
      exact dctK_diag_pos (Nat.pos_of_ne_zero hj0) hj
  · rw [if_neg hjk]
    exact dctK_rows_orthogonal hj hk hjk

/-- Same statement with the kernel written out, no local definition. -/
theorem dctII_orthogonality_explicit {N j k : ℕ} (hj : j < N) (hk : k < N) :
    ∑ m ∈ range N,
        Real.cos (π * ((m : ℝ) + 1 / 2) * j / N)
          * Real.cos (π * ((m : ℝ) + 1 / 2) * k / N)
      = if j = k then (if j = 0 then (N : ℝ) else (N : ℝ) / 2) else 0 :=
  dctII_orthogonality hj hk

end DCTOrthogonality

/-! ## Kernel axiom receipt -/

section Receipt
open DCTOrthogonality
#print axioms DCTOrthogonality.two_sin_mul_sum_cos_odd
#print axioms DCTOrthogonality.sum_cos_odd_eq_zero
#print axioms DCTOrthogonality.dctK_diag_zero
#print axioms DCTOrthogonality.dctK_diag_pos
#print axioms DCTOrthogonality.dctK_rows_orthogonal
#print axioms DCTOrthogonality.dctII_orthogonality
#print axioms DCTOrthogonality.dctII_orthogonality_explicit
end Receipt
