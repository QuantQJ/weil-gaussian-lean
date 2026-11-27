import Mathlib
import FibonacciCore

/-!
# φ-Spectral Compression: formalized claims

Formal support for US provisional 63/945,277 (φ-spectral compression).
Written 2026-08-01: the patent's mathematics had **no** formal backing
anywhere in the codebase; this module supplies it, targeting exactly the
claims that are (a) true and (b) independent of the empirical
"φ beats other decay rates" question — which the project's own multi-seed
ablation does NOT support (`results/ablation_multiseed.json`:
φ 0.9039 ± 0.0009 vs learned-geometric 0.9045 ± 0.0009, p = 0.166).

Proven here, no `sorry`, no custom axioms:

1. **Two-parameter determination** — a geometric spectrum `λ_k = λ₀ r^k`
   is fixed by any two entries. This is the real parameter-count claim
   (2 stored numbers, not K), and it holds for any ratio `r`.
2. **Spectral energy bound** — `Σ_{k<K} λ_k² ≤ λ₀²/(1 − r²)` for `|r| < 1`,
   with the exact infinite sum `∑' k, λ_k² = λ₀²/(1 − r²)`.
3. **Truncation error** — discarding components past `K` costs exactly
   `λ₀² r^{2K}/(1 − r²)`.
4. **The φ instantiation** — with `r = φ⁻¹`, `∑' λ_k² = λ₀² · φ`
   (via `φ² = φ + 1`).
5. **DCT-II orthogonality** — the un-normalized DCT-II rows
   `c_k(n) = cos(π(2n+1)k/(2N))` satisfy `Σ_n c_k(n)² = N` (k = 0) and
   `N/2` (0 < k < N), and distinct rows are orthogonal. This is exactly
   the `√(1/N)` / `√(2/N)` normalization in
   `phi-spectral-perceptron/src/constants.py::build_dct_basis`, i.e. the
   published code's `Q @ Qᵀ = I_K` claim, proven.
-/

noncomputable section
open Finset Real

namespace SpectralCompression

/-! ## Geometric spectra: the two-parameter claim -/

/-- A geometric spectrum `λ_k = λ₀ · r^k`; the φ-spectral eigenvalue law
is the case `r = φ⁻¹`. -/
def geoSpec (lam0 r : ℝ) (k : ℕ) : ℝ := lam0 * r ^ k

@[simp] lemma geoSpec_zero (lam0 r : ℝ) : geoSpec lam0 r 0 = lam0 := by
  simp [geoSpec]

@[simp] lemma geoSpec_one (lam0 r : ℝ) : geoSpec lam0 r 1 = lam0 * r := by
  simp [geoSpec]

/-- **Two-parameter determination.** Every entry is determined by `λ₀` and
`r` — the parameter-count claim behind the patent. -/
theorem geometric_spectrum_determined (lam0 r : ℝ) (k : ℕ) :
    geoSpec lam0 r k = geoSpec lam0 r 0 * r ^ k := by
  simp [geoSpec]

/-- **Uniqueness from two observations.** Two geometric spectra agreeing at
indices 0 and 1 (with `λ₀ ≠ 0`) agree everywhere: measuring any two
eigenvalues pins the whole spectrum. -/
theorem geometric_spectrum_unique_of_two
    {lam0 lam0' r r' : ℝ} (h0 : lam0 ≠ 0)
    (e0 : geoSpec lam0 r 0 = geoSpec lam0' r' 0)
    (e1 : geoSpec lam0 r 1 = geoSpec lam0' r' 1) :
    ∀ k, geoSpec lam0 r k = geoSpec lam0' r' k := by
  simp only [geoSpec_zero] at e0
  simp only [geoSpec_one] at e1
  subst e0
  have hr : r = r' := mul_left_cancel₀ h0 e1
  subst hr
  intro k
  rfl

/-! ## Energy bounds -/

lemma geoSpec_sq (lam0 r : ℝ) (k : ℕ) :
    (geoSpec lam0 r k) ^ 2 = lam0 ^ 2 * (r ^ 2) ^ k := by
  simp [geoSpec, mul_pow, ← pow_mul, mul_comm]

lemma sq_lt_one_of_abs_lt_one {r : ℝ} (hr : |r| < 1) : r ^ 2 < 1 := by
  have h := abs_lt.mp hr
  nlinarith [h.1, h.2]

lemma summable_geoSpec_sq (lam0 r : ℝ) (hr : |r| < 1) :
    Summable (fun k : ℕ => (geoSpec lam0 r k) ^ 2) := by
  have hr2 : r ^ 2 < 1 := sq_lt_one_of_abs_lt_one hr
  have : Summable (fun k : ℕ => lam0 ^ 2 * (r ^ 2) ^ k) :=
    (summable_geometric_of_lt_one (by positivity) hr2).mul_left _
  exact this.congr (fun k => (geoSpec_sq lam0 r k).symm)

/-- **Exact total spectral energy**: `∑' k, λ_k² = λ₀²/(1 − r²)`. -/
theorem spectral_energy_tsum (lam0 r : ℝ) (hr : |r| < 1) :
    ∑' k : ℕ, (geoSpec lam0 r k) ^ 2 = lam0 ^ 2 / (1 - r ^ 2) := by
  have hr2 : r ^ 2 < 1 := sq_lt_one_of_abs_lt_one hr
  rw [tsum_congr (geoSpec_sq lam0 r), tsum_mul_left,
      tsum_geometric_of_lt_one (by positivity) hr2]
  ring

/-- **Spectral energy bound.** For `|r| < 1` the retained energy never
exceeds `λ₀²/(1 − r²)`, uniformly in `K`. -/
theorem spectral_energy_bound (lam0 r : ℝ) (hr : |r| < 1) (K : ℕ) :
    ∑ k ∈ range K, (geoSpec lam0 r k) ^ 2 ≤ lam0 ^ 2 / (1 - r ^ 2) := by
  rw [← spectral_energy_tsum lam0 r hr]
  exact Summable.sum_le_tsum (range K) (fun k _ => sq_nonneg _) (summable_geoSpec_sq lam0 r hr)

/-- **Truncation error.** Discarding all components from index `K` on costs
exactly `λ₀² r^{2K}/(1 − r²)` — the compression error bound. -/
theorem spectral_tail_bound (lam0 r : ℝ) (hr : |r| < 1) (K : ℕ) :
    ∑' k : ℕ, (geoSpec lam0 r (k + K)) ^ 2
      = lam0 ^ 2 * (r ^ 2) ^ K / (1 - r ^ 2) := by
  have hr2 : r ^ 2 < 1 := sq_lt_one_of_abs_lt_one hr
  have hrw : ∀ k : ℕ, (geoSpec lam0 r (k + K)) ^ 2
      = (lam0 ^ 2 * (r ^ 2) ^ K) * (r ^ 2) ^ k := by
    intro k
    rw [geoSpec_sq, pow_add]
    ring
  rw [tsum_congr hrw, tsum_mul_left,
      tsum_geometric_of_lt_one (by positivity) hr2]
  ring

/-! ## The φ instantiation -/

open FibonacciCore

lemma phi_pos : 0 < phi := by
  unfold phi
  have := sqrt5_pos
  linarith

lemma one_lt_phi : 1 < phi := by
  unfold phi
  have := two_lt_sqrt5
  linarith

/-- `φ⁻¹ < 1`: the φ decay ratio satisfies the hypothesis of every bound
above. -/
theorem phi_inv_lt_one : |phi⁻¹| < 1 := by
  have h1 := one_lt_phi
  have h0 := phi_pos
  rw [abs_of_pos (by positivity)]
  rw [inv_lt_one_iff₀]
  right; exact h1

/-- The φ-spectrum's total energy is `λ₀² · φ`, using `φ² = φ + 1`. -/
theorem phi_spectrum_energy (lam0 : ℝ) :
    ∑' k : ℕ, (geoSpec lam0 phi⁻¹ k) ^ 2 = lam0 ^ 2 * phi := by
  rw [spectral_energy_tsum lam0 phi⁻¹ phi_inv_lt_one]
  have h0 : phi ≠ 0 := ne_of_gt phi_pos
  have hsq : phi ^ 2 = phi + 1 := phi_sq
  have hden : 1 - (phi⁻¹) ^ 2 = 1 / phi := by
    field_simp
    nlinarith [hsq]
  rw [hden]
  field_simp

/-! ## DCT-II orthogonality

The un-normalized DCT-II basis rows, matching `build_dct_basis` in
`phi-spectral-perceptron/src/constants.py`. -/

/-- Un-normalized DCT-II entry: `c_k(n) = cos(π(2n+1)k/(2N))`. -/
def dct (N k n : ℕ) : ℝ := Real.cos (π * (2 * n + 1) * k / (2 * N))

/-- **Telescoping Dirichlet sum**: `2 sin θ · Σ_{n<N} cos((2n+1)θ) = sin(2Nθ)`.
The identity that makes the DCT orthogonal. -/
theorem two_sin_mul_sum_cos (θ : ℝ) (N : ℕ) :
    2 * Real.sin θ * (∑ n ∈ range N, Real.cos ((2 * n + 1) * θ))
      = Real.sin (2 * N * θ) := by
  have step : ∀ n : ℕ,
      2 * Real.sin θ * Real.cos ((2 * n + 1) * θ)
        = Real.sin (2 * (n + 1) * θ) - Real.sin (2 * n * θ) := by
    intro n
    have h1 : Real.sin (2 * (n + 1) * θ) = Real.sin ((2 * n + 1) * θ + θ) := by
      ring_nf
    have h2 : Real.sin (2 * n * θ) = Real.sin ((2 * n + 1) * θ - θ) := by
      ring_nf
    rw [h1, h2, Real.sin_add, Real.sin_sub]
    ring
  rw [Finset.mul_sum]
  have hcong : ∀ n ∈ range N,
      2 * Real.sin θ * Real.cos ((2 * n + 1) * θ)
        = (fun m : ℕ => Real.sin (2 * m * θ)) (n + 1)
          - (fun m : ℕ => Real.sin (2 * m * θ)) n := by
    intro n _
    simp only []
    rw [step n]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl hcong, Finset.sum_range_sub
    (fun m : ℕ => Real.sin (2 * m * θ))]
  simp

/-- For `0 < k < 2N`, the DCT phase `θ = πk/(2N)` has `sin θ ≠ 0`. -/
lemma sin_dct_phase_ne_zero {N k : ℕ} (hN : 0 < N) (hk : 0 < k) (hk2 : k < 2 * N) :
    Real.sin (π * k / (2 * N)) ≠ 0 := by
  have hNR : (0 : ℝ) < 2 * N := by positivity
  have hpos : 0 < π * k / (2 * N) := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  have hlt : π * k / (2 * N) < π := by
    rw [div_lt_iff₀ hNR]
    have hkR : (k : ℝ) < 2 * N := by exact_mod_cast hk2
    nlinarith [pi_pos, hkR]
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hpos hlt)

/-- **Row sum of cosines vanishes**: for `0 < k < 2N`,
`Σ_{n<N} cos(π(2n+1)k/(2N)) = 0`. -/
theorem dct_sum_eq_zero {N k : ℕ} (hN : 0 < N) (hk : 0 < k) (hk2 : k < 2 * N) :
    ∑ n ∈ range N, Real.cos (π * (2 * n + 1) * k / (2 * N)) = 0 := by
  set θ : ℝ := π * k / (2 * N) with hθ
  have hsin : Real.sin θ ≠ 0 := sin_dct_phase_ne_zero hN hk hk2
  have hrw : ∀ n : ℕ, Real.cos (π * (2 * n + 1) * k / (2 * N))
      = Real.cos ((2 * n + 1) * θ) := by
    intro n; rw [hθ]; ring_nf
  rw [Finset.sum_congr rfl (fun n _ => hrw n)]
  have hkey := two_sin_mul_sum_cos θ N
  have hNθ : 2 * (N : ℝ) * θ = π * k := by
    rw [hθ]
    have : (2 : ℝ) * N ≠ 0 := by positivity
    field_simp
  rw [hNθ] at hkey
  have hzero : Real.sin (π * k) = 0 := by
    rw [mul_comm]
    exact Real.sin_nat_mul_pi k
  rw [hzero] at hkey
  have h2 : 2 * Real.sin θ ≠ 0 := by simpa using hsin
  exact (mul_eq_zero.mp hkey).resolve_left h2

/-- **DCT row square-sum** (the normalization constant). For `0 < k < N`,
`Σ_{n<N} c_k(n)² = N/2`; this is why `build_dct_basis` scales rows `k > 0`
by `√(2/N)`. -/
theorem dct_row_sq_sum {N k : ℕ} (hN : 0 < N) (hk : 0 < k) (hkN : k < N) :
    ∑ n ∈ range N, (dct N k n) ^ 2 = (N : ℝ) / 2 := by
  have hdouble : ∀ n : ℕ, (dct N k n) ^ 2
      = 1 / 2 + (1 / 2) * Real.cos (π * (2 * n + 1) * (2 * k) / (2 * N)) := by
    intro n
    unfold dct
    have h := Real.cos_sq (π * (2 * n + 1) * k / (2 * N))
    rw [h]
    congr 2
    ring
  have hzero := dct_sum_eq_zero (k := 2 * k) hN (by omega) (by omega)
  push_cast at hzero
  rw [Finset.sum_congr rfl (fun n _ => hdouble n), Finset.sum_add_distrib,
      Finset.sum_const, ← Finset.mul_sum, hzero]
  simp
  ring

/-- Row `0` has square-sum `N` — why `build_dct_basis` scales row 0 by
`√(1/N)` rather than `√(2/N)`. -/
theorem dct_row_zero_sq_sum {N : ℕ} :
    ∑ n ∈ range N, (dct N 0 n) ^ 2 = (N : ℝ) := by
  unfold dct
  simp

/-- Orthogonality for the ordered case `k < j`. -/
lemma dct_orthogonal_of_lt {N j k : ℕ} (hN : 0 < N)
    (hj : j < N) (hkj : k < j) :
    ∑ n ∈ range N, (dct N j n) * (dct N k n) = 0 := by
  have hprod : ∀ n : ℕ, (dct N j n) * (dct N k n)
      = (1 / 2) * Real.cos (π * (2 * n + 1) * ((j - k : ℕ)) / (2 * N))
        + (1 / 2) * Real.cos (π * (2 * n + 1) * ((j + k : ℕ)) / (2 * N)) := by
    intro n
    set A : ℝ := π * (2 * n + 1) * j / (2 * N) with hA
    set B : ℝ := π * (2 * n + 1) * k / (2 * N) with hB
    have hsub := Real.cos_sub A B
    have hadd := Real.cos_add A B
    have hcast : ((j - k : ℕ) : ℝ) = (j : ℝ) - (k : ℝ) := by
      have : k ≤ j := le_of_lt hkj
      push_cast [Nat.cast_sub this]
      ring
    have e1 : π * (2 * n + 1) * ((j - k : ℕ)) / (2 * N) = A - B := by
      rw [hcast, hA, hB]; ring
    have e2 : π * (2 * n + 1) * ((j + k : ℕ)) / (2 * N) = A + B := by
      push_cast; rw [hA, hB]; ring
    rw [e1, e2, hsub, hadd]
    unfold dct
    rw [← hA, ← hB]
    ring
  rw [Finset.sum_congr rfl (fun n _ => hprod n), Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum,
      dct_sum_eq_zero (k := j - k) hN (by omega) (by omega),
      dct_sum_eq_zero (k := j + k) hN (by omega) (by omega)]
  ring

/-- **Distinct DCT rows are orthogonal**: for `j ≠ k` in `[0, N)`,
`Σ_n c_j(n) c_k(n) = 0`. Together with the row square-sums this is exactly
the `Q @ Qᵀ = I_K` property claimed in `build_dct_basis`. -/
theorem dct_rows_orthogonal {N j k : ℕ} (hN : 0 < N)
    (hj : j < N) (hk : k < N) (hjk : j ≠ k) :
    ∑ n ∈ range N, (dct N j n) * (dct N k n) = 0 := by
  rcases lt_or_gt_of_ne hjk with h | h
  · have := dct_orthogonal_of_lt (N := N) (j := k) (k := j) hN hk h
    rw [← this]
    exact Finset.sum_congr rfl (fun n _ => mul_comm _ _)
  · exact dct_orthogonal_of_lt hN hj h

end SpectralCompression
