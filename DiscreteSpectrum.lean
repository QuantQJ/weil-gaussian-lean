import Mathlib

/-!
# Exact spectrum of the discrete Dirichlet Laplacian (the solvable backbone)

The kinetic operator `T` of the HP construction (the tridiagonal second-difference
matrix, `kinetic` in `HPProof.lean`) is exactly solvable. With Dirichlet boundary
conditions on `(0, L)` discretized at `N` interior points, spacing `h = L/(N+1)`,
its eigenpairs are, in closed form,

    eigenvector   φ^{(m)}_i = sin( m π i / (N+1) ),    i = 0,…,N+1
    eigenvalue    μ_m       = (2/h²)(1 − cos θ_m)
                            = (4/h²) sin²(θ_m / 2),    θ_m = m π / (N+1).

This file proves that eigen-relation, its closed form, and the Dirichlet boundary
vanishing — fully, with **no `sorry`**. This is the honest "solvable operator
whose spectrum is known exactly" that the project can legitimately own. It is the
unperturbed backbone of `H_N = T + D_V`; the perturbation `D_V` is finite-band
(bandwidth 6), and the connection to the Riemann zeros is a *numerical fit of the
smooth (Weyl) density*, NOT a theorem — see `ANALYSIS_eigenvalue_reduction.md`.
-/

noncomputable section
open Real

namespace DiscreteSpectrum

/-- Core sum-to-product identity: `sin(a+θ) + sin(a−θ) = 2 sin a cos θ`.
    This single identity is the entire reason the discrete Laplacian is solvable. -/
theorem sin_add_add_sin_sub (a θ : ℝ) :
    Real.sin (a + θ) + Real.sin (a - θ) = 2 * Real.sin a * Real.cos θ := by
  rw [Real.sin_add, Real.sin_sub]; ring

/-- The Dirichlet eigenvector entries `φ_i = sin(i θ)`. -/
def sineVec (θ : ℝ) (i : ℕ) : ℝ := Real.sin ((i : ℝ) * θ)

/-- The closed-form eigenvalue `μ = (2/h²)(1 − cos θ)`. -/
def laplEigenvalue (h θ : ℝ) : ℝ := (2 / (h * h)) * (1 - Real.cos θ)

/-- **Second-difference (discrete Laplacian) eigen-relation:**
    `φ_{i+2} − 2 φ_{i+1} + φ_i = −2(1 − cos θ) φ_{i+1}`.
    The three-term recurrence collapses to one trig identity. -/
theorem second_difference_sineVec (θ : ℝ) (i : ℕ) :
    sineVec θ (i + 2) - 2 * sineVec θ (i + 1) + sineVec θ i
      = -2 * (1 - Real.cos θ) * sineVec θ (i + 1) := by
  unfold sineVec
  have e2 : ((i + 2 : ℕ) : ℝ) * θ = ((i + 1 : ℕ) : ℝ) * θ + θ := by push_cast; ring
  have e0 : ((i : ℕ) : ℝ) * θ = ((i + 1 : ℕ) : ℝ) * θ - θ := by push_cast; ring
  rw [e2, e0, Real.sin_add, Real.sin_sub]; ring

/-- **Eigenvalue equation for the kinetic operator** `−Δ_h φ = μ φ`:
    `−(φ_{i+2} − 2 φ_{i+1} + φ_i)/h² = μ φ_{i+1}` with `μ = (2/h²)(1 − cos θ)`. -/
theorem discrete_laplacian_eigen (h θ : ℝ) (i : ℕ) :
    -(sineVec θ (i + 2) - 2 * sineVec θ (i + 1) + sineVec θ i) / (h * h)
      = laplEigenvalue h θ * sineVec θ (i + 1) := by
  rw [second_difference_sineVec]; unfold laplEigenvalue; ring

/-- **Closed form** `μ = (4/h²) sin²(θ/2)` (half-angle). -/
theorem eigenvalue_half_angle (h θ : ℝ) :
    laplEigenvalue h θ = (4 / (h * h)) * Real.sin (θ / 2) ^ 2 := by
  unfold laplEigenvalue
  have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h2 := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h2
    have hp := Real.sin_sq_add_cos_sq (θ / 2)
    linarith [h2, hp]
  rw [hcos]; ring

/-- Left Dirichlet boundary: `φ_0 = 0`. -/
theorem sineVec_left (θ : ℝ) : sineVec θ 0 = 0 := by
  unfold sineVec; simp

/-- Right Dirichlet boundary: with `θ_m = mπ/(N+1)`, `φ_{N+1} = sin(mπ) = 0`. -/
theorem sineVec_dirichlet_right (N m : ℕ) :
    sineVec ((m : ℝ) * π / ((N : ℝ) + 1)) (N + 1) = 0 := by
  unfold sineVec
  have hN : ((N : ℝ) + 1) ≠ 0 := by positivity
  have key : ((N + 1 : ℕ) : ℝ) * ((m : ℝ) * π / ((N : ℝ) + 1)) = (m : ℝ) * π := by
    push_cast; field_simp
  rw [key]; exact Real.sin_nat_mul_pi m

/-- **Discrete Dirichlet Laplacian spectrum (full statement).**
    For `θ_m = mπ/(N+1)`, the sine vector `φ_i = sin(i θ_m)`:
    1. solves the kinetic eigenvalue equation with `μ_m = (2/h²)(1 − cos θ_m)`,
    2. whose closed form is `(4/h²) sin²(θ_m/2)`,
    3. and vanishes at both Dirichlet endpoints `i = 0` and `i = N+1`.
    Machine-checked, no `sorry`. -/
theorem dirichlet_laplacian_spectrum (h : ℝ) (N m : ℕ) :
    (∀ i : ℕ,
      -(sineVec ((m : ℝ) * π / ((N : ℝ) + 1)) (i + 2)
        - 2 * sineVec ((m : ℝ) * π / ((N : ℝ) + 1)) (i + 1)
        + sineVec ((m : ℝ) * π / ((N : ℝ) + 1)) i) / (h * h)
        = laplEigenvalue h ((m : ℝ) * π / ((N : ℝ) + 1))
            * sineVec ((m : ℝ) * π / ((N : ℝ) + 1)) (i + 1))
    ∧ laplEigenvalue h ((m : ℝ) * π / ((N : ℝ) + 1))
        = (4 / (h * h)) * Real.sin (((m : ℝ) * π / ((N : ℝ) + 1)) / 2) ^ 2
    ∧ sineVec ((m : ℝ) * π / ((N : ℝ) + 1)) 0 = 0
    ∧ sineVec ((m : ℝ) * π / ((N : ℝ) + 1)) (N + 1) = 0 := by
  refine ⟨fun i => discrete_laplacian_eigen h _ i,
          eigenvalue_half_angle h _, sineVec_left _, sineVec_dirichlet_right N m⟩

/-- **Positivity (T is positive-definite):** every eigenvalue is strictly
    positive for 1 ≤ m ≤ N. Because θ_m/2 = mπ/(2(N+1)) ∈ (0, π), sin(θ_m/2) > 0,
    so μ_m = (4/h²) sin²(θ_m/2) > 0. -/
theorem eigenvalue_pos (h : ℝ) (hh : h ≠ 0) {N m : ℕ} (hm : 1 ≤ m) (hN : m ≤ N) :
    0 < laplEigenvalue h ((m : ℝ) * π / ((N : ℝ) + 1)) := by
  rw [eigenvalue_half_angle]
  have hhh : (0 : ℝ) < h * h := mul_self_pos.mpr hh
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmN : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpi := Real.pi_pos
  have harg_pos : 0 < (m : ℝ) * π / ((N : ℝ) + 1) / 2 :=
    div_pos (div_pos (mul_pos hmpos hpi) hNpos) (by norm_num)
  have harg_lt : (m : ℝ) * π / ((N : ℝ) + 1) / 2 < π := by
    rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 2), div_lt_iff₀ hNpos]
    nlinarith [hpi, hmN, hNpos]
  have hsin_pos : 0 < Real.sin ((m : ℝ) * π / ((N : ℝ) + 1) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi harg_pos harg_lt
  have hcoef : (0 : ℝ) < 4 / (h * h) := div_pos (by norm_num) hhh
  exact mul_pos hcoef (pow_pos hsin_pos 2)

/-- **Simple spectrum (strict monotonicity):** the eigenvalues are strictly
    increasing in m for m₁ < m₂ ≤ N. Hence the N eigenvalues μ_1,…,μ_N are
    distinct — the discrete Dirichlet Laplacian is non-degenerate. -/
theorem eigenvalue_strictMono (h : ℝ) (hh : h ≠ 0) {N m₁ m₂ : ℕ}
    (hlt : m₁ < m₂) (hN : m₂ ≤ N) :
    laplEigenvalue h ((m₁ : ℝ) * π / ((N : ℝ) + 1))
      < laplEigenvalue h ((m₂ : ℝ) * π / ((N : ℝ) + 1)) := by
  rw [eigenvalue_half_angle, eigenvalue_half_angle]
  have hhh : (0 : ℝ) < h * h := mul_self_pos.mpr hh
  have hcoef : (0 : ℝ) < 4 / (h * h) := div_pos (by norm_num) hhh
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hpi := Real.pi_pos
  have hm12 : (m₁ : ℝ) < (m₂ : ℝ) := by exact_mod_cast hlt
  have hmN : (m₂ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have ha₁_nonneg : 0 ≤ (m₁ : ℝ) * π / ((N : ℝ) + 1) / 2 := by positivity
  have hlt_a : (m₁ : ℝ) * π / ((N : ℝ) + 1) / 2 < (m₂ : ℝ) * π / ((N : ℝ) + 1) / 2 := by
    gcongr
  have ha₂_le : (m₂ : ℝ) * π / ((N : ℝ) + 1) / 2 ≤ π / 2 := by
    have hx : (m₂ : ℝ) * π / ((N : ℝ) + 1) ≤ π := by
      rw [div_le_iff₀ hNpos]; nlinarith [hpi, hmN]
    linarith [hx]
  have ha₁_le : (m₁ : ℝ) * π / ((N : ℝ) + 1) / 2 ≤ π / 2 := le_of_lt (lt_of_lt_of_le hlt_a ha₂_le)
  have hsin : Real.sin ((m₁ : ℝ) * π / ((N : ℝ) + 1) / 2)
      < Real.sin ((m₂ : ℝ) * π / ((N : ℝ) + 1) / 2) :=
    Real.strictMonoOn_sin ⟨by linarith [hpi], ha₁_le⟩ ⟨by linarith [hpi], ha₂_le⟩ hlt_a
  have hsin₁_nonneg : 0 ≤ Real.sin ((m₁ : ℝ) * π / ((N : ℝ) + 1) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi ha₁_nonneg (by linarith [hpi, ha₁_le])
  have hsq : Real.sin ((m₁ : ℝ) * π / ((N : ℝ) + 1) / 2) ^ 2
      < Real.sin ((m₂ : ℝ) * π / ((N : ℝ) + 1) / 2) ^ 2 := by
    nlinarith [hsin, hsin₁_nonneg]
  exact mul_lt_mul_of_pos_left hsq hcoef

end DiscreteSpectrum
