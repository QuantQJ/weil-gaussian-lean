import Mathlib

/-!
# Boundary triples: eigenvalues under a symmetric boundary condition are real

Built on Mathlib's partially defined operators `H →ₗ.[ℂ] H` and their adjoint `T†`
(`Mathlib/Analysis/InnerProductSpace/LinearPMap.lean`); no new unbounded-operator layer.
Mathlib's inner product is conjugate-linear in the first argument.

`im_eigenvalue_zero_of_boundaryTriple` : if `T† f = z • f`, `f ≠ 0`, and the boundary form
`⟪Γ₁ f, Γ₀ f⟫` is real, then `z` is real. Only Green's identity is used; no spectral theorem.
This says nothing about which operator has the zeta zeros as eigenvalues.
-/

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ComplexConjugate
open LinearPMap

namespace BoundaryTripleReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A boundary triple `(G, Γ₀, Γ₁)` for `T`: boundary maps on the domain of `T†` satisfying
Green's identity, jointly surjective onto `G × G`. -/
structure BoundaryTriple (T : H →ₗ.[ℂ] H) (G : Type*) [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] where
  Γ₀ : T†.domain →ₗ[ℂ] G
  Γ₁ : T†.domain →ₗ[ℂ] G
  surjective_pair : Function.Surjective (fun u => (Γ₀ u, Γ₁ u))
  green_identity : ∀ u v : T†.domain,
    ⟪T† u, (v : H)⟫_ℂ - ⟪(u : H), T† v⟫_ℂ = ⟪Γ₁ u, Γ₀ v⟫_ℂ - ⟪Γ₀ u, Γ₁ v⟫_ℂ

variable {T : H →ₗ.[ℂ] H} {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- Green's identity at `u = v = f` for an eigenvector: `Im z · ‖f‖² = -Im ⟪Γ₁ f, Γ₀ f⟫`. -/
theorem im_eigenvalue_mul_normSq (BT : BoundaryTriple T G) {z : ℂ} {f : T†.domain}
    (hf_ker : T† f = z • (f : H)) :
    z.im * ‖(f : H)‖ ^ 2 = -(⟪BT.Γ₁ f, BT.Γ₀ f⟫_ℂ).im := by
  have g := BT.green_identity f f
  rw [hf_ker, inner_smul_left, inner_smul_right] at g
  have gi := congrArg Complex.im g
  have hsym : (⟪BT.Γ₀ f, BT.Γ₁ f⟫_ℂ).im = -(⟪BT.Γ₁ f, BT.Γ₀ f⟫_ℂ).im := by
    have e := inner_conj_symm (𝕜 := ℂ) (BT.Γ₀ f) (BT.Γ₁ f)
    rw [← e, Complex.conj_im]
  have h1 : (⟪(f : H), (f : H)⟫_ℂ).im = 0 := inner_self_im (𝕜 := ℂ) (f : H)
  have h2 : (⟪(f : H), (f : H)⟫_ℂ).re = ‖(f : H)‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (f : H)
  simp only [Complex.sub_im, Complex.mul_im, Complex.conj_re, Complex.conj_im, h1, h2] at gi
  linarith

/-- **Eigenvalues under a symmetric boundary condition are real.** -/
theorem im_eigenvalue_zero_of_boundaryTriple (BT : BoundaryTriple T G) {z : ℂ}
    {f : T†.domain} (hf_ne : (f : H) ≠ 0) (hf_ker : T† f = z • (f : H))
    (h_symm : (⟪BT.Γ₁ f, BT.Γ₀ f⟫_ℂ).im = 0) : z.im = 0 := by
  have h := im_eigenvalue_mul_normSq BT hf_ker
  rw [h_symm, neg_zero] at h
  have hn : ‖(f : H)‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hf_ne)
  exact (mul_eq_zero.mp h).resolve_right hn

/-- The usual way to meet `h_symm`: a boundary condition `Γ₁ f = c • Γ₀ f` with `c` real. -/
theorem boundary_form_real_of_real_condition (BT : BoundaryTriple T G) {f : T†.domain} {c : ℝ}
    (hc : BT.Γ₁ f = (c : ℂ) • BT.Γ₀ f) : (⟪BT.Γ₁ f, BT.Γ₀ f⟫_ℂ).im = 0 := by
  rw [hc, inner_smul_left]
  have h1 : (⟪BT.Γ₀ f, BT.Γ₀ f⟫_ℂ).im = 0 := inner_self_im (𝕜 := ℂ) (BT.Γ₀ f)
  simp [Complex.mul_im, ← Complex.ofReal_pow]

end BoundaryTripleReal
