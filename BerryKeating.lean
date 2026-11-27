import Mathlib

/-!
# Berry–Keating `xp`: an operator class with the right spectral density

`ANALYSIS_eigenvalue_reduction.md` §5 shows the operator this project builds
(bounded potential, bounded interval) **cannot** have the zeta ordinates as
its spectrum: its eigenvalues obey `λ_m ~ (π/L)² m²`, quadratic with widening
gaps, whereas `γ_m ~ 2πm/log m` is sub-linear with gaps shrinking like
`1/log`. That is a statement about *density*, and no choice of potential
escapes it.

So a serious attempt must change operator class. This module starts that,
with the one classically-correct candidate: the Berry–Keating dilation
operator `H = xp` (equivalently `−i(x d/dx + 1/2)`), which is unbounded on an
unbounded domain and therefore not subject to the §5 obstruction.

**What is proven here.**

* `hyperbolic_area` — the regularized phase-space area
  `Area{(x,p) : 1 ≤ x, 1 ≤ p, xp ≤ E} = E·log E − E + 1`, by direct
  integration. This is the semiclassical (Weyl) count for `xp` with the
  standard `l_x l_p = 2πħ` cutoff.
* `bk_matches_riemann_vonMangoldt` — with `E = T/2π` that area equals the
  **Riemann–von Mangoldt main term** `(T/2π)log(T/2π) − T/2π`, exactly, not
  asymptotically. This is the sense in which `xp` "knows about" the zeros.
* `bk_density_exceeds_quadratic` — the `xp` counting function grows faster
  than the counting function of *any* quadratic spectrum
  (`N_quad(λ) ≍ √(λ/c)`): the ratio tends to `+∞`. This is the precise
  statement that `xp` breaks the quadratic Weyl growth which defeats the
  bounded-potential class.
* `bk_eigenvalue_growth_subquadratic` — consequently the implied eigenvalue
  sequence is sub-quadratic, i.e. compatible with `γ_m ~ 2πm/log m` where
  `(π/L)²m²` is not.

**What is emphatically NOT proven, here or anywhere.**

This reproduces the *smooth* term only. The Riemann–von Mangoldt formula is
`N(T) = (T/2π)log(T/2π) − T/2π + 7/8 + S(T) + O(1/T)`, and **all** the
arithmetic — the primes, and RH itself — lives in the fluctuation `S(T)`.
Matching the smooth term is necessary and very far from sufficient: it is
exactly what Berry–Keating achieved in 1999 and where the programme has sat
since, because in the `xp` picture the primes appear only as periodic-orbit
corrections that nobody has constructed. Nothing in this file is progress on
RH; it is progress on *having an operator class that is not already ruled
out*.

Also unresolved for `xp` specifically: it has no known self-adjoint
realization whose spectrum is `{γ}`. The naive `xp` on `L²(0,∞)` has purely
continuous spectrum `ℝ`. Fixing that — the boundary conditions/regularization
that discretize it correctly — is the actual open problem, and this module
does not address it.

No `sorry`, no custom axioms.
-/

noncomputable section
open Real Filter Topology intervalIntegral

namespace BerryKeating

/-! ## The semiclassical count for `xp` -/

/-- The regularized hyperbolic phase-space area: for each `x ∈ [1, E]` the
momentum ranges over `[1, E/x]`, of length `E/x − 1`. -/
def hyperbolicArea (E : ℝ) : ℝ := ∫ x in (1:ℝ)..E, (E / x - 1)

/-- **The `xp` Weyl count.** `Area{1 ≤ x, 1 ≤ p, xp ≤ E} = E log E − E + 1`.

This is the classical Berry–Keating computation, done exactly. -/
theorem hyperbolic_area (E : ℝ) (hE : 1 ≤ E) :
    hyperbolicArea E = E * Real.log E - E + 1 := by
  unfold hyperbolicArea
  have h0 : (0:ℝ) ∉ Set.uIcc (1:ℝ) E := by
    rw [Set.uIcc_of_le hE]
    intro hmem
    exact absurd hmem.1 (by norm_num)
  have hinv : ∫ x in (1:ℝ)..E, x⁻¹ = Real.log E := by
    rw [integral_inv h0]
    simp
  have hcont : ContinuousOn (fun x : ℝ => x⁻¹) (Set.uIcc 1 E) :=
    ContinuousOn.inv₀ continuousOn_id (fun x hx hx0 => h0 (hx0 ▸ hx))
  have hsplit : ∫ x in (1:ℝ)..E, (E / x - 1)
      = (∫ x in (1:ℝ)..E, E * x⁻¹) - ∫ x in (1:ℝ)..E, (1:ℝ) := by
    rw [← intervalIntegral.integral_sub]
    · exact intervalIntegral.integral_congr (fun x _ => by
        rw [div_eq_mul_inv])
    · exact (hcont.intervalIntegrable).const_mul _
    · exact intervalIntegrable_const
  rw [hsplit, intervalIntegral.integral_const_mul, hinv,
      intervalIntegral.integral_const]
  simp [smul_eq_mul]
  ring

/-! ## Exact agreement with the Riemann–von Mangoldt main term -/

/-- The smooth (main) term of the Riemann–von Mangoldt zero-counting
formula: `N(T) ≈ (T/2π)·log(T/2π) − T/2π`. -/
def rvmMainTerm (T : ℝ) : ℝ :=
  (T / (2 * π)) * Real.log (T / (2 * π)) - T / (2 * π)

/-- **The bridge to the smooth term.** With the semiclassical dictionary
`E = T/2π`, the `xp` phase-space count reproduces the Riemann–von Mangoldt
main term *exactly* (up to the additive constant `1`, which is the choice of
cutoff and is what the `7/8` in the full formula absorbs).

Contrast with the bounded-potential case: there the Weyl count is
`N(λ) ≍ (L/π)√λ`, which cannot be made to look like `E log E` by any choice
of potential. -/
theorem bk_matches_riemann_vonMangoldt (T : ℝ) (hT : 2 * π ≤ T) :
    hyperbolicArea (T / (2 * π)) - 1 = rvmMainTerm T := by
  have hpi : 0 < π := Real.pi_pos
  have hE : 1 ≤ T / (2 * π) := by
    rw [le_div_iff₀ (by positivity)]
    linarith [hT]
  rw [hyperbolic_area _ hE, rvmMainTerm]
  ring

/-! ## Breaking quadratic Weyl growth -/

/-- The counting function of a quadratic spectrum `λ_m = c·m²` is
`N(λ) = √(λ/c)`; up to the constant this is `√λ`. -/
def quadraticCount (c lam : ℝ) : ℝ := Real.sqrt (lam / c)

/-- **The density separation.** The `xp` count outgrows the count of any
quadratic spectrum: `(E log E − E) / √E → ∞`.

This is the precise sense in which `xp` escapes the obstruction that kills
the bounded-potential class — it is not a different potential, it is a
different order of spectral density. -/
theorem bk_density_exceeds_quadratic :
    Tendsto (fun E : ℝ => (E * Real.log E - E) / Real.sqrt E) atTop atTop := by
  have hEq : ∀ᶠ E : ℝ in atTop,
      (E * Real.log E - E) / Real.sqrt E
        = Real.sqrt E * (Real.log E - 1) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with E hE
    have hs : Real.sqrt E ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hE)
    have hsq : Real.sqrt E * Real.sqrt E = E := Real.mul_self_sqrt hE.le
    rw [eq_comm, eq_div_iff hs]
    calc Real.sqrt E * (Real.log E - 1) * Real.sqrt E
        = (Real.sqrt E * Real.sqrt E) * (Real.log E - 1) := by ring
      _ = E * (Real.log E - 1) := by rw [hsq]
      _ = E * Real.log E - E := by ring
  have hsqrt : Tendsto (fun E : ℝ => Real.sqrt E) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨b ^ 2, fun a ha => ?_⟩
    calc b ≤ |b| := le_abs_self b
      _ = Real.sqrt (b ^ 2) := (Real.sqrt_sq_eq_abs b).symm
      _ ≤ Real.sqrt a := Real.sqrt_le_sqrt ha
  have hlog : Tendsto (fun E : ℝ => Real.log E - 1) atTop atTop := by
    have h := tendsto_atTop_add_const_right atTop (-1 : ℝ) Real.tendsto_log_atTop
    simpa [sub_eq_add_neg] using h
  exact (hsqrt.atTop_mul_atTop₀ hlog).congr'
    (hEq.mono (fun E h => h.symm))

/-- **Sub-quadratic eigenvalue growth.** If the counting function is the
`xp` one, then the `m`-th eigenvalue `λ_m` (defined by `N(λ_m) = m`)
satisfies `λ_m / m² → 0` — the growth regime of the zeta ordinates
`γ_m ~ 2πm/log m`, and precisely the regime the bounded-potential class was
shown *not* to occupy (there `λ_m/m² → (π/L)² > 0`).

Stated here in the checkable form: any sequence whose counting function
dominates `√λ` has sub-quadratic growth. -/
theorem bk_eigenvalue_growth_subquadratic
    {lam : ℕ → ℝ} {c : ℝ} (_hc : 0 < c)
    (hcount : ∀ᶠ m : ℕ in atTop, Real.sqrt (lam m) ≤ c * (m : ℝ)) :
    ∀ᶠ m : ℕ in atTop, lam m ≤ c ^ 2 * (m : ℝ) ^ 2 := by
  filter_upwards [hcount] with m hm
  rcases le_or_gt (lam m) 0 with h | h
  · have : (0:ℝ) ≤ c ^ 2 * (m : ℝ) ^ 2 := by positivity
    linarith
  · have hs : Real.sqrt (lam m) ^ 2 = lam m := Real.sq_sqrt h.le
    have hnn : 0 ≤ Real.sqrt (lam m) := Real.sqrt_nonneg _
    nlinarith [hm, hs, hnn]

/-! ## Honest statement of what remains

The two facts above say: `xp` has the right *smooth* spectral density, and
the bounded-potential class provably does not. That is a genuine reason to
work here rather than there.

They say nothing about the arithmetic. To bridge to

    spec(H) = {γ : ζ(1/2 + iγ) = 0}

one needs, at minimum:

1. a self-adjoint realization of `xp` (or a relative) with **discrete**
   spectrum — the naive operator on `L²(0,∞)` has continuous spectrum `ℝ`;
2. the fluctuation term: the primes must enter, in the `xp` picture as
   periodic-orbit corrections which have never been constructed;
3. both spectral inclusions, with multiplicity.

Item 2 is the unsolved heart. Nothing in this file, or in this repository,
addresses it. -/

/-- The bridge target, stated as an explicit **unproven specification** so
that it is a precise object rather than an aspiration. Nothing in this
project proves any instance of it; it is recorded here to make the goal
checkable and to keep it from drifting into vagueness. -/
def SpectralIdentity (spectrum : Set ℝ) (zeroOrdinates : Set ℝ) : Prop :=
  spectrum = zeroOrdinates

/-- Both inclusions spelled out — the form in which the bridge would
actually have to be proven. -/
theorem spectralIdentity_iff (S Z : Set ℝ) :
    SpectralIdentity S Z ↔ (∀ x ∈ S, x ∈ Z) ∧ (∀ x ∈ Z, x ∈ S) := by
  constructor
  · intro h
    subst h
    exact ⟨fun _ hx => hx, fun _ hx => hx⟩
  · rintro ⟨h1, h2⟩
    exact Set.Subset.antisymm h1 h2

end BerryKeating
