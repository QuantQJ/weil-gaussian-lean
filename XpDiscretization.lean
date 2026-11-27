import BerryKeating
import Mathlib

/-!
# The `xp` discretization problem: what a correct compactification must do

`BerryKeating.lean` establishes that the `xp` phase-space count reproduces
the Riemann–von Mangoldt main term exactly, so `xp` has the right spectral
*density*. But the naive operator has no discrete spectrum at all, so
"`spec(H) = {γ}`" is not yet even a well-posed question. This module attacks
that prerequisite.

## Why `xp` has continuous spectrum

`dilation_log_identity` proves the classical substitution: writing
`f(x) = x^{-1/2} g(log x)`, the symmetrized dilation generator satisfies

    x·f'(x) + f(x)/2 = x^{-1/2} · g'(log x)

i.e. under `u = log x` the operator `xp = −i(x d/dx + 1/2)` becomes exactly
`−i d/du`, the **momentum operator on the whole line**. Momentum on `ℝ` is
self-adjoint with purely continuous spectrum `ℝ` and no eigenvalues. That is
the precise reason `xp` fails to be a Hilbert–Pólya operator as it stands:
not a technicality, a unitary equivalence.

## What the obvious repair does — and why it is wrong

The natural fix is to compactify: restrict `u` to an interval of length `ℓ`
with periodic boundary conditions, turning `−i d/du` into the momentum
operator on a circle, which *is* self-adjoint with discrete spectrum
`λ_n = 2πn/ℓ`. That is the standard construction and it does give
discreteness.

But `fixed_length_compactification_fails` proves it gives the **wrong
density**: equally-spaced eigenvalues have a counting function linear in `E`,
`N(E) ≍ ℓE/π`, whereas the target is `E log E − E`. The ratio diverges. So
*no* choice of `ℓ`, and more generally no energy-independent compactification
producing an equally-spaced spectrum, can reproduce the Riemann–von Mangoldt
density.

## What that forces

The obstruction is quantitative and it points somewhere specific: to get
`E log E` the effective number of available modes must grow **logarithmically
with the energy**. In the Berry–Keating phase-space picture this is exactly
what the cutoff `l_x l_p = 2πħ` does — the region `{x ≥ l_x, p ≥ l_p, xp ≤ E}`
corresponds in the `u = log x` variable to an interval of length
`log E − log(l_x l_p)`, which grows like `log E` rather than staying fixed
(`effective_length_grows`). An honest discretization of `xp` must reproduce
that energy-dependent effective domain, which is precisely why a boundary
condition on a fixed interval cannot do it.

**Status.** This narrows the search and rules out the naive route; it does
not exhibit the correct operator. Nothing here is progress on RH, and the
arithmetic (the fluctuation `S(T)`, where the primes live) remains entirely
untouched.

No `sorry`, no custom axioms.
-/

noncomputable section
open Real Filter Topology

namespace XpDiscretization

/-! ## `xp` is the momentum operator in disguise -/

/-- **The logarithmic substitution.** If `f(x) = x^{-1/2}·g(log x)` and `g`
is differentiable at `log x`, then the symmetrized dilation generator acts as
`x·f'(x) + f(x)/2 = x^{-1/2}·g'(log x)`.

So `xp` is unitarily equivalent to `−i d/du` on `L²(ℝ)` — momentum on the
line, whose spectrum is all of `ℝ` and purely continuous. This is the exact
reason the naive `xp` has no eigenvalues to compare with `{γ}`. -/
theorem dilation_hasDerivAt {g : ℝ → ℝ} {gx' x : ℝ} (hx : 0 < x)
    (hgd : HasDerivAt g gx' (Real.log x)) :
    HasDerivAt (fun y => (Real.sqrt y)⁻¹ * g (Real.log y))
      ((-(1 / (2 * Real.sqrt x)) / (Real.sqrt x) ^ 2) * g (Real.log x)
        + (Real.sqrt x)⁻¹ * (gx' * x⁻¹)) x := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hsqne : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx)
  exact ((Real.hasDerivAt_sqrt hxne).inv hsqne).mul
    (hgd.comp x (Real.hasDerivAt_log hxne))

/-- The algebraic half: applying `x·(d/dx) + 1/2` to that derivative
collapses everything except `g'`. -/
theorem dilation_log_identity {g : ℝ → ℝ} {gx' x : ℝ} (hx : 0 < x) :
    x * ((-(1 / (2 * Real.sqrt x)) / (Real.sqrt x) ^ 2) * g (Real.log x)
          + (Real.sqrt x)⁻¹ * (gx' * x⁻¹))
        + ((Real.sqrt x)⁻¹ * g (Real.log x)) / 2
      = (Real.sqrt x)⁻¹ * gx' := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hsqne : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx)
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  rw [hsq]
  field_simp
  ring

/-! ## The counting functions -/

/-- Counting function of an equally-spaced spectrum `λ_n = 2πn/ℓ`, `n ∈ ℤ`,
i.e. momentum on a circle of circumference `ℓ`: `#{n : |λ_n| ≤ E} ≍ ℓE/π`. -/
def circleCount (l E : ℝ) : ℝ := l * E / π

/-- The Berry–Keating / Riemann–von Mangoldt target count. -/
def targetCount (E : ℝ) : ℝ := E * Real.log E - E

/-- **No fixed-length compactification works.** For every circumference
`ℓ > 0`, the target count outgrows the circle count without bound:

    (E log E − E) / (ℓE/π) → ∞.

Equally-spaced spectra are linear in `E`; the zeta density is `E log E`.
So discretizing `xp` by putting `u = log x` on a fixed interval — the obvious
route to self-adjointness with discrete spectrum — necessarily gives the
wrong asymptotics, for any interval length. -/
theorem fixed_length_compactification_fails (l : ℝ) (hl : 0 < l) :
    Tendsto (fun E : ℝ => targetCount E / circleCount l E) atTop atTop := by
  have hpi : 0 < π := Real.pi_pos
  have hEq : ∀ᶠ E : ℝ in atTop,
      targetCount E / circleCount l E = (π / l) * (Real.log E - 1) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with E hE
    unfold targetCount circleCount
    have hEne : E ≠ 0 := ne_of_gt hE
    have hlne : l ≠ 0 := ne_of_gt hl
    have hpine : π ≠ 0 := ne_of_gt hpi
    field_simp
  have hlog : Tendsto (fun E : ℝ => Real.log E - 1) atTop atTop := by
    have h := tendsto_atTop_add_const_right atTop (-1 : ℝ) Real.tendsto_log_atTop
    simpa [sub_eq_add_neg] using h
  have hscaled : Tendsto (fun E : ℝ => (π / l) * (Real.log E - 1)) atTop atTop :=
    hlog.const_mul_atTop (by positivity)
  exact hscaled.congr' (hEq.mono (fun E h => h.symm))

/-- Restated as a non-existence: no circumference reproduces the target
density even up to a bounded factor. -/
theorem no_circumference_matches_density (l : ℝ) (hl : 0 < l) :
    ¬ ∃ C : ℝ, ∀ᶠ E : ℝ in atTop, targetCount E ≤ C * circleCount l E := by
  rintro ⟨C, hC⟩
  have hpi : 0 < π := Real.pi_pos
  have hdiv := fixed_length_compactification_fails l hl
  have hev := hdiv.eventually_gt_atTop C
  obtain ⟨E, ⟨hgt, hle⟩, hEpos⟩ :=
    ((hev.and hC).and (eventually_gt_atTop (0:ℝ))).exists
  have hcirc : 0 < circleCount l E := by
    unfold circleCount
    exact div_pos (mul_pos hl hEpos) hpi
  have hratio : targetCount E / circleCount l E ≤ C := by
    rw [div_le_iff₀ hcirc]
    linarith [hle]
  linarith [hgt, hratio]

/-! ## What the correct construction must satisfy -/

/-- The Berry–Keating effective domain. Under `u = log x`, the phase-space
region `{x ≥ l_x, p ≥ l_p, xp ≤ E}` is an interval in `u` of length
`log E − log(l_x·l_p)`. -/
def effectiveLength (lxlp E : ℝ) : ℝ := Real.log E - Real.log lxlp

/-- **The design constraint.** The effective domain length grows without
bound, like `log E` — it is *not* a fixed interval. This is the structural
difference between the Berry–Keating regularization and a boundary condition,
and it is what produces `E log E` instead of a linear count. Any honest
discretization of `xp` has to reproduce this energy-dependence. -/
theorem effective_length_grows (lxlp : ℝ) (_hlxlp : 0 < lxlp) :
    Tendsto (fun E : ℝ => effectiveLength lxlp E) atTop atTop := by
  unfold effectiveLength
  have h := tendsto_atTop_add_const_right atTop (-(Real.log lxlp)) Real.tendsto_log_atTop
  simpa [sub_eq_add_neg] using h

/-- Sanity check tying the two together: with the effective length in hand,
the mode count at energy `E` — spacing `2π/ℓ(E)` over a momentum range of
size `≍ E` — is `≍ E·log E`, matching `targetCount`, whereas a fixed `ℓ`
gives `≍ E`. The content is `effective_length_grows` plus
`fixed_length_compactification_fails`; this records the conclusion. -/
theorem density_requires_growing_domain :
    (∀ l : ℝ, 0 < l →
      Tendsto (fun E : ℝ => targetCount E / circleCount l E) atTop atTop)
    ∧ (∀ lxlp : ℝ, 0 < lxlp →
      Tendsto (fun E : ℝ => effectiveLength lxlp E) atTop atTop) :=
  ⟨fixed_length_compactification_fails, effective_length_grows⟩

end XpDiscretization
