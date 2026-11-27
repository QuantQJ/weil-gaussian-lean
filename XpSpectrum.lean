import BerryKeating
import XpDiscretization
import Mathlib

/-!
# Quantizing the `xp` area: a spectrum with the zeta growth envelope

The previous modules established the negative half: `xp` has continuous
spectrum, and no fixed-length compactification gives the right density
because equally-spaced eigenvalues count linearly while the target counts
like `E log E`.

This module does the constructive half. Rather than a boundary condition, we
impose the **Bohr–Sommerfeld quantization condition** on the Berry–Keating
phase-space area itself:

    A(λ_n) = 2πn,    A(E) = E·log E − E + 1

which is the semiclassical rule "one state per `2πħ` of phase-space area".
Because `A` is strictly increasing (proven), this determines the `λ_n`
uniquely, and by construction the counting function is `A(E)/2π` — the
Riemann–von Mangoldt density, exactly.

The main theorem `quantization_growth_envelope` shows the resulting spectrum
sits in the growth envelope of the zeta ordinates:

    2πn / log(2πn)  ≤  λ_n  ≤  2πn

Compare `γ_n ~ 2πn / log n`. This is the same regime, and it is precisely
the regime the bounded-potential class was proven *not* to occupy (there
`λ_m ≍ (π/L)²m²`).

## What this settles, and what it does not

It settles that **spectral density is not the obstruction.** A discrete
spectrum with the Riemann–von Mangoldt counting function and the correct
growth envelope exists and is easy to write down. Anyone who produces an
operator matching the smooth term — as this project's original cosine
potential did to `R² = 0.9995` — has matched something cheap.

It does not produce the zeros. `λ_n` here is defined by a smooth
quantization rule; the actual ordinates deviate from it by the fluctuation
`S(T)`, which is `Ω(log T / log log T)` infinitely often and encodes the
primes. Nothing in this module, or this repository, touches `S(T)`.

The honest conclusion of the whole `xp` line: the easy half of Hilbert–Pólya
(get the density right) is genuinely easy, and the hard half (get the
arithmetic right) is untouched by any of it.

No `sorry`, no custom axioms.
-/

noncomputable section
open Real Filter Topology Set

namespace XpSpectrum

/-- The Berry–Keating quantization function — the closed form of the
regularized hyperbolic phase-space area (`BerryKeating.hyperbolic_area`). -/
def A (E : ℝ) : ℝ := E * Real.log E - E + 1

lemma A_eq_area (E : ℝ) (hE : 1 ≤ E) : A E = BerryKeating.hyperbolicArea E := by
  rw [BerryKeating.hyperbolic_area E hE, A]

/-! ## `A` is strictly increasing, so the quantization condition is well posed -/

/-- `A'(E) = log E`. -/
theorem A_hasDerivAt {E : ℝ} (hE : 0 < E) :
    HasDerivAt A (Real.log E) E := by
  have hEne : E ≠ 0 := ne_of_gt hE
  have hlog : HasDerivAt Real.log E⁻¹ E := Real.hasDerivAt_log hEne
  have hmul : HasDerivAt (fun y : ℝ => y * Real.log y)
      (1 * Real.log E + E * E⁻¹) E :=
    (hasDerivAt_id E).mul hlog
  have hsub : HasDerivAt (fun y : ℝ => y * Real.log y - y)
      (1 * Real.log E + E * E⁻¹ - 1) E :=
    hmul.sub (hasDerivAt_id E)
  have hfin : HasDerivAt A (1 * Real.log E + E * E⁻¹ - 1) E := hsub.add_const 1
  have hval : 1 * Real.log E + E * E⁻¹ - 1 = Real.log E := by
    rw [mul_inv_cancel₀ hEne]; ring
  rwa [hval] at hfin

/-- **`A` is strictly increasing on `[1, ∞)`.** Hence the quantization
condition `A(λ) = 2πn` has at most one solution, and the eigenvalue sequence
it defines is unambiguous. -/
theorem A_strictMonoOn : StrictMonoOn A (Ici 1) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 1)
    (f' := fun E => Real.log E)
  · -- continuity on [1, ∞)
    intro x hx
    exact (A_hasDerivAt (lt_of_lt_of_le zero_lt_one hx)).continuousAt.continuousWithinAt
  · -- derivative within
    intro x hx
    exact (A_hasDerivAt (lt_of_lt_of_le zero_lt_one (interior_subset hx))).hasDerivWithinAt
  · -- positivity on the interior
    intro x hx
    rw [interior_Ici] at hx
    exact Real.log_pos hx

/-! ## The growth envelope -/

/-- Upper bound: past `e²` the area dominates its argument, `A(E) ≥ E`. -/
lemma le_A {E : ℝ} (hE : Real.exp 2 ≤ E) : E ≤ A E := by
  have hEpos : 0 < E := lt_of_lt_of_le (Real.exp_pos 2) hE
  have hlog : 2 ≤ Real.log E := by
    rw [← Real.log_exp 2]
    exact Real.log_le_log (Real.exp_pos 2) hE
  unfold A
  nlinarith [hEpos, hlog]

/-- Lower bound on the area: `A(E) ≤ E·log E` for `E ≥ 1`. -/
lemma A_le {E : ℝ} (hE : 1 ≤ E) : A E ≤ E * Real.log E := by
  unfold A
  linarith [hE]

/-- **THE GROWTH ENVELOPE.** If `λ` satisfies the Bohr–Sommerfeld condition
`A(λ) = 2πn` (with `λ ≥ e²`), then

    2πn / log(2πn)  ≤  λ  ≤  2πn.

This is exactly the growth regime of the Riemann ordinates
`γ_n ~ 2πn/log n`, and it is the regime the bounded-potential class was
proven not to occupy. -/
theorem quantization_growth_envelope {lam : ℝ} {n : ℕ}
    (hlam : Real.exp 2 ≤ lam) (hq : A lam = 2 * π * n) :
    lam ≤ 2 * π * n ∧ 2 * π * n / Real.log (2 * π * n) ≤ lam := by
  have hlampos : 0 < lam := lt_of_lt_of_le (Real.exp_pos 2) hlam
  have hlam1 : (1:ℝ) ≤ lam := le_trans (by
    have := Real.add_one_le_exp (2:ℝ)
    linarith) hlam
  -- upper bound
  have hupper : lam ≤ 2 * π * n := by
    have := le_A hlam
    linarith [hq]
  refine ⟨hupper, ?_⟩
  -- lower bound
  have hloglam : 0 < Real.log lam := Real.log_pos (by
    have := Real.add_one_le_exp (2:ℝ)
    nlinarith [hlam])
  have hAle : A lam ≤ lam * Real.log lam := A_le hlam1
  have hmono : Real.log lam ≤ Real.log (2 * π * n) :=
    Real.log_le_log hlampos hupper
  have hkey : 2 * π * n ≤ lam * Real.log (2 * π * n) := by
    calc 2 * π * n = A lam := hq.symm
      _ ≤ lam * Real.log lam := hAle
      _ ≤ lam * Real.log (2 * π * n) :=
          mul_le_mul_of_nonneg_left hmono hlampos.le
  have hlogpos : 0 < Real.log (2 * π * n) := lt_of_lt_of_le hloglam hmono
  rw [div_le_iff₀ hlogpos]
  linarith [hkey]

/-- Consequence: the quantized spectrum is **sub-quadratic**, unlike the
bounded-potential spectrum `λ_m ≍ (π/L)²m²`. -/
theorem quantized_subquadratic {lam : ℕ → ℝ}
    (hq : ∀ n : ℕ, Real.exp 2 ≤ lam n → A (lam n) = 2 * π * n)
    (hbig : ∀ n : ℕ, Real.exp 2 ≤ lam n) :
    ∀ n : ℕ, lam n ≤ 2 * π * n :=
  fun n => ((quantization_growth_envelope (hbig n) (hq n (hbig n))).1)

/-! ## The honest scorecard

`quantization_growth_envelope` gives a discrete spectrum with

* the Riemann–von Mangoldt counting function (by construction: `N = A/2π`),
* the correct growth envelope `2πn/log(2πn) ≤ λ_n ≤ 2πn`.

and it took one monotone function and two inequalities. That is the point:
**matching the smooth spectral density is cheap.** The original motivation
for this repository — a cosine potential whose eigenvalues fit 100 zeros at
`R² = 0.9995` — was matching this same cheap quantity, which is why the fit
did not extend.

What separates `λ_n` above from `γ_n` is the fluctuation `S(T)`: unbounded
(`Ω(√(log T / log log T))` infinitely often, Montgomery), GUE-distributed
under RH (Montgomery–Dyson), and carrying every prime. No construction in
this repository produces it, and no known construction does. -/

end XpSpectrum
