import Mathlib

/-!
# Residue of the logarithmic derivative at a zero of finite order

This file proves a general fact of one-variable complex analysis, needed to
identify the residues of `ζ'/ζ` at the zeros of `ζ`:

* `LogDerivResidue.tendsto_sub_mul_logDeriv` — if `g` is analytic at `p` with
  `g p ≠ 0`, and `f z = (z - p) ^ m * g z` on a neighbourhood of `p`, then
  `(z - p) * (deriv f z / f z) → m` as `z → p`, `z ≠ p`.  In other words the
  logarithmic derivative `f'/f` has a simple pole at `p` with residue `m`
  (the order of the zero).
* `LogDerivResidue.tendsto_sub_mul_logDeriv_simple_zero` — the `m = 1` case.
* Auxiliary: `LogDerivResidue.deriv_eq_of_eventually_eq_pow_mul` (explicit
  formula for `deriv f` on a neighbourhood of `p`) and
  `LogDerivResidue.continuousAt_deriv_of_analyticAt`.

Everything is fully proven with no additional axioms.  Nothing about `ζ` is
stated here; the connection to `ζ'/ζ` (that `ζ` factors as `(z-ρ)^m g` near a
zero `ρ`) is left to the file that consumes this one.
-/

noncomputable section

open Filter Topology

namespace LogDerivResidue

/-- The derivative of an analytic function is continuous at the point
(analyticity propagates to the derivative on a neighbourhood). -/
theorem continuousAt_deriv_of_analyticAt {g : ℂ → ℂ} {p : ℂ} (hg : AnalyticAt ℂ g p) :
    ContinuousAt (deriv g) p := by
  obtain ⟨s, hs, hgs⟩ := hg.exists_mem_nhds_analyticOnNhd
  exact (hgs.deriv p (mem_of_mem_nhds hs)).continuousAt

/-- If `f z = (z - p) ^ m * g z` near `p` and `g` is analytic at `p`, then near `p`
the derivative of `f` is given by the product rule:
`deriv f z = m * (z - p) ^ (m - 1) * g z + (z - p) ^ m * deriv g z`. -/
theorem deriv_eq_of_eventually_eq_pow_mul {f g : ℂ → ℂ} {p : ℂ} (hg : AnalyticAt ℂ g p)
    (m : ℕ) (hf : ∀ᶠ z in 𝓝 p, f z = (z - p) ^ m * g z) :
    ∀ᶠ z in 𝓝 p,
      deriv f z = (m : ℂ) * (z - p) ^ (m - 1) * g z + (z - p) ^ m * deriv g z := by
  filter_upwards [hf.eventually_nhds, hg.eventually_analyticAt] with z hfz hgz
  have hpow : HasDerivAt (fun w : ℂ => (w - p) ^ m) ((m : ℂ) * (z - p) ^ (m - 1) * 1) z :=
    ((hasDerivAt_id' z).sub_const p).pow m
  have hprod : HasDerivAt (fun w : ℂ => (w - p) ^ m * g w)
      ((m : ℂ) * (z - p) ^ (m - 1) * 1 * g z + (z - p) ^ m * deriv g z) z :=
    hpow.mul hgz.differentiableAt.hasDerivAt
  have hderiv : deriv f z = deriv (fun w : ℂ => (w - p) ^ m * g w) z :=
    Filter.EventuallyEq.deriv_eq hfz
  rw [hderiv, hprod.deriv]
  ring

/-- **Residue of the logarithmic derivative at a zero of order `m`.**
If `g` is analytic at `p`, `g p ≠ 0`, and `f z = (z - p) ^ m * g z` on a
neighbourhood of `p`, then `(z - p) * (f' z / f z) → m` as `z → p` through
`z ≠ p`.  Thus `f'/f` has a simple pole at `p` with residue `m`. -/
theorem tendsto_sub_mul_logDeriv {f g : ℂ → ℂ} {p : ℂ} (hg : AnalyticAt ℂ g p)
    (hg0 : g p ≠ 0) (m : ℕ) (hf : ∀ᶠ z in 𝓝 p, f z = (z - p) ^ m * g z) :
    Tendsto (fun z => (z - p) * (deriv f z / f z)) (𝓝[≠] p) (𝓝 (m : ℂ)) := by
  -- the "regular part" `(z - p) * (g' z / g z)` tends to `0`
  have hreg : Tendsto (fun z => (m : ℂ) + (z - p) * (deriv g z / g z)) (𝓝 p) (𝓝 (m : ℂ)) := by
    have h1 : Tendsto (fun z : ℂ => z - p) (𝓝 p) (𝓝 (p - p)) :=
      tendsto_id.sub_const p
    have h2 : Tendsto (fun z => deriv g z / g z) (𝓝 p) (𝓝 (deriv g p / g p)) :=
      (continuousAt_deriv_of_analyticAt hg).tendsto.div hg.continuousAt.tendsto hg0
    have h3 := (h1.mul h2).const_add (m : ℂ)
    simpa using h3
  -- on a punctured neighbourhood the two expressions agree
  have hg_ne : ∀ᶠ z in 𝓝 p, g z ≠ 0 := hg.continuousAt.eventually_ne hg0
  have hderiv := deriv_eq_of_eventually_eq_pow_mul hg m hf
  have heq : (fun z => (m : ℂ) + (z - p) * (deriv g z / g z))
      =ᶠ[𝓝[≠] p] (fun z => (z - p) * (deriv f z / f z)) := by
    have hall : ∀ᶠ z in 𝓝 p, f z = (z - p) ^ m * g z ∧ g z ≠ 0 ∧
        deriv f z = (m : ℂ) * (z - p) ^ (m - 1) * g z + (z - p) ^ m * deriv g z :=
      hf.and (hg_ne.and hderiv)
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hall,
      self_mem_nhdsWithin] with z ⟨hfz, hgz, hdz⟩ hzp
    have hzp' : z - p ≠ 0 := sub_ne_zero.mpr hzp
    rw [hfz, hdz]
    rcases m with _ | k
    · simp
    · have hk : (k + 1 : ℕ) - 1 = k := by omega
      rw [hk]
      push_cast
      field_simp
      ring
  exact (tendsto_nhdsWithin_of_tendsto_nhds hreg).congr' heq

/-- **Simple zero.** If `g` is analytic at `p`, `g p ≠ 0`, and `f z = (z - p) * g z`
near `p`, then `(z - p) * (f' z / f z) → 1` as `z → p`, `z ≠ p`:
the logarithmic derivative has residue `1` at a simple zero. -/
theorem tendsto_sub_mul_logDeriv_simple_zero {f g : ℂ → ℂ} {p : ℂ} (hg : AnalyticAt ℂ g p)
    (hg0 : g p ≠ 0) (hf : ∀ᶠ z in 𝓝 p, f z = (z - p) * g z) :
    Tendsto (fun z => (z - p) * (deriv f z / f z)) (𝓝[≠] p) (𝓝 (1 : ℂ)) := by
  have hf1 : ∀ᶠ z in 𝓝 p, f z = (z - p) ^ 1 * g z := by
    filter_upwards [hf] with z hz
    simpa using hz
  simpa using tendsto_sub_mul_logDeriv hg hg0 1 hf1

end LogDerivResidue

end
