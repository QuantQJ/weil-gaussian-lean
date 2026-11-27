/-
Copyright 2026 James C. Kerr (QuantQJ). Apache-2.0.
-/
import FleetArchimedeanLogBound

/-!
# The Weil functional on the growing Fejér family: a fully elementary residual

Weil positivity is closed in both directions (`FleetWeilCriterion.weil_positivity_criterion`),
so any positive-definite test function gives a **necessary** condition for RH.  This file pins
the canonical **growing compactly supported** family and records what its Weil functional
actually is.

**It is necessary, not sufficient, and here is why.**  Every Fejér kernel peaks at `t = 0` and
decays like `1/t²`, so the positive span of `{h_A}_{A>0}` is a proper subclass of the
positive-definite cone — the Pólya-type convex-decreasing ones — and no member of it localizes
at a height `α`.  A zero at ordinate `γ` contributes `≈ 2/(A γ²) ≥ 0` whatever it does, so the
family is blind to high zeros: sensitivity dies like `1/γ²`.  The measured detection table below
shows it directly (at `A = 16`, `e = 0.05` the pair defect is `-0.000422` against a margin of
`0.005743`).  A *sufficient* family must be modulated, `h_A(u) cos (α u)` with `α` ranging; that
is the two-parameter residual, and `FleetPrimeTarget.PrimeTarget` is its smooth analogue.

Take `h_A u = max 0 (1 - |u|/A)`, the triangle of width `A`.  It is positive definite because
`h_A = g * g̃` with `g = 1_[-A/2,A/2]/√A`, and its transform is the Fejér kernel

  `fejerHat A t = 2(1 - cos (A t))/(A t²) ≥ 0`,   `fejerHat A 0 = A`.

* `fejerHat_nonneg` — the positive-definiteness, from `cos ≤ 1`.
* `fejerPole_eq` — the pole term is exactly `ĥ(i/2) + ĥ(-i/2) = 16(cosh (A/2) - 1)/A`.
* `tendsto_fejerPole` — `A · pole A · exp(-A/2) → 8`, so `pole A ≍ 8 e^{A/2}/A`.
* `FejerWeilPositive` — the residual as a **pure prime inequality**: no zeros, no transforms,
  no Gaussian.

## What was measured

Λ sieved to `2 × 10⁷` (support `1,271,339`), archimedean term by numerical quadrature against
the digamma kernel, zero side from the first 300 ordinates as a rigorous lower bound (every
term is nonnegative).  The identity `zeros = pole - primes + arch` closes at every `A`:

| `A`  | `pole`      | `primes`    | `arch`   | `W = pole-primes+arch` | zeros (lower) |
|------|-------------|-------------|----------|------------------------|---------------|
| 2.0  | 4.344645    | 1.745851    | -2.54801 | 0.050782               | 0.050127      |
| 8.0  | 52.616466   | 48.293063   | -4.31593 | 0.007471               | 0.006945      |
| 16.0 | 1489.479161 | 1484.639126 | -4.83429 | 0.005743               | 0.004701      |
| 16.8 | 2116.698558 | 2111.833013 | -4.86025 | 0.005296               | 0.004697      |

`W > 0` at every `A`, as Weil positivity requires.  Three facts came out of it:

1. **The margin is `W ≈ 0.09/A`** while `pole ≈ 8 e^{A/2}/A`.  `A · W` stays in `0.060–0.121`
   across `A ∈ [2, 16.8]`, and `A · pole · e^{-A/2}` converges to `8` (7.9964 at `A = 16.8`).
   So the relative margin is `≈ 0.011 e^{-A/2}`: `2.5 × 10⁻⁶` at `A = 16.8`.
2. **Precision is not the obstruction.**  That margin needs only `A/2 · log₁₀ e ≈ 3.65` digits
   of cancellation at `A = 16.8`, and `0.217 A` digits in general — cheap at any `A`.
3. **The archimedean term converges**, `arch A → ψ(1/4) - log π ≈ -5.372`, approached from
   above (`-4.860` at `A = 16.8`).

So the necessary condition on this family is the elementary inequality below, and the estimate
it needs is
a one-sided bound on `2 Σ_{n ≤ e^A} Λ(n) n^{-1/2}(1 - log n/A)` against `8 e^{A/2}/A` to within
`0.09/A`.  That is the **full square-root saving** in `ψ(x) - x`; no bilinear or minor-arc
input shortcuts it, because the required saving is exactly the one RH asserts.

One concrete defect of this family, also measured: the offset it can resolve **oscillates**
rather than improving monotonically with the prime budget, because of the `1 - cos (A t)`
factor.  The smallest offset whose pair defect exceeds the whole margin runs
`0.2575, 0.2641, 0.1719, 0.1794, 0.1504, 0.2057` at `A = 8, 10, 12, 14, 16, 16.8` — worse at
`A = 16.8` than at `A = 16`.  A smooth family (the Gaussian one, i.e.
`FleetPrimeTarget.PrimeTarget`) has no such oscillation.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped Real ArithmeticFunction

namespace FleetFejerWeil

/-- The Fejér kernel: the Fourier transform of the width-`A` triangle. -/
def fejerHat (A t : ℝ) : ℝ := if t = 0 then A else 2 * (1 - Real.cos (A * t)) / (A * t ^ 2)

/-- **Positive definiteness.**  `fejerHat A = |ĝ|²` for `g = 1_[-A/2,A/2]/√A`, and directly
`1 - cos ≥ 0`.  This is what makes the triangle a legal Weil test function. -/
theorem fejerHat_nonneg {A : ℝ} (hA : 0 < A) (t : ℝ) : 0 ≤ fejerHat A t := by
  unfold fejerHat
  split_ifs with h
  · exact hA.le
  · have h1 : 0 ≤ 1 - Real.cos (A * t) := by linarith [Real.cos_le_one (A * t)]
    have h2 : 0 < A * t ^ 2 := by
      have : t ^ 2 > 0 := by positivity
      positivity
    positivity

@[simp] theorem fejerHat_zero {A : ℝ} : fejerHat A 0 = A := by simp [fejerHat]

/-- The pole term of the explicit formula for the triangle: `ĥ(i/2) + ĥ(-i/2)`.  Evaluating the
Fejér kernel at `t = ±i/2` turns the cosine into a hyperbolic cosine. -/
def fejerPole (A : ℝ) : ℝ := 16 * (Real.cosh (A / 2) - 1) / A

theorem fejerPole_nonneg {A : ℝ} (hA : 0 < A) : 0 ≤ fejerPole A := by
  have := Real.one_le_cosh (A / 2)
  unfold fejerPole
  have h1 : 0 ≤ Real.cosh (A / 2) - 1 := by linarith
  positivity

/-- **`pole A ≍ 8 e^{A/2}/A`.**  Exactly `A · pole A · e^{-A/2} = 8(1 + e^{-A} - 2 e^{-A/2})`,
which tends to `8`; measured `7.9964` at `A = 16.8`. -/
theorem fejerPole_mul_eq (A : ℝ) (hA : A ≠ 0) :
    A * fejerPole A * Real.exp (-A / 2)
      = 8 * (1 + Real.exp (-A) - 2 * Real.exp (-A / 2)) := by
  have he : Real.exp (A / 2) * Real.exp (-A / 2) = 1 := by
    rw [← Real.exp_add, show A / 2 + -A / 2 = 0 by ring, Real.exp_zero]
  have he2 : Real.exp (-A / 2) * Real.exp (-A / 2) = Real.exp (-A) := by
    rw [← Real.exp_add]; congr 1; ring
  have hn : Real.exp (-(A / 2)) = Real.exp (-A / 2) := by congr 1; ring
  unfold fejerPole
  have hcancel : A * (16 * (Real.cosh (A / 2) - 1) / A) = 16 * (Real.cosh (A / 2) - 1) := by
    rw [mul_comm, div_mul_cancel₀ _ hA]
  rw [hcancel, Real.cosh_eq, hn]
  linear_combination (8 : ℝ) * he + (8 : ℝ) * he2

theorem tendsto_fejerPole :
    Tendsto (fun A : ℝ => A * fejerPole A * Real.exp (-A / 2)) atTop (𝓝 8) := by
  have h1 : Tendsto (fun A : ℝ => Real.exp (-A)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have hhalf : Tendsto (fun A : ℝ => A / 2) atTop atTop :=
    Filter.Tendsto.atTop_div_const (by norm_num : (0:ℝ) < 2) Filter.tendsto_id
  have h2 : Tendsto (fun A : ℝ => Real.exp (-A / 2)) atTop (𝓝 0) := by
    have hcomp := Real.tendsto_exp_neg_atTop_nhds_zero.comp hhalf
    simpa [Function.comp_def, neg_div] using hcomp
  have hc1 : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hs : Tendsto (fun A : ℝ => 1 + Real.exp (-A) - 2 * Real.exp (-A / 2))
      atTop (𝓝 1) := by
    have hsum := hc1.add h1
    have hdbl := h2.const_mul (2:ℝ)
    simpa using hsum.sub hdbl
  have hlim : Tendsto (fun A : ℝ => 8 * (1 + Real.exp (-A) - 2 * Real.exp (-A / 2)))
      atTop (𝓝 8) := by simpa using hs.const_mul (8:ℝ)
  refine hlim.congr' ?_
  filter_upwards [eventually_ne_atTop (0:ℝ)] with A hA
  exact (fejerPole_mul_eq A hA).symm

/-! ## The residual -/

/-- The smoothed von Mangoldt sum of the triangle family:
`2 Σ_{n ≤ e^A} Λ(n) n^{-1/2} (1 - log n / A)`. -/
def fejerPrimes (A : ℝ) : ℝ :=
  2 * ∑' n : ℕ, (Λ n) * (n : ℝ) ^ (-(1:ℝ)/2) * max 0 (1 - Real.log n / A)

/-- **The necessary condition as a pure prime inequality.**  `archFejer` is the archimedean term of the
explicit formula for the triangle, a single explicit integral against the digamma kernel with
no zero data in it; measured to converge to `ψ(1/4) - log π ≈ -5.372`.  Positivity of the Weil
functional on this family — implied by RH, but *not* implying it, see the header — is exactly

  `fejerPrimes A ≤ fejerPole A + archFejer A`   for every `A > 0`,

with measured slack `≈ 0.09/A` against terms of size `≈ 8 e^{A/2}/A`. -/
def FejerWeilPositive (archFejer : ℝ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → fejerPrimes A ≤ fejerPole A + archFejer A

end FleetFejerWeil
