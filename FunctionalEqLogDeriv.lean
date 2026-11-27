import Mathlib

/-!
# Logarithmic derivative of the functional equation of `ζ`

Mathlib's `riemannZeta_one_sub` gives, for `s ∉ -ℕ` and `s ≠ 1`,
`ζ(1 - s) = 2 (2π)^(-s) Γ(s) cos(πs/2) ζ(s)`.
This file differentiates that identity.

Main results (all fully proven, no axioms beyond Mathlib's standard three):
* `eventually_ne_neg_nat`: the condition `∀ n : ℕ, s ≠ -n` is open (via `Γ s ≠ 0`).
* `hasDerivAt_zeta_one_sub`: `s ↦ ζ(1 - s)` has derivative `-ζ'(1 - s)` at `s ≠ 0`.
* `deriv_zeta_one_sub`: the derivative of the functional equation, i.e.
  `-ζ'(1-s) = 2 (2π)^(-s) [(-log 2π) Γ(s) cos + Γ'(s) cos - Γ(s) (π/2) sin] ζ(s)
               + 2 (2π)^(-s) Γ(s) cos(πs/2) ζ'(s)`, for `s ∉ -ℕ`, `s ≠ 0`, `s ≠ 1`.
* `logDeriv_zeta_one_sub`: dividing by `ζ(1-s)` (nonzero when additionally `ζ(s) ≠ 0` and
  `cos(πs/2) ≠ 0`):
  `-(ζ'(1-s)/ζ(1-s)) = -log(2π) + Γ'(s)/Γ(s) - (π/2) tan(πs/2) + ζ'(s)/ζ(s)`.

Hypotheses on the theorems are exactly the natural non-vanishing / non-pole conditions;
nothing is left unproven.
-/

noncomputable section

open Complex Filter Topology Real

namespace FunctionalEqLogDeriv

/-- The condition `∀ n : ℕ, s ≠ -n` is open: it holds on a neighbourhood of any `s`
satisfying it. Proof: `Γ` is continuous at such `s` with `Γ s ≠ 0`, and `Γ (-n) = 0`. -/
theorem eventually_ne_neg_nat {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) :
    ∀ᶠ t in 𝓝 s, ∀ n : ℕ, t ≠ -(n : ℂ) := by
  have hcont : ContinuousAt Complex.Gamma s :=
    (Complex.differentiableAt_Gamma s hs).continuousAt
  have hne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
  filter_upwards [hcont.eventually_ne hne] with t ht n htn
  apply ht
  rw [htn]
  exact Complex.Gamma_neg_nat_eq_zero n

/-- `s ↦ ζ(1 - s)` has derivative `-ζ'(1 - s)` at every `s ≠ 0`. -/
theorem hasDerivAt_zeta_one_sub {s : ℂ} (hs0 : s ≠ 0) :
    HasDerivAt (fun t : ℂ => riemannZeta (1 - t)) (-(deriv riemannZeta (1 - s))) s := by
  have h1 : (1 : ℂ) - s ≠ 1 := by
    intro h
    apply hs0
    linear_combination -h
  exact HasDerivAt.comp_const_sub 1 s (differentiableAt_riemannZeta h1).hasDerivAt

/-- `(2π : ℂ) ≠ 0`. -/
theorem two_pi_ne_zero : (2 * (π : ℂ)) ≠ 0 := by
  have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact mul_ne_zero two_ne_zero this

/-- `Complex.log (2π) = Real.log (2π)` (as a complex number). -/
theorem log_two_pi_eq : Complex.log (2 * (π : ℂ)) = (Real.log (2 * π) : ℂ) := by
  have h : (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
  rw [h, ← Complex.ofReal_log (by positivity)]

/-- The right-hand side of the functional equation has the expected derivative. -/
theorem hasDerivAt_functionalEq_rhs {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1) :
    HasDerivAt
      (fun t : ℂ => 2 * (2 * (π : ℂ)) ^ (-t) * Complex.Gamma t * Complex.cos (π * t / 2)
        * riemannZeta t)
      (((2 * ((2 * (π : ℂ)) ^ (-s) * Complex.log (2 * (π : ℂ)) * (-1)) * Complex.Gamma s
          + 2 * (2 * (π : ℂ)) ^ (-s) * deriv Complex.Gamma s) * Complex.cos (π * s / 2)
          + 2 * (2 * (π : ℂ)) ^ (-s) * Complex.Gamma s
            * (-Complex.sin (π * s / 2) * (π * 1 / 2))) * riemannZeta s
        + 2 * (2 * (π : ℂ)) ^ (-s) * Complex.Gamma s * Complex.cos (π * s / 2)
          * deriv riemannZeta s) s := by
  have hpow : HasDerivAt (fun t : ℂ => (2 * (π : ℂ)) ^ (-t))
      ((2 * (π : ℂ)) ^ (-s) * Complex.log (2 * (π : ℂ)) * (-1)) s :=
    (hasDerivAt_neg' s).const_cpow (Or.inl two_pi_ne_zero)
  have hG : HasDerivAt Complex.Gamma (deriv Complex.Gamma s) s :=
    (Complex.differentiableAt_Gamma s hs).hasDerivAt
  have hcos : HasDerivAt (fun t : ℂ => Complex.cos (π * t / 2))
      (-Complex.sin (π * s / 2) * (π * 1 / 2)) s :=
    (((hasDerivAt_id s).const_mul (π : ℂ)).div_const 2).ccos
  have hζ : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
    (differentiableAt_riemannZeta hs').hasDerivAt
  exact (((hpow.const_mul 2).mul hG).mul hcos).mul hζ

/-- **Derivative of the functional equation.** For `s ∉ -ℕ`, `s ≠ 0`, `s ≠ 1`:
`-ζ'(1-s) = d/ds [2 (2π)^(-s) Γ(s) cos(πs/2) ζ(s)]`, with the product rule expanded and
`Complex.log (2π)` written as `Real.log (2π)`. -/
theorem deriv_zeta_one_sub {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs0 : s ≠ 0) (hs' : s ≠ 1) :
    -(deriv riemannZeta (1 - s)) =
      2 * (2 * (π : ℂ)) ^ (-s)
        * ((-(Real.log (2 * π) : ℂ)) * Complex.Gamma s * Complex.cos (π * s / 2)
            + deriv Complex.Gamma s * Complex.cos (π * s / 2)
            - Complex.Gamma s * ((π : ℂ) / 2) * Complex.sin (π * s / 2)) * riemannZeta s
      + 2 * (2 * (π : ℂ)) ^ (-s) * Complex.Gamma s * Complex.cos (π * s / 2)
          * deriv riemannZeta s := by
  -- the functional equation holds on a neighbourhood of `s`
  have hev : (fun t : ℂ => riemannZeta (1 - t)) =ᶠ[𝓝 s]
      fun t : ℂ => 2 * (2 * (π : ℂ)) ^ (-t) * Complex.Gamma t * Complex.cos (π * t / 2)
        * riemannZeta t := by
    filter_upwards [eventually_ne_neg_nat hs, eventually_ne_nhds hs'] with t ht ht1
    exact riemannZeta_one_sub ht ht1
  have hL := hasDerivAt_zeta_one_sub hs0
  have hR := (hasDerivAt_functionalEq_rhs hs hs').congr_of_eventuallyEq hev
  have huniq := hL.unique hR
  rw [huniq, log_two_pi_eq]
  ring

/-- **Logarithmic derivative of the functional equation.** For `s ∉ -ℕ`, `s ≠ 0`, `s ≠ 1`,
`ζ(s) ≠ 0` and `cos(πs/2) ≠ 0`:
`-(ζ'(1-s)/ζ(1-s)) = -log(2π) + Γ'(s)/Γ(s) - (π/2) tan(πs/2) + ζ'(s)/ζ(s)`.
All hypotheses are the natural non-vanishing conditions; nothing is assumed beyond Mathlib. -/
theorem logDeriv_zeta_one_sub {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs0 : s ≠ 0) (hs' : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) (hcos : Complex.cos (π * s / 2) ≠ 0) :
    -(deriv riemannZeta (1 - s) / riemannZeta (1 - s)) =
      -(Real.log (2 * π) : ℂ) + deriv Complex.Gamma s / Complex.Gamma s
        - ((π : ℂ) / 2) * Complex.tan (π * s / 2)
        + deriv riemannZeta s / riemannZeta s := by
  have hFE := riemannZeta_one_sub hs hs'
  have hD := deriv_zeta_one_sub hs hs0 hs'
  have hG : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hs
  have hpow : (2 * (π : ℂ)) ^ (-s) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => two_pi_ne_zero h.1
  rw [← neg_div, hD, hFE, Complex.tan_eq_sin_div_cos]
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  rw [div_eq_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 hpow) hG) hcos) hζ)]
  field_simp

end FunctionalEqLogDeriv
