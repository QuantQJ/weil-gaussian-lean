import Mathlib

/-!
# The logarithmic derivative of `ζ` has a simple pole at `s = 1` with residue `-1`

Main result: `tendsto_sub_one_mul_logDeriv_zeta`, i.e.
`(s - 1) * (ζ'(s) / ζ(s)) → -1` as `s → 1`, `s ≠ 1`.

Route (fully proven, no axioms beyond Mathlib's standard three):
* `zetaReg s := ζ(s) - 1/(s-1)/Γℝ(s)` is **entire**: differentiable at `1` by Mathlib's
  `differentiableAt_hurwitzZetaEven_sub_one_div 0`, and away from `1` because `ζ` is.
* With `G := Γℝ⁻¹` (entire, `G 1 = 1`), we have `ζ = zetaReg + G/(s-1)` identically, so for
  `s ≠ 1`: `ζ'(s) = zetaReg'(s) + (G'(s)(s-1) - G(s))/(s-1)^2`.
* Hence `(s-1) ζ'/ζ = N(s) / ((s-1) ζ(s))` with
  `N(s) = (s-1)^2 zetaReg'(s) + (s-1) G'(s) - G(s)`; `N` is continuous (derivatives of entire
  functions are continuous) with `N(1) = -1`, and `(s-1)ζ(s) → 1` (`riemannZeta_residue_one`).
Division by a vanishing `ζ(s)` needs no special treatment: Lean's `x / 0 = 0` convention makes
both sides of the pointwise identity `0` in that case.

Nothing is left unproven in this file.
-/

noncomputable section

open Complex Filter Topology

namespace ZetaLogDerivPole

/-- The regular part of `ζ` near `s = 1`: `ζ(s) - 1/(s-1)/Γℝ(s)`. -/
def zetaReg (s : ℂ) : ℂ := riemannZeta s - 1 / (s - 1) / Gammaℝ s

/-- `zetaReg` is an entire function. -/
theorem differentiable_zetaReg : Differentiable ℂ zetaReg := by
  intro z
  rcases ne_or_eq z 1 with hz | rfl
  · have h1 : DifferentiableAt ℂ (fun s : ℂ => 1 / (s - 1) / Gammaℝ s) z := by
      have hfun : (fun s : ℂ => 1 / (s - 1) / Gammaℝ s)
          = fun s : ℂ => (1 / (s - 1)) * (Gammaℝ s)⁻¹ := by
        funext s; rw [div_eq_mul_inv]
      rw [hfun]
      have hA : DifferentiableAt ℂ (fun s : ℂ => 1 / (s - 1)) z :=
        (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _))
          (sub_ne_zero.mpr hz)
      exact hA.mul differentiable_Gammaℝ_inv.differentiableAt
    exact (differentiableAt_riemannZeta hz).sub h1
  · exact HurwitzZeta.differentiableAt_hurwitzZetaEven_sub_one_div 0

/-- The decomposition `ζ(s) = zetaReg s + Γℝ(s)⁻¹ / (s - 1)`, valid for every `s`. -/
theorem riemannZeta_eq_zetaReg_add (s : ℂ) :
    riemannZeta s = zetaReg s + (Gammaℝ s)⁻¹ / (s - 1) := by
  unfold zetaReg; ring

/-- `Γℝ(1)⁻¹ = 1`. -/
theorem Gammaℝ_inv_one : (Gammaℝ (1 : ℂ))⁻¹ = 1 := by
  rw [Gammaℝ_one, inv_one]

/-- Derivative of `ζ` at `s ≠ 1`, in terms of the entire functions `zetaReg` and `Γℝ⁻¹`. -/
theorem hasDerivAt_riemannZeta_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    HasDerivAt riemannZeta
      (deriv zetaReg s +
        (deriv (fun t : ℂ => (Gammaℝ t)⁻¹) s * (s - 1) - (Gammaℝ s)⁻¹ * 1) / (s - 1) ^ 2) s := by
  have hfun : riemannZeta = fun t : ℂ => zetaReg t + (Gammaℝ t)⁻¹ / (t - 1) :=
    funext riemannZeta_eq_zetaReg_add
  rw [hfun]
  exact (differentiable_zetaReg s).hasDerivAt.add
    ((differentiable_Gammaℝ_inv s).hasDerivAt.div ((hasDerivAt_id' s).sub_const 1)
      (sub_ne_zero.mpr hs))

/-- The logarithmic derivative of `ζ` has a simple pole at `s = 1` with residue `-1`:
`(s - 1) * (ζ'(s) / ζ(s)) → -1` as `s → 1` through `s ≠ 1`. -/
theorem tendsto_sub_one_mul_logDeriv_zeta :
    Tendsto (fun s : ℂ => (s - 1) * (deriv riemannZeta s / riemannZeta s))
      (𝓝[≠] 1) (𝓝 (-1)) := by
  -- the numerator `N`
  have hN : Tendsto
      (fun s : ℂ => (s - 1) ^ 2 * deriv zetaReg s
        + (s - 1) * deriv (fun t : ℂ => (Gammaℝ t)⁻¹) s - (Gammaℝ s)⁻¹) (𝓝 1) (𝓝 (-1)) := by
    have h1 : Continuous (deriv zetaReg) :=
      (differentiable_zetaReg.contDiff (n := 1)).continuous_deriv le_rfl
    have h2 : Continuous (deriv (fun t : ℂ => (Gammaℝ t)⁻¹)) :=
      (differentiable_Gammaℝ_inv.contDiff (n := 1)).continuous_deriv le_rfl
    have h3 : Continuous (fun t : ℂ => (Gammaℝ t)⁻¹) := differentiable_Gammaℝ_inv.continuous
    have hc : Continuous (fun s : ℂ => (s - 1) ^ 2 * deriv zetaReg s
        + (s - 1) * deriv (fun t : ℂ => (Gammaℝ t)⁻¹) s - (Gammaℝ s)⁻¹) :=
      ((((continuous_id.sub continuous_const).pow 2).mul h1).add
        ((continuous_id.sub continuous_const).mul h2)).sub h3
    have hval : ((1 : ℂ) - 1) ^ 2 * deriv zetaReg 1
        + (1 - 1) * deriv (fun t : ℂ => (Gammaℝ t)⁻¹) 1 - (Gammaℝ 1)⁻¹ = -1 := by
      rw [Gammaℝ_inv_one]; ring
    rw [← hval]
    exact hc.continuousAt.tendsto
  have hD : Tendsto (fun s : ℂ => (s - 1) * riemannZeta s) (𝓝[≠] 1) (𝓝 1) :=
    riemannZeta_residue_one
  have hlim := (tendsto_nhdsWithin_of_tendsto_nhds hN).div hD one_ne_zero
  rw [div_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s ≠ 1 := hs
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  simp only [Pi.div_apply]
  rw [(hasDerivAt_riemannZeta_of_ne_one hs1).deriv]
  rcases eq_or_ne (riemannZeta s) 0 with h0 | h0
  · simp [h0]
  · field_simp
    ring

end ZetaLogDerivPole

end
