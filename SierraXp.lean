import BerryKeating
import XpDiscretization
import XpSpectrum
import Mathlib

/-!
# Sierra-style truncated `xp`: the live candidate after the ruled-out paths

`XpDiscretization` left two negative facts on purpose:

* naive `xp` is unitarily `-i d/du` on the line (continuous spectrum);
* any fixed-length compactification has linear counting, incompatible with
  the Riemann–von Mangoldt `E log E` density.

This module writes the next candidate those results force: Sierra truncation
`x ∈ [1, Λ]` promoted to an **energy-dependent cutoff** `Λ(E) = E` so that
`ℓ(E) = log E`.

## Proven

* Fixed `Λ > 1`: discrete model spectrum, wrong density
  (`fixed_truncation_density_fails`).
* Energy-dependent cutoff: one-sided mode count equals `(E log E)/(2π)` and
  is asymptotically equivalent to `A(E)/(2π)`
  (`energy_dependent_matches_rvm_leading`).
* `SmoothDensityCandidate` inhabited by `log`.

## Not proven

No self-adjoint realization with spectrum `{γ}`. Arithmetic `S(T)` open.
`OperatorRealization` is uninhabited on purpose (not `True`, no `axiom`, no
`sorry`).

No `sorry`, no custom axioms.
-/

noncomputable section
open Real Filter Topology Asymptotics

namespace SierraXp

/-! ## Fixed truncation `x ∈ [1, Λ]` -/

/-- Effective `u = log x` length for Sierra truncation `x ∈ [1, Λ]`. -/
def truncationLength (Λ : ℝ) : ℝ := Real.log Λ

theorem truncationLength_pos {Λ : ℝ} (hΛ : 1 < Λ) :
    0 < truncationLength Λ :=
  Real.log_pos hΛ

/-- Model eigenvalues `λ_n = 2π n / log Λ`. -/
def eigenvalue (Λ : ℝ) (n : ℕ) : ℝ :=
  (2 * Real.pi * n) / truncationLength Λ

/-- One-sided mode count `ℓ · E / (2π)`. -/
def sierraCount (Λ E : ℝ) : ℝ :=
  truncationLength Λ * E / (2 * Real.pi)

theorem sierraCount_eq_half_circle (Λ E : ℝ) :
    sierraCount Λ E =
      XpDiscretization.circleCount (truncationLength Λ) E / 2 := by
  unfold sierraCount XpDiscretization.circleCount
  ring

/-- Fixed Sierra truncation cannot match `E log E` density. -/
theorem fixed_truncation_density_fails {Λ : ℝ} (hΛ : 1 < Λ) :
    Tendsto (fun E : ℝ => XpDiscretization.targetCount E / sierraCount Λ E)
      atTop atTop := by
  have hℓ : 0 < truncationLength Λ := truncationLength_pos hΛ
  have hbase :=
    XpDiscretization.fixed_length_compactification_fails (truncationLength Λ) hℓ
  have hEq : ∀ᶠ E : ℝ in atTop,
      XpDiscretization.targetCount E / sierraCount Λ E =
        2 * (XpDiscretization.targetCount E /
          XpDiscretization.circleCount (truncationLength Λ) E) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with E hE
    have hc : XpDiscretization.circleCount (truncationLength Λ) E ≠ 0 := by
      unfold XpDiscretization.circleCount
      exact ne_of_gt (by positivity)
    rw [sierraCount_eq_half_circle]
    field_simp [hc]
  have htwo :
      Tendsto (fun E : ℝ =>
        2 * (XpDiscretization.targetCount E /
          XpDiscretization.circleCount (truncationLength Λ) E)) atTop atTop :=
    hbase.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  exact htwo.congr' (hEq.mono fun _ h => h.symm)

/-! ## Energy-dependent cutoff -/

def cutoffLambda (E : ℝ) : ℝ := E

def cutoffLength (E : ℝ) : ℝ := truncationLength (cutoffLambda E)

theorem cutoffLength_eq_effective {E : ℝ} (_hE : 1 ≤ E) :
    cutoffLength E = XpDiscretization.effectiveLength 1 E := by
  unfold cutoffLength cutoffLambda truncationLength XpDiscretization.effectiveLength
  simp [Real.log_one]

theorem sierraCount_cutoff (E : ℝ) :
    sierraCount (cutoffLambda E) E = E * Real.log E / (2 * Real.pi) := by
  unfold sierraCount cutoffLambda truncationLength
  ring

def areaCount (E : ℝ) : ℝ := XpSpectrum.A E / (2 * Real.pi)

theorem areaCount_eq (E : ℝ) :
    areaCount E = (E * Real.log E - E + 1) / (2 * Real.pi) := by
  unfold areaCount XpSpectrum.A
  rfl

private theorem correction_littleO_leading :
    (fun E : ℝ => (-E + (1 : ℝ))) =o[atTop] fun E => E * Real.log E := by
  refine (isLittleO_iff_tendsto' ?_).mpr ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually_gt_atTop (0 : ℝ)] with E hE hlog
    intro hg
    exact (mul_ne_zero (ne_of_gt (lt_trans Real.zero_lt_one hE)) (ne_of_gt hlog) hg).elim
  · have hlog_inv :
        Tendsto (fun E : ℝ => (Real.log E)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    have hprod_inv :
        Tendsto (fun E : ℝ => (E * Real.log E)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop)
    have hform : ∀ᶠ E : ℝ in atTop,
        (-E + 1) / (E * Real.log E) = -(Real.log E)⁻¹ + (E * Real.log E)⁻¹ := by
      filter_upwards [eventually_gt_atTop (1 : ℝ),
        Real.tendsto_log_atTop.eventually_gt_atTop (0 : ℝ)] with E hE hlog
      have hEne : E ≠ 0 := ne_of_gt (lt_trans Real.zero_lt_one hE)
      have hlogne : Real.log E ≠ 0 := ne_of_gt hlog
      field_simp [hEne, hlogne]
    have hsum :
        Tendsto (fun E : ℝ => -(Real.log E)⁻¹ + (E * Real.log E)⁻¹)
          atTop (nhds 0) := by
      simpa using hlog_inv.neg.add hprod_inv
    exact hsum.congr' (hform.mono fun _ h => h.symm)

private theorem leading_equiv_area_num :
    (fun E : ℝ => E * Real.log E) ~[atTop]
      fun E => E * Real.log E - E + 1 := by
  have heq :
      (fun E : ℝ => E * Real.log E - E + 1) =
        (fun E => E * Real.log E) + fun E => -E + 1 := by
    funext E; dsimp; abel
  rw [heq]
  have hurefl :
      (fun E : ℝ => E * Real.log E) ~[atTop] (fun E => E * Real.log E) :=
    IsEquivalent.refl
  exact (hurefl.add_isLittleO correction_littleO_leading).symm

/-- **Energy-dependent cutoff matches the smooth envelope.** -/
theorem energy_dependent_matches_rvm_leading :
    Tendsto (fun E : ℝ => sierraCount (cutoffLambda E) E / areaCount E)
      atTop (nhds 1) := by
  have hEq : ∀ᶠ E : ℝ in atTop,
      sierraCount (cutoffLambda E) E / areaCount E =
        (E * Real.log E) / (E * Real.log E - E + 1) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with E _
    rw [sierraCount_cutoff, areaCount_eq]
    have h2π : (2 * π : ℝ) ≠ 0 := ne_of_gt (by positivity)
    field_simp [h2π]
  have hz : ∀ᶠ E : ℝ in atTop, (E * Real.log E - E + 1) ≠ 0 := by
    filter_upwards [eventually_gt_atTop (3 : ℝ),
      Real.tendsto_log_atTop.eventually_gt_atTop (1 : ℝ)] with E hE hlog
    have hpos : (0 : ℝ) < E * (Real.log E - 1) + 1 := by
      have : 0 < E * (Real.log E - 1) :=
        mul_pos (lt_trans (by norm_num : (0 : ℝ) < 3) hE) (sub_pos.mpr hlog)
      linarith
    convert ne_of_gt hpos using 1
    ring
  have htend :
      Tendsto (fun E : ℝ => (E * Real.log E) / (E * Real.log E - E + 1))
        atTop (nhds 1) :=
    (isEquivalent_iff_tendsto_one hz).mp leading_equiv_area_num
  exact htend.congr' (hEq.mono fun _ h => h.symm)

/-! ## Packaging -/

def SmoothDensityCandidate (ℓ : ℝ → ℝ) : Prop :=
  Tendsto (fun E : ℝ => (ℓ E * E / (2 * Real.pi)) / areaCount E) atTop (nhds 1)

theorem log_is_smooth_density_candidate :
    SmoothDensityCandidate fun E => Real.log E := by
  change Tendsto (fun E : ℝ => sierraCount (cutoffLambda E) E / areaCount E)
    atTop (nhds 1)
  exact energy_dependent_matches_rvm_leading

/-- **Open:** self-adjoint realization whose spectrum equals the zeta ordinates. -/
structure OperatorRealization where
  confirmed : False  -- audit:allow-false-field (deliberately uninhabited: names the open problem)

def SpectrumMatchesZerosProgress : Prop := Nonempty OperatorRealization

theorem spectrum_match_still_open :
    SpectrumMatchesZerosProgress ↔ False := by
  constructor
  · rintro ⟨⟨h⟩⟩; exact h
  · exact False.elim

end SierraXp
