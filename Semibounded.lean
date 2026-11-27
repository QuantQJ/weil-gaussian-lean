import Sobolev1D
import Mathlib

/-!
# Semiboundedness: proving the hypotheses instead of assuming the conclusion

`SelfAdjointness.lean` carries the project's one cited axiom,
`regular_sl_self_adjoint`, which asserts outright that our operator is
self-adjoint. That is assuming the conclusion.

The classical route to self-adjointness for `H = −d²/dx² + V` on a bounded
interval is the **Friedrichs extension**: a *symmetric* and *semibounded*
quadratic form has a distinguished self-adjoint extension. Both hypotheses
are concrete, checkable statements about our operator — and this module
proves them:

* symmetry — already machine-checked in `KatoRellichContinuum.lean`
  (`hp_continuum_symmetric`, standard axioms only);
* **semiboundedness — proven here**: `⟨Hu, u⟩ ≥ −M‖u‖²` whenever `|V| ≤ M`.

The engine is `H2.integration_by_parts` (Sobolev1D): with `v = u` it gives
the *kinetic energy identity* `⟨−u'', u⟩ = ∫ (u')² ≥ 0`, i.e. the Dirichlet
Laplacian is a positive operator. The potential can then drag the form down
by at most `M`.

**What this changes.** The cited input shrinks from
"*our specific operator is self-adjoint*" (a statement about this
construction, which a reader must take on faith) to
"*a symmetric semibounded form has a self-adjoint Friedrichs extension*"
(an abstract theorem of Friedrichs 1934, independent of anything here),
whose hypotheses are now both machine-checked. That is a materially
smaller and more honest assumption, and it is the standard shape of a
formalization that is waiting on Mathlib rather than hand-waving.

No `sorry`, no custom axioms in this file.
-/

noncomputable section
open MeasureTheory Set intervalIntegral

namespace Semibounded

variable {L : ℝ}

/-! ## Kinetic energy: the Dirichlet Laplacian is positive -/

/-- **Kinetic energy identity.** For `u ∈ H²∩H¹₀(0,L)`,
`∫ (−u'')·u = ∫ (u')²`. Immediate from integration by parts with `v = u`;
the boundary term vanishes by the Dirichlet conditions. -/
theorem kinetic_energy_eq (hL : 0 < L) (u : H2 L) :
    ∫ x in (0)..L, (-(deriv (deriv u.f) x)) * u.f x
      = ∫ x in (0)..L, (deriv u.f x) ^ 2 := by
  have h := H2.integration_by_parts hL u u
  rw [h]
  exact intervalIntegral.integral_congr (fun x _ => by ring)

/-- **The Dirichlet Laplacian is a positive operator**: `⟨−u'', u⟩ ≥ 0`.
This is the quantitative content of "no negative kinetic energy", and it is
the first half of semiboundedness. -/
theorem kinetic_energy_nonneg (hL : 0 < L) (u : H2 L) :
    0 ≤ ∫ x in (0)..L, (-(deriv (deriv u.f) x)) * u.f x := by
  rw [kinetic_energy_eq hL u]
  exact intervalIntegral.integral_nonneg hL.le (fun x _ => sq_nonneg _)

/-! ## Semiboundedness of the full operator -/

/-- **SEMIBOUNDEDNESS.** For `H = −d²/dx² + V` with `|V| ≤ M` on `[0,L]`
and `u ∈ H²∩H¹₀(0,L)`,

  `⟨Hu, u⟩ ≥ −M · ∫ u²`.

So the quadratic form is bounded below by `−M` times the squared norm: the
operator is semibounded, uniformly in `u`. Together with the machine-checked
symmetry this is exactly the hypothesis pair of the Friedrichs extension
theorem. -/
theorem hp_form_semibounded (hL : 0 < L) (u : H2 L) (V : ℝ → ℝ) (M : ℝ)
    (hVcont : ContinuousOn V (Icc 0 L))
    (hVbound : ∀ x ∈ Icc 0 L, |V x| ≤ M) :
    -M * (∫ x in (0)..L, (u.f x) ^ 2)
      ≤ ∫ x in (0)..L, (-(deriv (deriv u.f) x) + V x * u.f x) * u.f x := by
  have huIcc : Set.uIcc (0:ℝ) L = Icc 0 L := Set.uIcc_of_le hL.le
  -- integrability of the two pieces
  have hkin : IntervalIntegrable
      (fun x => (-(deriv (deriv u.f) x)) * u.f x) volume 0 L :=
    u.hddf_int.neg.mul_continuousOn (by rw [huIcc]; exact u.hf_cont)
  have hpot : IntervalIntegrable
      (fun x => V x * u.f x * u.f x) volume 0 L := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    exact (hVcont.mul u.hf_cont).mul u.hf_cont
  have hsq : IntervalIntegrable (fun x => (u.f x) ^ 2) volume 0 L := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    exact u.hf_cont.pow 2
  have hMsq : IntervalIntegrable (fun x => -M * (u.f x) ^ 2) volume 0 L :=
    hsq.const_mul _
  -- split the form
  have hsplit : ∫ x in (0)..L, (-(deriv (deriv u.f) x) + V x * u.f x) * u.f x
      = (∫ x in (0)..L, (-(deriv (deriv u.f) x)) * u.f x)
        + ∫ x in (0)..L, V x * u.f x * u.f x := by
    rw [← intervalIntegral.integral_add hkin hpot]
    exact intervalIntegral.integral_congr (fun x _ => by ring)
  rw [hsplit]
  -- potential term ≥ −M ∫ u²
  have hpot_lb : -M * (∫ x in (0)..L, (u.f x) ^ 2)
      ≤ ∫ x in (0)..L, V x * u.f x * u.f x := by
    have hmono : ∀ x ∈ Icc (0:ℝ) L, -M * (u.f x) ^ 2 ≤ V x * u.f x * u.f x := by
      intro x hx
      have hV := hVbound x hx
      have hVge : -M ≤ V x := neg_le_of_abs_le hV
      have : -M * (u.f x) ^ 2 ≤ V x * (u.f x) ^ 2 :=
        mul_le_mul_of_nonneg_right hVge (sq_nonneg _)
      calc -M * (u.f x) ^ 2 ≤ V x * (u.f x) ^ 2 := this
        _ = V x * u.f x * u.f x := by ring
    have := intervalIntegral.integral_mono_on hL.le hMsq hpot hmono
    rwa [intervalIntegral.integral_const_mul] at this
  linarith [kinetic_energy_nonneg hL u, hpot_lb]

/-- Convenient restatement: the form is bounded below by `−M` on the unit
sphere, i.e. `⟨Hu,u⟩ ≥ −M` whenever `∫u² = 1`. -/
theorem hp_form_ge_neg_M_of_normalized (hL : 0 < L) (u : H2 L) (V : ℝ → ℝ) (M : ℝ)
    (hVcont : ContinuousOn V (Icc 0 L))
    (hVbound : ∀ x ∈ Icc 0 L, |V x| ≤ M)
    (hnorm : ∫ x in (0)..L, (u.f x) ^ 2 = 1) :
    -M ≤ ∫ x in (0)..L, (-(deriv (deriv u.f) x) + V x * u.f x) * u.f x := by
  have := hp_form_semibounded hL u V M hVcont hVbound
  rwa [hnorm, mul_one] at this

/-- **Rayleigh-quotient consequence.** Any eigenvalue of the operator,
exhibited via a normalized eigenfunction, is `≥ −M`. Since a symmetric
operator's eigenvalues are exactly the values of the form on normalized
eigenfunctions, the spectrum is bounded below by `−M` — no self-adjointness
needed for this half. -/
theorem eigenvalue_ge_neg_M (hL : 0 < L) (u : H2 L) (V : ℝ → ℝ) (M lam : ℝ)
    (hVcont : ContinuousOn V (Icc 0 L))
    (hVbound : ∀ x ∈ Icc 0 L, |V x| ≤ M)
    (hnorm : ∫ x in (0)..L, (u.f x) ^ 2 = 1)
    (heig : ∀ x ∈ Icc 0 L,
      -(deriv (deriv u.f) x) + V x * u.f x = lam * u.f x) :
    -M ≤ lam := by
  have hform : ∫ x in (0)..L, (-(deriv (deriv u.f) x) + V x * u.f x) * u.f x
      = lam := by
    have hcongr : ∫ x in (0)..L, (-(deriv (deriv u.f) x) + V x * u.f x) * u.f x
        = ∫ x in (0)..L, lam * (u.f x) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hL.le] at hx
      simp only []
      rw [heig x hx]; ring
    rw [hcongr, intervalIntegral.integral_const_mul, hnorm, mul_one]
  rw [← hform]
  exact hp_form_ge_neg_M_of_normalized hL u V M hVcont hVbound hnorm

/-! ## Symmetry in the same `H2`-packaged form

`KatoRellichContinuum.hp_continuum_symmetric` proves symmetry from raw
hypotheses; this restates it over `H2 L` so that symmetry and
semiboundedness — the two Friedrichs hypotheses — have matching shapes and
can be bundled together. -/

/-- **Symmetry of `H = −d²/dx² + V` on `H²∩H¹₀`**, packaged over `H2`. -/
theorem hp_symmetric_H2 (hL : 0 < L) (u v : H2 L) (V : ℝ → ℝ)
    (hVcont : ContinuousOn V (Icc 0 L)) :
    ∫ x in (0)..L, (-(deriv (deriv u.f) x) + V x * u.f x) * v.f x
      = ∫ x in (0)..L, u.f x * (-(deriv (deriv v.f) x) + V x * v.f x) := by
  have huIcc : Set.uIcc (0:ℝ) L = Icc 0 L := Set.uIcc_of_le hL.le
  -- integrability of all four pieces
  have hk1 : IntervalIntegrable (fun x => (-(deriv (deriv u.f) x)) * v.f x) volume 0 L :=
    u.hddf_int.neg.mul_continuousOn (by rw [huIcc]; exact v.hf_cont)
  have hk2 : IntervalIntegrable (fun x => u.f x * (-(deriv (deriv v.f) x))) volume 0 L :=
    v.hddf_int.neg.continuousOn_mul (by rw [huIcc]; exact u.hf_cont)
  have hp1 : IntervalIntegrable (fun x => V x * u.f x * v.f x) volume 0 L := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]; exact (hVcont.mul u.hf_cont).mul v.hf_cont
  have hp2 : IntervalIntegrable (fun x => u.f x * (V x * v.f x)) volume 0 L := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]; exact u.hf_cont.mul (hVcont.mul v.hf_cont)
  have hsplitL : ∫ x in (0)..L, (-(deriv (deriv u.f) x) + V x * u.f x) * v.f x
      = (∫ x in (0)..L, (-(deriv (deriv u.f) x)) * v.f x)
        + ∫ x in (0)..L, V x * u.f x * v.f x := by
    rw [← intervalIntegral.integral_add hk1 hp1]
    exact intervalIntegral.integral_congr (fun x _ => by ring)
  have hsplitR : ∫ x in (0)..L, u.f x * (-(deriv (deriv v.f) x) + V x * v.f x)
      = (∫ x in (0)..L, u.f x * (-(deriv (deriv v.f) x)))
        + ∫ x in (0)..L, u.f x * (V x * v.f x) := by
    rw [← intervalIntegral.integral_add hk2 hp2]
    exact intervalIntegral.integral_congr (fun x _ => by ring)
  rw [hsplitL, hsplitR, H2.laplacian_symmetric hL u v]
  congr 1
  exact intervalIntegral.integral_congr (fun x _ => by ring)

end Semibounded
