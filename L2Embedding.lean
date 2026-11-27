import Sobolev1D
import SelfAdjointness
import Mathlib

/-!
# L² Embedding of H²(0,L)

First Hilbert-space infrastructure for a future Friedrichs extension of the
continuum HP operator: every `u : H2 L` (continuous on the compact `[0,L]`)
is realised as an element `toL2 hL u` of the concrete Hilbert space
`L2 L := Lp ℝ 2 (volume.restrict (Icc 0 L))`.

## What is proven (all with standard axioms only)

* `memℒp_of_H2`  — `u.f ∈ L²(μ L)` for every `u : H2 L`: `u.f` is continuous
  on the compact `Icc 0 L`, hence bounded and a.e.-strongly measurable for the
  restricted measure, and the restricted Lebesgue measure is finite.
* `toL2`         — the induced element of `L2 L` (via `MeasureTheory.MemLp.toLp`).
* `inner_toL2`   — `⟪toL2 u, toL2 v⟫ = ∫ x in (0)..L, u.f x * v.f x`, the L²
  inner product agrees with the interval integral used in `Sobolev1D` and
  `SelfAdjointness`.
* `norm_sq_toL2` — `‖toL2 u‖² = ∫ x in (0)..L, (u.f x)²`.
* `orthogonal_of_eigen` — `SelfAdjointness.eigenfunctions_orthogonal`
  restated in L² language: eigenfunctions of `-d²/dx² + V` for distinct
  eigenvalues have `⟪toL2 u, toL2 v⟫ = 0`.

## What is NOT proven

* No linear structure on `H2 L` (it is a plain structure), so `toL2` is not
  shown to be additive/homogeneous; no closedness/density statements; no
  Friedrichs extension — these are future work.
-/

noncomputable section

open MeasureTheory Set

namespace L2Embedding

/-- Lebesgue measure restricted to the interval `[0,L]`. -/
def μ (L : ℝ) : Measure ℝ := volume.restrict (Icc (0:ℝ) L)

/-- The concrete Hilbert space `L²(0,L)` of real-valued square-integrable
functions on `[0,L]`. -/
abbrev L2 (L : ℝ) := Lp ℝ 2 (μ L)

/-- The restricted Lebesgue measure on `[0,L]` is finite. -/
instance instIsFiniteMeasure_μ (L : ℝ) : IsFiniteMeasure (μ L) := by
  unfold μ; infer_instance

variable {L : ℝ}

/-- **H² ⊂ L².** Every `u : H2 L` has `u.f ∈ L²(μ L)`: `u.f` is continuous on
the compact `Icc 0 L`, hence bounded there and a.e.-strongly measurable for the
restricted measure, and `μ L` is finite. (The hypothesis `0 < L` is not needed
here; it is kept in the signature so `toL2 hL u` has a uniform API.) -/
theorem memℒp_of_H2 (_hL : 0 < L) (u : H2 L) : MeasureTheory.MemLp u.f 2 (μ L) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn u.hf_cont
  refine MeasureTheory.MemLp.of_bound (u.hf_cont.aestronglyMeasurable measurableSet_Icc) C ?_
  unfold μ
  exact ae_restrict_of_forall_mem measurableSet_Icc hC

/-- The element of `L²(0,L)` determined by `u : H2 L`. -/
def toL2 (hL : 0 < L) (u : H2 L) : L2 L := (memℒp_of_H2 hL u).toLp u.f

/-- **L² inner product = interval integral.** For `u v : H2 L`,
`⟪toL2 u, toL2 v⟫ = ∫ x in (0)..L, u.f x * v.f x`. -/
theorem inner_toL2 (hL : 0 < L) (u v : H2 L) :
    inner ℝ (toL2 hL u) (toL2 hL v) = ∫ x in (0)..L, u.f x * v.f x := by
  rw [L2.inner_def, intervalIntegral.integral_of_le hL.le, ← integral_Icc_eq_integral_Ioc]
  have hu := MeasureTheory.MemLp.coeFn_toLp (memℒp_of_H2 hL u)
  have hv := MeasureTheory.MemLp.coeFn_toLp (memℒp_of_H2 hL v)
  show ∫ a, inner ℝ ((toL2 hL u) a) ((toL2 hL v) a) ∂(μ L) = ∫ x in Icc (0:ℝ) L, u.f x * v.f x
  unfold toL2
  apply integral_congr_ae
  filter_upwards [hu, hv] with x hxu hxv
  rw [hxu, hxv]
  simp [mul_comm]

/-- **L² norm squared = ∫ u².** For `u : H2 L`,
`‖toL2 u‖² = ∫ x in (0)..L, (u.f x)²`. -/
theorem norm_sq_toL2 (hL : 0 < L) (u : H2 L) :
    ‖toL2 hL u‖ ^ 2 = ∫ x in (0)..L, (u.f x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_toL2]
  congr 1; ext x; ring

/-- **Orthogonality of eigenfunctions in L².** Restatement of
`SelfAdjointness.eigenfunctions_orthogonal`: if `u, v : H2 H.L` are
eigenfunctions of `-d²/dx² + V` with distinct eigenvalues `lam ≠ mu`, then
`⟪toL2 u, toL2 v⟫ = 0` in `L²(0, H.L)`. -/
theorem orthogonal_of_eigen (H : HPContinuum)
    (hVcont : ContinuousOn H.V (Set.Icc 0 H.L))
    (u v : H2 H.L) (lam mu : ℝ) (hlm : lam ≠ mu)
    (hu : ∀ x ∈ Set.Icc 0 H.L,
      -(deriv (deriv u.f) x) + H.V x * u.f x = lam * u.f x)
    (hv : ∀ x ∈ Set.Icc 0 H.L,
      -(deriv (deriv v.f) x) + H.V x * v.f x = mu * v.f x) :
    inner ℝ (toL2 H.hL u) (toL2 H.hL v) = 0 := by
  rw [inner_toL2]
  exact eigenfunctions_orthogonal H hVcont u v lam mu hlm hu hv

end L2Embedding

end
