import Mathlib
import Reduction
import ZerosCountable

/-!
# `ζ` has only finitely many zeros in any compact set

**Proven (unconditionally, no axioms beyond Mathlib's standard three):**

* `eventually_ne_zero_nhdsNE_one` — `ζ` is nonvanishing on a punctured
  neighbourhood of the pole `1` (from `riemannZeta_residue_one`).
* `zeros_ne_one_isClosed_and_discrete` — for any compact `K ⊆ ℂ`, the set
  `{s ∈ K | ζ s = 0 ∧ s ≠ 1}` is closed in `ℂ` and has the discrete subspace
  topology. Every point of `ℂ` has a punctured neighbourhood missing the set:
  at `1` by the pole, elsewhere by `ZerosCountable.isolated_zero_riemannZeta`
  (the identity theorem on the connected domain `{1}ᶜ`).
* `finite_zeros_ne_one_of_isCompact` — that set is finite
  (closed subset of a compact set, discrete ⟹ finite via `IsCompact.finite`).
* `finite_zeros_of_isCompact` — if moreover `1 ∉ K`, `{s ∈ K | ζ s = 0}` is finite.
* `finite_nontrivialZeros_of_isCompact` — `{ρ ∈ K | IsNontrivialZero ρ}` is finite.
* `isCompact_rect` / `finite_zeros_rect` — the closed rectangle
  `[[1 - c, c]] ×ℂ [[-T, T]]` used in `ContourShift` is compact and contains
  only finitely many zeros `≠ 1` of `ζ`.

Nothing about the *location* of the zeros is claimed. No `sorry`, no axioms,
no hypothesis-dependent statements.
-/

noncomputable section
open Complex Filter Topology Set
open scoped Interval

namespace FiniteZeros

/-- `ζ` is nonvanishing on a punctured neighbourhood of its pole `s = 1`:
`(s - 1) ζ(s) → 1 ≠ 0` as `s → 1`, `s ≠ 1`. -/
theorem eventually_ne_zero_nhdsNE_one : ∀ᶠ s in 𝓝[≠] (1 : ℂ), riemannZeta s ≠ 0 := by
  filter_upwards [riemannZeta_residue_one.eventually_ne one_ne_zero] with s hs
  exact fun h => hs (by rw [h, mul_zero])

/-- For every point `x ∈ ℂ`, `ζ` is nonvanishing on a punctured neighbourhood
of `x`: at `x = 1` by the pole, at `x ≠ 1` by the identity theorem
(`ZerosCountable.isolated_zero_riemannZeta`). -/
theorem eventually_ne_zero_nhdsNE (x : ℂ) : ∀ᶠ w in 𝓝[≠] x, riemannZeta w ≠ 0 := by
  by_cases hx : x = 1
  · subst hx; exact eventually_ne_zero_nhdsNE_one
  · exact ZerosCountable.isolated_zero_riemannZeta hx

/-- For any set `K`, the set of zeros of `ζ` in `K` other than `1` is
closed in `ℂ` whenever `K` is closed, and always carries the discrete subspace
topology. Proven through `isClosed_and_discrete_iff`: every point of `ℂ` has a
punctured neighbourhood disjoint from the set. -/
theorem zeros_ne_one_isClosed_and_discrete {K : Set ℂ} (hK : IsClosed K) :
    IsClosed {s ∈ K | riemannZeta s = 0 ∧ s ≠ 1} ∧
      DiscreteTopology {s ∈ K | riemannZeta s = 0 ∧ s ≠ 1} := by
  rw [← isDiscrete_iff_discreteTopology, isClosed_and_discrete_iff]
  intro x
  rw [Filter.disjoint_principal_right]
  by_cases hxK : x ∈ K
  · filter_upwards [eventually_ne_zero_nhdsNE x] with w hw
    exact fun hw' => hw hw'.2.1
  · have hopen : Kᶜ ∈ 𝓝 x := hK.isOpen_compl.mem_nhds hxK
    filter_upwards [mem_nhdsWithin_of_mem_nhds hopen] with w hw
    exact fun hw' => hw hw'.1

/-- **Finitely many zeros in a compact set.** For any compact `K ⊆ ℂ`, the set
of zeros of `ζ` in `K` other than the pole `1` is finite. -/
theorem finite_zeros_ne_one_of_isCompact {K : Set ℂ} (hK : IsCompact K) :
    Set.Finite {s ∈ K | riemannZeta s = 0 ∧ s ≠ 1} := by
  obtain ⟨hcl, hdisc⟩ := zeros_ne_one_isClosed_and_discrete hK.isClosed
  exact (hK.of_isClosed_subset hcl (Set.sep_subset _ _)).finite
    (isDiscrete_iff_discreteTopology.mpr hdisc)

/-- **Finitely many zeros in a compact set avoiding `1`.** -/
theorem finite_zeros_of_isCompact {K : Set ℂ} (hK : IsCompact K) (h1 : (1 : ℂ) ∉ K) :
    Set.Finite {s ∈ K | riemannZeta s = 0} := by
  refine (finite_zeros_ne_one_of_isCompact hK).subset ?_
  rintro s ⟨hsK, hs⟩
  exact ⟨hsK, hs, fun h => h1 (h ▸ hsK)⟩

/-- **Finitely many nontrivial zeros in a compact set.** -/
theorem finite_nontrivialZeros_of_isCompact {K : Set ℂ} (hK : IsCompact K) :
    Set.Finite {ρ ∈ K | Reduction.IsNontrivialZero ρ} := by
  refine (finite_zeros_ne_one_of_isCompact hK).subset ?_
  rintro ρ ⟨hρK, hρ⟩
  exact ⟨hρK, hρ.1, hρ.2.2⟩

/-- The closed rectangle `[[1 - c, c]] ×ℂ [[-T, T]]` is compact. -/
theorem isCompact_rect (c T : ℝ) : IsCompact ([[1 - c, c]] ×ℂ [[-T, T]]) :=
  isCompact_uIcc.reProdIm isCompact_uIcc

/-- **Finitely many zeros in the contour rectangle.** The closed rectangle
`[[1 - c, c]] ×ℂ [[-T, T]]` (which contains the pole `1`) contains only
finitely many zeros `s ≠ 1` of `ζ`. The hypotheses `hc`, `hT` are not needed
(compactness holds for every `c`, `T`); they are kept to match the signature
used by `ContourShift`. -/
theorem finite_zeros_rect (c T : ℝ) (hc : 1 < c) (hT : 0 < T) :
    Set.Finite {s ∈ ([[1 - c, c]] ×ℂ [[-T, T]]) | riemannZeta s = 0 ∧ s ≠ 1} :=
  finite_zeros_ne_one_of_isCompact (isCompact_rect c T)

end FiniteZeros

end

