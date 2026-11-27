import Mathlib
import Reduction

/-!
# The nontrivial zeros of `ζ` form a countable set

`Reduction.ZeroSideIdentity` quantifies over an enumeration `zeros : ℕ → ℂ` of
the nontrivial zeros. This module proves that such an enumeration exists,
i.e. that the set `{ρ | Reduction.IsNontrivialZero ρ}` is countable.

**Proven (unconditionally, no axioms beyond Mathlib's standard three):**

* `analyticOnNhd_riemannZeta` — `ζ` is analytic on `{1}ᶜ`
  (`differentiableAt_riemannZeta` + `analyticOnNhd_iff_differentiableOn`).
* `isPreconnected_compl_singleton_one` — `{1}ᶜ ⊆ ℂ` is preconnected
  (`ℂ` has real rank `2 > 1`).
* `isolated_zero_riemannZeta` — for every `z ≠ 1`, `∀ᶠ w in 𝓝[≠] z, ζ w ≠ 0`;
  in particular every zero `z ≠ 1` of `ζ` is isolated. By the identity
  theorem, otherwise `ζ ≡ 0` on `{1}ᶜ`, contradicting `ζ 2 ≠ 0`.
* `isolated_of_isNontrivialZero` — the same for nontrivial zeros.
* `countable_of_forall_isolated` — a subset of a second-countable space all
  of whose points are isolated in it is countable (via
  `TopologicalSpace.countable_cover_nhdsWithin`).
* `countable_nontrivialZeros` — the set of nontrivial zeros is countable.
* `exists_enumeration_nontrivialZeros` — hence (if nonempty) an enumeration
  `zeros : ℕ → ℂ` whose range is exactly the set of nontrivial zeros.

Nothing about the *location* of the zeros is claimed. No `sorry`, no axioms.
-/

noncomputable section
open Complex Filter Topology Set

namespace ZerosCountable

/-! ## Topological lemma: isolated ⟹ countable -/

/-- A subset `S` of a second-countable space, every point of which is
isolated in `S` (no other point of `S` in a punctured neighbourhood), is
countable. -/
theorem countable_of_forall_isolated {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] {S : Set X}
    (h : ∀ x ∈ S, ∀ᶠ y in 𝓝[≠] x, y ∉ S) : S.Countable := by
  have key : ∀ x : X, ∃ U : Set X, (x ∈ S → U ∈ 𝓝 x) ∧ ∀ y ∈ U, y ∈ S → y = x := by
    intro x
    by_cases hx : x ∈ S
    · have hev := h x hx
      rw [eventually_nhdsWithin_iff] at hev
      refine ⟨{y | y ∈ ({x}ᶜ : Set X) → y ∉ S}, fun _ => hev, ?_⟩
      intro y hy hyS
      by_contra hne
      exact hy hne hyS
    · exact ⟨∅, fun h' => absurd h' hx, fun y hy => absurd hy (Set.notMem_empty y)⟩
  choose U hU hU' using key
  obtain ⟨t, htS, htc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := U) (s := S) (fun x hx => mem_nhdsWithin_of_mem_nhds (hU x hx))
  refine htc.mono ?_
  intro y hy
  obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (hcov hy)
  rw [hU' x y hyx hy]
  exact hxt

/-! ## Analytic facts about `ζ` off the pole -/

/-- `ζ` is analytic on the complement of the pole `s = 1`. -/
theorem analyticOnNhd_riemannZeta : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := by
  rw [analyticOnNhd_iff_differentiableOn isOpen_compl_singleton]
  intro s hs
  exact (differentiableAt_riemannZeta (Set.mem_compl_singleton_iff.mp hs)).differentiableWithinAt

/-- The punctured plane `{1}ᶜ` is preconnected (`ℂ` has real rank `2`). -/
theorem isPreconnected_compl_singleton_one : IsPreconnected ({1}ᶜ : Set ℂ) :=
  (isConnected_compl_singleton_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; exact_mod_cast one_lt_two) (1 : ℂ)).isPreconnected

/-- `ζ` is not identically zero on `{1}ᶜ`: `ζ 2 ≠ 0`. -/
theorem riemannZeta_two_ne_zero : riemannZeta 2 ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re (by norm_num)

/-- **Isolated zeros.** For every `z ≠ 1`, `ζ` is nonvanishing on a punctured
neighbourhood of `z`; in particular every zero `z ≠ 1` of `ζ` is isolated.
(The hypothesis `ζ z = 0` is not needed: the identity theorem applies to any
point of the connected domain `{1}ᶜ`.) -/
theorem isolated_zero_riemannZeta {z : ℂ} (hz : z ≠ 1) :
    ∀ᶠ w in 𝓝[≠] z, riemannZeta w ≠ 0 := by
  by_contra hfreq
  rw [Filter.not_eventually] at hfreq
  simp only [not_not] at hfreq
  have hzero := analyticOnNhd_riemannZeta.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_compl_singleton_one (Set.mem_compl_singleton_iff.mpr hz) hfreq
  exact riemannZeta_two_ne_zero (hzero (Set.mem_compl_singleton_iff.mpr (by norm_num)))

/-- Every nontrivial zero is isolated among the zeros of `ζ`. -/
theorem isolated_of_isNontrivialZero {ρ : ℂ} (hρ : Reduction.IsNontrivialZero ρ) :
    ∀ᶠ w in 𝓝[≠] ρ, riemannZeta w ≠ 0 :=
  isolated_zero_riemannZeta hρ.2.2

/-! ## Main result -/

/-- **The nontrivial zeros of `ζ` form a countable set.** -/
theorem countable_nontrivialZeros : Set.Countable {ρ : ℂ | Reduction.IsNontrivialZero ρ} := by
  apply countable_of_forall_isolated
  intro ρ hρ
  filter_upwards [isolated_of_isNontrivialZero hρ] with w hw
  exact fun hw' => hw hw'.1

/-- If there is at least one nontrivial zero, there is an enumeration
`zeros : ℕ → ℂ` whose range is exactly the set of nontrivial zeros (the shape
quantified over in `Reduction.ZeroSideIdentity`). -/
theorem exists_enumeration_nontrivialZeros
    (hne : ∃ ρ, Reduction.IsNontrivialZero ρ) :
    ∃ zeros : ℕ → ℂ, Set.range zeros = {ρ : ℂ | Reduction.IsNontrivialZero ρ} := by
  obtain ⟨f, hf⟩ := Set.Countable.exists_eq_range countable_nontrivialZeros hne
  exact ⟨f, hf.symm⟩

end ZerosCountable

end
