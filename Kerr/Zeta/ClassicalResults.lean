import Kerr.Zeta.FunctionalEquation
import Mathlib

/-!
# File-14 RH scaffold, part 2: every remaining placeholder / postulate of the five RH files

Sources (QJ, read-only), with their header comments:
* `File-14/formal_proofs/riemann_hypothesis_complete.lean` — "Complete Riemann Hypothesis
  Formalization for Constant Framework. Publication-Ready Version. Author: James Campbell Ross
  Stuart Kerr. © 2025 Constant Framework LLC."
* `riemann_hypothesis.lean` — "Refined Lean 4 Formalization of the Riemann Hypothesis Framework.
  This provides a solid structural foundation for RH within Lean 4. Author: James Campbell Ross
  Stuart Kerr. © 2025 Constant Framework LLC."
* `riemann_hypothesis_refined.lean` — "Refined Lean 4 Formalization of the Riemann Hypothesis
  Framework. Improved version with proper Filter support and Mathlib integration. Author: James
  Campbell Ross Stuart Kerr. © 2025 Constant Framework LLC."
* `ConstantFramework_RH.lean` — "The Constant Framework – formally verified Riemann Hypothesis.
  Author: James Campbell Ross Stuart Kerr. © 2025 Constant Framework LLC."
* `ConstantFramework_RH_final.lean` — "Constant Framework – Formalised Riemann Hypothesis.
  Author: James Campbell Ross Stuart Kerr. Date: 2025-12-22."

Ported to Lean v4.16 / Mathlib, 2026-11-11; ported to Lean v4.35.0 / Mathlib, 2026-11-11.

`Kerr.File14RH` (imported) already proves the source's `IsNonTrivialZero`, `IsOnCriticalLine`,
`RiemannHypothesis'` (`= RiemannHypothesis`), `zero_free_region`, both `zero_symmetry` forms,
`zero_symmetry_critical_line`, and corrected `zeta_functional_equation` / `functional_equation`
(= source `functional_equation_xi`). This module covers everything else that the five files
left as a placeholder or postulated. Identical statements across the five files are merged; the
source name is the Lean name unless stated.

## Proved (no hypotheses)
* Real definitions replacing placeholders: `zerosUpTo` (nontrivial zeros with `|Im ρ| ≤ T`),
  `zeroMultiplicity` (order of vanishing), `PartialExplicitSum`, `ExplicitFormulaSum`,
  `ExplicitFormulaLimit`, `ZeroCount` / `N` (zeros with `0 < Im ρ ≤ T`, with multiplicity),
  `N_sigma`, `PerronIntegral` (symmetric limit of `PerronTruncated`), `zero_ordinate`,
  `SHO_eigenvalue`. Finiteness: `zerosUpTo_finite`, `zeroCountSet_finite` (identity theorem,
  copied from hp-proof `FiniteZeros`).
* `zero_density_under_RH`, `riemann_von_mangoldt` (as stated: `C` is chosen after `T`).
* `zeta_ne_zero_strip_lt_fourteen`, `small_rh_verified_fourteen` — **no zeros with
  `0 < Re s < 1`, `|Im s| < 14`** (the first zero is at `1/2 + 14.1347… i`). The band
  `10 ≤ Im s < 14` uses nineteen Euler–Maclaurin terms (boundary point `20`), a first-order
  expansion on each cell, a kernel-checked table of `log 1, …, log 20` (`lcTabOK_true`), and 134
  rectangular cells in 31 rows, each row checked by the kernel (`zfr14_row0` … `zfr14_row30`).
* `small_rh_verified_small` — **no zeros with `0 < Re s < 1`, `|Im s| < 10`**
  (`zeta_ne_zero_strip_lt_ten`): fourth-order Euler–Maclaurin (`ZetaGrowth*`, copied from
  hp-proof) with three terms and boundary point `4`; on `|Im s| ≤ 3/2` hp-proof's
  `FleetLowZeroFree` argument; on `3/2 ≤ Im s < 10`, `1/2 ≤ Re s < 1` a grid of 77 square cells,
  each certified by verified rational disc arithmetic (`Disc`, `expDisc`) evaluated by the
  kernel (`zeroFreeRows_ok`, `decide +kernel`); symmetry `ρ ↦ 1 − ρ̄`, `ρ ↦ ρ̄` for the rest.
  Corollaries: `riemannZeta_half_ne_zero`, `not_LindelofHypothesis`.
* The "growth ⇒ RH" halves of the three source equivalences: `RH_of_Mertens_growth`,
  `RH_of_Liouville_growth` (via `L(λ,s) ζ(s) = ζ(2s)`, `liouville_mul_zeta`),
  `RH_of_Chebyshev_growth` (via `−ζ'/ζ − ζ = ∑ (Λ(n) − 1) n^{-s}`), by Abel summation
  (`Dser`, `Dser_differentiableOn`) and the identity theorem (`eqOn_halfplane`).
* `ABC_constant_16_31_verified_alt` (final-file form: coprime, `rad > 1`) — proved: if
  `rad(abc) ≥ 9` then `rad^16.31 ≥ 9^16 > 10^15`; if `rad(abc) ≤ 8` then `c ≤ 9`
  (`small_rad_bound`, via `2^i + 1 = 3^j`, `3^j + 1 = 2^i`).
* `quadratic_reconstruction_verified` (was a postulate; a tautology of the source's own
  `SHO_eigenvalue`), `SHO_spectrum_equals_zeros`.
* `HypothesisH_implies_RH_bound` (= `HypothesisH_implies_Chebyshev_Growth`),
  `effective_ABC_bound`, `effective_ABC_bound'`: proved **vacuously** — `not_HypothesisH`
  shows Hypothesis H is false for every `σ₀` (the variance of `rad n / log n` is unbounded).

## Statements corrected (source false), with proofs
* `de_la_vallee_poussin_region` (every `A > 0`) — false (`A = 3`, `s = −2`):
  `de_la_vallee_poussin_region_source_false`; corrected `∃ A > 0` is the target
  `deLaValleePoussin_statement` (= `Nonempty ZeroFreeRegion`, also source `zero_free_region_exists`).
* `ZeroCount_bound` (all `T > 0`) — false at `T = 1/2` (`ZeroCount_bound_source_false`);
  corrected `ZeroCount_bound` (`T > 1`) proved.
* `ABC_constant_16_31_verified` / `ABC_constant_verified_10_15` — false (`2^16 + 2^16 = 2^17`,
  quality 17): `ABC_constant_16_31_source_false`; corrected `ABC_constant_16_31_verified_coprime`.
* `ABC_constant_16_31_verified_alt` (complete-file form, no `rad > 1`) — false (`0 + 1 = 1`):
  `ABC_alt_complete_source_false`.
* `RH_ABC_link` — its conclusion is false (`0 + 1 = 1`): `RH_ABC_link_conclusion_false`; corrected
  (positive triples) is the open `RH_ABC_link_statement` / `WeakABC`.
* `Mertens_bound_by_Chebyshev` — false at `x = 1` (`M(1) = 1`, `ψ(1) = 0`):
  `Mertens_bound_by_Chebyshev_source_false`; corrected `x ≥ 2` proved (`Mertens_bound_by_Chebyshev`,
  via `M(X) = ∑_{X/2 < n ≤ X, n odd} μ(n)` and Chebyshev's `ψ(2n) ≥ log C(2n, n)`).
* `LindelofHypothesis` as defined is false (`t = 0`): `not_LindelofHypothesis`; so
  `RH_implies_Lindelof` as stated would prove `¬RH`. Corrected `LindelofHypothesis'` (`|t| ≥ 1`).
* `Chebyshev_Explicit_Formula` (all forms), `Chebyshev_Perron_Formula`, `Perron_to_Explicit_Formula`
  / `Perron_equals_Explicit_Formula`: false at prime powers `x` with the source's right-continuous
  `ψ` (the limits give `ψ₀ = ψ − Λ(x)/2`); `riemann_hypothesis.lean`'s explicit formula and the
  Perron-to-explicit statements omit `−½ log(1 − x⁻²)`; the `PerronIntegral := 0` versions are
  false outright (`ψ(2) = log 2`). Corrected with `ChebyshevPsi0` and the missing term; proved from
  the targets `ExplicitFormula_statement`, `Perron_statement` (hypotheses), as are
  `Chebyshev_Explicit_Formula_simple`, `Chebyshev_Explicit_Formula_limit`, and
  `explicitFormulaConverges` (its `by`-placeholder argument is the hypothesis `h`).
* `hadamard_factorization` — incorrect as written (Γ-factor inverted relative to the classical
  formula; product over the type `VerifiedZero`, which repeats each zero once per height); not
  refuted in Lean; replaced by the target `Hadamard_statement`.
* `ZeroCount_asymptotic` in `ConstantFramework_RH(_final)` counts `0 < |Im ρ| ≤ T` (both
  half-planes), for which the limit would be `2`; the target uses the one-sided `ZeroCount`.

## Prop hypotheses (cited computation / open problems; never postulated)
* `PlattVerification` — Platt (2017), `SmallRHVerified (10^13)` (was the postulate
  `small_rh_verified_platt`); `small_rh_verified_of_platt`.
* Open: `Mertens_bound_under_RH_statement`, `Liouville_bound_under_RH_statement`,
  `RH_via_SHO_statement` (`RH_via_SHO_of_RH`), `RH_ABC_link_statement`, `WeakABC`.

## Formalization targets (true, not yet proved)
* `deLaValleePoussin_statement` — now proved: `deLaValleePoussin_holds` in
  `Kerr/Zeta/ClassicalDischarged.lean` (from `KerrPNT.target1_zeroFree`, `Kerr/PNT/Targets.lean`).
* `ZeroCount_asymptotic_statement`, `RiemannVonMangoldt_statement` — need the argument principle
  for `ξ` on rectangles and `S(T) = O(log T)`. Now proved: `Kerr.RvM.riemannVonMangoldt` (C = 30),
  `Kerr.RvM.zeroCount_asymptotic` (Kerr/Zeta/RiemannVonMangoldt.lean).
* `ExplicitFormula_statement`, `Perron_statement` — need truncated Perron with error terms and
  contour shifting past the zeros (hp-proof proves a test-function explicit formula, not this
  sharp-cutoff one).
* `PNT_statement`, `PNT_error_statement` — now proved: `PNT_holds`, `PNT_error_holds` in
  `Kerr/Zeta/ClassicalDischarged.lean` (from `KerrPNT.target2_psi`, `KerrPNT.target3_strongPNT`,
  `Kerr/PNT/Targets.lean`, the copied PrimeNumberTheoremAnd development).
* `Chebyshev_bound_under_RH_statement` (von Koch); with it `RH_iff_Chebyshev_Growth` is proved. Now proved:
  `Kerr.File14RHExtra.vonKoch`, `perron_holds`, `RH_iff_Chebyshev_Growth'` (Kerr/Zeta/ExplicitFormula.lean).
  `ExplicitFormula_statement` is proved as `explicitFormula_holds` (same module).
* `RH_implies_Mertens_growth_statement`, `RH_implies_Liouville_growth_statement` (Littlewood;
  need bounds for `1/ζ` on `Re s = 1/2 + ε` under RH); with them `RH_iff_Mertens_Growth`,
  `RH_iff_Liouville_Growth` are proved. Now proved: `Kerr.Littlewood.RH_implies_Mertens_growth`,
  `RH_implies_Liouville_growth`, `RH_iff_Mertens_Growth'`, `RH_iff_Liouville_Growth'`
  (Kerr/Zeta/Littlewood.lean).
* `Hadamard_statement` — Hadamard factorization of order-1 entire functions (not in Mathlib).
  Now proved: `Kerr.File14RHExtra.hadamard_xi` (Kerr/Zeta/Hadamard.lean).
* `RH_implies_Lindelof_statement` — needs Borel–Carathéodory / Hadamard three-circles bounds. Now proved: `Kerr.Littlewood.RH_implies_Lindelof`.

## Source notes (not mathematical statements)
* `weil_explicit_formula {f} (hf : sorry) : ∑ ρ in (zerosUpTo sorry), f ρ.ρ =
  ∑ p in (Finset.range sorry).filter Nat.Prime, sorry + sorry` — the statement itself has holes;
  dropped. (A Weil explicit formula is proved in hp-proof `FleetStandardExplicitFormula`.)
* `axiom a0_platt : VerifiedZero := { ρ := 1/2 + 2501 i, isZero := by sorry, … }` — labelled
  "Verified zero table entry (example)", "representative zero"; dropped. (Numerically
  `|ζ(1/2 + 2501 i)| ≈ 2.09`, so it is not a zero; not refuted in Lean.)
* `zerosUpTo T := []`, `zeroSequence` (five approximate ordinates), `RHConstants` /
  `current_best_bounds`, the "PUBLICATION NOTES" / "ROADMAP" comment blocks.

Reading choices (mine): `∀ ε > 0` binders whose type the source leaves to elaboration are read
as real `ε`; `|ζ(…)|` on `ℂ` is read as the norm; `Complex.abs s.im` as `|s.im|`; the source's
`1/2 < σ ≤ 1` as `1/2 < σ ∧ σ ≤ 1`; `zero_ordinate` is indexed from `0`; `SHO_eigenvalue` uses
the source formula for all `n`.
-/

noncomputable section
open Complex Filter Topology
open scoped ComplexConjugate Real ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt
  ArithmeticFunction.Omega

namespace Kerr.File14RHExtra
open Kerr.File14RH

/-! ## 1. Arithmetic summatory functions (source definitions) -/

/-- The radical of `n` (source). -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

/-- The Mertens function `M(x) = ∑_{n ≤ x} μ(n)` (source). -/
def Mertens (x : ℝ) : ℝ := ∑ n ∈ Finset.range (⌊x⌋.toNat + 1), (μ n : ℝ)

/-- The von Mangoldt function (source). -/
def vonMangoldt (n : ℕ) : ℝ := if n = 0 then 0 else Λ n

/-- Chebyshev `ψ(x) = ∑_{n ≤ x} Λ(n)` (source). -/
def ChebyshevPsi (x : ℝ) : ℝ := ∑ n ∈ Finset.range (⌊x⌋.toNat + 1), vonMangoldt n

/-- The Liouville function `λ(n) = (-1)^Ω(n)` (source; Mathlib has no `liouville`, so it is
written with `Ω = ArithmeticFunction.cardFactors`). -/
def Liouville (n : ℕ) : ℝ := if n = 0 then 0 else (-1) ^ (Ω n)

/-- `L(x) = ∑_{n ≤ x} λ(n)` (source). -/
def LiouvilleSum (x : ℝ) : ℝ := ∑ n ∈ Finset.range (⌊x⌋.toNat + 1), Liouville n

/-! ## 2. Zeros, multiplicities, zero counting -/

open scoped Classical in
/-- Multiplicity of a zero: the order of vanishing of `ζ` at `ρ` (`0` if `ζ ρ ≠ 0`). -/
def zeroMultiplicity (ρ : ℂ) : ℕ :=
  (analyticOrderAt riemannZeta ρ).toNat

/-- Nontrivial zeros with `|Im ρ| ≤ T` (replaces the source's empty-list / placeholder stub). -/
def zerosUpTo (T : ℝ) : Set ℂ := {ρ | IsNonTrivialZero ρ ∧ |ρ.im| ≤ T}

/-- `∑_{|Im ρ| ≤ T} x^ρ / ρ`, zeros counted with multiplicity. -/
def PartialExplicitSum (x T : ℝ) : ℂ :=
  ∑ᶠ ρ ∈ zerosUpTo T, (zeroMultiplicity ρ : ℂ) * ((x : ℂ) ^ ρ / ρ)

/-- The symmetric limit `lim_{T→∞} ∑_{|Im ρ| ≤ T} x^ρ/ρ` exists (source definition). -/
def ExplicitFormulaSum (x : ℝ) : Prop :=
  ∃ sum : ℂ, Tendsto (fun T => PartialExplicitSum x T) atTop (𝓝 sum)

/-- The limit, when it exists (source definition). -/
def ExplicitFormulaLimit (x : ℝ) (h : ExplicitFormulaSum x) : ℂ := Classical.choose h

/-- **`N(T)`**: number of nontrivial zeros with `0 < Im ρ ≤ T`, with multiplicity
(real definition replacing the source's placeholder `ZeroCount`). -/
def ZeroCount (T : ℝ) : ℝ :=
  ∑ᶠ ρ ∈ {ρ : ℂ | IsNonTrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ T}, (zeroMultiplicity ρ : ℝ)

/-- The same count as a natural number (source's `N`). -/
def N (T : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ {ρ : ℂ | IsNonTrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ T}, zeroMultiplicity ρ

/-- `N_σ(T)`: zeros with `|Im ρ| ≤ T` and `Re ρ ≥ σ`, with multiplicity (source's `N_sigma`). -/
def N_sigma (σ T : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ {ρ : ℂ | ρ ∈ zerosUpTo T ∧ σ ≤ ρ.re}, zeroMultiplicity ρ

/-! ### Finiteness of the zero sets (copied from hp-proof `ZerosCountable`, `FiniteZeros`) -/

theorem analyticOnNhd_riemannZeta : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := by
  rw [analyticOnNhd_iff_differentiableOn isOpen_compl_singleton]
  intro s hs
  exact (differentiableAt_riemannZeta (Set.mem_compl_singleton_iff.mp hs)).differentiableWithinAt

theorem isPreconnected_compl_singleton_one : IsPreconnected ({1}ᶜ : Set ℂ) :=
  (isConnected_compl_singleton_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; exact_mod_cast one_lt_two) (1 : ℂ)).isPreconnected

theorem isolated_zero_riemannZeta {z : ℂ} (hz : z ≠ 1) :
    ∀ᶠ w in 𝓝[≠] z, riemannZeta w ≠ 0 := by
  by_contra hfreq
  rw [Filter.not_eventually] at hfreq
  simp only [not_not] at hfreq
  have hzero := analyticOnNhd_riemannZeta.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_compl_singleton_one (Set.mem_compl_singleton_iff.mpr hz) hfreq
  exact riemannZeta_ne_zero_of_one_le_re (s := 2) (by norm_num)
    (hzero (Set.mem_compl_singleton_iff.mpr (by norm_num)))

theorem eventually_ne_zero_nhdsNE (x : ℂ) : ∀ᶠ w in 𝓝[≠] x, riemannZeta w ≠ 0 := by
  by_cases hx : x = 1
  · subst hx
    filter_upwards [riemannZeta_residue_one.eventually_ne one_ne_zero] with s hs
    exact fun h => hs (by rw [h, mul_zero])
  · exact isolated_zero_riemannZeta hx

theorem finite_zeros_ne_one_of_isCompact {K : Set ℂ} (hK : IsCompact K) :
    Set.Finite {s ∈ K | riemannZeta s = 0 ∧ s ≠ 1} := by
  have h : IsClosed {s ∈ K | riemannZeta s = 0 ∧ s ≠ 1} ∧
      DiscreteTopology {s ∈ K | riemannZeta s = 0 ∧ s ≠ 1} := by
    rw [← isDiscrete_iff_discreteTopology, isClosed_and_discrete_iff]
    intro x
    rw [Filter.disjoint_principal_right]
    by_cases hxK : x ∈ K
    · filter_upwards [eventually_ne_zero_nhdsNE x] with w hw
      exact fun hw' => hw hw'.2.1
    · have hopen : Kᶜ ∈ 𝓝 x := hK.isClosed.isOpen_compl.mem_nhds hxK
      filter_upwards [mem_nhdsWithin_of_mem_nhds hopen] with w hw
      exact fun hw' => hw hw'.1
  exact (hK.of_isClosed_subset h.1 (Set.sep_subset _ _)).finite
    (isDiscrete_iff_discreteTopology.mpr h.2)

/-- Nontrivial zeros with `|Im ρ| ≤ T` are finitely many. -/
theorem zerosUpTo_finite (T : ℝ) : (zerosUpTo T).Finite := by
  have hK : IsCompact ((Set.uIcc (0 : ℝ) 1) ×ℂ (Set.uIcc (-T) T)) :=
    isCompact_uIcc.reProdIm isCompact_uIcc
  refine (finite_zeros_ne_one_of_isCompact hK).subset ?_
  rintro ρ ⟨⟨hz, h0, h1⟩, hT⟩
  refine ⟨?_, hz, ?_⟩
  · rw [Complex.mem_reProdIm, Set.mem_uIcc, Set.mem_uIcc]
    exact ⟨Or.inl ⟨h0.le, h1.le⟩, Or.inl (abs_le.mp hT)⟩
  · intro e; rw [e] at h1; simp at h1

theorem zeroCountSet_finite (T : ℝ) :
    {ρ : ℂ | IsNonTrivialZero ρ ∧ 0 < ρ.im ∧ ρ.im ≤ T}.Finite :=
  (zerosUpTo_finite T).subset fun ρ ⟨hz, h0, hT⟩ =>
    ⟨hz, by rw [abs_of_pos h0]; exact hT⟩

theorem ZeroCount_eq_N (T : ℝ) : ZeroCount T = N T := by
  unfold ZeroCount N
  rw [finsum_mem_eq_finite_toFinset_sum _ (zeroCountSet_finite T),
    finsum_mem_eq_finite_toFinset_sum _ (zeroCountSet_finite T), Nat.cast_sum]

/-- **Zero density under RH** (source theorem; restated for the real `N_sigma`). The source
writes the hypothesis as `1/2 < σ ≤ 1`, read here as `1/2 < σ ∧ σ ≤ 1`. -/
theorem zero_density_under_RH (σ : ℝ) (hσ : 1 / 2 < σ ∧ σ ≤ 1) (T : ℝ) :
    RiemannHypothesis' → N_sigma σ T = 0 := by
  intro hRH
  have : {ρ : ℂ | ρ ∈ zerosUpTo T ∧ σ ≤ ρ.re} = ∅ := by
    ext ρ
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨hz, -⟩, hle⟩
    have := hRH ρ hz
    unfold IsOnCriticalLine at this
    linarith [hσ.1]
  unfold N_sigma
  rw [this, finsum_mem_empty]

/-! ### `N(T)` error bounds: the source's quantifier order -/

lemma exists_pos_mul_ge (a L : ℝ) (hL : 0 < L) : ∃ C > 0, |a| ≤ C * L := by
  refine ⟨|a| / L + 1, by positivity, ?_⟩
  rw [add_mul, div_mul_cancel₀ _ hL.ne']
  linarith

/-- The main term `(T/2π) log(T/2π) − T/2π`. -/
def mainTerm (T : ℝ) : ℝ := (T / (2 * π)) * Real.log (T / (2 * π)) - T / (2 * π)

/-- Source `riemann_von_mangoldt` (as stated: the constant `C` is chosen **after** `T`, so the
statement holds for every `T > 1`, whatever the value of `N T`). -/
theorem riemann_von_mangoldt (T : ℝ) (hT : T > 2) :
    ∃ C > 0, |(N T : ℝ) - mainTerm T| ≤ C * Real.log T :=
  exists_pos_mul_ge _ _ (Real.log_pos (by linarith))

/-- Source `ZeroCount_bound` is **false** as written for `0 < T < 1` (there `log T < 0`).
Counterexample `T = 1/2`. -/
theorem ZeroCount_bound_source_false :
    ¬ ∀ T : ℝ, T > 0 → ∃ C > 0, |ZeroCount T - mainTerm T| ≤ C * Real.log T := by
  intro h
  obtain ⟨C, hC, hle⟩ := h (1 / 2) (by norm_num)
  have hl : Real.log (1 / 2) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have : C * Real.log (1 / 2) < 0 := mul_neg_of_pos_of_neg hC hl
  linarith [abs_nonneg (ZeroCount (1 / 2) - mainTerm (1 / 2))]

/-- Corrected version of source `ZeroCount_bound` (source false: `T = 1/2`): `T > 1`. -/
theorem ZeroCount_bound (T : ℝ) (hT : T > 1) :
    ∃ C > 0, |ZeroCount T - mainTerm T| ≤ C * Real.log T :=
  exists_pos_mul_ge _ _ (Real.log_pos hT)



/-! ## Hypothesis H (source) is refutable -/

/-- The source's Hypothesis H (`x` is real; the source's `∀ N > 0` binder is unused). -/
def HypothesisH (σ₀ : ℝ) : Prop :=
  ∀ N : ℕ, N > 0 → ∃ x₀ > (0 : ℝ), ∀ x ≥ x₀,
    let E := fun n : ℕ => (rad n : ℝ) / Real.log n
    let variance := (∑ n ∈ Finset.range (⌊x⌋.toNat + 1),
        (E n - (∑ m ∈ Finset.range (⌊x⌋.toNat + 1), E m) / (⌊x⌋.toNat + 1 : ℝ)) ^ 2) /
          (⌊x⌋.toNat + 1 : ℝ)
    Real.sqrt variance ≤ σ₀

lemma log_lt_four_mul_sqrt_sqrt {p : ℝ} (hp : 0 < p) :
    Real.log p < 4 * Real.sqrt (Real.sqrt p) := by
  set q := Real.sqrt (Real.sqrt p) with hq
  have hq0 : 0 < q := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hp)
  have hq4 : q ^ 4 = p := by
    have h1 : q ^ 2 = Real.sqrt p := Real.sq_sqrt (Real.sqrt_nonneg _)
    have h2 : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp.le
    calc q ^ 4 = (q ^ 2) ^ 2 := by ring
      _ = p := by rw [h1, h2]
  have hlog : Real.log p = 4 * Real.log q := by
    rw [← hq4, Real.log_pow]; norm_num
  have : Real.log q < q := by
    have := Real.log_le_sub_one_of_pos hq0; linarith
  rw [hlog]; linarith

/-- **Hypothesis H is false for every `σ₀`**: the variance of `E(n) = rad n / log n` over
`n ≤ x` is unbounded (take `x = p` prime: the two values `E(1) = 0`, `E(p) = p / log p` already
force variance `≥ (p/log p)²/(2(p+1)) → ∞`). -/
theorem not_HypothesisH (σ₀ : ℝ) : ¬ HypothesisH σ₀ := by
  intro h
  obtain ⟨x₀, -, hall⟩ := h 1 one_pos
  set B : ℝ := max σ₀ 0 with hB
  have hB0 : 0 ≤ B := le_max_right _ _
  obtain ⟨p, hp_ge, hp⟩ := Nat.exists_infinite_primes (⌈x₀⌉₊ + ⌈(64 * B ^ 2) ^ 2⌉₊ + 2)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpx : x₀ ≤ (p : ℝ) := by
    have h1 : x₀ ≤ (⌈x₀⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈x₀⌉₊ + ⌈(64 * B ^ 2) ^ 2⌉₊ + 2 : ℕ) : ℝ) ≤ p := by exact_mod_cast hp_ge
    push_cast at h2; linarith [(Nat.cast_nonneg ⌈(64 * B ^ 2) ^ 2⌉₊ : (0 : ℝ) ≤ _)]
  have hpB : (64 * B ^ 2) ^ 2 < (p : ℝ) := by
    have h1 : (64 * B ^ 2) ^ 2 ≤ (⌈(64 * B ^ 2) ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈x₀⌉₊ + ⌈(64 * B ^ 2) ^ 2⌉₊ + 2 : ℕ) : ℝ) ≤ p := by exact_mod_cast hp_ge
    push_cast at h2; linarith [(Nat.cast_nonneg ⌈x₀⌉₊ : (0 : ℝ) ≤ _)]
  have hx := hall (p : ℝ) hpx
  simp only at hx
  have hfl : ⌊(p : ℝ)⌋.toNat = p := by simp
  rw [hfl] at hx
  set E : ℕ → ℝ := fun n => (rad n : ℝ) / Real.log n with hE
  set M : ℝ := (p : ℝ) + 1 with hM
  set m : ℝ := (∑ k ∈ Finset.range (p + 1), E k) / ((p : ℕ) + 1 : ℝ) with hm
  set V : ℝ := (∑ n ∈ Finset.range (p + 1), (E n - m) ^ 2) / ((p : ℕ) + 1 : ℝ) with hV
  have hM0 : 0 < ((p : ℕ) + 1 : ℝ) := by positivity
  have hsum : (E p - m) ^ 2 + (E 1 - m) ^ 2 ≤ ∑ n ∈ Finset.range (p + 1), (E n - m) ^ 2 := by
    have hsub : ({p, 1} : Finset ℕ) ⊆ Finset.range (p + 1) := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact Finset.mem_range.mpr (Nat.lt_succ_self _)
      · exact Finset.mem_range.mpr (by have := hp.two_le; omega)
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => sq_nonneg (E i - m))
    rwa [Finset.sum_pair hp.one_lt.ne'] at this
  have hE1 : E 1 = 0 := by simp [hE]
  have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
  have hEp : E p = p / Real.log p := by
    simp only [hE, rad, hp.primeFactors, Finset.prod_singleton]
  have hVge : (E p) ^ 2 / (2 * ((p : ℝ) + 1)) ≤ V := by
    rw [hV, div_le_div_iff₀ (by positivity) hM0]
    have h1 : (E p) ^ 2 ≤ 2 * ((E p - m) ^ 2 + (E 1 - m) ^ 2) := by
      rw [hE1]; nlinarith [sq_nonneg (E p - 2 * m)]
    have h2 : (E p) ^ 2 ≤ 2 * ∑ n ∈ Finset.range (p + 1), (E n - m) ^ 2 := by linarith
    calc E p ^ 2 * ((p : ℝ) + 1) ≤ (2 * ∑ n ∈ Finset.range (p + 1), (E n - m) ^ 2) * ((p : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right h2 hM0.le
      _ = (∑ n ∈ Finset.range (p + 1), (E n - m) ^ 2) * (2 * ((p : ℝ) + 1)) := by ring
  have hV0 : 0 ≤ V := by
    rw [hV]; exact div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) hM0.le
  have hVB : V ≤ B ^ 2 := by
    have hs : Real.sqrt V ≤ B := hx.trans (le_max_left _ _)
    have h1 := Real.sq_sqrt hV0
    have h2 := Real.sqrt_nonneg V
    calc V = Real.sqrt V ^ 2 := h1.symm
      _ ≤ B ^ 2 := pow_le_pow_left₀ h2 hs 2
  -- the lower bound beats `B²`
  set q := Real.sqrt (Real.sqrt p) with hq
  have hp0 : (0 : ℝ) < p := by linarith
  have hq0 : 0 < q := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hp0)
  have hq2 : q ^ 2 = Real.sqrt p := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hq4 : q ^ 4 = p := by
    have h2 : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
    calc q ^ 4 = (q ^ 2) ^ 2 := by ring
      _ = (p : ℝ) := by rw [hq2, h2]
  have hlt : Real.log p < 4 * q := log_lt_four_mul_sqrt_sqrt hp0
  have hsqrtB : 64 * B ^ 2 < q ^ 2 := by
    rw [hq2]
    have : Real.sqrt ((64 * B ^ 2) ^ 2) < Real.sqrt p :=
      Real.sqrt_lt_sqrt (by positivity) hpB
    rwa [Real.sqrt_sq (by positivity)] at this
  -- `(p / log p)^2 ≥ q^6/16`
  have hEp2 : q ^ 6 / 16 ≤ (E p) ^ 2 := by
    rw [hEp, div_pow, le_div_iff₀ (by positivity)]
    have : Real.log p ^ 2 ≤ 16 * q ^ 2 := by nlinarith
    calc q ^ 6 / 16 * Real.log p ^ 2 ≤ q ^ 6 / 16 * (16 * q ^ 2) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = (q ^ 4) ^ 2 := by ring
      _ = (p : ℝ) ^ 2 := by rw [hq4]
  have hfin : q ^ 2 / 64 ≤ V := by
    refine le_trans ?_ hVge
    rw [le_div_iff₀ (by positivity)]
    have : 2 * ((p : ℝ) + 1) ≤ 4 * q ^ 4 := by rw [hq4]; linarith
    calc q ^ 2 / 64 * (2 * ((p : ℝ) + 1)) ≤ q ^ 2 / 64 * (4 * q ^ 4) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = q ^ 6 / 16 := by ring
      _ ≤ (E p) ^ 2 := hEp2
  have : B ^ 2 < q ^ 2 / 64 := by linarith
  linarith

/-- Source `HypothesisH_implies_RH_bound` / `HypothesisH_implies_Chebyshev_Growth`: proved, but
**vacuously** — its hypothesis `HypothesisH 3.0` is refuted by `not_HypothesisH`. -/
theorem HypothesisH_implies_RH_bound (hH : HypothesisH 3.0) :
    ∃ C > 0, ∀ x ≥ 2, |ChebyshevPsi x - x| ≤ C * Real.sqrt x * (Real.log x) ^ 2 :=
  absurd hH (not_HypothesisH _)

/-! ## ABC constant (source section 15) -/

/-- `rad(abc)` (source helper). -/
def rad_abc (a b c : ℕ) : ℕ := rad (a * b * c)

/-- ABC quality `log c / log rad(abc)` (source). -/
def ABCQuality (a b c : ℕ) : ℝ :=
  if a + b = c ∧ a > 0 ∧ b > 0 ∧ c > 0 then
    (if rad (a * b * c) > 1 then Real.log (c : ℝ) / Real.log (rad (a * b * c) : ℝ) else 0)
  else 0

/-- `ABCConstantBound C max_c` (source; no coprimality, as in the source). -/
def ABCConstantBound (C : ℝ) (max_c : ℕ) : Prop :=
  ∀ a b c : ℕ, a + b = c → a > 0 → b > 0 → c > 0 → c ≤ max_c →
    rad (a * b * c) > 1 → ABCQuality a b c < C

lemma rad_two_pow (k : ℕ) (hk : k ≠ 0) : rad (2 ^ k) = 2 := by
  simp [rad, Nat.primeFactors_prime_pow hk Nat.prime_two]

/-- The source postulate `ABC_constant_16_31_verified : ABCConstantBound 16.31 (10^15)` (also stated
as theorem `ABC_constant_verified_10_15`) is **false**: the source's bound does not require
`gcd(a,b) = 1`, and `2^16 + 2^16 = 2^17` has `rad = 2`, quality `17 > 16.31`. -/
theorem ABC_constant_16_31_source_false : ¬ ABCConstantBound 16.31 (10 ^ 15) := by
  intro h
  have hrad : rad (2 ^ 16 * 2 ^ 16 * 2 ^ 17) = 2 := by
    rw [← pow_add, ← pow_add]; exact rad_two_pow _ (by norm_num)
  have := h (2 ^ 16) (2 ^ 16) (2 ^ 17) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by rw [hrad]; norm_num)
  unfold ABCQuality at this
  rw [if_pos ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, hrad,
    if_pos (by norm_num)] at this
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : Real.log (((2 ^ 17 : ℕ) : ℝ)) / Real.log ((2 : ℕ) : ℝ) = 17 := by
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [Real.log_pow, mul_div_assoc, div_self hl2.ne']; norm_num
  linarith

lemma rad_pos (n : ℕ) : 0 < rad n := Finset.prod_pos fun _ hp => (Nat.prime_of_mem_primeFactors hp).pos

lemma prod_dvd_rad {n : ℕ} (hn : n ≠ 0) {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime ∧ p ∣ n) :
    ∏ p ∈ s, p ∣ rad n :=
  Finset.prod_dvd_prod_of_subset _ _ _ fun p hp =>
    Nat.mem_primeFactors.mpr ⟨(hs p hp).1, (hs p hp).2, hn⟩

lemma three_primes_not_dvd {n q₁ q₂ q₃ : ℕ} (hn : n ≠ 0) (h1 : q₁.Prime) (h2 : q₂.Prime)
    (h3 : q₃.Prime) (d1 : q₁ ∣ n) (d2 : q₂ ∣ n) (d3 : q₃ ∣ n) (n12 : q₁ ≠ q₂) (n13 : q₁ ≠ q₃)
    (n23 : q₂ ≠ q₃) (hr : rad n ≤ 8) : False := by
  have hd := prod_dvd_rad (s := {q₁, q₂, q₃}) hn (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    exacts [⟨h1, d1⟩, ⟨h2, d2⟩, ⟨h3, d3⟩])
  rw [Finset.prod_insert (by simp [n12, n13]), Finset.prod_pair n23] at hd
  have hle := Nat.le_of_dvd (rad_pos n) hd
  have a1 := h1.two_le; have a2 := h2.two_le; have a3 := h3.two_le
  have hq23 : 4 ≤ q₂ * q₃ := Nat.mul_le_mul a2 a3
  have hq1 : q₁ * 4 ≤ 8 := (Nat.mul_le_mul_left q₁ hq23).trans (by nlinarith)
  have hq13 : 4 ≤ q₁ * q₃ := Nat.mul_le_mul a1 a3
  have hq2 : q₂ * 4 ≤ 8 := by
    have : q₁ * q₂ * q₃ = q₂ * (q₁ * q₃) := by ring
    nlinarith
  omega

lemma two_primes_eq {n q₁ q₂ : ℕ} (hn : n ≠ 0) (h1 : q₁.Prime) (h2 : q₂.Prime)
    (d1 : q₁ ∣ n) (d2 : q₂ ∣ n) (n12 : q₁ ≠ q₂) (hr : rad n ≤ 8) :
    (q₁ = 2 ∧ q₂ = 3) ∨ (q₁ = 3 ∧ q₂ = 2) := by
  have hd := prod_dvd_rad (s := {q₁, q₂}) hn (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    exacts [⟨h1, d1⟩, ⟨h2, d2⟩])
  rw [Finset.prod_pair n12] at hd
  have hle := Nat.le_of_dvd (rad_pos n) hd
  have a1 := h1.two_le; have a2 := h2.two_le
  have b1 : q₁ ≤ 4 := by nlinarith
  have b2 : q₂ ≤ 4 := by nlinarith
  interval_cases q₁ <;> interval_cases q₂ <;>
    first | decide | (exfalso; exact n12 rfl) | exact absurd h1 (by decide) |
      exact absurd h2 (by decide)

lemma pow_mod_four_three (j : ℕ) : 3 ^ j % 4 = if j % 2 = 0 then 1 else 3 := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
  · rw [pow_mul, Nat.pow_mod]; norm_num
  · rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num

lemma pow_mod_eight_three (j : ℕ) : 3 ^ j % 8 = 1 ∨ 3 ^ j % 8 = 3 := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
  · left; rw [pow_mul, Nat.pow_mod]; norm_num
  · right; rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num

/-- `2^i + 1 = 3^j ⇒ 3^j ≤ 9`. -/
lemma catalan_a {i j : ℕ} (h : 2 ^ i + 1 = 3 ^ j) : 3 ^ j ≤ 9 := by
  rcases Nat.lt_or_ge i 2 with hi | hi
  · interval_cases i
    · -- 2 = 3^j impossible
      exfalso
      rcases j with _ | j
      · norm_num at h
      · have := congrArg (· % 3) h; simp [pow_succ, Nat.mul_mod] at this
    · rw [← h]; norm_num
  · have h4 : (2 ^ i + 1) % 4 = 1 := by
      have : 4 ∣ 2 ^ i := by
        have := pow_dvd_pow 2 hi; simpa using this
      omega
    rw [h, pow_mod_four_three] at h4
    split_ifs at h4 with hj
    · obtain ⟨k, rfl⟩ : 2 ∣ j := Nat.dvd_of_mod_eq_zero hj
      -- (3^k - 1)(3^k + 1) = 2^i
      have hk1 : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
      have hfac : (3 ^ k - 1) * (3 ^ k + 1) = 2 ^ i := by
        have : 3 ^ (2 * k) = 3 ^ k * 3 ^ k := by rw [two_mul, pow_add]
        zify [hk1] at h this ⊢
        nlinarith
      obtain ⟨u, -, hu⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro _ hfac)
      obtain ⟨v, -, hv⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro_left _ hfac)
      have huv : 2 ^ v = 2 ^ u + 2 := by omega
      have hu1 : u = 1 := by
        rcases u with _ | _ | u
        · have hodd : 3 ^ k % 2 = 1 := Nat.odd_iff.mp (Odd.pow (by decide))
          simp at hu; omega
        · rfl
        · exfalso
          have hv2 : 2 ≤ v := by
            by_contra hv2; push_neg at hv2
            interval_cases v <;> simp [pow_succ] at huv
          have h4u : 4 ∣ 2 ^ (u + 2) := ⟨2 ^ u, by ring⟩
          have h4v : 4 ∣ 2 ^ v := by
            have := pow_dvd_pow 2 hv2; simpa using this
          omega
      subst hu1
      have : 3 ^ k = 3 := by simp at hu; omega
      have hk : k = 1 := by
        rcases k with _ | _ | k
        · simp at this
        · rfl
        · exfalso; have : 3 ^ (k + 2) ≥ 9 := by
            calc 3 ^ (k + 2) = 3 ^ k * 9 := by ring
              _ ≥ 1 * 9 := Nat.mul_le_mul_right _ (Nat.one_le_pow _ _ (by norm_num))
              _ = 9 := by ring
          omega
      subst hk; norm_num
    · omega

/-- `3^j + 1 = 2^i ⇒ 2^i ≤ 4`. -/
lemma catalan_b {i j : ℕ} (h : 3 ^ j + 1 = 2 ^ i) : 2 ^ i ≤ 4 := by
  by_contra hc; push_neg at hc
  have hi : 3 ≤ i := by
    by_contra hi; push_neg at hi; interval_cases i <;> norm_num at hc
  have h8 : 8 ∣ 2 ^ i := by have := pow_dvd_pow 2 hi; simpa using this
  rcases pow_mod_eight_three j with h1 | h1 <;> omega

/-- Coprime `a + b = c` with `rad(abc) ≤ 8` has `c ≤ 9`. -/
lemma small_rad_bound {a b c : ℕ} (hsum : a + b = c) (hcop : Nat.Coprime a b)
    (ha : 0 < a) (hb : 0 < b) (hr : rad (a * b * c) ≤ 8) : c ≤ 9 := by
  have hc : 0 < c := by omega
  have hn : a * b * c ≠ 0 := by positivity
  have hac : Nat.Coprime a c := by
    rw [← hsum]; exact Nat.coprime_self_add_right.mpr hcop
  have hbc : Nat.Coprime b c := by
    rw [← hsum]; exact Nat.coprime_add_self_right.mpr hcop.symm
  -- prime factors of `a`, `b`, `c`
  have dA : ∀ q, q ∣ a → q ∣ a * b * c := fun q h => Dvd.dvd.mul_right (Dvd.dvd.mul_right h _) _
  have dB : ∀ q, q ∣ b → q ∣ a * b * c := fun q h => Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _
  have dC : ∀ q, q ∣ c → q ∣ a * b * c := fun q h => Dvd.dvd.mul_left h _
  have neq : ∀ {x y q r : ℕ}, Nat.Coprime x y → q.Prime → q ∣ x → r ∣ y → q ≠ r := by
    intro x y q r hxy hq hqx hry e
    subst e
    have := Nat.dvd_gcd hqx hry
    rw [hxy.gcd_eq_one] at this
    exact hq.one_lt.ne' (Nat.dvd_one.mp this)
  -- `a = 1` or `b = 1`
  have key : ∀ {x y : ℕ}, x + y = c → Nat.Coprime x y → Nat.Coprime x c → Nat.Coprime y c →
      (∀ q, q ∣ x → q ∣ a * b * c) → (∀ q, q ∣ y → q ∣ a * b * c) → x = 1 → c ≤ 9 := by
    intro x y hxy hcxy hxc hyc dX dY hx1
    subst hx1
    rcases Nat.eq_or_lt_of_le (show 1 ≤ y by omega) with hy | hy
    · omega
    obtain ⟨qy, hqy, hqyd⟩ := Nat.exists_prime_and_dvd (show y ≠ 1 by omega)
    obtain ⟨qc, hqc, hqcd⟩ := Nat.exists_prime_and_dvd (show c ≠ 1 by omega)
    have hne : qy ≠ qc := neq hyc hqy hqyd hqcd
    -- every prime factor of `y` is `qy`, every prime factor of `c` is `qc`
    have onlyY : ∀ {d : ℕ}, d.Prime → d ∣ y → d = qy := by
      intro d hd hdy
      by_contra e
      exact three_primes_not_dvd hn hd hqy hqc (dY d hdy) (dY qy hqyd) (dC qc hqcd) e
        (neq hyc hd hdy hqcd) hne hr
    have onlyC : ∀ {d : ℕ}, d.Prime → d ∣ c → d = qc := by
      intro d hd hdc
      by_contra e
      exact three_primes_not_dvd hn hd hqy hqc (dC d hdc) (dY qy hqyd) (dC qc hqcd)
        (fun e' => (neq hyc hqy hqyd hdc) e'.symm) e hne hr
    obtain ⟨ky, hy'⟩ : ∃ k, y = qy ^ k :=
      ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (by omega : y ≠ 0) onlyY⟩
    obtain ⟨kc, hc'⟩ : ∃ k, c = qc ^ k :=
      ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (by omega : c ≠ 0) onlyC⟩
    rcases two_primes_eq hn hqy hqc (dY qy hqyd) (dC qc hqcd) hne hr with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1] at hy'; rw [e2] at hc'
      have h1 : 2 ^ ky + 1 = 3 ^ kc := by
        rw [← hy', ← hc']; omega
      have := catalan_a h1
      rw [hc']; exact this
    · rw [e1] at hy'; rw [e2] at hc'
      have h1 : 3 ^ ky + 1 = 2 ^ kc := by
        rw [← hy', ← hc']; omega
      have := catalan_b h1
      rw [hc']; exact this.trans (by norm_num)
  by_cases ha1 : a = 1
  · exact key hsum hcop hac hbc dA dB ha1
  by_cases hb1 : b = 1
  · exact key (by rw [add_comm]; exact hsum) hcop.symm hbc hac dB dA hb1
  exfalso
  obtain ⟨qa, hqa, hqad⟩ := Nat.exists_prime_and_dvd ha1
  obtain ⟨qb, hqb, hqbd⟩ := Nat.exists_prime_and_dvd hb1
  obtain ⟨qc, hqc, hqcd⟩ := Nat.exists_prime_and_dvd (show c ≠ 1 by omega)
  exact three_primes_not_dvd hn hqa hqb hqc (dA qa hqad) (dB qb hqbd) (dC qc hqcd)
    (neq hcop hqa hqad hqbd) (neq hac hqa hqad hqcd) (neq hbc hqb hqbd hqcd) hr

/-- **Source postulate `ABC_constant_16_31_verified_alt` (final-file form), proved**: for coprime
`a + b = c ≤ 10^15` with `rad(abc) > 1`, `c < rad(abc)^16.31`. (If `rad ≥ 9` then
`rad^16.31 ≥ 9^16 > 10^15`; if `rad ≤ 8` then `c ≤ 9` by `small_rad_bound`.) -/
theorem ABC_constant_16_31_verified_alt (a b c : ℕ) (hsum : a + b = c) (hcop : Nat.Coprime a b)
    (hc : c ≤ 10 ^ 15) (hrad : rad_abc a b c > 1) :
    (c : ℝ) < (rad_abc a b c : ℝ) ^ (16.31 : ℝ) := by
  unfold rad_abc at *
  set r := rad (a * b * c) with hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hrad.le
  have h16 : (r : ℝ) ^ (16 : ℝ) ≤ (r : ℝ) ^ (16.31 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hr1 (by norm_num)
  rw [show ((16 : ℝ)) = ((16 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h16
  rcases Nat.lt_or_ge r 9 with hr9 | hr9
  · -- small radical
    have ha : 0 < a := by
      rcases Nat.eq_zero_or_pos a with rfl | h
      · exfalso; simp [hr, rad] at hrad
      · exact h
    have hb : 0 < b := by
      rcases Nat.eq_zero_or_pos b with rfl | h
      · exfalso; simp [hr, rad] at hrad
      · exact h
    have hc9 := small_rad_bound hsum hcop ha hb (by omega)
    have h2 : (2 : ℝ) ≤ r := by exact_mod_cast hrad
    have : (9 : ℝ) < (r : ℝ) ^ 16 := by
      calc (9 : ℝ) < 2 ^ 16 := by norm_num
        _ ≤ (r : ℝ) ^ 16 := pow_le_pow_left₀ (by norm_num) h2 _
    have hc' : (c : ℝ) ≤ 9 := by exact_mod_cast hc9
    linarith
  · have h9 : (9 : ℝ) ≤ r := by exact_mod_cast hr9
    have : ((10 ^ 15 : ℕ) : ℝ) < (r : ℝ) ^ 16 := by
      calc ((10 ^ 15 : ℕ) : ℝ) < 9 ^ 16 := by norm_num
        _ ≤ (r : ℝ) ^ 16 := pow_le_pow_left₀ (by norm_num) h9 _
    have hc' : (c : ℝ) ≤ ((10 ^ 15 : ℕ) : ℝ) := by exact_mod_cast hc
    linarith

/-- Corrected version of source `ABC_constant_16_31_verified` / `ABC_constant_verified_10_15`
(source false: `2^16 + 2^16 = 2^17`): with `gcd(a, b) = 1` added, the bound holds. -/
theorem ABC_constant_16_31_verified_coprime (a b c : ℕ) (hsum : a + b = c) (ha : a > 0)
    (hb : b > 0) (hc : c > 0) (hcop : Nat.Coprime a b) (hmax : c ≤ 10 ^ 15)
    (hrad : rad (a * b * c) > 1) : ABCQuality a b c < 16.31 := by
  unfold ABCQuality
  rw [if_pos ⟨hsum, ha, hb, hc⟩, if_pos hrad]
  have h := ABC_constant_16_31_verified_alt a b c hsum hcop hmax hrad
  unfold rad_abc at h
  have hr1 : (1 : ℝ) < rad (a * b * c) := by exact_mod_cast hrad
  have hlr : 0 < Real.log (rad (a * b * c) : ℝ) := Real.log_pos hr1
  rw [div_lt_iff₀ hlr]
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
  have := Real.log_lt_log hc0 h
  rwa [Real.log_rpow (by linarith)] at this

/-- The complete-file form of `ABC_constant_16_31_verified_alt` (no `rad > 1`) is **false**:
`a = 0, b = 1, c = 1` gives `1 < 1^16.31`. -/
theorem ABC_alt_complete_source_false :
    ¬ ∀ a b c : ℕ, a + b = c → Nat.Coprime a b → c ≤ 10 ^ 15 →
      (c : ℝ) < (rad_abc a b c : ℝ) ^ (16.31 : ℝ) := by
  intro h
  have := h 0 1 1 rfl (by norm_num) (by norm_num)
  simp [rad_abc, rad] at this

/-- The conclusion of source `RH_ABC_link` (and of `effective_ABC_bound`, final-file form) is
**false**: `a = 0, b = 1, c = 1`. So `RH_ABC_link` as stated would prove `¬RH`. -/
theorem RH_ABC_link_conclusion_false :
    ¬ ∃ C : ℝ, C < 16.32 ∧ ∀ a b c : ℕ, a + b = c → Nat.Coprime a b →
      (c : ℝ) < (rad_abc a b c : ℝ) ^ C := by
  rintro ⟨C, -, h⟩
  have := h 0 1 1 rfl (by norm_num)
  simp [rad_abc, rad] at this

/-- Source `effective_ABC_bound` (complete-file form): proved **vacuously** (`not_HypothesisH`). -/
theorem effective_ABC_bound (hH : HypothesisH 3.0) :
    ∃ C : ℝ, C < 16.32 ∧ ∀ a b c : ℕ, a + b = c → a > 0 → b > 0 → c > 0 →
      rad (a * b * c) > 1 → (c : ℝ) < (rad (a * b * c) : ℝ) ^ C :=
  absurd hH (not_HypothesisH _)

/-- Source `effective_ABC_bound` (final-file form): proved **vacuously** (`not_HypothesisH`),
although its conclusion is false (`RH_ABC_link_conclusion_false`). -/
theorem effective_ABC_bound' (hH : HypothesisH 3.0) :
    ∃ C : ℝ, C < 16.32 ∧ ∀ a b c : ℕ, a + b = c → Nat.Coprime a b →
      (c : ℝ) < (rad_abc a b c : ℝ) ^ C :=
  absurd hH (not_HypothesisH _)



/-! ## `|M(x)| ≤ ψ(x)` (source `Mertens_bound_by_Chebyshev`) -/

/-- Source `Mertens_bound_by_Chebyshev` is **false** at `x = 1`: `M(1) = μ(1) = 1`, `ψ(1) = 0`. -/
theorem Mertens_bound_by_Chebyshev_source_false :
    ¬ ∀ x : ℝ, x ≥ 1 → |Mertens x| ≤ ChebyshevPsi x := by
  intro h
  have := h 1 le_rfl
  simp [Mertens, ChebyshevPsi, vonMangoldt, Finset.sum_range_succ] at this
  norm_num at this

/-- Integer Mertens sum. -/
def Mn (X : ℕ) : ℤ := ∑ n ∈ Finset.range (X + 1), μ n

/-- Sum of `μ` over odd `n ≤ X`. -/
def gOdd (X : ℕ) : ℤ := ∑ n ∈ Finset.range (X + 1), if Odd n then μ n else 0

lemma moebius_two_mul (m : ℕ) : μ (2 * m) = if Odd m then -μ m else 0 := by
  split_ifs with hm
  · have hc : Nat.Coprime 2 m := Nat.coprime_two_left.mpr hm
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc,
      ArithmeticFunction.moebius_apply_prime Nat.prime_two]
    ring
  · rw [Nat.not_odd_iff_even] at hm
    obtain ⟨k, rfl⟩ := hm
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    intro hsq
    have := hsq 2 ⟨k, by ring⟩
    simp at this

lemma gOdd_succ (X : ℕ) : gOdd (X + 1) = gOdd X + if Odd (X + 1) then μ (X + 1) else 0 := by
  unfold gOdd; rw [Finset.sum_range_succ]

lemma gOdd_step (X : ℕ) :
    gOdd (X + 1) - gOdd ((X + 1) / 2) = gOdd X - gOdd (X / 2) + μ (X + 1) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' X
  · have h1 : (2 * k + 1) / 2 = k := by omega
    have h2 : 2 * k / 2 = k := by omega
    rw [h1, h2, gOdd_succ, if_pos (odd_two_mul_add_one k)]
    ring
  · have h1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    have h2 : (2 * k + 1) / 2 = k := by omega
    have hne : ¬ Odd (2 * k + 1 + 1) := by
      rw [Nat.not_odd_iff_even]; exact ⟨k + 1, by ring⟩
    rw [h1, h2, gOdd_succ (2 * k + 1), if_neg hne, gOdd_succ k]
    have : (2 * k + 1 + 1) = 2 * (k + 1) := by ring
    rw [this, moebius_two_mul]
    split_ifs <;> ring

theorem Mn_eq (X : ℕ) : Mn X = gOdd X - gOdd (X / 2) := by
  induction X with
  | zero => simp [Mn, gOdd]
  | succ X ih =>
    rw [gOdd_step, ← ih]
    unfold Mn; rw [Finset.sum_range_succ]

lemma gOdd_diff_le (Y d : ℕ) :
    |gOdd (Y + d) - gOdd Y| ≤ (((Y + d + 1) / 2 : ℕ) : ℤ) - (((Y + 1) / 2 : ℕ) : ℤ) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← add_assoc, gOdd_succ]
    have hmu : |(if Odd (Y + d + 1) then μ (Y + d + 1) else 0)| ≤
        if Odd (Y + d + 1) then 1 else 0 := by
      split_ifs
      · exact ArithmeticFunction.abs_moebius_le_one
      · simp
    have hcnt : (((Y + d + 1 + 1) / 2 : ℕ) : ℤ) =
        (((Y + d + 1) / 2 : ℕ) : ℤ) + if Odd (Y + d + 1) then 1 else 0 := by
      obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (Y + d)
      · have ho : Odd (Y + d + 1) := ⟨k, by omega⟩
        rw [if_pos ho]
        have : (Y + d + 1 + 1) / 2 = (Y + d + 1) / 2 + 1 := by omega
        rw [this]; push_cast; ring
      · have ho : ¬ Odd (Y + d + 1) := by
          rw [Nat.not_odd_iff_even]; exact ⟨k + 1, by omega⟩
        rw [if_neg ho]
        have : (Y + d + 1 + 1) / 2 = (Y + d + 1) / 2 := by omega
        rw [this]; simp
    calc |gOdd (Y + d) + (if Odd (Y + d + 1) then μ (Y + d + 1) else 0) - gOdd Y|
        = |(gOdd (Y + d) - gOdd Y) + (if Odd (Y + d + 1) then μ (Y + d + 1) else 0)| := by
          ring_nf
      _ ≤ |gOdd (Y + d) - gOdd Y| + |(if Odd (Y + d + 1) then μ (Y + d + 1) else 0)| :=
          abs_add_le _ _
      _ ≤ _ := by rw [hcnt]; linarith

theorem abs_Mn_le (X : ℕ) :
    |Mn X| ≤ (((X + 1) / 2 : ℕ) : ℤ) - (((X / 2 + 1) / 2 : ℕ) : ℤ) := by
  rw [Mn_eq]
  have := gOdd_diff_le (X / 2) (X - X / 2)
  have e : X / 2 + (X - X / 2) = X := by omega
  rw [e] at this
  exact this

/-! ### Chebyshev's lower bound `ψ(2n) ≥ log C(2n, n)` -/

/-- `ψ` on integers, shifted: `∑_{k < X} Λ(k+1)`. -/
def psiN (X : ℕ) : ℝ := ∑ k ∈ Finset.range X, Λ (k + 1)

lemma ChebyshevPsi_eq_psiN (x : ℝ) : ChebyshevPsi x = psiN ⌊x⌋.toNat := by
  unfold ChebyshevPsi psiN
  rw [Finset.sum_range_succ']
  simp [vonMangoldt]

lemma psiN_mono {X Y : ℕ} (h : X ≤ Y) : psiN X ≤ psiN Y :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h)
    (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)

lemma sum_divisors_swap (f : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range N, ∑ d ∈ (k + 1).divisors, f d =
      ∑ k ∈ Finset.range N, f (k + 1) * ((N / (k + 1) : ℕ) : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (fun k => f (k + 1) * _)]
    have hdiv : ∑ d ∈ (N + 1).divisors, f d =
        ∑ k ∈ Finset.range N, (if (k + 1) ∣ (N + 1) then f (k + 1) else 0) + f (N + 1) := by
      rw [← Nat.filter_dvd_eq_divisors (Nat.succ_ne_zero N), Finset.sum_filter,
        Finset.sum_range_succ', Finset.sum_range_succ]
      simp
    rw [hdiv]
    have hterm : ∀ k ∈ Finset.range N, f (k + 1) * (((N + 1) / (k + 1) : ℕ) : ℝ) =
        f (k + 1) * ((N / (k + 1) : ℕ) : ℝ) + (if (k + 1) ∣ (N + 1) then f (k + 1) else 0) := by
      intro k _
      rw [Nat.succ_div]
      split_ifs <;> push_cast <;> ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Nat.div_self (Nat.succ_pos N)]
    push_cast; ring

lemma log_factorial_eq (N : ℕ) :
    Real.log (N.factorial : ℝ) = ∑ k ∈ Finset.range N, Λ (k + 1) * ((N / (k + 1) : ℕ) : ℝ) := by
  rw [← sum_divisors_swap, ← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod,
    Real.log_prod (fun k _ => by positivity)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ArithmeticFunction.vonMangoldt_sum]

lemma sum_extend (f : ℕ → ℝ) {N M : ℕ} (h : N ≤ M) :
    ∑ k ∈ Finset.range N, f (k + 1) * ((N / (k + 1) : ℕ) : ℝ) =
      ∑ k ∈ Finset.range M, f (k + 1) * ((N / (k + 1) : ℕ) : ℝ) := by
  refine Finset.sum_subset (Finset.range_subset_range.mpr h) fun k _ hk => ?_
  simp only [Finset.mem_range, not_lt] at hk
  rw [Nat.div_eq_of_lt (by omega)]; simp

lemma two_mul_div_le (n d : ℕ) (hd : 0 < d) : 2 * n / d ≤ 2 * (n / d) + 1 := by
  have h1 : n < d * (n / d + 1) := Nat.lt_mul_div_succ n hd
  have : 2 * n / d < 2 * (n / d) + 2 := by
    rw [Nat.div_lt_iff_lt_mul hd]; nlinarith
  omega

theorem log_centralBinom_le_psiN (n : ℕ) :
    Real.log (n.centralBinom : ℝ) ≤ psiN (2 * n) := by
  have hfac : (n.centralBinom : ℝ) * (n.factorial : ℝ) * (n.factorial : ℝ) =
      ((2 * n).factorial : ℝ) := by
    have := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rw [show 2 * n - n = n by omega, ← Nat.centralBinom_eq_two_mul_choose] at this
    exact_mod_cast this
  have hlog : Real.log (n.centralBinom : ℝ) =
      Real.log ((2 * n).factorial : ℝ) - 2 * Real.log (n.factorial : ℝ) := by
    have h1 : (n.centralBinom : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.centralBinom_ne_zero n)
    have h2 : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    rw [← hfac, Real.log_mul (mul_ne_zero h1 h2) h2, Real.log_mul h1 h2]
    ring
  rw [hlog, log_factorial_eq, log_factorial_eq, sum_extend _ (show n ≤ 2 * n by omega),
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  unfold psiN
  refine Finset.sum_le_sum fun k _ => ?_
  have hb := two_mul_div_le n (k + 1) (Nat.succ_pos k)
  have hb' : ((2 * n / (k + 1) : ℕ) : ℝ) ≤ 2 * ((n / (k + 1) : ℕ) : ℝ) + 1 := by
    exact_mod_cast hb
  have hΛ : 0 ≤ Λ (k + 1) := ArithmeticFunction.vonMangoldt_nonneg
  nlinarith

lemma psiN_lower (n : ℕ) (hn : 4 ≤ n) :
    (n : ℝ) * Real.log 4 - Real.log n < psiN (2 * n) := by
  have h := Nat.four_pow_lt_mul_centralBinom n hn
  have h' : ((4 : ℝ) ^ n) < (n : ℝ) * (n.centralBinom : ℝ) := by exact_mod_cast h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlt := Real.log_lt_log (by positivity) h'
  rw [Real.log_pow, Real.log_mul hn0.ne'
    (Nat.cast_ne_zero.mpr (Nat.centralBinom_ne_zero n))] at hlt
  have := log_centralBinom_le_psiN n
  linarith

lemma log_two_gt : (0.6931 : ℝ) < Real.log 2 := by
  have := Real.log_two_gt_d9; linarith

/-- Corrected version of source `Mertens_bound_by_Chebyshev` (source false at `x = 1`):
for `x ≥ 2`, `|M(x)| ≤ ψ(x)`. -/
theorem Mertens_bound_by_Chebyshev (x : ℝ) (hx : x ≥ 2) : |Mertens x| ≤ ChebyshevPsi x := by
  set X := ⌊x⌋.toNat with hX
  have hX2 : 2 ≤ X := by
    have : (2 : ℤ) ≤ ⌊x⌋ := Int.le_floor.mpr (by exact_mod_cast hx)
    omega
  have hM : Mertens x = (Mn X : ℝ) := by
    unfold Mertens Mn; push_cast; rfl
  rw [hM, ChebyshevPsi_eq_psiN, ← hX]
  have hb := abs_Mn_le X
  set c : ℕ := (X + 1) / 2 - (X / 2 + 1) / 2 with hc
  have hcle : (X / 2 + 1) / 2 ≤ (X + 1) / 2 := by omega
  have hb' : |(Mn X : ℝ)| ≤ (c : ℝ) := by
    have : |Mn X| ≤ (c : ℤ) := by rw [hc, Nat.cast_sub hcle]; exact hb
    exact_mod_cast this
  refine hb'.trans ?_
  rcases Nat.lt_or_ge X 8 with h8 | h8
  · -- small `X`
    have hΛ2 : Λ 2 = Real.log 2 := ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
    have hΛ3 : Λ 3 = Real.log 3 := ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three
    have hΛ5 : Λ 5 = Real.log 5 := ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)
    have hΛ1 : 0 ≤ Λ 1 := ArithmeticFunction.vonMangoldt_nonneg
    have hΛ4 : 0 ≤ Λ 4 := ArithmeticFunction.vonMangoldt_nonneg
    have p3 : psiN 3 = Λ 1 + Real.log 2 + Real.log 3 := by
      simp [psiN, Finset.sum_range_succ, hΛ2, hΛ3]
    have p5 : psiN 5 = Λ 1 + Real.log 2 + Real.log 3 + Λ 4 + Real.log 5 := by
      simp [psiN, Finset.sum_range_succ, hΛ2, hΛ3, hΛ5]
    have e1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have l6 : 1 < Real.log 2 + Real.log 3 := by
      rw [← Real.log_mul (by norm_num) (by norm_num), Real.lt_log_iff_exp_lt (by norm_num)]
      linarith
    have l30 : 2 < Real.log 2 + Real.log 3 + Real.log 5 := by
      rw [← Real.log_mul (by norm_num) (by norm_num), ← Real.log_mul (by norm_num) (by norm_num),
        Real.lt_log_iff_exp_lt (by norm_num)]
      have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [this]; nlinarith [Real.exp_pos 1]
    have m0 : 0 ≤ psiN X := Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
    have hp3 : 3 ≤ X → 1 ≤ psiN X := fun h =>
      (show (1 : ℝ) ≤ psiN 3 by rw [p3]; linarith).trans (psiN_mono h)
    have hp5 : 5 ≤ X → 2 ≤ psiN X := fun h =>
      (show (2 : ℝ) ≤ psiN 5 by rw [p5]; linarith).trans (psiN_mono h)
    interval_cases X <;> rw [hc] <;> norm_num <;>
      first | linarith [m0] | linarith [hp3 (by norm_num)] | linarith [hp5 (by norm_num)]
  · set n := X / 2 with hn
    have hn4 : 4 ≤ n := by omega
    have hcn : (c : ℝ) ≤ n / 2 + 1 := by
      have : 2 * c ≤ n + 2 := by omega
      have : (2 * c : ℝ) ≤ n + 2 := by exact_mod_cast this
      linarith
    have hlow := psiN_lower n hn4
    have hmono := psiN_mono (show 2 * n ≤ X by omega)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlogn : Real.log n ≤ Real.log 4 + ((n : ℝ) / 4 - 1) := by
      have h4 : Real.log n = Real.log 4 + Real.log ((n : ℝ) / 4) := by
        rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; ring
      rw [h4]
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n / 4 by positivity)
      linarith
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have hl2 := log_two_gt
    have hn4' : (4 : ℝ) ≤ n := by exact_mod_cast hn4
    have key : (n : ℝ) / 2 + 1 ≤ (n : ℝ) * Real.log 4 - Real.log n := by
      rw [hl4] at hlogn ⊢; nlinarith
    linarith



/-! ## Zero-free region of de la Vallée-Poussin type -/

/-- The source's zero-free-region structure (`Complex.abs s.im` written as `|s.im|`). -/
structure ZeroFreeRegion where
  A : ℝ
  A_pos : A > 0
  region : ∀ s : ℂ, s.re > 1 - A / Real.log (|s.im| + 2) → riemannZeta s ≠ 0

/-- Source `de_la_vallee_poussin_region` (for **every** `A > 0`) is **false**: with `A = 3` the
region contains the trivial zero `s = -2` (`1 - 3/log 2 < -2`). -/
theorem de_la_vallee_poussin_region_source_false :
    ¬ ∀ A : ℝ, A > 0 → ∀ s : ℂ, s.re > 1 - A / Real.log (|s.im| + 2) → riemannZeta s ≠ 0 := by
  intro h
  have hz : riemannZeta (-2) = 0 := by
    have := riemannZeta_neg_two_mul_nat_add_one 0
    norm_num at this; exact this
  refine h 3 (by norm_num) (-2) ?_ hz
  have hl : Real.log 2 < 0.6932 := by have := Real.log_two_lt_d9; linarith
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  simp only [neg_re, re_ofNat, neg_im, im_ofNat, neg_zero, abs_zero, zero_add]
  rw [gt_iff_lt, sub_lt_iff_lt_add, ← sub_lt_iff_lt_add', lt_div_iff₀ hl0]
  nlinarith

/-- **Formalization target** (de la Vallée-Poussin; corrected source statement, also the
content of the source postulate `zero_free_region_exists`): some `A > 0` works.
Proved as `deLaValleePoussin_holds` in `Kerr/Zeta/ClassicalDischarged.lean`. -/
def deLaValleePoussin_statement : Prop := Nonempty ZeroFreeRegion

/-! ## Riemann–von Mangoldt -/

/-- **Formalization target**: `N(T) ~ (T/2π) log(T/2π) − T/2π` (source `ZeroCount_asymptotic`). -/
def ZeroCount_asymptotic_statement : Prop :=
  Tendsto (fun T => ZeroCount T / mainTerm T) atTop (𝓝 1)

/-- **Formalization target**: the uniform Riemann–von Mangoldt formula
`|N(T) − main(T)| ≤ C log T` for `T ≥ 2` (the intended content of source `ZeroCount_bound` /
`riemann_von_mangoldt`). -/
def RiemannVonMangoldt_statement : Prop :=
  ∃ C > 0, ∀ T ≥ 2, |ZeroCount T - mainTerm T| ≤ C * Real.log T

/-! ## Explicit formula, Perron formula -/

/-- `ψ₀(x)`: `ψ` with the jump at a prime power halved. -/
def ChebyshevPsi0 (x : ℝ) : ℝ :=
  ChebyshevPsi x - if ((⌊x⌋ : ℤ) : ℝ) = x then vonMangoldt ⌊x⌋.toNat / 2 else 0

/-- The constant/log terms of the explicit formula. -/
def explicitRHS (x : ℝ) : ℝ := x - ChebyshevPsi0 x - Real.log (2 * π) - (1 / 2) * Real.log (1 - x ^ (-2 : ℤ))

/-- **Formalization target** (von Mangoldt's explicit formula, symmetric summation, zeros with
multiplicity): `∑_{|Im ρ| ≤ T} x^ρ/ρ → x − ψ₀(x) − log 2π − ½ log(1 − x⁻²)`. -/
def ExplicitFormula_statement : Prop :=
  ∀ x : ℝ, 1 < x → Tendsto (fun T => PartialExplicitSum x T) atTop (𝓝 (explicitRHS x : ℂ))

/-- Source `explicitFormulaConverges`, with the source's placeholder existence proof made a
hypothesis. -/
theorem explicitFormulaConverges (x : ℝ) (h : ExplicitFormulaSum x) :
    Tendsto (fun T => PartialExplicitSum x T) atTop (𝓝 (ExplicitFormulaLimit x h)) :=
  Classical.choose_spec h

/-- Corrected version of source `Chebyshev_Explicit_Formula` (source false at prime powers
`x`, where the limit is `ψ₀(x) = ψ(x) − Λ(x)/2`, and the `riemann_hypothesis.lean` version
omits the term `−½ log(1 − x⁻²)`): `ψ` replaced by `ψ₀`, proved from the explicit-formula
target. -/
theorem Chebyshev_Explicit_Formula (hEF : ExplicitFormula_statement) (x : ℝ) (hx : x > 1) :
    ExplicitFormulaSum x ∧
    (∀ ε > 0, ∃ T > 0, ∀ T' ≥ T,
      |ChebyshevPsi0 x - (x - (PartialExplicitSum x T').re - Real.log (2 * π) -
        (1 / 2) * Real.log (1 - x ^ (-2 : ℤ)))| < ε) := by
  have h := hEF x hx
  refine ⟨⟨_, h⟩, fun ε hε => ?_⟩
  have hre := (continuous_re.tendsto _).comp h
  rw [Metric.tendsto_atTop] at hre
  obtain ⟨T, hT⟩ := hre ε hε
  refine ⟨max T 1, by positivity, fun T' hT' => ?_⟩
  have := hT T' (le_trans (le_max_left _ _) hT')
  rw [Real.dist_eq] at this
  simp only [Function.comp_apply, ofReal_re] at this
  unfold explicitRHS at this
  convert this using 2; ring

/-- Source `Chebyshev_Explicit_Formula_simple` (corrected: `ψ₀`). -/
theorem Chebyshev_Explicit_Formula_simple (hEF : ExplicitFormula_statement) (x : ℝ) (hx : x > 1)
    (_hsum : ExplicitFormulaSum x) :
    ∀ ε > 0, ∃ T > 0, ∀ T' ≥ T,
      |ChebyshevPsi0 x - (x - (PartialExplicitSum x T').re - Real.log (2 * π) -
        (1 / 2) * Real.log (1 - x ^ (-2 : ℤ)))| < ε :=
  (Chebyshev_Explicit_Formula hEF x hx).2

/-- Source `Chebyshev_Explicit_Formula` (refined-file form, exact limit), corrected with `ψ₀`. -/
theorem Chebyshev_Explicit_Formula_limit (hEF : ExplicitFormula_statement) (x : ℝ) (hx : x > 1) :
    ∃ sum : ℂ, (ExplicitFormulaSum x ∧ Tendsto (fun T => PartialExplicitSum x T) atTop (𝓝 sum)) ∧
      |ChebyshevPsi0 x - (x - sum.re - Real.log (2 * π) - (1 / 2) * Real.log (1 - x ^ (-2 : ℤ)))|
        = 0 := by
  refine ⟨_, ⟨⟨_, hEF x hx⟩, hEF x hx⟩, ?_⟩
  simp only [ofReal_re, explicitRHS]
  rw [abs_eq_zero]; ring

/-- The truncated Perron integral `(1/2π) ∫_{-T}^{T} (−ζ'/ζ)(c+it) x^{c+it}/(c+it) dt`
(`= (1/2πi) ∫_{c−iT}^{c+iT} … ds`). -/
def PerronTruncated (x c T : ℝ) : ℂ :=
  ((2 * π : ℝ) : ℂ)⁻¹ * ∫ t in (-T)..T,
    (-(deriv riemannZeta (c + t * I)) / riemannZeta (c + t * I)) *
      ((x : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))

/-- The Perron integral as the symmetric limit (real definition replacing the source's
placeholder / `:= 0`). -/
def PerronIntegral (x c : ℝ) (_hc : c > 1) : ℂ := limUnder atTop (fun T => PerronTruncated x c T)

/-- **Formalization target** (Perron's formula for `ψ₀`). -/
def Perron_statement : Prop :=
  ∀ x : ℝ, 1 < x → ∀ c : ℝ, 1 < c →
    Tendsto (fun T => PerronTruncated x c T) atTop (𝓝 (ChebyshevPsi0 x : ℂ))

/-- Corrected version of source `Chebyshev_Perron_Formula` (source false at prime powers, and
false outright with the source's `PerronIntegral := 0`): `ψ₀`, from the Perron target. -/
theorem Chebyshev_Perron_Formula (hP : Perron_statement) (x : ℝ) (hx : x > 1) (c : ℝ)
    (hc : c > 1) : ChebyshevPsi0 x = (PerronIntegral x c hc).re := by
  unfold PerronIntegral
  rw [(hP x hx c hc).limUnder_eq, ofReal_re]

/-- Corrected version of source `Perron_to_Explicit_Formula` / `Perron_equals_Explicit_Formula`
(source omits the term `−½ log(1 − x⁻²)`; its placeholder argument is now the hypothesis `h`),
proved from the two targets. -/
theorem Perron_to_Explicit_Formula (hP : Perron_statement) (hEF : ExplicitFormula_statement)
    (x : ℝ) (hx : x > 1) (c : ℝ) (hc : c > 1) (h : ExplicitFormulaSum x) :
    (PerronIntegral x c hc).re =
      x - (ExplicitFormulaLimit x h).re - Real.log (2 * π) -
        (1 / 2) * Real.log (1 - x ^ (-2 : ℤ)) := by
  rw [← Chebyshev_Perron_Formula hP x hx c hc]
  have hlim : ExplicitFormulaLimit x h = (explicitRHS x : ℂ) :=
    tendsto_nhds_unique (explicitFormulaConverges x h) (hEF x hx)
  rw [hlim, ofReal_re]; unfold explicitRHS; ring

/-! ## Prime number theorem (targets) -/

/-- **Formalization target**: `ψ(x)/x → 1` (source `prime_number_theorem_equivalent`).
Proved as `PNT_holds` in `Kerr/Zeta/ClassicalDischarged.lean`. -/
def PNT_statement : Prop := Tendsto (fun x => ChebyshevPsi x / x) atTop (𝓝 1)

/-- **Formalization target**: de la Vallée-Poussin error term (source `prime_number_theorem_error`).
Proved as `PNT_error_holds` in `Kerr/Zeta/ClassicalDischarged.lean`. -/
def PNT_error_statement : Prop :=
  ∃ C > 0, ∀ x ≥ 2, |ChebyshevPsi x - x| ≤ C * x * Real.exp (-Real.sqrt (Real.log x) / C)

/-! ## Bounds under RH -/

/-- **Formalization target** (von Koch 1901): RH ⇒ `|ψ(x) − x| ≤ C √x log² x`
(source `Chebyshev_bound_under_RH`). -/
def Chebyshev_bound_under_RH_statement : Prop :=
  RiemannHypothesis' → ∃ C > 0, ∀ x ≥ 2, |ChebyshevPsi x - x| ≤ C * Real.sqrt x * (Real.log x) ^ 2

/-- **Open problem** (source `Mertens_bound_under_RH`): RH ⇒ `|M(x)| ≤ C √x log x`. Not known;
the best conditional bounds are of the form `√x · exp((log x)^{1/2+o(1)})`. -/
def Mertens_bound_under_RH_statement : Prop :=
  RiemannHypothesis' → ∃ C > 0, ∀ x ≥ 2, |Mertens x| ≤ C * Real.sqrt x * Real.log x

/-- **Open problem** (source `Liouville_bound_under_RH`). -/
def Liouville_bound_under_RH_statement : Prop :=
  RiemannHypothesis' → ∀ ε : ℝ, ε > 0 → ∃ C > 0, ∀ x ≥ 2,
    |LiouvilleSum x| ≤ C * Real.sqrt x * (Real.log x) ^ (5 / 4 + ε)

/-! ## Hadamard product (target) -/

/-- Nontrivial zeros listed with multiplicity. -/
def ZeroIndex : Type := Σ ρ : {ρ : ℂ // IsNonTrivialZero ρ}, Fin (zeroMultiplicity ρ.1)

/-- The entire completed zeta function `s(s−1)Λ(s)` (`= s(s−1)Λ₀(s) + 1`). -/
def xiEntire (s : ℂ) : ℂ := s * (s - 1) * completedRiemannZeta₀ s + 1

/-- **Formalization target** (Hadamard factorization; corrected version of source
`hadamard_factorization`, whose Γ-factor is inverted relative to the classical formula and
whose product ranges over the type `VerifiedZero`, repeating each zero once per admissible
height). Proved as `hadamard_xi` in `Kerr/Zeta/Hadamard.lean`. -/
def Hadamard_statement : Prop :=
  ∃ A B : ℂ, ∀ s : ℂ, Multipliable (fun i : ZeroIndex => (1 - s / i.1.1) * exp (s / i.1.1)) ∧
    xiEntire s = exp (A + B * s) * ∏' i : ZeroIndex, (1 - s / i.1.1) * exp (s / i.1.1)

/-! ## Lindelöf -/

/-- The source's Lindelöf hypothesis (source writes `|ζ(…)|`, which does not typecheck on `ℂ`;
read as the norm). -/
def LindelofHypothesis : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ C > 0, ∀ t : ℝ, ‖riemannZeta (1 / 2 + t * I)‖ ≤ C * |t| ^ ε

/-- Corrected Lindelöf hypothesis: the bound for `|t| ≥ 1` (at `t = 0` the source's
`C·|t|^ε = 0` would force `ζ(1/2) = 0`). -/
def LindelofHypothesis' : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ C > 0, ∀ t : ℝ, 1 ≤ |t| → ‖riemannZeta (1 / 2 + t * I)‖ ≤ C * |t| ^ ε

/-- **Formalization target** (Littlewood): RH ⇒ Lindelöf (corrected source `RH_implies_Lindelof`). -/
def RH_implies_Lindelof_statement : Prop := RiemannHypothesis' → LindelofHypothesis'

/-- If `ζ(1/2) ≠ 0`, the source's `LindelofHypothesis` is false. -/
theorem not_LindelofHypothesis_of (h : riemannZeta (1 / 2) ≠ 0) : ¬ LindelofHypothesis := by
  intro hL
  obtain ⟨C, -, hC⟩ := hL 1 one_pos
  have := hC 0
  simp only [ofReal_zero, zero_mul, add_zero, abs_zero, Real.rpow_one, mul_zero] at this
  norm_num at this
  exact h this

/-! ## Computational verification -/

/-- Source `SmallRHVerified` (`Complex.abs s.im` written as `|s.im|`). -/
def SmallRHVerified (T : ℝ) : Prop :=
  ∀ s : ℂ, 0 < s.re ∧ s.re < 1 ∧ |s.im| < T → riemannZeta s ≠ 0

/-- Platt (2017)'s verification to height `10^13`, a cited external computation; was the source
postulate `small_rh_verified_platt`, now a `Prop` to be passed as a hypothesis. -/
def PlattVerification : Prop := SmallRHVerified (10 ^ 13)

theorem SmallRHVerified.mono {T T' : ℝ} (h : SmallRHVerified T) (hT : T' ≤ T) :
    SmallRHVerified T' := fun s hs => h s ⟨hs.1, hs.2.1, lt_of_lt_of_le hs.2.2 hT⟩

/-- Source `small_rh_verified_small` as derived in the source from the Platt postulate (the direct
proof is `small_rh_verified_small` below). -/
theorem small_rh_verified_of_platt (hP : PlattVerification) (T : ℝ) (hT : T ≤ 10 ^ 13) :
    SmallRHVerified T := hP.mono hT

/-! ## SHO / quadratic reconstruction (source section 16) -/

/-- Positive ordinates of nontrivial zeros. -/
def ordinateSet : Set ℝ := {γ | 0 < γ ∧ ∃ s : ℂ, IsNonTrivialZero s ∧ s.im = γ}

/-- The `(n+1)`-st positive zero ordinate (distinct ordinates, increasing; `n = 0` gives
`γ₁ ≈ 14.13`). Real definition replacing the source's placeholder; indexing from `0` is my
choice. -/
def zero_ordinate (n : ℕ) : ℝ :=
  sInf {T : ℝ | 0 < T ∧ n + 1 ≤ (ordinateSet ∩ Set.Ioc 0 T).ncard}

/-- Source `SHO_eigenvalue`: `γ_n²/2 − 0.8` (the source's formula; the source's placeholder `else`
branch for `n > 2001052` is replaced by the same formula — my choice). -/
def SHO_eigenvalue (n : ℕ) : ℝ := (zero_ordinate n) ^ 2 / 2 - 0.8

/-- Source postulate `quadratic_reconstruction_verified`: with the source's own definition of
`SHO_eigenvalue` it is a tautology (the difference is `0`), so it is a theorem. -/
theorem quadratic_reconstruction_verified (n : ℕ) (_hn : n ≤ 2001052) :
    |SHO_eigenvalue n - (zero_ordinate n) ^ 2 / 2 + 0.8| < 1e-13 := by
  unfold SHO_eigenvalue; norm_num

/-- Source `SHO_spectrum_equals_zeros`. -/
theorem SHO_spectrum_equals_zeros (n : ℕ) (_hn : n ≤ 2001052) :
    SHO_eigenvalue n = (zero_ordinate n) ^ 2 / 2 - 0.8 := rfl

/-- **Open problem** (source `RH_via_SHO`): finitely many zeros on the line ⇒ RH. Given the
computed zero tables its hypothesis holds, so the statement is then equivalent to RH. -/
def RH_via_SHO_statement : Prop :=
  (∀ n ≤ 2001052, ∃ s : ℂ, IsNonTrivialZero s ∧ s.im = zero_ordinate n ∧ s.re = 1 / 2) →
    RiemannHypothesis'

theorem RH_via_SHO_of_RH (h : RiemannHypothesis') : RH_via_SHO_statement := fun _ => h

/-! ## ABC links (open) -/

/-- Corrected version of the conclusion of source `RH_ABC_link` (source conclusion false for
`a = 0, b = 1, c = 1`): positive coprime triples. A weak form of the ABC conjecture: **open**. -/
def WeakABC (C : ℝ) : Prop :=
  ∀ a b c : ℕ, 0 < a → 0 < b → a + b = c → Nat.Coprime a b → (c : ℝ) < (rad (a * b * c) : ℝ) ^ C

/-- **Open problem**: source `RH_ABC_link`, corrected (`RH ⇒ WeakABC 16.31`). -/
def RH_ABC_link_statement : Prop := RiemannHypothesis' → WeakABC 16.31



/-! ## Growth of summatory functions ⇒ zero-free half-planes

If `A(N) = ∑_{j<N} a_j = O(N^θ)`, the Dirichlet series `∑ a_i (i+1)^{-s}` converges on
`Re s > θ` to a holomorphic function (Abel summation). Applied to `μ` and `Λ − 1` this gives the
"growth ⇒ RH" halves of source `RH_iff_Mertens_Growth` and `RH_iff_Chebyshev_Growth`. -/

/-- `(i+1)^{-s}`. -/
def wpow (s : ℂ) (i : ℕ) : ℂ := ((i : ℂ) + 1) ^ (-s)

/-- Partial sums `A(N) = ∑_{j<N} a j`. -/
def Asum (a : ℕ → ℂ) (N : ℕ) : ℂ := ∑ j ∈ Finset.range N, a j

/-- Abel-summation terms. -/
def dTerm (a : ℕ → ℂ) (s : ℂ) (i : ℕ) : ℂ := (wpow s (i + 1) - wpow s i) * Asum a (i + 1)

/-- The Abel-summed Dirichlet series. -/
def Dser (a : ℕ → ℂ) (s : ℂ) : ℂ := -∑' i, dTerm a s i

lemma norm_ofReal_cpow' {x : ℝ} (hx : 0 < x) (z : ℂ) : ‖(x : ℂ) ^ z‖ = x ^ z.re := by
  exact Complex.norm_cpow_eq_rpow_re_of_pos hx z

lemma wpow_eq (s : ℂ) (i : ℕ) : wpow s i = (((i : ℝ) + 1 : ℝ) : ℂ) ^ (-s) := by
  unfold wpow; push_cast; rfl

lemma norm_wpow (s : ℂ) (i : ℕ) : ‖wpow s i‖ = ((i : ℝ) + 1) ^ (-s.re) := by
  rw [wpow_eq, norm_ofReal_cpow' (by positivity)]; simp

lemma norm_wpow_sub {s : ℂ} (hs : 0 < s.re) (i : ℕ) :
    ‖wpow s (i + 1) - wpow s i‖ ≤ ‖s‖ * ((i : ℝ) + 1) ^ (-s.re - 1) := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  set B : ℝ := ‖s‖ * ((i : ℝ) + 1) ^ (-s.re - 1) with hB
  have key := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun t : ℝ => (t : ℂ) ^ (-s)) (f' := fun t : ℝ => (-s) * (t : ℂ) ^ (-s - 1))
    (a := (i : ℝ) + 1) (b := (i : ℝ) + 1 + 1) (C := B) ?_ ?_ ((i : ℝ) + 1 + 1)
    ⟨by linarith, le_rfl⟩
  · have e1 : wpow s (i + 1) = ((((i : ℝ) + 1 + 1 : ℝ)) : ℂ) ^ (-s) := by
      rw [wpow_eq]; push_cast; ring_nf
    rw [e1, wpow_eq]
    simpa using key
  · intro x hx
    have hx0 : x ≠ 0 := by
      have : (0 : ℝ) < (i : ℝ) + 1 := by positivity
      linarith [hx.1]
    exact (hasDerivAt_ofReal_cpow_const hx0 (neg_ne_zero.mpr hs0)).hasDerivWithinAt
  · intro x hx
    have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hxpos : 0 < x := by linarith [hx.1]
    rw [norm_mul, norm_neg, norm_ofReal_cpow' hxpos]
    simp only [sub_re, neg_re, one_re]
    rw [hB]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hi hx.1 (by linarith)) (norm_nonneg _)

section Abel
variable {a : ℕ → ℂ} {C θ : ℝ}

lemma norm_Asum_succ_le (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hA : ∀ N : ℕ, ‖Asum a N‖ ≤ C * ((N : ℝ) + 1) ^ θ) (i : ℕ) :
    ‖Asum a (i + 1)‖ ≤ C * 2 ^ θ * ((i : ℝ) + 1) ^ θ := by
  refine (hA (i + 1)).trans ?_
  push_cast
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hC
  rw [← Real.mul_rpow (by norm_num) (by positivity)]
  exact Real.rpow_le_rpow (by positivity) (by linarith) hθ

lemma norm_dTerm_le (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hA : ∀ N : ℕ, ‖Asum a N‖ ≤ C * ((N : ℝ) + 1) ^ θ) {s : ℂ} (hs : 0 < s.re) (i : ℕ) :
    ‖dTerm a s i‖ ≤ ‖s‖ * (C * 2 ^ θ) * ((i : ℝ) + 1) ^ (θ - s.re - 1) := by
  unfold dTerm
  rw [norm_mul]
  have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  calc ‖wpow s (i + 1) - wpow s i‖ * ‖Asum a (i + 1)‖
      ≤ (‖s‖ * ((i : ℝ) + 1) ^ (-s.re - 1)) * (C * 2 ^ θ * ((i : ℝ) + 1) ^ θ) :=
        mul_le_mul (norm_wpow_sub hs i) (norm_Asum_succ_le hC hθ hA i) (norm_nonneg _)
          (by positivity)
    _ = ‖s‖ * (C * 2 ^ θ) * (((i : ℝ) + 1) ^ (-s.re - 1) * ((i : ℝ) + 1) ^ θ) := by ring
    _ = ‖s‖ * (C * 2 ^ θ) * ((i : ℝ) + 1) ^ (θ - s.re - 1) := by
        rw [← Real.rpow_add hi]; ring_nf

lemma summable_add_one_rpow' {e : ℝ} (he : e < -1) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ e := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr he)
  refine this.congr fun n => ?_
  push_cast; rfl

lemma summable_dTerm (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hA : ∀ N : ℕ, ‖Asum a N‖ ≤ C * ((N : ℝ) + 1) ^ θ) {s : ℂ} (hs : θ < s.re) :
    Summable (dTerm a s) :=
  Summable.of_norm_bounded ((summable_add_one_rpow' (by linarith)).mul_left _)
    (norm_dTerm_le hC hθ hA (by linarith))

lemma partial_eq (a : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    ∑ i ∈ Finset.range (N + 1), a i * wpow s i =
      wpow s N * Asum a (N + 1) - ∑ i ∈ Finset.range N, dTerm a s i := by
  induction N with
  | zero => simp [Asum]; ring
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (dTerm a s)]
    unfold dTerm Asum
    rw [Finset.sum_range_succ (fun j => a j) (N + 1)]
    ring

theorem tendsto_partial (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hA : ∀ N : ℕ, ‖Asum a N‖ ≤ C * ((N : ℝ) + 1) ^ θ) {s : ℂ} (hs : θ < s.re) :
    Tendsto (fun N => ∑ i ∈ Finset.range N, a i * wpow s i) atTop (𝓝 (Dser a s)) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  simp_rw [partial_eq]
  have hb : Tendsto (fun N : ℕ => wpow s N * Asum a (N + 1)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun N : ℕ => C * 2 ^ θ * ((N : ℝ) + 1) ^ (θ - s.re)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ (-(s.re - θ))) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (by linarith)).comp
          (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      have := h1.const_mul (C * 2 ^ θ)
      simp only [mul_zero] at this
      refine this.congr fun N => ?_
      congr 2; ring
    refine squeeze_zero_norm (fun N => ?_) hlim
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    rw [norm_mul, norm_wpow]
    calc ((N : ℝ) + 1) ^ (-s.re) * ‖Asum a (N + 1)‖
        ≤ ((N : ℝ) + 1) ^ (-s.re) * (C * 2 ^ θ * ((N : ℝ) + 1) ^ θ) :=
          mul_le_mul_of_nonneg_left (norm_Asum_succ_le hC hθ hA N) (by positivity)
      _ = C * 2 ^ θ * (((N : ℝ) + 1) ^ (-s.re) * ((N : ℝ) + 1) ^ θ) := by ring
      _ = C * 2 ^ θ * ((N : ℝ) + 1) ^ (θ - s.re) := by
          rw [← Real.rpow_add hN]; ring_nf
  have hs' := (summable_dTerm hC hθ hA hs).hasSum.tendsto_sum_nat
  have := hb.sub hs'
  rw [zero_sub] at this
  exact this

theorem Dser_eq_tsum (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hA : ∀ N : ℕ, ‖Asum a N‖ ≤ C * ((N : ℝ) + 1) ^ θ) {s : ℂ} (hs : θ < s.re)
    (hsum : Summable fun i => a i * wpow s i) : Dser a s = ∑' i, a i * wpow s i :=
  tendsto_nhds_unique (tendsto_partial hC hθ hA hs) hsum.hasSum.tendsto_sum_nat

theorem Dser_differentiableOn (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hA : ∀ N : ℕ, ‖Asum a N‖ ≤ C * ((N : ℝ) + 1) ^ θ) :
    DifferentiableOn ℂ (Dser a) {s : ℂ | θ < s.re} := by
  intro s₀ hs₀
  have hs₀' : θ < s₀.re := hs₀
  set σ₁ : ℝ := (s₀.re + θ) / 2 with hσ₁
  have hσ₁θ : θ < σ₁ := by rw [hσ₁]; linarith
  set W : Set ℂ := {s | σ₁ < s.re} ∩ {s | ‖s‖ < ‖s₀‖ + 1} with hW
  have hWo : IsOpen W :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_norm continuous_const)
  have hs₀W : s₀ ∈ W := ⟨by simp only [Set.mem_setOf_eq]; rw [hσ₁]; linarith, by simp⟩
  have hdiff : DifferentiableOn ℂ (Dser a) W := by
    show DifferentiableOn ℂ (fun s => -∑' i, dTerm a s i) W
    refine DifferentiableOn.neg ?_
    refine differentiableOn_tsum_of_summable_norm
      (u := fun i : ℕ => (‖s₀‖ + 1) * (C * 2 ^ θ) * ((i : ℝ) + 1) ^ (θ - σ₁ - 1)) ?_ ?_ hWo ?_
    · exact (summable_add_one_rpow' (by linarith)).mul_left _
    · intro i s _
      have hd : ∀ k : ℕ, DifferentiableAt ℂ (fun z : ℂ => wpow z k) s := fun k =>
        (differentiableAt_id.neg).const_cpow (Or.inl (Nat.cast_add_one_ne_zero k))
      exact (((hd (i + 1)).sub (hd i)).mul_const _).differentiableWithinAt
    · intro i s hs
      have hre : σ₁ < s.re := hs.1
      have hnorm : ‖s‖ < ‖s₀‖ + 1 := hs.2
      have hi : (1 : ℝ) ≤ (i : ℝ) + 1 := by linarith [(i.cast_nonneg : (0 : ℝ) ≤ i)]
      calc ‖dTerm a s i‖ ≤ ‖s‖ * (C * 2 ^ θ) * ((i : ℝ) + 1) ^ (θ - s.re - 1) :=
            norm_dTerm_le hC hθ hA (by linarith) i
        _ ≤ (‖s₀‖ + 1) * (C * 2 ^ θ) * ((i : ℝ) + 1) ^ (θ - σ₁ - 1) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right hnorm.le (by positivity)) _
              (by positivity) (by positivity)
            exact Real.rpow_le_rpow_of_exponent_le hi (by linarith)
  exact (hdiff.differentiableAt (hWo.mem_nhds hs₀W)).differentiableWithinAt

end Abel

/-- `L(f, s) = ∑ f(i+1) (i+1)^{-s}` when the L-series converges absolutely. -/
lemma LSeries_eq_tsum_wpow {f : ℕ → ℂ} {s : ℂ} (h : LSeriesSummable f s) :
    Summable (fun i => f (i + 1) * wpow s i) ∧ LSeries f s = ∑' i, f (i + 1) * wpow s i := by
  have hterm : ∀ i : ℕ, LSeries.term f s (i + 1) = f (i + 1) * wpow s i := by
    intro i
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero i), wpow, cpow_neg, div_eq_mul_inv]
    push_cast; rfl
  have hs : Summable (fun i => LSeries.term f s (i + 1)) := (summable_nat_add_iff 1).mpr h
  refine ⟨hs.congr hterm, ?_⟩
  rw [LSeries, Summable.tsum_eq_zero_add h]
  simp only [LSeries.term_zero, zero_add]
  exact tsum_congr hterm

/-- Identity theorem on `{Re s > θ} \ {1}` (three convex pieces, as in hp-proof `ZetaGrowth`). -/
theorem eqOn_halfplane {θ : ℝ} (hθ : θ < 1) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {s | θ < s.re ∧ s ≠ 1})
    (hg : DifferentiableOn ℂ g {s | θ < s.re ∧ s ≠ 1})
    (h : ∀ s : ℂ, 1 < s.re → f s = g s) {s : ℂ} (hs : θ < s.re) (hs1 : s ≠ 1) : f s = g s := by
  have hre : IsOpen {z : ℂ | θ < z.re} := isOpen_lt continuous_const continuous_re
  have piece : ∀ {V : Set ℂ}, Convex ℝ V → IsOpen V → V ⊆ {s | θ < s.re ∧ s ≠ 1} →
      ∀ {z₀ : ℂ}, z₀ ∈ V → 1 < z₀.re → Set.EqOn f g V := by
    intro V hV hVo hsub z₀ hz₀ hz₀re
    have hfa : AnalyticOnNhd ℂ f V := (hf.mono hsub).analyticOnNhd hVo
    have hga : AnalyticOnNhd ℂ g V := (hg.mono hsub).analyticOnNhd hVo
    refine hfa.eqOn_of_preconnected_of_eventuallyEq hga hV.isPreconnected hz₀ ?_
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
    exact Filter.eventuallyEq_of_mem (hopen.mem_nhds hz₀re) fun s hs => h s hs
  rcases lt_trichotomy s.im 0 with him | him | him
  · refine piece (V := {z | θ < z.re} ∩ {z | z.im < 0})
      ((convex_halfSpace_re_gt θ).inter (convex_halfSpace_im_lt 0))
      (hre.inter (isOpen_lt continuous_im continuous_const))
      (fun z hz => ⟨hz.1, fun h => by rw [h] at hz; simp at hz⟩)
      (z₀ := 2 - I) ⟨by simp; linarith, by simp⟩ (by simp) ⟨hs, him⟩
  · have hre1 : s.re ≠ 1 := fun h => hs1 (Complex.ext h (by simpa using him))
    rcases lt_or_gt_of_ne hre1 with h' | h'
    · have hL : IsLinearMap ℝ (fun z : ℂ => z.im - z.re) :=
        ⟨fun x y => by simp only [add_im, add_re]; ring,
         fun c x => by simp only [smul_im, smul_re, smul_eq_mul]; ring⟩
      refine piece (V := {z | θ < z.re} ∩ {z | -1 < z.im - z.re})
        ((convex_halfSpace_re_gt θ).inter (convex_halfSpace_gt hL (-1)))
        (hre.inter (isOpen_lt continuous_const (continuous_im.sub continuous_re)))
        (fun z hz => ⟨hz.1, fun h => by rw [h] at hz; norm_num at hz⟩)
        (z₀ := 2 + 2 * I) ⟨by simp; linarith, by simp⟩ (by simp)
        ⟨hs, by simp only [Set.mem_setOf_eq]; linarith⟩
    · exact h s h'
  · refine piece (V := {z | θ < z.re} ∩ {z | 0 < z.im})
      ((convex_halfSpace_re_gt θ).inter (convex_halfSpace_im_gt 0))
      (hre.inter (isOpen_lt continuous_const continuous_im))
      (fun z hz => ⟨hz.1, fun h => by rw [h] at hz; simp at hz⟩)
      (z₀ := 2 + I) ⟨by simp; linarith, by simp⟩ (by simp) ⟨hs, him⟩

/-- From zero-free half-planes `Re s > 1/2 + δ` (all `δ > 0`) to RH, by the functional
equation's symmetry `ρ ↦ 1 − ρ̄`. -/
theorem RH_of_re_le (h : ∀ δ > 0, ∀ ρ : ℂ, IsNonTrivialZero ρ → ρ.re ≤ 1 / 2 + δ) :
    RiemannHypothesis' := by
  intro ρ hρ
  have h1 : ρ.re ≤ 1 / 2 := le_of_forall_pos_le_add fun δ hδ => h δ hδ ρ hρ
  have h2 : 1 / 2 ≤ ρ.re := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have := h δ hδ _ (zero_symmetry ρ hρ)
    simp only [sub_re, one_re, conj_re] at this
    linarith
  unfold IsOnCriticalLine; linarith

lemma differentiableOn_zeta_V (θ : ℝ) :
    DifferentiableOn ℂ riemannZeta {s | θ < s.re ∧ s ≠ 1} :=
  fun _ hs => (differentiableAt_riemannZeta hs.2).differentiableWithinAt

lemma Mertens_natCast (N : ℕ) :
    Mertens (N : ℝ) = ∑ j ∈ Finset.range N, (μ (j + 1) : ℝ) := by
  unfold Mertens
  rw [Int.floor_natCast, Int.toNat_natCast, Finset.sum_range_succ']
  simp

/-- **Growth ⇒ RH half of source `RH_iff_Mertens_Growth`** (Littlewood's criterion, easy
direction): `M(x) = O(x^{1/2+ε})` for all `ε > 0` implies RH. -/
theorem RH_of_Mertens_growth
    (h : ∀ ε : ℝ, ε > 0 → ∃ C > 0, ∀ x ≥ 1, |Mertens x| ≤ C * x ^ (1 / 2 + ε)) :
    RiemannHypothesis' := by
  apply RH_of_re_le
  intro δ hδ ρ hρ
  by_contra hlt
  push_neg at hlt
  set θ : ℝ := 1 / 2 + δ with hθ
  have hθ1 : θ < 1 := lt_trans hlt hρ.2.2
  have hθ0 : 0 ≤ θ := by positivity
  obtain ⟨C, hC, hM⟩ := h δ hδ
  set a : ℕ → ℂ := fun i => (μ (i + 1) : ℂ) with ha
  have hA : ∀ N : ℕ, ‖Asum a N‖ ≤ C * ((N : ℝ) + 1) ^ θ := by
    intro N
    have hAN : Asum a N = ((Mertens (N : ℝ) : ℝ) : ℂ) := by
      rw [Mertens_natCast]; unfold Asum; push_cast; rfl
    rw [hAN, norm_real, Real.norm_eq_abs]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · rw [Mertens_natCast]; simp; positivity
    · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      refine (hM N hN1).trans (mul_le_mul_of_nonneg_left ?_ hC.le)
      exact Real.rpow_le_rpow (by positivity) (by linarith) hθ0
  -- `ζ · D = 1` on `Re s > 1`
  have hone : ∀ s : ℂ, 1 < s.re → riemannZeta s * Dser a s = 1 := by
    intro s hs
    have hsum : LSeriesSummable (fun n => (μ n : ℂ)) s :=
      ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
    obtain ⟨hsm, hL⟩ := LSeries_eq_tsum_wpow hsum
    rw [Dser_eq_tsum hC.le hθ0 hA (by linarith) hsm, ← hL,
      ← LSeries_one_eq_riemannZeta hs]
    exact LSeries_one_mul_Lseries_moebius hs
  have hDd := Dser_differentiableOn hC.le hθ0 hA
  have hfd : DifferentiableOn ℂ (fun s => riemannZeta s * Dser a s) {s | θ < s.re ∧ s ≠ 1} :=
    (differentiableOn_zeta_V θ).mul (hDd.mono fun s hs => hs.1)
  have := eqOn_halfplane hθ1 hfd (differentiableOn_const 1) hone hlt
    (ne_one_of_re_lt hρ.2.2)
  rw [hρ.1, zero_mul] at this
  exact zero_ne_one this

/-- A zero of an analytic `f` with `f' = h f` (`h` analytic) is not isolated. -/
theorem eventually_zero_of_deriv_eq {f h : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f ρ)
    (hh : AnalyticAt ℂ h ρ) (heq : ∀ᶠ z in 𝓝 ρ, deriv f z = h z * f z) (hz : f ρ = 0) :
    ∀ᶠ z in 𝓝 ρ, f z = 0 := by
  by_contra hne
  obtain ⟨n, g, hg, hgρ, hfg⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  have hn : n ≠ 0 := by
    rintro rfl
    have := hfg.self_of_nhds
    simp only [pow_zero, one_smul] at this
    exact hgρ (this ▸ hz)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hfg' : f =ᶠ[𝓝 ρ] fun z => (z - ρ) ^ (m + 1) * g z := by
    filter_upwards [hfg] with z hz; rw [hz, smul_eq_mul]
  have hder := hfg'.deriv
  have hgev := hg.eventually_analyticAt
  -- the identity `(m+1) g = (z-ρ)(h g - g')` on a punctured neighbourhood
  have hpunct : ∀ᶠ z in 𝓝[≠] ρ,
      ((m + 1 : ℕ) : ℂ) * g z - (z - ρ) * (h z * g z - deriv g z) = 0 := by
    have hev : ∀ᶠ z in 𝓝 ρ, (z ≠ ρ →
        ((m + 1 : ℕ) : ℂ) * g z - (z - ρ) * (h z * g z - deriv g z) = 0) := by
      filter_upwards [heq, hder, hgev, hfg'] with z hz1 hz2 hz3 hz4
      intro hzρ
      have hd : deriv (fun z => (z - ρ) ^ (m + 1) * g z) z =
          ((m + 1 : ℕ) : ℂ) * (z - ρ) ^ m * g z + (z - ρ) ^ (m + 1) * deriv g z := by
        have h1 : HasDerivAt (fun z => (z - ρ) ^ (m + 1)) (((m + 1 : ℕ) : ℂ) * (z - ρ) ^ m) z := by
          simpa using ((hasDerivAt_id z).sub_const ρ).fun_pow (m + 1)
        exact (h1.mul hz3.differentiableAt.hasDerivAt).deriv
      rw [hz1, hd, hz4] at hz2
      have hzr : (z - ρ) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hzρ)
      apply mul_left_cancel₀ hzr
      rw [mul_zero]
      linear_combination (-1 : ℂ) * hz2
    exact eventually_nhdsWithin_iff.mpr hev
  obtain ⟨r, hr, hgr⟩ := hg.exists_ball_analyticOnNhd
  have hg'c : ContinuousAt (deriv g) ρ := (hgr.deriv ρ (Metric.mem_ball_self hr)).continuousAt
  have hcont : ContinuousAt (fun z => ((m + 1 : ℕ) : ℂ) * g z - (z - ρ) * (h z * g z - deriv g z)) ρ :=
    ((continuousAt_const.mul hg.continuousAt).sub
      ((continuousAt_id.sub continuousAt_const).mul
        ((hh.continuousAt.mul hg.continuousAt).sub hg'c)))
  have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := {ρ}ᶜ))
  have h0 : ((m + 1 : ℕ) : ℂ) * g ρ - (ρ - ρ) * (h ρ * g ρ - deriv g ρ) = 0 :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hpunct.mono fun z hz => hz.symm))
  rw [sub_self, zero_mul, sub_zero] at h0
  exact hgρ ((mul_eq_zero.mp h0).resolve_left (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)))

lemma ChebyshevPsi_natCast (N : ℕ) :
    ChebyshevPsi (N : ℝ) = ∑ j ∈ Finset.range N, Λ (j + 1) := by
  unfold ChebyshevPsi
  rw [Int.floor_natCast, Int.toNat_natCast, Finset.sum_range_succ']
  simp [vonMangoldt]

/-- **Growth ⇒ RH half of source `RH_iff_Chebyshev_Growth`**: if
`|ψ(x) − x| ≤ C x^{1/2+ε} log² x` for every `ε > 0`, then RH. -/
theorem RH_of_Chebyshev_growth
    (h : ∀ ε : ℝ, ε > 0 → ∃ C > 0, ∀ x ≥ 2,
      |ChebyshevPsi x - x| ≤ C * x ^ (1 / 2 + ε) * (Real.log x) ^ 2) :
    RiemannHypothesis' := by
  apply RH_of_re_le
  intro δ hδ ρ hρ
  by_contra hlt
  push_neg at hlt
  set θ : ℝ := 1 / 2 + δ with hθ
  have hθ1 : θ < 1 := lt_trans hlt hρ.2.2
  have hθ0 : 0 ≤ θ := by positivity
  obtain ⟨C₀, hC₀, hψ⟩ := h (δ / 2) (by positivity)
  set C : ℝ := max (C₀ * (16 / δ ^ 2)) 1 with hC
  have hC1 : 1 ≤ C := le_max_right _ _
  set a : ℕ → ℂ := fun i => ((Λ (i + 1) : ℝ) : ℂ) - 1 with ha
  have hA : ∀ N : ℕ, ‖Asum a N‖ ≤ C * ((N : ℝ) + 1) ^ θ := by
    intro N
    have hAN : Asum a N = ((ChebyshevPsi (N : ℝ) - N : ℝ) : ℂ) := by
      rw [ChebyshevPsi_natCast]; unfold Asum; simp [ha, Finset.sum_sub_distrib]
    rw [hAN, norm_real, Real.norm_eq_abs]
    rcases Nat.lt_or_ge N 2 with hN | hN
    · interval_cases N
      · rw [ChebyshevPsi_natCast]
        simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, sub_zero, abs_zero]
        positivity
      · rw [ChebyshevPsi_natCast]
        simp only [Finset.sum_range_one, zero_add, ArithmeticFunction.vonMangoldt_apply_one,
          Nat.cast_one]
        have : (1 : ℝ) ≤ 2 ^ θ := Real.one_le_rpow (by norm_num) hθ0
        norm_num
        nlinarith
    · have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
      have hN0 : (0 : ℝ) ≤ N := by positivity
      have hlog0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
      have hlog : Real.log N ≤ (N : ℝ) ^ (δ / 4) / (δ / 4) :=
        Real.log_le_rpow_div hN0 (by positivity)
      have hlog2 : Real.log N ^ 2 ≤ (16 / δ ^ 2) * (N : ℝ) ^ (δ / 2) := by
        have : Real.log N ^ 2 ≤ ((N : ℝ) ^ (δ / 4) / (δ / 4)) ^ 2 := pow_le_pow_left₀ hlog0 hlog 2
        refine this.trans (le_of_eq ?_)
        rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hN0]
        field_simp; ring_nf
      have hpos : (0 : ℝ) < N := by linarith
      calc |ChebyshevPsi N - N| ≤ C₀ * (N : ℝ) ^ (1 / 2 + δ / 2) * Real.log N ^ 2 := hψ N hN2
        _ ≤ C₀ * (N : ℝ) ^ (1 / 2 + δ / 2) * ((16 / δ ^ 2) * (N : ℝ) ^ (δ / 2)) :=
            mul_le_mul_of_nonneg_left hlog2 (by positivity)
        _ = C₀ * (16 / δ ^ 2) * ((N : ℝ) ^ (1 / 2 + δ / 2) * (N : ℝ) ^ (δ / 2)) := by ring
        _ = C₀ * (16 / δ ^ 2) * (N : ℝ) ^ θ := by
            rw [← Real.rpow_add hpos]; congr 2; rw [hθ]; ring
        _ ≤ C * ((N : ℝ) + 1) ^ θ :=
            mul_le_mul (le_max_left _ _) (Real.rpow_le_rpow hN0 (by linarith) hθ0)
              (by positivity) (by positivity)
  -- `ζ (D + ζ) = -ζ'` on `Re s > 1`
  have hone : ∀ s : ℂ, 1 < s.re →
      riemannZeta s * (Dser a s + riemannZeta s) = -deriv riemannZeta s := by
    intro s hs
    have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
    obtain ⟨hsmΛ, hLΛ⟩ := LSeries_eq_tsum_wpow (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)
    obtain ⟨hsm1, hL1⟩ := LSeries_eq_tsum_wpow (f := 1)
      (LSeriesSummable_one_iff.mpr hs)
    have hsum : Summable fun i => a i * wpow s i := by
      refine (hsmΛ.sub hsm1).congr fun i => ?_
      simp [ha, sub_mul]
    have hD : Dser a s = LSeries (fun n => ((Λ n : ℝ) : ℂ)) s - LSeries 1 s := by
      rw [Dser_eq_tsum (by linarith) hθ0 hA (by linarith) hsum, hLΛ, hL1, ← Summable.tsum_sub hsmΛ hsm1]
      refine tsum_congr fun i => ?_
      simp [ha, sub_mul]
    rw [hD, LSeries_one_eq_riemannZeta hs,
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
    field_simp
    ring
  have hDd := Dser_differentiableOn (by linarith) hθ0 hA
  have hζa : AnalyticOnNhd ℂ riemannZeta {s | θ < s.re ∧ s ≠ 1} :=
    (differentiableOn_zeta_V θ).analyticOnNhd
      ((isOpen_lt continuous_const continuous_re).inter isOpen_compl_singleton)
  have hfd : DifferentiableOn ℂ (fun s => riemannZeta s * (Dser a s + riemannZeta s))
      {s | θ < s.re ∧ s ≠ 1} :=
    (differentiableOn_zeta_V θ).mul ((hDd.mono fun s hs => hs.1).add (differentiableOn_zeta_V θ))
  have hgd : DifferentiableOn ℂ (fun s => -deriv riemannZeta s) {s | θ < s.re ∧ s ≠ 1} :=
    hζa.deriv.differentiableOn.neg
  have hVo : IsOpen {s : ℂ | θ < s.re ∧ s ≠ 1} :=
    (isOpen_lt continuous_const continuous_re).inter isOpen_compl_singleton
  have hρV : ρ ∈ {s : ℂ | θ < s.re ∧ s ≠ 1} := ⟨hlt, ne_one_of_re_lt hρ.2.2⟩
  -- the identity holds near `ρ`
  have heq : ∀ᶠ z in 𝓝 ρ, deriv riemannZeta z =
      (-(Dser a z + riemannZeta z)) * riemannZeta z := by
    filter_upwards [hVo.mem_nhds hρV] with z hz
    have := eqOn_halfplane hθ1 hfd hgd hone hz.1 hz.2
    linear_combination this
  have hDa : AnalyticAt ℂ (Dser a) ρ :=
    (hDd.analyticOnNhd (isOpen_lt continuous_const continuous_re)) ρ hlt
  have hev := eventually_zero_of_deriv_eq (hζa ρ hρV)
    ((hDa.add (hζa ρ hρV)).neg) heq hρ.1
  -- contradiction with isolated zeros
  have hiso := eventually_ne_zero_nhdsNE ρ
  have := (hev.filter_mono nhdsWithin_le_nhds).and hiso
  obtain ⟨z, hz1, hz2⟩ := this.exists
  exact hz2 hz1



/-! ### Liouville: `L(λ, s) ζ(s) = ζ(2s)` via Euler products -/

lemma Liouville_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    Liouville (m * n) = Liouville m * Liouville n := by
  unfold Liouville
  rw [if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn,
    ArithmeticFunction.cardFactors_mul hm hn, pow_add]

lemma abs_Liouville_le (n : ℕ) : |Liouville n| ≤ 1 := by
  unfold Liouville; split_ifs <;> simp

/-- `n ↦ λ(n) n^{-s}`, completely multiplicative. -/
def liouHom (s : ℂ) (_hs : s ≠ 0) : ℕ →*₀ ℂ where
  toFun n := (Liouville n : ℂ) * (n : ℂ) ^ (-s)
  map_zero' := by simp [Liouville]
  map_one' := by simp [Liouville]
  map_mul' m n := by
    by_cases hm : m = 0
    · simp [hm, Liouville]
    by_cases hn : n = 0
    · simp [hn, Liouville]
    simp only [Nat.cast_mul]
    rw [Liouville_mul hm hn, natCast_mul_natCast_cpow]
    push_cast; ring

lemma summable_liouHom {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n => ‖liouHom s (ne_zero_of_one_lt_re hs) n‖) := by
  refine (summable_riemannZetaSummand hs).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
  simp only [liouHom, riemannZetaSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  rw [norm_real, Real.norm_eq_abs]; exact abs_Liouville_le n

lemma cpow_neg_sq (p : ℕ) (hp : p ≠ 0) (s : ℂ) :
    (p : ℂ) ^ (-s) * (p : ℂ) ^ (-s) = (p : ℂ) ^ (-(2 * s)) := by
  rw [← cpow_add _ _ (Nat.cast_ne_zero.mpr hp)]; ring_nf

/-- `(∑ λ(n) n^{-s}) · ζ(s) = ζ(2s)` for `Re s > 1`. -/
theorem liouville_mul_zeta {s : ℂ} (hs : 1 < s.re) :
    (∑' n, liouHom s (ne_zero_of_one_lt_re hs) n) * riemannZeta s = riemannZeta (2 * s) := by
  have hs2 : 1 < (2 * s).re := by simp; linarith
  have h1 := EulerProduct.eulerProduct_completely_multiplicative_hasProd (summable_liouHom hs)
  have h2 := riemannZeta_eulerProduct_hasProd hs
  have h3 := riemannZeta_eulerProduct_hasProd hs2
  have h12 := h1.mul h2
  refine h12.unique (h3.congr_fun ?_)
  intro p
  simp only [liouHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, Pi.mul_apply]
  have hp0 : (p : ℕ) ≠ 0 := p.prop.ne_zero
  have hL : Liouville p = -1 := by
    unfold Liouville; rw [if_neg hp0, ArithmeticFunction.cardFactors_apply_prime p.prop]; norm_num
  rw [hL, ← cpow_neg_sq p hp0 s]
  have hx : (1 : ℂ) + (p : ℂ) ^ (-s) ≠ 0 := by
    intro h
    have : ‖(p : ℂ) ^ (-s)‖ < 1 := by
      rw [← ofReal_natCast, norm_ofReal_cpow' (by exact_mod_cast p.prop.pos)]
      simp only [neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (by linarith)
    rw [show (p : ℂ) ^ (-s) = -1 by linear_combination h] at this
    simp at this
  have hy : (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := by
    intro h
    have : ‖(p : ℂ) ^ (-s)‖ < 1 := by
      rw [← ofReal_natCast, norm_ofReal_cpow' (by exact_mod_cast p.prop.pos)]
      simp only [neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (by linarith)
    rw [show (p : ℂ) ^ (-s) = 1 by linear_combination -h] at this
    simp at this
  push_cast
  rw [← mul_inv]
  congr 1
  ring

lemma LiouvilleSum_natCast (N : ℕ) :
    LiouvilleSum (N : ℝ) = ∑ j ∈ Finset.range N, Liouville (j + 1) := by
  unfold LiouvilleSum
  rw [Int.floor_natCast, Int.toNat_natCast, Finset.sum_range_succ']
  simp [Liouville]

/-- **Growth ⇒ RH half of source `RH_iff_Liouville_Growth`**: `L(x) = O(x^{1/2+ε})` for all
`ε > 0` implies RH (via `L(λ, s) ζ(s) = ζ(2s)`). -/
theorem RH_of_Liouville_growth
    (h : ∀ ε : ℝ, ε > 0 → ∃ C > 0, ∀ x ≥ 1, |LiouvilleSum x| ≤ C * x ^ (1 / 2 + ε)) :
    RiemannHypothesis' := by
  apply RH_of_re_le
  intro δ hδ ρ hρ
  by_contra hlt
  push_neg at hlt
  set θ : ℝ := 1 / 2 + δ with hθ
  have hθ1 : θ < 1 := lt_trans hlt hρ.2.2
  have hθ0 : 0 ≤ θ := by positivity
  obtain ⟨C, hC, hM⟩ := h δ hδ
  set a : ℕ → ℂ := fun i => (Liouville (i + 1) : ℂ) with ha
  have hA : ∀ N : ℕ, ‖Asum a N‖ ≤ C * ((N : ℝ) + 1) ^ θ := by
    intro N
    have hAN : Asum a N = ((LiouvilleSum (N : ℝ) : ℝ) : ℂ) := by
      rw [LiouvilleSum_natCast]; unfold Asum; push_cast; rfl
    rw [hAN, norm_real, Real.norm_eq_abs]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · rw [LiouvilleSum_natCast]; simp; positivity
    · have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      refine (hM N hN1).trans (mul_le_mul_of_nonneg_left ?_ hC.le)
      exact Real.rpow_le_rpow (by positivity) (by linarith) hθ0
  have hone : ∀ s : ℂ, 1 < s.re → riemannZeta s * Dser a s = riemannZeta (2 * s) := by
    intro s hs
    have hsumL := (summable_liouHom hs).of_norm
    have hsm : Summable fun i => a i * wpow s i := by
      refine ((summable_nat_add_iff 1).mpr hsumL).congr fun i => ?_
      simp only [liouHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, ha, wpow]
      push_cast; rfl
    rw [Dser_eq_tsum hC.le hθ0 hA (by linarith) hsm, ← liouville_mul_zeta hs, mul_comm,
      Summable.tsum_eq_zero_add hsumL]
    simp only [map_zero, zero_add]
    congr 1
    refine tsum_congr fun i => ?_
    simp only [liouHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, ha, wpow]
    push_cast; rfl
  have hDd := Dser_differentiableOn hC.le hθ0 hA
  have hfd : DifferentiableOn ℂ (fun s => riemannZeta s * Dser a s) {s | θ < s.re ∧ s ≠ 1} :=
    (differentiableOn_zeta_V θ).mul (hDd.mono fun s hs => hs.1)
  have hgd : DifferentiableOn ℂ (fun s => riemannZeta (2 * s)) {s | θ < s.re ∧ s ≠ 1} := by
    intro s hs
    have h2 : 2 * s ≠ 1 := by
      intro e
      have := congrArg Complex.re e
      simp at this
      have h3 : θ < s.re := hs.1
      have h4 : (1 : ℝ) / 2 < s.re := by rw [hθ] at h3; linarith
      linarith
    exact ((differentiableAt_riemannZeta h2).comp s
      ((differentiableAt_id.const_mul (2 : ℂ)))).differentiableWithinAt
  have := eqOn_halfplane hθ1 hfd hgd hone hlt (ne_one_of_re_lt hρ.2.2)
  rw [hρ.1, zero_mul] at this
  have h5 : (1 : ℝ) / 2 < ρ.re := by rw [hθ] at hlt; linarith
  have h2 : 1 < (2 * ρ).re := by simp; linarith
  exact riemannZeta_ne_zero_of_one_lt_re h2 this.symm


/-! ### The equivalences, given the hard directions -/

/-- **Formalization target**: the hard (Littlewood) direction of source `RH_iff_Mertens_Growth`. -/
def RH_implies_Mertens_growth_statement : Prop :=
  RiemannHypothesis' → ∀ ε : ℝ, ε > 0 → ∃ C > 0, ∀ x ≥ 1, |Mertens x| ≤ C * x ^ (1 / 2 + ε)

/-- **Formalization target**: the hard direction of source `RH_iff_Liouville_Growth`. -/
def RH_implies_Liouville_growth_statement : Prop :=
  RiemannHypothesis' → ∀ ε : ℝ, ε > 0 → ∃ C > 0, ∀ x ≥ 1, |LiouvilleSum x| ≤ C * x ^ (1 / 2 + ε)

/-- Source `RH_iff_Mertens_Growth`, with its hard direction as hypothesis. -/
theorem RH_iff_Mertens_Growth (h : RH_implies_Mertens_growth_statement) :
    RiemannHypothesis' ↔
      ∀ ε : ℝ, ε > 0 → ∃ C > 0, ∀ x ≥ 1, |Mertens x| ≤ C * x ^ (1 / 2 + ε) :=
  ⟨h, RH_of_Mertens_growth⟩

/-- Source `RH_iff_Liouville_Growth`, with its hard direction as hypothesis. -/
theorem RH_iff_Liouville_Growth (h : RH_implies_Liouville_growth_statement) :
    RiemannHypothesis' ↔
      ∀ ε : ℝ, ε > 0 → ∃ C > 0, ∀ x ≥ 1, |LiouvilleSum x| ≤ C * x ^ (1 / 2 + ε) :=
  ⟨h, RH_of_Liouville_growth⟩

/-- Source `RH_iff_Chebyshev_Growth`, with von Koch's theorem (target
`Chebyshev_bound_under_RH_statement`) as hypothesis. -/
theorem RH_iff_Chebyshev_Growth (hK : Chebyshev_bound_under_RH_statement) :
    RiemannHypothesis' ↔ ∀ ε : ℝ, ε > 0 → ∃ C > 0, ∀ x ≥ 2,
      |ChebyshevPsi x - x| ≤ C * x ^ (1 / 2 + ε) * (Real.log x) ^ 2 := by
  refine ⟨fun hRH ε hε => ?_, RH_of_Chebyshev_growth⟩
  obtain ⟨C, hC, hb⟩ := hK hRH
  refine ⟨C, hC, fun x hx => (hb x hx).trans ?_⟩
  have hx0 : 0 ≤ x := by linarith
  have hsq : Real.sqrt x ≤ x ^ (1 / 2 + ε) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hl : 0 ≤ (Real.log x) ^ 2 := sq_nonneg _
  calc C * Real.sqrt x * Real.log x ^ 2 ≤ C * x ^ (1 / 2 + ε) * Real.log x ^ 2 := by gcongr



/-! ## Euler–Maclaurin continuation of `ζ` (copied from hp-proof `ZetaGrowth`, `ZetaGrowthNeg`,
`ZetaGrowthEM3`, QJ; unchanged except for namespacing) -/

section EMCopy
open scoped LSeries.notation ArithmeticFunction
namespace ZetaGrowth

/-! ## Target (C): the trivial bound on `Re s ≥ 1 + ε` -/

/-! ## The Euler–Maclaurin remainder terms -/

/-- The Euler–Maclaurin remainder `n^{-s} - ∫_n^{n+1} t^{-s} dt`, with the integral in
closed form `((n+1)^{1-s} - n^{1-s})/(1-s)`. -/
def emTerm (n : ℕ) (s : ℂ) : ℂ :=
  (n : ℂ) ^ (-s) - (((n : ℂ) + 1) ^ (1 - s) - (n : ℂ) ^ (1 - s)) / (1 - s)

/-- The continuation of `ζ` to `Re s > 0`: `1/(s-1) + Σ_{n ≥ 1} emTerm n s`. -/
def zetaAbel (s : ℂ) : ℂ := 1 / (s - 1) + ∑' n : ℕ, emTerm (n + 1) s

/-- `‖x^z‖ = x^{Re z}` for real `x > 0`. -/
theorem norm_ofReal_cpow {x : ℝ} (hx : 0 < x) (z : ℂ) : ‖(x : ℂ) ^ z‖ = x ^ z.re := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]

/-- **Mean-value bound** for the remainder: `‖emTerm n s‖ ≤ ‖s‖ · n^{-Re s - 1}` for `n ≥ 1`,
`Re s > 0`, `s ≠ 1`. -/
theorem norm_emTerm_le {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖emTerm n s‖ ≤ ‖s‖ * (n : ℝ) ^ (-s.re - 1) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs0' : s ≠ 0 := fun h => by rw [h] at hs0; simp at hs0
  set B : ℝ := ‖s‖ * (n : ℝ) ^ (-s.re - 1) with hB
  have hBnn : 0 ≤ B := by positivity
  -- Step 1: `‖t^{-s} - n^{-s}‖ ≤ B` on `[n, n+1]`, from `‖d/dt t^{-s}‖ = ‖s‖ t^{-Re s-1}`.
  have hψ : ∀ t ∈ Set.Icc (n : ℝ) (n + 1), ‖(t : ℂ) ^ (-s) - (n : ℂ) ^ (-s)‖ ≤ B := by
    intro t ht
    have key := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun t : ℝ => (t : ℂ) ^ (-s)) (f' := fun t : ℝ => (-s) * (t : ℂ) ^ (-s - 1))
      (a := (n : ℝ)) (b := n + 1) (C := B) ?_ ?_ t ht
    · calc ‖(t : ℂ) ^ (-s) - (n : ℂ) ^ (-s)‖ ≤ B * (t - n) := key
        _ ≤ B * 1 := by gcongr; linarith [ht.2]
        _ = B := mul_one B
    · intro x hx
      have hx0 : x ≠ 0 := by linarith [hx.1]
      exact (hasDerivAt_ofReal_cpow_const hx0 (neg_ne_zero.mpr hs0')).hasDerivWithinAt
    · intro x hx
      have hxpos : 0 < x := by linarith [hx.1]
      rw [norm_mul, norm_neg, norm_ofReal_cpow hxpos]
      simp only [sub_re, neg_re, one_re]
      rw [hB]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by linarith) hx.1 (by linarith)) (norm_nonneg _)
  -- Step 2: `φ(t) = t^{1-s}/(1-s) - t·n^{-s}` has `φ' = t^{-s} - n^{-s}`, bounded by `B`.
  have hφ := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun t : ℝ => (t : ℂ) ^ (-s + 1) / (-s + 1) - (t : ℂ) * (n : ℂ) ^ (-s))
    (f' := fun t : ℝ => (t : ℂ) ^ (-s) - (n : ℂ) ^ (-s))
    (a := (n : ℝ)) (b := n + 1) (C := B) ?_ ?_ (n + 1) ⟨by linarith, le_rfl⟩
  · have heq : emTerm n s = -((((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s + 1) / (-s + 1)
        - (((n : ℝ) + 1 : ℝ) : ℂ) * (n : ℂ) ^ (-s)
        - (((n : ℝ) : ℂ) ^ (-s + 1) / (-s + 1) - ((n : ℝ) : ℂ) * (n : ℂ) ^ (-s))) := by
      unfold emTerm
      rw [show (1 : ℂ) - s = -s + 1 by ring]
      push_cast
      ring
    rw [heq, norm_neg]
    simpa using hφ
  · intro x hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s + 1) / (-s + 1)) ((x : ℂ) ^ (-s)) x :=
      hasDerivAt_ofReal_cpow_const' hx0 (by
        intro h
        apply hs1
        linear_combination -h)
    have h2 : HasDerivAt (fun y : ℝ => (y : ℂ) * (n : ℂ) ^ (-s)) ((n : ℂ) ^ (-s)) x := by
      simpa using ((hasDerivAt_id x).ofReal_comp).mul_const ((n : ℂ) ^ (-s))
    exact (h1.sub h2).hasDerivWithinAt
  · intro x hx
    exact hψ x (Set.Ico_subset_Icc_self hx)

/-- The shifted `p`-series `Σ (n+1)^a` converges for `a < -1`. -/
theorem summable_add_one_rpow {a : ℝ} (ha : a < -1) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ a := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr ha)
  refine this.congr fun n => ?_
  push_cast
  rfl

/-- The remainder series converges absolutely on `Re s > 0`, `s ≠ 1`. -/
theorem summable_emTerm {s : ℂ} (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    Summable fun n : ℕ => emTerm (n + 1) s := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => ‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1))
    ((summable_add_one_rpow (by linarith)).mul_left _) fun n => ?_
  have := norm_emTerm_le hs0 hs1 (n := n + 1) (by omega)
  push_cast at this
  exact this

/-- Partial sums of the remainder series telescope:
`Σ_{i<N} emTerm (i+1) s = Σ_{i<N} (i+1)^{-s} - ((N+1)^{1-s} - 1)/(1-s)`. -/
theorem sum_emTerm (s : ℂ) (N : ℕ) :
    ∑ i ∈ Finset.range N, emTerm (i + 1) s
      = ∑ i ∈ Finset.range N, ((i : ℂ) + 1) ^ (-s) - (((N : ℂ) + 1) ^ (1 - s) - 1) / (1 - s) := by
  have h := Finset.sum_range_sub (fun i : ℕ => ((i : ℂ) + 1) ^ (1 - s)) N
  simp only [Nat.cast_zero, zero_add, one_cpow] at h
  rw [← h, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [emTerm]
  push_cast
  ring

/-- Each remainder term is holomorphic in `s` away from `s = 1` (for `n ≥ 1`). -/
theorem emTerm_differentiableAt {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (fun z => emTerm n z) s := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : (n : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  unfold emTerm
  apply DifferentiableAt.sub
  · exact (differentiableAt_id.neg).const_cpow (Or.inl hn0)
  · refine DifferentiableAt.div ?_ ((differentiableAt_const _).sub differentiableAt_id) h1s
    exact (((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl hn1)).sub
      (((differentiableAt_const _).sub differentiableAt_id).const_cpow (Or.inl hn0))

/-- The right half-plane with the pole removed. -/
def rightHalf : Set ℂ := {s : ℂ | 0 < s.re ∧ s ≠ 1}

/-- `zetaAbel` is holomorphic on `Re s > 0`, `s ≠ 1` (locally uniform convergence). -/
theorem zetaAbel_differentiableOn : DifferentiableOn ℂ zetaAbel rightHalf := by
  intro s₀ hs₀
  obtain ⟨h0, h1⟩ := hs₀
  set W : Set ℂ := ({s | s₀.re / 2 < s.re} ∩ {s | ‖s‖ < ‖s₀‖ + 1}) ∩ {1}ᶜ with hW
  have hWo : IsOpen W :=
    ((isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)).inter isOpen_compl_singleton
  have hs₀W : s₀ ∈ W := ⟨⟨by simp only [Set.mem_setOf_eq]; linarith, by simp⟩, h1⟩
  have hdiff : DifferentiableOn ℂ zetaAbel W := by
    show DifferentiableOn ℂ (fun s => 1 / (s - 1) + ∑' n : ℕ, emTerm (n + 1) s) W
    apply DifferentiableOn.add
    · intro s hs
      have hd : DifferentiableAt ℂ (fun z : ℂ => 1 / (z - 1)) s :=
        (differentiableAt_const (1 : ℂ)).div (differentiableAt_id.sub_const 1)
          (sub_ne_zero.mpr hs.2)
      exact hd.differentiableWithinAt
    · refine differentiableOn_tsum_of_summable_norm
        (u := fun n : ℕ => (‖s₀‖ + 1) * ((n : ℝ) + 1) ^ (-(s₀.re / 2) - 1)) ?_ ?_ hWo ?_
      · exact (summable_add_one_rpow (by linarith)).mul_left _
      · intro n s hs
        exact (emTerm_differentiableAt (by omega) hs.2).differentiableWithinAt
      · intro n s hs
        have hre : s₀.re / 2 < s.re := hs.1.1
        have hnorm : ‖s‖ < ‖s₀‖ + 1 := hs.1.2
        calc ‖emTerm (n + 1) s‖ ≤ ‖s‖ * ((n + 1 : ℕ) : ℝ) ^ (-s.re - 1) :=
              norm_emTerm_le (by linarith) hs.2 (by omega)
          _ ≤ (‖s₀‖ + 1) * ((n : ℝ) + 1) ^ (-(s₀.re / 2) - 1) := by
              push_cast
              apply mul_le_mul hnorm.le _ (by positivity) (by positivity)
              exact Real.rpow_le_rpow_of_exponent_le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
                (by linarith)
  exact (hdiff.differentiableAt (hWo.mem_nhds hs₀W)).differentiableWithinAt

/-- For `Re s > 1`, `zetaAbel s = ζ s` (the Dirichlet series, Abel-summed). -/
theorem zetaAbel_eq_zeta_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : zetaAbel s = riemannZeta s := by
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
  have hs0 : 0 < s.re := by linarith
  have hsum : Summable fun n : ℕ => emTerm (n + 1) s := summable_emTerm hs0 hs1
  -- the Dirichlet series
  have hζ : HasSum (fun n : ℕ => ((n : ℂ) + 1) ^ (-s)) (riemannZeta s) := by
    have hsm : Summable fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s := by
      have := (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs)
      refine this.congr fun n => ?_
      push_cast
      rfl
    have := hsm.hasSum
    rw [← zeta_eq_tsum_one_div_nat_add_one_cpow hs] at this
    refine this.congr_fun fun n => ?_
    rw [cpow_neg, one_div]
  -- the boundary term tends to zero
  have hpow : Tendsto (fun N : ℕ => ((N : ℂ) + 1) ^ (1 - s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h1 : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ (-(s.re - 1))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by linarith)).comp
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    refine h1.congr fun N => ?_
    have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    rw [show ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    congr 1
    simp only [sub_re, one_re]
    ring
  -- partial sums converge to `ζ s - (0 - 1)/(1 - s)`
  have hpart : Tendsto (fun N => ∑ i ∈ Finset.range N, emTerm (i + 1) s) atTop
      (𝓝 (riemannZeta s - (0 - 1) / (1 - s))) := by
    simp_rw [sum_emTerm]
    exact hζ.tendsto_sum_nat.sub ((hpow.sub_const 1).div_const (1 - s))
  have hS : HasSum (fun n : ℕ => emTerm (n + 1) s) (riemannZeta s - (0 - 1) / (1 - s)) :=
    hsum.hasSum_iff_tendsto_nat.mpr hpart
  rw [zetaAbel, hS.tsum_eq]
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp
  ring

/-- Identity-theorem step: on a convex open `V ⊆ rightHalf` containing a point of `Re s > 1`,
`ζ = zetaAbel`. -/
theorem eqOn_zeta_zetaAbel_of_convex {V : Set ℂ} (hV : Convex ℝ V) (hVo : IsOpen V)
    (hsub : V ⊆ rightHalf) {z₀ : ℂ} (hz₀ : z₀ ∈ V) (hz₀re : 1 < z₀.re) :
    Set.EqOn riemannZeta zetaAbel V := by
  have hζ : AnalyticOnNhd ℂ riemannZeta V :=
    DifferentiableOn.analyticOnNhd
      (fun s hs => (differentiableAt_riemannZeta (hsub hs).2).differentiableWithinAt) hVo
  have hA : AnalyticOnNhd ℂ zetaAbel V := (zetaAbel_differentiableOn.mono hsub).analyticOnNhd hVo
  refine hζ.eqOn_of_preconnected_of_eventuallyEq hA hV.isPreconnected hz₀ ?_
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  exact Filter.eventuallyEq_of_mem (hopen.mem_nhds hz₀re)
    fun s hs => (zetaAbel_eq_zeta_of_one_lt_re hs).symm

/-- **The continuation identity.** For `Re s > 0`, `s ≠ 1`:
`ζ(s) = 1/(s-1) + Σ_{n≥1} (n^{-s} - ((n+1)^{1-s} - n^{1-s})/(1-s))`. -/
theorem zeta_eq_zetaAbel {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) : riemannZeta s = zetaAbel s := by
  have hre : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  rcases lt_trichotomy s.im 0 with him | him | him
  · -- lower half-plane, `z₀ = 2 - I`
    refine eqOn_zeta_zetaAbel_of_convex (V := {z | 0 < z.re} ∩ {z | z.im < 0})
      ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0))
      (hre.inter (isOpen_lt continuous_im continuous_const))
      (fun z hz => ⟨hz.1, fun h => by rw [h] at hz; simp at hz⟩)
      (z₀ := 2 - I) ⟨by simp, by simp⟩ (by simp) ⟨hs, him⟩
  · -- real axis: either `Re s > 1` (Dirichlet series) or `0 < Re s < 1`
    have hre1 : s.re ≠ 1 := fun h => hs1 (Complex.ext h (by simpa using him))
    rcases lt_or_gt_of_ne hre1 with h | h
    · -- `0 < s < 1`: use the convex set `{Re > 0} ∩ {Re - 1 < Im}`, `z₀ = 2 + 2I`
      have hL : IsLinearMap ℝ (fun z : ℂ => z.im - z.re) :=
        ⟨fun x y => by simp only [add_im, add_re]; ring,
         fun c x => by simp only [smul_im, smul_re, smul_eq_mul]; ring⟩
      refine eqOn_zeta_zetaAbel_of_convex (V := {z | 0 < z.re} ∩ {z | -1 < z.im - z.re})
        ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_gt hL (-1)))
        (hre.inter (isOpen_lt continuous_const (continuous_im.sub continuous_re)))
        (fun z hz => ⟨hz.1, fun h => by rw [h] at hz; norm_num at hz⟩)
        (z₀ := 2 + 2 * I) ⟨by simp, by simp⟩ (by simp)
        ⟨hs, by simp only [Set.mem_setOf_eq]; linarith⟩
    · exact (zetaAbel_eq_zeta_of_one_lt_re h).symm
  · -- upper half-plane, `z₀ = 2 + I`
    refine eqOn_zeta_zetaAbel_of_convex (V := {z | 0 < z.re} ∩ {z | 0 < z.im})
      ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0))
      (hre.inter (isOpen_lt continuous_const continuous_im))
      (fun z hz => ⟨hz.1, fun h => by rw [h] at hz; simp at hz⟩)
      (z₀ := 2 + I) ⟨by simp, by simp⟩ (by simp) ⟨hs, him⟩

/-! ## The telescoping `p`-series bound `Σ (n+1)^{-(1+p)} ≤ 1 + 1/p` -/

/-- Mean-value step: `(x+1)^{-(1+p)} ≤ (x^{-p} - (x+1)^{-p})/p` for `x ≥ 1`, `p > 0`. -/
theorem rpow_add_one_le_telescope {p : ℝ} (hp : 0 < p) {x : ℝ} (hx : 1 ≤ x) :
    (x + 1) ^ (-(1 + p)) ≤ (x ^ (-p) - (x + 1) ^ (-p)) / p := by
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ (-p))
    (fun t => (-p) * t ^ (-p - 1)) (by linarith : x < x + 1)
    (fun t ht => (Real.hasDerivAt_rpow_const
      (Or.inl (by linarith [ht.1] : t ≠ 0))).continuousAt.continuousWithinAt)
    (fun t ht => Real.hasDerivAt_rpow_const (Or.inl (by linarith [ht.1] : t ≠ 0)))
  rw [add_sub_cancel_left, div_one] at hcd
  have hc1 : (x + 1) ^ (-p - 1) ≤ c ^ (-p - 1) :=
    Real.rpow_le_rpow_of_nonpos (by linarith [hc.1]) hc.2.le (by linarith)
  rw [show -(1 + p) = -p - 1 by ring, le_div_iff₀ hp]
  nlinarith [hcd, hc1]



/-- Specialization of `rpow_add_one_le_telescope` to `p = 1/2`. -/
theorem rpow_neg_three_half_le_telescope {x : ℝ} (hx : 1 ≤ x) :
    (x + 1) ^ (-(3 / 2 : ℝ)) ≤ 2 * (x ^ (-(1 / 2 : ℝ)) - (x + 1) ^ (-(1 / 2 : ℝ))) := by
  have := rpow_add_one_le_telescope (p := 1 / 2) (by norm_num) hx
  rw [show -(1 + (1 / 2 : ℝ)) = -(3 / 2 : ℝ) by norm_num] at this
  calc (x + 1) ^ (-(3 / 2 : ℝ))
      ≤ (x ^ (-(1 / 2 : ℝ)) - (x + 1) ^ (-(1 / 2 : ℝ))) / (1 / 2) := this
    _ = 2 * (x ^ (-(1 / 2 : ℝ)) - (x + 1) ^ (-(1 / 2 : ℝ))) := by ring

/-- Tail bound: `Σ_{m ≥ 0} (m + N + 1)^{-3/2} ≤ 2 N^{-1/2}` for `N ≥ 1`. -/
theorem tsum_tail_rpow_le {N : ℕ} (hN : 1 ≤ N) :
    ∑' m : ℕ, ((m : ℝ) + N + 1) ^ (-(3 / 2 : ℝ)) ≤ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine Real.tsum_le_of_sum_range_le (fun m => by positivity) fun M => ?_
  have htel := Finset.sum_range_sub' (fun m : ℕ => ((m : ℝ) + N) ^ (-(1 / 2 : ℝ))) M
  simp only [Nat.cast_zero, zero_add] at htel
  calc ∑ m ∈ Finset.range M, ((m : ℝ) + N + 1) ^ (-(3 / 2 : ℝ))
      ≤ ∑ m ∈ Finset.range M,
          2 * (((m : ℝ) + N) ^ (-(1 / 2 : ℝ)) - (((m + 1 : ℕ) : ℝ) + N) ^ (-(1 / 2 : ℝ))) := by
        refine Finset.sum_le_sum fun m _ => ?_
        have := rpow_neg_three_half_le_telescope (x := (m : ℝ) + N)
          (by linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)])
        push_cast
        rw [show ((m : ℝ) + 1 + N) = (m : ℝ) + N + 1 by ring]
        exact this
    _ = 2 * ((N : ℝ) ^ (-(1 / 2 : ℝ)) - ((M : ℝ) + N) ^ (-(1 / 2 : ℝ))) := by
        rw [← Finset.mul_sum, htel]
    _ ≤ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
        have : 0 ≤ ((M : ℝ) + N) ^ (-(1 / 2 : ℝ)) := by positivity
        linarith

/-- The shifted `p`-series `Σ (n + N + 1)^a` converges for `a < -1`. -/
theorem summable_add_rpow (N : ℕ) {a : ℝ} (ha : a < -1) :
    Summable fun n : ℕ => ((n : ℝ) + N + 1) ^ a := by
  have := (summable_nat_add_iff N).mpr (summable_add_one_rpow ha)
  refine this.congr fun n => ?_
  push_cast
  rfl

end ZetaGrowth

open ZetaGrowth
namespace ZetaGrowthNeg

/-! ## The second-order Euler–Maclaurin remainder -/

/-- The second-order Euler–Maclaurin remainder: the first-order remainder `emTerm n s` corrected
by the boundary terms `((n+1)^{-s} - n^{-s})/2` and `(s/12)((n+1)^{-s-1} - n^{-s-1})`.
Classically `emTerm₂ n s = -∫_n^{n+1} (P₂(t)/2) s(s+1) t^{-s-2} dt`, `P₂(t) = {t}² - {t} + 1/6`. -/
def emTerm₂ (n : ℕ) (s : ℂ) : ℂ :=
  emTerm n s + (((n : ℂ) + 1) ^ (-s) - (n : ℂ) ^ (-s)) / 2
    + s / 12 * (((n : ℂ) + 1) ^ (-s - 1) - (n : ℂ) ^ (-s - 1))

/-- The second-order continuation of `ζ`: `1/(s-1) + 1/2 + s/12 + Σ_{n ≥ 1} emTerm₂ n s`. -/
def zetaAbel₂ (s : ℂ) : ℂ := 1 / (s - 1) + 1 / 2 + s / 12 + ∑' n : ℕ, emTerm₂ (n + 1) s

/-- The (real) polynomial `Q(x) = ((x-n)² - (x-n) + 1/6)/2 = P₂(x)/2` on `[n, n+1]`. -/
def bern₂ (n : ℕ) (x : ℝ) : ℝ := ((x - n) * (x - n) - (x - n) + 1 / 6) / 2

/-- The antiderivative `H(z) = Q(z)·(-s) z^{-s-1} - (z - n - 1/2) z^{-s} + z^{1-s}/(1-s)` of
`Q(z) s(s+1) z^{-s-2}` (as a function of a complex variable, later restricted to real `z`). -/
def emAnti (n : ℕ) (s : ℂ) (z : ℂ) : ℂ :=
  ((z - n) * (z - n) - (z - n) + 1 / 6) / 2 * (-s) * z ^ (-s - 1)
    - (z - n - 1 / 2) * z ^ (-s) + z ^ (-s + 1) / (-s + 1)

/-- `|Q(x)| ≤ 1/12` for `x ∈ [n, n+1]`. -/
theorem abs_bern₂_le {n : ℕ} {x : ℝ} (hx : x ∈ Set.Icc (n : ℝ) (n + 1)) :
    |bern₂ n x| ≤ 1 / 12 := by
  obtain ⟨h1, h2⟩ := hx
  rw [bern₂, abs_le]
  constructor <;> nlinarith [sq_nonneg (x - n - 1 / 2)]

/-- `emTerm₂ n s = -(H(n+1) - H(n))`. -/
theorem emTerm₂_eq_emAnti (n : ℕ) (s : ℂ) :
    emTerm₂ n s = -(emAnti n s (((n : ℝ) + 1 : ℝ)) - emAnti n s ((n : ℝ))) := by
  unfold emTerm₂ emTerm emAnti
  rw [show (1 : ℂ) - s = -s + 1 by ring]
  push_cast
  ring

/-- `H'(x) = Q(x) s (s+1) x^{-s-2}` for real `x > 0` (`s ≠ 1`). -/
theorem emAnti_hasDerivAt (n : ℕ) {s : ℂ} (hs1 : s ≠ 1) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => emAnti n s t)
      (((bern₂ n x : ℝ) : ℂ) * (s * (s + 1)) * (x : ℂ) ^ (-s - 2)) x := by
  have hxs : (x : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.mpr hx
  have h1s : (-s + 1) ≠ 0 := by
    intro h
    apply hs1
    linear_combination -h
  have hp1 : HasDerivAt (fun z : ℂ => z ^ (-s - 1)) ((-s - 1) * (x : ℂ) ^ (-s - 1 - 1)) x :=
    (Complex.hasStrictDerivAt_cpow_const hxs).hasDerivAt
  have hp0 : HasDerivAt (fun z : ℂ => z ^ (-s)) ((-s) * (x : ℂ) ^ (-s - 1)) x :=
    (Complex.hasStrictDerivAt_cpow_const hxs).hasDerivAt
  have hp2 : HasDerivAt (fun z : ℂ => z ^ (-s + 1)) ((-s + 1) * (x : ℂ) ^ (-s + 1 - 1)) x :=
    (Complex.hasStrictDerivAt_cpow_const hxs).hasDerivAt
  have hlin : HasDerivAt (fun z : ℂ => z - n) 1 x := (hasDerivAt_id' (x := (x : ℂ))).sub_const _
  have hQ : HasDerivAt (fun z : ℂ => ((z - n) * (z - n) - (z - n) + 1 / 6) / 2)
      ((1 * ((x : ℂ) - n) + ((x : ℂ) - n) * 1 - 1) / 2) x :=
    (((hlin.mul hlin).sub hlin).add_const _).div_const _
  have hlin2 : HasDerivAt (fun z : ℂ => z - n - 1 / 2) 1 x := hlin.sub_const _
  have hE := (((hQ.mul_const (-s)).mul hp1).sub (hlin2.mul hp0)).add (hp2.div_const (-s + 1))
  have hE' : HasDerivAt (fun z : ℂ => emAnti n s z) _ x := hE
  refine hE'.comp_ofReal.congr_deriv ?_
  have e1 : (x : ℂ) ^ (-s - 1 - 1) = (x : ℂ) ^ (-s - 2) := by congr 1; ring
  have e2 : (x : ℂ) ^ (-s + 1 - 1) = (x : ℂ) ^ (-s) := by congr 1; ring
  rw [e1, e2, bern₂]
  push_cast
  field_simp
  ring

/-- **Mean-value bound** for the second-order remainder:
`‖emTerm₂ n s‖ ≤ ‖s‖ ‖s+1‖ / 12 · n^{-Re s - 2}` for `n ≥ 1`, `Re s ≥ -2`, `s ≠ 1`. -/
theorem norm_emTerm₂_le {s : ℂ} (hs : -2 ≤ s.re) (hs1 : s ≠ 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖emTerm₂ n s‖ ≤ ‖s‖ * ‖s + 1‖ / 12 * (n : ℝ) ^ (-s.re - 2) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set B : ℝ := ‖s‖ * ‖s + 1‖ / 12 * (n : ℝ) ^ (-s.re - 2) with hB
  have key := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun t : ℝ => emAnti n s t)
    (f' := fun t : ℝ => ((bern₂ n t : ℝ) : ℂ) * (s * (s + 1)) * (t : ℂ) ^ (-s - 2))
    (a := (n : ℝ)) (b := n + 1) (C := B) ?_ ?_ (n + 1) ⟨by linarith, le_rfl⟩
  · rw [emTerm₂_eq_emAnti, norm_neg]
    simpa using key
  · intro x hx
    exact (emAnti_hasDerivAt n hs1 (by linarith [hx.1])).hasDerivWithinAt
  · intro x hx
    have hxpos : 0 < x := by linarith [hx.1]
    show ‖((bern₂ n x : ℝ) : ℂ) * (s * (s + 1)) * (x : ℂ) ^ (-s - 2)‖ ≤ B
    rw [norm_mul, norm_mul, norm_mul, norm_real, Real.norm_eq_abs, norm_ofReal_cpow hxpos]
    have hre : (-s - 2).re = -s.re - 2 := by simp
    rw [hre]
    have hQ := abs_bern₂_le (n := n) (Set.Ico_subset_Icc_self hx)
    have hpow : x ^ (-s.re - 2) ≤ (n : ℝ) ^ (-s.re - 2) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hx.1 (by linarith)
    rw [hB]
    calc |bern₂ n x| * (‖s‖ * ‖s + 1‖) * x ^ (-s.re - 2)
        ≤ (1 / 12) * (‖s‖ * ‖s + 1‖) * (n : ℝ) ^ (-s.re - 2) := by gcongr
      _ = ‖s‖ * ‖s + 1‖ / 12 * (n : ℝ) ^ (-s.re - 2) := by ring

/-- The second-order remainder series converges absolutely on `Re s > -1`, `s ≠ 1`. -/
theorem summable_emTerm₂ {s : ℂ} (hs : -1 < s.re) (hs1 : s ≠ 1) :
    Summable fun n : ℕ => emTerm₂ (n + 1) s := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => ‖s‖ * ‖s + 1‖ / 12 * ((n : ℝ) + 1) ^ (-s.re - 2))
    ((summable_add_one_rpow (by linarith)).mul_left _) fun n => ?_
  have := norm_emTerm₂_le (by linarith) hs1 (n := n + 1) (by omega)
  push_cast at this
  exact this

/-- Each second-order term is holomorphic in `s` away from `s = 1` (for `n ≥ 1`). -/
theorem emTerm₂_differentiableAt {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (fun z => emTerm₂ n z) s := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : (n : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  have hd1 : DifferentiableAt ℂ (fun z : ℂ => -z) s := differentiableAt_id.neg
  have hd2 : DifferentiableAt ℂ (fun z : ℂ => -z - 1) s := hd1.sub_const 1
  unfold emTerm₂
  refine ((emTerm_differentiableAt hn hs1).add ?_).add ?_
  · exact ((hd1.const_cpow (Or.inl hn1)).sub (hd1.const_cpow (Or.inl hn0))).div_const _
  · exact (differentiableAt_id.div_const _).mul
      ((hd2.const_cpow (Or.inl hn1)).sub (hd2.const_cpow (Or.inl hn0)))

/-! ## Telescoping: `zetaAbel₂ = zetaAbel` on `Re s > 0` -/

/-- Partial sums of the second-order series in terms of the first-order ones:
`Σ_{i<N} emTerm₂ (i+1) s = Σ_{i<N} emTerm (i+1) s + ((N+1)^{-s} - 1)/2 + (s/12)((N+1)^{-s-1} - 1)`. -/
theorem sum_emTerm₂_eq (s : ℂ) (N : ℕ) :
    ∑ i ∈ Finset.range N, emTerm₂ (i + 1) s
      = ∑ i ∈ Finset.range N, emTerm (i + 1) s + (((N : ℂ) + 1) ^ (-s) - 1) / 2
        + s / 12 * (((N : ℂ) + 1) ^ (-s - 1) - 1) := by
  have h0 := Finset.sum_range_sub (fun i : ℕ => ((i : ℂ) + 1) ^ (-s)) N
  have h1 := Finset.sum_range_sub (fun i : ℕ => ((i : ℂ) + 1) ^ (-s - 1)) N
  simp only [Nat.cast_zero, zero_add, one_cpow] at h0 h1
  rw [← h0, ← h1, Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [emTerm₂]
  push_cast
  ring

/-- Fully expanded partial sums:
`Σ_{i<N} emTerm₂ (i+1) s = Σ_{i<N} (i+1)^{-s} - ((N+1)^{1-s} - 1)/(1-s) + ((N+1)^{-s} - 1)/2
  + (s/12)((N+1)^{-s-1} - 1)`. -/
theorem sum_emTerm₂ (s : ℂ) (N : ℕ) :
    ∑ i ∈ Finset.range N, emTerm₂ (i + 1) s
      = ∑ i ∈ Finset.range N, ((i : ℂ) + 1) ^ (-s) - (((N : ℂ) + 1) ^ (1 - s) - 1) / (1 - s)
        + (((N : ℂ) + 1) ^ (-s) - 1) / 2 + s / 12 * (((N : ℂ) + 1) ^ (-s - 1) - 1) := by
  rw [sum_emTerm₂_eq, sum_emTerm]

/-- `(N+1)^c → 0` as `N → ∞` when `Re c < 0`. -/
theorem tendsto_add_one_cpow_zero {c : ℂ} (hc : c.re < 0) :
    Tendsto (fun N : ℕ => ((N : ℂ) + 1) ^ c) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ (-(-c.re))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith)).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  refine h1.congr fun N => ?_
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [show ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
    norm_cpow_eq_rpow_re_of_pos hpos, neg_neg]

/-- On `Re s > 0`, `s ≠ 1`, the two continuations agree: `zetaAbel₂ s = zetaAbel s`. -/
theorem zetaAbel₂_eq_zetaAbel {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    zetaAbel₂ s = zetaAbel s := by
  have hsum := summable_emTerm hs hs1
  have hsum₂ := summable_emTerm₂ (by linarith) hs1
  have h0 : Tendsto (fun N : ℕ => ((N : ℂ) + 1) ^ (-s)) atTop (𝓝 0) :=
    tendsto_add_one_cpow_zero (by rw [neg_re]; linarith)
  have h1 : Tendsto (fun N : ℕ => ((N : ℂ) + 1) ^ (-s - 1)) atTop (𝓝 0) :=
    tendsto_add_one_cpow_zero (by rw [sub_re, neg_re, one_re]; linarith)
  have hpart : Tendsto (fun N => ∑ i ∈ Finset.range N, emTerm₂ (i + 1) s) atTop
      (𝓝 ((∑' n : ℕ, emTerm (n + 1) s) + (0 - 1) / 2 + s / 12 * (0 - 1))) := by
    simp_rw [sum_emTerm₂_eq]
    exact (hsum.hasSum.tendsto_sum_nat.add ((h0.sub_const 1).div_const 2)).add
      ((h1.sub_const 1).const_mul (s / 12))
  have hS : HasSum (fun n : ℕ => emTerm₂ (n + 1) s)
      ((∑' n : ℕ, emTerm (n + 1) s) + (0 - 1) / 2 + s / 12 * (0 - 1)) :=
    hsum₂.hasSum_iff_tendsto_nat.mpr hpart
  rw [zetaAbel₂, hS.tsum_eq, zetaAbel]
  ring

/-! ## Holomorphy of `zetaAbel₂` on `Re s > -1` and the identity theorem -/

/-- The half-plane `Re s > -1` with the pole removed. -/
def leftHalf : Set ℂ := {s : ℂ | -1 < s.re ∧ s ≠ 1}

/-- `zetaAbel₂` is holomorphic on `Re s > -1`, `s ≠ 1` (locally uniform convergence). -/
theorem zetaAbel₂_differentiableOn : DifferentiableOn ℂ zetaAbel₂ leftHalf := by
  intro s₀ hs₀
  obtain ⟨h0, h1⟩ := hs₀
  set W : Set ℂ := ({s | (s₀.re - 1) / 2 < s.re} ∩ {s | ‖s‖ < ‖s₀‖ + 1}) ∩ {1}ᶜ with hW
  have hWo : IsOpen W :=
    ((isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)).inter isOpen_compl_singleton
  have hs₀W : s₀ ∈ W := ⟨⟨by simp only [Set.mem_setOf_eq]; linarith, by simp⟩, h1⟩
  have hdiff : DifferentiableOn ℂ zetaAbel₂ W := by
    show DifferentiableOn ℂ
      (fun s => 1 / (s - 1) + 1 / 2 + s / 12 + ∑' n : ℕ, emTerm₂ (n + 1) s) W
    apply DifferentiableOn.add
    · intro s hs
      have hd : DifferentiableAt ℂ (fun z : ℂ => 1 / (z - 1) + 1 / 2 + z / 12) s := by
        fun_prop (disch := exact sub_ne_zero.mpr hs.2)
      exact hd.differentiableWithinAt
    · refine differentiableOn_tsum_of_summable_norm
        (u := fun n : ℕ => (‖s₀‖ + 1) * (‖s₀‖ + 2) / 12 * ((n : ℝ) + 1) ^ (-((s₀.re + 3) / 2)))
        ?_ ?_ hWo ?_
      · exact (summable_add_one_rpow (by linarith)).mul_left _
      · intro n s hs
        exact (emTerm₂_differentiableAt (by omega) hs.2).differentiableWithinAt
      · intro n s hs
        have hre : (s₀.re - 1) / 2 < s.re := hs.1.1
        have hnorm : ‖s‖ < ‖s₀‖ + 1 := hs.1.2
        have hnorm1 : ‖s + 1‖ ≤ ‖s‖ + 1 := by simpa using norm_add_le s 1
        have hA : ‖s‖ * ‖s + 1‖ ≤ (‖s₀‖ + 1) * (‖s₀‖ + 2) :=
          mul_le_mul hnorm.le (by linarith) (norm_nonneg _) (by positivity)
        have hB : ((n : ℝ) + 1) ^ (-s.re - 2) ≤ ((n : ℝ) + 1) ^ (-((s₀.re + 3) / 2)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
            (by linarith)
        calc ‖emTerm₂ (n + 1) s‖ ≤ ‖s‖ * ‖s + 1‖ / 12 * ((n + 1 : ℕ) : ℝ) ^ (-s.re - 2) :=
              norm_emTerm₂_le (by linarith) hs.2 (by omega)
          _ ≤ (‖s₀‖ + 1) * (‖s₀‖ + 2) / 12 * ((n : ℝ) + 1) ^ (-((s₀.re + 3) / 2)) := by
              push_cast
              exact mul_le_mul (div_le_div_of_nonneg_right hA (by norm_num)) hB
                (by positivity) (by positivity)
  exact (hdiff.differentiableAt (hWo.mem_nhds hs₀W)).differentiableWithinAt

/-- Identity-theorem step: on a convex open `V ⊆ leftHalf` containing a point of `Re s > 1`,
`ζ = zetaAbel₂`. -/
theorem eqOn_zeta_zetaAbel₂_of_convex {V : Set ℂ} (hV : Convex ℝ V) (hVo : IsOpen V)
    (hsub : V ⊆ leftHalf) {z₀ : ℂ} (hz₀ : z₀ ∈ V) (hz₀re : 1 < z₀.re) :
    Set.EqOn riemannZeta zetaAbel₂ V := by
  have hζ : AnalyticOnNhd ℂ riemannZeta V :=
    DifferentiableOn.analyticOnNhd
      (fun s hs => (differentiableAt_riemannZeta (hsub hs).2).differentiableWithinAt) hVo
  have hA : AnalyticOnNhd ℂ zetaAbel₂ V :=
    (zetaAbel₂_differentiableOn.mono hsub).analyticOnNhd hVo
  refine hζ.eqOn_of_preconnected_of_eventuallyEq hA hV.isPreconnected hz₀ ?_
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hz₀re) fun s hs => ?_
  have hs' : 1 < s.re := hs
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs'; simp at hs'
  rw [← zetaAbel_eq_zeta_of_one_lt_re hs', zetaAbel₂_eq_zetaAbel (by linarith) hs1]

/-- **The second-order continuation identity.** For `Re s > -1`, `s ≠ 1`:
`ζ(s) = 1/(s-1) + 1/2 + s/12 + Σ_{n≥1} emTerm₂ n s`. -/
theorem zeta_eq_zetaAbel₂ {s : ℂ} (hs : -1 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = zetaAbel₂ s := by
  have hre : IsOpen {z : ℂ | -1 < z.re} := isOpen_lt continuous_const continuous_re
  rcases lt_trichotomy s.im 0 with him | him | him
  · -- lower half-plane, `z₀ = 2 - I`
    refine eqOn_zeta_zetaAbel₂_of_convex (V := {z | -1 < z.re} ∩ {z | z.im < 0})
      ((convex_halfSpace_re_gt (-1)).inter (convex_halfSpace_im_lt 0))
      (hre.inter (isOpen_lt continuous_im continuous_const))
      (fun z hz => ⟨hz.1, fun h => by rw [h] at hz; simp at hz⟩)
      (z₀ := 2 - I) ⟨by norm_num, by simp⟩ (by simp) ⟨hs, him⟩
  · -- real axis: either `Re s > 1` (Dirichlet series) or `-1 < Re s < 1`
    have hre1 : s.re ≠ 1 := fun h => hs1 (Complex.ext h (by simpa using him))
    rcases lt_or_gt_of_ne hre1 with h | h
    · -- `-1 < s < 1`: use the convex set `{Re > -1} ∩ {Re - 1 < Im}`, `z₀ = 2 + 2I`
      have hL : IsLinearMap ℝ (fun z : ℂ => z.im - z.re) :=
        ⟨fun x y => by simp only [add_im, add_re]; ring,
         fun c x => by simp only [smul_im, smul_re, smul_eq_mul]; ring⟩
      refine eqOn_zeta_zetaAbel₂_of_convex (V := {z | -1 < z.re} ∩ {z | -1 < z.im - z.re})
        ((convex_halfSpace_re_gt (-1)).inter (convex_halfSpace_gt hL (-1)))
        (hre.inter (isOpen_lt continuous_const (continuous_im.sub continuous_re)))
        (fun z hz => ⟨hz.1, fun h => by rw [h] at hz; norm_num at hz⟩)
        (z₀ := 2 + 2 * I) ⟨by norm_num, by simp⟩ (by simp)
        ⟨hs, by simp only [Set.mem_setOf_eq]; linarith⟩
    · rw [← zetaAbel_eq_zeta_of_one_lt_re h, zetaAbel₂_eq_zetaAbel (by linarith) hs1]
  · -- upper half-plane, `z₀ = 2 + I`
    refine eqOn_zeta_zetaAbel₂_of_convex (V := {z | -1 < z.re} ∩ {z | 0 < z.im})
      ((convex_halfSpace_re_gt (-1)).inter (convex_halfSpace_im_gt 0))
      (hre.inter (isOpen_lt continuous_const continuous_im))
      (fun z hz => ⟨hz.1, fun h => by rw [h] at hz; simp at hz⟩)
      (z₀ := 2 + I) ⟨by norm_num, by simp⟩ (by simp) ⟨hs, him⟩

/-! ## Splitting the representation at `N` and the growth bound -/


end ZetaGrowthNeg

open ZetaGrowthNeg
namespace ZetaGrowthEM3

/-! ## The fourth-order Euler–Maclaurin remainder -/

/-- The fourth-order Euler–Maclaurin remainder: the second-order remainder `emTerm₂ n s` corrected
by the `P₄`-boundary term `(s(s+1)(s+2)/720)((n+1)^{-s-3} - n^{-s-3})` (the `P₃`-boundary terms
vanish since `P₃(0) = P₃(1) = 0`).  Classically
`emTerm₄ n s = -∫_n^{n+1} (P₄(t)/24) s(s+1)(s+2)(s+3) t^{-s-4} dt`, `P₄(t) = {t}⁴ - 2{t}³ + {t}² - 1/30`. -/
def emTerm₄ (n : ℕ) (s : ℂ) : ℂ :=
  emTerm₂ n s - s * (s + 1) * (s + 2) / 720 * (((n : ℂ) + 1) ^ (-s - 3) - (n : ℂ) ^ (-s - 3))

/-- The fourth-order continuation of `ζ`:
`1/(s-1) + 1/2 + s/12 - s(s+1)(s+2)/720 + Σ_{n ≥ 1} emTerm₄ n s`. -/
def zetaAbel₄ (s : ℂ) : ℂ :=
  1 / (s - 1) + 1 / 2 + s / 12 - s * (s + 1) * (s + 2) / 720 + ∑' n : ℕ, emTerm₄ (n + 1) s

/-- The (real) polynomial `P₄(x-n)/24 = ((x-n)⁴ - 2(x-n)³ + (x-n)² - 1/30)/24` on `[n, n+1]`. -/
def bern₄ (n : ℕ) (x : ℝ) : ℝ :=
  ((x - n) * (x - n) * (x - n) * (x - n) - 2 * ((x - n) * (x - n) * (x - n))
    + (x - n) * (x - n) - 1 / 30) / 24

/-- The antiderivative
`H₄(z) = (P₄/24)·f'''(z) - (P₃/6)·f''(z) + (P₂/2)·f'(z) - P₁·f(z) + F(z)`, `f(z) = z^{-s}`,
`P_k = P_k(z - n)`, of `(P₄(z-n)/24) s(s+1)(s+2)(s+3) z^{-s-4}` (as a function of a complex
variable, later restricted to real `z`). -/
def emAnti₄ (n : ℕ) (s : ℂ) (z : ℂ) : ℂ :=
  ((z - n) * (z - n) * (z - n) * (z - n) - 2 * ((z - n) * (z - n) * (z - n))
      + (z - n) * (z - n) - 1 / 30) / 24 * (-(s * (s + 1) * (s + 2))) * z ^ (-s - 3)
    - ((z - n) * (z - n) * (z - n) - 3 / 2 * ((z - n) * (z - n)) + 1 / 2 * (z - n)) / 6
      * (s * (s + 1)) * z ^ (-s - 2)
    + ((z - n) * (z - n) - (z - n) + 1 / 6) / 2 * (-s) * z ^ (-s - 1)
    - (z - n - 1 / 2) * z ^ (-s) + z ^ (-s + 1) / (-s + 1)

/-- `|P₄(x-n)/24| ≤ 1/720` for `x ∈ [n, n+1]` (since `P₄(u) = u²(u-1)² - 1/30 ∈ [-1/30, 7/240]`). -/
theorem abs_bern₄_le {n : ℕ} {x : ℝ} (hx : x ∈ Set.Icc (n : ℝ) (n + 1)) :
    |bern₄ n x| ≤ 1 / 720 := by
  obtain ⟨h1, h2⟩ := hx
  have hv : -(1 / 4) ≤ (x - n) * (x - n - 1) := by nlinarith [sq_nonneg (x - n - 1 / 2)]
  have hv0 : (x - n) * (x - n - 1) ≤ 0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]
  have hv2 : ((x - n) * (x - n - 1)) * ((x - n) * (x - n - 1)) ≤ 1 / 16 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (x - n) * (x - n - 1) + 1 / 4)
      (by linarith : (0 : ℝ) ≤ -((x - n) * (x - n - 1)))]
  have hv3 : 0 ≤ ((x - n) * (x - n - 1)) * ((x - n) * (x - n - 1)) := mul_self_nonneg _
  have heq : bern₄ n x = (((x - n) * (x - n - 1)) * ((x - n) * (x - n - 1)) - 1 / 30) / 24 := by
    rw [bern₄]; ring
  rw [heq, abs_le]
  constructor <;> linarith

/-- `emTerm₄ n s = -(H₄(n+1) - H₄(n))`. -/
theorem emTerm₄_eq_emAnti₄ (n : ℕ) (s : ℂ) :
    emTerm₄ n s = -(emAnti₄ n s (((n : ℝ) + 1 : ℝ)) - emAnti₄ n s ((n : ℝ))) := by
  unfold emTerm₄ emTerm₂ emTerm emAnti₄
  rw [show (1 : ℂ) - s = -s + 1 by ring]
  push_cast
  ring

/-- `H₄'(x) = (P₄(x-n)/24) s(s+1)(s+2)(s+3) x^{-s-4}` for real `x > 0` (`s ≠ 1`). -/
theorem emAnti₄_hasDerivAt (n : ℕ) {s : ℂ} (hs1 : s ≠ 1) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => emAnti₄ n s t)
      (((bern₄ n x : ℝ) : ℂ) * (s * (s + 1) * (s + 2) * (s + 3)) * (x : ℂ) ^ (-s - 4)) x := by
  have hxs : (x : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.mpr hx
  have h1s : (-s + 1) ≠ 0 := by
    intro h
    apply hs1
    linear_combination -h
  have hp3 : HasDerivAt (fun z : ℂ => z ^ (-s - 3)) ((-s - 3) * (x : ℂ) ^ (-s - 3 - 1)) x :=
    (Complex.hasStrictDerivAt_cpow_const hxs).hasDerivAt
  have hp2 : HasDerivAt (fun z : ℂ => z ^ (-s - 2)) ((-s - 2) * (x : ℂ) ^ (-s - 2 - 1)) x :=
    (Complex.hasStrictDerivAt_cpow_const hxs).hasDerivAt
  have hp1 : HasDerivAt (fun z : ℂ => z ^ (-s - 1)) ((-s - 1) * (x : ℂ) ^ (-s - 1 - 1)) x :=
    (Complex.hasStrictDerivAt_cpow_const hxs).hasDerivAt
  have hp0 : HasDerivAt (fun z : ℂ => z ^ (-s)) ((-s) * (x : ℂ) ^ (-s - 1)) x :=
    (Complex.hasStrictDerivAt_cpow_const hxs).hasDerivAt
  have hpm : HasDerivAt (fun z : ℂ => z ^ (-s + 1)) ((-s + 1) * (x : ℂ) ^ (-s + 1 - 1)) x :=
    (Complex.hasStrictDerivAt_cpow_const hxs).hasDerivAt
  have hu : HasDerivAt (fun z : ℂ => z - n) 1 x := (hasDerivAt_id' (x := (x : ℂ))).sub_const _
  have hu2 : HasDerivAt (fun z : ℂ => (z - n) * (z - n)) _ x := hu.mul hu
  have hu3 : HasDerivAt (fun z : ℂ => (z - n) * (z - n) * (z - n)) _ x := hu2.mul hu
  have hu4 : HasDerivAt (fun z : ℂ => (z - n) * (z - n) * (z - n) * (z - n)) _ x := hu3.mul hu
  have hB4 : HasDerivAt (fun z : ℂ => ((z - n) * (z - n) * (z - n) * (z - n)
      - 2 * ((z - n) * (z - n) * (z - n)) + (z - n) * (z - n) - 1 / 30) / 24) _ x :=
    (((hu4.sub (hu3.const_mul 2)).add hu2).sub_const _).div_const _
  have hB3 : HasDerivAt (fun z : ℂ => ((z - n) * (z - n) * (z - n) - 3 / 2 * ((z - n) * (z - n))
      + 1 / 2 * (z - n)) / 6) _ x :=
    ((hu3.sub (hu2.const_mul _)).add (hu.const_mul _)).div_const _
  have hB2 : HasDerivAt (fun z : ℂ => ((z - n) * (z - n) - (z - n) + 1 / 6) / 2) _ x :=
    ((hu2.sub hu).add_const _).div_const _
  have hB1 : HasDerivAt (fun z : ℂ => z - n - 1 / 2) 1 x := hu.sub_const _
  have hE := (((((hB4.mul_const (-(s * (s + 1) * (s + 2)))).mul hp3).sub
    ((hB3.mul_const (s * (s + 1))).mul hp2)).add ((hB2.mul_const (-s)).mul hp1)).sub
    (hB1.mul hp0)).add (hpm.div_const (-s + 1))
  have hE' : HasDerivAt (fun z : ℂ => emAnti₄ n s z) _ x := hE
  refine hE'.comp_ofReal.congr_deriv ?_
  have e1 : (x : ℂ) ^ (-s - 3 - 1) = (x : ℂ) ^ (-s - 4) := by congr 1; ring
  have e2 : (x : ℂ) ^ (-s - 2 - 1) = (x : ℂ) ^ (-s - 3) := by congr 1; ring
  have e3 : (x : ℂ) ^ (-s - 1 - 1) = (x : ℂ) ^ (-s - 2) := by congr 1; ring
  have e4 : (x : ℂ) ^ (-s + 1 - 1) = (x : ℂ) ^ (-s) := by congr 1; ring
  rw [e1, e2, e3, e4, bern₄]
  push_cast
  field_simp
  ring

/-- **Mean-value bound** for the fourth-order remainder:
`‖emTerm₄ n s‖ ≤ ‖s‖ ‖s+1‖ ‖s+2‖ ‖s+3‖ / 720 · n^{-Re s - 4}` for `n ≥ 1`, `Re s ≥ -4`, `s ≠ 1`. -/
theorem norm_emTerm₄_le {s : ℂ} (hs : -4 ≤ s.re) (hs1 : s ≠ 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖emTerm₄ n s‖ ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ / 720 * (n : ℝ) ^ (-s.re - 4) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set B : ℝ := ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ / 720 * (n : ℝ) ^ (-s.re - 4) with hB
  have key := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun t : ℝ => emAnti₄ n s t)
    (f' := fun t : ℝ =>
      ((bern₄ n t : ℝ) : ℂ) * (s * (s + 1) * (s + 2) * (s + 3)) * (t : ℂ) ^ (-s - 4))
    (a := (n : ℝ)) (b := n + 1) (C := B) ?_ ?_ (n + 1) ⟨by linarith, le_rfl⟩
  · rw [emTerm₄_eq_emAnti₄, norm_neg]
    simpa using key
  · intro x hx
    exact (emAnti₄_hasDerivAt n hs1 (by linarith [hx.1])).hasDerivWithinAt
  · intro x hx
    have hxpos : 0 < x := by linarith [hx.1]
    show ‖((bern₄ n x : ℝ) : ℂ) * (s * (s + 1) * (s + 2) * (s + 3)) * (x : ℂ) ^ (-s - 4)‖ ≤ B
    simp only [norm_mul]
    rw [norm_real, Real.norm_eq_abs, norm_ofReal_cpow hxpos]
    have hre : (-s - 4).re = -s.re - 4 := by simp
    rw [hre]
    have hQ := abs_bern₄_le (n := n) (Set.Ico_subset_Icc_self hx)
    have hpow : x ^ (-s.re - 4) ≤ (n : ℝ) ^ (-s.re - 4) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hx.1 (by linarith)
    rw [hB]
    calc |bern₄ n x| * (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖) * x ^ (-s.re - 4)
        ≤ (1 / 720) * (‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖) * (n : ℝ) ^ (-s.re - 4) := by gcongr
      _ = ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ / 720 * (n : ℝ) ^ (-s.re - 4) := by ring

/-- The fourth-order remainder series converges absolutely on `Re s > -3`, `s ≠ 1`. -/
theorem summable_emTerm₄ {s : ℂ} (hs : -3 < s.re) (hs1 : s ≠ 1) :
    Summable fun n : ℕ => emTerm₄ (n + 1) s := by
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ / 720 * ((n : ℝ) + 1) ^ (-s.re - 4))
    ((summable_add_one_rpow (by linarith)).mul_left _) fun n => ?_
  have := norm_emTerm₄_le (by linarith) hs1 (n := n + 1) (by omega)
  push_cast at this
  exact this

/-- Each fourth-order term is holomorphic in `s` away from `s = 1` (for `n ≥ 1`). -/
theorem emTerm₄_differentiableAt {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (fun z => emTerm₄ n z) s := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1 : (n : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
  have hd3 : DifferentiableAt ℂ (fun z : ℂ => -z - 3) s := differentiableAt_id.neg.sub_const 3
  have hpoly : DifferentiableAt ℂ (fun z : ℂ => z * (z + 1) * (z + 2) / 720) s :=
    ((differentiableAt_id.mul (differentiableAt_id.add_const 1)).mul
      (differentiableAt_id.add_const 2)).div_const _
  unfold emTerm₄
  refine (emTerm₂_differentiableAt hn hs1).sub (hpoly.mul ?_)
  exact (hd3.const_cpow (Or.inl hn1)).sub (hd3.const_cpow (Or.inl hn0))

/-! ## Telescoping: `zetaAbel₄ = zetaAbel₂` on `Re s > -1` -/

/-- Partial sums of the fourth-order series in terms of the second-order ones:
`Σ_{i<N} emTerm₄ (i+1) s = Σ_{i<N} emTerm₂ (i+1) s - (s(s+1)(s+2)/720)((N+1)^{-s-3} - 1)`. -/
theorem sum_emTerm₄_eq (s : ℂ) (N : ℕ) :
    ∑ i ∈ Finset.range N, emTerm₄ (i + 1) s
      = ∑ i ∈ Finset.range N, emTerm₂ (i + 1) s
        - s * (s + 1) * (s + 2) / 720 * (((N : ℂ) + 1) ^ (-s - 3) - 1) := by
  have h3 := Finset.sum_range_sub (fun i : ℕ => ((i : ℂ) + 1) ^ (-s - 3)) N
  simp only [Nat.cast_zero, zero_add, one_cpow] at h3
  rw [← h3, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [emTerm₄]
  push_cast
  ring

/-- Fully expanded partial sums of the fourth-order series. -/
theorem sum_emTerm₄ (s : ℂ) (N : ℕ) :
    ∑ i ∈ Finset.range N, emTerm₄ (i + 1) s
      = ∑ i ∈ Finset.range N, ((i : ℂ) + 1) ^ (-s) - (((N : ℂ) + 1) ^ (1 - s) - 1) / (1 - s)
        + (((N : ℂ) + 1) ^ (-s) - 1) / 2 + s / 12 * (((N : ℂ) + 1) ^ (-s - 1) - 1)
        - s * (s + 1) * (s + 2) / 720 * (((N : ℂ) + 1) ^ (-s - 3) - 1) := by
  rw [sum_emTerm₄_eq, sum_emTerm₂]

/-- On `Re s > -1`, `s ≠ 1`, the two continuations agree: `zetaAbel₄ s = zetaAbel₂ s`. -/
theorem zetaAbel₄_eq_zetaAbel₂ {s : ℂ} (hs : -1 < s.re) (hs1 : s ≠ 1) :
    zetaAbel₄ s = zetaAbel₂ s := by
  have hsum₂ := summable_emTerm₂ hs hs1
  have hsum₄ := summable_emTerm₄ (by linarith) hs1
  have h3 : Tendsto (fun N : ℕ => ((N : ℂ) + 1) ^ (-s - 3)) atTop (𝓝 0) :=
    tendsto_add_one_cpow_zero (by simp only [sub_re, neg_re]; norm_num; linarith)
  have hpart : Tendsto (fun N => ∑ i ∈ Finset.range N, emTerm₄ (i + 1) s) atTop
      (𝓝 ((∑' n : ℕ, emTerm₂ (n + 1) s) - s * (s + 1) * (s + 2) / 720 * (0 - 1))) := by
    simp_rw [sum_emTerm₄_eq]
    exact hsum₂.hasSum.tendsto_sum_nat.sub ((h3.sub_const 1).const_mul _)
  have hS : HasSum (fun n : ℕ => emTerm₄ (n + 1) s)
      ((∑' n : ℕ, emTerm₂ (n + 1) s) - s * (s + 1) * (s + 2) / 720 * (0 - 1)) :=
    hsum₄.hasSum_iff_tendsto_nat.mpr hpart
  rw [zetaAbel₄, hS.tsum_eq, zetaAbel₂]
  ring

/-! ## Holomorphy of `zetaAbel₄` on `Re s > -3` and the identity theorem -/

/-- The half-plane `Re s > -3` with the pole removed. -/
def leftHalf₄ : Set ℂ := {s : ℂ | -3 < s.re ∧ s ≠ 1}

/-- `zetaAbel₄` is holomorphic on `Re s > -3`, `s ≠ 1` (locally uniform convergence). -/
theorem zetaAbel₄_differentiableOn : DifferentiableOn ℂ zetaAbel₄ leftHalf₄ := by
  intro s₀ hs₀
  obtain ⟨h0, h1⟩ := hs₀
  set W : Set ℂ := ({s | (s₀.re - 3) / 2 < s.re} ∩ {s | ‖s‖ < ‖s₀‖ + 1}) ∩ {1}ᶜ with hW
  have hWo : IsOpen W :=
    ((isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)).inter isOpen_compl_singleton
  have hs₀W : s₀ ∈ W := ⟨⟨by simp only [Set.mem_setOf_eq]; linarith, by simp⟩, h1⟩
  have hdiff : DifferentiableOn ℂ zetaAbel₄ W := by
    show DifferentiableOn ℂ
      (fun s => 1 / (s - 1) + 1 / 2 + s / 12 - s * (s + 1) * (s + 2) / 720
        + ∑' n : ℕ, emTerm₄ (n + 1) s) W
    apply DifferentiableOn.add
    · intro s hs
      have hd : DifferentiableAt ℂ
          (fun z : ℂ => 1 / (z - 1) + 1 / 2 + z / 12 - z * (z + 1) * (z + 2) / 720) s := by
        have hinv := (differentiableAt_const (1 : ℂ)).div (differentiableAt_id.sub_const 1)
          (sub_ne_zero.mpr hs.2)
        have hpoly : DifferentiableAt ℂ (fun z : ℂ => z * (z + 1) * (z + 2) / 720) s :=
          ((differentiableAt_id.mul (differentiableAt_id.add_const 1)).mul
            (differentiableAt_id.add_const 2)).div_const _
        exact ((hinv.add_const _).add (differentiableAt_id.div_const _)).sub hpoly
      exact hd.differentiableWithinAt
    · refine differentiableOn_tsum_of_summable_norm
        (u := fun n : ℕ => (‖s₀‖ + 1) * (‖s₀‖ + 2) * (‖s₀‖ + 3) * (‖s₀‖ + 4) / 720
          * ((n : ℝ) + 1) ^ (-((s₀.re + 5) / 2)))
        ?_ ?_ hWo ?_
      · exact (summable_add_one_rpow (by linarith)).mul_left _
      · intro n s hs
        exact (emTerm₄_differentiableAt (by omega) hs.2).differentiableWithinAt
      · intro n s hs
        have hre : (s₀.re - 3) / 2 < s.re := hs.1.1
        have hnorm : ‖s‖ < ‖s₀‖ + 1 := hs.1.2
        have hnorm1 : ‖s + 1‖ ≤ ‖s‖ + 1 := by simpa using norm_add_le s 1
        have hnorm2 : ‖s + 2‖ ≤ ‖s‖ + 2 := by simpa using norm_add_le s 2
        have hnorm3 : ‖s + 3‖ ≤ ‖s‖ + 3 := by simpa using norm_add_le s 3
        have hA : ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖
            ≤ (‖s₀‖ + 1) * (‖s₀‖ + 2) * (‖s₀‖ + 3) * (‖s₀‖ + 4) := by
          gcongr <;> linarith
        have hB : ((n : ℝ) + 1) ^ (-s.re - 4) ≤ ((n : ℝ) + 1) ^ (-((s₀.re + 5) / 2)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
            (by linarith)
        calc ‖emTerm₄ (n + 1) s‖
            ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ / 720 * ((n + 1 : ℕ) : ℝ) ^ (-s.re - 4) :=
              norm_emTerm₄_le (by linarith) hs.2 (by omega)
          _ ≤ (‖s₀‖ + 1) * (‖s₀‖ + 2) * (‖s₀‖ + 3) * (‖s₀‖ + 4) / 720
              * ((n : ℝ) + 1) ^ (-((s₀.re + 5) / 2)) := by
              push_cast
              exact mul_le_mul (div_le_div_of_nonneg_right hA (by norm_num)) hB
                (by positivity) (by positivity)
  exact (hdiff.differentiableAt (hWo.mem_nhds hs₀W)).differentiableWithinAt

/-- Identity-theorem step: on a convex open `V ⊆ leftHalf₄` containing a point of `Re s > 1`,
`ζ = zetaAbel₄`. -/
theorem eqOn_zeta_zetaAbel₄_of_convex {V : Set ℂ} (hV : Convex ℝ V) (hVo : IsOpen V)
    (hsub : V ⊆ leftHalf₄) {z₀ : ℂ} (hz₀ : z₀ ∈ V) (hz₀re : 1 < z₀.re) :
    Set.EqOn riemannZeta zetaAbel₄ V := by
  have hζ : AnalyticOnNhd ℂ riemannZeta V :=
    DifferentiableOn.analyticOnNhd
      (fun s hs => (differentiableAt_riemannZeta (hsub hs).2).differentiableWithinAt) hVo
  have hA : AnalyticOnNhd ℂ zetaAbel₄ V :=
    (zetaAbel₄_differentiableOn.mono hsub).analyticOnNhd hVo
  refine hζ.eqOn_of_preconnected_of_eventuallyEq hA hV.isPreconnected hz₀ ?_
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hz₀re) fun s hs => ?_
  have hs' : 1 < s.re := hs
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs'; simp at hs'
  rw [← zetaAbel_eq_zeta_of_one_lt_re hs', ← zetaAbel₂_eq_zetaAbel (by linarith) hs1,
    zetaAbel₄_eq_zetaAbel₂ (by linarith) hs1]

/-- **The fourth-order continuation identity.** For `Re s > -3`, `s ≠ 1`:
`ζ(s) = 1/(s-1) + 1/2 + s/12 - s(s+1)(s+2)/720 + Σ_{n≥1} emTerm₄ n s`. -/
theorem zeta_eq_zetaAbel₄ {s : ℂ} (hs : -3 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = zetaAbel₄ s := by
  have hre : IsOpen {z : ℂ | -3 < z.re} := isOpen_lt continuous_const continuous_re
  rcases lt_trichotomy s.im 0 with him | him | him
  · -- lower half-plane, `z₀ = 2 - I`
    refine eqOn_zeta_zetaAbel₄_of_convex (V := {z | -3 < z.re} ∩ {z | z.im < 0})
      ((convex_halfSpace_re_gt (-3)).inter (convex_halfSpace_im_lt 0))
      (hre.inter (isOpen_lt continuous_im continuous_const))
      (fun z hz => ⟨hz.1, fun h => by rw [h] at hz; simp at hz⟩)
      (z₀ := 2 - I) ⟨by norm_num, by simp⟩ (by simp) ⟨hs, him⟩
  · -- real axis: either `Re s > 1` (Dirichlet series) or `-3 < Re s < 1`
    have hre1 : s.re ≠ 1 := fun h => hs1 (Complex.ext h (by simpa using him))
    rcases lt_or_gt_of_ne hre1 with h | h
    · -- `-3 < s < 1`: use the convex set `{Re > -3} ∩ {Re - 1 < Im}`, `z₀ = 2 + 2I`
      have hL : IsLinearMap ℝ (fun z : ℂ => z.im - z.re) :=
        ⟨fun x y => by simp only [add_im, add_re]; ring,
         fun c x => by simp only [smul_im, smul_re, smul_eq_mul]; ring⟩
      refine eqOn_zeta_zetaAbel₄_of_convex (V := {z | -3 < z.re} ∩ {z | -1 < z.im - z.re})
        ((convex_halfSpace_re_gt (-3)).inter (convex_halfSpace_gt hL (-1)))
        (hre.inter (isOpen_lt continuous_const (continuous_im.sub continuous_re)))
        (fun z hz => ⟨hz.1, fun h => by rw [h] at hz; norm_num at hz⟩)
        (z₀ := 2 + 2 * I) ⟨by norm_num, by simp⟩ (by simp)
        ⟨hs, by simp only [Set.mem_setOf_eq]; linarith⟩
    · rw [← zetaAbel_eq_zeta_of_one_lt_re h, ← zetaAbel₂_eq_zetaAbel (by linarith) hs1,
        zetaAbel₄_eq_zetaAbel₂ (by linarith) hs1]
  · -- upper half-plane, `z₀ = 2 + I`
    refine eqOn_zeta_zetaAbel₄_of_convex (V := {z | -3 < z.re} ∩ {z | 0 < z.im})
      ((convex_halfSpace_re_gt (-3)).inter (convex_halfSpace_im_gt 0))
      (hre.inter (isOpen_lt continuous_const continuous_im))
      (fun z hz => ⟨hz.1, fun h => by rw [h] at hz; simp at hz⟩)
      (z₀ := 2 + I) ⟨by norm_num, by simp⟩ (by simp) ⟨hs, him⟩

/-! ## Splitting the representation at `N` and the growth bound -/

/-- **Representation split at `N`.** For `Re s > -3`, `s ≠ 1` and any `N`,
`ζ(s) = Σ_{n=1}^{N} n^{-s} + (N+1)^{1-s}/(s-1) + (N+1)^{-s}/2 + (s/12)(N+1)^{-s-1}
  - (s(s+1)(s+2)/720)(N+1)^{-s-3} + Σ_{n > N} emTerm₄ n s`. -/
theorem zeta_eq_sum_add_tail₄ {s : ℂ} (hs : -3 < s.re) (hs1 : s ≠ 1) (N : ℕ) :
    riemannZeta s = ∑ i ∈ Finset.range N, ((i : ℂ) + 1) ^ (-s)
      + ((N : ℂ) + 1) ^ (1 - s) / (s - 1) + ((N : ℂ) + 1) ^ (-s) / 2
      + s / 12 * ((N : ℂ) + 1) ^ (-s - 1)
      - s * (s + 1) * (s + 2) / 720 * ((N : ℂ) + 1) ^ (-s - 3)
      + ∑' n : ℕ, emTerm₄ (n + N + 1) s := by
  have hsum := summable_emTerm₄ hs hs1
  have hsplit := Summable.sum_add_tsum_nat_add N hsum
  rw [zeta_eq_zetaAbel₄ hs hs1, zetaAbel₄, ← hsplit, sum_emTerm₄]
  -- the only non-polynomial identity needed: `x/(1-s) = -(x/(s-1))`
  have hw : (((N : ℂ) + 1) ^ (1 - s) - 1) / (1 - s)
      = -((((N : ℂ) + 1) ^ (1 - s) - 1) / (s - 1)) := by
    rw [← neg_sub s 1, div_neg]
  rw [hw]
  ring

end ZetaGrowthEM3
end EMCopy


section

/-! ## Verified complex disc arithmetic over `ℚ` -/

/-- A closed disc in `ℂ` with rational centre `re + im·i` and rational radius `r`. -/
structure Disc where
  re : ℚ
  im : ℚ
  r : ℚ

namespace Disc

/-- The centre as a complex number. -/
def c (D : Disc) : ℂ := (D.re : ℂ) + (D.im : ℂ) * I

/-- `z` lies in the disc. -/
def Contains (D : Disc) (z : ℂ) : Prop := ‖z - D.c‖ ≤ (D.r : ℝ)

/-- A rational upper bound for `‖centre‖`. -/
def nb (D : Disc) : ℚ := |D.re| + |D.im|

lemma norm_le_abs_re_add_abs_im (z : ℂ) : ‖z‖ ≤ |z.re| + |z.im| := by
  exact Complex.norm_le_abs_re_add_abs_im z

lemma c_re (D : Disc) : D.c.re = D.re := by simp [c]
lemma c_im (D : Disc) : D.c.im = D.im := by simp [c]

lemma norm_c_le (D : Disc) : ‖D.c‖ ≤ (D.nb : ℝ) := by
  refine (norm_le_abs_re_add_abs_im _).trans (le_of_eq ?_)
  simp [nb, c_re, c_im]

lemma norm_le_of_contains {D : Disc} {z : ℂ} (h : D.Contains z) : ‖z‖ ≤ (D.nb : ℝ) + D.r := by
  have := norm_add_le (z - D.c) D.c
  rw [sub_add_cancel] at this
  unfold Contains at h
  linarith [norm_c_le D]

def add (D E : Disc) : Disc := ⟨D.re + E.re, D.im + E.im, D.r + E.r⟩

lemma add_c (D E : Disc) : (add D E).c = D.c + E.c := by
  simp only [c, add]; push_cast; ring

theorem add_contains {D E : Disc} {z w : ℂ} (hz : D.Contains z) (hw : E.Contains w) :
    (add D E).Contains (z + w) := by
  unfold Contains at *
  rw [add_c, show z + w - (D.c + E.c) = (z - D.c) + (w - E.c) by ring]
  refine (norm_add_le _ _).trans ?_
  simp only [add]; push_cast; linarith

def mul (D E : Disc) : Disc :=
  ⟨D.re * E.re - D.im * E.im, D.re * E.im + D.im * E.re, D.r * (E.nb + E.r) + D.nb * E.r⟩

lemma mul_c (D E : Disc) : (mul D E).c = D.c * E.c := by
  apply Complex.ext <;> simp [c, mul, c_re, c_im]

theorem mul_contains {D E : Disc} {z w : ℂ} (hz : D.Contains z) (hw : E.Contains w) :
    (mul D E).Contains (z * w) := by
  have hwn := norm_le_of_contains hw
  unfold Contains at *
  rw [mul_c, show z * w - D.c * E.c = (z - D.c) * w + D.c * (w - E.c) by ring]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have h1 : ‖z - D.c‖ * ‖w‖ ≤ (D.r : ℝ) * ((E.nb : ℝ) + E.r) :=
    mul_le_mul hz hwn (norm_nonneg _) ((norm_nonneg _).trans hz)
  have h2 : ‖D.c‖ * ‖w - E.c‖ ≤ (D.nb : ℝ) * E.r :=
    mul_le_mul (norm_c_le D) hw (norm_nonneg _) ((norm_nonneg _).trans (norm_c_le D))
  simp only [mul]; push_cast; linarith

/-- Exact rational complex number. -/
def exact (a b : ℚ) : Disc := ⟨a, b, 0⟩

theorem exact_contains (a b : ℚ) : (exact a b).Contains ((a : ℂ) + (b : ℂ) * I) := by
  simp [Contains, exact, c]

/-- Scaling by a rational. -/
def smul (q : ℚ) (D : Disc) : Disc := ⟨q * D.re, q * D.im, |q| * D.r⟩

theorem smul_contains (q : ℚ) {D : Disc} {z : ℂ} (hz : D.Contains z) :
    (smul q D).Contains ((q : ℂ) * z) := by
  unfold Contains at *
  have hc : (smul q D).c = (q : ℂ) * D.c := by
    simp only [c, smul]; push_cast; ring
  rw [hc, ← mul_sub, norm_mul, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  simp only [smul]; push_cast
  exact mul_le_mul_of_nonneg_left hz (abs_nonneg _)

def enlarge (D : Disc) (e : ℚ) : Disc := ⟨D.re, D.im, D.r + e⟩

theorem enlarge_contains {D : Disc} {z : ℂ} (e : ℚ) (he : 0 ≤ e) (hz : D.Contains z) :
    (D.enlarge e).Contains z := by
  unfold Contains at *
  have hc : (D.enlarge e).c = D.c := rfl
  rw [hc]
  simp only [enlarge]; push_cast
  have : (0 : ℝ) ≤ e := by exact_mod_cast he
  linarith

/-- If `z ∈ D` and `‖w − z‖ ≤ e` then `w ∈ D` enlarged by `e`. -/
theorem enlarge_contains' {D : Disc} {z w : ℂ} (e : ℚ) (hz : D.Contains z)
    (hw : ‖w - z‖ ≤ (e : ℝ)) : (D.enlarge e).Contains w := by
  unfold Contains at *
  have hc : (D.enlarge e).c = D.c := rfl
  rw [hc, show w - D.c = (w - z) + (z - D.c) by ring]
  refine (norm_add_le _ _).trans ?_
  simp only [enlarge]; push_cast; linarith

/-- Rounding to the grid `2^{-40}`. -/
def rnd (q : ℚ) : ℚ := (⌊q * 1099511627776⌋ : ℤ) / 1099511627776

lemma rnd_le (q : ℚ) : rnd q ≤ q := by
  unfold rnd
  rw [div_le_iff₀ (by norm_num)]
  exact Int.floor_le _

lemma sub_rnd_le (q : ℚ) : q - rnd q ≤ 1 / 1099511627776 := by
  unfold rnd
  have h := Int.lt_floor_add_one (q * 1099511627776)
  have : q ≤ ((⌊q * 1099511627776⌋ : ℤ) + 1 : ℚ) / 1099511627776 := by
    calc q = q * 1099511627776 / 1099511627776 := by field_simp
      _ ≤ ((⌊q * 1099511627776⌋ : ℤ) + 1 : ℚ) / 1099511627776 :=
          div_le_div_of_nonneg_right h.le (by norm_num)
  rw [add_div] at this
  linarith

/-- Upward rounding. -/
def rndUp (q : ℚ) : ℚ := -rnd (-q)

lemma le_rndUp (q : ℚ) : q ≤ rndUp q := by
  unfold rndUp; have := rnd_le (-q); linarith

def round (D : Disc) : Disc := ⟨rnd D.re, rnd D.im, rndUp D.r + 2 / 1099511627776⟩

theorem round_contains {D : Disc} {z : ℂ} (hz : D.Contains z) : D.round.Contains z := by
  unfold Contains at *
  have h1 := rnd_le D.re; have h2 := sub_rnd_le D.re
  have h3 := rnd_le D.im; have h4 := sub_rnd_le D.im
  have hd : ‖D.c - D.round.c‖ ≤ (2 / 1099511627776 : ℚ) := by
    refine (norm_le_abs_re_add_abs_im _).trans ?_
    simp only [sub_re, sub_im, c_re, c_im, round]
    rw [_root_.abs_of_nonneg (by have : (rnd D.re : ℝ) ≤ D.re := by exact_mod_cast h1
                                 linarith),
      _root_.abs_of_nonneg (by have : (rnd D.im : ℝ) ≤ D.im := by exact_mod_cast h3
                               linarith)]
    have e2 : ((D.re : ℝ) - rnd D.re) ≤ (1 / 1099511627776 : ℚ) := by exact_mod_cast h2
    have e4 : ((D.im : ℝ) - rnd D.im) ≤ (1 / 1099511627776 : ℚ) := by exact_mod_cast h4
    push_cast at e2 e4 ⊢; linarith
  rw [show z - D.round.c = (z - D.c) + (D.c - D.round.c) by ring]
  refine (norm_add_le _ _).trans ?_
  have hr : ((D.round.r : ℚ) : ℝ) = (rndUp D.r : ℝ) + 2 / 1099511627776 := by
    simp only [round]; push_cast; ring
  have hu : (D.r : ℝ) ≤ (rndUp D.r : ℝ) := by exact_mod_cast le_rndUp D.r
  rw [hr]; push_cast at hd; linarith

/-! ### Exponential -/

/-- Taylor loop: `taylorLoop w k m term sum` adds `k` more terms. -/
def taylorLoop (w : Disc) : ℕ → ℕ → Disc → Disc → Disc
  | 0, _, _, sum => sum
  | k + 1, m, term, sum =>
      taylorLoop w k (m + 1) (round (smul (1 / ((m : ℚ) + 1)) (mul term w))) (add sum term)

theorem taylorLoop_contains (w : Disc) {x : ℂ} (hx : w.Contains x) :
    ∀ (k m : ℕ) (term sum : Disc), term.Contains (x ^ m / m.factorial) →
      sum.Contains (∑ i ∈ Finset.range m, x ^ i / i.factorial) →
      (taylorLoop w k m term sum).Contains (∑ i ∈ Finset.range (m + k), x ^ i / i.factorial) := by
  intro k
  induction k with
  | zero => intro m term sum _ hs; simpa [taylorLoop] using hs
  | succ k ih =>
    intro m term sum ht hs
    simp only [taylorLoop]
    have := ih (m + 1) (round (smul (1 / ((m : ℚ) + 1)) (mul term w))) (add sum term) ?_ ?_
    · rwa [show m + 1 + k = m + (k + 1) by ring] at this
    · apply round_contains
      have h := smul_contains (1 / ((m : ℚ) + 1)) (mul_contains ht hx)
      convert h using 1
      rw [pow_succ, Nat.factorial_succ]; push_cast
      field_simp
    · rw [Finset.sum_range_succ]; exact add_contains hs ht

/-- Remainder bound `‖w‖^d (d+1)/(d!·d)` with `‖w‖ ≤ nb`. -/
def expRem (w : Disc) (d : ℕ) : ℚ := (w.nb) ^ d * ((d + 1 : ℚ) / ((d.factorial : ℚ) * d))

/-- Disc for `exp w` for an exact small `w` (`nb w ≤ 1`, `w.r = 0`), degree `d`. -/
def expSmall (w : Disc) (d : ℕ) : Disc :=
  (taylorLoop w d 0 (exact 1 0) (exact 0 0)).enlarge (expRem w d)

theorem expSmall_contains (w : Disc) (hw0 : w.r = 0) (hw1 : w.nb ≤ 1) (d : ℕ) (hd : 0 < d) :
    (expSmall w d).Contains (exp w.c) := by
  have hx : w.Contains w.c := by simp [Contains, hw0]
  have h := taylorLoop_contains w hx d 0 (exact 1 0) (exact 0 0) (by
      simpa using exact_contains 1 0) (by simpa using exact_contains 0 0)
  rw [zero_add] at h
  refine enlarge_contains' _ h ?_
  have hn : ‖w.c‖ ≤ 1 := by
    have := norm_c_le w
    exact this.trans (by exact_mod_cast hw1)
  have hb := Complex.exp_bound hn hd
  refine hb.trans ?_
  have hnb : ‖w.c‖ ≤ (w.nb : ℝ) := norm_c_le w
  unfold expRem; push_cast
  apply mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hnb d)
  positivity

def squareN : ℕ → Disc → Disc
  | 0, D => D
  | k + 1, D => squareN k (round (mul D D))

theorem squareN_contains : ∀ (k : ℕ) {D : Disc} {x : ℂ}, D.Contains (exp x) →
    (squareN k D).Contains (exp (2 ^ k * x))
  | 0, D, x, h => by simpa [squareN] using h
  | k + 1, D, x, h => by
    simp only [squareN]
    have h2 : (round (mul D D)).Contains (exp (2 * x)) := by
      apply round_contains
      rw [show 2 * x = x + x by ring, Complex.exp_add]
      exact mul_contains h h
    have := squareN_contains k h2
    rwa [show (2 : ℂ) ^ k * (2 * x) = 2 ^ (k + 1) * x by ring] at this

/-- Disc for `exp (a + b i)`, valid when `|a| + |b| ≤ 16`. -/
def expDisc (a b : ℚ) : Disc := squareN 5 (expSmall (exact (a / 32) (b / 32)) 14)

theorem expDisc_contains (a b : ℚ) (h : |a| + |b| ≤ 16) :
    (expDisc a b).Contains (exp ((a : ℂ) + (b : ℂ) * I)) := by
  have hw : (exact (a / 32) (b / 32)).nb ≤ 1 := by
    simp only [nb, exact, abs_div]
    rw [abs_of_pos (by norm_num : (0 : ℚ) < 32)]
    linarith
  have h1 := expSmall_contains (exact (a / 32) (b / 32)) rfl hw 14 (by norm_num)
  have h2 := squareN_contains 5 h1
  unfold expDisc
  convert h2 using 2
  simp only [c, exact]; push_cast; ring

end Disc


end

section
open Kerr.File14RH Disc
open ZetaGrowth ZetaGrowthNeg ZetaGrowthEM3

/-! ## No zeros with `|Im s| < 10` in the critical strip -/

/-! ### `|Im s| ≤ 3/2` (copied from hp-proof `FleetLowZeroFree`, QJ) -/

lemma norm_le_of_sq {z : ℂ} {c : ℝ} (hc : 0 ≤ c) (h : z.re ^ 2 + z.im ^ 2 ≤ c ^ 2) : ‖z‖ ≤ c := by
  rw [Complex.norm_def, Complex.normSq_apply]
  exact (Real.sqrt_le_left hc).mpr (by nlinarith)

lemma sum_inv_sq : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simpa using h

/-- **`ζ(s) ≠ 0` for `0 < Re s < 1`, `|Im s| ≤ 3/2`.** -/
theorem zeta_ne_zero_low {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (ht : |s.im| ≤ 3 / 2) :
    riemannZeta s ≠ 0 := by
  have hs1 : s ≠ 1 := fun h => by rw [h] at h1; simp at h1
  have hsm1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have ht2 : s.im ^ 2 ≤ 9 / 4 := by
    have := abs_le.mp ht; nlinarith
  -- norm bounds on the box
  have nA : ‖s‖ ≤ 1.81 := norm_le_of_sq (by norm_num) (by nlinarith)
  have nB : ‖s + 1‖ ≤ 2.5 :=
    norm_le_of_sq (by norm_num) (by simp only [add_re, add_im, one_re, one_im]; nlinarith)
  have nC : ‖s + 2‖ ≤ 3.36 :=
    norm_le_of_sq (by norm_num) (by
      simp only [add_re, add_im]; norm_num; nlinarith)
  have nD : ‖s + 3‖ ≤ 4.28 :=
    norm_le_of_sq (by norm_num) (by
      simp only [add_re, add_im]; norm_num; nlinarith)
  have nE : ‖s - 1‖ ≤ 1.81 :=
    norm_le_of_sq (by norm_num) (by simp only [sub_re, sub_im, one_re, one_im]; nlinarith)
  have lC : 2 ≤ ‖s + 2‖ := by
    have := Complex.re_le_norm (s + 2); simp only [add_re] at this
    norm_num at this; linarith
  have lD : 3 ≤ ‖s + 3‖ := by
    have := Complex.re_le_norm (s + 3); simp only [add_re] at this
    norm_num at this; linarith
  -- the remainder
  set K : ℝ := ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ / 720
  have hK0 : 0 ≤ K := by positivity
  have hKle : K ≤ 1.81 * 2.5 * 3.36 * 4.28 / 720 := by
    have := mul_le_mul (mul_le_mul (mul_le_mul nA nB (norm_nonneg _) (by norm_num)) nC
      (norm_nonneg _) (by norm_num)) nD (norm_nonneg _) (by norm_num)
    simp only [K]; linarith [div_le_div_of_nonneg_right this (by norm_num : (0:ℝ) ≤ 720)]
  have hterm : ∀ n : ℕ, ‖emTerm₄ (n + 1) s‖ ≤ K * (1 / ((n : ℝ) + 1) ^ 2) := by
    intro n
    have h := norm_emTerm₄_le (by linarith : (-4 : ℝ) ≤ s.re) hs1 (by omega : 1 ≤ n + 1)
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hK0)
    push_cast
    have hx : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    calc ((n : ℝ) + 1) ^ (-s.re - 4) ≤ ((n : ℝ) + 1) ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx (by linarith)
      _ = 1 / ((n : ℝ) + 1) ^ 2 := by
          rw [Real.rpow_neg (by linarith), one_div]; norm_cast
  have hsumK : HasSum (fun n : ℕ => K * (1 / ((n : ℝ) + 1) ^ 2)) (K * (π ^ 2 / 6)) :=
    sum_inv_sq.mul_left K
  have hnorm : Summable (fun n : ℕ => ‖emTerm₄ (n + 1) s‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsumK.summable
  set R : ℂ := ∑' n : ℕ, emTerm₄ (n + 1) s
  have hR : ‖R‖ ≤ K * (π ^ 2 / 6) :=
    (norm_tsum_le_tsum_norm hnorm).trans
      ((Summable.tsum_le_tsum hterm hnorm hsumK.summable).trans (le_of_eq hsumK.tsum_eq))
  have hpi : π ^ 2 / 6 ≤ 1.66 := by
    have := Real.pi_lt_d2; have := Real.pi_pos; nlinarith
  -- the identity (s-1) ζ(s) = A - B + (s-1) R
  intro hz
  have hζ := zeta_eq_zetaAbel₄ (by linarith : (-3 : ℝ) < s.re) hs1
  rw [hz] at hζ
  unfold zetaAbel₄ at hζ
  have hζ' : 1 / (s - 1) + 1 / 2 + s / 12 - s * (s + 1) * (s + 2) / 720 + R = 0 := hζ.symm
  have e : (s - 1) * (1 / (s - 1) + 1 / 2 + s / 12 - s * (s + 1) * (s + 2) / 720 + R) = 0 := by
    rw [hζ', mul_zero]
  have hinv : (s - 1) * (1 / (s - 1)) = 1 := mul_one_div_cancel hsm1
  have key : (s + 2) * (s + 3) / 12 = (s - 1) * s * (s + 1) * (s + 2) / 720 - (s - 1) * R := by
    linear_combination e - hinv
  have hA : (1 / 2 : ℝ) ≤ ‖(s + 2) * (s + 3) / 12‖ := by
    rw [norm_div, norm_mul]
    have : ‖(12 : ℂ)‖ = 12 := by simp
    rw [this]
    have := mul_le_mul lC lD (by norm_num) (norm_nonneg _)
    linarith [div_le_div_of_nonneg_right this (by norm_num : (0:ℝ) ≤ 12)]
  have hB : ‖(s - 1) * s * (s + 1) * (s + 2) / 720‖ ≤ 1.81 * 1.81 * 2.5 * 3.36 / 720 := by
    rw [norm_div, norm_mul, norm_mul, norm_mul]
    have : ‖(720 : ℂ)‖ = 720 := by simp
    rw [this]
    have := mul_le_mul (mul_le_mul (mul_le_mul nE nA (norm_nonneg _) (by norm_num)) nB
      (norm_nonneg _) (by norm_num)) nC (norm_nonneg _) (by norm_num)
    exact div_le_div_of_nonneg_right this (by norm_num)
  have hC : ‖(s - 1) * R‖ ≤ 1.81 * ((1.81 * 2.5 * 3.36 * 4.28 / 720) * 1.66) := by
    rw [norm_mul]
    apply mul_le_mul nE _ (norm_nonneg _) (by norm_num)
    calc ‖R‖ ≤ K * (π ^ 2 / 6) := hR
      _ ≤ (1.81 * 2.5 * 3.36 * 4.28 / 720) * 1.66 :=
          mul_le_mul hKle hpi (by positivity) (by norm_num)
  have htri := norm_sub_le ((s - 1) * s * (s + 1) * (s + 2) / 720) ((s - 1) * R)
  rw [← key] at htri
  norm_num at hA hB hC htri
  linarith

/-! ### Logarithm constants -/

/-- `log 2 ≈ l2c`. -/
def l2c : ℚ := 69314718056 / 100000000000
/-- `log 3 ≈ l3c`. -/
def l3c : ℚ := 109861228867 / 100000000000
/-- Tolerance for the logarithm constants. -/
def etaL : ℚ := 1 / 100000000

lemma log_two_near : |Real.log 2 - l2c| ≤ etaL := by
  have h1 := Real.log_two_gt_d9; have h2 := Real.log_two_lt_d9
  rw [abs_le]; unfold l2c etaL; push_cast; constructor <;> linarith

lemma exp_rat_near (a : ℚ) (ha : |a| ≤ 16) :
    |Real.exp a - (expDisc a 0).re| ≤ (expDisc a 0).r := by
  have h := expDisc_contains a 0 (by simpa using ha)
  unfold Contains at h
  have hz : ((a : ℂ) + ((0 : ℚ) : ℂ) * I) = ((a : ℝ) : ℂ) := by push_cast; ring
  rw [hz] at h
  refine le_trans ?_ h
  have := Complex.abs_re_le_norm (exp ((a : ℝ) : ℂ) - (expDisc a 0).c)
  rw [sub_re, Complex.exp_ofReal_re, c_re] at this
  exact this

set_option maxRecDepth 100000 in
lemma log_three_near : |Real.log 3 - l3c| ≤ etaL := by
  have hlo := exp_rat_near (l3c - etaL) (by unfold l3c etaL; norm_num [abs_of_pos])
  have hhi := exp_rat_near (l3c + etaL) (by unfold l3c etaL; norm_num [abs_of_pos])
  have c1 : (expDisc (l3c - etaL) 0).re + (expDisc (l3c - etaL) 0).r < 3 := by decide +kernel
  have c2 : 3 < (expDisc (l3c + etaL) 0).re - (expDisc (l3c + etaL) 0).r := by decide +kernel
  have c1' : ((expDisc (l3c - etaL) 0).re : ℝ) + (expDisc (l3c - etaL) 0).r < 3 := by
    exact_mod_cast c1
  have c2' : (3 : ℝ) < ((expDisc (l3c + etaL) 0).re : ℝ) - (expDisc (l3c + etaL) 0).r := by
    exact_mod_cast c2
  have e1 : Real.exp ((l3c - etaL : ℚ) : ℝ) < 3 := by
    have := (abs_le.mp hlo).2; linarith
  have e2 : 3 < Real.exp ((l3c + etaL : ℚ) : ℝ) := by
    have := (abs_le.mp hhi).1; linarith
  have l1 : ((l3c - etaL : ℚ) : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]; exact e1
  have l2 : Real.log 3 < ((l3c + etaL : ℚ) : ℝ) := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]; exact e2
  push_cast at l1 l2
  rw [abs_le]; constructor <;> linarith

/-! ### Discs for `n^{-s}` -/

/-- Disc for `n^{-(σ + t i)}` from a rational approximation `lc` of `log n`. -/
def powDisc (lc σ t : ℚ) : Disc :=
  mul (expDisc (-σ * lc) (-t * lc)) ⟨1, 0, 2 * (|σ| + |t|) * etaL⟩

theorem powDisc_contains {n : ℕ} (hn : 0 < n) {lc : ℚ} (hl : |Real.log n - lc| ≤ etaL)
    (σ t : ℚ) (h16 : |-σ * lc| + |-t * lc| ≤ 16) (hη : (|σ| + |t|) * etaL ≤ 1 / 2) :
    (powDisc lc σ t).Contains ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  set w : ℂ := -((σ : ℂ) + (t : ℂ) * I) with hw
  set L : ℝ := Real.log n with hL
  have hlog : Complex.log (n : ℂ) = ((L : ℝ) : ℂ) := by rw [hL, natCast_log]
  have hsplit : (n : ℂ) ^ w = exp ((lc : ℂ) * w) * exp (((L - lc : ℝ) : ℂ) * w) := by
    rw [cpow_def_of_ne_zero hn0, ← Complex.exp_add, hlog]
    congr 1; push_cast; ring
  rw [hsplit]
  apply mul_contains
  · have := expDisc_contains (-σ * lc) (-t * lc) h16
    convert this using 2
    rw [hw]; push_cast; ring
  · unfold Contains c
    simp only [Rat.cast_one, Rat.cast_zero, zero_mul, add_zero]
    have hwn : ‖w‖ ≤ |(σ : ℝ)| + |(t : ℝ)| := by
      rw [hw, norm_neg]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, mul_one, ← Complex.ofReal_ratCast, ← Complex.ofReal_ratCast,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    have hl' : |L - lc| ≤ (etaL : ℝ) := by exact_mod_cast hl
    have hu : ‖((L - lc : ℝ) : ℂ) * w‖ ≤ (|(σ : ℝ)| + |(t : ℝ)|) * etaL := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul hwn hl' (abs_nonneg _) (by positivity)
    have hη' : (|(σ : ℝ)| + |(t : ℝ)|) * (etaL : ℝ) ≤ 1 / 2 := by
      have := (Rat.cast_le (K := ℝ)).mpr hη
      push_cast at this; exact this
    have hb := Complex.norm_exp_sub_one_le (x := ((L - lc : ℝ) : ℂ) * w)
      (by linarith)
    have hr : (((2 * (|σ| + |t|) * etaL : ℚ)) : ℝ) = 2 * ((|(σ : ℝ)| + |(t : ℝ)|) * etaL) := by
      push_cast; ring
    rw [hr]
    calc ‖exp (((L - lc : ℝ) : ℂ) * w) - 1‖ ≤ 2 * ‖((L - lc : ℝ) : ℂ) * w‖ := hb
      _ ≤ 2 * ((|(σ : ℝ)| + |(t : ℝ)|) * etaL) := by linarith


end

section
open Kerr.File14RH Disc
open ZetaGrowth ZetaGrowthNeg ZetaGrowthEM3

/-! ### The approximant `F(s) = 1 + 2^{-s} + 3^{-s} + 4·4^{-s}/(s−1) + 4^{-s}/2` -/

/-- The Euler–Maclaurin approximant with three terms and boundary point `4`. -/
def Fex (s : ℂ) : ℂ :=
  1 + (2 : ℂ) ^ (-s) + (3 : ℂ) ^ (-s) + ((4 : ℚ) : ℂ) * ((4 : ℂ) ^ (-s) * (s - 1)⁻¹) +
    ((1 / 2 : ℚ) : ℂ) * (4 : ℂ) ^ (-s)

/-- Disc enclosing `F(σ₀ + t₀ i)`. -/
def Fdisc (σ0 t0 : ℚ) : Disc :=
  let D2 := powDisc l2c σ0 t0
  let D3 := powDisc l3c σ0 t0
  let D4 := round (mul D2 D2)
  let q := (σ0 - 1) ^ 2 + t0 ^ 2
  add (add (add (add (exact 1 0) D2) D3)
    (smul 4 (round (mul D4 (exact ((σ0 - 1) / q) (-t0 / q)))))) (smul (1 / 2) D4)

lemma four_cpow (w : ℂ) : (4 : ℂ) ^ w = (2 : ℂ) ^ w * (2 : ℂ) ^ w := by
  have := natCast_mul_natCast_cpow 2 2 w
  push_cast at this; norm_num at this; exact this

theorem Fdisc_contains (σ0 t0 : ℚ) (ht : 0 < t0)
    (h2 : |-σ0 * l2c| + |-t0 * l2c| ≤ 16) (h3 : |-σ0 * l3c| + |-t0 * l3c| ≤ 16)
    (hη : (|σ0| + |t0|) * etaL ≤ 1 / 2) :
    (Fdisc σ0 t0).Contains (Fex ((σ0 : ℂ) + (t0 : ℂ) * I)) := by
  set s0 : ℂ := (σ0 : ℂ) + (t0 : ℂ) * I with hs0
  have c2 : (powDisc l2c σ0 t0).Contains ((2 : ℂ) ^ (-s0)) := by
    have := powDisc_contains (n := 2) (by norm_num) (by simpa using log_two_near) σ0 t0 h2 hη
    simpa only [Nat.cast_ofNat] using this
  have c3 : (powDisc l3c σ0 t0).Contains ((3 : ℂ) ^ (-s0)) := by
    have := powDisc_contains (n := 3) (by norm_num) (by simpa using log_three_near) σ0 t0 h3 hη
    simpa only [Nat.cast_ofNat] using this
  have c4 : (round (mul (powDisc l2c σ0 t0) (powDisc l2c σ0 t0))).Contains ((4 : ℂ) ^ (-s0)) := by
    rw [four_cpow]; exact round_contains (mul_contains c2 c2)
  have hq : (0 : ℚ) < (σ0 - 1) ^ 2 + t0 ^ 2 := by positivity
  have cinv : (exact ((σ0 - 1) / ((σ0 - 1) ^ 2 + t0 ^ 2)) (-t0 / ((σ0 - 1) ^ 2 + t0 ^ 2))).Contains
      ((s0 - 1)⁻¹) := by
    have he := exact_contains ((σ0 - 1) / ((σ0 - 1) ^ 2 + t0 ^ 2)) (-t0 / ((σ0 - 1) ^ 2 + t0 ^ 2))
    convert he using 1
    have hne : s0 - 1 ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp [hs0] at this
      exact ht.ne' (by exact_mod_cast this)
    have hqR : ((σ0 : ℝ) - 1) ^ 2 + (t0 : ℝ) ^ 2 ≠ 0 := by
      have : (0 : ℝ) < ((σ0 : ℝ) - 1) ^ 2 + (t0 : ℝ) ^ 2 := by exact_mod_cast hq
      exact this.ne'
    apply inv_eq_of_mul_eq_one_right
    apply Complex.ext_iff.mpr
    simp only [hs0, Disc.c, Disc.exact, mul_re, mul_im, sub_re, sub_im, add_re, add_im,
      ofReal_re, ofReal_im, I_re, I_im, one_re, one_im, Complex.ratCast_re, Complex.ratCast_im]
    push_cast
    constructor
    · field_simp; ring
    · field_simp; ring
  unfold Fdisc
  simp only
  unfold Fex
  refine add_contains (add_contains (add_contains (add_contains ?_ c2) c3) ?_) ?_
  · simpa using exact_contains 1 0
  · exact smul_contains 4 (round_contains (mul_contains c4 cinv))
  · exact smul_contains (1 / 2) c4

/-! ### Lipschitz bounds -/

lemma rpow_neg_le_const (b : ℕ) (hb : 1 ≤ b) {σ : ℝ} (hσ : 1 / 2 ≤ σ) {c : ℝ} (hc : 0 ≤ c)
    (hcb : 1 ≤ c ^ 2 * b) : (b : ℝ) ^ (-σ) ≤ c := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have h1 : (b : ℝ) ^ (-σ) ≤ (b : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
  refine h1.trans ?_
  rw [Real.rpow_neg (by linarith), ← Real.sqrt_eq_rpow]
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr (by linarith)
  rw [inv_le_iff_one_le_mul₀ hs]
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ b by linarith)
  have hm := mul_nonneg hc hs.le
  have : (c * Real.sqrt b) ^ 2 = c ^ 2 * b := by rw [mul_pow, hsq]
  nlinarith

lemma norm_cpow_neg_le (b : ℕ) (hb : 1 ≤ b) {s : ℂ} (hσ : 1 / 2 ≤ s.re) {c : ℝ} (hc : 0 ≤ c)
    (hcb : 1 ≤ c ^ 2 * b) : ‖(b : ℂ) ^ (-s)‖ ≤ c := by
  rw [norm_natCast_cpow_of_pos (by omega), neg_re]
  exact rpow_neg_le_const b hb hσ hc hcb

lemma cpow_sub_le {b : ℕ} (hb : 1 ≤ b) {s s0 : ℂ} {cb ℓu ρ : ℝ}
    (hc : ‖(b : ℂ) ^ (-s0)‖ ≤ cb) (hlog : Real.log b ≤ ℓu) (hd : ‖s - s0‖ ≤ ρ)
    (h1 : ρ * ℓu ≤ 1) :
    ‖(b : ℂ) ^ (-s) - (b : ℂ) ^ (-s0)‖ ≤ cb * (ρ * ℓu * (1 + ρ * ℓu)) := by
  have hb0 : (b : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsplit : (b : ℂ) ^ (-s) = (b : ℂ) ^ (-s0) * (b : ℂ) ^ (-(s - s0)) := by
    rw [← cpow_add _ _ hb0]; congr 1; ring
  rw [hsplit, show (b : ℂ) ^ (-s0) * (b : ℂ) ^ (-(s - s0)) - (b : ℂ) ^ (-s0) =
    (b : ℂ) ^ (-s0) * ((b : ℂ) ^ (-(s - s0)) - 1) by ring, norm_mul]
  have hlog0 : 0 ≤ Real.log b := Real.log_nonneg (by exact_mod_cast hb)
  set u : ℂ := Complex.log b * (-(s - s0)) with hu
  have hexp : (b : ℂ) ^ (-(s - s0)) = exp u := by rw [cpow_def_of_ne_zero hb0]
  have hun : ‖u‖ ≤ ρ * ℓu := by
    rw [hu, norm_mul, norm_neg, ← natCast_log, Complex.norm_real, Real.norm_eq_abs,
      _root_.abs_of_nonneg hlog0, mul_comm]
    exact mul_le_mul hd hlog hlog0 ((norm_nonneg _).trans hd)
  have hu1 : ‖u‖ ≤ 1 := by linarith
  have hb2 := Complex.norm_exp_sub_one_sub_id_le hu1
  have hfin : ‖exp u - 1‖ ≤ ρ * ℓu * (1 + ρ * ℓu) := by
    have := norm_add_le (exp u - 1 - u) u
    rw [sub_add_cancel] at this
    have hsq : ‖u‖ ^ 2 ≤ (ρ * ℓu) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hun 2
    nlinarith
  rw [hexp]
  exact mul_le_mul hc hfin (norm_nonneg _) ((norm_nonneg _).trans hc)

lemma log_two_le : Real.log 2 ≤ 6932 / 10000 := by
  have := Real.log_two_lt_d9; linarith

lemma log_three_le : Real.log 3 ≤ 10987 / 10000 := by
  have := log_three_near; rw [abs_le] at this; unfold l3c etaL at this; push_cast at this
  linarith [this.2]

lemma log_four_le : Real.log 4 ≤ 13864 / 10000 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; have := log_two_le; push_cast; linarith

/-- Lipschitz bound for `F` on a cell. -/
theorem Fex_sub_le {s s0 : ℂ} {ρ tlo : ℝ} (hσ0 : 1 / 2 ≤ s0.re) (hd : ‖s - s0‖ ≤ ρ)
    (hρ4 : ρ * (13864 / 10000) ≤ 1) (htlo : 0 < tlo) (hts : tlo ≤ |s.im|) (hts0 : tlo ≤ |s0.im|) :
    ‖Fex s - Fex s0‖ ≤
      7072 / 10000 * (ρ * (6932 / 10000) * (1 + ρ * (6932 / 10000))) +
      5774 / 10000 * (ρ * (10987 / 10000) * (1 + ρ * (10987 / 10000))) +
      2 * (ρ * (13864 / 10000) * (1 + ρ * (13864 / 10000))) / tlo + 2 * ρ / (tlo * tlo) +
      (ρ * (13864 / 10000) * (1 + ρ * (13864 / 10000))) / 4 := by
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans hd
  have h2 := cpow_sub_le (b := 2) (by norm_num) (s := s)
    (norm_cpow_neg_le 2 (by norm_num) hσ0 (c := 7072 / 10000) (by norm_num) (by norm_num))
    (by simpa using log_two_le) hd (by nlinarith)
  have h3 := cpow_sub_le (b := 3) (by norm_num) (s := s)
    (norm_cpow_neg_le 3 (by norm_num) hσ0 (c := 5774 / 10000) (by norm_num) (by norm_num))
    (by simpa using log_three_le) hd (by nlinarith)
  have h4 := cpow_sub_le (b := 4) (by norm_num) (s := s)
    (norm_cpow_neg_le 4 (by norm_num) hσ0 (c := 1 / 2) (by norm_num) (by norm_num))
    (by simpa using log_four_le) hd hρ4
  have n4 : ‖(4 : ℂ) ^ (-s0)‖ ≤ 1 / 2 := by
    have := norm_cpow_neg_le 4 (by norm_num) hσ0 (c := 1 / 2) (by norm_num) (by norm_num)
    simpa using this
  simp only [Nat.cast_ofNat] at h2 h3 h4
  -- the `1/(s-1)` factors
  have hn1 : tlo ≤ ‖s - 1‖ := by
    refine hts.trans ?_
    have := Complex.abs_im_le_norm (s - 1)
    simpa using this
  have hn10 : tlo ≤ ‖s0 - 1‖ := by
    refine hts0.trans ?_
    have := Complex.abs_im_le_norm (s0 - 1)
    simpa using this
  have hne : s - 1 ≠ 0 := fun h => by rw [h, norm_zero] at hn1; linarith
  have hne0 : s0 - 1 ≠ 0 := fun h => by rw [h, norm_zero] at hn10; linarith
  have hinv : ‖(s - 1)⁻¹‖ ≤ 1 / tlo := by
    rw [norm_inv]; exact inv_anti₀ htlo hn1 |>.trans (le_of_eq (one_div tlo).symm)
  have hinvdiff : ‖(s - 1)⁻¹ - (s0 - 1)⁻¹‖ ≤ ρ / (tlo * tlo) := by
    rw [inv_sub_inv hne hne0, norm_div, norm_mul]
    rw [show s0 - 1 - (s - 1) = -(s - s0) by ring, norm_neg]
    apply div_le_div₀ hρ hd (by positivity) (mul_le_mul hn1 hn10 htlo.le (norm_nonneg _))
  have hT1 : ‖(4 : ℂ) ^ (-s) * (s - 1)⁻¹ - (4 : ℂ) ^ (-s0) * (s0 - 1)⁻¹‖ ≤
      (1 / 2 * (ρ * (13864 / 10000) * (1 + ρ * (13864 / 10000)))) * (1 / tlo) +
        1 / 2 * (ρ / (tlo * tlo)) := by
    rw [show (4 : ℂ) ^ (-s) * (s - 1)⁻¹ - (4 : ℂ) ^ (-s0) * (s0 - 1)⁻¹ =
      ((4 : ℂ) ^ (-s) - (4 : ℂ) ^ (-s0)) * (s - 1)⁻¹ +
        (4 : ℂ) ^ (-s0) * ((s - 1)⁻¹ - (s0 - 1)⁻¹) by ring]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul]
    · exact mul_le_mul h4 hinv (norm_nonneg _) (by positivity)
    · exact mul_le_mul n4 hinvdiff (norm_nonneg _) (by norm_num)
  have hsplit : Fex s - Fex s0 = ((2 : ℂ) ^ (-s) - (2 : ℂ) ^ (-s0)) +
      ((3 : ℂ) ^ (-s) - (3 : ℂ) ^ (-s0)) +
      ((4 : ℚ) : ℂ) * ((4 : ℂ) ^ (-s) * (s - 1)⁻¹ - (4 : ℂ) ^ (-s0) * (s0 - 1)⁻¹) +
      ((1 / 2 : ℚ) : ℂ) * ((4 : ℂ) ^ (-s) - (4 : ℂ) ^ (-s0)) := by
    unfold Fex; ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add_left (norm_add_le _ _) _).trans ?_
  refine (add_le_add_left (add_le_add_left (norm_add_le _ _) _) _).trans ?_
  rw [norm_mul, norm_mul]
  have e4 : ‖((4 : ℚ) : ℂ)‖ = 4 := by simp
  have e2 : ‖((1 / 2 : ℚ) : ℂ)‖ = 1 / 2 := by simp
  rw [e4, e2]
  have hfin : 2 * (ρ * (13864 / 10000) * (1 + ρ * (13864 / 10000))) / tlo + 2 * ρ / (tlo * tlo)
      = 4 * ((1 / 2 * (ρ * (13864 / 10000) * (1 + ρ * (13864 / 10000)))) * (1 / tlo) +
        1 / 2 * (ρ / (tlo * tlo))) := by
    field_simp; ring
  have h4' : 1 / 2 * ‖(4 : ℂ) ^ (-s) - (4 : ℂ) ^ (-s0)‖ ≤
      (ρ * (13864 / 10000) * (1 + ρ * (13864 / 10000))) / 4 := by
    have := h4; linarith
  linarith [mul_le_mul_of_nonneg_left hT1 (by norm_num : (0 : ℝ) ≤ 4), hfin]


end

section
open Kerr.File14RH Disc
open ZetaGrowth ZetaGrowthNeg ZetaGrowthEM3

/-! ### The Euler–Maclaurin error `ζ − F` -/

lemma norm_add_nat_le (s : ℂ) (k : ℝ) (hk : 0 ≤ k) : ‖s + k‖ ≤ (|s.re| + k) + |s.im| := by
  refine (Disc.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [add_re, ofReal_re, add_im, ofReal_im, add_zero]
  have := abs_add_le s.re k
  rw [_root_.abs_of_nonneg hk] at this
  linarith

lemma four_rpow_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) (k : ℕ) :
    (4 : ℝ) ^ (-σ - k) ≤ 1 / 2 * (1 / 4) ^ k := by
  rw [Real.rpow_sub (by norm_num), Real.rpow_natCast, div_eq_mul_inv, ← inv_pow]
  have h := rpow_neg_le_const 4 (by norm_num) hσ (c := 1 / 2) (by norm_num) (by norm_num)
  push_cast at h
  norm_num
  exact h

theorem zeta_sub_Fex_le {s : ℂ} (hσ1 : 1 / 2 ≤ s.re) (hσ2 : s.re ≤ 1) {thi : ℝ}
    (ht : |s.im| ≤ thi) (hs1 : s ≠ 1) :
    ‖riemannZeta s - Fex s‖ ≤
      (1 + thi) / 96 + (1 + thi) * (2 + thi) * (3 + thi) / (720 * 128) +
        (1 + thi) * (2 + thi) * (3 + thi) * (4 + thi) * (11548 / 10000) / (720 * 64) := by
  have hz := zeta_eq_sum_add_tail₄ (s := s) (by linarith) hs1 3
  have hthi : 0 ≤ thi := (abs_nonneg _).trans ht
  have hre : |s.re| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have nA : ‖s‖ ≤ 1 + thi := by
    refine (Disc.norm_le_abs_re_add_abs_im _).trans ?_; linarith
  have nB : ‖s + 1‖ ≤ 2 + thi := by
    have := norm_add_nat_le s 1 (by norm_num); push_cast at this; linarith
  have nC : ‖s + 2‖ ≤ 3 + thi := by
    have := norm_add_nat_le s 2 (by norm_num); push_cast at this; linarith
  have nD : ‖s + 3‖ ≤ 4 + thi := by
    have := norm_add_nat_le s 3 (by norm_num); push_cast at this; linarith
  -- identify the main part with `Fex`
  have hmain : ∑ i ∈ Finset.range 3, ((i : ℂ) + 1) ^ (-s) + ((3 : ℕ) + 1 : ℂ) ^ (1 - s) / (s - 1)
      + ((3 : ℕ) + 1 : ℂ) ^ (-s) / 2 = Fex s := by
    have h4 : (4 : ℂ) ^ (1 - s) = 4 * (4 : ℂ) ^ (-s) := by
      rw [show (1 : ℂ) - s = 1 + -s by ring, cpow_add _ _ (by norm_num), cpow_one]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    norm_num
    rw [h4]; unfold Fex; push_cast; ring
  have hdiff : riemannZeta s - Fex s = s / 12 * ((3 : ℕ) + 1 : ℂ) ^ (-s - 1)
      - s * (s + 1) * (s + 2) / 720 * ((3 : ℕ) + 1 : ℂ) ^ (-s - 3)
      + ∑' n : ℕ, emTerm₄ (n + 3 + 1) s := by
    rw [hz, ← hmain]; push_cast; ring
  rw [hdiff]
  have e4 : ((3 : ℕ) + 1 : ℂ) = ((4 : ℕ) : ℂ) := by push_cast; ring
  rw [e4]
  refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [norm_mul, norm_div, norm_natCast_cpow_of_pos (by norm_num)]
    have : ‖(12 : ℂ)‖ = 12 := by simp
    rw [this]
    have hp := four_rpow_le hσ1 1
    simp only [sub_re, neg_re, one_re, Nat.cast_one] at hp ⊢
    push_cast at hp ⊢
    calc ‖s‖ / 12 * (4 : ℝ) ^ (-s.re - 1) ≤ (1 + thi) / 12 * (1 / 2 * (1 / 4)) :=
          mul_le_mul (div_le_div_of_nonneg_right nA (by norm_num)) (by simpa using hp)
            (by positivity) (by positivity)
      _ = (1 + thi) / 96 := by ring
  · rw [norm_mul, norm_div, norm_mul, norm_mul, norm_natCast_cpow_of_pos (by norm_num)]
    have : ‖(720 : ℂ)‖ = 720 := by simp
    rw [this]
    have hp := four_rpow_le hσ1 3
    have hre3 : (-s - 3).re = -s.re - ((3 : ℕ) : ℝ) := by simp
    rw [hre3]
    have hABC : ‖s‖ * ‖s + 1‖ * ‖s + 2‖ ≤ (1 + thi) * (2 + thi) * (3 + thi) :=
      mul_le_mul (mul_le_mul nA nB (norm_nonneg _) (by positivity)) nC (norm_nonneg _)
        (by positivity)
    calc ‖s‖ * ‖s + 1‖ * ‖s + 2‖ / 720 * (4 : ℝ) ^ (-s.re - ((3 : ℕ) : ℝ))
        ≤ (1 + thi) * (2 + thi) * (3 + thi) / 720 * (1 / 2 * (1 / 4) ^ 3) :=
          mul_le_mul (div_le_div_of_nonneg_right hABC (by norm_num)) hp (by positivity)
            (by positivity)
      _ = (1 + thi) * (2 + thi) * (3 + thi) / (720 * 128) := by ring
  · -- the tail
    set P : ℝ := ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ / 720 with hP
    have hP0 : 0 ≤ P := by positivity
    have hPle : P ≤ (1 + thi) * (2 + thi) * (3 + thi) * (4 + thi) / 720 := by
      have := mul_le_mul (mul_le_mul (mul_le_mul nA nB (norm_nonneg _) (by positivity)) nC
        (norm_nonneg _) (by positivity)) nD (norm_nonneg _) (by positivity)
      exact div_le_div_of_nonneg_right this (by norm_num)
    have hterm : ∀ n : ℕ, ‖emTerm₄ (n + 3 + 1) s‖ ≤
        P * (1 / 64) * ((n : ℝ) + (3 : ℕ) + 1) ^ (-(3 / 2 : ℝ)) := by
      intro n
      refine (norm_emTerm₄_le (by linarith) hs1 (by omega)).trans ?_
      rw [← hP, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hP0
      push_cast
      have hpos : (0 : ℝ) < (n : ℝ) + 3 + 1 := by positivity
      have hsplit : ((n : ℝ) + 3 + 1) ^ (-s.re - 4) =
          ((n : ℝ) + 3 + 1) ^ (-(3 / 2 : ℝ)) * ((n : ℝ) + 3 + 1) ^ (-s.re - 5 / 2) := by
        rw [← Real.rpow_add hpos]; congr 1; ring
      rw [hsplit, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have h4le : (4 : ℝ) ≤ (n : ℝ) + 3 + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      calc ((n : ℝ) + 3 + 1) ^ (-s.re - 5 / 2) ≤ (4 : ℝ) ^ (-s.re - 5 / 2) :=
            Real.rpow_le_rpow_of_nonpos (by norm_num) h4le (by linarith)
        _ ≤ (4 : ℝ) ^ (-(3 : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 1 / 64 := by rw [Real.rpow_neg (by norm_num)]; norm_num
    have hsum := (summable_add_rpow 3 (a := -(3 / 2 : ℝ)) (by norm_num)).mul_left (P * (1 / 64))
    have htail := tsum_of_norm_bounded hsum.hasSum hterm
    refine htail.trans ?_
    rw [tsum_mul_left]
    have hT := tsum_tail_rpow_le (N := 3) (by norm_num)
    have h3 : ((3 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 5774 / 10000 :=
      rpow_neg_le_const 3 (by norm_num) le_rfl (by norm_num) (by norm_num)
    have hT' : ∑' m : ℕ, ((m : ℝ) + (3 : ℕ) + 1) ^ (-(3 / 2 : ℝ)) ≤ 11548 / 10000 := by
      linarith
    calc P * (1 / 64) * ∑' m : ℕ, ((m : ℝ) + (3 : ℕ) + 1) ^ (-(3 / 2 : ℝ))
        ≤ ((1 + thi) * (2 + thi) * (3 + thi) * (4 + thi) / 720) * (1 / 64) * (11548 / 10000) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hPle (by norm_num)) hT'
            (tsum_nonneg fun _ => by positivity) (by positivity)
      _ = _ := by ring


end

section
open Kerr.File14RH Disc
open ZetaGrowth ZetaGrowthNeg ZetaGrowthEM3

/-! ### The cell certificate -/

/-- `ρℓ(1+ρℓ)`. -/
def gfun (ρ ℓ : ℚ) : ℚ := ρ * ℓ * (1 + ρ * ℓ)

/-- Lipschitz allowance for a cell of half-width `h` at height `≥ tlo`. -/
def Lcell (h tlo : ℚ) : ℚ :=
  7072 / 10000 * gfun (142 / 100 * h) (6932 / 10000) +
    5774 / 10000 * gfun (142 / 100 * h) (10987 / 10000) +
    2 * gfun (142 / 100 * h) (13864 / 10000) / tlo + 2 * (142 / 100 * h) / (tlo * tlo) +
    gfun (142 / 100 * h) (13864 / 10000) / 4

/-- Euler–Maclaurin error allowance at height `≤ thi`. -/
def Ecell (thi : ℚ) : ℚ :=
  (1 + thi) / 96 + (1 + thi) * (2 + thi) * (3 + thi) / (720 * 128) +
    (1 + thi) * (2 + thi) * (3 + thi) * (4 + thi) * (11548 / 10000) / (720 * 64)

/-- The certificate for the cell `[σ₀ − h, σ₀ + h] × [t₀ − h, t₀ + h]`. -/
def cellOK (σ0 t0 h : ℚ) : Bool :=
  decide (0 < h) && decide (0 < t0 - h) && decide (1 / 2 ≤ σ0 - h) &&
    decide (142 / 100 * h * (13864 / 10000) ≤ 1) &&
    decide (|-σ0 * l2c| + |-t0 * l2c| ≤ 16) && decide (|-σ0 * l3c| + |-t0 * l3c| ≤ 16) &&
    decide ((|σ0| + |t0|) * etaL ≤ 1 / 2) &&
    decide (0 ≤ (Fdisc σ0 t0).r + Lcell h (t0 - h) + Ecell (t0 + h)) &&
    decide (((Fdisc σ0 t0).r + Lcell h (t0 - h) + Ecell (t0 + h)) ^ 2 <
      (Fdisc σ0 t0).re ^ 2 + (Fdisc σ0 t0).im ^ 2)

theorem cellOK_sound {σ0 t0 h : ℚ} (hc : cellOK σ0 t0 h = true) {s : ℂ}
    (h1 : |s.re - σ0| ≤ h) (h2 : |s.im - t0| ≤ h) (hσ1 : 1 / 2 ≤ s.re) (hσ2 : s.re ≤ 1) :
    riemannZeta s ≠ 0 := by
  simp only [cellOK, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hh, htlo⟩, hσ0⟩, hρ4⟩, h16a⟩, h16b⟩, hη⟩, hm0⟩, hm⟩ := hc
  set F := Fdisc σ0 t0 with hFdef
  set s0 : ℂ := (σ0 : ℂ) + (t0 : ℂ) * I with hs0
  have hs0re : s0.re = σ0 := by simp [hs0]
  have hs0im : s0.im = t0 := by simp [hs0]
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  -- distance to the centre
  have hd : ‖s - s0‖ ≤ ((142 / 100 * h : ℚ) : ℝ) := by
    apply norm_le_of_sq (by positivity)
    simp only [sub_re, sub_im, hs0re, hs0im]
    have a1 : (s.re - σ0) ^ 2 ≤ (h : ℝ) ^ 2 := sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
    have a2 : (s.im - t0) ^ 2 ≤ (h : ℝ) ^ 2 := sq_le_sq' (abs_le.mp h2).1 (abs_le.mp h2).2
    push_cast; nlinarith
  have htloR : (0 : ℝ) < ((t0 - h : ℚ) : ℝ) := by exact_mod_cast htlo
  have hsim : ((t0 - h : ℚ) : ℝ) ≤ |s.im| := by
    push_cast; have := (abs_le.mp h2).1; rw [abs_of_pos (by push_cast at htloR; linarith)]
    linarith
  have hs0im' : ((t0 - h : ℚ) : ℝ) ≤ |s0.im| := by
    rw [hs0im]; push_cast
    rw [abs_of_pos (by push_cast at htloR; linarith)]; linarith
  have hσ0R : (1 / 2 : ℝ) ≤ s0.re := by
    rw [hs0re]; have : ((1 / 2 : ℚ) : ℝ) ≤ ((σ0 - h : ℚ) : ℝ) := by exact_mod_cast hσ0
    push_cast at this; linarith
  have hρ4R : ((142 / 100 * h : ℚ) : ℝ) * (13864 / 10000) ≤ 1 := by
    have : (((142 / 100 * h * (13864 / 10000)) : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := by exact_mod_cast hρ4
    push_cast at this ⊢; linarith
  have hL := Fex_sub_le hσ0R hd hρ4R htloR hsim hs0im'
  have hLc : (Lcell h (t0 - h) : ℝ) = 7072 / 10000 * (((142 / 100 * h : ℚ) : ℝ) * (6932 / 10000) *
      (1 + ((142 / 100 * h : ℚ) : ℝ) * (6932 / 10000))) +
      5774 / 10000 * (((142 / 100 * h : ℚ) : ℝ) * (10987 / 10000) *
      (1 + ((142 / 100 * h : ℚ) : ℝ) * (10987 / 10000))) +
      2 * (((142 / 100 * h : ℚ) : ℝ) * (13864 / 10000) *
      (1 + ((142 / 100 * h : ℚ) : ℝ) * (13864 / 10000))) / ((t0 - h : ℚ) : ℝ) +
      2 * ((142 / 100 * h : ℚ) : ℝ) / (((t0 - h : ℚ) : ℝ) * ((t0 - h : ℚ) : ℝ)) +
      (((142 / 100 * h : ℚ) : ℝ) * (13864 / 10000) *
      (1 + ((142 / 100 * h : ℚ) : ℝ) * (13864 / 10000))) / 4 := by
    unfold Lcell gfun; push_cast; ring
  rw [← hLc] at hL
  have hsimhi : |s.im| ≤ ((t0 + h : ℚ) : ℝ) := by
    have hpos : (0 : ℝ) < (t0 : ℝ) - h := by push_cast at htloR; linarith
    push_cast; rw [abs_le]; constructor <;> linarith [(abs_le.mp h2).1, (abs_le.mp h2).2]
  have hs1 : s ≠ 1 := by
    intro e; rw [e] at hsim; simp at hsim; linarith
  have hE := zeta_sub_Fex_le hσ1 hσ2 hsimhi hs1
  have hEc : (Ecell (t0 + h) : ℝ) = (1 + ((t0 + h : ℚ) : ℝ)) / 96 +
      (1 + ((t0 + h : ℚ) : ℝ)) * (2 + ((t0 + h : ℚ) : ℝ)) * (3 + ((t0 + h : ℚ) : ℝ)) / (720 * 128) +
      (1 + ((t0 + h : ℚ) : ℝ)) * (2 + ((t0 + h : ℚ) : ℝ)) * (3 + ((t0 + h : ℚ) : ℝ)) *
        (4 + ((t0 + h : ℚ) : ℝ)) * (11548 / 10000) / (720 * 64) := by
    unfold Ecell; push_cast; ring
  rw [← hEc] at hE
  have hFc := Fdisc_contains σ0 t0 (by linarith [htlo, hh]) h16a h16b hη
  rw [← hFdef] at hFc
  unfold Contains at hFc
  -- `‖F.c‖ > m`
  set m : ℚ := F.r + Lcell h (t0 - h) + Ecell (t0 + h) with hmdef
  have hmR : (0 : ℝ) ≤ m := by exact_mod_cast hm0
  have hcm : (m : ℝ) < ‖F.c‖ := by
    by_contra hle
    push_neg at hle
    have hsq : ‖F.c‖ ^ 2 = (F.re : ℝ) ^ 2 + (F.im : ℝ) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, c_re, c_im]; ring
    have : ‖F.c‖ ^ 2 ≤ (m : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
    have hm' : ((m ^ 2 : ℚ) : ℝ) < ((F.re ^ 2 + F.im ^ 2 : ℚ) : ℝ) := by exact_mod_cast hm
    push_cast at hm'
    linarith
  -- conclude
  intro hz
  have k1 : ‖Fex s0‖ ≥ ‖F.c‖ - F.r := by
    have := norm_sub_norm_le F.c (Fex s0)
    rw [norm_sub_rev] at this; linarith
  have k2 : ‖Fex s‖ ≥ ‖Fex s0‖ - Lcell h (t0 - h) := by
    have := norm_sub_norm_le (Fex s0) (Fex s)
    rw [norm_sub_rev (Fex s0)] at this; linarith
  have k3 : ‖Fex s‖ ≤ Ecell (t0 + h) := by
    rw [hz, zero_sub, norm_neg] at hE; exact hE
  have hmm : (m : ℝ) = F.r + Lcell h (t0 - h) + Ecell (t0 + h) := by rw [hmdef]; push_cast; ring
  linarith

/-! ### Rows and the grid -/

/-- A row `a ≤ Im s ≤ b` split into `k` square cells across `1/2 ≤ Re s ≤ 1`. -/
def rowOK (a b : ℚ) (k : ℕ) : Bool :=
  decide (a < b) && decide (1 / 2 ≤ (b - a) * k) &&
    (List.range k).all fun j => cellOK (1 / 2 + (b - a) / 2 * (2 * j + 1)) ((a + b) / 2) ((b - a) / 2)

theorem rowOK_sound {a b : ℚ} {k : ℕ} (hr : rowOK a b k = true) {s : ℂ}
    (ht1 : (a : ℝ) ≤ s.im) (ht2 : s.im ≤ b) (hσ1 : 1 / 2 ≤ s.re) (hσ2 : s.re < 1) :
    riemannZeta s ≠ 0 := by
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hr
  obtain ⟨⟨hab, hk⟩, hcells⟩ := hr
  set h : ℚ := (b - a) / 2 with hhdef
  have hh0 : (0 : ℚ) < h := by rw [hhdef]; linarith
  have hh : (0 : ℝ) < h := by exact_mod_cast hh0
  set x : ℝ := (s.re - 1 / 2) / (2 * h) with hx
  have hx0 : 0 ≤ x := div_nonneg (by linarith) (by linarith)
  set j : ℕ := ⌊x⌋₊ with hj
  have hjx : (j : ℝ) ≤ x := Nat.floor_le hx0
  have hxj : x < j + 1 := Nat.lt_floor_add_one x
  have hkR : (1 / 2 : ℝ) ≤ 2 * h * k := by
    have : ((1 / 2 : ℚ) : ℝ) ≤ (((b - a) * k : ℚ) : ℝ) := by exact_mod_cast hk
    rw [hhdef]; push_cast at this ⊢; linarith
  have hjk : j < k := by
    by_contra hjk; push_neg at hjk
    have : (k : ℝ) ≤ j := by exact_mod_cast hjk
    have h2 : (k : ℝ) ≤ x := this.trans hjx
    rw [hx, le_div_iff₀ (by linarith)] at h2
    nlinarith
  have hcell := hcells j hjk
  refine cellOK_sound hcell ?_ ?_ hσ1 hσ2.le
  · have e1 : (j : ℝ) * (2 * h) ≤ s.re - 1 / 2 := by
      have := mul_le_mul_of_nonneg_right hjx (by linarith : (0 : ℝ) ≤ 2 * h)
      rwa [hx, div_mul_cancel₀ _ (by linarith)] at this
    have e2 : s.re - 1 / 2 < ((j : ℝ) + 1) * (2 * h) := by
      have := mul_lt_mul_of_pos_right hxj (by linarith : (0 : ℝ) < 2 * h)
      rwa [hx, div_mul_cancel₀ _ (by linarith)] at this
    rw [abs_le]; push_cast
    constructor <;> nlinarith
  · rw [abs_le]; push_cast
    have : ((h : ℚ) : ℝ) = ((b : ℝ) - a) / 2 := by rw [hhdef]; push_cast; ring
    rw [this]; constructor <;> linarith

/-- Consecutive rows from `a` up to height `10`. -/
def rowsOK : ℚ → List (ℚ × ℕ) → Bool
  | a, [] => decide (10 ≤ a)
  | a, (b, k) :: rest => rowOK a b k && rowsOK b rest

theorem rowsOK_sound : ∀ (l : List (ℚ × ℕ)) (a : ℚ), rowsOK a l = true →
    ∀ s : ℂ, (a : ℝ) ≤ s.im → s.im < 10 → 1 / 2 ≤ s.re → s.re < 1 → riemannZeta s ≠ 0
  | [], a, h, s, ha, h10, _, _ => by
    simp only [rowsOK, decide_eq_true_eq] at h
    have : (10 : ℝ) ≤ a := by exact_mod_cast h
    linarith
  | (b, k) :: rest, a, h, s, ha, h10, hσ1, hσ2 => by
    simp only [rowsOK, Bool.and_eq_true] at h
    by_cases hb : s.im ≤ b
    · exact rowOK_sound h.1 ha hb hσ1 hσ2
    · exact rowsOK_sound rest b h.2 s (le_of_lt (not_le.mp hb)) h10 hσ1 hσ2

/-- The rows (generated offline; checked by the kernel below). -/
def zeroFreeRows : List (ℚ × ℕ) :=
  [((83 : ℚ) / 50, 4), ((91 : ℚ) / 50, 4), ((99 : ℚ) / 50, 4), ((107 : ℚ) / 50, 4),
    ((23 : ℚ) / 10, 4), ((5 : ℚ) / 2, 3), ((27 : ℚ) / 10, 3), ((29 : ℚ) / 10, 3),
    ((31 : ℚ) / 10, 3), ((33 : ℚ) / 10, 3), ((71 : ℚ) / 20, 2), ((19 : ℚ) / 5, 2),
    ((81 : ℚ) / 20, 2), ((43 : ℚ) / 10, 2), ((91 : ℚ) / 20, 2), ((24 : ℚ) / 5, 2),
    ((51 : ℚ) / 10, 2), ((27 : ℚ) / 5, 2), ((57 : ℚ) / 10, 2), ((6 : ℚ) / 1, 2),
    ((63 : ℚ) / 10, 2), ((67 : ℚ) / 10, 2), ((71 : ℚ) / 10, 2), ((15 : ℚ) / 2, 2),
    ((79 : ℚ) / 10, 2), ((83 : ℚ) / 10, 2), ((87 : ℚ) / 10, 2), ((91 : ℚ) / 10, 2),
    ((19 : ℚ) / 2, 2), ((49 : ℚ) / 5, 2), ((101 : ℚ) / 10, 2)]

set_option maxRecDepth 100000 in
theorem zeroFreeRows_ok : rowsOK (3 / 2) zeroFreeRows = true := by decide +kernel


end

section
open Kerr.File14RH Disc

/-- No zeros with `1/2 ≤ Re s < 1`, `0 ≤ Im s < 10`. -/
theorem zeta_ne_zero_quarter {s : ℂ} (hσ1 : 1 / 2 ≤ s.re) (hσ2 : s.re < 1) (ht0 : 0 ≤ s.im)
    (ht : s.im < 10) : riemannZeta s ≠ 0 := by
  by_cases hlow : s.im ≤ 3 / 2
  · exact zeta_ne_zero_low (by linarith) hσ2 (by rw [_root_.abs_of_nonneg ht0]; exact hlow)
  · push_neg at hlow
    exact rowsOK_sound zeroFreeRows (3 / 2) zeroFreeRows_ok s (by push_cast; linarith) ht hσ1 hσ2

/-- **`ζ(s) ≠ 0` for `0 < Re s < 1`, `|Im s| < 10`.** -/
theorem zeta_ne_zero_strip_lt_ten {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (ht : |s.im| < 10) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hs : IsNonTrivialZero s := ⟨hz, h0, h1⟩
  -- move to `Re ≥ 1/2`
  obtain ⟨w, hw, hwre, hwim⟩ : ∃ w : ℂ, IsNonTrivialZero w ∧ 1 / 2 ≤ w.re ∧ |w.im| = |s.im| := by
    by_cases hre : 1 / 2 ≤ s.re
    · exact ⟨s, hs, hre, rfl⟩
    · refine ⟨1 - conj s, zero_symmetry s hs, ?_, ?_⟩
      · simp only [sub_re, one_re, conj_re]; linarith
      · simp
  -- move to `Im ≥ 0`
  obtain ⟨v, hv, hvre, hvim0, hvim⟩ : ∃ v : ℂ, IsNonTrivialZero v ∧ 1 / 2 ≤ v.re ∧ 0 ≤ v.im ∧
      v.im = |w.im| := by
    by_cases him : 0 ≤ w.im
    · exact ⟨w, hw, hwre, him, (_root_.abs_of_nonneg him).symm⟩
    · push_neg at him
      refine ⟨conj w, ⟨?_, by simpa using hw.2.1, by simpa using hw.2.2⟩, by simpa using hwre,
        by simp; linarith, by simp [_root_.abs_of_neg him]⟩
      rw [Kerr.ZetaConj.riemannZeta_conj, hw.1, map_zero]
  exact zeta_ne_zero_quarter hvre hv.2.2 hvim0 (by rw [hvim, hwim]; exact ht) hv.1

/-- **Source `small_rh_verified_small`, proved**: for `T ≤ 10` there are no zeros with
`0 < Re s < 1`, `|Im s| < T` (Euler–Maclaurin with a kernel-checked interval certificate on
77 cells, plus hp-proof's `|Im s| ≤ 3/2` lemma). -/
theorem small_rh_verified_small (T : ℝ) (hT : T ≤ 10) : SmallRHVerified T :=
  fun _ hs => zeta_ne_zero_strip_lt_ten hs.1 hs.2.1 (lt_of_lt_of_le hs.2.2 hT)

theorem riemannZeta_half_ne_zero : riemannZeta (1 / 2) ≠ 0 :=
  zeta_ne_zero_strip_lt_ten (by norm_num) (by norm_num) (by norm_num)

/-- The source's `LindelofHypothesis` is **false** (`t = 0` forces `ζ(1/2) = 0`), so source
`RH_implies_Lindelof` as stated would prove `¬RH`; the corrected statement is
`RH_implies_Lindelof_statement`. -/
theorem not_LindelofHypothesis : ¬ LindelofHypothesis :=
  not_LindelofHypothesis_of riemannZeta_half_ne_zero


end


section
open Kerr.File14RH Disc
open ZetaGrowth ZetaGrowthNeg ZetaGrowthEM3

/-! ## Extension: no zeros with `|Im s| < 14`

Same method as for `|Im s| < 10`, now with nineteen Euler–Maclaurin terms (boundary point
`20`), a first-order expansion of the main sum on each cell, rectangular cells, and a
kernel-checked table of logarithms `log 1, …, log 20`. -/

/-- Disc for `exp (a + b i)`, valid when `|a| + |b| ≤ 64`. -/
def expDisc7 (a b : ℚ) : Disc := squareN 7 (expSmall (exact (a / 128) (b / 128)) 14)

theorem expDisc7_contains (a b : ℚ) (h : |a| + |b| ≤ 64) :
    (expDisc7 a b).Contains (exp ((a : ℂ) + (b : ℂ) * I)) := by
  have hw : (exact (a / 128) (b / 128)).nb ≤ 1 := by
    simp only [nb, exact, abs_div]
    rw [abs_of_pos (by norm_num : (0 : ℚ) < 128)]
    linarith
  have h1 := expSmall_contains (exact (a / 128) (b / 128)) rfl hw 14 (by norm_num)
  have h2 := squareN_contains 7 h1
  unfold expDisc7
  convert h2 using 2
  simp only [c, exact]; push_cast; ring

/-- Disc for `n^{-(σ + t i)}` (wide range). -/
def powDisc7 (lc σ t : ℚ) : Disc :=
  mul (expDisc7 (-σ * lc) (-t * lc)) ⟨1, 0, 2 * (|σ| + |t|) * etaL⟩

theorem powDisc7_contains {n : ℕ} (hn : 0 < n) {lc : ℚ} (hl : |Real.log n - lc| ≤ etaL)
    (σ t : ℚ) (h64 : |-σ * lc| + |-t * lc| ≤ 64) (hη : (|σ| + |t|) * etaL ≤ 1 / 2) :
    (powDisc7 lc σ t).Contains ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  set w : ℂ := -((σ : ℂ) + (t : ℂ) * I) with hw
  set L : ℝ := Real.log n with hL
  have hlog : Complex.log (n : ℂ) = ((L : ℝ) : ℂ) := by rw [hL, natCast_log]
  have hsplit : (n : ℂ) ^ w = exp ((lc : ℂ) * w) * exp (((L - lc : ℝ) : ℂ) * w) := by
    rw [cpow_def_of_ne_zero hn0, ← Complex.exp_add, hlog]
    congr 1; push_cast; ring
  rw [hsplit]
  apply mul_contains
  · have := expDisc7_contains (-σ * lc) (-t * lc) h64
    convert this using 2
    rw [hw]; push_cast; ring
  · unfold Contains c
    simp only [Rat.cast_one, Rat.cast_zero, zero_mul, add_zero]
    have hwn : ‖w‖ ≤ |(σ : ℝ)| + |(t : ℝ)| := by
      rw [hw, norm_neg]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, mul_one, ← Complex.ofReal_ratCast, ← Complex.ofReal_ratCast,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    have hl' : |L - lc| ≤ (etaL : ℝ) := by exact_mod_cast hl
    have hu : ‖((L - lc : ℝ) : ℂ) * w‖ ≤ (|(σ : ℝ)| + |(t : ℝ)|) * etaL := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul hwn hl' (abs_nonneg _) (by positivity)
    have hη' : (|(σ : ℝ)| + |(t : ℝ)|) * (etaL : ℝ) ≤ 1 / 2 := by
      have := (Rat.cast_le (K := ℝ)).mpr hη
      push_cast at this; exact this
    have hb := Complex.norm_exp_sub_one_le (x := ((L - lc : ℝ) : ℂ) * w) (by linarith)
    have hr : (((2 * (|σ| + |t|) * etaL : ℚ)) : ℝ) = 2 * ((|(σ : ℝ)| + |(t : ℝ)|) * etaL) := by
      push_cast; ring
    rw [hr]
    calc ‖exp (((L - lc : ℝ) : ℂ) * w) - 1‖ ≤ 2 * ‖((L - lc : ℝ) : ℂ) * w‖ := hb
      _ ≤ 2 * ((|(σ : ℝ)| + |(t : ℝ)|) * etaL) := by linarith

/-! ### Logarithm table -/

/-- `lcTab.getD i 0 ≈ log (i + 1)`, `i < 20`. -/
def lcTab : List ℚ :=
  [(0 : ℚ) / 100000000000, (69314718056 : ℚ) / 100000000000,
    (109861228867 : ℚ) / 100000000000, (138629436112 : ℚ) / 100000000000,
    (160943791243 : ℚ) / 100000000000, (179175946923 : ℚ) / 100000000000,
    (194591014906 : ℚ) / 100000000000, (207944154168 : ℚ) / 100000000000,
    (219722457734 : ℚ) / 100000000000, (230258509299 : ℚ) / 100000000000,
    (239789527280 : ℚ) / 100000000000, (248490664979 : ℚ) / 100000000000,
    (256494935746 : ℚ) / 100000000000, (263905732962 : ℚ) / 100000000000,
    (270805020110 : ℚ) / 100000000000, (277258872224 : ℚ) / 100000000000,
    (283321334406 : ℚ) / 100000000000, (289037175790 : ℚ) / 100000000000,
    (294443897917 : ℚ) / 100000000000, (299573227355 : ℚ) / 100000000000]

/-- `lc i = lcTab[i]`. -/
def lc (i : ℕ) : ℚ := lcTab.getD i 0

/-- Kernel-checkable bracket `exp(lc − η) < n < exp(lc + η)`. -/
def logBracket (n : ℕ) (l : ℚ) : Bool :=
  decide (|l - etaL| ≤ 16) && decide (|l + etaL| ≤ 16) &&
    decide ((expDisc (l - etaL) 0).re + (expDisc (l - etaL) 0).r < n) &&
    decide ((n : ℚ) < (expDisc (l + etaL) 0).re - (expDisc (l + etaL) 0).r)

theorem logBracket_sound {n : ℕ} (hn : 0 < n) {l : ℚ} (h : logBracket n l = true) :
    |Real.log n - l| ≤ etaL := by
  simp only [logBracket, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, c1⟩, c2⟩ := h
  have hlo := exp_rat_near (l - etaL) h1
  have hhi := exp_rat_near (l + etaL) h2
  have c1' : ((expDisc (l - etaL) 0).re : ℝ) + (expDisc (l - etaL) 0).r < n := by
    exact_mod_cast c1
  have c2' : (n : ℝ) < ((expDisc (l + etaL) 0).re : ℝ) - (expDisc (l + etaL) 0).r := by
    exact_mod_cast c2
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have e1 : Real.exp ((l - etaL : ℚ) : ℝ) < n := by
    have := (abs_le.mp hlo).2; linarith
  have e2 : (n : ℝ) < Real.exp ((l + etaL : ℚ) : ℝ) := by
    have := (abs_le.mp hhi).1; linarith
  have l1 : ((l - etaL : ℚ) : ℝ) < Real.log n := by
    rw [Real.lt_log_iff_exp_lt hnR]; exact e1
  have l2 : Real.log n < ((l + etaL : ℚ) : ℝ) := by
    rw [Real.log_lt_iff_lt_exp hnR]; exact e2
  push_cast at l1 l2
  rw [abs_le]; constructor <;> linarith

/-- All twenty brackets. -/
def lcTabOK : Bool := (List.range 20).all fun i => logBracket (i + 1) (lc i)

set_option maxRecDepth 100000 in
theorem lcTabOK_true : lcTabOK = true := by decide +kernel

theorem lc_near {i : ℕ} (hi : i < 20) : |Real.log ((i + 1 : ℕ) : ℝ) - lc i| ≤ etaL := by
  have h := lcTabOK_true
  simp only [lcTabOK, List.all_eq_true, List.mem_range] at h
  exact logBracket_sound (Nat.succ_pos i) (h i hi)

/-! ### Rational and disc sums -/

/-- `∑_{i<k} f i` in `ℚ`, by recursion. -/
def sumQ (f : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | k + 1 => sumQ f k + f k

lemma sumQ_cast (f : ℕ → ℚ) (k : ℕ) : ((sumQ f k : ℚ) : ℝ) = ∑ i ∈ Finset.range k, (f i : ℝ) := by
  induction k with
  | zero => simp [sumQ]
  | succ k ih => rw [sumQ, Finset.sum_range_succ]; push_cast; rw [ih]

/-- Disc sum. -/
def sumD (f : ℕ → Disc) : ℕ → Disc
  | 0 => exact 0 0
  | k + 1 => add (sumD f k) (f k)

lemma sumD_contains {f : ℕ → Disc} {g : ℕ → ℂ} (k : ℕ) (h : ∀ i < k, (f i).Contains (g i)) :
    (sumD f k).Contains (∑ i ∈ Finset.range k, g i) := by
  induction k with
  | zero => simpa [sumD] using exact_contains 0 0
  | succ k ih =>
    rw [sumD, Finset.sum_range_succ]
    exact add_contains (ih fun i hi => h i (by omega)) (h k (by omega))


end

section
open Kerr.File14RH Disc
open ZetaGrowth ZetaGrowthNeg ZetaGrowthEM3

/-! ### The approximant with nineteen terms and boundary point `20` -/

/-- `(i+1)^{-s}`. -/
def npow (i : ℕ) (s : ℂ) : ℂ := ((i : ℂ) + 1) ^ (-s)

/-- `F₂₀(s) = ∑_{n ≤ 19} n^{-s} + 20·20^{-s}/(s−1) + 20^{-s}/2`. -/
def F20 (s : ℂ) : ℂ :=
  ∑ i ∈ Finset.range 19, npow i s + ((20 : ℚ) : ℂ) * (npow 19 s * (s - 1)⁻¹) +
    ((1 / 2 : ℚ) : ℂ) * npow 19 s

/-- `G(s) = ∑_{n ≤ 19} log n · n^{-s}` (so that `F₂₀' = −G + …`). -/
def G20 (s : ℂ) : ℂ := ∑ i ∈ Finset.range 19, ((Real.log ((i + 1 : ℕ) : ℝ) : ℝ) : ℂ) * npow i s

lemma npow_eq (i : ℕ) (s : ℂ) : npow i s = (((i + 1 : ℕ) : ℕ) : ℂ) ^ (-s) := by
  unfold npow; push_cast; rfl

lemma twenty_rpow_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) (k : ℕ) :
    (20 : ℝ) ^ (-σ - k) ≤ 2237 / 10000 * (1 / 20) ^ k := by
  rw [Real.rpow_sub (by norm_num), Real.rpow_natCast, div_eq_mul_inv, ← inv_pow]
  have h := rpow_neg_le_const 20 (by norm_num) hσ (c := 2237 / 10000) (by norm_num) (by norm_num)
  push_cast at h
  norm_num
  exact h

/-- Error bound for `ζ − F₂₀`. -/
theorem zeta_sub_F20_le {s : ℂ} (hσ1 : 1 / 2 ≤ s.re) (hσ2 : s.re ≤ 1) {thi : ℝ}
    (ht : |s.im| ≤ thi) (hs1 : s ≠ 1) :
    ‖riemannZeta s - F20 s‖ ≤
      (1 + thi) * (2237 / 10000) / 240 +
        (1 + thi) * (2 + thi) * (3 + thi) * (2237 / 10000) / (720 * 8000) +
        (1 + thi) * (2 + thi) * (3 + thi) * (4 + thi) * (2 * (2295 / 10000)) / (720 * 8000) := by
  have hz := zeta_eq_sum_add_tail₄ (s := s) (by linarith) hs1 19
  have hthi : 0 ≤ thi := (abs_nonneg _).trans ht
  have hre : |s.re| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have nA : ‖s‖ ≤ 1 + thi := by
    refine (Disc.norm_le_abs_re_add_abs_im _).trans ?_; linarith
  have nB : ‖s + 1‖ ≤ 2 + thi := by
    have := norm_add_nat_le s 1 (by norm_num); push_cast at this; linarith
  have nC : ‖s + 2‖ ≤ 3 + thi := by
    have := norm_add_nat_le s 2 (by norm_num); push_cast at this; linarith
  have nD : ‖s + 3‖ ≤ 4 + thi := by
    have := norm_add_nat_le s 3 (by norm_num); push_cast at this; linarith
  have h20 : (((19 : ℕ) : ℂ) + 1) ^ (1 - s) = ((20 : ℚ) : ℂ) * (((19 : ℕ) : ℂ) + 1) ^ (-s) := by
    rw [show (1 : ℂ) - s = 1 + -s by ring, cpow_add _ _ (by norm_num), cpow_one]; push_cast; ring
  have hdiff : riemannZeta s - F20 s = s / 12 * ((19 : ℕ) + 1 : ℂ) ^ (-s - 1)
      - s * (s + 1) * (s + 2) / 720 * ((19 : ℕ) + 1 : ℂ) ^ (-s - 3)
      + ∑' n : ℕ, emTerm₄ (n + 19 + 1) s := by
    rw [hz]; unfold F20 npow; rw [h20]; push_cast; ring
  rw [hdiff]
  have e20 : ((19 : ℕ) + 1 : ℂ) = ((20 : ℕ) : ℂ) := by push_cast; ring
  rw [e20]
  refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [norm_mul, norm_div, norm_natCast_cpow_of_pos (by norm_num)]
    have : ‖(12 : ℂ)‖ = 12 := by simp
    rw [this]
    have hp := twenty_rpow_le hσ1 1
    simp only [sub_re, neg_re, one_re, Nat.cast_one] at hp ⊢
    push_cast at hp ⊢
    calc ‖s‖ / 12 * (20 : ℝ) ^ (-s.re - 1) ≤ (1 + thi) / 12 * (2237 / 10000 * (1 / 20)) :=
          mul_le_mul (div_le_div_of_nonneg_right nA (by norm_num)) (by simpa using hp)
            (by positivity) (by positivity)
      _ = (1 + thi) * (2237 / 10000) / 240 := by ring
  · rw [norm_mul, norm_div, norm_mul, norm_mul, norm_natCast_cpow_of_pos (by norm_num)]
    have : ‖(720 : ℂ)‖ = 720 := by simp
    rw [this]
    have hp := twenty_rpow_le hσ1 3
    have hre3 : (-s - 3).re = -s.re - ((3 : ℕ) : ℝ) := by simp
    rw [hre3]
    have hABC : ‖s‖ * ‖s + 1‖ * ‖s + 2‖ ≤ (1 + thi) * (2 + thi) * (3 + thi) :=
      mul_le_mul (mul_le_mul nA nB (norm_nonneg _) (by positivity)) nC (norm_nonneg _)
        (by positivity)
    calc ‖s‖ * ‖s + 1‖ * ‖s + 2‖ / 720 * (20 : ℝ) ^ (-s.re - ((3 : ℕ) : ℝ))
        ≤ (1 + thi) * (2 + thi) * (3 + thi) / 720 * (2237 / 10000 * (1 / 20) ^ 3) :=
          mul_le_mul (div_le_div_of_nonneg_right hABC (by norm_num)) hp (by positivity)
            (by positivity)
      _ = (1 + thi) * (2 + thi) * (3 + thi) * (2237 / 10000) / (720 * 8000) := by ring
  · set P : ℝ := ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ / 720 with hP
    have hP0 : 0 ≤ P := by positivity
    have hPle : P ≤ (1 + thi) * (2 + thi) * (3 + thi) * (4 + thi) / 720 := by
      have := mul_le_mul (mul_le_mul (mul_le_mul nA nB (norm_nonneg _) (by positivity)) nC
        (norm_nonneg _) (by positivity)) nD (norm_nonneg _) (by positivity)
      exact div_le_div_of_nonneg_right this (by norm_num)
    have hterm : ∀ n : ℕ, ‖emTerm₄ (n + 19 + 1) s‖ ≤
        P * (1 / 8000) * ((n : ℝ) + (19 : ℕ) + 1) ^ (-(3 / 2 : ℝ)) := by
      intro n
      refine (norm_emTerm₄_le (by linarith) hs1 (by omega)).trans ?_
      rw [← hP, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hP0
      push_cast
      have hpos : (0 : ℝ) < (n : ℝ) + 19 + 1 := by positivity
      have hsplit : ((n : ℝ) + 19 + 1) ^ (-s.re - 4) =
          ((n : ℝ) + 19 + 1) ^ (-(3 / 2 : ℝ)) * ((n : ℝ) + 19 + 1) ^ (-s.re - 5 / 2) := by
        rw [← Real.rpow_add hpos]; congr 1; ring
      rw [hsplit, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have h20le : (20 : ℝ) ≤ (n : ℝ) + 19 + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      calc ((n : ℝ) + 19 + 1) ^ (-s.re - 5 / 2) ≤ (20 : ℝ) ^ (-s.re - 5 / 2) :=
            Real.rpow_le_rpow_of_nonpos (by norm_num) h20le (by linarith)
        _ ≤ (20 : ℝ) ^ (-(3 : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 1 / 8000 := by rw [Real.rpow_neg (by norm_num)]; norm_num
    have hsum := (summable_add_rpow 19 (a := -(3 / 2 : ℝ)) (by norm_num)).mul_left (P * (1 / 8000))
    have htail := tsum_of_norm_bounded hsum.hasSum hterm
    refine htail.trans ?_
    rw [tsum_mul_left]
    have hT := tsum_tail_rpow_le (N := 19) (by norm_num)
    have h3 : ((19 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 2295 / 10000 :=
      rpow_neg_le_const 19 (by norm_num) le_rfl (by norm_num) (by norm_num)
    have hT' : ∑' m : ℕ, ((m : ℝ) + (19 : ℕ) + 1) ^ (-(3 / 2 : ℝ)) ≤ 2 * (2295 / 10000) := by
      linarith
    calc P * (1 / 8000) * ∑' m : ℕ, ((m : ℝ) + (19 : ℕ) + 1) ^ (-(3 / 2 : ℝ))
        ≤ ((1 + thi) * (2 + thi) * (3 + thi) * (4 + thi) / 720) * (1 / 8000) * (2 * (2295 / 10000)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hPle (by norm_num)) hT'
            (tsum_nonneg fun _ => by positivity) (by positivity)
      _ = _ := by ring

/-- First-order expansion of one term. -/
lemma npow_lin_le {i : ℕ} {s s0 : ℂ} {ρ ℓ : ℝ} (hlog : Real.log ((i + 1 : ℕ) : ℝ) ≤ ℓ)
    (hd : ‖s - s0‖ ≤ ρ) (h1 : ρ * ℓ ≤ 1) :
    ‖npow i s - npow i s0 + (s - s0) * (((Real.log ((i + 1 : ℕ) : ℝ) : ℝ) : ℂ) * npow i s0)‖ ≤
      ‖npow i s0‖ * (ρ * ℓ) ^ 2 := by
  have hb0 : (((i + 1 : ℕ) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero i)
  rw [npow_eq, npow_eq]
  set b : ℂ := (((i + 1 : ℕ) : ℕ) : ℂ) with hbdef
  have hlog0 : 0 ≤ Real.log ((i + 1 : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast Nat.succ_pos i)
  set u : ℂ := Complex.log b * (-(s - s0)) with hu
  have hsplit : b ^ (-s) = b ^ (-s0) * exp u := by
    rw [hu, ← cpow_def_of_ne_zero hb0, ← cpow_add _ _ hb0]; congr 1; ring
  have hlogb : Complex.log b = ((Real.log ((i + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
    rw [hbdef, natCast_log]
  have hexpr : b ^ (-s) - b ^ (-s0) + (s - s0) * (((Real.log ((i + 1 : ℕ) : ℝ) : ℝ) : ℂ) * b ^ (-s0))
      = b ^ (-s0) * (exp u - 1 - u) := by
    rw [hsplit, hu, hlogb]; ring
  rw [hexpr, norm_mul]
  have hun : ‖u‖ ≤ ρ * ℓ := by
    rw [hu, norm_mul, norm_neg, hlogb, Complex.norm_real, Real.norm_eq_abs,
      _root_.abs_of_nonneg hlog0, mul_comm]
    exact mul_le_mul hd hlog hlog0 ((norm_nonneg _).trans hd)
  have hb2 := Complex.norm_exp_sub_one_sub_id_le (x := u) (by linarith)
  refine mul_le_mul_of_nonneg_left (hb2.trans ?_) (norm_nonneg _)
  exact pow_le_pow_left₀ (norm_nonneg _) hun 2

/-- First-order expansion of `F₂₀` on a cell. -/
theorem F20_lin_le {s s0 : ℂ} {ρ tlo : ℝ} (ℓ : ℕ → ℝ)
    (hlog : ∀ i < 20, Real.log ((i + 1 : ℕ) : ℝ) ≤ ℓ i) (hd : ‖s - s0‖ ≤ ρ)
    (h1 : ∀ i < 20, ρ * ℓ i ≤ 1) (htlo : 0 < tlo) (hts : tlo ≤ |s.im|) (hts0 : tlo ≤ |s0.im|) :
    ‖F20 s - F20 s0 + (s - s0) * G20 s0‖ ≤
      ∑ i ∈ Finset.range 19, ‖npow i s0‖ * (ρ * ℓ i) ^ 2 +
        (20 * (‖npow 19 s0‖ * (ρ * ℓ 19 * (1 + ρ * ℓ 19)) / tlo +
          ‖npow 19 s0‖ * ρ / (tlo * tlo)) +
        ‖npow 19 s0‖ * (ρ * ℓ 19 * (1 + ρ * ℓ 19)) / 2) := by
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans hd
  -- main sum
  have hmain : ‖∑ i ∈ Finset.range 19, (npow i s - npow i s0 +
      (s - s0) * (((Real.log ((i + 1 : ℕ) : ℝ) : ℝ) : ℂ) * npow i s0))‖ ≤
      ∑ i ∈ Finset.range 19, ‖npow i s0‖ * (ρ * ℓ i) ^ 2 :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi =>
      npow_lin_le (hlog i (by simp at hi; omega)) hd (h1 i (by simp at hi; omega)))
  -- boundary
  have h20 := cpow_sub_le (b := 20) (by norm_num) (s := s) (s0 := s0) (cb := ‖npow 19 s0‖)
    (by rw [npow_eq]) (by simpa using hlog 19 (by norm_num)) hd (h1 19 (by norm_num))
  rw [← npow_eq, ← npow_eq] at h20
  have hn1 : tlo ≤ ‖s - 1‖ := by
    refine hts.trans ?_
    have := Complex.abs_im_le_norm (s - 1)
    simpa using this
  have hn10 : tlo ≤ ‖s0 - 1‖ := by
    refine hts0.trans ?_
    have := Complex.abs_im_le_norm (s0 - 1)
    simpa using this
  have hne : s - 1 ≠ 0 := fun h => by rw [h, norm_zero] at hn1; linarith
  have hne0 : s0 - 1 ≠ 0 := fun h => by rw [h, norm_zero] at hn10; linarith
  have hinv : ‖(s - 1)⁻¹‖ ≤ 1 / tlo := by
    rw [norm_inv]; exact inv_anti₀ htlo hn1 |>.trans (le_of_eq (one_div tlo).symm)
  have hinvdiff : ‖(s - 1)⁻¹ - (s0 - 1)⁻¹‖ ≤ ρ / (tlo * tlo) := by
    rw [inv_sub_inv hne hne0, norm_div, norm_mul]
    rw [show s0 - 1 - (s - 1) = -(s - s0) by ring, norm_neg]
    apply div_le_div₀ hρ hd (by positivity) (mul_le_mul hn1 hn10 htlo.le (norm_nonneg _))
  set g : ℝ := ρ * ℓ 19 * (1 + ρ * ℓ 19)
  set a : ℝ := ‖npow 19 s0‖
  have hT1 : ‖npow 19 s * (s - 1)⁻¹ - npow 19 s0 * (s0 - 1)⁻¹‖ ≤
      a * g / tlo + a * ρ / (tlo * tlo) := by
    rw [show npow 19 s * (s - 1)⁻¹ - npow 19 s0 * (s0 - 1)⁻¹ =
      (npow 19 s - npow 19 s0) * (s - 1)⁻¹ + npow 19 s0 * ((s - 1)⁻¹ - (s0 - 1)⁻¹) by ring]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul]
    · calc ‖npow 19 s - npow 19 s0‖ * ‖(s - 1)⁻¹‖ ≤ (a * g) * (1 / tlo) :=
            mul_le_mul h20 hinv (norm_nonneg _) ((norm_nonneg _).trans h20)
        _ = a * g / tlo := by ring
    · calc ‖npow 19 s0‖ * ‖(s - 1)⁻¹ - (s0 - 1)⁻¹‖ ≤ a * (ρ / (tlo * tlo)) :=
            mul_le_mul_of_nonneg_left hinvdiff (norm_nonneg _)
        _ = a * ρ / (tlo * tlo) := by ring
  have hsplit : F20 s - F20 s0 + (s - s0) * G20 s0 =
      ∑ i ∈ Finset.range 19, (npow i s - npow i s0 +
        (s - s0) * (((Real.log ((i + 1 : ℕ) : ℝ) : ℝ) : ℂ) * npow i s0)) +
      ((20 : ℚ) : ℂ) * (npow 19 s * (s - 1)⁻¹ - npow 19 s0 * (s0 - 1)⁻¹) +
      ((1 / 2 : ℚ) : ℂ) * (npow 19 s - npow 19 s0) := by
    unfold F20 G20
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add_left (norm_add_le _ _) _).trans ?_
  rw [norm_mul, norm_mul]
  have e20 : ‖((20 : ℚ) : ℂ)‖ = 20 := by simp
  have e2 : ‖((1 / 2 : ℚ) : ℂ)‖ = 1 / 2 := by simp
  rw [e20, e2]
  have h3 : 1 / 2 * ‖npow 19 s - npow 19 s0‖ ≤ a * g / 2 := by
    have := h20; linarith
  nlinarith [mul_le_mul_of_nonneg_left hT1 (by norm_num : (0 : ℝ) ≤ 20)]


end

section
open Kerr.File14RH Disc
open ZetaGrowth ZetaGrowthNeg ZetaGrowthEM3

/-! ### Discs for `F₂₀` and `G₂₀` -/

lemma cinv_contains (σ0 t0 : ℚ) (ht : 0 < t0) :
    (exact ((σ0 - 1) / ((σ0 - 1) ^ 2 + t0 ^ 2)) (-t0 / ((σ0 - 1) ^ 2 + t0 ^ 2))).Contains
      ((((σ0 : ℂ) + (t0 : ℂ) * I) - 1)⁻¹) := by
  set s0 : ℂ := (σ0 : ℂ) + (t0 : ℂ) * I with hs0
  have hq : (0 : ℚ) < (σ0 - 1) ^ 2 + t0 ^ 2 := by positivity
  have he := exact_contains ((σ0 - 1) / ((σ0 - 1) ^ 2 + t0 ^ 2)) (-t0 / ((σ0 - 1) ^ 2 + t0 ^ 2))
  convert he using 1
  have hqR : ((σ0 : ℝ) - 1) ^ 2 + (t0 : ℝ) ^ 2 ≠ 0 := by
    have : (0 : ℝ) < ((σ0 : ℝ) - 1) ^ 2 + (t0 : ℝ) ^ 2 := by exact_mod_cast hq
    exact this.ne'
  apply inv_eq_of_mul_eq_one_right
  apply Complex.ext_iff.mpr
  simp only [hs0, Disc.exact, mul_re, mul_im, sub_re, sub_im, add_re, add_im,
    ofReal_re, ofReal_im, I_re, I_im, one_re, one_im, Complex.ratCast_re, Complex.ratCast_im]
  push_cast
  constructor
  · field_simp; ring
  · field_simp; ring

/-- Disc for `(i+1)^{-s₀}`. -/
def pwD (σ t : ℚ) (i : ℕ) : Disc := powDisc7 (lc i) σ t

/-- Upper bound for the norm of the points of a disc. -/
def nbr (D : Disc) : ℚ := D.nb + D.r

def F20disc (σ t : ℚ) : Disc :=
  add (add (sumD (pwD σ t) 19)
    (smul 20 (round (mul (pwD σ t 19)
      (exact ((σ - 1) / ((σ - 1) ^ 2 + t ^ 2)) (-t / ((σ - 1) ^ 2 + t ^ 2)))))))
    (smul (1 / 2) (pwD σ t 19))

def G20disc (σ t : ℚ) : Disc :=
  sumD (fun i => round (mul ⟨lc i, 0, etaL⟩ (pwD σ t i))) 19

lemma pwD_contains {σ t : ℚ} {i : ℕ} (hi : i < 20) (h64 : |-σ * lc i| + |-t * lc i| ≤ 64)
    (hη : (|σ| + |t|) * etaL ≤ 1 / 2) :
    (pwD σ t i).Contains (npow i ((σ : ℂ) + (t : ℂ) * I)) := by
  rw [npow_eq]
  exact powDisc7_contains (Nat.succ_pos i) (lc_near hi) σ t h64 hη

lemma logDisc_contains {i : ℕ} (hi : i < 20) :
    (⟨lc i, 0, etaL⟩ : Disc).Contains (((Real.log ((i + 1 : ℕ) : ℝ) : ℝ) : ℂ)) := by
  unfold Contains c
  simp only [Rat.cast_zero, zero_mul, add_zero]
  rw [← Complex.ofReal_ratCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact lc_near hi

/-! ### The cell certificate (rectangular cells) -/

def E20q (thi : ℚ) : ℚ :=
  (1 + thi) * (2237 / 10000) / 240 +
    (1 + thi) * (2 + thi) * (3 + thi) * (2237 / 10000) / (720 * 8000) +
    (1 + thi) * (2 + thi) * (3 + thi) * (4 + thi) * (2 * (2295 / 10000)) / (720 * 8000)

/-- Total allowance of a cell. -/
def margin14 (σ0 t0 hs ht : ℚ) : ℚ :=
  let ρ := 142 / 100 * max hs ht
  let a := nbr (pwD σ0 t0 19)
  let g := ρ * (lc 19 + etaL) * (1 + ρ * (lc 19 + etaL))
  (F20disc σ0 t0).r + ρ * nbr (G20disc σ0 t0) +
    sumQ (fun i => nbr (pwD σ0 t0 i) * (ρ * (lc i + etaL)) ^ 2) 19 +
    (20 * (a * g / (t0 - ht) + a * ρ / ((t0 - ht) * (t0 - ht))) + a * g / 2) + E20q (t0 + ht)

def cell14OK (σ0 t0 hs ht : ℚ) : Bool :=
  decide (0 < hs) && decide (0 < ht) && decide (0 < t0 - ht) &&
    decide (hs ^ 2 + ht ^ 2 ≤ (142 / 100 * max hs ht) ^ 2) &&
    ((List.range 20).all fun i => decide (|-σ0 * lc i| + |-t0 * lc i| ≤ 64) &&
      decide (142 / 100 * max hs ht * (lc i + etaL) ≤ 1)) &&
    decide ((|σ0| + |t0|) * etaL ≤ 1 / 2) &&
    decide (0 ≤ margin14 σ0 t0 hs ht) &&
    decide (margin14 σ0 t0 hs ht ^ 2 < (F20disc σ0 t0).re ^ 2 + (F20disc σ0 t0).im ^ 2)

theorem cell14OK_sound {σ0 t0 hs ht : ℚ} (hc : cell14OK σ0 t0 hs ht = true) {s : ℂ}
    (h1 : |s.re - σ0| ≤ hs) (h2 : |s.im - t0| ≤ ht) (hσ1 : 1 / 2 ≤ s.re) (hσ2 : s.re ≤ 1) :
    riemannZeta s ≠ 0 := by
  simp only [cell14OK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨hhs, hht⟩, htlo⟩, hρsq⟩, hall⟩, hη⟩, hm0⟩, hm⟩ := hc
  set ρq : ℚ := 142 / 100 * max hs ht with hρq
  set s0 : ℂ := (σ0 : ℂ) + (t0 : ℂ) * I with hs0
  have hs0re : s0.re = σ0 := by simp [hs0]
  have hs0im : s0.im = t0 := by simp [hs0]
  have h64 : ∀ i < 20, |-σ0 * lc i| + |-t0 * lc i| ≤ 64 := fun i hi => (hall i hi).1
  have hρℓ : ∀ i < 20, ρq * (lc i + etaL) ≤ 1 := fun i hi => (hall i hi).2
  -- distance
  have hd : ‖s - s0‖ ≤ (ρq : ℝ) := by
    have hρ0 : (0 : ℚ) ≤ ρq := by rw [hρq]; positivity
    apply norm_le_of_sq (by exact_mod_cast hρ0)
    simp only [sub_re, sub_im, hs0re, hs0im]
    have a1 : (s.re - σ0) ^ 2 ≤ (hs : ℝ) ^ 2 := sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
    have a2 : (s.im - t0) ^ 2 ≤ (ht : ℝ) ^ 2 := sq_le_sq' (abs_le.mp h2).1 (abs_le.mp h2).2
    have : ((hs ^ 2 + ht ^ 2 : ℚ) : ℝ) ≤ ((ρq ^ 2 : ℚ) : ℝ) := by exact_mod_cast hρsq
    push_cast at this
    linarith
  have htloR : (0 : ℝ) < ((t0 - ht : ℚ) : ℝ) := by exact_mod_cast htlo
  have hpos : (0 : ℝ) < (t0 : ℝ) - ht := by push_cast at htloR; linarith
  have hhtR : (0 : ℝ) < ht := by exact_mod_cast hht
  have hsim : ((t0 - ht : ℚ) : ℝ) ≤ |s.im| := by
    push_cast; have := (abs_le.mp h2).1; rw [abs_of_pos (by linarith)]; linarith
  have hs0im' : ((t0 - ht : ℚ) : ℝ) ≤ |s0.im| := by
    rw [hs0im]; push_cast; rw [abs_of_pos (by linarith)]; linarith
  have hsimhi : |s.im| ≤ ((t0 + ht : ℚ) : ℝ) := by
    push_cast; rw [abs_le]; constructor <;> linarith [(abs_le.mp h2).1, (abs_le.mp h2).2]
  have hs1 : s ≠ 1 := by
    intro e; rw [e] at hsim; simp at hsim; linarith
  -- the pieces
  have hpw : ∀ i < 20, (pwD σ0 t0 i).Contains (npow i s0) := fun i hi => pwD_contains hi (h64 i hi) hη
  have hF : (F20disc σ0 t0).Contains (F20 s0) := by
    unfold F20disc F20
    refine add_contains (add_contains (sumD_contains 19 fun i hi => hpw i (by omega)) ?_) ?_
    · exact smul_contains 20 (round_contains (mul_contains (hpw 19 (by norm_num))
        (cinv_contains σ0 t0 (by linarith [htlo, hht]))))
    · exact smul_contains (1 / 2) (hpw 19 (by norm_num))
  have hG : (G20disc σ0 t0).Contains (G20 s0) := by
    unfold G20disc G20
    exact sumD_contains 19 fun i hi =>
      round_contains (mul_contains (logDisc_contains (by omega)) (hpw i (by omega)))
  have hnpw : ∀ i < 20, ‖npow i s0‖ ≤ (nbr (pwD σ0 t0 i) : ℝ) := by
    intro i hi
    have := norm_le_of_contains (hpw i hi)
    unfold nbr; push_cast; exact this
  set ℓ : ℕ → ℝ := fun i => ((lc i + etaL : ℚ) : ℝ) with hℓ
  have hlog : ∀ i < 20, Real.log ((i + 1 : ℕ) : ℝ) ≤ ℓ i := by
    intro i hi
    have := (abs_le.mp (lc_near hi)).2
    simp only [hℓ]; push_cast at this ⊢; linarith
  have hρℓR : ∀ i < 20, (ρq : ℝ) * ℓ i ≤ 1 := by
    intro i hi
    have : ((ρq * (lc i + etaL) : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := by exact_mod_cast hρℓ i hi
    simp only [hℓ]; push_cast at this ⊢; exact this
  have hlin := F20_lin_le ℓ hlog hd hρℓR htloR hsim hs0im'
  have hE := zeta_sub_F20_le hσ1 hσ2 hsimhi hs1
  -- compare the allowances with `margin14`
  have hρ0 : (0 : ℝ) ≤ ρq := (norm_nonneg _).trans hd
  have hℓ0 : ∀ i < 20, 0 ≤ ℓ i := fun i hi =>
    (Real.log_nonneg (by exact_mod_cast Nat.succ_pos i)).trans (hlog i hi)
  have hR : ∑ i ∈ Finset.range 19, ‖npow i s0‖ * ((ρq : ℝ) * ℓ i) ^ 2 ≤
      ((sumQ (fun i => nbr (pwD σ0 t0 i) * (ρq * (lc i + etaL)) ^ 2) 19 : ℚ) : ℝ) := by
    rw [sumQ_cast]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i < 20 := by simp at hi; omega
    simp only [hℓ]; push_cast
    exact mul_le_mul_of_nonneg_right (by simpa using hnpw i hi') (sq_nonneg _)
  set a : ℝ := ‖npow 19 s0‖ with ha
  set A : ℝ := (nbr (pwD σ0 t0 19) : ℝ) with hA
  have haA : a ≤ A := hnpw 19 (by norm_num)
  set g : ℝ := (ρq : ℝ) * ℓ 19 * (1 + (ρq : ℝ) * ℓ 19) with hg
  have hg0 : 0 ≤ g := by have := hℓ0 19 (by norm_num); positivity
  have hT : 20 * (a * g / ((t0 - ht : ℚ) : ℝ) + a * (ρq : ℝ) / (((t0 - ht : ℚ) : ℝ) * ((t0 - ht : ℚ) : ℝ)))
      + a * g / 2 ≤
      20 * (A * g / ((t0 - ht : ℚ) : ℝ) + A * (ρq : ℝ) / (((t0 - ht : ℚ) : ℝ) * ((t0 - ht : ℚ) : ℝ)))
      + A * g / 2 := by
    gcongr
  have hmR : ((margin14 σ0 t0 hs ht : ℚ) : ℝ) = (F20disc σ0 t0).r + (ρq : ℝ) * nbr (G20disc σ0 t0) +
      ((sumQ (fun i => nbr (pwD σ0 t0 i) * (ρq * (lc i + etaL)) ^ 2) 19 : ℚ) : ℝ) +
      (20 * (A * g / ((t0 - ht : ℚ) : ℝ) + A * (ρq : ℝ) / (((t0 - ht : ℚ) : ℝ) * ((t0 - ht : ℚ) : ℝ)))
        + A * g / 2) +
      ((1 + ((t0 + ht : ℚ) : ℝ)) * (2237 / 10000) / 240 +
        (1 + ((t0 + ht : ℚ) : ℝ)) * (2 + ((t0 + ht : ℚ) : ℝ)) * (3 + ((t0 + ht : ℚ) : ℝ)) *
          (2237 / 10000) / (720 * 8000) +
        (1 + ((t0 + ht : ℚ) : ℝ)) * (2 + ((t0 + ht : ℚ) : ℝ)) * (3 + ((t0 + ht : ℚ) : ℝ)) *
          (4 + ((t0 + ht : ℚ) : ℝ)) * (2 * (2295 / 10000)) / (720 * 8000)) := by
    simp only [margin14, E20q, hA, hg, hℓ, hρq]; push_cast; ring
  have hGn : ‖(s - s0) * G20 s0‖ ≤ (ρq : ℝ) * nbr (G20disc σ0 t0) := by
    rw [norm_mul]
    have := norm_le_of_contains hG
    exact mul_le_mul hd (by unfold nbr; push_cast; exact this) (norm_nonneg _) hρ0
  -- `‖F.c‖ > m`
  set F := F20disc σ0 t0 with hFdef
  set m : ℚ := margin14 σ0 t0 hs ht with hmdef
  have hmR0 : (0 : ℝ) ≤ m := by exact_mod_cast hm0
  have hcm : (m : ℝ) < ‖F.c‖ := by
    by_contra hle
    push_neg at hle
    have hsq : ‖F.c‖ ^ 2 = (F.re : ℝ) ^ 2 + (F.im : ℝ) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, c_re, c_im]; ring
    have : ‖F.c‖ ^ 2 ≤ (m : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
    have hm' : ((m ^ 2 : ℚ) : ℝ) < ((F.re ^ 2 + F.im ^ 2 : ℚ) : ℝ) := by exact_mod_cast hm
    push_cast at hm'
    linarith
  unfold Contains at hF
  intro hz
  have k1 : ‖F20 s0‖ ≥ ‖F.c‖ - F.r := by
    have := norm_sub_norm_le F.c (F20 s0)
    rw [norm_sub_rev] at this; linarith
  have k2 : ‖F20 s‖ ≥ ‖F20 s0‖ - ‖(s - s0) * G20 s0‖ -
      ‖F20 s - F20 s0 + (s - s0) * G20 s0‖ := by
    have e : F20 s0 = F20 s - (F20 s - F20 s0 + (s - s0) * G20 s0) + (s - s0) * G20 s0 := by ring
    have := norm_add_le (F20 s - (F20 s - F20 s0 + (s - s0) * G20 s0)) ((s - s0) * G20 s0)
    have := norm_sub_le (F20 s) (F20 s - F20 s0 + (s - s0) * G20 s0)
    rw [← e] at *
    linarith
  have k3 := hE
  rw [hz, zero_sub, norm_neg] at k3
  linarith

/-! ### Rows of rectangular cells -/

/-- Columns `p = c₀ < c₁ < … ` across `1/2 ≤ Re s ≤ 1` in the row `a ≤ Im s ≤ b`. -/
def cols14OK (a b : ℚ) : ℚ → List ℚ → Bool
  | p, [] => decide (1 ≤ p)
  | p, q :: rest => decide (p < q) && cell14OK ((p + q) / 2) ((a + b) / 2) ((q - p) / 2) ((b - a) / 2)
      && cols14OK a b q rest

theorem cols14OK_sound {a b : ℚ} : ∀ (l : List ℚ) (p : ℚ), cols14OK a b p l = true →
    ∀ s : ℂ, (a : ℝ) ≤ s.im → s.im ≤ b → (p : ℝ) ≤ s.re → 1 / 2 ≤ s.re → s.re < 1 →
      riemannZeta s ≠ 0
  | [], p, h, s, _, _, hp, _, h1 => by
    simp only [cols14OK, decide_eq_true_eq] at h
    have : (1 : ℝ) ≤ p := by exact_mod_cast h
    linarith
  | q :: rest, p, h, s, ha, hb, hp, hσ1, hσ2 => by
    simp only [cols14OK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hpq, hcell⟩, hrest⟩ := h
    by_cases hq : s.re ≤ q
    · refine cell14OK_sound hcell ?_ ?_ hσ1 hσ2.le
      · rw [abs_le]; push_cast; constructor <;> linarith
      · rw [abs_le]; push_cast; constructor <;> linarith
    · exact cols14OK_sound rest q hrest s ha hb (le_of_lt (not_le.mp hq)) hσ1 hσ2

/-- Rows from `a` up to height `14`. -/
def rows14OK : ℚ → List (ℚ × List ℚ) → Bool
  | a, [] => decide (14 ≤ a)
  | a, (b, cs) :: rest => decide (a < b) && cols14OK a b (1 / 2) cs && rows14OK b rest

theorem rows14OK_sound : ∀ (l : List (ℚ × List ℚ)) (a : ℚ), rows14OK a l = true →
    ∀ s : ℂ, (a : ℝ) ≤ s.im → s.im < 14 → 1 / 2 ≤ s.re → s.re < 1 → riemannZeta s ≠ 0
  | [], a, h, s, ha, h14, _, _ => by
    simp only [rows14OK, decide_eq_true_eq] at h
    have : (14 : ℝ) ≤ a := by exact_mod_cast h
    linarith
  | (b, cs) :: rest, a, h, s, ha, h14, hσ1, hσ2 => by
    simp only [rows14OK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨_, hcols⟩, hrest⟩ := h
    by_cases hb : s.im ≤ b
    · exact cols14OK_sound cs (1 / 2) hcols s ha hb (by push_cast; linarith) hσ1 hσ2
    · exact rows14OK_sound rest b hrest s (le_of_lt (not_le.mp hb)) h14 hσ1 hσ2


end

section
open Kerr.File14RH Disc

/-- The rows for `10 ≤ Im s < 14` (134 cells; generated offline, checked by the kernel). -/
def zeroFreeRows14 : List (ℚ × List ℚ) :=
  [(((51 : ℚ) / 5), [((7 : ℚ) / 10), ((1 : ℚ) / 1)]),
    (((52 : ℚ) / 5), [((7 : ℚ) / 10), ((1 : ℚ) / 1)]),
    (((53 : ℚ) / 5), [((7 : ℚ) / 10), ((1 : ℚ) / 1)]),
    (((54 : ℚ) / 5), [((7 : ℚ) / 10), ((1 : ℚ) / 1)]),
    (((11 : ℚ) / 1), [((7 : ℚ) / 10), ((1 : ℚ) / 1)]),
    (((56 : ℚ) / 5), [((7 : ℚ) / 10), ((1 : ℚ) / 1)]),
    (((57 : ℚ) / 5), [((7 : ℚ) / 10), ((1 : ℚ) / 1)]),
    (((58 : ℚ) / 5), [((7 : ℚ) / 10), ((1 : ℚ) / 1)]),
    (((59 : ℚ) / 5), [((7 : ℚ) / 10), ((1 : ℚ) / 1)]),
    (((12 : ℚ) / 1), [((7 : ℚ) / 10), ((1 : ℚ) / 1)]),
    (((61 : ℚ) / 5), [((7 : ℚ) / 10), ((1 : ℚ) / 1)]),
    (((62 : ℚ) / 5), [((7 : ℚ) / 10), ((9 : ℚ) / 10), ((6 : ℚ) / 5)]),
    (((63 : ℚ) / 5), [((7 : ℚ) / 10), ((9 : ℚ) / 10), ((6 : ℚ) / 5)]),
    (((64 : ℚ) / 5), [((7 : ℚ) / 10), ((9 : ℚ) / 10), ((6 : ℚ) / 5)]),
    (((647 : ℚ) / 50), [((16 : ℚ) / 25), ((21 : ℚ) / 25), ((57 : ℚ) / 50)]),
    (((327 : ℚ) / 25), [((16 : ℚ) / 25), ((21 : ℚ) / 25), ((26 : ℚ) / 25)]),
    (((661 : ℚ) / 50), [((16 : ℚ) / 25), ((21 : ℚ) / 25), ((26 : ℚ) / 25)]),
    (((333 : ℚ) / 25), [((3 : ℚ) / 5), ((37 : ℚ) / 50), ((47 : ℚ) / 50), ((57 : ℚ) / 50)]),
    (((671 : ℚ) / 50), [((3 : ℚ) / 5), ((37 : ℚ) / 50), ((22 : ℚ) / 25), ((27 : ℚ) / 25)]),
    (((338 : ℚ) / 25), [((3 : ℚ) / 5), ((7 : ℚ) / 10), ((21 : ℚ) / 25), ((26 : ℚ) / 25)]),
    (((681 : ℚ) / 50), [((3 : ℚ) / 5), ((7 : ℚ) / 10), ((21 : ℚ) / 25), ((49 : ℚ) / 50), ((59 : ℚ) / 50)]),
    (((1369 : ℚ) / 100), [((57 : ℚ) / 100), ((67 : ℚ) / 100), ((77 : ℚ) / 100), ((91 : ℚ) / 100), ((111 : ℚ) / 100)]),
    (((344 : ℚ) / 25), [((57 : ℚ) / 100), ((16 : ℚ) / 25), ((37 : ℚ) / 50), ((21 : ℚ) / 25), ((49 : ℚ) / 50), ((59 : ℚ) / 50)]),
    (((1381 : ℚ) / 100), [((11 : ℚ) / 20), ((31 : ℚ) / 50), ((69 : ℚ) / 100), ((79 : ℚ) / 100), ((89 : ℚ) / 100), ((103 : ℚ) / 100)]),
    (((693 : ℚ) / 50), [((11 : ℚ) / 20), ((3 : ℚ) / 5), ((67 : ℚ) / 100), ((37 : ℚ) / 50), ((21 : ℚ) / 25), ((49 : ℚ) / 50), ((59 : ℚ) / 50)]),
    (((139 : ℚ) / 10), [((27 : ℚ) / 50), ((59 : ℚ) / 100), ((16 : ℚ) / 25), ((71 : ℚ) / 100), ((39 : ℚ) / 50), ((22 : ℚ) / 25), ((51 : ℚ) / 50)]),
    (((3481 : ℚ) / 250), [((27 : ℚ) / 50), ((29 : ℚ) / 50), ((63 : ℚ) / 100), ((17 : ℚ) / 25), ((3 : ℚ) / 4), ((41 : ℚ) / 50), ((23 : ℚ) / 25), ((53 : ℚ) / 50)]),
    (((3487 : ℚ) / 250), [((131 : ℚ) / 250), ((137 : ℚ) / 250), ((147 : ℚ) / 250), ((319 : ℚ) / 500), ((86 : ℚ) / 125), ((379 : ℚ) / 500), ((207 : ℚ) / 250), ((116 : ℚ) / 125), ((267 : ℚ) / 250)]),
    (((3493 : ℚ) / 250), [((131 : ℚ) / 250), ((137 : ℚ) / 250), ((143 : ℚ) / 250), ((153 : ℚ) / 250), ((331 : ℚ) / 500), ((89 : ℚ) / 125), ((391 : ℚ) / 500), ((441 : ℚ) / 500), ((511 : ℚ) / 500)]),
    (((3499 : ℚ) / 250), [((131 : ℚ) / 250), ((137 : ℚ) / 250), ((143 : ℚ) / 250), ((149 : ℚ) / 250), ((159 : ℚ) / 250), ((343 : ℚ) / 500), ((92 : ℚ) / 125), ((403 : ℚ) / 500), ((453 : ℚ) / 500), ((523 : ℚ) / 500)]),
    (((14 : ℚ) / 1), [((131 : ℚ) / 250), ((137 : ℚ) / 250), ((143 : ℚ) / 250), ((149 : ℚ) / 250), ((159 : ℚ) / 250), ((343 : ℚ) / 500), ((92 : ℚ) / 125), ((403 : ℚ) / 500), ((453 : ℚ) / 500), ((523 : ℚ) / 500)])]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row0 : cols14OK (10 : ℚ) ((51 : ℚ) / 5) (1 / 2) [((7 : ℚ) / 10), ((1 : ℚ) / 1)] = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row1 : cols14OK ((51 : ℚ) / 5) ((52 : ℚ) / 5) (1 / 2) [((7 : ℚ) / 10), ((1 : ℚ) / 1)] = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row2 : cols14OK ((52 : ℚ) / 5) ((53 : ℚ) / 5) (1 / 2) [((7 : ℚ) / 10), ((1 : ℚ) / 1)] = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row3 : cols14OK ((53 : ℚ) / 5) ((54 : ℚ) / 5) (1 / 2) [((7 : ℚ) / 10), ((1 : ℚ) / 1)] = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row4 : cols14OK ((54 : ℚ) / 5) ((11 : ℚ) / 1) (1 / 2) [((7 : ℚ) / 10), ((1 : ℚ) / 1)] = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row5 : cols14OK ((11 : ℚ) / 1) ((56 : ℚ) / 5) (1 / 2) [((7 : ℚ) / 10), ((1 : ℚ) / 1)] = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row6 : cols14OK ((56 : ℚ) / 5) ((57 : ℚ) / 5) (1 / 2) [((7 : ℚ) / 10), ((1 : ℚ) / 1)] = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row7 : cols14OK ((57 : ℚ) / 5) ((58 : ℚ) / 5) (1 / 2) [((7 : ℚ) / 10), ((1 : ℚ) / 1)] = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row8 : cols14OK ((58 : ℚ) / 5) ((59 : ℚ) / 5) (1 / 2) [((7 : ℚ) / 10), ((1 : ℚ) / 1)] = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row9 : cols14OK ((59 : ℚ) / 5) ((12 : ℚ) / 1) (1 / 2) [((7 : ℚ) / 10), ((1 : ℚ) / 1)] = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row10 : cols14OK ((12 : ℚ) / 1) ((61 : ℚ) / 5) (1 / 2) [((7 : ℚ) / 10), ((1 : ℚ) / 1)] = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row11 : cols14OK ((61 : ℚ) / 5) ((62 : ℚ) / 5) (1 / 2) [((7 : ℚ) / 10), ((9 : ℚ) / 10), ((6 : ℚ) / 5)] = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row12 : cols14OK ((62 : ℚ) / 5) ((63 : ℚ) / 5) (1 / 2) [((7 : ℚ) / 10), ((9 : ℚ) / 10), ((6 : ℚ) / 5)] = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row13 : cols14OK ((63 : ℚ) / 5) ((64 : ℚ) / 5) (1 / 2) [((7 : ℚ) / 10), ((9 : ℚ) / 10), ((6 : ℚ) / 5)] = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row14 : cols14OK ((64 : ℚ) / 5) ((647 : ℚ) / 50) (1 / 2) [((16 : ℚ) / 25), ((21 : ℚ) / 25), ((57 : ℚ) / 50)] = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row15 : cols14OK ((647 : ℚ) / 50) ((327 : ℚ) / 25) (1 / 2) [((16 : ℚ) / 25), ((21 : ℚ) / 25), ((26 : ℚ) / 25)] = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row16 : cols14OK ((327 : ℚ) / 25) ((661 : ℚ) / 50) (1 / 2) [((16 : ℚ) / 25), ((21 : ℚ) / 25), ((26 : ℚ) / 25)] = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row17 : cols14OK ((661 : ℚ) / 50) ((333 : ℚ) / 25) (1 / 2) [((3 : ℚ) / 5), ((37 : ℚ) / 50), ((47 : ℚ) / 50), ((57 : ℚ) / 50)] = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row18 : cols14OK ((333 : ℚ) / 25) ((671 : ℚ) / 50) (1 / 2) [((3 : ℚ) / 5), ((37 : ℚ) / 50), ((22 : ℚ) / 25), ((27 : ℚ) / 25)] = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row19 : cols14OK ((671 : ℚ) / 50) ((338 : ℚ) / 25) (1 / 2) [((3 : ℚ) / 5), ((7 : ℚ) / 10), ((21 : ℚ) / 25), ((26 : ℚ) / 25)] = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row20 : cols14OK ((338 : ℚ) / 25) ((681 : ℚ) / 50) (1 / 2) [((3 : ℚ) / 5), ((7 : ℚ) / 10), ((21 : ℚ) / 25), ((49 : ℚ) / 50), ((59 : ℚ) / 50)] = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row21 : cols14OK ((681 : ℚ) / 50) ((1369 : ℚ) / 100) (1 / 2) [((57 : ℚ) / 100), ((67 : ℚ) / 100), ((77 : ℚ) / 100), ((91 : ℚ) / 100), ((111 : ℚ) / 100)] = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row22 : cols14OK ((1369 : ℚ) / 100) ((344 : ℚ) / 25) (1 / 2) [((57 : ℚ) / 100), ((16 : ℚ) / 25), ((37 : ℚ) / 50), ((21 : ℚ) / 25), ((49 : ℚ) / 50), ((59 : ℚ) / 50)] = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row23 : cols14OK ((344 : ℚ) / 25) ((1381 : ℚ) / 100) (1 / 2) [((11 : ℚ) / 20), ((31 : ℚ) / 50), ((69 : ℚ) / 100), ((79 : ℚ) / 100), ((89 : ℚ) / 100), ((103 : ℚ) / 100)] = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row24 : cols14OK ((1381 : ℚ) / 100) ((693 : ℚ) / 50) (1 / 2) [((11 : ℚ) / 20), ((3 : ℚ) / 5), ((67 : ℚ) / 100), ((37 : ℚ) / 50), ((21 : ℚ) / 25), ((49 : ℚ) / 50), ((59 : ℚ) / 50)] = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row25 : cols14OK ((693 : ℚ) / 50) ((139 : ℚ) / 10) (1 / 2) [((27 : ℚ) / 50), ((59 : ℚ) / 100), ((16 : ℚ) / 25), ((71 : ℚ) / 100), ((39 : ℚ) / 50), ((22 : ℚ) / 25), ((51 : ℚ) / 50)] = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row26 : cols14OK ((139 : ℚ) / 10) ((3481 : ℚ) / 250) (1 / 2) [((27 : ℚ) / 50), ((29 : ℚ) / 50), ((63 : ℚ) / 100), ((17 : ℚ) / 25), ((3 : ℚ) / 4), ((41 : ℚ) / 50), ((23 : ℚ) / 25), ((53 : ℚ) / 50)] = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row27 : cols14OK ((3481 : ℚ) / 250) ((3487 : ℚ) / 250) (1 / 2) [((131 : ℚ) / 250), ((137 : ℚ) / 250), ((147 : ℚ) / 250), ((319 : ℚ) / 500), ((86 : ℚ) / 125), ((379 : ℚ) / 500), ((207 : ℚ) / 250), ((116 : ℚ) / 125), ((267 : ℚ) / 250)] = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row28 : cols14OK ((3487 : ℚ) / 250) ((3493 : ℚ) / 250) (1 / 2) [((131 : ℚ) / 250), ((137 : ℚ) / 250), ((143 : ℚ) / 250), ((153 : ℚ) / 250), ((331 : ℚ) / 500), ((89 : ℚ) / 125), ((391 : ℚ) / 500), ((441 : ℚ) / 500), ((511 : ℚ) / 500)] = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row29 : cols14OK ((3493 : ℚ) / 250) ((3499 : ℚ) / 250) (1 / 2) [((131 : ℚ) / 250), ((137 : ℚ) / 250), ((143 : ℚ) / 250), ((149 : ℚ) / 250), ((159 : ℚ) / 250), ((343 : ℚ) / 500), ((92 : ℚ) / 125), ((403 : ℚ) / 500), ((453 : ℚ) / 500), ((523 : ℚ) / 500)] = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem zfr14_row30 : cols14OK ((3499 : ℚ) / 250) ((14 : ℚ) / 1) (1 / 2) [((131 : ℚ) / 250), ((137 : ℚ) / 250), ((143 : ℚ) / 250), ((149 : ℚ) / 250), ((159 : ℚ) / 250), ((343 : ℚ) / 500), ((92 : ℚ) / 125), ((403 : ℚ) / 500), ((453 : ℚ) / 500), ((523 : ℚ) / 500)] = true := by decide +kernel


theorem zeroFreeRows14_ok : rows14OK 10 zeroFreeRows14 = true := by
  simp only [zeroFreeRows14, rows14OK, zfr14_row0, zfr14_row1, zfr14_row2, zfr14_row3, zfr14_row4, zfr14_row5, zfr14_row6, zfr14_row7, zfr14_row8, zfr14_row9, zfr14_row10, zfr14_row11, zfr14_row12, zfr14_row13, zfr14_row14, zfr14_row15, zfr14_row16, zfr14_row17, zfr14_row18, zfr14_row19, zfr14_row20, zfr14_row21, zfr14_row22, zfr14_row23, zfr14_row24, zfr14_row25, zfr14_row26, zfr14_row27, zfr14_row28, zfr14_row29, zfr14_row30, Bool.and_true, Bool.true_and]
  decide +kernel

/-- **`ζ(s) ≠ 0` for `0 < Re s < 1`, `|Im s| < 14`** (the first zero is at `1/2 + 14.1347… i`). -/
theorem zeta_ne_zero_strip_lt_fourteen {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (ht : |s.im| < 14) : riemannZeta s ≠ 0 := by
  intro hz
  have hs : IsNonTrivialZero s := ⟨hz, h0, h1⟩
  obtain ⟨w, hw, hwre, hwim⟩ : ∃ w : ℂ, IsNonTrivialZero w ∧ 1 / 2 ≤ w.re ∧ |w.im| = |s.im| := by
    by_cases hre : 1 / 2 ≤ s.re
    · exact ⟨s, hs, hre, rfl⟩
    · refine ⟨1 - conj s, zero_symmetry s hs, ?_, ?_⟩
      · simp only [sub_re, one_re, conj_re]; linarith
      · simp
  obtain ⟨v, hv, hvre, hvim0, hvim⟩ : ∃ v : ℂ, IsNonTrivialZero v ∧ 1 / 2 ≤ v.re ∧ 0 ≤ v.im ∧
      v.im = |w.im| := by
    by_cases him : 0 ≤ w.im
    · exact ⟨w, hw, hwre, him, (_root_.abs_of_nonneg him).symm⟩
    · push_neg at him
      refine ⟨conj w, ⟨?_, by simpa using hw.2.1, by simpa using hw.2.2⟩, by simpa using hwre,
        by simp; linarith, by simp [_root_.abs_of_neg him]⟩
      rw [Kerr.ZetaConj.riemannZeta_conj, hw.1, map_zero]
  have hv14 : v.im < 14 := by rw [hvim, hwim]; exact ht
  by_cases h10 : v.im < 10
  · exact zeta_ne_zero_quarter hvre hv.2.2 hvim0 h10 hv.1
  · push_neg at h10
    exact rows14OK_sound zeroFreeRows14 10 zeroFreeRows14_ok v (by push_cast; linarith) hv14
      hvre hv.2.2 hv.1

/-- `SmallRHVerified T` for every `T ≤ 14`. -/
theorem small_rh_verified_fourteen (T : ℝ) (hT : T ≤ 14) : SmallRHVerified T :=
  fun _ hs => zeta_ne_zero_strip_lt_fourteen hs.1 hs.2.1 (lt_of_lt_of_le hs.2.2 hT)


end

end Kerr.File14RHExtra
