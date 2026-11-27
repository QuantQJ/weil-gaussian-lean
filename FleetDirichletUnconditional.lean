import QuasiRHProved
import FleetDirichletZeroFree
import FleetLeastNonresidue

/-!
# Dirichlet results, unconditionally

`FleetDirichletZeroFree.DirichletQuasiRH` is word for word the statement of OpenAI's
`OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re` (vendored under `OAI/`, Apache-2.0),
so every theorem conditional on it holds outright. No new mathematics.
-/

namespace FleetDirichletUnconditional

/-- The Dirichlet `7/8` half-plane, proved (OpenAI's Lean proof). -/
theorem dirichletQuasiRH_holds : FleetDirichletZeroFree.DirichletQuasiRH :=
  fun χ _ hs hpole => OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re χ hs hpole

/-- Zero-free region `Re s > 1 − 1/((8/log q₀) log(q·max(1,|Im s|)))` for all `q ≥ q₀ ≥ 2`. -/
theorem LFunction_ne_zero_region_strict {q₀ q : ℕ} [NeZero q]
    (hq₀ : 2 ≤ q₀) (hq : q₀ ≤ q) (χ : DirichletCharacter ℂ q) {R : ℝ}
    (hR : 8 / Real.log q₀ ≤ R) {s : ℂ} (hs : 1 - 1 / (R * FleetDirichletZeroFree.logQT q s.im) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) : DirichletCharacter.LFunction χ s ≠ 0 :=
  FleetDirichletZeroFree.LFunction_ne_zero_region_strict dirichletQuasiRH_holds hq₀ hq χ hR hs hpole

/-- Kadiri's shape with constant `5.60`, every `q ≥ 5`, every character (no exceptional zero). -/
theorem LFunction_ne_zero_kadiri_shape {q : ℕ} [NeZero q] (hq : 5 ≤ q)
    (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 - 1 / (5.60 * FleetDirichletZeroFree.logQT q s.im) ≤ s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  FleetDirichletZeroFree.LFunction_ne_zero_kadiri_shape dirichletQuasiRH_holds hq χ hs hpole

/-- Least quadratic nonresidue: for every `A > 8`, `n(p) ≤ C (log p)^A` for all odd primes `p`. -/
theorem exists_nonresidue_le {A : ℝ} (hA : 8 < A) :
    ∃ C : ℝ, ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ C * Real.log p ^ A ∧ ¬ IsSquare (n : ZMod p) :=
  FleetLeastNonresidue.exists_nonresidue_le_of_dirichletQuasiRH dirichletQuasiRH_holds hA

end FleetDirichletUnconditional
