import FleetLandauTransferZeta
import FleetLandauTransferPerron
import FleetHeadContourConverse

/-!
# Landau's transfer: a zero-free strip gives `Σ_{n≤N} μ(n) ≪ N^{1/2+δ+ε}`

Generalizes kerr-lean `Kerr/Zeta/Littlewood.lean`'s `RH_implies_Mertens_growth` (James C. Kerr, Apache-2.0)
from RH to the strip `|Re ρ − 1/2| ≤ δ`, and discharges the named hypothesis
`FleetHeadContour.LandauTransfer δ` of `FleetHeadContourConverse`.

* `zeta_ne_zero_of_stripBound`: under `StripBound δ`, `ζ s ≠ 0` for `Re s > 1/2 + δ`.
* `landauTransfer`: `LandauTransfer δ` for every `0 ≤ δ < 1/2`. Proof: `invZeta_bound`
  (`‖1/ζ(s)‖ ≪ (1+|Im s|)^{ε'/4}` on `Re s ≥ 1/2 + δ + ε'/2`) and `partial_sum_bound` with `a = μ`,
  `G = 1/ζ`, `σ₀ = 1/2 + δ + ε'/2`, `θ = ε'/2`, `ε' = min ε (1/2)`.
* Corollaries, with the transfer hypothesis removed: `windowRate_of_strip'` (strip `δ ≥ 0` ⇒ window rate
  `(11/5)δ + ε`), `RH_iff_windowSubexp'` (`RH ↔ WindowSubexpBound`), `windowRate_of_quasiRH'`
  (`QuasiRH` ⇒ window rate `33/40 + ε`).
-/

noncomputable section
open Complex
open scoped ArithmeticFunction.Moebius

namespace FleetHeadContour

open Reduction

/-- Under the strip of half-width `δ ≥ 0`, `ζ` has no zero with `Re s > 1/2 + δ`. -/
theorem zeta_ne_zero_of_stripBound {δ : ℝ} (hδ : 0 ≤ δ) (hs : StripBound δ) {s : ℂ}
    (hre : 1 / 2 + δ < s.re) : riemannZeta s ≠ 0 := by
  intro h
  by_cases h1 : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h1 h
  · push Not at h1
    have hnt : IsNontrivialZero s := by
      refine ⟨h, ?_, ?_⟩
      · rintro ⟨n, hn⟩
        have := congrArg Complex.re hn
        simp at this
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      · rintro rfl; simp at h1
    have := hs s hnt
    rw [abs_le] at this
    linarith [this.2]

/-- **Landau's transfer, proved.** For `0 ≤ δ < 1/2`: if every nontrivial zero has `|Re ρ − 1/2| ≤ δ`,
then `|Σ_{n≤N} μ(n)| ≤ C_ε N^{1/2+δ+ε}` for every `ε > 0`. -/
theorem landauTransfer (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ < 1 / 2) : LandauTransfer δ := by
  intro hs ε hε
  have hZ : ∀ s : ℂ, 1 / 2 + δ < s.re → riemannZeta s ≠ 0 :=
    fun s hre => zeta_ne_zero_of_stripBound hδ hs hre
  set ε' := min ε (1 / 2) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by norm_num)
  have hε'1 : ε' ≤ 1 / 2 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  obtain ⟨C, hC, hb⟩ := FleetLandauTransfer.invZeta_bound hδ hZ (σ₀ := 1 / 2 + δ + ε' / 2)
    (by linarith) (η := ε' / 2 / 2) (by positivity)
  set K := 64 * (16 * C * ∫ t : ℝ, (1 + ‖t‖) ^ (-(1 + ε' / 2 / 2))) + 2 with hK
  refine ⟨K, fun N hN => ?_⟩
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have key := FleetLandauTransfer.partial_sum_bound (a := fun n => (μ n : ℂ)) (by simp)
    (fun n => by rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one)
    (G := FleetLandauTransfer.invZeta) (fun s hs => FleetLandauTransfer.invZeta_eq_LSeries hs)
    (σ₀ := 1 / 2 + δ + ε' / 2) (θ := ε' / 2)
    (by linarith) (by linarith) (by positivity) (by linarith) hC.le
    (fun s hs => FleetLandauTransfer.invZeta_differentiableAt_of_zeroFree hZ (by linarith)) hb hx
  rw [← hK, Nat.floor_natCast] at key
  have hset : Finset.Iic N = Finset.range (N + 1) := by ext n; simp
  have hM : |∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.moebius n : ℝ)| =
      ‖∑ n ∈ Finset.Iic N, (μ n : ℂ)‖ := by
    have e : ((∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.moebius n : ℝ) : ℝ) : ℂ) =
        ∑ n ∈ Finset.range (N + 1), (μ n : ℂ) := by push_cast; rfl
    rw [hset, ← e, Complex.norm_real, Real.norm_eq_abs]
  rw [hM]
  refine key.trans ?_
  have : (N : ℝ) ^ (1 / 2 + δ + ε' / 2 + ε' / 2) ≤ (N : ℝ) ^ (1 / 2 + δ + ε) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hK0 : 0 ≤ K := by
    have : 0 ≤ ∫ t : ℝ, (1 + ‖t‖) ^ (-(1 + ε' / 2 / 2)) :=
      MeasureTheory.integral_nonneg fun t => Real.rpow_nonneg (by positivity) _
    positivity
  exact mul_le_mul_of_nonneg_left this hK0

/-- **Converse, strip form, unconditional transfer.** Strip of half-width `δ ≥ 0` ⇒ window rate
`(11/5)δ + ε` for every `ε > 0` (for `δ ≥ 1/2` this is `windowRate_eleven_tenths`). -/
theorem windowRate_of_strip' {δ : ℝ} (hδ : 0 ≤ δ) (hs : StripBound δ) {ε : ℝ} (hε : 0 < ε) :
    WindowRate ((11 / 5) * δ + ε) := by
  by_cases hδ' : δ < 1 / 2
  · exact windowRate_of_strip hδ (landauTransfer δ hδ hδ') hs hε
  · push Not at hδ'
    exact windowRate_mono (by linarith) windowRate_eleven_tenths

/-- **RH ⟺ the subexponential window bound**, with Littlewood's theorem (`LandauTransfer 0`) proved. -/
theorem RH_iff_windowSubexp' : RiemannHypothesis ↔ WindowSubexpBound :=
  RH_iff_windowSubexp (landauTransfer 0 le_rfl (by norm_num))

/-- **The `δ = 3/8` instance**: `QuasiRH` gives the window rate `33/40 + ε`. -/
theorem windowRate_of_quasiRH' (hQ : QuasiRHWiring.QuasiRH) {ε : ℝ} (hε : 0 < ε) :
    WindowRate (33 / 40 + ε) :=
  windowRate_of_quasiRH hQ (landauTransfer (3 / 8) (by norm_num) (by norm_num)) hε

end FleetHeadContour
