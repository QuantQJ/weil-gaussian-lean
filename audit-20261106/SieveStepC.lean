import SineBasis
import FiniteZeros
import Reduction
import ZetaStrip

set_option autoImplicit false
noncomputable section
open Complex Real Set
open scoped Real Interval

namespace SieveStepC

open Reduction DiscreteSpectrum ZetaStrip FiniteZeros

/-! ### The spectrum side: the sine eigenbasis is bounded -/

/-- Every discrete Dirichlet Laplacian eigenvalue is at most `4/h²`. -/
theorem laplEigenvalue_le (h θ : ℝ) (hh : h ≠ 0) :
    laplEigenvalue h θ ≤ 4 / (h * h) := by
  rw [eigenvalue_half_angle]
  have hhh : (0 : ℝ) < h * h := mul_self_pos.mpr hh
  have hc : (0 : ℝ) < 4 / (h * h) := div_pos (by norm_num) hhh
  have hs : Real.sin (θ / 2) ^ 2 ≤ 1 := Real.sin_sq_le_one _
  nlinarith

/-! ### The zero side: the ordinates are unbounded -/

/-- With infinitely many nontrivial zeros, no bound `T` contains all their ordinates. -/
theorem ordinates_unbounded
    (hinf : {ρ : ℂ | IsNontrivialZero ρ}.Infinite) (T : ℝ) :
    ∃ ρ : ℂ, IsNontrivialZero ρ ∧ T < |ρ.im| := by
  by_contra hc
  push_neg at hc
  set T' : ℝ := max T 1 with hT'
  have hT'pos : 0 < T' := lt_of_lt_of_le one_pos (le_max_right T 1)
  have hsub : {ρ : ℂ | IsNontrivialZero ρ} ⊆
      {ρ ∈ ([[1 - 2, (2:ℝ)]] ×ℂ [[-T', T']]) | IsNontrivialZero ρ} := by
    intro ρ hρ
    refine ⟨⟨?_, ?_⟩, hρ⟩
    · obtain ⟨h0, h1⟩ := mem_strip_of_isNontrivialZero hρ
      simp only [Set.mem_preimage, Set.mem_uIcc]
      left; constructor <;> linarith
    · have hb := le_trans (hc ρ hρ) (le_max_left T 1)
      obtain ⟨ha, hb2⟩ := abs_le.mp hb
      simp only [Set.mem_preimage, Set.mem_uIcc]
      left; exact ⟨ha, hb2⟩
  exact hinf (Set.Finite.subset
    (finite_nontrivialZeros_of_isCompact (isCompact_rect 2 T')) hsub)

/-! ### The collision -/

/-- **Step C fails, and this is why.** A bounded set of reals cannot contain the
ordinates of all nontrivial zeros. The sine eigenbasis of the discrete Dirichlet
Laplacian has spectrum inside `[0, 4/h²]`, so no finite-`N`, fixed-`h` instance of
it realizes the zeros. -/
theorem no_bounded_spectrum_realizes
    (hinf : {ρ : ℂ | IsNontrivialZero ρ}.Infinite)
    (S : Set ℂ) (B : ℝ) (hB : ∀ z ∈ S, |z.re| ≤ B)
    (hreal : SpectrumRealizesZeros S) : False := by
  obtain ⟨ρ, hρ, hgt⟩ := ordinates_unbounded hinf B
  have hmem := hreal ρ hρ
  have hre : (ordinate ρ).re = ρ.im := ordinate_re ρ
  have := hB _ hmem
  rw [hre] at this
  linarith

end SieveStepC

#print axioms SieveStepC.laplEigenvalue_le
#print axioms SieveStepC.ordinates_unbounded
#print axioms SieveStepC.no_bounded_spectrum_realizes
