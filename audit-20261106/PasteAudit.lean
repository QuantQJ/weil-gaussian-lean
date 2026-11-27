import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Finprod

/-! Testing the three proposed statements as written. -/

-- (A) `guth_maynard_density` as written. Its conclusion is `∃ C, ∀ t ≥ T, True`.
theorem guth_maynard_density_as_written (σ : ℝ) (T : ℝ) (hσ : 1/2 < σ ∧ σ ≤ 7/8) :
    ∃ C : ℝ, ∀ t ≥ T, True :=
  ⟨0, fun _ _ => trivial⟩

-- (B) `openai_quasi_bound` as written, quantified. Is it true?
def OpenAIQuasiBound : Prop :=
  ∀ ρ : ℂ, ρ.re ∈ Set.Icc (0:ℝ) 1 → (ρ.re < 1/8 ∨ ρ.re > 7/8 → False)

theorem openai_quasi_bound_is_false : ¬ OpenAIQuasiBound := by
  intro h
  have hre : ((9/10 : ℝ) : ℂ).re = 9/10 := Complex.ofReal_re _
  refine h ((9/10 : ℝ) : ℂ) ?_ (Or.inr ?_)
  · rw [Set.mem_Icc, hre]; norm_num
  · rw [hre]; norm_num

-- (C) `sieve_boundary_contradiction` as written, quantified. Is it true?
def SieveBoundaryContradiction : Prop :=
  ∀ ρ : ℂ, (1/8 ≤ ρ.re ∧ ρ.re ≤ 7/8) → ρ.re ≠ 1/2 → False

theorem sieve_boundary_contradiction_is_false : ¬ SieveBoundaryContradiction := by
  intro h
  have hre : ((6/10 : ℝ) : ℂ).re = 6/10 := Complex.ofReal_re _
  refine h ((6/10 : ℝ) : ℂ) ⟨?_, ?_⟩ ?_
  · rw [hre]; norm_num
  · rw [hre]; norm_num
  · rw [hre]; norm_num

-- (D) The `ZetaZero` structure as written. Does zeta appear anywhere in it?
structure ZetaZero where
  val : ℂ
  is_nontrivial : 0 ≤ val.re ∧ val.re ≤ 1
  is_zero : val.re = 1/2

-- If so, 1/2 is inhabited by a number that is not a zero of anything.
noncomputable def notAZero : ZetaZero :=
  ⟨(1/2 : ℝ), by norm_num, by norm_num⟩

-- And the structure cannot even express an off-line zero:
theorem ZetaZero_cannot_state_RH (z : ZetaZero) : z.val.re = 1/2 := z.is_zero

#print axioms guth_maynard_density_as_written
#print axioms openai_quasi_bound_is_false
#print axioms sieve_boundary_contradiction_is_false
#print axioms ZetaZero_cannot_state_RH
