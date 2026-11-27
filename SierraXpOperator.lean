import SierraXp
import Mathlib

/-!
# Self-adjoint realization with RVM smooth density

`SierraXp` produced the counting function for the energy-dependent cutoff.
This module supplies **self-adjoint operators** whose spectra realize that
count.

## Construction

    H_{Λ,M} = diag(λ_1, …, λ_M),   λ_n = 2π n / log Λ

Finite-dimensional Hermitian ⇒ self-adjoint. Energy-dependent family:
`H_E := H_{E, ⌊sierraCount E E⌋}`.

The diagonal entries *are* the Sierra model eigenvalues, so the spectrum of
`H_E` is exactly `{λ_1,…,λ_{M(E)}}` with `M(E) = ⌊sierraCount E E⌋`, hence
the spectral counting function tracks the RVM leading density within floor
error (see `modeBudget_le_sierra`).

A single continuum differential regularization of `xp` on `L²` (one operator,
not an `E`-family) remains `SingleContinuumXpRealization`.

No `sorry`, no custom axioms.
-/

noncomputable section
open Matrix SierraXp

namespace SierraXpOperator

/-- Model Sierra operator: diagonal of `eigenvalue Λ 1 .. eigenvalue Λ M`. -/
def modelMatrix (Λ : ℝ) (M : ℕ) : Matrix (Fin M) (Fin M) ℝ :=
  Matrix.diagonal fun i => SierraXp.eigenvalue Λ (i.val + 1)

theorem modelMatrix_hermitian (Λ : ℝ) (M : ℕ) :
    (modelMatrix Λ M).IsHermitian :=
  isHermitian_diagonal _

/-- Finite-dim Hermitian ⇒ self-adjoint. -/
theorem modelMatrix_selfAdjoint (Λ : ℝ) (M : ℕ) :
    IsSelfAdjoint (modelMatrix Λ M) :=
  (modelMatrix_hermitian Λ M).isSelfAdjoint

theorem modelMatrix_entry (Λ : ℝ) (M : ℕ) (i : Fin M) :
    modelMatrix Λ M i i = SierraXp.eigenvalue Λ (i.val + 1) := by
  simp [modelMatrix]

/-- Mode budget at energy `E` for `Λ(E) = E`. -/
def modeBudget (E : ℝ) : ℕ :=
  Nat.floor (SierraXp.sierraCount (SierraXp.cutoffLambda E) E)

/-- Energy-dependent model operator `H_E`. -/
def energyDependentMatrix (E : ℝ) :
    Matrix (Fin (modeBudget E)) (Fin (modeBudget E)) ℝ :=
  modelMatrix (SierraXp.cutoffLambda E) (modeBudget E)

theorem energyDependentMatrix_selfAdjoint (E : ℝ) :
    IsSelfAdjoint (energyDependentMatrix E) :=
  modelMatrix_selfAdjoint _ _

theorem energyDependent_entry (E : ℝ) (i : Fin (modeBudget E)) :
    energyDependentMatrix E i i =
      SierraXp.eigenvalue (SierraXp.cutoffLambda E) (i.val + 1) :=
  modelMatrix_entry _ _ _

/-- Package: self-adjoint matrix equal to the Sierra model. -/
structure DensityRealization (Λ : ℝ) (M : ℕ) where
  H : Matrix (Fin M) (Fin M) ℝ
  selfAdjoint : IsSelfAdjoint H
  spectrum_model : H = modelMatrix Λ M

/-- **Exists:** self-adjoint realization of the Sierra model spectrum. -/
theorem densityRealization_exists (Λ : ℝ) (M : ℕ) :
    Nonempty (DensityRealization Λ M) :=
  ⟨{ H := modelMatrix Λ M
     selfAdjoint := modelMatrix_selfAdjoint Λ M
     spectrum_model := rfl }⟩

structure EnergyDependentDensityRealization (E : ℝ) where
  realization : DensityRealization (SierraXp.cutoffLambda E) (modeBudget E)

/-- **Exists:** energy-dependent self-adjoint family with Sierra/RVM density. -/
theorem energyDependentDensityRealization_exists (E : ℝ) :
    Nonempty (EnergyDependentDensityRealization E) :=
  ⟨{ realization := (densityRealization_exists _ _).some }⟩

theorem sierraCount_nonneg (E : ℝ) (hE : 1 ≤ E) :
    0 ≤ SierraXp.sierraCount (SierraXp.cutoffLambda E) E := by
  rw [SierraXp.sierraCount_cutoff]
  have hlog : 0 ≤ Real.log E := Real.log_nonneg hE
  have hE0 : 0 ≤ E := le_trans zero_le_one hE
  positivity

/-- Mode budget tracks the smooth count from below. -/
theorem modeBudget_le_sierra (E : ℝ) (hE : 1 ≤ E) :
    (modeBudget E : ℝ) ≤
      SierraXp.sierraCount (SierraXp.cutoffLambda E) E := by
  unfold modeBudget
  exact Nat.floor_le (sierraCount_nonneg E hE)

/-- Floor error bound: `|M(E) - sierraCount E E| < 1`. -/
theorem modeBudget_abs_err_lt_one (E : ℝ) (hE : 1 ≤ E) :
    |(modeBudget E : ℝ) - SierraXp.sierraCount (SierraXp.cutoffLambda E) E| < 1 := by
  unfold modeBudget
  have hx := sierraCount_nonneg E hE
  have h1 := Nat.floor_le hx
  have h2 := Nat.lt_floor_add_one
    (SierraXp.sierraCount (SierraXp.cutoffLambda E) E)
  rw [abs_sub_lt_iff]
  constructor <;> linarith

/-- Open: one continuum `xp` operator on a Hilbert space with RVM density. -/
structure SingleContinuumXpRealization where
  confirmed : False  -- audit:allow-false-field (deliberately uninhabited: names the open problem)

def SingleContinuumXpRealizationProgress : Prop :=
  Nonempty SingleContinuumXpRealization

theorem single_continuum_still_open :
    SingleContinuumXpRealizationProgress ↔ False := by
  constructor
  · rintro ⟨⟨h⟩⟩; exact h
  · exact False.elim

end SierraXpOperator
