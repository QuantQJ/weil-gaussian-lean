import FluctuationCapable
import Mathlib

/-!
# Crossing the fluctuation barrier is cheap

`FluctuationCapable.CrossesFluctuationBarrier c lam` says: the fluctuation
of `lam` against the Riemann–von Mangoldt smooth term is unbounded. The
module that defines it calls this the "prize side".

This module shows the property is **trivially satisfiable**, and therefore
is not the prize-relevant property. The cascade `λ_n = eⁿ` — a stack of
exponentially spaced levels, each of which is the spectrum of a self-adjoint
(diagonal) operator — crosses the barrier: its counting function grows like
`log E` while the smooth term grows like `E log E`, so the fluctuation goes to
`−∞`. The direct sum of the layers is self-adjoint for free.

So an operator family that is self-adjoint **and** crosses the barrier exists
and says nothing about the zeros. What the zeros require is not *unbounded*
fluctuation but the **specific** fluctuation `S(T)` — the prime sum from the
explicit formula. "Wild" is not the criterion; "arithmetic" is.

No `sorry`, no custom axioms.
-/

noncomputable section
open Real SpectralFluctuation FluctuationCapable Matrix

namespace CascadeCounterexample

/-- The exponential cascade `λ_n = eⁿ`. -/
def cascade (n : ℕ) : ℝ := Real.exp n

lemma cascade_zero : cascade 0 = 1 := by simp [cascade]

lemma cascade_strictMono : StrictMono cascade := by
  intro a b hab
  simp only [cascade]
  exact Real.exp_lt_exp.mpr (by exact_mod_cast hab)

/-- Each finite layer of the cascade is the spectrum of a self-adjoint
(diagonal) operator. -/
def layer (M : ℕ) : Matrix (Fin M) (Fin M) ℝ :=
  Matrix.diagonal fun i => cascade i.val

theorem layer_selfAdjoint (M : ℕ) : IsSelfAdjoint (layer M) :=
  (Matrix.isHermitian_diagonal (fun i : Fin M => cascade i.val)).isSelfAdjoint

/-- Counting function of the cascade: at most `⌊log E⌋ + 1` levels below `E`. -/
theorem count_cascade_le {E : ℝ} (hE : 1 ≤ E) :
    count cascade E ≤ Nat.floor (Real.log E) + 1 := by
  have hEpos : 0 < E := lt_of_lt_of_le one_pos hE
  have hsub : {n : ℕ | cascade n ≤ E} ⊆ Set.Iic (Nat.floor (Real.log E)) := by
    intro n hn
    simp only [Set.mem_setOf_eq, cascade] at hn
    simp only [Set.mem_Iic]
    apply Nat.le_floor
    exact (Real.le_log_iff_exp_le hEpos).mpr hn
  unfold count
  calc Set.ncard {n : ℕ | cascade n ≤ E}
      ≤ Set.ncard (Set.Iic (Nat.floor (Real.log E))) :=
        Set.ncard_le_ncard hsub (Set.finite_Iic _)
    _ = Nat.floor (Real.log E) + 1 := by
        rw [← Finset.coe_Iic, Set.ncard_coe_finset, Nat.card_Iic]

/-- The fluctuation of the cascade against the RVM term is bounded above by
`log E + 1 + c − A(E)/(2π)`. -/
theorem rvmFluct_cascade_le (c : ℝ) {E : ℝ} (hE : 1 ≤ E) :
    rvmFluct c cascade E ≤ Real.log E + 1 + c - XpSpectrum.A E / (2 * π) := by
  unfold rvmFluct fluct smoothCount
  have h1 := count_cascade_le hE
  have h2 : (Nat.floor (Real.log E) : ℝ) ≤ Real.log E :=
    Nat.floor_le (Real.log_nonneg hE)
  have h3 : ((count cascade E : ℕ) : ℝ) ≤ (Nat.floor (Real.log E) : ℝ) + 1 := by
    exact_mod_cast h1
  linarith

/-- **The cascade crosses the barrier.** For every `K` there is `E` with
`|rvmFluct c cascade E| > K`. -/
theorem cascade_crosses (c : ℝ) : CrossesFluctuationBarrier c cascade := by
  intro K
  -- choose m large, E = e^m
  set m : ℕ := Nat.ceil (8 * (|c| + |K| + 3)) with hm
  have hm_ge : 8 * (|c| + |K| + 3) ≤ (m : ℝ) := Nat.le_ceil _
  have hm1 : (1 : ℝ) ≤ m := by
    have : (0:ℝ) ≤ |c| + |K| := by positivity
    linarith
  set E : ℝ := Real.exp m with hE
  have hE1 : 1 ≤ E := by
    rw [hE]; exact Real.one_le_exp (by positivity)
  refine ⟨E, ?_, ?_⟩
  · rw [cascade_zero]; exact hE1
  · have hlogE : Real.log E = m := by rw [hE, Real.log_exp]
    have hA : XpSpectrum.A E = E * m - E + 1 := by
      simp only [XpSpectrum.A, hlogE]
    -- e^m ≥ m + 1, so A(E) ≥ m²
    have hexp : (m : ℝ) + 1 ≤ E := by rw [hE]; exact Real.add_one_le_exp _
    have hAge : (m : ℝ) ^ 2 ≤ XpSpectrum.A E := by
      rw [hA]
      nlinarith [hexp, hm1]
    -- 2π ≤ 8
    have hpi : 2 * π ≤ 8 := by linarith [Real.pi_le_four]
    have hpipos : 0 < 2 * π := by positivity
    -- m² / (2π) ≥ m + 2 + c + K  (so the fluctuation is ≤ −K − 1)
    have hsq : (m : ℝ) + 2 + c + K ≤ (m : ℝ) ^ 2 / (2 * π) := by
      rw [le_div_iff₀ hpipos]
      have hcK : c ≤ |c| := le_abs_self c
      have hKK : K ≤ |K| := le_abs_self K
      have hnn : 0 ≤ (m : ℝ) + 2 + c + K := by
        linarith [neg_abs_le c, neg_abs_le K, abs_nonneg c, abs_nonneg K]
      calc ((m : ℝ) + 2 + c + K) * (2 * π)
          ≤ ((m : ℝ) + 2 + c + K) * 8 := mul_le_mul_of_nonneg_left hpi hnn
        _ ≤ (m : ℝ) ^ 2 := by nlinarith [abs_nonneg c, abs_nonneg K, hcK, hKK, hm_ge, hm1]
    have hfl := rvmFluct_cascade_le c hE1
    rw [hlogE] at hfl
    have hAdiv : (m : ℝ) ^ 2 / (2 * π) ≤ XpSpectrum.A E / (2 * π) :=
      div_le_div_of_nonneg_right hAge hpipos.le
    have hneg : rvmFluct c cascade E ≤ -(K + 1) := by linarith
    have : K + 1 ≤ |rvmFluct c cascade E| :=
      le_trans (by linarith) (neg_le_abs (rvmFluct c cascade E))
    linarith

/-- **The barrier-crossing property is not the prize property.** A self-adjoint
cascade crosses it. Whatever singles out the zeros is not "unbounded
fluctuation"; it is the specific arithmetic fluctuation `S(T)`. -/
theorem barrier_crossing_is_cheap (c : ℝ) :
    (∀ M, IsSelfAdjoint (layer M)) ∧ CrossesFluctuationBarrier c cascade :=
  ⟨layer_selfAdjoint, cascade_crosses c⟩

end CascadeCounterexample

end
