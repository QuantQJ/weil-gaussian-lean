import Mathlib

noncomputable section
open Filter
open scoped Topology BigOperators
namespace FleetFiniteTruncation

/-- The finite configurations are chosen once, independently of the test function.
They exhaust atom indices, retaining repeated ordinate values with multiplicity. -/
theorem exists_finite_truncations {ι : Type*} [Countable ι]
    (γ : ι → ℝ) (w : ℝ → ℝ) (hw : ∀ t, 0 ≤ w t)
    (hsum : Summable (fun i => w (γ i))) :
    ∃ c : ℕ → ℕ, ∃ x : ∀ n, Fin (c n) → ℝ,
      (∀ n, (∑ i, w (x n i)) ≤ ∑' i, w (γ i)) ∧
      (∀ f : ℝ → ℂ, ∀ L : ℂ, HasSum (fun i => f (γ i)) L →
        Tendsto (fun n => ∑ i, f (x n i)) atTop (𝓝 L)) := by
  classical
  obtain ⟨s, _, hs⟩ := exists_seq_monotone_tendsto_atTop_atTop (Finset ι)
  let c : ℕ → ℕ := fun n => Fintype.card (s n)
  let e : ∀ n, Fin (c n) ≃ (s n) := fun n => (Fintype.equivFin (s n)).symm
  let x : ∀ n, Fin (c n) → ℝ := fun n i => γ (e n i)
  have hsum_eq {A : Type} [AddCommMonoid A] (f : ι → A) (n : ℕ) :
      (∑ i : Fin (c n), f (e n i)) = ∑ i ∈ s n, f i := by
    exact ((e n).sum_comp (fun i : s n => f i)).trans (Finset.sum_coe_sort (s n) f)
  refine ⟨c, x, ?_, ?_⟩
  · intro n
    change (∑ i, (fun j => w (γ j)) (e n i)) ≤ _
    rw [hsum_eq (fun j => w (γ j)) n]
    exact Summable.sum_le_tsum (s n) (fun i _ => hw (γ i)) hsum
  · intro f L hf
    have ht := hf.comp hs
    convert ht using 1
    funext n
    exact hsum_eq (fun i => f (γ i)) n

/-- Inverse-quadratic specialization, with no assumption that the countable
spectrum is infinite. Empty and finite spectra are allowed. -/
theorem exists_inverse_quadratic_truncations {ι : Type*} [Countable ι]
    (γ : ι → ℝ) (hsum : Summable (fun i => (1 + (γ i)^2)⁻¹)) :
    ∃ c : ℕ → ℕ, ∃ x : ∀ n, Fin (c n) → ℝ,
      (∀ n, (∑ i, (1 + (x n i)^2)⁻¹) ≤ ∑' i, (1 + (γ i)^2)⁻¹) ∧
      (∀ f : ℝ → ℂ, ∀ L : ℂ, HasSum (fun i => f (γ i)) L →
        Tendsto (fun n => ∑ i, f (x n i)) atTop (𝓝 L)) := by
  exact exists_finite_truncations γ (fun t => (1+t^2)⁻¹) (fun t => by positivity) hsum

end FleetFiniteTruncation
