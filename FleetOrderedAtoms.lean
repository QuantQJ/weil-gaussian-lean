import FleetAtomicLimit
import Mathlib

noncomputable section
open scoped Classical
namespace FleetOrderedAtoms

/-- Sort original indices, using the original index to break absolute-value ties. -/
theorem exists_ordered_permutation {N : ℕ} (x : Fin N → ℝ) :
    ∃ e : Fin N ≃ Fin N, Monotone (fun i => |x (e i)|) := by
  let key : ULift.{0} (Fin N) → ℝ ×ₗ Fin N := fun i => toLex (|x i.down|, i.down)
  have hinj : Function.Injective key := by
    intro i j h
    have h' := congrArg (fun p : ℝ ×ₗ Fin N => (ofLex p).2) h
    exact ULift.ext h'
  letI : LinearOrder (ULift.{0} (Fin N)) := LinearOrder.lift' key hinj
  letI : LE (ULift.{0} (Fin N)) := (LinearOrder.lift' key hinj).toLE
  let o := monoEquivOfFin (ULift.{0} (Fin N)) (k := N) (by rw [Fintype.card_ulift, Fintype.card_fin])
  refine ⟨o.toEquiv.trans (Equiv.ulift : ULift.{0} (Fin N) ≃ Fin N), ?_⟩
  intro i j hij
  have h : key (o i) ≤ key (o j) := o.le_iff_le.mpr hij
  exact (Prod.Lex.toLex_le_toLex'.mp h).1

/-- Every index up through rank k lies within the radius of the kth atom. -/
theorem rank_le_local_card {N : ℕ} (x : Fin N → ℝ) (e : Fin N ≃ Fin N)
    (he : Monotone (fun i => |x (e i)|)) (k : Fin N) {R : ℝ}
    (hk : |x (e k)| ≤ R) :
    k.val + 1 ≤ (Finset.univ.filter (fun i => |x i| ≤ R)).card := by
  have h := Finset.card_le_card_of_injOn (s := Finset.Iic k)
    (t := Finset.univ.filter (fun i => |x i| ≤ R)) e
    (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (he (Finset.mem_Iic.mp hi)).trans hk⟩)
    (fun i _ j _ h => e.injective h)
  simpa only [Fin.card_Iic] using h

/-- Permuting indices preserves arbitrary finite traces and all multiplicities. -/
theorem sum_ordered {N : ℕ} (x : Fin N → ℝ) (e : Fin N ≃ Fin N)
    {A : Type*} [AddCommMonoid A] (f : ℝ → A) :
    (∑ i, f (x (e i))) = ∑ i, f (x i) :=
  Equiv.sum_comp e (fun i => f (x i))

/-- A uniform weighted bound forces every atom in radius R into a bounded prefix. -/
theorem rank_lt_weighted_bound {N : ℕ} (x : Fin N → ℝ) (e : Fin N ≃ Fin N)
    (he : Monotone (fun i => |x (e i)|)) (k : Fin N) {R M : ℝ}
    (hR : 0 ≤ R) (hm : (∑ i, (1+(x i)^2)⁻¹) ≤ M)
    (hk : |x (e k)| ≤ R) : k.val < ⌈M * (1+R^2)⌉₊ := by
  have hrank := rank_le_local_card x e he k hk
  have hcard := FleetAtomicLimit.local_card_bound Finset.univ x hR hm
  have hceil : ((Finset.univ.filter (fun i => |x i| ≤ R)).card : ℝ) ≤
      (⌈M * (1+R^2)⌉₊ : ℝ) := hcard.trans (Nat.le_ceil _)
  have hn : (Finset.univ.filter (fun i => |x i| ≤ R)).card ≤
      ⌈M * (1+R^2)⌉₊ := by exact_mod_cast hceil
  omega

/-- Outside the bounded prefix, the ordered source ordinates exceed radius R. -/
theorem radius_lt_of_rank_ge {N : ℕ} (x : Fin N → ℝ) (e : Fin N ≃ Fin N)
    (he : Monotone (fun i => |x (e i)|)) (k : Fin N) {R M : ℝ}
    (hR : 0 ≤ R) (hm : (∑ i, (1+(x i)^2)⁻¹) ≤ M)
    (hk : ⌈M * (1+R^2)⌉₊ ≤ k.val) : R < |x (e k)| := by
  by_contra h
  have := rank_lt_weighted_bound x e he k hR hm (le_of_not_gt h)
  omega

end FleetOrderedAtoms
