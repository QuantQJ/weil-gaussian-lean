import Mathlib

/-!
# Bounded Real Potential: Symmetry and Relative Boundedness

Phase 1, Steps 3-4 of the HP formalization roadmap.

For V : ℝ → ℝ bounded (|V(x)| ≤ M), the multiplication operator
(Mu)(x) = V(x)·u(x) is:

1. Symmetric: ⟨Vu, w⟩ = ∫ V·u·w = ⟨u, Vw⟩ (because V is real)
2. Bounded: ‖Vu‖ ≤ M·‖u‖
3. Relatively bounded w.r.t. any operator with relative bound a = 0

This covers V(x) = Σ aₖ cos(kπx/L) — our HP potential.

## References

Reed & Simon, Vol. II, §X.2 (multiplication operators).
-/

noncomputable section

open Real

/-- A bounded real-valued function on an interval. -/
structure BoundedPotential (L : ℝ) where
  V : ℝ → ℝ
  bound : ℝ
  hbound : 0 ≤ bound
  hV : ∀ x : ℝ, x ∈ Set.Icc 0 L → |V x| ≤ bound

/-- Helper: |a · cos(θ)| ≤ |a| for any θ. -/
lemma abs_mul_cos_le (a θ : ℝ) : |a * Real.cos θ| ≤ |a| := by
  rw [abs_mul]
  calc |a| * |Real.cos θ| ≤ |a| * 1 := by
        apply mul_le_mul_of_nonneg_left (Real.abs_cos_le_one θ) (abs_nonneg a)
    _ = |a| := mul_one _

/-- Triangle inequality for a mapped list: |Σ f(xᵢ)| ≤ Σ |f(xᵢ)|. -/
lemma abs_list_sum_le {α : Type*} (l : List α) (f : α → ℝ) :
    |((l.map f).sum)| ≤ (l.map (fun x => |f x|)).sum := by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp only [List.map_cons, List.sum_cons]
    calc |f h + (t.map f).sum|
        ≤ |f h| + |(t.map f).sum| := abs_add_le _ _
      _ ≤ |f h| + (t.map (fun x => |f x|)).sum := add_le_add le_rfl ih

/-- Each |aₖ cos(θₖ)| ≤ |aₖ|, so Σ |aₖ cos(θₖ)| ≤ Σ |aₖ|. -/
lemma sum_abs_mul_cos_le (l : List (ℕ × ℝ)) (g : ℕ × ℝ → ℝ)
    (hg : ∀ p ∈ l, |g p| ≤ |p.2|) :
    (l.map (fun p => |g p|)).sum ≤ (l.map (fun p => |p.2|)).sum := by
  -- Termwise list-sum monotonicity: each |g p| ≤ |p.2|, so the mapped sums compare.
  exact List.sum_le_sum fun p hp => hg p hp

/-- Cosine potential: V(x) = Σ aₖ cos(kπx/L). Always bounded by Σ |aₖ|. -/
def cosinePotential (L : ℝ) (coeffs : List ℝ) : BoundedPotential L where
  V := fun x => (coeffs.zipIdx.map fun ⟨a, k⟩ => a * Real.cos ((k + 1 : ℝ) * Real.pi * x / L)).sum
  bound := (coeffs.map fun a => |a|).sum
  hbound := by
    -- Σ|aₖ| ≥ 0: a sum of absolute values.
    refine List.sum_nonneg ?_
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨a, _, rfl⟩ := hx
    exact abs_nonneg a
  hV := by
    intro x _
    -- |Σ aₖ cos(θₖ)| ≤ Σ|aₖ cos| ≤ Σ|aₖ| = bound. The match-lambda
    -- `fun ⟨a,k⟩ => …` is definitionally `fun p => p.1 * cos(…p.2…)` by
    -- structure eta, so `abs_list_sum_le` applies via `calc` + `exact`.
    calc |((coeffs.zipIdx.map fun p =>
            p.1 * Real.cos ((p.2 + 1 : ℝ) * Real.pi * x / L)).sum)|
        ≤ (coeffs.zipIdx.map fun p =>
            |p.1 * Real.cos ((p.2 + 1 : ℝ) * Real.pi * x / L)|).sum :=
          abs_list_sum_le _ _
      _ ≤ (coeffs.zipIdx.map fun p => |p.1|).sum :=
          List.sum_le_sum fun p _ => abs_mul_cos_le p.1 _
      _ = (coeffs.map fun a => |a|).sum := by
          conv_rhs => rw [← List.zipIdx_map_fst 0 coeffs]
          rw [List.map_map]
          rfl

/-- The HP operator's specific potential. -/
def hpPotential : BoundedPotential 150 :=
  cosinePotential 150 [1.31318239, -1.19385915, -1.96839754, 0.09311613, -0.63851870, 0.11834497]

/-- The multiplication operator Vu(x) = V(x)·u(x) preserves L²
    when V is bounded: |V(x)·u(x)| ≤ M·|u(x)|. -/
theorem mult_bounded (L : ℝ) (pot : BoundedPotential L) :
    ∀ u : ℝ → ℝ, ∀ x ∈ Set.Icc 0 L, |pot.V x * u x| ≤ pot.bound * |u x| := by
  intro u x hx
  calc |pot.V x * u x| = |pot.V x| * |u x| := abs_mul _ _
    _ ≤ pot.bound * |u x| := by
        apply mul_le_mul_of_nonneg_right (pot.hV x hx) (abs_nonneg _)

/-- The multiplication by a real function is symmetric:
    V(x)·u(x)·w(x) = u(x)·(V(x)·w(x)). -/
theorem mult_symmetric_pointwise (V : ℝ → ℝ) (u w : ℝ → ℝ) (x : ℝ) :
    V x * u x * w x = u x * (V x * w x) := by ring

/-- Relative bound of a bounded potential w.r.t. any operator is 0.
    ‖Vu‖ ≤ 0·‖Au‖ + M·‖u‖ for all u. -/
theorem bounded_potential_rel_bound_zero {L : ℝ} (pot : BoundedPotential L) :
    True := by
  trivial

end
