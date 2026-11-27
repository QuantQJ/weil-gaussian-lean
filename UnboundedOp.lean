import Mathlib

/-!
# Unbounded Operators on Hilbert Spaces

Phase 1, Step 0 of the HP formalization roadmap.

Defines unbounded linear operators with explicit domains,
symmetric (Hermitian) unbounded operators, and self-adjoint
unbounded operators. These are the foundations needed for
Kato-Rellich and the continuum HP operator.

## Key Definitions

- `UnboundedOp H` — linear operator T : D(T) → H with domain D(T) ⊆ H
- `UnboundedOp.IsSymmetric` — ⟨Tu, v⟩ = ⟨u, Tv⟩ for all u, v ∈ D(T)
- `UnboundedOp.IsDenselyDefined` — D(T) is dense in H
- `UnboundedOp.sum` — T + S on D(T) ∩ D(S)
- `UnboundedOp.IsRelBounded` — S is T-bounded with relative bound a

## References

Reed & Simon, Methods of Modern Mathematical Physics, Vol. I, Ch. VIII.
-/

noncomputable section

open InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- An unbounded operator on a real Hilbert space with explicit domain.
    The domain is a subspace of H, and the operator maps D(T) → H. -/
structure UnboundedOp (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  /-- The domain D(T) as a submodule of H. -/
  domain : Submodule ℝ H
  /-- The operator T : D(T) → H. -/
  toFun : domain → H
  /-- Linearity: T(au + bv) = aT(u) + bT(v). -/
  map_add' : ∀ (u v : domain), toFun (u + v) = toFun u + toFun v
  map_smul' : ∀ (c : ℝ) (u : domain), toFun (c • u) = c • toFun u

namespace UnboundedOp

variable (T S : UnboundedOp H)

/-- T is symmetric if ⟨Tu, v⟩ = ⟨u, Tv⟩ for all u, v ∈ D(T). -/
def IsSymmetric : Prop :=
  ∀ (u v : T.domain), @inner ℝ H _ (T.toFun u) (v : H) = @inner ℝ H _ (u : H) (T.toFun v)

/-- T is densely defined if D(T) is dense in H. -/
def IsDenselyDefined : Prop :=
  ∀ (x : H) (ε : ℝ), 0 < ε → ∃ (u : T.domain), ‖x - (u : H)‖ < ε

/-- The sum T + S defined on D(T) ∩ D(S). -/
def sum (T S : UnboundedOp H) : UnboundedOp H where
  domain := T.domain ⊓ S.domain
  toFun := fun u =>
    T.toFun ⟨(u : H), (Submodule.mem_inf.mp u.2).1⟩ +
    S.toFun ⟨(u : H), (Submodule.mem_inf.mp u.2).2⟩
  map_add' := by
    -- (T+S)(u+v) = (T+S)u + (T+S)v from linearity of T and S. The subtype
    -- components of u+v in T.domain (resp. S.domain) coincide with the sums of
    -- the components (`Subtype.ext rfl`), then `map_add'` of T and S applies.
    intro u v
    have hT : (⟨((u + v : ↥(T.domain ⊓ S.domain)) : H),
        (Submodule.mem_inf.mp (u + v).2).1⟩ : T.domain)
        = ⟨(u : H), (Submodule.mem_inf.mp u.2).1⟩
          + ⟨(v : H), (Submodule.mem_inf.mp v.2).1⟩ := Subtype.ext rfl
    have hS : (⟨((u + v : ↥(T.domain ⊓ S.domain)) : H),
        (Submodule.mem_inf.mp (u + v).2).2⟩ : S.domain)
        = ⟨(u : H), (Submodule.mem_inf.mp u.2).2⟩
          + ⟨(v : H), (Submodule.mem_inf.mp v.2).2⟩ := Subtype.ext rfl
    show T.toFun _ + S.toFun _ = _
    rw [hT, hS, T.map_add', S.map_add']
    abel
  map_smul' := by
    intro c u
    have hT : (⟨((c • u : ↥(T.domain ⊓ S.domain)) : H),
        (Submodule.mem_inf.mp (c • u).2).1⟩ : T.domain)
        = c • ⟨(u : H), (Submodule.mem_inf.mp u.2).1⟩ := Subtype.ext rfl
    have hS : (⟨((c • u : ↥(T.domain ⊓ S.domain)) : H),
        (Submodule.mem_inf.mp (c • u).2).2⟩ : S.domain)
        = c • ⟨(u : H), (Submodule.mem_inf.mp u.2).2⟩ := Subtype.ext rfl
    show T.toFun _ + S.toFun _ = _
    rw [hT, hS, T.map_smul', S.map_smul', smul_add]

/-- S is T-bounded with constants (a, b) if
    ‖Su‖ ≤ a · ‖Tu‖ + b · ‖u‖ for all u ∈ D(T). -/
def IsRelBounded (S T : UnboundedOp H) (a b : ℝ) : Prop :=
  ∃ hsub : T.domain ≤ S.domain,
    ∀ (u : T.domain),
      ‖S.toFun ⟨(u : H), hsub u.2⟩‖ ≤
      a * ‖T.toFun u‖ + b * ‖(u : H)‖

/-- The infimum of all valid relative bounds. -/
def relBound (S T : UnboundedOp H) : ℝ :=
  sInf { a : ℝ | ∃ b : ℝ, IsRelBounded S T a b }

/-- Symmetric + symmetric = symmetric on the intersection domain. -/
theorem sum_symmetric (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (_hD : T.domain = S.domain) :
    (sum T S).IsSymmetric := by
  -- ⟨(T+S)u, v⟩ = ⟨Tu,v⟩+⟨Su,v⟩ = ⟨u,Tv⟩+⟨u,Sv⟩ = ⟨u,(T+S)v⟩ using hT, hS.
  -- The subtype components coerce back to ↑u, ↑v definitionally, so the
  -- symmetry hypotheses apply directly after splitting the inner products.
  intro u v
  show @inner ℝ H _
      (T.toFun ⟨(u : H), (Submodule.mem_inf.mp u.2).1⟩
        + S.toFun ⟨(u : H), (Submodule.mem_inf.mp u.2).2⟩) (v : H)
    = @inner ℝ H _ (u : H)
      (T.toFun ⟨(v : H), (Submodule.mem_inf.mp v.2).1⟩
        + S.toFun ⟨(v : H), (Submodule.mem_inf.mp v.2).2⟩)
  rw [inner_add_left, inner_add_right]
  exact congrArg₂ (· + ·)
    (hT ⟨(u : H), (Submodule.mem_inf.mp u.2).1⟩ ⟨(v : H), (Submodule.mem_inf.mp v.2).1⟩)
    (hS ⟨(u : H), (Submodule.mem_inf.mp u.2).2⟩ ⟨(v : H), (Submodule.mem_inf.mp v.2).2⟩)

end UnboundedOp

/-- A bounded multiplication operator: given M : H → H bounded,
    its domain is all of H. -/
def boundedAsUnbounded {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (M : H →L[ℝ] H) : UnboundedOp H where
  domain := ⊤
  toFun := fun u => M (u : H)
  map_add' := by intro u v; simp [map_add]
  map_smul' := by intro c u; simp [map_smul]

/-- A bounded operator viewed as unbounded is symmetric iff
    ⟨Mu, v⟩ = ⟨u, Mv⟩ for all u, v. -/
theorem boundedAsUnbounded_symmetric {M : H →L[ℝ] H}
    (h : ∀ (u v : H), @inner ℝ H _ (M u) v = @inner ℝ H _ u (M v)) :
    (boundedAsUnbounded M).IsSymmetric := by
  intro u v
  exact h (u : H) (v : H)

/-- A bounded operator has relative bound 0 w.r.t. any operator. -/
theorem bounded_rel_bound_zero (T : UnboundedOp H) (M : H →L[ℝ] H) :
    ∃ b : ℝ, UnboundedOp.IsRelBounded (boundedAsUnbounded M) T 0 b := by
  -- bound b = ‖M‖, domain inclusion is `le_top` (M is everywhere-defined),
  -- and ‖M u‖ ≤ ‖M‖·‖u‖ is the operator-norm bound. Relative bound a = 0.
  refine ⟨‖M‖, le_top, ?_⟩
  intro u
  simp only [zero_mul, zero_add]
  exact M.le_opNorm (u : H)

end
