import Mathlib
import Sobolev1D

/-!
# Dirichlet Laplacian: Symmetry on H²∩H¹₀

Phase 3, Step 2.

Defines -d²/dx² on (0,L) with Dirichlet BCs as a concrete operator
and proves it is symmetric using integration by parts (proven in Sobolev1D.lean).

The self-adjointness (D(A*) = D(A)) for Sturm-Liouville operators on
bounded intervals is a classical result requiring elliptic regularity.
We prove symmetry here; the domain characterization is stated with
classical citations.

## References

Reed & Simon, Vol. II, Theorem X.1.
Zettl, Sturm-Liouville Theory, Ch. 4.
-/

noncomputable section

open MeasureTheory Set intervalIntegral

/-- The Dirichlet Laplacian data: domain (0,L), operator -d²/dx². -/
structure DirichletLaplacian where
  L : ℝ
  hL : 0 < L

namespace DirichletLaplacian

variable (D : DirichletLaplacian)

/-- The operator acts as u ↦ -u''. (Takes `_D` so `D.apply` dot-notation
    resolves; the action itself is independent of the domain data.) -/
def apply (_D : DirichletLaplacian) (u : ℝ → ℝ) : ℝ → ℝ := fun x => -(deriv (deriv u) x)

/-- Symmetry: ⟨-u'', v⟩ = ⟨u, -v''⟩ for functions with Dirichlet BCs.

    This is proven by two applications of integration by parts.
    Both boundary terms vanish from u(0)=u(L)=v(0)=v(L)=0.

    The proof chains:
      ⟨-u'', v⟩ = ∫ u'v' = ⟨-v'', u⟩ = ⟨u, -v''⟩

    The key IBP step uses Mathlib's
    `integral_mul_deriv_eq_deriv_mul_of_hasDerivAt`. -/
theorem symmetric
    (u v : ℝ → ℝ)
    -- u is in H²∩H¹₀
    (hu_diff : DifferentiableOn ℝ u (Ioo 0 D.L))
    (hu_cont : ContinuousOn u (Icc 0 D.L))
    (hdu_diff : DifferentiableOn ℝ (deriv u) (Ioo 0 D.L))
    (hdu_cont : ContinuousOn (deriv u) (Icc 0 D.L))
    (hu0 : u 0 = 0) (huL : u D.L = 0)
    -- v is in H²∩H¹₀
    (hv_diff : DifferentiableOn ℝ v (Ioo 0 D.L))
    (hv_cont : ContinuousOn v (Icc 0 D.L))
    (hdv_diff : DifferentiableOn ℝ (deriv v) (Ioo 0 D.L))
    (hdv_cont : ContinuousOn (deriv v) (Icc 0 D.L))
    (hv0 : v 0 = 0) (hvL : v D.L = 0)
    -- u'', v'' ∈ L¹ — the genuine H² integrability data (u'' ∈ L² ⊂ L¹),
    -- required: without it the IBP boundary formula is false under Lean's
    -- junk-value integral semantics.
    (hddu_int : IntervalIntegrable (deriv (deriv u)) volume 0 D.L)
    (hddv_int : IntervalIntegrable (deriv (deriv v)) volume 0 D.L) :
    -- ⟨-u'', v⟩ = ⟨u, -v''⟩
    ∫ x in (0)..D.L, (D.apply u x) * v x =
    ∫ x in (0)..D.L, u x * (D.apply v x) := by
  -- Package the hypotheses into H²∩H¹₀ structures and apply the proven
  -- `H2.laplacian_symmetric` (Sobolev1D.lean, product-FTC route, no sorry).
  have hu_int : IntervalIntegrable (deriv u) volume 0 D.L := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le D.hL.le]; exact hdu_cont
  have hv_int : IntervalIntegrable (deriv v) volume 0 D.L := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le D.hL.le]; exact hdv_cont
  exact H2.laplacian_symmetric D.hL
    ⟨⟨u, hu_diff, hu_cont, hu0, huL, hu_int⟩, hdu_diff, hdu_cont, hddu_int⟩
    ⟨⟨v, hv_diff, hv_cont, hv0, hvL, hv_int⟩, hdv_diff, hdv_cont, hddv_int⟩

/- Original (Mathlib-version-sensitive) IBP attempt, preserved for reference.
   Superseded by the `sorry` in `symmetric` above; commented out so it does not
   break the build against the current Mathlib revision.

private theorem symmetric_ibp_attempt
    (D : DirichletLaplacian) (u v : ℝ → ℝ)
    (hu_diff : DifferentiableOn ℝ u (Ioo 0 D.L))
    (hu_cont : ContinuousOn u (Icc 0 D.L))
    (hdu_diff : DifferentiableOn ℝ (deriv u) (Ioo 0 D.L))
    (hdu_cont : ContinuousOn (deriv u) (Icc 0 D.L))
    (hu0 : u 0 = 0) (huL : u D.L = 0)
    (hv_diff : DifferentiableOn ℝ v (Ioo 0 D.L))
    (hv_cont : ContinuousOn v (Icc 0 D.L))
    (hdv_diff : DifferentiableOn ℝ (deriv v) (Ioo 0 D.L))
    (hdv_cont : ContinuousOn (deriv v) (Icc 0 D.L))
    (hv0 : v 0 = 0) (hvL : v D.L = 0) :
    ∫ x in (0)..D.L, (D.apply u x) * v x =
    ∫ x in (0)..D.L, u x * (D.apply v x) := by
  unfold apply
  -- Step 1: ∫ (-u'') · v = ∫ u' · v' (IBP, boundary terms vanish)
  have ibp_uv := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (hdu_cont.mono (by simp [Set.uIcc_of_le D.hL.le]))
    (hv_cont.mono (by simp [Set.uIcc_of_le D.hL.le]))
    (fun x hx => by
      simp [min_eq_left D.hL.le, max_eq_right D.hL.le] at hx
      exact (hdu_diff x hx).hasDerivAt
        (hdu_cont.mono (by simp [Set.uIcc_of_le D.hL.le]) |>.isOpen_inter_preimage isOpen_Ioo
          |>.mem_nhds ⟨hx.1, hx.2⟩))
    (fun x hx => by
      simp [min_eq_left D.hL.le, max_eq_right D.hL.le] at hx
      exact (hv_diff x hx).hasDerivAt
        (hv_cont.mono (by simp [Set.uIcc_of_le D.hL.le]) |>.isOpen_inter_preimage isOpen_Ioo
          |>.mem_nhds ⟨hx.1, hx.2⟩))
    (hdu_cont.mono (by simp [Set.uIcc_of_le D.hL.le]) |>.integrableOn_compact isCompact_uIcc
      |>.1)
    (hv_cont.mono (by simp [Set.uIcc_of_le D.hL.le]) |>.integrableOn_compact isCompact_uIcc
      |>.1)
  -- ibp_uv: ∫ (deriv u) · (deriv v) = (deriv u)(L)·v(L) - (deriv u)(0)·v(0) - ∫ (deriv² u) · v
  rw [hvL, hv0, mul_zero, mul_zero, sub_zero, zero_sub, neg_neg] at ibp_uv
  -- ibp_uv: ∫ (deriv u) · (deriv v) = ∫ (deriv² u) · v
  -- Step 2: ∫ u' · v' = ∫ u · (-v'') (IBP again, other direction)
  have ibp_vu := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (hdv_cont.mono (by simp [Set.uIcc_of_le D.hL.le]))
    (hu_cont.mono (by simp [Set.uIcc_of_le D.hL.le]))
    (fun x hx => by
      simp [min_eq_left D.hL.le, max_eq_right D.hL.le] at hx
      exact (hdv_diff x hx).hasDerivAt
        (hdv_cont.mono (by simp [Set.uIcc_of_le D.hL.le]) |>.isOpen_inter_preimage isOpen_Ioo
          |>.mem_nhds ⟨hx.1, hx.2⟩))
    (fun x hx => by
      simp [min_eq_left D.hL.le, max_eq_right D.hL.le] at hx
      exact (hu_diff x hx).hasDerivAt
        (hu_cont.mono (by simp [Set.uIcc_of_le D.hL.le]) |>.isOpen_inter_preimage isOpen_Ioo
          |>.mem_nhds ⟨hx.1, hx.2⟩))
    (hdv_cont.mono (by simp [Set.uIcc_of_le D.hL.le]) |>.integrableOn_compact isCompact_uIcc
      |>.1)
    (hu_cont.mono (by simp [Set.uIcc_of_le D.hL.le]) |>.integrableOn_compact isCompact_uIcc
      |>.1)
  rw [huL, hu0, mul_zero, mul_zero, sub_zero, zero_sub, neg_neg] at ibp_vu
  -- ibp_vu: ∫ (deriv v) · (deriv u) = ∫ (deriv² v) · u
  -- Now chain: ∫ (-u'')·v = ∫ u'·v' = ∫ v'·u' = ∫ (-v'')·u = ∫ u·(-v'')
  -- From ibp_uv: ∫ u'·v' = ∫ (u'')·v, so ∫ (-u'')·v = -∫(u'')·v = -(∫u'v' - ... )
  -- Let's use linarith on the relationship
  have comm : ∫ x in (0)..D.L, deriv u x * deriv v x =
              ∫ x in (0)..D.L, deriv v x * deriv u x := by
    congr 1; ext x; ring
  -- From ibp_uv: ∫ u'v' = ∫ u''v
  -- Want: ∫ (-u'')v = ∫ u(-v'')
  -- ∫ (-u'')v = -∫ u''v = -∫ u'v' (by ibp_uv) = -∫ v'u' (by comm) = -∫ v''u (by ibp_vu) = ∫ u(-v'')
  have key1 : ∫ x in (0)..D.L, -(deriv (deriv u) x) * v x =
              -(∫ x in (0)..D.L, deriv (deriv u) x * v x) := by
    rw [← intervalIntegral.integral_neg]; congr 1; ext x; ring
  have key2 : ∫ x in (0)..D.L, u x * -(deriv (deriv v) x) =
              -(∫ x in (0)..D.L, deriv (deriv v) x * u x) := by
    rw [← intervalIntegral.integral_neg]; congr 1; ext x; ring
  rw [key1, key2]
  congr 1
  -- Need: ∫ (u'')v = ∫ (v'')u
  -- From ibp_uv: ∫ u'v' = ∫ u''v → ∫ u''v = ∫ u'v'
  -- From ibp_vu: ∫ v'u' = ∫ v''u → ∫ v''u = ∫ v'u'
  -- And ∫ u'v' = ∫ v'u'
  linarith [ibp_uv, ibp_vu, comm]
-/

end DirichletLaplacian

end
