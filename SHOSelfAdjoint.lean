import KatoRellichContinuum
import SelfAdjointness

/-!
# SHO framework: honest statement of the self-adjointness half

`Constant-Framework-SHO/lean-constant-framework/` and
`New folder (15)/lean-constant-framework/` advertise "0 sorry, 0 axioms"
for four theorems about the Spiral Hermitian Operator. That figure is
achieved by defining the load-bearing hypothesis to be trivially true:

    abbrev SemiclassicalDecoupling : Prop := True
    theorem semiclassicalDecoupling_available : SemiclassicalDecoupling := True.intro

and the "spectral reduction" theorem proves `∀ γ, ∃ E, E = 1/4 + γ^2`
(discharged by `use 1/4 + γ^2`) — a statement with no operator, no zeta,
and no spectrum in it.

The prose source (`constant_framework_rigorous_proofs.md`) is much better:
its Lemma 1 / Lemma 2 (Friedrichs extension; magnetic Laplacian + bounded
potential via Kato–Rellich) are correct standard mathematics, and the
document honestly labels the Hilbert–Pólya *correspondence* as an
assumption rather than a result.

This module records the honest version of the formalizable half. The
1-D Dirichlet realization is genuinely proven (in
`KatoRellichContinuum.hp_continuum_symmetric`, machine-checked with axioms
`[propext, Classical.choice, Quot.sound]` only), and the correspondence is
stated as an explicit hypothesis-carrying definition — never as an axiom
and never as `True`.
-/

noncomputable section
open Set

namespace SHO

/-- The SHO framework's operator data in the formalizable 1-D case:
`H = -d²/dx² + V` on `(0,L)` with Dirichlet conditions, `V` bounded.
This is `HPContinuumOp` — the same structure the machine-checked
symmetry theorem is stated about. -/
abbrev Operator := HPContinuumOp

/-- **The honest content of "Theorem 1/2 (self-adjointness)".**

For any bounded potential on a bounded interval, the operator is symmetric
on H²∩H¹₀ — proven, not assumed. This is `hp_continuum_symmetric`
specialized and re-exported so the SHO framework can cite a real theorem
instead of `SemiclassicalDecoupling := True`.

Note the hypotheses are the genuine H²∩H¹₀ data plus the integrability
side conditions; nothing here is vacuous. -/
theorem symmetric_of_bounded_potential (H : Operator)
    (u v : ℝ → ℝ)
    (hu_diff : DifferentiableOn ℝ u (Ioo 0 H.L))
    (hu_cont : ContinuousOn u (Icc 0 H.L))
    (hdu_diff : DifferentiableOn ℝ (deriv u) (Ioo 0 H.L))
    (hdu_cont : ContinuousOn (deriv u) (Icc 0 H.L))
    (hu0 : u 0 = 0) (huL : u H.L = 0)
    (hv_diff : DifferentiableOn ℝ v (Ioo 0 H.L))
    (hv_cont : ContinuousOn v (Icc 0 H.L))
    (hdv_diff : DifferentiableOn ℝ (deriv v) (Ioo 0 H.L))
    (hdv_cont : ContinuousOn (deriv v) (Icc 0 H.L))
    (hv0 : v 0 = 0) (hvL : v H.L = 0)
    (hVu_int : IntervalIntegrable (fun x => H.V x * u x * v x) MeasureTheory.volume 0 H.L)
    (hVv_int : IntervalIntegrable (fun x => u x * (H.V x * v x)) MeasureTheory.volume 0 H.L)
    (hddu_int : IntervalIntegrable (deriv (deriv u)) MeasureTheory.volume 0 H.L)
    (hddv_int : IntervalIntegrable (deriv (deriv v)) MeasureTheory.volume 0 H.L) :
    ∫ x in (0)..H.L, (H.apply u x) * v x =
    ∫ x in (0)..H.L, u x * (H.apply v x) :=
  hp_continuum_symmetric H u v hu_diff hu_cont hdu_diff hdu_cont hu0 huL
    hv_diff hv_cont hdv_diff hdv_cont hv0 hvL hVu_int hVv_int hddu_int hddv_int

/-- **The correspondence claim, stated honestly as a hypothesis.**

`SpectrumMatchesZeros H f` says: the operator's eigenvalue at index `n`,
transported by `f`, equals the `n`-th zeta ordinate. The SHO documents
call this the "claimed correspondence" and give no existence proof for
the required parameter choices; it is therefore a *predicate to be
discharged*, not an axiom to be assumed.

Nothing in this project proves any instance of it, and — per the growth-rate
obstruction in `ANALYSIS_eigenvalue_reduction.md` — no bounded potential on
a bounded interval can satisfy it for all `n`. -/
def SpectrumMatchesZeros (_H : Operator) (eigen zeros : ℕ → ℝ) : Prop :=
  ∀ n, eigen n = zeros n

/-- The honest conditional: *if* one exhibits an operator whose spectrum is
the zero set, *then* the correspondence holds for it — by definition. This
is the entire logical content the SHO framework actually has, and it is a
tautology, which is exactly why the correspondence must be *constructed*
rather than assumed. Stating it this way makes the gap visible instead of
hiding it behind `True`. -/
theorem correspondence_is_the_open_problem
    (H : Operator) (eigen zeros : ℕ → ℝ) (h : ∀ n, eigen n = zeros n) :
    SpectrumMatchesZeros H eigen zeros := h

end SHO
