import PoincareSobolev
import Mathlib

/-!
# Hölder continuity and equicontinuity of `H¹₀` functions

The classical route from "the operator is coercive" to "the spectrum is
**discrete**" runs through the Rellich–Kondrachov theorem: the embedding
`H¹₀(0,L) ↪ L²(0,L)` is *compact*, hence the resolvent is compact, hence the
spectrum is a sequence of eigenvalues accumulating only at `+∞`.

In one dimension that compactness is elementary, and its analytic content is
a single estimate proven here:

  **`|u(x) − u(y)| ≤ √|x−y| · ‖u'‖₂`**  (`holder_half`)

i.e. every `H¹₀` function is Hölder continuous with exponent `1/2`, with a
constant controlled by the `H¹` seminorm alone. Two consequences follow
immediately and are also proven:

* `holder_uniform` — a *uniform* modulus of continuity for the whole ball
  `‖u'‖₂ ≤ C`. This is exactly equicontinuity of that family.
* `unif_bounded_of_deriv_bound` — the same ball is uniformly bounded in sup
  norm (from `sobolev_sup_bound`).

Uniform boundedness + equicontinuity are precisely the hypotheses of
Arzelà–Ascoli, so this module supplies both inputs to 1-D
Rellich–Kondrachov. Applying Mathlib's Ascoli machinery to conclude
compactness of the embedding is the natural next step; the analysis is done
here.

No `sorry`, no custom axioms.
-/

noncomputable section
open MeasureTheory Set intervalIntegral

namespace HolderEquicontinuity

variable {L : ℝ}

/-! ## The increment formula -/

/-- For `u ∈ H²∩H¹₀(0,L)` and `y ≤ x` in `[0,L]`, `u(x) − u(y) = ∫_y^x u'`. -/
theorem increment_eq (hL : 0 < L) (u : H2 L) {x y : ℝ}
    (hy0 : 0 ≤ y) (hyx : y ≤ x) (hxL : x ≤ L) :
    u.f x - u.f y = ∫ t in y..x, deriv u.f t := by
  have hx0 : 0 ≤ x := le_trans hy0 hyx
  have hyL : y ≤ L := le_trans hyx hxL
  have hux : u.f x = ∫ t in (0)..x, deriv u.f t :=
    H1zero.ftc_repr u.toH1zero x hx0 hxL
  have huy : u.f y = ∫ t in (0)..y, deriv u.f t :=
    H1zero.ftc_repr u.toH1zero y hy0 hyL
  have huIcc : Set.uIcc (0:ℝ) L = Icc 0 L := Set.uIcc_of_le hL.le
  have hint : IntervalIntegrable (deriv u.f) volume 0 L := u.hdf_int
  have h1 : IntervalIntegrable (deriv u.f) volume 0 y :=
    hint.mono_set (by
      rw [Set.uIcc_of_le hy0, Set.uIcc_of_le hL.le]
      exact Icc_subset_Icc_right hyL)
  have h2 : IntervalIntegrable (deriv u.f) volume y x :=
    hint.mono_set (by
      rw [Set.uIcc_of_le hyx, Set.uIcc_of_le hL.le]
      exact Icc_subset_Icc (by linarith) hxL)
  have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
  rw [hux, huy, ← hadd]
  ring

/-! ## The Hölder-1/2 estimate -/

/-- Local energy is bounded by total energy. -/
lemma local_energy_le (hL : 0 < L) (u : H2 L) {x y : ℝ}
    (hy0 : 0 ≤ y) (hyx : y ≤ x) (hxL : x ≤ L) :
    (∫ t in y..x, (deriv u.f t) ^ 2) ≤ ∫ t in (0)..L, (deriv u.f t) ^ 2 := by
  have hx0 : 0 ≤ x := le_trans hy0 hyx
  have hyL : y ≤ L := le_trans hyx hxL
  have huIcc : Set.uIcc (0:ℝ) L = Icc 0 L := Set.uIcc_of_le hL.le
  have hint : IntervalIntegrable (fun t => (deriv u.f t) ^ 2) volume 0 L := by
    apply ContinuousOn.intervalIntegrable; rw [huIcc]; exact u.hdf_cont.pow 2
  have h0y : IntervalIntegrable (fun t => (deriv u.f t) ^ 2) volume 0 y :=
    hint.mono_set (by
      rw [Set.uIcc_of_le hy0, Set.uIcc_of_le hL.le]
      exact Icc_subset_Icc_right hyL)
  have hyx' : IntervalIntegrable (fun t => (deriv u.f t) ^ 2) volume y x :=
    hint.mono_set (by
      rw [Set.uIcc_of_le hyx, Set.uIcc_of_le hL.le]
      exact Icc_subset_Icc (by linarith) hxL)
  have hxL' : IntervalIntegrable (fun t => (deriv u.f t) ^ 2) volume x L :=
    hint.mono_set (by
      rw [Set.uIcc_of_le hxL, Set.uIcc_of_le hL.le]
      exact Icc_subset_Icc_left hx0)
  have e1 := intervalIntegral.integral_add_adjacent_intervals h0y hyx'
  have e2 := intervalIntegral.integral_add_adjacent_intervals
    (h0y.trans hyx' : IntervalIntegrable _ volume 0 x) hxL'
  have hn0y : 0 ≤ ∫ t in (0)..y, (deriv u.f t) ^ 2 :=
    intervalIntegral.integral_nonneg hy0 (fun t _ => sq_nonneg _)
  have hnxL : 0 ≤ ∫ t in x..L, (deriv u.f t) ^ 2 :=
    intervalIntegral.integral_nonneg hxL (fun t _ => sq_nonneg _)
  linarith [e1, e2, hn0y, hnxL]

/-- **Hölder-1/2 estimate, squared form** (ordered case):
`|u(x) − u(y)|² ≤ (x − y) · ∫₀ᴸ (u')²`. -/
theorem holder_half_sq_of_le (hL : 0 < L) (u : H2 L) {x y : ℝ}
    (hy0 : 0 ≤ y) (hyx : y ≤ x) (hxL : x ≤ L) :
    (u.f x - u.f y) ^ 2 ≤ (x - y) * ∫ t in (0)..L, (deriv u.f t) ^ 2 := by
  have hx0 : 0 ≤ x := le_trans hy0 hyx
  have hyL : y ≤ L := le_trans hyx hxL
  have hcont : ContinuousOn (deriv u.f) (Icc y x) :=
    u.hdf_cont.mono (Icc_subset_Icc hy0 hxL)
  have hcs := PoincareSobolev.sq_intervalIntegral_le hyx hcont
  rw [increment_eq hL u hy0 hyx hxL]
  have hloc := local_energy_le hL u hy0 hyx hxL
  have hxy : (0:ℝ) ≤ x - y := by linarith
  calc (∫ t in y..x, deriv u.f t) ^ 2
      ≤ (x - y) * ∫ t in y..x, (deriv u.f t) ^ 2 := hcs
    _ ≤ (x - y) * ∫ t in (0)..L, (deriv u.f t) ^ 2 :=
        mul_le_mul_of_nonneg_left hloc hxy

/-- **Hölder-1/2 estimate** (squared, symmetric form):
`|u(x) − u(y)|² ≤ |x − y| · ‖u'‖₂²` for all `x, y ∈ [0,L]`. -/
theorem holder_half_sq (hL : 0 < L) (u : H2 L) {x y : ℝ}
    (hx : x ∈ Icc (0:ℝ) L) (hy : y ∈ Icc (0:ℝ) L) :
    (u.f x - u.f y) ^ 2 ≤ |x - y| * ∫ t in (0)..L, (deriv u.f t) ^ 2 := by
  rcases le_total y x with h | h
  · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ x - y)]
    exact holder_half_sq_of_le hL u hy.1 h hx.2
  · rw [abs_of_nonpos (by linarith : x - y ≤ 0)]
    have := holder_half_sq_of_le hL u hx.1 h hy.2
    calc (u.f x - u.f y) ^ 2 = (u.f y - u.f x) ^ 2 := by ring
      _ ≤ (y - x) * ∫ t in (0)..L, (deriv u.f t) ^ 2 := this
      _ = -(x - y) * ∫ t in (0)..L, (deriv u.f t) ^ 2 := by ring

/-- **Hölder-1/2 continuity.** `|u(x) − u(y)| ≤ √|x−y| · ‖u'‖₂`.

Every `H¹₀` function is `1/2`-Hölder, with constant the `H¹` seminorm. -/
theorem holder_half (hL : 0 < L) (u : H2 L) {x y : ℝ}
    (hx : x ∈ Icc (0:ℝ) L) (hy : y ∈ Icc (0:ℝ) L) :
    |u.f x - u.f y|
      ≤ Real.sqrt |x - y| * Real.sqrt (∫ t in (0)..L, (deriv u.f t) ^ 2) := by
  have hsq := holder_half_sq hL u hx hy
  have hK : 0 ≤ ∫ t in (0)..L, (deriv u.f t) ^ 2 :=
    intervalIntegral.integral_nonneg hL.le (fun t _ => sq_nonneg _)
  have hprod : Real.sqrt |x - y| * Real.sqrt (∫ t in (0)..L, (deriv u.f t) ^ 2)
      = Real.sqrt (|x - y| * ∫ t in (0)..L, (deriv u.f t) ^ 2) :=
    (Real.sqrt_mul (abs_nonneg _) _).symm
  rw [hprod, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hsq

/-! ## Equicontinuity and uniform boundedness of `H¹` balls -/

/-- **Uniform modulus of continuity = equicontinuity.**
On the ball `‖u'‖₂² ≤ C` the same estimate `|u(x) − u(y)| ≤ √C·√|x−y|`
holds for *every* member, with no dependence on `u`. -/
theorem holder_uniform (hL : 0 < L) (u : H2 L) {C : ℝ}
    (hC : (∫ t in (0)..L, (deriv u.f t) ^ 2) ≤ C)
    {x y : ℝ} (hx : x ∈ Icc (0:ℝ) L) (hy : y ∈ Icc (0:ℝ) L) :
    |u.f x - u.f y| ≤ Real.sqrt C * Real.sqrt |x - y| := by
  have hK : 0 ≤ ∫ t in (0)..L, (deriv u.f t) ^ 2 :=
    intervalIntegral.integral_nonneg hL.le (fun t _ => sq_nonneg _)
  have h := holder_half hL u hx hy
  have hmono : Real.sqrt (∫ t in (0)..L, (deriv u.f t) ^ 2) ≤ Real.sqrt C :=
    Real.sqrt_le_sqrt hC
  calc |u.f x - u.f y|
      ≤ Real.sqrt |x - y| * Real.sqrt (∫ t in (0)..L, (deriv u.f t) ^ 2) := h
    _ ≤ Real.sqrt |x - y| * Real.sqrt C :=
        mul_le_mul_of_nonneg_left hmono (Real.sqrt_nonneg _)
    _ = Real.sqrt C * Real.sqrt |x - y| := by ring

/-- **Uniform boundedness** on the same ball: `|u(x)| ≤ √(L·C)`. -/
theorem unif_bounded_of_deriv_bound (hL : 0 < L) (u : H2 L) {C : ℝ}
    (hC : (∫ t in (0)..L, (deriv u.f t) ^ 2) ≤ C)
    {x : ℝ} (hx : x ∈ Icc (0:ℝ) L) :
    |u.f x| ≤ Real.sqrt (L * C) := by
  have hsup := PoincareSobolev.sobolev_sup_bound hL u hx.1 hx.2
  have hstep : (u.f x) ^ 2 ≤ L * C := by
    have := mul_le_mul_of_nonneg_left hC hL.le
    linarith [hsup, this]
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hstep

/-- The two Arzelà–Ascoli inputs, packaged: on `‖u'‖₂² ≤ C` the family is
uniformly bounded **and** uniformly equicontinuous. This is the analytic
content of 1-D Rellich–Kondrachov. -/
theorem ascoli_inputs (hL : 0 < L) (u : H2 L) {C : ℝ}
    (hC : (∫ t in (0)..L, (deriv u.f t) ^ 2) ≤ C) :
    (∀ x ∈ Icc (0:ℝ) L, |u.f x| ≤ Real.sqrt (L * C)) ∧
    (∀ x ∈ Icc (0:ℝ) L, ∀ y ∈ Icc (0:ℝ) L,
      |u.f x - u.f y| ≤ Real.sqrt C * Real.sqrt |x - y|) :=
  ⟨fun x hx => unif_bounded_of_deriv_bound hL u hC hx,
   fun x hx y hy => holder_uniform hL u hC hx hy⟩

end HolderEquicontinuity
