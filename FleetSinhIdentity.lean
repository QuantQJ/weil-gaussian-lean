import Mathlib

/-!
# The exact sinh² identity behind two-point log-convexity

For a finite family of real ordinates `γ i` with real weights `w i`, put

  `g_b(γ, q) = exp (-(q-γ)²/(4b))`,   `R(q) = Σ_i w_i g_b(γ_i, q)`.

Then, for every `b ≠ 0`, `q`, `h`,

  `e^{h²/(2b)} R(q-h) R(q+h) − R(q)² = 2 Σ_i Σ_j w_i w_j g_i(q) g_j(q) sinh²(h(γ_i−γ_j)/(4b))`.

This is an algebraic identity (no analysis). With nonnegative weights the right side is `≥ 0`,
which is the two-point condition `R(q)² ≤ e^{h²/(2b)} R(q-h) R(q+h)` of `FleetTwoPointConvexity`
for a trace whose ordinates are all real.
-/

set_option autoImplicit false
noncomputable section
open Finset

namespace FleetSinhIdentity

variable {ι : Type*}

/-- Width-`b` Gaussian bump centred at `γ`, evaluated at `q`. -/
def g (b γ q : ℝ) : ℝ := Real.exp (-(q - γ)^2 / (4*b))

/-- Finite real-ordinate trace. -/
def R (s : Finset ι) (w γ : ι → ℝ) (b q : ℝ) : ℝ := ∑ i ∈ s, w i * g b (γ i) q

lemma shift_term {b : ℝ} (hb : b ≠ 0) (γi γj q h : ℝ) :
    Real.exp (h^2/(2*b)) * (g b γi (q-h) * g b γj (q+h))
      = g b γi q * g b γj q * Real.exp (h*(γj-γi)/(2*b)) := by
  simp only [g, ← Real.exp_add]
  congr 1
  field_simp
  ring

/-- An antisymmetric double sum vanishes. -/
lemma double_sum_antisymm (s : Finset ι) (f : ι → ι → ℝ) (hf : ∀ i j, f j i = -f i j) :
    ∑ i ∈ s, ∑ j ∈ s, f i j = 0 := by
  have h1 : ∑ i ∈ s, ∑ j ∈ s, f i j = ∑ j ∈ s, ∑ i ∈ s, f i j := Finset.sum_comm
  have h2 : ∑ j ∈ s, ∑ i ∈ s, f i j = -∑ i ∈ s, ∑ j ∈ s, f i j := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [hf i j, neg_neg])
  linarith

lemma cosh_sub_one (x : ℝ) : Real.cosh x - 1 = 2 * Real.sinh (x/2)^2 := by
  have h := Real.cosh_two_mul (x/2)
  rw [show 2*(x/2) = x by ring] at h
  rw [h, Real.cosh_sq]
  ring

/-- **The sinh² identity.** -/
theorem sinh_sq_identity (s : Finset ι) (w γ : ι → ℝ) {b : ℝ} (hb : b ≠ 0) (q h : ℝ) :
    Real.exp (h^2/(2*b)) * (R s w γ b (q-h) * R s w γ b (q+h)) - R s w γ b q ^ 2
      = 2 * ∑ i ∈ s, ∑ j ∈ s, w i * w j * g b (γ i) q * g b (γ j) q
          * Real.sinh (h*(γ i - γ j)/(4*b))^2 := by
  set a : ι → ι → ℝ := fun i j => w i * w j * g b (γ i) q * g b (γ j) q with ha
  set x : ι → ι → ℝ := fun i j => h*(γ j - γ i)/(2*b) with hx
  -- expand the left side as a double sum of a_ij (e^{x_ij} - 1)
  have hL : Real.exp (h^2/(2*b)) * (R s w γ b (q-h) * R s w γ b (q+h)) - R s w γ b q ^ 2
      = ∑ i ∈ s, ∑ j ∈ s, a i j * (Real.exp (x i j) - 1) := by
    unfold R
    rw [Finset.sum_mul_sum, sq (∑ i ∈ s, w i * g b (γ i) q), Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have := shift_term hb (γ i) (γ j) q h
    simp only [ha, hx]
    calc Real.exp (h^2/(2*b)) * (w i * g b (γ i) (q-h) * (w j * g b (γ j) (q+h)))
          - w i * g b (γ i) q * (w j * g b (γ j) q)
        = w i * w j * (Real.exp (h^2/(2*b)) * (g b (γ i) (q-h) * g b (γ j) (q+h)))
          - w i * g b (γ i) q * (w j * g b (γ j) q) := by ring
      _ = _ := by rw [this]; ring
  -- split e^x - 1 = (cosh x - 1) + sinh x; the sinh part is antisymmetric
  have hsplit : ∑ i ∈ s, ∑ j ∈ s, a i j * (Real.exp (x i j) - 1)
      = ∑ i ∈ s, ∑ j ∈ s, a i j * (Real.cosh (x i j) - 1)
        + ∑ i ∈ s, ∑ j ∈ s, a i j * Real.sinh (x i j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Real.cosh_add_sinh]; ring
  have hodd : ∑ i ∈ s, ∑ j ∈ s, a i j * Real.sinh (x i j) = 0 := by
    apply double_sum_antisymm
    intro i j
    have hx' : x j i = -x i j := by simp only [hx]; ring
    rw [hx', Real.sinh_neg]
    simp only [ha]; ring
  rw [hL, hsplit, hodd, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [cosh_sub_one]
  have e : x i j / 2 = -(h*(γ i - γ j)/(4*b)) := by simp only [hx]; field_simp; ring
  rw [e, Real.sinh_neg, neg_sq]
  simp only [ha]; ring

/-- Nonnegative weights give the two-point log-convexity inequality. -/
theorem two_point_of_nonneg (s : Finset ι) (w γ : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    {b : ℝ} (hb : b ≠ 0) (q h : ℝ) :
    R s w γ b q ^ 2 ≤ Real.exp (h^2/(2*b)) * (R s w γ b (q-h) * R s w γ b (q+h)) := by
  have key := sinh_sq_identity s w γ hb q h
  have hnn : 0 ≤ 2 * ∑ i ∈ s, ∑ j ∈ s, w i * w j * g b (γ i) q * g b (γ j) q
          * Real.sinh (h*(γ i - γ j)/(4*b))^2 := by
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg; intro i hi
    apply Finset.sum_nonneg; intro j hj
    have := hw i hi; have := hw j hj
    have : 0 ≤ g b (γ i) q := (Real.exp_pos _).le
    have : 0 ≤ g b (γ j) q := (Real.exp_pos _).le
    positivity
  linarith

end FleetSinhIdentity
