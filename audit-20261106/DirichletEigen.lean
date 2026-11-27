import Sobolev1D
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The Dirichlet eigenfunctions: the first non-trivial elements of `H2 L`

`H2Algebra` builds `zero`, `add` and `smul`. Nothing else inhabits `H2 L`, so
every continuum theorem in the project is so far exhibited only on `0`.

Here `sin (n*pi*x/L)` is put into `H2 L` for each `n >= 1`, and shown to solve
`-u'' = (n*pi/L)^2 * u`. That gives the project its first eigenpairs, and the
explicit quadratic growth `lam n = (n*pi/L)^2` that the growth obstruction
consumes on the eigenvalue side.
-/

set_option autoImplicit false
noncomputable section
open Real Set intervalIntegral

namespace DirichletEigen

variable {L : ℝ}

/-- The scaled frequency. -/
def freq (L : ℝ) (n : ℕ) : ℝ := (n : ℝ) * π / L

lemma hasDerivAt_sin_mul (a x : ℝ) :
    HasDerivAt (fun y => Real.sin (a * y)) (a * Real.cos (a * x)) x := by
  have h := (Real.hasDerivAt_sin (a * x)).comp x ((hasDerivAt_id x).const_mul a)
  simpa [mul_comm] using h

lemma hasDerivAt_cos_mul (a x : ℝ) :
    HasDerivAt (fun y => Real.cos (a * y)) (-(a * Real.sin (a * x))) x := by
  have h := (Real.hasDerivAt_cos (a * x)).comp x ((hasDerivAt_id x).const_mul a)
  simpa [mul_comm, neg_mul] using h

lemma deriv_sin_mul (a : ℝ) :
    deriv (fun y => Real.sin (a * y)) = fun x => a * Real.cos (a * x) :=
  funext fun x => (hasDerivAt_sin_mul a x).deriv

lemma deriv_cos_mul_const (a c : ℝ) :
    deriv (fun y => c * Real.cos (a * y)) = fun x => -(c * a * Real.sin (a * x)) := by
  funext x
  have h := (hasDerivAt_cos_mul a x).const_mul c
  have := h.deriv
  rw [this]; ring

/-- `deriv (deriv (sin (a*x))) = -a^2 * sin (a*x)`. -/
lemma deriv_deriv_sin_mul (a : ℝ) :
    deriv (deriv fun y => Real.sin (a * y)) = fun x => -(a ^ 2 * Real.sin (a * x)) := by
  rw [deriv_sin_mul]
  have : (fun x => a * Real.cos (a * x)) = fun y => a * Real.cos (a * y) := rfl
  rw [this, deriv_cos_mul_const]
  funext x; ring

/-- **The n-th Dirichlet eigenfunction, as an element of `H2 L`.** -/
def eigenfun (hL : 0 < L) (n : ℕ) : H2 L where
  f := fun x => Real.sin (freq L n * x)
  hf_diff := by
    intro x _
    exact ((Real.differentiable_sin.comp (differentiable_id.const_mul _)) x).differentiableWithinAt
  hf_cont := (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  bc_left := by simp
  bc_right := by
    show Real.sin (freq L n * L) = 0
    have : freq L n * L = (n : ℝ) * π := by
      unfold freq; field_simp
    rw [this]
    exact Real.sin_nat_mul_pi n
  hdf_int := by
    rw [deriv_sin_mul]
    exact (Continuous.intervalIntegrable
      (continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))) _ _)
  hdf_diff := by
    rw [deriv_sin_mul]
    intro x _
    exact (((Real.differentiable_cos.comp (differentiable_id.const_mul _)).const_mul _) x).differentiableWithinAt
  hdf_cont := by
    rw [deriv_sin_mul]
    exact (continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))).continuousOn
  hddf_int := by
    rw [deriv_deriv_sin_mul]
    exact (Continuous.intervalIntegrable
      (continuous_neg.comp (continuous_const.mul
        (Real.continuous_sin.comp (continuous_const.mul continuous_id)))) _ _)

/-- **The eigenvalue equation.** `-u'' = (n*pi/L)^2 * u`, pointwise everywhere. -/
theorem eigen_equation (hL : 0 < L) (n : ℕ) (x : ℝ) :
    -(deriv (deriv (eigenfun hL n).f) x) = freq L n ^ 2 * (eigenfun hL n).f x := by
  show -(deriv (deriv fun y => Real.sin (freq L n * y)) x)
      = freq L n ^ 2 * Real.sin (freq L n * x)
  rw [deriv_deriv_sin_mul]; ring

/-- The eigenfunction is not the zero element: it is nonzero at `L/(2n)`. -/
theorem eigenfun_ne_zero (hL : 0 < L) (n : ℕ) (hn : 0 < n) :
    (eigenfun hL n).f (L / (2 * n)) ≠ 0 := by
  show Real.sin (freq L n * (L / (2 * n))) ≠ 0
  have hnR : (0:ℝ) < (n:ℝ) := Nat.cast_pos.mpr hn
  have : freq L n * (L / (2 * n)) = π / 2 := by
    unfold freq; field_simp; ring
  rw [this, Real.sin_pi_div_two]
  norm_num

/-- **The quadratic growth, explicitly.** `lam n = (n*pi/L)^2 = (pi/L)^2 * n^2`,
which is exactly the `c * n^2` lower bound the growth obstruction consumes. -/
theorem eigenvalue_quadratic (hL : 0 < L) (n : ℕ) :
    freq L n ^ 2 = (π / L) ^ 2 * (n : ℝ) ^ 2 := by
  unfold freq; field_simp; ring

end DirichletEigen

#print axioms DirichletEigen.eigenfun
#print axioms DirichletEigen.eigen_equation
#print axioms DirichletEigen.eigenfun_ne_zero
#print axioms DirichletEigen.eigenvalue_quadratic
