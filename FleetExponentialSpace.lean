import FleetArithmeticContinuity

noncomputable section
open Complex
namespace FleetExponentialSpace
open FleetArithmeticContinuity FleetExponentialEnvelope

theorem bound_zero : Bound 0 (0 : ℝ → ℂ) := by
  change Bound 0 (fun _ : ℝ => (0 : ℂ))
  constructor
  · exact contDiff_const
  · simp
  · simp
  · simp

theorem bound_add {E F : ℝ} {f g : ℝ → ℂ} (hf : Bound E f) (hg : Bound F g) :
    Bound (E+F) (f+g) := by
  have hfd := hf.smooth.differentiable (by norm_num)
  have hgd := hg.smooth.differentiable (by norm_num)
  have hfd' : Differentiable ℝ (deriv f) :=
    ((contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1+1) f from hf.smooth)).2.2).differentiable (by norm_num)
  have hgd' : Differentiable ℝ (deriv g) :=
    ((contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1+1) g from hg.smooth)).2.2).differentiable (by norm_num)
  have h1 : deriv (f+g) = deriv f + deriv g := funext (fun u => deriv_add (hfd u) (hgd u))
  have h2 : deriv (deriv (f+g)) = deriv (deriv f) + deriv (deriv g) := by
    rw [h1]
    exact funext (fun u => deriv_add (hfd' u) (hgd' u))
  refine ⟨hf.smooth.add hg.smooth, ?_, ?_, ?_⟩
  · intro u
    exact (norm_add_le _ _).trans (by simpa only [add_mul] using add_le_add (hf.zero u) (hg.zero u))
  · intro u
    rw [h1]
    exact (norm_add_le _ _).trans (by simpa only [add_mul] using add_le_add (hf.first u) (hg.first u))
  · intro u
    rw [h2]
    exact (norm_add_le _ _).trans (by simpa only [add_mul] using add_le_add (hf.second u) (hg.second u))

theorem bound_const_mul {E : ℝ} {g : ℝ → ℂ} (hg : Bound E g) (c : ℂ) :
    Bound (‖c‖*E) (fun u => c*g u) := by
  have hd := hg.smooth.differentiable (by norm_num)
  have hd' : Differentiable ℝ (deriv g) :=
    ((contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1+1) g from hg.smooth)).2.2).differentiable (by norm_num)
  have h1 : deriv (fun u => c*g u) = fun u => c*deriv g u :=
    funext (fun u => (hd u).hasDerivAt.const_mul c |>.deriv)
  have h2 : deriv (deriv (fun u => c*g u)) = fun u => c*deriv (deriv g) u := by
    rw [h1]
    exact funext (fun u => (hd' u).hasDerivAt.const_mul c |>.deriv)
  refine ⟨contDiff_const.mul hg.smooth, ?_, ?_, ?_⟩
  · intro u
    rw [norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hg.zero u) (norm_nonneg _)
  · intro u
    rw [h1, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hg.first u) (norm_nonneg _)
  · intro u
    rw [h2, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hg.second u) (norm_nonneg _)

/-- Finite spans preserve membership in the exponential C² test class. -/
theorem bound_sum {D : Type*} (s : Finset D) (E : D → ℝ) (g : D → ℝ → ℂ)
    (hg : ∀ d ∈ s, Bound (E d) (g d)) :
    Bound (∑ d ∈ s, E d) (fun u => ∑ d ∈ s, g d u) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (show Bound 0 (fun _ : ℝ => (0:ℂ)) from bound_zero)
  | @insert d s hd ih =>
    simp only [Finset.sum_insert hd]
    exact bound_add (hg d (Finset.mem_insert_self _ _))
      (ih (fun e he => hg e (Finset.mem_insert_of_mem he)))

end FleetExponentialSpace
