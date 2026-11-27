import FleetFourierLittleO

namespace FleetFiniteWindowEscape
open Filter Topology Set

/-- A finite bank of vanishing probes cannot detect an arbitrarily distant fixed multiplicity
at fixed positive tolerance. Its added weighted mass can simultaneously be arbitrarily small. -/
theorem exists_remote_atoms {ι : Type*} (J : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ j ∈ J, Tendsto (f j) atTop (𝓝 0))
    (m : ℕ) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (R : ℝ) :
    ∃ x : ℝ, R < x ∧ 0 < x ∧
      (∀ j ∈ J, ‖(m : ℂ) * f j x‖ < ε) ∧ (m : ℝ) / (1+x^2) < η := by
  classical
  have hprobe (j : ι) (hj : j ∈ J) : ∀ᶠ x : ℝ in atTop, ‖(m : ℂ)*f j x‖ < ε := by
    have ht := ((hf j hj).const_mul (m : ℂ)).norm
    simp only [mul_zero, norm_zero] at ht
    exact ht.eventually (Iio_mem_nhds hε)
  have hall : ∀ᶠ x : ℝ in atTop, ∀ j ∈ J, ‖(m : ℂ)*f j x‖ < ε := by
    exact (Filter.eventually_all_finset J).mpr hprobe
  have hpow : Tendsto (fun x : ℝ => x^2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have hden : Tendsto (fun x : ℝ => 1+x^2) atTop atTop :=
    tendsto_atTop_mono (fun x => by linarith) hpow
  have hmass : Tendsto (fun x : ℝ => (m : ℝ)/(1+x^2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have hsmall := hmass.eventually (Iio_mem_nhds hη)
  obtain ⟨x, hxR, hx0, hxp, hxm⟩ :=
    (Filter.Eventually.and (eventually_gt_atTop R)
      ((eventually_gt_atTop (0 : ℝ)).and (hall.and hsmall))).exists
  exact ⟨x, hxR, hx0, hxp, hxm⟩

/-- Adding the remote atoms changes each pre-existing trace by less than epsilon. -/
theorem exists_remote_trace_perturbation {ι : Type*} (J : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ j ∈ J, Tendsto (f j) atTop (𝓝 0)) (oldTrace : ι → ℂ)
    (m : ℕ) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (R : ℝ) :
    ∃ x : ℝ, R < x ∧ 0 < x ∧
      (∀ j ∈ J, ‖(oldTrace j + (m : ℂ)*f j x) - oldTrace j‖ < ε) ∧
      (m : ℝ)/(1+x^2) < η := by
  simpa only [add_sub_cancel_left] using exists_remote_atoms J f hf m hε hη R

/-- The same phenomenon applies to any finite bank of the repository's interval transforms.
No assertion about an infinite determining family or exact zero-tolerance identities is made. -/
theorem exists_remote_hfun_atoms {ι : Type*} (J : Finset ι) (a : ι → ℝ)
    (g : ι → ℝ → ℂ) (ha : ∀ j ∈ J, 0 ≤ a j)
    (m : ℕ) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (R : ℝ) :
    ∃ x : ℝ, R < x ∧ 0 < x ∧
      (∀ j ∈ J, ‖(m : ℂ)*TestFunctions.hfun (a j) (g j) (x : ℂ)‖ < ε) ∧
      (m : ℝ)/(1+x^2) < η := by
  apply exists_remote_atoms J (fun j x => TestFunctions.hfun (a j) (g j) (x : ℂ))
    (fun j hj => (FleetFourierLittleO.hfun_tendsto_zero (ha j hj) (g j)).mono_left
      _root_.atTop_le_cocompact) m hε hη R

/-- Even after enforcing paired ordinates, remote atoms escape any fixed positive-tolerance bank. -/
theorem exists_remote_paired_hfun_atoms {ι : Type*} (J : Finset ι) (a : ι → ℝ)
    (g : ι → ℝ → ℂ) (hg : ∀ j ∈ J, TestFunctions.IsTestFn (a j) (g j))
    (m : ℕ) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (R : ℝ) :
    ∃ x : ℝ, R < x ∧ 0 < x ∧
      (∀ j ∈ J, ‖(m : ℂ) *
        (TestFunctions.hfun (a j) (g j) (x : ℂ) +
          TestFunctions.hfun (a j) (g j) ((-x : ℝ) : ℂ))‖ < ε) ∧
      (2*(m : ℝ))/(1+x^2) < η := by
  have hf (j : ι) (hj : j ∈ J) :
      Tendsto (fun x : ℝ => TestFunctions.hfun (a j) (g j) (x : ℂ) +
        TestFunctions.hfun (a j) (g j) ((-x : ℝ) : ℂ)) atTop (𝓝 0) := by
    have ht := FleetFourierLittleO.hfun_tendsto_zero (hg j hj).nonneg (g j)
    have hp := ht.mono_left _root_.atTop_le_cocompact
    have hn := ht.comp (tendsto_neg_atTop_atBot.mono_right _root_.atBot_le_cocompact)
    simpa using hp.add hn
  obtain ⟨x, hxR, hx0, hprobe, hmass⟩ := exists_remote_atoms J _ hf m hε
    (half_pos hη) R
  refine ⟨x, hxR, hx0, hprobe, ?_⟩
  have he : (2*(m : ℝ))/(1+x^2) = 2*((m : ℝ)/(1+x^2)) := by ring
  rw [he]
  linarith

end FleetFiniteWindowEscape

#print axioms FleetFiniteWindowEscape.exists_remote_atoms
#print axioms FleetFiniteWindowEscape.exists_remote_trace_perturbation
#print axioms FleetFiniteWindowEscape.exists_remote_hfun_atoms

#print axioms FleetFiniteWindowEscape.exists_remote_paired_hfun_atoms
