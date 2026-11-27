import FleetFiniteSpectrumCompactness

noncomputable section
open Filter Topology
namespace FleetApproximationTransfer

/-- A finite positive unit spectrum controls traces in the inverse-quadratic weighted norm. -/
theorem finite_trace_difference_le {N : ℕ} (x : Fin N → ℝ) {M ε : ℝ}
    (hm : (∑ i, (1+(x i)^2)⁻¹) ≤ M) (hε : 0 ≤ ε)
    (f g : ℝ → ℂ) (hfg : ∀ t, ‖f t-g t‖ ≤ ε/(1+t^2)) :
    ‖(∑ i, f (x i)) - ∑ i, g (x i)‖ ≤ M*ε := by
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ i, (f (x i)-g (x i))‖ ≤ ∑ i, ‖f (x i)-g (x i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ε/(1+(x i)^2) := Finset.sum_le_sum (fun i _ => hfg (x i))
    _ = ε * ∑ i, (1+(x i)^2)⁻¹ := by simp only [div_eq_mul_inv, Finset.mul_sum]
    _ ≤ ε*M := mul_le_mul_of_nonneg_left hm hε
    _ = M*ε := mul_comm _ _

/-- Dictionary convergence extends to a target if both its trace function and target
value admit compatible arbitrary-accuracy approximations by dictionary entries. -/
theorem residual_tendsto_of_dictionary
    {D : Type*} (c : ℕ → ℕ) (x : ∀ n, Fin (c n) → ℝ) {M : ℝ}
    (hm : ∀ n, (∑ i, (1+(x n i)^2)⁻¹) ≤ M)
    (dictionary : D → ℝ → ℂ) (target : D → ℂ)
    (hd : ∀ d, Tendsto (fun n => (∑ i, dictionary d (x n i))-target d)
      atTop (𝓝 0))
    (f : ℝ → ℂ) (L : ℂ)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ d : D,
      (∀ t, ‖f t-dictionary d t‖ ≤ ε/(1+t^2)) ∧ ‖L-target d‖ ≤ ε) :
    Tendsto (fun n => (∑ i, f (x n i))-L) atTop (𝓝 0) := by
  have hM : 0 ≤ M := (Finset.sum_nonneg (fun i _ => by positivity)).trans (hm 0)
  apply Metric.tendsto_nhds.mpr
  intro η hη
  let ε := η/(2*(M+2))
  have hε : 0 < ε := div_pos hη (by positivity)
  have heq : ε * (2*(M+2)) = η := div_mul_cancel₀ _ (by positivity)
  obtain ⟨d, hfd, hLd⟩ := happrox ε hε
  have hd' := (Metric.tendsto_nhds.mp (hd d)) ε hε
  filter_upwards [hd'] with n hn
  rw [dist_zero_right] at hn ⊢
  have hdiff := finite_trace_difference_le (x n) (hm n) hε.le f (dictionary d) hfd
  have hdecomp : (∑ i, f (x n i))-L =
      ((∑ i, f (x n i))-(∑ i, dictionary d (x n i))) +
      ((∑ i, dictionary d (x n i))-target d) + (target d-L) := by ring
  rw [hdecomp]
  have ht := norm_add_le
    (((∑ i, f (x n i))-(∑ i, dictionary d (x n i))) +
      ((∑ i, dictionary d (x n i))-target d)) (target d-L)
  have ht' := norm_add_le ((∑ i, f (x n i))-(∑ i, dictionary d (x n i)))
    ((∑ i, dictionary d (x n i))-target d)
  have hlast : ‖target d-L‖ ≤ ε := by rw [norm_sub_rev]; exact hLd
  nlinarith

/-- An explicit sufficient dictionary interface for the finite-spectrum criterion.
No density or arithmetic-target continuity theorem is presumed. -/
theorem RH_of_dictionary_approximation
    {D : Type*} (c : ℕ → ℕ) (x : ∀ n, Fin (c n) → ℝ) {M : ℝ}
    (hm : ∀ n, (∑ i, (1+(x n i)^2)⁻¹) ≤ M)
    (dictionary : D → ℝ → ℂ) (target : D → ℂ)
    (hd : ∀ d, Tendsto (fun n => (∑ i, dictionary d (x n i))-target d)
      atTop (𝓝 0))
    (happrox : ∀ (a : ℝ) (g : ℝ → ℂ), TestFunctions.IsTestFn a g →
      (∀ u, a < |u| → g u = 0) → ∀ ε : ℝ, 0 < ε → ∃ d : D,
      (∀ t : ℝ, ‖TestFunctions.hfun a g (t : ℂ)-dictionary d t‖ ≤ ε/(1+t^2)) ∧
      ‖GammaExplicitFormula.gammaRHS a g-target d‖ ≤ ε) :
    RiemannHypothesis := by
  apply FleetFiniteSpectrumCompactness.RH_of_uniform_finite_approximation c x hm
  intro a g hg hs
  exact residual_tendsto_of_dictionary c x hm dictionary target hd
    (fun t : ℝ => TestFunctions.hfun a g (t : ℂ))
    (GammaExplicitFormula.gammaRHS a g) (happrox a g hg hs)

end FleetApproximationTransfer
