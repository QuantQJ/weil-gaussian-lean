import FleetGaussianUntwist
import FleetPeriodicReplacement
import FleetDampedPeriodicApproximation
import FleetGaussianPeriodizationTail
import FleetGaussianFiniteSpan

noncomputable section
open Set
namespace FleetGaussianDensity
open FleetArithmeticContinuity FleetSmoothPeriodization FleetGaussianUntwist

/-- Fixed-width Gaussians with rational centers span a dense test family in the
exponential C² topology for all admissible supported compact tests. -/
theorem exists_rational_gaussian_approx {b R : ℝ} (hb : 0 < b) {g : ℝ → ℂ}
    (hg : TestFunctions.IsTestFn R g) (hs : ∀ u, R < |u| → g u = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ ∃ s : Finset ℤ, ∃ c : ℤ → ℂ,
      Bound ε (g - fun u => ∑ k ∈ s, c k *
        GaussianTest.gauss b ((-((k : ℚ)/m) : ℚ) : ℝ) u) := by
  have hgc : HasCompactSupport g := by
    apply IsCompact.of_isClosed_subset (isCompact_Icc : IsCompact (Icc (-R) R)) (isClosed_tsupport g)
    apply closure_minimal _ isClosed_Icc
    intro u hu
    exact abs_le.mp (le_of_not_gt (fun h => hu (hs u h)))
  let F := untwist b g
  have hF : ContDiff ℝ 2 F := smooth hg.smooth
  have hFs : ∀ u, R < |u| → F u = 0 := support hs
  obtain ⟨C, hC, h0, h1, h2⟩ := exists_uniform_bound (a := b) hg.smooth hgc
  have he : 0 < ε/2 := by positivity
  obtain ⟨T, hT, htail⟩ := FleetGaussianPeriodizationTail.exists_gaussian_gluing_radius hb hC he
  obtain ⟨m, hm, hp, hPs, hPe, hP0, hP1, hP2⟩ :=
    FleetPeriodicReplacement.exists_periodic_replacement hg.nonneg hC hF hFs h0 h1 h2 T hT
  let P := periodize (2*Real.pi*m) F
  have herr := htail F P hF hPs (fun u hu => (hPe u hu).symm)
    (fun u => ⟨h0 u, h1 u, h2 u⟩) (fun u => ⟨hP0 u, hP1 u, hP2 u⟩)
  have hmP : 0 < 2*Real.pi*(m:ℝ) := mul_pos Real.two_pi_pos (by exact_mod_cast hm)
  obtain ⟨s, c, hpoly⟩ := FleetDampedPeriodicApproximation.exists_damped_polynomial_approx
    hb hmP he hPs hp
  have hadd := FleetExponentialSpace.bound_add herr hpoly
  have heq : (fun u => (F u-P u)*GaussianTest.gauss b 0 u) +
      (fun u => (P u-FleetTrigPrimitive.polynomial (2*Real.pi*m) s c u)*GaussianTest.gauss b 0 u) =
      g - fun u => ∑ k ∈ s, c k*GaussianTest.gauss b ((-((k:ℚ)/m):ℚ):ℝ) u := by
    funext u
    change (F u-P u)*GaussianTest.gauss b 0 u +
      (P u-FleetTrigPrimitive.polynomial (2*Real.pi*m) s c u)*GaussianTest.gauss b 0 u = _
    rw [show (F u-P u)*GaussianTest.gauss b 0 u +
        (P u-FleetTrigPrimitive.polynomial (2*Real.pi*m) s c u)*GaussianTest.gauss b 0 u =
        F u*GaussianTest.gauss b 0 u - GaussianTest.gauss b 0 u*
          FleetTrigPrimitive.polynomial (2*Real.pi*m) s c u by ring]
    rw [FleetGaussianFiniteSpan.damped_polynomial hm, damp_untwist]
    rfl
  refine ⟨m, hm, s, c, ?_⟩
  rw [heq] at hadd
  simpa only [add_halves] using hadd

end FleetGaussianDensity
