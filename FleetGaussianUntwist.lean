import FleetGaussianDictionaryMember
import FleetCompactExponentialBound

noncomputable section
open Complex
namespace FleetGaussianUntwist

/-- Undo Gaussian damping before periodizing a compact test. -/
def untwist (a : ℝ) (g : ℝ → ℂ) (u : ℝ) : ℂ :=
  g u * Complex.exp ((a : ℂ)*(u : ℂ)^2)

theorem smooth {a : ℝ} {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 (untwist a g) := by
  apply hg.mul
  exact (GaussianTest.contDiff_cexp 2).comp (contDiff_const.mul ((GaussianTest.contDiff_ofReal 2).pow 2))

theorem compact {a : ℝ} {g : ℝ → ℂ} (hg : HasCompactSupport g) :
    HasCompactSupport (untwist a g) := hg.mul_right

theorem damp_untwist (a : ℝ) (g : ℝ → ℂ) (u : ℝ) :
    untwist a g u * GaussianTest.gauss a 0 u = g u := by
  unfold untwist GaussianTest.gauss
  rw [mul_assoc, ← Complex.exp_add]
  simp

theorem support {a R : ℝ} {g : ℝ → ℂ} (hg : ∀ u, R < |u| → g u = 0) :
    ∀ u, R < |u| → untwist a g u = 0 := by
  intro u hu
  simp [untwist, hg u hu]

/-- Untwisting preserves a finite uniform bound through derivative order two. -/
theorem exists_uniform_bound {a : ℝ} {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g)
    (hs : HasCompactSupport g) : ∃ C : ℝ, 0 ≤ C ∧
    (∀ u, ‖untwist a g u‖ ≤ C) ∧
    (∀ u, ‖deriv (untwist a g) u‖ ≤ C) ∧
    (∀ u, ‖deriv (deriv (untwist a g)) u‖ ≤ C) := by
  obtain ⟨C, hC, h0, h1, h2⟩ := FleetCompactExponentialBound.exists_common_envelope
    (smooth (a := a) hg) (compact hs)
  have he (u : ℝ) : FleetExponentialEnvelope.envelope 3 u ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hu := _root_.abs_nonneg u
    linarith
  refine ⟨C, hC, ?_, ?_, ?_⟩
  · intro u
    exact (h0 u).trans (mul_le_of_le_one_right hC (he u))
  · intro u
    exact (h1 u).trans (mul_le_of_le_one_right hC (he u))
  · intro u
    exact (h2 u).trans (mul_le_of_le_one_right hC (he u))

end FleetGaussianUntwist
