import FleetGaussianDensity
import FleetArithmeticLinearSpan
import FleetLinearDictionary
import FleetExponentialDictionary

noncomputable section
open Filter Topology
namespace FleetGaussianCriterion
open FleetArithmeticContinuity GaussianTest

structure Span where
  denominator : ℕ
  modes : Finset ℤ
  coefficient : ℤ → ℂ

def Span.center (d : Span) (k : ℤ) : ℚ := -((k : ℚ)/d.denominator)
def test (b : ℝ) (d : Span) (u : ℝ) : ℂ :=
  ∑ k ∈ d.modes, d.coefficient k*gauss b (d.center k : ℝ) u

lemma rhs_test {b : ℝ} (hb : 0 < b) (d : Span) :
    FleetFullLineArithmetic.rhs (test b d) =
      ∑ k ∈ d.modes, d.coefficient k*FleetFullLineArithmetic.rhs (gauss b (d.center k : ℝ)) := by
  choose E hE hg using (fun k : ℤ => FleetGaussianDictionaryMember.exists_bound hb (d.center k : ℝ))
  unfold test
  rw [FleetArithmeticLinearSpan.rhs_sum d.modes (fun k => ‖d.coefficient k‖*E k)
    (fun k u => d.coefficient k*gauss b (d.center k : ℝ) u)
    (fun k _ => mul_nonneg (norm_nonneg _) (hE k))
    (fun k _ => FleetExponentialSpace.bound_const_mul (hg k) (d.coefficient k))]
  simp_rw [FleetArithmeticLinearSpan.rhs_const_mul]

lemma h_test {b : ℝ} (hb : 0 < b) (d : Span) (t : ℝ) :
    FleetFullLineFourier.h (test b d) t =
      ∑ k ∈ d.modes, d.coefficient k*FleetFullLineFourier.h (gauss b (d.center k : ℝ)) t := by
  unfold test
  rw [FleetGaussianFiniteSpan.h_sum_real hb]
  simp_rw [FleetGaussianDictionaryMember.h_gauss_eq hb]

/-- A single fixed-width rational-centered Gaussian bank suffices, provided
one finite family has uniformly bounded weighted mass and convergent residuals
for every bank entry. Existence of such a family is not asserted. -/
theorem RH_of_rational_gaussian_residuals {b : ℝ} (hb : 0 < b)
    (c : ℕ → ℕ) (x : ∀ n, Fin (c n) → ℝ) {M : ℝ}
    (hm : ∀ n, (∑ i, (1+(x n i)^2)⁻¹) ≤ M)
    (hr : ∀ q : ℚ, Tendsto (fun n =>
      (∑ i : Fin (c n), FleetFullLineFourier.h (gauss b (q : ℝ)) (x n i))-
        FleetFullLineArithmetic.rhs (gauss b (q : ℝ))) atTop (𝓝 0)) :
    RiemannHypothesis := by
  apply FleetExponentialDictionary.RH_of_exponential_dictionary c x hm (test b)
  · intro d
    exact FleetGaussianFiniteSpan.exists_bound hb d.modes (fun k => (d.center k : ℝ)) d.coefficient
  · intro a g hg hs ε hε
    obtain ⟨m, _, s, coeff, hd⟩ := FleetGaussianDensity.exists_rational_gaussian_approx hb hg hs hε
    exact ⟨⟨m, s, coeff⟩, hd⟩
  · intro d
    have ht := FleetLinearDictionary.residual_tendsto_linear_combination c x
      (fun k t => FleetFullLineFourier.h (gauss b (d.center k : ℝ)) t)
      (fun k => FleetFullLineArithmetic.rhs (gauss b (d.center k : ℝ)))
      d.modes d.coefficient (fun k _ => hr (d.center k))
    simpa only [h_test hb, rhs_test hb] using ht

/-- The same criterion displaying the exact spectral Gaussian normalization. -/
theorem RH_of_normalized_gaussian_residuals {b : ℝ} (hb : 0 < b)
    (c : ℕ → ℕ) (x : ∀ n, Fin (c n) → ℝ) {M : ℝ}
    (hm : ∀ n, (∑ i, (1+(x n i)^2)⁻¹) ≤ M)
    (hr : ∀ q : ℚ, Tendsto (fun n =>
      (∑ i : Fin (c n), (Real.sqrt (Real.pi/b) : ℂ)*
        Complex.exp (-((x n i : ℂ)-(q : ℝ))^2/(4*b)))-
        FleetFullLineArithmetic.rhs (gauss b (q : ℝ))) atTop (𝓝 0)) :
    RiemannHypothesis := by
  apply RH_of_rational_gaussian_residuals hb c x hm
  intro q
  simpa only [FleetGaussianDictionaryMember.h_gauss_eq hb] using hr q

end FleetGaussianCriterion
