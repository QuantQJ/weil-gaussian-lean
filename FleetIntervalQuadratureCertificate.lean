import Mathlib

/-!
# Soundness of quadrature from certified cell bounds

For a continuous real function, proved pointwise lower and upper bounds on each
closed partition cell bound the integral by the corresponding sums of cell
widths times those bounds. The partition may be nonuniform, adjacent endpoints
may coincide, and an empty partition is allowed.

The proof uses integral monotonicity on each cell and exact addition of adjacent
interval integrals. The error theorems require uniform local error bounds on
whole cells, not only sampled values. This module proves the soundness of such
certificates; it does not prove cell bounds for a digamma or Gaussian integrand,
or turn an external quadrature output into a Lean proof of those bounds.
-/

noncomputable section
namespace FleetIntervalQuadratureCertificate
open MeasureTheory Set

/-- A proved range on a closed cell gives an enclosure for its exact integral. -/
lemma cell_integral_enclosure {f : ℝ → ℝ} (hf : Continuous f)
    {a b lo hi : ℝ} (hab : a ≤ b)
    (hcell : ∀ x ∈ Icc a b, lo ≤ f x ∧ f x ≤ hi) :
    (b-a)*lo ≤ (∫ x in a..b, f x) ∧ (∫ x in a..b, f x) ≤ (b-a)*hi := by
  constructor
  · have hh := intervalIntegral.integral_mono_on (μ := volume) hab intervalIntegrable_const
      (hf.intervalIntegrable a b) (fun x hx => (hcell x hx).1)
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using hh
  · have hh := intervalIntegral.integral_mono_on (μ := volume) hab (hf.intervalIntegrable a b)
      intervalIntegrable_const (fun x hx => (hcell x hx).2)
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using hh

/-- Lower and upper cell ranges integrate to a proved enclosure of the whole
interval integral. Only the first `n` adjacent endpoint comparisons are needed. -/
theorem partition_integral_enclosure {f : ℝ → ℝ} (hf : Continuous f)
    (a : ℕ → ℝ) (n : ℕ) (lo hi : ℕ → ℝ)
    (hmono : ∀ k < n, a k ≤ a (k+1))
    (hcell : ∀ k < n, ∀ x ∈ Icc (a k) (a (k+1)), lo k ≤ f x ∧ f x ≤ hi k) :
    (∑ k ∈ Finset.range n, (a (k+1)-a k)*lo k) ≤ (∫ x in (a 0)..(a n), f x) ∧
      (∫ x in (a 0)..(a n), f x) ≤ ∑ k ∈ Finset.range n, (a (k+1)-a k)*hi k := by
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (a := a) (n := n)
    (fun k _ => hf.intervalIntegrable (a k) (a (k+1)))
  rw [← hsplit]
  constructor
  · apply Finset.sum_le_sum
    intro k hk
    exact (cell_integral_enclosure hf (hmono k (Finset.mem_range.mp hk))
      (hcell k (Finset.mem_range.mp hk))).1
  · apply Finset.sum_le_sum
    intro k hk
    exact (cell_integral_enclosure hf (hmono k (Finset.mem_range.mp hk))
      (hcell k (Finset.mem_range.mp hk))).2

/-- Arbitrary cell reference values give a quadrature rule with total error
bounded by the sum of cell widths times proved uniform local errors. The
reference values need not be evaluations of the integrand. -/
theorem quadrature_error_le {f : ℝ → ℝ} (hf : Continuous f)
    (a : ℕ → ℝ) (n : ℕ) (value error : ℕ → ℝ)
    (hmono : ∀ k < n, a k ≤ a (k+1))
    (herror : ∀ k < n, ∀ x ∈ Icc (a k) (a (k+1)), |f x-value k| ≤ error k) :
    |(∫ x in (a 0)..(a n), f x) - ∑ k ∈ Finset.range n, (a (k+1)-a k)*value k| ≤
      ∑ k ∈ Finset.range n, (a (k+1)-a k)*error k := by
  have hbounds := partition_integral_enclosure hf a n
    (fun k => value k-error k) (fun k => value k+error k) hmono (by
      intro k hk x hx
      have hh := abs_le.mp (herror k hk x hx)
      constructor <;> (try dsimp only) <;> linarith [hh.1, hh.2])
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib] at hbounds
  exact abs_le.mpr ⟨by linarith [hbounds.1], by linarith [hbounds.2]⟩

/-- The midpoint rule is sound when the deviation from each exact midpoint
value is proved uniformly on that whole cell. This theorem does not infer
a local error bound from midpoint sampling. -/
theorem midpoint_error_le {f : ℝ → ℝ} (hf : Continuous f)
    (a : ℕ → ℝ) (n : ℕ) (error : ℕ → ℝ)
    (hmono : ∀ k < n, a k ≤ a (k+1))
    (herror : ∀ k < n, ∀ x ∈ Icc (a k) (a (k+1)),
      |f x-f ((a k+a (k+1))/2)| ≤ error k) :
    |(∫ x in (a 0)..(a n), f x) -
      ∑ k ∈ Finset.range n, (a (k+1)-a k)*f ((a k+a (k+1))/2)| ≤
      ∑ k ∈ Finset.range n, (a (k+1)-a k)*error k := by
  exact quadrature_error_le hf a n (fun k => f ((a k+a (k+1))/2)) error hmono herror

end FleetIntervalQuadratureCertificate
