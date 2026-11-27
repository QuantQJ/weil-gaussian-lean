import Mathlib

/-!
# Midpoint quadrature from second-derivative bounds

The local theorem proves the sharp cell error `M * (b-a)^3 / 24` from actual
first- and second-derivative witnesses and a bound for the absolute second
derivative on the cell. The quadratic Taylor remainder is derived here:
convexity of `(M/2)*x^2 - f x` and the corresponding expression for `-f` give
`|f x - f m - f' m * (x-m)| ≤ (M/2)*(x-m)^2`. Integration cancels the linear
term at the midpoint and evaluates the quadratic majorant exactly.

The `ContDiff` wrapper and partition and uniform-grid corollaries use ordinary
`deriv (deriv f)`. Their second-derivative bounds are restricted to the cells
being integrated; they do not assume uniform bounds for function-value errors.
Actual integrand-specific derivative bounds and midpoint-value enclosures remain
separate certification work.
-/

noncomputable section
namespace FleetMidpointQuadrature
open MeasureTheory Set

/-- A tangent line to a differentiable convex real function lies below it. -/
lemma convex_tangent_le {g : ℝ → ℝ} {s : Set ℝ} (hg : ConvexOn ℝ s g)
    {m x d : ℝ} (hm : m ∈ s) (hx : x ∈ s) (hd : HasDerivAt g d m) :
    g m+d*(x-m) ≤ g x := by
  rcases lt_trichotomy m x with hmx | rfl | hxm
  · have hh := hg.le_slope_of_hasDerivAt hm hx hmx hd
    rw [slope_def_field] at hh
    have hh' := (le_div_iff₀ (sub_pos.mpr hmx)).mp hh
    linarith
  · simp
  · have hh := hg.slope_le_of_hasDerivAt hx hm hxm hd
    rw [slope_def_field] at hh
    have hh' := (div_le_iff₀ (sub_pos.mpr hxm)).mp hh
    linarith

/-- The upper quadratic Taylor remainder follows from the second derivative
upper bound on the interval, for points on either side of the expansion point. -/
lemma taylor_upper_of_second_deriv_le {f f' f'' : ℝ → ℝ} {a b M m x : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (h1 : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (h2 : ∀ t ∈ Icc a b, HasDerivAt f' (f'' t) t)
    (hbound : ∀ t ∈ Icc a b, f'' t ≤ M)
    (hm : m ∈ Icc a b) (hx : x ∈ Icc a b) :
    f x-f m-f' m*(x-m) ≤ (M/2)*(x-m)^2 := by
  let g : ℝ → ℝ := fun t => (M/2)*t^2-f t
  have hg : ContinuousOn g (Icc a b) :=
    ((continuous_const.mul (continuous_id.pow 2)).continuousOn).sub hf
  have hg1 : ∀ t ∈ Icc a b, HasDerivAt g (M*t-f' t) t := by
    intro t ht
    convert ((hasDerivAt_pow 2 t).const_mul (M/2)).sub (h1 t ht) using 1; dsimp [g]; ring
  have hg2 : ∀ t ∈ Icc a b,
      HasDerivAt (fun z => M*z-f' z) (M-f'' t) t := by
    intro t ht
    convert ((hasDerivAt_id t).const_mul M).sub (h2 t ht) using 1 <;> first | rfl | ring
  have hconvex : ConvexOn ℝ (Icc a b) g := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc a b) hg
      (f' := fun t => M*t-f' t) (f'' := fun t => M-f'' t)
    · intro t ht
      exact (hg1 t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      exact (hg2 t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      exact sub_nonneg.mpr (hbound t (interior_subset ht))
  have hh := convex_tangent_le hconvex hm hx (hg1 m hm)
  dsimp [g] at hh
  nlinarith

/-- Actual first- and second-derivative data imply the quadratic remainder
bound; no local function-value error bound is assumed. -/
lemma abs_taylor_remainder_le {f f' f'' : ℝ → ℝ} {a b M m x : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (h1 : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (h2 : ∀ t ∈ Icc a b, HasDerivAt f' (f'' t) t)
    (hbound : ∀ t ∈ Icc a b, |f'' t| ≤ M)
    (hm : m ∈ Icc a b) (hx : x ∈ Icc a b) :
    |f x-f m-f' m*(x-m)| ≤ (M/2)*(x-m)^2 := by
  have hu := taylor_upper_of_second_deriv_le hf h1 h2
    (fun t ht => (le_abs_self _).trans (hbound t ht)) hm hx
  have hl := taylor_upper_of_second_deriv_le hf.neg
    (f' := fun t => -f' t) (f'' := fun t => -f'' t)
    (fun t ht => (h1 t ht).neg) (fun t ht => (h2 t ht).neg)
    (fun t ht => (neg_le_abs _).trans (hbound t ht)) hm hx
  dsimp at hl
  exact abs_le.mpr ⟨by linarith, hu⟩

/-- The linear part of a midpoint Taylor expansion integrates to zero. -/
lemma integral_midpoint_linear (a b : ℝ) :
    (∫ x in a..b, x-(a+b)/2) = 0 := by
  have hi : IntervalIntegrable (fun x : ℝ => x) volume a b := continuous_id.intervalIntegrable a b
  have hc : IntervalIntegrable (fun _ : ℝ => (a+b)/2) volume a b := intervalIntegrable_const
  rw [intervalIntegral.integral_sub hi hc, integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- Exact integration of the quadratic majorant gives the coefficient 1/24. -/
lemma integral_midpoint_quadratic (a b M : ℝ) :
    (∫ x in a..b, (M/2)*(x-(a+b)/2)^2) = M*(b-a)^3/24 := by
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right (fun x : ℝ => x^2) ((a+b)/2),
    integral_pow]
  norm_num
  ring

/-- Sharp midpoint error from local derivative witnesses on the closed cell.
Only the displayed values of the functions and derivatives on that cell matter. -/
theorem midpoint_error_of_hasDerivAt {f f' f'' : ℝ → ℝ} {a b M : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (h1 : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (h2 : ∀ t ∈ Icc a b, HasDerivAt f' (f'' t) t)
    (hbound : ∀ t ∈ Icc a b, |f'' t| ≤ M) :
    |(∫ x in a..b, f x) - (b-a)*f ((a+b)/2)| ≤ M*(b-a)^3/24 := by
  let m := (a+b)/2
  let r : ℝ → ℝ := fun x => f x-f m-f' m*(x-m)
  have hm : m ∈ Icc a b := by dsimp [m]; constructor <;> linarith
  have hfi : IntervalIntegrable f volume a b := hf.intervalIntegrable_of_Icc hab
  have hr : ContinuousOn r (Icc a b) := by
    exact (hf.sub continuous_const.continuousOn).sub
      (continuous_const.mul (continuous_id.sub continuous_const)).continuousOn
  have hl : IntervalIntegrable (fun x : ℝ => x-m) volume a b :=
    (continuous_id.sub continuous_const).intervalIntegrable a b
  have heq : (∫ x in a..b, r x) = (∫ x in a..b, f x)-(b-a)*f m := by
    dsimp [r]
    rw [intervalIntegral.integral_sub (hfi.sub intervalIntegrable_const) (hl.const_mul _),
      intervalIntegral.integral_sub hfi intervalIntegrable_const,
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
    have hz : (∫ x in a..b, x-m) = 0 := integral_midpoint_linear a b
    rw [hz]
    simp [smul_eq_mul]
  calc
    _ = |∫ x in a..b, r x| := by rw [heq]
    _ ≤ ∫ x in a..b, |r x| := by
      simpa only [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_integral_norm (f := r) hab)
    _ ≤ ∫ x in a..b, (M/2)*(x-m)^2 := by
      apply intervalIntegral.integral_mono_on hab (hr.abs.intervalIntegrable_of_Icc hab)
        ((continuous_const.mul ((continuous_id.sub continuous_const).pow 2)).intervalIntegrable a b)
      intro x hx
      exact abs_taylor_remainder_le hf h1 h2 hbound hm hx
    _ = _ := integral_midpoint_quadratic a b M

/-- Convenient `C²` version with ordinary first and second derivatives. -/
theorem midpoint_error_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {a b M : ℝ}
    (hab : a ≤ b) (hbound : ∀ t ∈ Icc a b, |deriv (deriv f) t| ≤ M) :
    |(∫ x in a..b, f x) - (b-a)*f ((a+b)/2)| ≤ M*(b-a)^3/24 := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd' : Differentiable ℝ (deriv f) :=
    ((contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1+1) f from hf)).2.2).differentiable (by norm_num)
  exact midpoint_error_of_hasDerivAt hab hf.continuous.continuousOn
    (fun t _ => (hd t).hasDerivAt) (fun t _ => (hd' t).hasDerivAt) hbound

/-- Cellwise second-derivative bounds yield the sum of the sharp cell errors
for any finite nondecreasing partition, including repeated endpoints. -/
theorem partition_midpoint_error_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (a : ℕ → ℝ) (n : ℕ) (M : ℕ → ℝ)
    (hmono : ∀ k < n, a k ≤ a (k+1))
    (hbound : ∀ k < n, ∀ t ∈ Icc (a k) (a (k+1)), |deriv (deriv f) t| ≤ M k) :
    |(∫ x in (a 0)..(a n), f x) -
      ∑ k ∈ Finset.range n, (a (k+1)-a k)*f ((a k+a (k+1))/2)| ≤
      ∑ k ∈ Finset.range n, M k*(a (k+1)-a k)^3/24 := by
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (a := a) (n := n)
    (fun k _ => hf.continuous.intervalIntegrable (a k) (a (k+1)))
  rw [← hsplit, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro k hk
  exact midpoint_error_le hf (hmono k (Finset.mem_range.mp hk)) (hbound k (Finset.mem_range.mp hk))

/-- On a uniform grid of `n` cells of width `h`, the total midpoint error is
at most `n*M*h^3/24`; only one second-derivative bound on the full interval is used. -/
theorem uniform_midpoint_error_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (a h M : ℝ) (n : ℕ) (hh : 0 ≤ h)
    (hbound : ∀ t ∈ Icc a (a+n*h), |deriv (deriv f) t| ≤ M) :
    |(∫ x in a..(a+n*h), f x) -
      h*∑ k ∈ Finset.range n, f (a+((k : ℝ)+1/2)*h)| ≤ (n : ℝ)*M*h^3/24 := by
  have hmono : ∀ k < n, a+(k : ℝ)*h ≤ a+((k+1 : ℕ) : ℝ)*h := by
    intro k _
    push_cast
    nlinarith
  have hc : ∀ k < n, ∀ t ∈ Icc (a+(k : ℝ)*h) (a+((k+1 : ℕ) : ℝ)*h),
      |deriv (deriv f) t| ≤ M := by
    intro k hk t ht
    apply hbound t
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have hkn : ((k+1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (show k+1 ≤ n by omega)
    constructor
    · nlinarith [ht.1, mul_nonneg hk0 hh]
    · nlinarith [ht.2, mul_le_mul_of_nonneg_right hkn hh]
  have hp := partition_midpoint_error_le hf (fun k => a+(k : ℝ)*h) n (fun _ => M) hmono hc
  have hw (k : ℕ) : (a+((k+1 : ℕ) : ℝ)*h)-(a+(k : ℝ)*h) = h := by push_cast; ring
  have hm (k : ℕ) : ((a+(k : ℝ)*h)+(a+((k+1 : ℕ) : ℝ)*h))/2 =
      a+((k : ℝ)+1/2)*h := by push_cast; ring
  simp_rw [hw, hm] at hp
  simpa [Finset.mul_sum, mul_assoc, mul_div_assoc] using hp

end FleetMidpointQuadrature
